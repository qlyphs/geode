//! Profile 0x00070001 on top of p3: the registered round table (spec §4), the registered-round
//! adapter that replaces the P3 challenger (§6), the global Merkle oracle framing (§3.1) and the
//! raw public-instance encodings (§2.4).
//!
//! The adapter is a state machine over the round table. Prover messages (observations) collect
//! the scalar body of the next round; the first challenge request after the body begins that
//! round: its singleton root (or its real Merkle root) is appended to the history, the one
//! registered SHAKE256 call derives the block prefix, and every typed slot is decoded and cached.
//! Requests then consume cached slots only. An observation while slots remain, a request for a
//! slot type or width the round does not register, a body of the wrong length, a grinding call
//! or a plain bit sample poisons the adapter; the verifier rejects a poisoned transcript.

use std::sync::Arc;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};

use p3_challenger::{CanObserve, CanSample, CanSampleBits, CanSampleUniformBits, FieldChallenger, GrindingChallenger, ResamplingError};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{CryptographicHasher, MerkleCap, PseudoCompressionFunction};
use p3_whir::WhirShape;

use crate::fs7::{self, CoinState, KIND_ROW, Shape, le32};
use crate::field::{EF, F};
use crate::pcs::Inject;

// ---------------------------------------------------------------- round table (§4)

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Body {
    /// A real WHIR tree; its root is observed as an opaque commitment.
    Real,
    /// A singleton scalar body of exactly this many bytes.
    Scalar(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoundDef {
    pub body: Body,
    pub shape: Shape,
    /// For a query round: the round whose real tree its indices open (§6.3).
    pub opens: Option<u32>,
    pub label: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table {
    pub profile: u32,
    pub n: usize,
    pub formal_len: usize,
    /// rounds[i] is round i + 1.
    pub rounds: Vec<RoundDef>,
}

impl Table {
    pub fn len(&self) -> usize {
        self.rounds.len()
    }
    pub fn def(&self, round: usize) -> &RoundDef {
        &self.rounds[round - 1]
    }
    pub fn used_total(&self) -> usize {
        self.rounds.iter().map(|r| r.shape.used()).sum()
    }
    pub fn scalar_rounds(&self) -> usize {
        self.rounds.iter().filter(|r| matches!(r.body, Body::Scalar(_))).count()
    }
}

/// Frontend sizes of a statement of n signatures.
pub struct Front {
    /// GKR leaf depth d (layers 1..d-1 run a sumcheck).
    pub d: usize,
    pub log_dc: usize,
    pub log_tab: usize,
    pub chunks: usize,
    pub trials: usize,
    pub slots: usize,
}

/// Build the round table from the frontend sizes and the WHIR shape (5 opened values).
pub fn build_table(profile: u32, n: usize, fr: &Front, ws: &WhirShape) -> Table {
    const K: usize = 40;
    let mut r: Vec<RoundDef> = Vec::with_capacity(360);
    fn push_to(r: &mut Vec<RoundDef>, body: Body, shape: Shape, opens: Option<u32>, label: &'static str) {
        r.push(RoundDef { body, shape, opens, label });
    }
    macro_rules! push {
        ($($a:expr),*) => { push_to(&mut r, $($a),*) };
    }
    push!(Body::Real, Shape { nq: fr.trials * (n + fr.slots), ..Default::default() }, None, "initial commitment; projections");
    push!(Body::Scalar(5 * fr.trials * fr.chunks), Shape { theta: true, ..Default::default() }, None, "quotients; theta");
    push!(Body::Scalar(4 * K), Shape::k(2), None, "GKR layer-1 finals; beta_0, lambda_1");
    for k in 1..fr.d {
        for _ in 0..k {
            push!(Body::Scalar(2 * K), Shape::k(1), None, "GKR round (a1, a2)");
        }
        push!(Body::Scalar(4 * K), Shape::k(if k + 1 < fr.d { 2 } else { 1 }), None, "GKR finals; beta_k (, lambda_k+1)");
    }
    push!(Body::Scalar(2 * K), Shape::k(2), None, "explicit (P_leaf, Q_leaf); gamma_P, gamma_Q");
    push!(Body::Scalar(K), Shape::k(1 + fr.log_dc + n + fr.chunks * fr.trials), None, "T; gamma_Z, tau, omega, mu");
    for _ in 0..fr.log_dc {
        push!(Body::Scalar(4 * K), Shape::k(1), None, "master round");
    }
    for _ in 0..fr.log_tab {
        push!(Body::Scalar(2 * K), Shape::k(1), None, "table round");
    }
    assert_eq!(ws.commitment_ood_samples, 1, "one initial OOD sample");
    assert!(!ws.stratified_queries);
    push!(Body::Scalar(0), Shape::k(1), None, "empty; initial OOD point");
    push!(Body::Scalar((1 + 5) * K), Shape::k(1), None, "initial OOD answer, 5 opened values; batching alpha");
    for _ in 0..ws.initial_sumcheck.rounds {
        push!(Body::Scalar(2 * K), Shape::k(1), None, "WHIR sumcheck");
    }
    // Tree committed by round j is opened by the queries of the next WHIR round.
    let mut prev_tree: u32 = 1;
    for rd in &ws.rounds {
        assert_eq!(rd.ood_samples, 1);
        assert!(rd.query_draws > 0 && rd.query_pow_bits == 0 && rd.sumcheck.pow_bits == 0);
        let tree = (r.len() + 1) as u32;
        push!(Body::Real, Shape::k(1), None, "WHIR commitment; OOD point");
        push!(Body::Scalar(K), Shape { nk: 1, widths: vec![rd.index_bits as u8; rd.query_draws], ..Default::default() }, Some(prev_tree), "OOD answer; query indices, gamma");
        for _ in 0..rd.sumcheck.rounds {
            push!(Body::Scalar(2 * K), Shape::k(1), None, "WHIR sumcheck");
        }
        prev_tree = tree;
    }
    assert!(ws.final_query_draws > 0 && ws.final_pow_bits == 0 && ws.final_sumcheck.pow_bits == 0);
    push!(Body::Scalar(ws.final_poly_len * K), Shape { widths: vec![ws.final_index_bits as u8; ws.final_query_draws], ..Default::default() }, Some(prev_tree), "final polynomial; final query indices");
    for _ in 0..ws.final_sumcheck.rounds {
        push!(Body::Scalar(2 * K), Shape::k(1), None, "final sumcheck");
    }
    let formal_len = r.iter().map(|d| d.shape.used()).max().unwrap();
    Table { profile, n, formal_len, rounds: r }
}

// ---------------------------------------------------------------- global Merkle oracle (§3.1)

/// Leaf hash of a real WHIR row: kind 0x00, the round that committed the tree read from the
/// adapter's routing cell, payload = row in canonical base-field-word order.
#[derive(Clone)]
pub struct Leaf7 {
    pub profile: u32,
    pub tree: Arc<AtomicU32>,
    pub calls: Arc<AtomicU64>,
}

impl CryptographicHasher<F, [u64; 8]> for Leaf7 {
    fn hash_iter<I: IntoIterator<Item = F>>(&self, input: I) -> [u64; 8] {
        let t = self.tree.load(Ordering::Relaxed);
        assert!(t != 0, "leaf hash outside a registered tree");
        let mut row = Vec::with_capacity(1280);
        for x in input {
            row.extend_from_slice(&x.as_canonical_u64().to_le_bytes());
        }
        self.calls.fetch_add(1, Ordering::Relaxed);
        count(t, true);
        to_words(&fs7::leaf_hash(self.profile, t, KIND_ROW, &row))
    }
}

/// Internal node hash. Without a tag (QLYAUTH7 and the round-9 lab profiles) it is
/// H64(0x81 || L || R). With a tag (round-10 lab profiles) it reads the same routing cell as
/// `Leaf7`, so every committed tree is its own oracle: H64(0x81 || LE32(profile) ||
/// LE16(tree commit round) || L || R).
#[derive(Clone, Default)]
pub struct Node7 {
    pub tag: Option<(u32, Arc<AtomicU32>)>,
}

impl Node7 {
    pub fn tagged(profile: u32, tree: Arc<AtomicU32>) -> Self {
        Node7 { tag: Some((profile, tree)) }
    }
}

/// Hash counting for the registry census and the per-tree barrier test (off by default: the
/// counters are only touched when COUNT is set).
pub static COUNT: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
pub static NODE_CALLS: AtomicU64 = AtomicU64::new(0);
pub static LEAF_CALLS: AtomicU64 = AtomicU64::new(0);
/// Per tree id: (leaf hashes, node hashes) while COUNT is set.
pub static TREE_COUNTS: std::sync::Mutex<std::collections::BTreeMap<u32, (u64, u64)>> = std::sync::Mutex::new(std::collections::BTreeMap::new());

fn count(tree: u32, leaf: bool) {
    if COUNT.load(Ordering::Relaxed) {
        if leaf { &LEAF_CALLS } else { &NODE_CALLS }.fetch_add(1, Ordering::Relaxed);
        let mut m = TREE_COUNTS.lock().unwrap();
        let e = m.entry(tree).or_default();
        if leaf { e.0 += 1 } else { e.1 += 1 }
    }
}

/// Test-only (dishonest prover): hash every tagged node with this tree round instead of the
/// routing cell's (0 = off).
pub static NODE_ROUND_OVERRIDE: AtomicU32 = AtomicU32::new(0);

impl PseudoCompressionFunction<[u64; 8], 2> for Node7 {
    fn compress(&self, input: [[u64; 8]; 2]) -> [u64; 8] {
        match &self.tag {
            None => to_words(&fs7::node_hash(&to_bytes(&input[0]), &to_bytes(&input[1]))),
            Some((profile, cell)) => {
                let t = cell.load(Ordering::Relaxed);
                count(t, false);
                assert!(t != 0, "node hash outside a registered tree");
                assert!(t <= u16::MAX as u32, "tree round does not fit LE16");
                let o = NODE_ROUND_OVERRIDE.load(Ordering::Relaxed);
                let t = if o != 0 { o } else { t };
                to_words(&fs7::node_hash_tree(*profile, t as u16, &to_bytes(&input[0]), &to_bytes(&input[1])))
            }
        }
    }
}

pub fn to_words(b: &[u8; 64]) -> [u64; 8] {
    core::array::from_fn(|i| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap()))
}
pub fn to_bytes(w: &[u64; 8]) -> [u8; 64] {
    let mut b = [0u8; 64];
    for (i, x) in w.iter().enumerate() {
        b[8 * i..8 * i + 8].copy_from_slice(&x.to_le_bytes());
    }
    b
}

pub type Mmcs7 = MerkleTreeMmcs<F, u64, Leaf7, Node7, 2, 8>;

// ---------------------------------------------------------------- the adapter (§6)

#[derive(Clone, Debug, Default)]
pub struct Stats {
    /// Registered FS calls (one SHAKE256 derivation per round).
    pub fs_calls: usize,
    /// Coin bytes squeezed (prefixes).
    pub fs_bytes: usize,
    /// Singleton leaf hashes computed for scalar rounds.
    pub singleton_hashes: usize,
    /// p3 DomainSeparator seeds declined (never absorbed).
    pub seeds_declined: usize,
    /// Grinding or plain bit samples requested (must stay 0).
    pub grind_calls: usize,
    pub bits_calls: usize,
}

/// One begun round, recorded for the acceptance gates.
#[derive(Clone, Debug)]
pub struct Logged {
    pub root: [u8; 64],
    pub body: Vec<u8>,
    pub prefix: Vec<u8>,
}

#[derive(Clone)]
pub struct Reg {
    table: Arc<Table>,
    coins: CoinState,
    cur: usize,
    body: Vec<u8>,
    root: Option<[u8; 64]>,
    k: Vec<[u64; 5]>,
    kc: usize,
    theta: Option<EF>,
    q: Option<Vec<u32>>,
    idx: Vec<u32>,
    ic: usize,
    pub tree: Arc<AtomicU32>,
    pub stats: Stats,
    pub log: Option<Vec<Logged>>,
    pub error: Option<String>,
    pub inject: Inject,
}

impl Reg {
    pub fn new(table: Arc<Table>, statement: &[u8], tree: Arc<AtomicU32>) -> Self {
        let coins = CoinState::new(table.profile, table.formal_len, statement);
        let mut r = Reg { table, coins, cur: 0, body: vec![], root: None, k: vec![], kc: 0, theta: None, q: None, idx: vec![], ic: 0, tree, stats: Stats::default(), log: None, error: None, inject: Inject::Off };
        r.route_next();
        r
    }
    pub fn table(&self) -> &Table {
        &self.table
    }
    pub fn round(&self) -> usize {
        self.cur
    }
    fn poison(&mut self, why: String) {
        if self.error.is_none() {
            self.error = Some(why);
        }
    }
    fn exhausted(&self) -> bool {
        self.kc == 5 * self.k.len() && self.theta.is_none() && self.q.is_none() && self.ic == self.idx.len()
    }
    /// Every registered round begun and every slot consumed.
    pub fn finished(&self) -> bool {
        self.error.is_none() && self.cur == self.table.len() && self.exhausted() && self.body.is_empty() && self.root.is_none()
    }
    /// Once the current block is consumed and the next round commits a real tree, the leaf
    /// hasher must frame that tree's rows with the next round id (prover-side commit).
    fn route_next(&mut self) {
        if self.exhausted() && self.cur < self.table.len() && self.table.def(self.cur + 1).body == Body::Real {
            self.tree.store((self.cur + 1) as u32, Ordering::Relaxed);
        }
    }
    fn begin(&mut self) {
        if self.error.is_some() {
            return;
        }
        if !self.exhausted() {
            return self.poison(format!("round {}: challenges left unconsumed", self.cur));
        }
        let next = self.cur + 1;
        if next > self.table.len() {
            return self.poison(format!("challenge requested after the last registered round {}", self.table.len()));
        }
        let def = self.table.def(next).clone();
        let root = match def.body {
            Body::Real => {
                if !self.body.is_empty() {
                    return self.poison(format!("round {next}: scalar message before a real commitment"));
                }
                match self.root.take() {
                    Some(r) => r,
                    None => return self.poison(format!("round {next}: real commitment missing")),
                }
            }
            Body::Scalar(len) => {
                if self.root.is_some() {
                    return self.poison(format!("round {next}: unexpected commitment"));
                }
                if self.body.len() != len {
                    return self.poison(format!("round {next} ({}): body of {} bytes, registered {len}", def.label, self.body.len()));
                }
                self.stats.singleton_hashes += 1;
                fs7::singleton_root(self.table.profile, next as u32, &self.body)
            }
        };
        self.coins.push(next as u32, &root);
        let used = def.shape.used();
        let raw = self.coins.block(&def.shape, used);
        self.stats.fs_calls += 1;
        self.stats.fs_bytes += used;
        let d = fs7::decode(&raw, &def.shape);
        if d.short {
            // Round-10 strict pool: never padded; prover and verifier both stop here.
            return self.poison(format!("round {next}: F_q pool short ({} of {} coefficients accepted)", d.q.len(), def.shape.nq));
        }
        if let Some(log) = self.log.as_mut() {
            log.push(Logged { root, body: std::mem::take(&mut self.body), prefix: raw });
        }
        self.body.clear();
        self.k = d.k;
        self.kc = 0;
        self.theta = d.theta.map(|c| EF::from_basis_coefficients_fn(|i| F::from_u64(c[i])));
        self.q = if def.shape.nq > 0 { Some(d.q) } else { None };
        self.idx = d.idx;
        self.ic = 0;
        self.cur = next;
        if let Some(t) = def.opens {
            self.tree.store(t, Ordering::Relaxed);
        }
        self.route_next();
    }
    fn begin_if_needed(&mut self) {
        if self.exhausted() {
            self.begin();
        }
    }
    /// Append prover-message bytes to the next round's body.
    pub fn observe_bytes(&mut self, b: &[u8]) {
        if self.error.is_some() {
            return;
        }
        if !self.exhausted() {
            return self.poison(format!("round {}: prover message before all challenges were consumed", self.cur));
        }
        self.body.extend_from_slice(b);
    }
    pub fn observe_root(&mut self, root: [u8; 64]) {
        if self.error.is_some() {
            return;
        }
        let next = self.cur + 1;
        if !self.exhausted() || next > self.table.len() || self.table.def(next).body != Body::Real || self.root.is_some() || !self.body.is_empty() {
            return self.poison(format!("round {next}: commitment not registered here"));
        }
        self.root = Some(root);
    }
    fn next_coeff(&mut self) -> F {
        self.begin_if_needed();
        if self.error.is_some() {
            return F::ZERO;
        }
        if self.kc >= 5 * self.k.len() {
            self.poison(format!("round {}: K challenge not registered", self.cur));
            return F::ZERO;
        }
        let v = self.k[self.kc / 5][self.kc % 5];
        self.kc += 1;
        self.route_next();
        F::from_u64(v)
    }
    pub fn sample_k(&mut self) -> EF {
        EF::from_basis_coefficients_fn(|_| self.next_coeff())
    }
    pub fn sample_theta(&mut self) -> EF {
        self.begin_if_needed();
        match self.theta.take() {
            Some(t) if self.error.is_none() => {
                self.route_next();
                t
            }
            _ => {
                self.poison(format!("round {}: theta not registered", self.cur));
                EF::ZERO
            }
        }
    }
    pub fn sample_fq(&mut self) -> Vec<u32> {
        self.begin_if_needed();
        match self.q.take() {
            Some(q) if self.error.is_none() => {
                self.route_next();
                q
            }
            _ => {
                self.poison(format!("round {}: F_q pool not registered", self.cur));
                vec![]
            }
        }
    }
    pub fn sample_index(&mut self, bits: usize) -> usize {
        self.begin_if_needed();
        if self.error.is_some() {
            return 0;
        }
        let w = self.table.def(self.cur).shape.widths.get(self.ic).copied();
        if self.ic >= self.idx.len() || w.map(|w| w as usize) != Some(bits) {
            self.poison(format!("round {}: query index of {bits} bits not registered", self.cur));
            return 0;
        }
        let v = self.idx[self.ic] as usize;
        self.ic += 1;
        self.route_next();
        v
    }
}

impl CanObserve<F> for Reg {
    fn observe(&mut self, x: F) {
        self.observe_bytes(&x.as_canonical_u64().to_le_bytes());
    }
    fn absorb_domain_seed(&mut self) -> bool {
        self.stats.seeds_declined += 1;
        false
    }
}

impl CanObserve<MerkleCap<F, [u64; 8]>> for Reg {
    fn observe(&mut self, cap: MerkleCap<F, [u64; 8]>) {
        if cap.roots().len() != 1 {
            return self.poison("commitment cap of height > 0".into());
        }
        self.observe_root(to_bytes(&cap.roots()[0]));
    }
}

impl CanSample<F> for Reg {
    fn sample(&mut self) -> F {
        self.next_coeff()
    }
}

impl CanSampleBits<usize> for Reg {
    fn sample_bits(&mut self, _bits: usize) -> usize {
        self.stats.bits_calls += 1;
        self.poison("plain bit sample (not registered)".into());
        0
    }
}

impl CanSampleUniformBits<F> for Reg {
    fn sample_uniform_bits<const RESAMPLE: bool>(&mut self, bits: usize) -> Result<usize, ResamplingError> {
        Ok(self.sample_index(bits))
    }
}

impl FieldChallenger<F> for Reg {}

impl GrindingChallenger for Reg {
    type Witness = F;
    fn grind(&mut self, _bits: usize) -> F {
        self.stats.grind_calls += 1;
        self.poison("grinding (not registered)".into());
        F::ZERO
    }
}

// ---------------------------------------------------------------- frontend transcript

/// The frontend's view of the adapter (same calls as the QLYAUTH4 transcript `pcs::Tr`).
pub struct Tr7 {
    pub ch: Reg,
}

impl Tr7 {
    pub fn new(table: Arc<Table>, statement: &[u8], tree: Arc<AtomicU32>, inject: Inject) -> Self {
        let mut ch = Reg::new(table, statement, tree);
        ch.inject = inject;
        Tr7 { ch }
    }
}

impl crate::pcs::Fs for Tr7 {
    fn absorb_ef(&mut self, x: EF) {
        let mut b = Vec::with_capacity(40);
        crate::field::ef_to_bytes(&x, &mut b);
        self.ch.observe_bytes(&b);
    }
    fn sample_ef(&mut self) -> EF {
        self.ch.sample_k()
    }
    fn inject(&self) -> Inject {
        self.ch.inject
    }
}

// ---------------------------------------------------------------- public instance (§2.4)

/// X = "Qlyphs/Archive/Instance/v7\0" || LE32(profile) || F(0x0100, manifest)
///     || F(0x0101, parent Header104) || F(0x0102, BlockSection) || F(0x0103, U) || F(0x0104, nu).
pub fn instance_chain(profile: u32, manifest: &[u8], parent104: &[u8], block_section: &[u8], u: &[u8], nu: &[u8]) -> Vec<u8> {
    let mut x = Vec::with_capacity(64 + manifest.len() + parent104.len() + block_section.len() + u.len() + nu.len() + 60);
    x.extend_from_slice(fs7::INSTANCE_DOMAIN);
    x.extend_from_slice(&le32(profile));
    x.extend_from_slice(&fs7::frame(0x0100, manifest));
    x.extend_from_slice(&fs7::frame(0x0101, parent104));
    x.extend_from_slice(&fs7::frame(0x0102, block_section));
    x.extend_from_slice(&fs7::frame(0x0103, u));
    x.extend_from_slice(&fs7::frame(0x0104, nu));
    x
}

/// Lab-only instance for the standalone statements of the soundness suites (records given as
/// (pk, ctx, msg), no chain): a distinct domain string, then the same framing with the records in
/// place of the block section. Only lab profiles 0xfff700xx use it.
pub fn instance_lab(profile: u32, manifest: &[u8], records: &[crate::mlnat::Record], u: &[u8], nu: &[u8]) -> Vec<u8> {
    let mut rs = Vec::new();
    rs.extend_from_slice(&le32(records.len() as u32));
    for r in records {
        rs.extend_from_slice(&le32(r.ctx.len() as u32));
        rs.extend_from_slice(&r.ctx);
        rs.extend_from_slice(&le32(r.msg.len() as u32));
        rs.extend_from_slice(&r.msg);
        rs.extend_from_slice(&r.pk);
    }
    let mut x = Vec::new();
    x.extend_from_slice(b"Qlyphs/Archive/Instance/v7-lab\0");
    x.extend_from_slice(&le32(profile));
    x.extend_from_slice(&fs7::frame(0x0100, manifest));
    x.extend_from_slice(&fs7::frame(0x0110, &rs));
    x.extend_from_slice(&fs7::frame(0x0103, u));
    x.extend_from_slice(&fs7::frame(0x0104, nu));
    x
}

/// Lab profile ids: 0xfff70000 | log2(N). Never accepted by the chain verifier.
pub fn lab_profile(n: usize) -> u32 {
    0xfff7_0000 | n.trailing_zeros()
}

/// Frontend sizes for n signatures (shared with cert.rs).
pub fn front(n: usize) -> Front {
    let t = crate::cert::Tree::new(n);
    Front { d: t.d, log_dc: t.log_dc, log_tab: crate::cert::LOG_TAB, chunks: crate::proj::chunks(n), trials: crate::proj::TRIALS, slots: crate::witness::SLOTS }
}
