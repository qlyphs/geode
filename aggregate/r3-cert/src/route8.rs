//! Round 8, review A.2: the routing invariant of the QLYAUTH7 leaf hasher, checked on a small
//! direct MMCS harness (no certificate prover).
//!
//! Invariant under test: every leaf hash of one Merkle operation observes the same predetermined
//! (profile, tree id) for the whole operation, including the rayon workers of a commitment and
//! a concurrent certificate job. The route is selected by the real registered-round adapter
//! (`reg7::Reg`) driven through the registered table, read by the real `reg7::Leaf7`, and every
//! root and opening is compared with a pure reference that takes the profile and the tree id as
//! explicit arguments.
//!
//! A job is paused immediately before one leaf call (a wrapper around `Leaf7`), a second job
//! selects its own route and hashes, then the first job resumes. With one routing cell per job
//! (what `cert::B7::new` builds, one per certificate) both jobs must agree with the reference.
//! The control runs the same schedule with one cell shared by both jobs and must show the
//! logical race (the harness can see it). Command: `r3-cert route8`.

use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

use p3_commit::{BatchOpeningRef, Mmcs};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_matrix::Dimensions;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{CryptographicHasher, MerkleCap, PseudoCompressionFunction};

use crate::cert;
use crate::field::F;
use crate::fs7::{self, KIND_ROW};
use crate::pcs::{ShakeLeaf, ShakeNode, shake64};
use crate::reg7::{self, Body, Leaf7, Node7, Reg, to_bytes, to_words};

// ---------------------------------------------------------------- pause gate

/// Blocks the leaf call whose arrival ordinal is `pause_at` until `release`.
struct Gate {
    calls: AtomicUsize,
    pause_at: usize,
    st: Mutex<(bool, bool)>,
    cv: Condvar,
}

impl Gate {
    fn new(pause_at: usize) -> Arc<Self> {
        Arc::new(Gate { calls: AtomicUsize::new(0), pause_at, st: Mutex::new((false, false)), cv: Condvar::new() })
    }
    fn never() -> Arc<Self> {
        Self::new(usize::MAX)
    }
    fn pause(&self) {
        let mut g = self.st.lock().unwrap();
        g.0 = true;
        self.cv.notify_all();
        while !g.1 {
            let (ng, to) = self.cv.wait_timeout(g, Duration::from_secs(120)).unwrap();
            g = ng;
            assert!(!to.timed_out() || g.1, "paused leaf call never released");
        }
    }
    fn wait_reached(&self) -> bool {
        let mut g = self.st.lock().unwrap();
        while !g.0 {
            let (ng, to) = self.cv.wait_timeout(g, Duration::from_secs(120)).unwrap();
            g = ng;
            if to.timed_out() && !g.0 {
                return false;
            }
        }
        true
    }
    fn release(&self) {
        let mut g = self.st.lock().unwrap();
        g.1 = true;
        self.cv.notify_all();
    }
}

#[derive(Clone)]
enum Inner {
    V7(Leaf7),
    V4(ShakeLeaf),
}

/// The production leaf hasher behind a pause point that runs before the hasher reads its route.
#[derive(Clone)]
struct Pausing {
    inner: Inner,
    gate: Arc<Gate>,
}

impl CryptographicHasher<F, [u64; 8]> for Pausing {
    fn hash_iter<I: IntoIterator<Item = F>>(&self, input: I) -> [u64; 8] {
        if self.gate.calls.fetch_add(1, Ordering::SeqCst) == self.gate.pause_at {
            self.gate.pause();
        }
        match &self.inner {
            Inner::V7(l) => l.hash_iter(input),
            Inner::V4(l) => l.hash_iter(input),
        }
    }
}

#[derive(Clone)]
enum NodeAny {
    V7,
    V4,
}

impl PseudoCompressionFunction<[u64; 8], 2> for NodeAny {
    fn compress(&self, input: [[u64; 8]; 2]) -> [u64; 8] {
        match self {
            NodeAny::V7 => Node7.compress(input),
            NodeAny::V4 => ShakeNode.compress(input),
        }
    }
}

type HMmcs = MerkleTreeMmcs<F, u64, Pausing, NodeAny, 2, 8>;

// ---------------------------------------------------------------- pure reference

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    /// QLYAUTH7 under this profile id.
    V7(u32),
    /// QLYAUTH4 (no route: the leaf framing has no tree id).
    V4,
}

fn row_bytes(row: &[F]) -> Vec<u8> {
    row.iter().flat_map(|x| x.as_canonical_u64().to_le_bytes()).collect()
}

/// Leaf hash with the profile and the tree id passed explicitly (PROTOCOL.md §12.5, §3.1).
fn ref_leaf(kind: Kind, tree: u32, row: &[F]) -> [u8; 64] {
    match kind {
        Kind::V7(p) => fs7::leaf_hash(p, tree, KIND_ROW, &row_bytes(row)),
        Kind::V4 => {
            let r = row_bytes(row);
            shake64(&[&[0x00], &(r.len() as u32).to_le_bytes(), &r])
        }
    }
}

fn ref_node(kind: Kind, l: &[u8; 64], r: &[u8; 64]) -> [u8; 64] {
    match kind {
        Kind::V7(_) => fs7::node_hash(l, r),
        Kind::V4 => shake64(&[&[0x01], l, r]),
    }
}

/// All layers of the binary tree over one matrix of power-of-two height, leaves first.
fn ref_layers(kind: Kind, tree: u32, m: &RowMajorMatrix<F>) -> Vec<Vec<[u8; 64]>> {
    let w = m.width;
    let mut layers = vec![m.values.chunks(w).map(|r| ref_leaf(kind, tree, r)).collect::<Vec<_>>()];
    while layers.last().unwrap().len() > 1 {
        let l = layers.last().unwrap();
        layers.push(l.chunks(2).map(|p| ref_node(kind, &p[0], &p[1])).collect());
    }
    layers
}

fn ref_path(layers: &[Vec<[u8; 64]>], mut i: usize) -> Vec<[u8; 64]> {
    let mut out = vec![];
    for l in &layers[..layers.len() - 1] {
        out.push(l[i ^ 1]);
        i >>= 1;
    }
    out
}

/// Reference verifier: recompute the root from a row and its siblings.
fn ref_verify(kind: Kind, tree: u32, root: &[u8; 64], row: &[F], mut i: usize, path: &[[u8; 64]]) -> bool {
    let mut h = ref_leaf(kind, tree, row);
    for s in path {
        h = if i & 1 == 0 { ref_node(kind, &h, s) } else { ref_node(kind, s, &h) };
        i >>= 1;
    }
    &h == root
}

fn matrix(seed: u64, h: usize, w: usize) -> RowMajorMatrix<F> {
    let mut x = seed ^ 0x9e37_79b9_7f4a_7c15;
    let v = (0..h * w)
        .map(|_| {
            x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = x;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            F::from_u64((z ^ (z >> 31)) % crate::field::P)
        })
        .collect();
    RowMajorMatrix::new(v, w)
}

// ---------------------------------------------------------------- driving the real adapter

#[derive(Clone, Copy, Debug)]
enum Stop {
    /// Prover side: the adapter has consumed every slot before round t, a real tree; the next
    /// call is the commitment of tree t.
    Commit(u32),
    /// Verifier side: the first challenge of query round q was drawn (round q has begun); the
    /// next calls check openings of the tree q opens.
    Open(u32),
}

fn table_for(profile: u32) -> Arc<reg7::Table> {
    if profile == fs7::PROFILE_V7 { cert::registered_table(profile, 2048, false) } else { cert::registered_table(profile, 2048, true) }.expect("registered table")
}

/// Advance `reg` (sitting at a round boundary) through the registered table, with registered-
/// length zero bodies and opaque roots, until `stop`.
fn drive(reg: &mut Reg, stop: Stop) {
    loop {
        let next = reg.round() + 1;
        if let Stop::Commit(t) = stop
            && next as u32 == t
        {
            return;
        }
        let def = reg.table().def(next).clone();
        match def.body {
            Body::Real => reg.observe_root([next as u8; 64]),
            Body::Scalar(len) => reg.observe_bytes(&vec![0u8; len]),
        }
        let is_stop = matches!(stop, Stop::Open(q) if q as usize == next);
        let s = &def.shape;
        let mut steps: Vec<Box<dyn Fn(&mut Reg)>> = vec![];
        for &w in &s.widths {
            steps.push(Box::new(move |r: &mut Reg| {
                r.sample_index(w as usize);
            }));
        }
        if s.nq > 0 {
            steps.push(Box::new(|r: &mut Reg| {
                r.sample_fq();
            }));
        }
        if s.theta {
            steps.push(Box::new(|r: &mut Reg| {
                let _ = r.sample_theta();
            }));
        }
        for _ in 0..s.nk {
            steps.push(Box::new(|r: &mut Reg| {
                let _ = r.sample_k();
            }));
        }
        for (j, st) in steps.iter().enumerate() {
            st(reg);
            assert!(reg.error.is_none(), "driver poisoned the adapter: {:?}", reg.error);
            if is_stop && j == 0 {
                return;
            }
        }
    }
}

/// The route the registered table prescribes at a stop.
fn expected_route(t: &reg7::Table, stop: Stop) -> u32 {
    match stop {
        Stop::Commit(t) => t,
        Stop::Open(q) => t.def(q as usize).opens.expect("a query round"),
    }
}

// ---------------------------------------------------------------- jobs

#[derive(Clone, Copy, Debug)]
enum Op {
    /// Commit a fresh matrix, open three rows, verify them with the same MMCS.
    Commit,
    /// Verify reference openings of an older tree against its reference root.
    VerifyOld,
}

#[derive(Clone, Copy, Debug)]
struct Spec {
    kind: Kind,
    stop: Stop,
    op: Op,
    seed: u64,
}

const H: usize = 1 << 11;
const W: usize = 64;

struct Done {
    ok: bool,
    detail: String,
}

/// Run one job: select its route through the real adapter, then hash. Returns the adapter so a
/// caller can keep driving it.
fn run_job(sp: Spec, cell: Arc<AtomicU32>, gate: Arc<Gate>, committed: Option<Arc<AtomicBool>>, then: Option<Stop>) -> Done {
    let (route, mut reg) = match sp.kind {
        Kind::V7(p) => {
            let table = table_for(p);
            let mut reg = Reg::new(table.clone(), format!("route8 statement {p:#x}").as_bytes(), cell.clone());
            drive(&mut reg, sp.stop);
            let want = expected_route(&table, sp.stop);
            let got = cell.load(Ordering::SeqCst);
            if got != want {
                return Done { ok: false, detail: format!("adapter selected route {got}, table prescribes {want}") };
            }
            (want, Some(reg))
        }
        Kind::V4 => (0, None),
    };
    let inner = match sp.kind {
        Kind::V7(p) => Inner::V7(Leaf7 { profile: p, tree: cell.clone(), calls: Arc::new(AtomicU64::new(0)) }),
        Kind::V4 => Inner::V4(ShakeLeaf),
    };
    let node = match sp.kind {
        Kind::V7(_) => NodeAny::V7,
        Kind::V4 => NodeAny::V4,
    };
    let mmcs = HMmcs::new(Pausing { inner, gate }, node, 0);
    let m = matrix(sp.seed, H, W);
    let layers = ref_layers(sp.kind, route, &m);
    let root = *layers.last().unwrap().first().unwrap();
    let dims = [Dimensions { width: W, height: H }];
    let idx = [0usize, H / 2 - 1, H - 1];
    let mut ok = true;
    let mut detail = String::new();
    match sp.op {
        Op::Commit => {
            let (c, pd) = mmcs.commit_matrix(m.clone());
            if let Some(f) = &committed {
                f.store(true, Ordering::SeqCst);
            }
            let got = to_bytes(&c.roots()[0]);
            if got != root {
                ok = false;
                detail += "root differs from the reference; ";
            }
            for &i in &idx {
                let bo = mmcs.open_batch(i, &pd);
                let (ov, proof) = bo.unpack();
                let rp = ref_path(&layers, i);
                if ov.len() != 1 || ov[0] != m.values[i * W..(i + 1) * W] || proof.len() != rp.len() || proof.iter().zip(&rp).any(|(a, b)| to_bytes(a) != *b) {
                    ok = false;
                    detail += &format!("opening {i} differs from the reference; ");
                }
                if !ref_verify(sp.kind, route, &got, &ov[0], i, &proof.iter().map(to_bytes).collect::<Vec<_>>()) {
                    ok = false;
                    detail += &format!("opening {i} fails the reference verifier; ");
                }
                if mmcs.verify_batch(&c, &dims, i, BatchOpeningRef::new(&ov, &proof)).is_err() {
                    ok = false;
                    detail += &format!("opening {i} fails p3 verify_batch; ");
                }
            }
        }
        Op::VerifyOld => {
            let c: MerkleCap<F, [u64; 8]> = MerkleCap::new(vec![to_words(&root)]);
            for &i in &idx {
                let ov = vec![m.values[i * W..(i + 1) * W].to_vec()];
                let proof: Vec<[u64; 8]> = ref_path(&layers, i).iter().map(to_words).collect();
                if mmcs.verify_batch(&c, &dims, i, BatchOpeningRef::new(&ov, &proof)).is_err() {
                    ok = false;
                    detail += &format!("reference opening {i} of tree {route} rejected by p3 verify_batch; ");
                }
            }
        }
    }
    if let (Some(r), Some(s)) = (reg.as_mut(), then) {
        drive(r, s);
    }
    if ok {
        detail = format!("route {route}: root and openings equal the reference");
    }
    Done { ok, detail }
}

fn name(sp: &Spec) -> String {
    let k = match sp.kind {
        Kind::V7(p) if p == fs7::PROFILE_V7 => "QLYAUTH7 0x00070001".to_string(),
        Kind::V7(p) => format!("QLYAUTH7 lab {p:#010x}"),
        Kind::V4 => "QLYAUTH4".to_string(),
    };
    match (sp.kind, sp.stop, sp.op) {
        (Kind::V4, _, Op::Commit) => format!("{k} commit"),
        (Kind::V4, _, Op::VerifyOld) => format!("{k} verify"),
        (_, Stop::Commit(t), _) => format!("{k} commit tree {t}"),
        (_, Stop::Open(q), _) => format!("{k} query round {q} (opens the tree it maps to)"),
    }
}

struct Tally {
    pass: usize,
    total: usize,
}

impl Tally {
    fn check(&mut self, label: &str, ok: bool, detail: &str) {
        self.total += 1;
        self.pass += ok as usize;
        println!("[{}] {label}{}", if ok { "PASS" } else { "FAIL" }, if detail.is_empty() { String::new() } else { format!(": {detail}") });
    }
}

/// Job A pauses before leaf call `pause_at`; job B runs to completion; A resumes.
/// `shared`: both jobs use one routing cell (control). Returns (A, B, route of A's cell at the
/// pause, route of A's cell after B).
fn interleave(a: Spec, b: Spec, shared: bool) -> (Done, Done, u32, u32) {
    let cell_a = Arc::new(AtomicU32::new(0));
    let cell_b = if shared { cell_a.clone() } else { Arc::new(AtomicU32::new(0)) };
    let pause_at = match a.op {
        Op::Commit => H / 2,
        Op::VerifyOld => 1,
    };
    let gate = Gate::new(pause_at);
    let (ca, ga) = (cell_a.clone(), gate.clone());
    let ta = std::thread::spawn(move || run_job(a, ca, ga, None, None));
    assert!(gate.wait_reached(), "job A never reached its pause point");
    let at_pause = cell_a.load(Ordering::SeqCst);
    let db = run_job(b, cell_b, Gate::never(), None, None);
    let after_b = cell_a.load(Ordering::SeqCst);
    gate.release();
    let da = ta.join().expect("job A");
    (da, db, at_pause, after_b)
}

pub fn run() {
    println!("# r3-cert route8: routing invariant of the QLYAUTH7 leaf hasher (review r8 A.2)");
    println!("# matrices of {H} rows x {W} base words (512-byte rows), global rayon pool of {} threads", rayon::current_num_threads());
    let p7 = fs7::PROFILE_V7;
    let lab = reg7::lab_profile(2048);
    let mut t = Tally { pass: 0, total: 0 };

    // 1. Route selection through the real adapter against the registered table.
    println!("## 1. route selected by the adapter at every tree commitment and query round");
    for p in [p7, lab] {
        let table = table_for(p);
        let trees: Vec<u32> = (1..=table.len()).filter(|&r| table.def(r).body == Body::Real).map(|r| r as u32).collect();
        let queries: Vec<(u32, u32)> = (1..=table.len()).filter_map(|r| table.def(r).opens.map(|o| (r as u32, o))).collect();
        let mut seen = vec![];
        for &tr in &trees {
            let cell = Arc::new(AtomicU32::new(0));
            let mut reg = Reg::new(table.clone(), b"route8 selection", cell.clone());
            drive(&mut reg, Stop::Commit(tr));
            seen.push(format!("commit {tr} -> {}", cell.load(Ordering::SeqCst)));
            t.check(&format!("{p:#010x}: before the commitment of tree {tr}, route = {tr}"), cell.load(Ordering::SeqCst) == tr, "");
        }
        for &(q, o) in &queries {
            let cell = Arc::new(AtomicU32::new(0));
            let mut reg = Reg::new(table.clone(), b"route8 selection", cell.clone());
            drive(&mut reg, Stop::Open(q));
            seen.push(format!("query {q} -> {}", cell.load(Ordering::SeqCst)));
            t.check(&format!("{p:#010x}: query round {q} opens tree {o}, route = {o}"), cell.load(Ordering::SeqCst) == o, "");
        }
        let mapping: Vec<(u32, u32)> = queries.clone();
        t.check(&format!("{p:#010x}: registered old-tree mapping is 331->1, 338->330, 345->337, 350->344"), mapping == vec![(331, 1), (338, 330), (345, 337), (350, 344)], &format!("{mapping:?}"));
    }

    // 2. Two concurrent jobs, one routing cell each (the production ownership of cert::B7).
    println!("## 2. forced interleaving: A pauses before a leaf call, B selects another route and hashes, A resumes (one cell per job)");
    let c = |kind, stop, op, seed| Spec { kind, stop, op, seed };
    let pairs: Vec<(Spec, Spec)> = vec![
        (c(Kind::V7(p7), Stop::Commit(1), Op::Commit, 1), c(Kind::V7(lab), Stop::Commit(330), Op::Commit, 2)),
        (c(Kind::V7(p7), Stop::Open(331), Op::VerifyOld, 3), c(Kind::V7(lab), Stop::Open(338), Op::VerifyOld, 4)),
        (c(Kind::V7(p7), Stop::Open(338), Op::VerifyOld, 5), c(Kind::V7(lab), Stop::Open(345), Op::VerifyOld, 6)),
        (c(Kind::V7(p7), Stop::Open(345), Op::VerifyOld, 7), c(Kind::V7(lab), Stop::Open(350), Op::VerifyOld, 8)),
        (c(Kind::V7(p7), Stop::Open(350), Op::VerifyOld, 9), c(Kind::V7(p7), Stop::Commit(1), Op::Commit, 10)),
        (c(Kind::V7(p7), Stop::Commit(337), Op::Commit, 11), c(Kind::V7(p7), Stop::Open(331), Op::VerifyOld, 12)),
        (c(Kind::V7(lab), Stop::Commit(344), Op::Commit, 13), c(Kind::V7(p7), Stop::Open(345), Op::VerifyOld, 14)),
        (c(Kind::V4, Stop::Commit(0), Op::Commit, 15), c(Kind::V7(p7), Stop::Commit(330), Op::Commit, 16)),
        (c(Kind::V7(p7), Stop::Commit(1), Op::Commit, 17), c(Kind::V4, Stop::Commit(0), Op::Commit, 18)),
        (c(Kind::V7(p7), Stop::Open(338), Op::VerifyOld, 19), c(Kind::V4, Stop::Commit(0), Op::VerifyOld, 20)),
    ];
    for (a, b) in &pairs {
        let (da, db, at_pause, after_b) = interleave(*a, *b, false);
        let label = format!("A = {} | B = {}", name(a), name(b));
        let stable = at_pause == after_b;
        t.check(&format!("{label}: A agrees with its reference"), da.ok, &da.detail);
        t.check(&format!("{label}: B agrees with its reference"), db.ok, &db.detail);
        t.check(&format!("{label}: A's route unchanged while paused ({at_pause} -> {after_b})"), stable, "");
    }

    // 3. Control: the same schedule with one cell shared by both jobs must expose the race.
    println!("## 3. control: one routing cell shared by both jobs (not the production design); the harness must see the race");
    for (a, b) in [&pairs[0], &pairs[1], &pairs[3], &pairs[5]] {
        let (da, db, at_pause, after_b) = interleave(*a, *b, true);
        let label = format!("shared cell, A = {} | B = {}", name(a), name(b));
        t.check(&format!("{label}: race detected (A disagrees with its reference after B moved the route {at_pause} -> {after_b})"), !da.ok && at_pause != after_b, &da.detail);
        t.check(&format!("{label}: B itself agrees with its reference"), db.ok, &db.detail);
    }

    // 4. The last worker of a commitment batch: the route cannot change before it joins.
    println!("## 4. the last leaf call of a parallel commitment paused; the driver cannot move the route until it joins");
    {
        let cell = Arc::new(AtomicU32::new(0));
        let gate = Gate::new(H - 1);
        let committed = Arc::new(AtomicBool::new(false));
        let (cc, gg, cf) = (cell.clone(), gate.clone(), committed.clone());
        let sp = c(Kind::V7(p7), Stop::Commit(1), Op::Commit, 21);
        // After the commitment the driver continues to the next tree (route 330), as the prover does.
        let th = std::thread::spawn(move || run_job(sp, cc, gg, Some(cf), Some(Stop::Commit(330))));
        assert!(gate.wait_reached(), "last leaf call never reached");
        let mut stable = true;
        let mut started = 0;
        for _ in 0..5 {
            std::thread::sleep(Duration::from_millis(60));
            stable &= cell.load(Ordering::SeqCst) == 1 && !committed.load(Ordering::SeqCst);
            started = gate.calls.load(Ordering::SeqCst);
        }
        t.check(&format!("while the last call ({}/{H} started) is paused: commit has not returned and the route stays 1 (5 checks over 300 ms)", started), stable && started == H, "");
        gate.release();
        let d = th.join().expect("job");
        t.check("after the worker joins: root and openings equal the reference for (0x00070001, tree 1)", d.ok, &d.detail);
        t.check("only then does the driver move the route to the next tree (330)", cell.load(Ordering::SeqCst) == 330, &format!("route now {}", cell.load(Ordering::SeqCst)));
    }

    // 5. Ownership in production: every certificate job builds its own cell.
    println!("## 5. ownership: cert::B7::new builds one routing cell per certificate");
    {
        let table = table_for(p7);
        let b1 = cert::B7::new(2048, p7, b"job one", false, crate::pcs::Inject::Off, Some(table.clone()));
        let b2 = cert::B7::new(2048, p7, b"job two", false, crate::pcs::Inject::Off, Some(table));
        t.check("two B7 instances do not share a routing cell", !Arc::ptr_eq(&b1.tr.ch.tree, &b2.tr.ch.tree), "");
        t.check("a fresh B7 starts with route 1 (round 1 is the initial tree)", b1.tr.ch.tree.load(Ordering::SeqCst) == 1, "");
    }

    let _ = F::ZERO;
    println!("ROUTE8 SUMMARY: {}/{} checks behave as expected", t.pass, t.total);
}
