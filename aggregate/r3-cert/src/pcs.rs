//! The WHIR backend (p3-whir 0.8.0, Goldilocks^5, SHAKE256-64 Merkle framing, JohnsonBound 272,
//! no grinding) and the single SHAKE256 Fiat-Shamir transcript shared by the frontend and WHIR.
//! Hasher framing is the r2-whir harness's: leaf 0x00 || LE32(len) || row, node 0x01 || L || R,
//! sponge SHAKE256(0x02 || buffer).

use p3_challenger::{CanObserve, CanSample, FieldChallenger, HashChallenger, SerializingChallenger64};
use p3_commit::Mmcs;
use p3_dft::Radix2DFTSmallBatch;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{CryptographicHasher, Hash, PseudoCompressionFunction};
use p3_sumcheck::layout::SuffixProver;
use p3_whir::parameters::{FoldingFactor, ProtocolParameters, SecurityAssumption, WhirConfig};
use p3_whir::pcs::prover::WhirProver;
use sha3::Shake256;
use sha3::digest::{ExtendableOutput, Update, XofReader};

use crate::field::{EF, F};

pub fn shake64(parts: &[&[u8]]) -> [u8; 64] {
    let mut h = Shake256::default();
    for p in parts {
        h.update(p);
    }
    let mut out = [0u8; 64];
    h.finalize_xof().read(&mut out);
    out
}

fn bytes_to_words(b: [u8; 64]) -> [u64; 8] {
    core::array::from_fn(|i| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap()))
}

pub fn words_to_bytes(w: &[u64; 8]) -> [u8; 64] {
    let mut b = [0u8; 64];
    for (i, x) in w.iter().enumerate() {
        b[8 * i..8 * i + 8].copy_from_slice(&x.to_le_bytes());
    }
    b
}

#[derive(Clone, Default)]
pub struct ShakeLeaf;
impl CryptographicHasher<F, [u64; 8]> for ShakeLeaf {
    fn hash_iter<I: IntoIterator<Item = F>>(&self, input: I) -> [u64; 8] {
        let mut row = Vec::with_capacity(512);
        for x in input {
            row.extend_from_slice(&x.as_canonical_u64().to_le_bytes());
        }
        let len = (row.len() as u32).to_le_bytes();
        bytes_to_words(shake64(&[&[0x00], &len, &row]))
    }
}

#[derive(Clone, Default)]
pub struct ShakeNode;
impl PseudoCompressionFunction<[u64; 8], 2> for ShakeNode {
    fn compress(&self, input: [[u64; 8]; 2]) -> [u64; 8] {
        bytes_to_words(shake64(&[&[0x01], &words_to_bytes(&input[0]), &words_to_bytes(&input[1])]))
    }
}

#[derive(Clone, Default)]
pub struct ShakeFs;
impl CryptographicHasher<u8, [u8; 64]> for ShakeFs {
    fn hash_iter<I: IntoIterator<Item = u8>>(&self, input: I) -> [u8; 64] {
        let buf: Vec<u8> = input.into_iter().collect();
        shake64(&[&[0x02], &buf])
    }
}

pub type MyMmcs = MerkleTreeMmcs<F, u64, ShakeLeaf, ShakeNode, 2, 8>;
pub type MyChallenger = SerializingChallenger64<F, HashChallenger<u8, ShakeFs, 64>>;
pub type Layout = SuffixProver<F, EF>;
pub type Dft = Radix2DFTSmallBatch<F>;
pub type Pcs = WhirProver<EF, F, Dft, MyMmcs, MyChallenger, Layout>;
pub type Commitment = <MyMmcs as Mmcs<F>>::Commitment;
pub type PcsProof = p3_whir::PcsProof<F, EF, MyMmcs>;

/// The WHIR profile per committed domain size: (start rate, round rates, folding factors).
/// 2^20, 2^22, 2^24 are the r2-whir measured profiles; 2^21 is the same family.
pub fn profile(num_vars: usize) -> (usize, Vec<usize>, Vec<usize>) {
    match num_vars {
        20 => (4, vec![7, 9], vec![6, 4, 4]),
        21 => (4, vec![7, 9], vec![6, 5, 4]),
        22 => (4, vec![7, 9, 11], vec![6, 4, 4, 4]),
        23 => (4, vec![7, 9, 11], vec![6, 5, 4, 4]),
        24 => (4, vec![7, 9, 11], vec![6, 5, 5, 4]),
        v => panic!("no WHIR profile for 2^{v} cells"),
    }
}

pub fn make_pcs(num_vars: usize, claims: usize) -> (Pcs, usize) {
    make_pcs_from(num_vars, claims, profile(num_vars))
}

/// A profile outside the registry (soundness test of profile binding only): the last two
/// folding factors exchanged.
pub fn make_pcs_alt(num_vars: usize, claims: usize) -> (Pcs, usize) {
    let (start, rounds, mut folds) = profile(num_vars);
    let k = folds.len();
    folds.swap(k - 1, k - 2);
    if folds == profile(num_vars).2 {
        folds[0] -= 1;
        folds[k - 1] += 1;
    }
    make_pcs_from(num_vars, claims, (start, rounds, folds))
}

fn make_pcs_from(num_vars: usize, claims: usize, prof: (usize, Vec<usize>, Vec<usize>)) -> (Pcs, usize) {
    let (start, rounds, folds) = prof;
    let params = ProtocolParameters {
        starting_log_inv_rate: start,
        round_log_inv_rates: rounds,
        folding_factor: FoldingFactor::PerRound(folds),
        soundness_type: SecurityAssumption::JohnsonBound,
        security_level: target_for(num_vars),
        pow_bits: 0,
    };
    let config = WhirConfig::<EF, F, MyChallenger>::new_with_initial_claims(num_vars, params, claims).expect("WHIR config");
    let fold0 = config.folding_schedule()[0];
    let dft = Dft::new(1 << config.max_fft_size());
    (Pcs::new(config, dft, MyMmcs::new(ShakeLeaf, ShakeNode, 0)), fold0)
}

/// Per-term planner target of the JohnsonBound profiles: 272, as in every registered profile.
pub fn target_for(_num_vars: usize) -> usize {
    272
}

/// Soundness regime and per-term planner target of a PCS.
#[derive(Clone, Copy, Debug)]
pub struct Sec {
    pub assumption: SecurityAssumption,
    pub target: usize,
}

impl Sec {
    /// JohnsonBound at the round-10 target for this dimension (classical figures).
    pub fn johnson(num_vars: usize) -> Self {
        Sec { assumption: SecurityAssumption::JohnsonBound, target: target_for(num_vars) }
    }
    /// The proven unique-decoding regime (list size 1, no OOD samples) at per-term target 286,
    /// the quantum-ready round-10 lab family.
    pub fn unique() -> Self {
        Sec { assumption: SecurityAssumption::UniqueDecoding, target: 286 }
    }
}

fn params_of(prof: (usize, Vec<usize>, Vec<usize>), sec: Sec) -> ProtocolParameters {
    let (start, rounds, folds) = prof;
    ProtocolParameters {
        starting_log_inv_rate: start,
        round_log_inv_rates: rounds,
        folding_factor: FoldingFactor::PerRound(folds),
        soundness_type: sec.assumption,
        security_level: sec.target,
        pow_bits: 0,
    }
}

/// A PCS with an explicit (start rate, round rates, folds) schedule (hidden-u lab sizes above
/// 2^24 and the schedule benchmark). The registered profiles above are unchanged.
pub fn make_pcs_prof(num_vars: usize, claims: usize, prof: (usize, Vec<usize>, Vec<usize>)) -> (Pcs, usize) {
    make_pcs_prof_sec(num_vars, claims, prof, Sec::johnson(num_vars))
}

pub fn make_pcs_prof_sec(num_vars: usize, claims: usize, prof: (usize, Vec<usize>, Vec<usize>), sec: Sec) -> (Pcs, usize) {
    let config = WhirConfig::<EF, F, MyChallenger>::new_with_initial_claims(num_vars, params_of(prof, sec), claims).expect("WHIR config");
    let fold0 = config.folding_schedule()[0];
    let dft = Dft::new(1 << config.max_fft_size());
    (Pcs::new(config, dft, MyMmcs::new(ShakeLeaf, ShakeNode, 0)), fold0)
}

/// The QLYAUTH7-style PCS (global Merkle oracle, registered-round adapter) with an explicit
/// schedule.
pub fn make_pcs7_prof(num_vars: usize, claims: usize, prof: (usize, Vec<usize>, Vec<usize>), profile_id: u32, tree: std::sync::Arc<std::sync::atomic::AtomicU32>, leaf_calls: std::sync::Arc<std::sync::atomic::AtomicU64>) -> (Pcs7, usize) {
    make_pcs7_prof_sec(num_vars, claims, prof, Sec::johnson(num_vars), profile_id, tree, leaf_calls)
}

#[allow(clippy::too_many_arguments)]
pub fn make_pcs7_prof_sec(num_vars: usize, claims: usize, prof: (usize, Vec<usize>, Vec<usize>), sec: Sec, profile_id: u32, tree: std::sync::Arc<std::sync::atomic::AtomicU32>, leaf_calls: std::sync::Arc<std::sync::atomic::AtomicU64>) -> (Pcs7, usize) {
    let config = WhirConfig::<EF, F, crate::reg7::Reg>::new_with_initial_claims(num_vars, params_of(prof, sec), claims).expect("WHIR config");
    let fold0 = config.folding_schedule()[0];
    let dft = Dft::new(1 << config.max_fft_size());
    let leaf = crate::reg7::Leaf7 { profile: profile_id, tree, calls: leaf_calls };
    // Round-10 lab profiles (0xfff910xx .. 0xfff913xx) separate the trees in the node hash too.
    let node = if crate::hidden::is_r10(profile_id) { crate::reg7::Node7::tagged(profile_id, leaf.tree.clone()) } else { crate::reg7::Node7::default() };
    (Pcs7::new(config, dft, crate::reg7::Mmcs7::new(leaf, node, 0)), fold0)
}

/// The round-10 lab PCS: the registered-round adapter and the per-operation tree context
/// commitment scheme (`mmcs10`).
pub type Pcs10 = WhirProver<EF, F, Dft, crate::mmcs10::Mmcs10, crate::reg7::Reg, Layout>;
pub type PcsProof10 = p3_whir::PcsProof<F, EF, crate::mmcs10::Mmcs10>;

#[allow(clippy::too_many_arguments)]
pub fn make_pcs10(num_vars: usize, claims: usize, prof: (usize, Vec<usize>, Vec<usize>), sec: Sec, profile_id: u32, tree: std::sync::Arc<std::sync::atomic::AtomicU32>, roots: crate::mmcs10::Roots, leaf_calls: std::sync::Arc<std::sync::atomic::AtomicU64>) -> (Pcs10, usize) {
    let config = WhirConfig::<EF, F, crate::reg7::Reg>::new_with_initial_claims(num_vars, params_of(prof, sec), claims).expect("WHIR config");
    let fold0 = config.folding_schedule()[0];
    let dft = Dft::new(1 << config.max_fft_size());
    let m = crate::mmcs10::Mmcs10 { profile: profile_id, cell: tree, roots, calls: leaf_calls };
    (Pcs10::new(config, dft, m), fold0)
}

/// Profile 0x00070001: the same WHIR configuration, the global Merkle oracle framing (§3.1) and
/// the registered-round adapter as challenger. `tree` is the adapter's routing cell.
pub type Pcs7 = WhirProver<EF, F, Dft, crate::reg7::Mmcs7, crate::reg7::Reg, Layout>;
pub type PcsProof7 = p3_whir::PcsProof<F, EF, crate::reg7::Mmcs7>;

pub fn make_pcs7(num_vars: usize, claims: usize, alt: bool, profile_id: u32, tree: std::sync::Arc<std::sync::atomic::AtomicU32>, leaf_calls: std::sync::Arc<std::sync::atomic::AtomicU64>) -> (Pcs7, usize) {
    let (start, rounds, mut folds) = profile(num_vars);
    if alt {
        let k = folds.len();
        folds.swap(k - 1, k - 2);
        if folds == profile(num_vars).2 {
            folds[0] -= 1;
            folds[k - 1] += 1;
        }
    }
    let params = ProtocolParameters {
        starting_log_inv_rate: start,
        round_log_inv_rates: rounds,
        folding_factor: FoldingFactor::PerRound(folds),
        soundness_type: SecurityAssumption::JohnsonBound,
        security_level: 272,
        pow_bits: 0,
    };
    let config = WhirConfig::<EF, F, crate::reg7::Reg>::new_with_initial_claims(num_vars, params, claims).expect("WHIR config");
    let fold0 = config.folding_schedule()[0];
    let dft = Dft::new(1 << config.max_fft_size());
    let leaf = crate::reg7::Leaf7 { profile: profile_id, tree, calls: leaf_calls };
    let node = if crate::hidden::is_r10(profile_id) { crate::reg7::Node7::tagged(profile_id, leaf.tree.clone()) } else { crate::reg7::Node7::default() };
    (Pcs7::new(config, dft, crate::reg7::Mmcs7::new(leaf, node, 0)), fold0)
}

/// Test-only replacement of the Gruen round challenges (GKR rounds and betas, table rounds).
/// The challenger is still sampled, so the sponge state and every other challenge follow the
/// protocol. `Off` is the protocol.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub enum Inject {
    #[default]
    Off,
    Zero,
    One,
    Half,
    /// r = (1 - x) / (1 - 2x): eq1(x, r) = 0 at every round (betas stay random).
    EqZero,
    /// Every round challenge and beta equals v = (1 + i) / 2 with i^2 = -1 in F_p, so
    /// eq1(v, v) = 0 and every accumulated eq(x, r) of a layer is zero.
    Vroot,
}

/// v = (1 + i) / 2 with i a primitive fourth root of unity of Goldilocks.
pub fn vroot() -> EF {
    use p3_field::{Field, TwoAdicField};
    let i = F::two_adic_generator(2);
    EF::from((F::ONE + i) * F::TWO.inverse())
}

/// The frontend's transcript calls, shared by the QLYAUTH4 sponge (`Tr`) and the QLYAUTH7
/// registered-round adapter (`reg7::Tr7`).
pub trait Fs {
    fn absorb_ef(&mut self, x: EF);
    fn sample_ef(&mut self) -> EF;
    fn inject(&self) -> Inject;
    fn absorb_efs(&mut self, xs: &[EF]) {
        for &x in xs {
            self.absorb_ef(x);
        }
    }
    fn sample_efs(&mut self, n: usize) -> Vec<EF> {
        (0..n).map(|_| self.sample_ef()).collect()
    }
    /// A Gruen round challenge; `x` is the claim coordinate of the round variable (None for a
    /// beta). Identical to sample_ef unless a test injection is set (the transcript is still
    /// sampled, so its state and every other challenge follow the protocol).
    fn sample_round(&mut self, x: Option<EF>) -> EF {
        let s = self.sample_ef();
        inject_value(self.inject(), s, x)
    }
}

pub fn inject_value(inject: Inject, s: EF, x: Option<EF>) -> EF {
    use p3_field::Field;
    match inject {
        Inject::Off => s,
        Inject::Zero => EF::ZERO,
        Inject::One => EF::ONE,
        Inject::Half => EF::TWO.inverse(),
        Inject::EqZero => match x {
            Some(x) if x.double() != EF::ONE => (EF::ONE - x) * (EF::ONE - x.double()).inverse(),
            _ => s,
        },
        Inject::Vroot => vroot(),
    }
}

impl Fs for Tr {
    fn absorb_ef(&mut self, x: EF) {
        Tr::absorb_ef(self, x)
    }
    fn sample_ef(&mut self) -> EF {
        Tr::sample_ef(self)
    }
    fn inject(&self) -> Inject {
        self.inject
    }
}

/// The one Fiat-Shamir transcript: the frontend absorbs and samples through the same SHAKE256
/// challenger that WHIR continues.
pub struct Tr {
    pub ch: MyChallenger,
    pub inject: Inject,
}

impl Tr {
    pub fn new() -> Self {
        Tr { ch: SerializingChallenger64::new(HashChallenger::new(b"qlyphs-r3-cert-v1".to_vec(), ShakeFs)), inject: Inject::Off }
    }
    /// Absorb a byte string as a domain-separated 64-byte SHAKE256 digest.
    pub fn absorb_bytes(&mut self, tag: &[u8], data: &[u8]) {
        let d = shake64(&[b"r3-cert/absorb", &(tag.len() as u32).to_le_bytes(), tag, &(data.len() as u64).to_le_bytes(), data]);
        self.ch.observe(Hash::<F, u8, 64>::from(d));
    }
    pub fn absorb_u64(&mut self, x: u64) {
        assert!(x < crate::field::P);
        self.ch.observe(F::from_u64(x));
    }
    pub fn absorb_ef(&mut self, x: EF) {
        self.ch.observe_algebra_element(x);
    }
    pub fn absorb_efs(&mut self, xs: &[EF]) {
        for &x in xs {
            self.absorb_ef(x);
        }
    }
    pub fn sample_ef(&mut self) -> EF {
        self.ch.sample_algebra_element()
    }
    pub fn sample_efs(&mut self, n: usize) -> Vec<EF> {
        (0..n).map(|_| self.sample_ef()).collect()
    }
    /// theta uniform in K \ F_p: exact rejection of samples whose four non-constant coordinates are zero.
    pub fn sample_theta(&mut self) -> (EF, usize) {
        let mut rejected = 0;
        loop {
            let t = self.sample_ef();
            if <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&t)[1..].iter().any(|c| *c != F::ZERO) {
                return (t, rejected);
            }
            rejected += 1;
        }
    }
    /// A 64-byte seed made of eight canonical Goldilocks samples.
    pub fn sample_seed(&mut self) -> [u8; 64] {
        let mut s = [0u8; 64];
        for i in 0..8 {
            let x: F = self.ch.sample();
            s[8 * i..8 * i + 8].copy_from_slice(&x.as_canonical_u64().to_le_bytes());
        }
        s
    }
}

impl Default for Tr {
    fn default() -> Self {
        Self::new()
    }
}
