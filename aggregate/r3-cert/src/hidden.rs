//! Hidden-u certificate (round 9, build 2): the public U_i = w1Encode(u_i) is removed, c_tilde_i
//! (64 bytes) becomes public, and c_tilde_i = SHAKE256(mu_i || U_i, 64) is proven inside the same
//! proof, over one WHIR commitment shared with the ML-DSA frontend. Lab profiles 0xfff900xx only:
//! the chain verifier never accepts them.
//!
//! Committed witness (table A, 15 columns of 2^log_dc cells, cell i * 2048 + t):
//!   X, Y, S                the existing ML-DSA columns;
//!   B0, B1, B2, B3         the four bit planes of u, u_t = B0 + 2 B1 + 4 B2 + 8 B3;
//!   T1 .. T8               the sponge states after permutations 1..8, +-1 encoded on the 1600
//!                          state cells (cell 64 (x + 5 y) + z), 0 on the 448 padding cells;
//! table B: m_even, m_odd (the 2^20-entry multiplicity table, unchanged).
//!
//! The ML-DSA frontend keeps the LogUp tree, the table link and the integer lifts. The region
//! coefficients become polynomials in d0 = prod (1 - Bj) and d15 = prod Bj, the u term of the
//! modular relation moves into the witness through r' = ctr(alpha eta a mod q), and Booleanity of
//! the bits joins the ternarity zerocheck. The master sumcheck has degree 8.
//!
//! The hash side is one data-parallel Keccak-f[1600] GKR (keccak.rs layers) over 16 N slots,
//! slot p = 16 i + q: slot q < 9 of signature i is permutation q + 1 of its sponge, slots 9..15 are
//! the field-zero vector, a fixed point of every layer. Its links to the committed witness are
//! sumchecks, never products of multilinear evaluations:
//!   output: a fixed mask keeps every cell of slots 0..7 and the 512 c_tilde cells of slot 8; the
//!           masked output is (T_{q+1}) for q < 8 and the public c_tilde for q = 8;
//!   input:  in_q = S_q (x) block_q with S_0 = 0, the message bits taken from mu (public) and from
//!           the committed bit planes through a wiring sumcheck, and the fixed SHAKE256 padding
//!           block on slot 8; capacity cells carry S_q unchanged.

use std::sync::Arc;
use std::sync::atomic::{AtomicU32, AtomicU64};
use std::time::Instant;

use p3_field::{Field, PrimeCharacteristicRing, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;
use p3_multilinear_util::point::Point;
use p3_sumcheck::layout::{Layout as _, Table, observe_commitment};
use p3_sumcheck::{OpeningBatch, OpeningProtocol, TableShape, TableSpec};
use p3_symmetric::MerkleCap;
use rayon::prelude::*;

use crate::cert::{self, Backend, ProjSrc, Reject, Timer, Tree, Witness3, LOG_TAB, MANIFEST, NU_MAX};
use crate::field::{EF, F, efb, eq_pts, eq_table, fi, lagrange};
use crate::fs7::{self, Shape};
use crate::gkr::{self, GkrProof, Layer};
use crate::keccak::{self, LOGW, STATE, W};
use crate::mlnat::{self, A2, K, L, N, Ntt, Poly, QI, Record, ctr, red};
use crate::pcs::{self, Commitment, Fs, Layout, words_to_bytes};
use crate::proj::{self, CHUNK, Challenges, TRIALS};
use crate::reg7::{self, Body, RoundDef};
use crate::region::{self, XK, XOFF};
use crate::sumcheck;
use crate::witness::{self, SLOTS, Witness};

// ---------------------------------------------------------------- constants and profiles

/// SHAKE256 rate in bytes.
pub const RATE: usize = 136;
/// Permutations per signature: |mu || U| = 1088 = 8 * 136 fills eight blocks, padding is a ninth.
pub const NPERM: usize = 9;
/// Permutation-slot bits per signature (16 slots, 9 real).
pub const LOGQ: usize = 4;
/// Committed columns of table A.
pub const NCOL: usize = 15;
pub const COL_B: usize = 3;
pub const COL_T: usize = 7;
/// Rate cells (1088 bits) and the c_tilde prefix (512 bits).
pub const RATE_BITS: usize = 8 * RATE;
pub const CT_BITS: usize = 512;
/// Opened values in the one WHIR proof: master 7, masked-output T 8, input-link T 8, bit wiring 4,
/// table 2.
pub const NCLAIMS: usize = 29;
pub const NBATCH: usize = 5;
/// Bit-wiring domain: 4 planes x 2048 coefficients.
pub const LOG_BW: usize = 13;

/// Round-10 lab families. Johnson: JohnsonBound WHIR (classical figures, one OOD sample per
/// commitment). Unique: the proven unique-decoding regime (list size 1, no OOD samples, per-term
/// target 286), the quantum-ready family.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fam {
    Johnson,
    Unique,
}

/// The family the lab commands and tests use (H9_FAMILY=ud selects Unique; default Johnson).
static FAMILY: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

pub fn set_family(f: Fam) {
    FAMILY.store(if f == Fam::Unique { 2 } else { 1 }, std::sync::atomic::Ordering::Relaxed);
}

pub fn family() -> Fam {
    match FAMILY.load(std::sync::atomic::Ordering::Relaxed) {
        0 => {
            let f = if std::env::var("H9_FAMILY").map(|v| v == "ud").unwrap_or(false) { Fam::Unique } else { Fam::Johnson };
            set_family(f);
            f
        }
        2 => Fam::Unique,
        _ => Fam::Johnson,
    }
}

/// Lab profile ids (round 10), never accepted by the chain verifier: 0xfff91000 | log2 N
/// (Johnson) and 0xfff91200 | log2 N (unique decoding). Round 10 replaces the round-9 ids
/// 0xfff900xx / 0xfff901xx on this branch: it scales the F_q pool slack with N and rejects a
/// short pool, separates the committed trees in the Merkle node hash, and registers N = 32 ..
/// 65536.
pub fn lab_profile9(n: usize) -> u32 {
    (if family() == Fam::Unique { 0xfff9_1200 } else { 0xfff9_1000 }) | n.trailing_zeros()
}

/// Lab chain profile ids (round 10): 0xfff91100 | log2 N (Johnson), 0xfff91300 | log2 N
/// (unique decoding).
pub fn lab_chain_profile9(n: usize) -> u32 {
    lab_profile9(n) | 0x100
}

/// Round-10 lab profile ids (standalone or chain, either family).
pub fn is_r10(profile: u32) -> bool {
    profile & 0xffff_fc00 == 0xfff9_1000 && profile & 0xff <= 31
}

pub fn fam_of(profile: u32) -> Fam {
    if profile & 0x200 != 0 { Fam::Unique } else { Fam::Johnson }
}

/// Manifest magics of the current family: (standalone, chain).
pub fn magics() -> (&'static [u8; 8], &'static [u8; 8]) {
    if family() == Fam::Unique { (b"QLYLB10Q", b"QLYLB10R") } else { (b"QLYLB10H", b"QLYLB10C") }
}

/// Largest registered N.
pub const MAX_N: usize = 65536;

pub fn stacked_vars9(n: usize) -> usize {
    (NCOL * n * SLOTS + (2 << LOG_TAB)).next_power_of_two().trailing_zeros() as usize
}

/// Variables of the Keccak batch: 11 cell bits, 4 slot bits, log2 N signature bits.
pub fn nvk(n: usize) -> usize {
    LOGW + LOGQ + n.trailing_zeros() as usize
}

// ---------------------------------------------------------------- sponge trace (native)

/// The nine absorbed blocks of SHAKE256(mu || U, 64): eight message blocks and the padding block.
pub fn absorb_blocks(mu: &[u8; 64], ubytes: &[u8]) -> [[u8; RATE]; NPERM] {
    assert_eq!(ubytes.len(), K * N / 2);
    let mut msg = Vec::with_capacity(8 * RATE);
    msg.extend_from_slice(mu);
    msg.extend_from_slice(ubytes);
    let mut b = [[0u8; RATE]; NPERM];
    for q in 0..8 {
        b[q].copy_from_slice(&msg[q * RATE..(q + 1) * RATE]);
    }
    b[8] = pad_block(0x1f);
    b
}

/// The padding block of a message whose length is a multiple of the rate, for a domain suffix
/// byte (0x1f for SHAKE, 0x06 for SHA3).
pub fn pad_block(suffix: u8) -> [u8; RATE] {
    let mut p = [0u8; RATE];
    p[0] = suffix;
    p[RATE - 1] |= 0x80;
    p
}

/// states[q] = S_{q+1} = f(S_q xor block_q), S_0 = 0.
pub fn run_trace(blocks: &[[u8; RATE]; NPERM]) -> [[u64; 25]; NPERM] {
    let mut s = [0u64; 25];
    let mut out = [[0u64; 25]; NPERM];
    for q in 0..NPERM {
        xor_block(&mut s, &blocks[q]);
        ::keccak::f1600(&mut s);
        out[q] = s;
    }
    out
}

pub fn xor_block(s: &mut [u64; 25], b: &[u8; RATE]) {
    for l in 0..RATE / 8 {
        s[l] ^= u64::from_le_bytes(b[8 * l..8 * l + 8].try_into().unwrap());
    }
}

/// The first 64 output bytes of a state.
pub fn squeeze64(s: &[u64; 25]) -> [u8; 64] {
    let mut o = [0u8; 64];
    for l in 0..8 {
        o[8 * l..8 * l + 8].copy_from_slice(&s[l].to_le_bytes());
    }
    o
}

/// Bit of a state at cell s = 64 lane + z.
#[inline(always)]
pub fn state_bit(st: &[u64; 25], s: usize) -> u64 {
    (st[s / 64] >> (s % 64)) & 1
}

/// +-1 encoding of a bit.
#[inline(always)]
fn pm(bit: u64) -> F {
    if bit == 1 { -F::ONE } else { F::ONE }
}

/// Where absorbed bit (block q, rate cell s) lives: a byte of mu, or bit (plane, coefficient) of
/// u. Rate byte b = s / 8, bit beta = s % 8, absorbed byte a = 136 q + b; U byte j = a - 64 holds
/// u_{2j} in its low nibble and u_{2j+1} in its high nibble (w1Encode).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Src {
    Mu(usize, usize),
    U { plane: usize, coef: usize },
    None,
}

pub fn src_of(q: usize, s: usize) -> Src {
    if q >= 8 || s >= RATE_BITS {
        return Src::None;
    }
    let (b, beta) = (s / 8, s % 8);
    let a = RATE * q + b;
    if a < 64 {
        Src::Mu(a, beta)
    } else {
        let j = a - 64;
        Src::U { plane: beta & 3, coef: 2 * j + (beta >> 2) }
    }
}

/// The inverse map: (plane, coefficient) -> (q, s). It is a bijection onto the U positions.
pub fn upos_of(plane: usize, coef: usize) -> (usize, usize) {
    let j = coef / 2;
    let beta = (coef & 1) * 4 + plane;
    let a = 64 + j;
    (a / RATE, 8 * (a % RATE) + beta)
}

/// Padding bit of rate cell s of the final block.
fn pad_bit(s: usize) -> u64 {
    let p = pad_block(0x1f);
    ((p[s / 8] >> (s % 8)) & 1) as u64
}

// ---------------------------------------------------------------- prover inputs and witness

/// What a signer hands to the hidden-u prover: z, u and the published c_tilde.
#[derive(Clone)]
pub struct SigIn9 {
    pub z: Vec<i64>,
    pub u: Vec<u8>,
    pub ct: [u8; 64],
}

pub fn input_from_raw9(ntt: &Ntt, rec: &Record, sig: &[u8]) -> SigIn9 {
    let w = witness::input_from_raw(ntt, rec, sig);
    let (ct, _, _) = mlnat::decode_sig(sig).expect("signature decodes");
    SigIn9 { z: w.z, u: w.u, ct }
}

/// Per-signature public data the prover and verifier derive: A_hat and b = c 2^13 t1 (no u term).
pub struct Pub9 {
    pub a_hat: Vec<Poly>,
    pub bc: Vec<u32>,
    pub mu: [u8; 64],
}

pub fn derive_public9(ntt: &Ntt, rec: &Record, ct: &[u8; 64]) -> Pub9 {
    let (rho, _) = mlnat::decode_pk(&rec.pk);
    let a_hat = mlnat::expand_a(&rho);
    let bc = mlnat::b_of(ntt, &rec.pk, ct);
    let mu = mlnat::mu_of(&mlnat::tr_of(&rec.pk), &rec.ctx, &rec.msg);
    Pub9 { a_hat, bc, mu }
}

/// The prover's full witness. Soundness tests mutate the public fields after `build9`.
pub struct Wit9 {
    pub w: Witness,
    /// Bit planes, cell i * 2048 + t.
    pub bits: [Vec<F>; 4],
    /// Per signature: the absorbed blocks and the nine states the prover uses for the Keccak
    /// trace (the input of slot q is states[q - 1] xor blocks[q]).
    pub blocks: Vec<[[u8; RATE]; NPERM]>,
    pub states: Vec<[[u64; 25]; NPERM]>,
    /// Per signature: the committed states T1..T8 (normally states[0..8]).
    pub t_states: Vec<[[u64; 25]; 8]>,
    /// Field overrides of committed T cells: (signature, state index 0..8, cell, value).
    pub t_extra: Vec<(usize, usize, usize, F)>,
    /// Field overrides of Keccak input-row cells: (slot p = 16 i + q, cell, value).
    pub in_extra: Vec<(usize, usize, F)>,
    /// Published c_tilde.
    pub ct: Vec<[u8; 64]>,
}

/// Build the witness. The arithmetic uses (z, u, c_tilde); the trace uses mu || w1Encode(u).
pub fn build9(ntt: &Ntt, records: &[Record], inputs: &[SigIn9]) -> (Wit9, Vec<Pub9>) {
    let n = records.len();
    let d = n * SLOTS;
    let per: Vec<(Pub9, Vec<i32>)> = records
        .par_iter()
        .zip(inputs.par_iter())
        .map(|(rec, inp)| {
            let p = derive_public9(ntt, rec, &inp.ct);
            let bu: Vec<u32> = (0..K * N).map(|t| red(p.bc[t] as u64 + A2 as u64 * inp.u[t] as u64)).collect();
            let w = mlnat::w_approx(ntt, &p.a_hat, &inp.z, &bu);
            (p, w.iter().map(|&v| ctr(v) as i32).collect())
        })
        .collect();
    let mut x = vec![F::ZERO; d];
    let mut y = vec![F::ZERO; d];
    let mut s = vec![F::ZERO; d];
    let mut zi = vec![0i32; d];
    let mut ei = vec![0i32; d];
    let mut class = vec![0u8; d];
    let mut counts = vec![0u8; n];
    let mut viol = witness::Violations::default();
    let mut bits: [Vec<F>; 4] = core::array::from_fn(|_| vec![F::ZERO; d]);
    for (i, ((_, e), inp)) in per.iter().zip(inputs).enumerate() {
        let base = i * SLOTS;
        for t in 0..L * N {
            let zz = inp.z[t];
            if zz.abs() >= mlnat::ZB {
                viol.z_out_of_range += 1;
            }
            x[base + t] = fi(zz + XOFF);
            zi[base + t] = zz as i32;
        }
        let mut hints = 0usize;
        for t in 0..K * N {
            let c = region::class_of(inp.u[t]);
            let ee = e[t] as i64;
            if !region::in_region(c, ee) {
                viol.e_out_of_region += 1;
            }
            let sel = region::selector_of(c, ee);
            hints += (sel * sel) as usize;
            s[base + t] = fi(sel);
            y[base + t] = fi(ee - region::start_int(c, sel));
            ei[base + t] = ee as i32;
            class[base + t] = c as u8;
            for (j, b) in bits.iter_mut().enumerate() {
                b[base + t] = F::from_u8((inp.u[t] >> j) & 1);
            }
        }
        viol.max_hints = viol.max_hints.max(hints);
        if hints > mlnat::OMEGA {
            viol.sigs_over_omega += 1;
        }
        counts[i] = hints.min(255) as u8;
    }
    let m = witness::multiplicities(&x, &y, &s, &class, n);
    let blocks: Vec<[[u8; RATE]; NPERM]> = per.par_iter().zip(inputs.par_iter()).map(|((p, _), inp)| absorb_blocks(&p.mu, &mlnat::w1_encode(&inp.u))).collect();
    let states: Vec<[[u64; 25]; NPERM]> = blocks.par_iter().map(run_trace).collect();
    let t_states = states.iter().map(|s| core::array::from_fn(|k| s[k])).collect();
    let w = Witness { n, x, y, s, zi, ei, class, m, counts, viol };
    let ct = inputs.iter().map(|i| i.ct).collect();
    (Wit9 { w, bits, blocks, states, t_states, t_extra: vec![], in_extra: vec![], ct }, per.into_iter().map(|(p, _)| p).collect())
}

/// Recount the multiplicities after a test mutation of X, Y, S or the classes.
pub fn recount(w: &mut Wit9) {
    w.w.m = witness::multiplicities(&w.w.x, &w.w.y, &w.w.s, &w.w.class, w.w.n);
}

/// Committed T columns (8 columns of 2^log_dc cells).
fn t_columns(wit: &Wit9) -> Vec<Vec<F>> {
    let n = wit.w.n;
    let mut cols: Vec<Vec<F>> = (0..8).map(|_| vec![F::ZERO; n * SLOTS]).collect();
    for (k, col) in cols.iter_mut().enumerate() {
        col.par_chunks_mut(SLOTS).enumerate().for_each(|(i, row)| {
            let st = &wit.t_states[i][k];
            for s in 0..STATE {
                row[s] = pm(state_bit(st, s));
            }
        });
    }
    for &(i, k, s, v) in &wit.t_extra {
        cols[k][i * SLOTS + s] = v;
    }
    cols
}

/// Keccak input rows, slot p = 16 i + q: S_q xor block_q (S_0 = 0) for q < 9, zero rows else.
fn input_rows(wit: &Wit9) -> Vec<F> {
    let n = wit.w.n;
    let mut v = vec![F::ZERO; 16 * n * W];
    v.par_chunks_mut(16 * W).enumerate().for_each(|(i, sig)| {
        for q in 0..NPERM {
            let mut st = if q == 0 { [0u64; 25] } else { wit.states[i][q - 1] };
            xor_block(&mut st, &wit.blocks[i][q]);
            let row = &mut sig[q * W..(q + 1) * W];
            for s in 0..STATE {
                row[s] = pm(state_bit(&st, s));
            }
        }
    });
    for &(p, s, x) in &wit.in_extra {
        v[p * W + s] = x;
    }
    v
}

// ---------------------------------------------------------------- certificate

/// Frontend element counts of the Keccak and link part, in transcript order.
pub fn kec_segments(n: usize) -> Vec<(&'static str, usize)> {
    let logp = LOGQ + n.trailing_zeros() as usize;
    let nvx = LOGW + n.trailing_zeros() as usize;
    let layers: usize = keccak::specs().iter().map(|s| s.main_elems(logp) + 2 * LOGW + 1).sum();
    vec![
        ("masked-output T openings", 8),
        ("mask sumcheck", 2 * nvk(n)),
        ("Keccak output claim", 1),
        ("Keccak GKR, 72 layers", layers),
        ("input-link sumcheck", 3 * nvx),
        ("re-indexed bit claims", 8),
        ("bit-wiring sumcheck", 2 * LOG_BW),
    ]
}

pub fn kec_elems(n: usize) -> usize {
    kec_segments(n).iter().map(|s| s.1).sum()
}

#[derive(Clone)]
pub struct Cert9 {
    pub manifest: Vec<u8>,
    pub ct: Vec<u8>,
    pub nu: Vec<u8>,
    pub quot: Vec<u8>,
    pub comm: [u8; 64],
    pub gkr: GkrProof,
    pub leaf_pair: [EF; 2],
    pub t_claim: EF,
    pub master: Vec<Vec<EF>>,
    pub table: Vec<[EF; 2]>,
    pub kec: Vec<u8>,
    pub whir: Vec<u8>,
}

/// Serialized bytes per component.
#[derive(Debug, Default, Clone)]
pub struct Sizes9 {
    pub parts: Vec<(String, usize)>,
    pub total: usize,
}

impl Sizes9 {
    pub fn get(&self, name: &str) -> usize {
        self.parts.iter().find(|p| p.0 == name).map(|p| p.1).unwrap_or(0)
    }
    /// Offset of a component in the serialized certificate.
    pub fn offset(&self, name: &str) -> usize {
        let mut o = 0;
        for (k, v) in &self.parts {
            if k == name {
                return o;
            }
            o += v;
        }
        panic!("no component {name}")
    }
}

pub const MASTER_DEG: usize = 8;

impl Cert9 {
    pub fn to_bytes(&self) -> (Vec<u8>, Sizes9) {
        let mut b = Vec::new();
        let mut parts = vec![];
        let mut last = 0usize;
        let mut mark = |b: &Vec<u8>, name: &str, parts: &mut Vec<(String, usize)>| {
            parts.push((name.to_string(), b.len() - last));
            last = b.len();
        };
        b.extend_from_slice(&self.manifest);
        mark(&b, "manifest", &mut parts);
        b.extend_from_slice(&self.ct);
        mark(&b, "c_tilde", &mut parts);
        b.extend_from_slice(&self.nu);
        mark(&b, "hint counts", &mut parts);
        b.extend_from_slice(&self.quot);
        mark(&b, "quotients", &mut parts);
        b.extend_from_slice(&self.comm);
        mark(&b, "commitment", &mut parts);
        for l in &self.gkr.layers {
            for r in &l.rounds {
                r.iter().for_each(|x| crate::field::ef_to_bytes(x, &mut b));
            }
            l.finals.iter().for_each(|x| crate::field::ef_to_bytes(x, &mut b));
        }
        mark(&b, "LogUp GKR", &mut parts);
        self.leaf_pair.iter().for_each(|x| crate::field::ef_to_bytes(x, &mut b));
        mark(&b, "leaf pair", &mut parts);
        crate::field::ef_to_bytes(&self.t_claim, &mut b);
        mark(&b, "table claim T", &mut parts);
        for r in &self.master {
            r.iter().for_each(|x| crate::field::ef_to_bytes(x, &mut b));
        }
        mark(&b, "master sumcheck", &mut parts);
        for r in &self.table {
            r.iter().for_each(|x| crate::field::ef_to_bytes(x, &mut b));
        }
        mark(&b, "table sumcheck", &mut parts);
        let n = self.nu.len();
        let mut off = 0;
        for (name, cnt) in kec_segments(n) {
            b.extend_from_slice(&self.kec[off..off + 40 * cnt]);
            off += 40 * cnt;
            mark(&b, name, &mut parts);
        }
        b.extend_from_slice(&(self.whir.len() as u32).to_le_bytes());
        mark(&b, "WHIR length", &mut parts);
        b.extend_from_slice(&self.whir);
        mark(&b, "WHIR proof", &mut parts);
        let total = b.len();
        (b, Sizes9 { parts, total })
    }

    /// Strict parsing: exact lengths, canonical field elements, no trailing bytes.
    pub fn from_bytes(n: usize, b: &[u8]) -> Result<Cert9, Reject> {
        let tree = Tree::new(n);
        let mut cur = 0usize;
        let take = |cur: &mut usize, len: usize| -> Result<Vec<u8>, Reject> {
            if *cur + len > b.len() {
                return Err(Reject::Parse("truncated"));
            }
            let s = b[*cur..*cur + len].to_vec();
            *cur += len;
            Ok(s)
        };
        let manifest = take(&mut cur, MANIFEST)?;
        let ct = take(&mut cur, 64 * n)?;
        let nu = take(&mut cur, n)?;
        let quot = take(&mut cur, 5 * TRIALS * proj::chunks(n))?;
        let comm: [u8; 64] = take(&mut cur, 64)?.try_into().unwrap();
        let rd = |cur: &mut usize| -> Result<EF, Reject> {
            if *cur + 40 > b.len() {
                return Err(Reject::Parse("truncated"));
            }
            let v = crate::field::ef_from_bytes(&b[*cur..*cur + 40]).ok_or(Reject::Parse("non-canonical field element"))?;
            *cur += 40;
            Ok(v)
        };
        let mut layers = Vec::with_capacity(tree.d);
        for k in 0..tree.d {
            let mut rounds = Vec::with_capacity(k);
            for _ in 0..k {
                rounds.push([rd(&mut cur)?, rd(&mut cur)?]);
            }
            let finals = [rd(&mut cur)?, rd(&mut cur)?, rd(&mut cur)?, rd(&mut cur)?];
            layers.push(Layer { rounds, finals });
        }
        let leaf_pair = [rd(&mut cur)?, rd(&mut cur)?];
        let t_claim = rd(&mut cur)?;
        let mut master = Vec::with_capacity(tree.log_dc);
        for _ in 0..tree.log_dc {
            master.push((0..MASTER_DEG).map(|_| rd(&mut cur)).collect::<Result<Vec<_>, _>>()?);
        }
        let mut table = Vec::with_capacity(LOG_TAB);
        for _ in 0..LOG_TAB {
            table.push([rd(&mut cur)?, rd(&mut cur)?]);
        }
        let ke = kec_elems(n);
        let kec = take(&mut cur, 40 * ke)?;
        for c in kec.chunks_exact(40) {
            if crate::field::ef_from_bytes(c).is_none() {
                return Err(Reject::Parse("non-canonical field element"));
            }
        }
        if cur + 4 > b.len() {
            return Err(Reject::Parse("truncated"));
        }
        let wl = u32::from_le_bytes(b[cur..cur + 4].try_into().unwrap()) as usize;
        cur += 4;
        if cur + wl != b.len() {
            return Err(Reject::Parse("length mismatch / trailing bytes"));
        }
        let whir = b[cur..].to_vec();
        Ok(Cert9 { manifest, ct, nu, quot, comm, gkr: GkrProof { layers }, leaf_pair, t_claim, master, table, kec, whir })
    }
}

// ---------------------------------------------------------------- statement

/// Lab manifest "QLYLB10H": magic, LE32(lab profile id), 64 reserved zero bytes, LE4 N, the
/// statement digest (cert::statement_digest), LE4 chunk count, zero padding.
pub fn manifest_lab9(records: &[Record]) -> Vec<u8> {
    let n = records.len();
    let mut m = Vec::with_capacity(MANIFEST);
    m.extend_from_slice(magics().0);
    m.extend_from_slice(&lab_profile9(n).to_le_bytes());
    m.extend_from_slice(&[0u8; 64]);
    m.extend_from_slice(&(n as u32).to_le_bytes());
    m.extend_from_slice(&cert::statement_digest(records));
    m.extend_from_slice(&(proj::chunks(n) as u32).to_le_bytes());
    m.resize(MANIFEST, 0);
    m
}

/// Lab raw instance: domain, LE32(profile), F(0x0100, manifest), F(0x0110, records),
/// F(0x0105, c_tilde_0 || ... || c_tilde_{N-1}), F(0x0104, nu).
pub fn instance_lab9(profile: u32, manifest: &[u8], records: &[Record], ct: &[u8], nu: &[u8]) -> Vec<u8> {
    let mut rs = Vec::new();
    rs.extend_from_slice(&fs7::le32(records.len() as u32));
    for r in records {
        rs.extend_from_slice(&fs7::le32(r.ctx.len() as u32));
        rs.extend_from_slice(&r.ctx);
        rs.extend_from_slice(&fs7::le32(r.msg.len() as u32));
        rs.extend_from_slice(&r.msg);
        rs.extend_from_slice(&r.pk);
    }
    let mut x = Vec::new();
    x.extend_from_slice(b"Qlyphs/Archive/Instance/r10-lab\0");
    x.extend_from_slice(&fs7::le32(profile));
    x.extend_from_slice(&fs7::frame(0x0100, manifest));
    x.extend_from_slice(&fs7::frame(0x0110, &rs));
    x.extend_from_slice(&fs7::frame(0x0105, ct));
    x.extend_from_slice(&fs7::frame(0x0104, nu));
    x
}

// ---------------------------------------------------------------- round table

/// The registered rounds of the hidden-u profile for n signatures, from the frontend sizes and
/// the WHIR shape. Built in transcript order; the adapter poisons on any deviation.
pub fn build_table9(profile: u32, n: usize, ws: &p3_whir::WhirShape) -> reg7::Table {
    const KB: usize = 40;
    let fr = reg7::front(n);
    let logp = LOGQ + n.trailing_zeros() as usize;
    let nvx = LOGW + n.trailing_zeros() as usize;
    let mut r: Vec<RoundDef> = Vec::with_capacity(4096);
    let mut push = |body: Body, shape: Shape, opens: Option<u32>, label: &'static str| r.push(RoundDef { body, shape, opens, label });
    let nq = fr.trials * (n + fr.slots);
    // Round 10: the F_q slack grows with nq and a short pool is rejected (fs7::qslack10).
    push(Body::Real, Shape { nq, qslack: fs7::qslack10(nq), ..Default::default() }, None, "initial commitment; projections");
    push(Body::Scalar(5 * fr.trials * fr.chunks), Shape { theta: true, ..Default::default() }, None, "quotients; theta");
    push(Body::Scalar(4 * KB), Shape::k(2), None, "GKR layer-1 finals; beta_0, lambda_1");
    for k in 1..fr.d {
        for _ in 0..k {
            push(Body::Scalar(2 * KB), Shape::k(1), None, "GKR round (a1, a2)");
        }
        push(Body::Scalar(4 * KB), Shape::k(if k + 1 < fr.d { 2 } else { 1 }), None, "GKR finals; beta_k (, lambda_k+1)");
    }
    push(Body::Scalar(2 * KB), Shape::k(2), None, "explicit (P_leaf, Q_leaf); gamma_P, gamma_Q");
    push(Body::Scalar(KB), Shape::k(1 + 4 + fr.log_dc + n + fr.chunks * fr.trials + nvk(n)), None, "T; gamma_Z, gamma_B, tau, omega, mu, r0");
    for _ in 0..fr.log_dc {
        push(Body::Scalar(MASTER_DEG * KB), Shape::k(1), None, "master round (degree 8)");
    }
    for _ in 0..fr.log_tab {
        push(Body::Scalar(2 * KB), Shape::k(1), None, "table round");
    }
    // Masked output: 8 openings, then the mask sumcheck.
    for v in 0..nvk(n) {
        push(Body::Scalar(if v == 0 { 10 * KB } else { 2 * KB }), Shape::k(1), None, "mask round");
    }
    // 72 layers, last first; the incoming claim value opens each layer's first body.
    let sp = keccak::specs();
    for s in sp.iter().rev() {
        let (df, d, ng) = (s.deg_f(), s.d(), s.gathers.len());
        for k in 0..logp {
            push(Body::Scalar((df + (k == 0) as usize) * KB), Shape::k(1), None, "Keccak layer p-round");
        }
        for _ in 0..LOGW {
            push(Body::Scalar(d * KB), Shape::k(1), None, "Keccak layer s-round");
        }
        push(Body::Scalar(ng * KB), Shape::k(ng), None, "Keccak gathered values; wiring betas");
        for _ in 0..LOGW {
            push(Body::Scalar(2 * KB), Shape::k(1), None, "Keccak wiring round");
        }
    }
    for v in 0..nvx {
        push(Body::Scalar(if v == 0 { 4 * KB } else { 3 * KB }), Shape::k(1), None, "input-link round");
    }
    push(Body::Scalar(8 * KB), Shape::k(8), None, "re-indexed bit claims; gamma_q");
    for _ in 0..LOG_BW {
        push(Body::Scalar(2 * KB), Shape::k(1), None, "bit-wiring round");
    }
    // Johnson profiles draw one OOD sample per commitment; unique-decoding profiles none.
    let ood0 = ws.commitment_ood_samples;
    assert!(ood0 <= 1, "at most one initial OOD sample");
    assert!(!ws.stratified_queries);
    if ood0 == 1 {
        push(Body::Scalar(0), Shape::k(1), None, "empty; initial OOD point");
        push(Body::Scalar((1 + NCLAIMS) * KB), Shape::k(1), None, "initial OOD answer, 29 opened values; batching alpha");
    } else {
        push(Body::Scalar(NCLAIMS * KB), Shape::k(1), None, "29 opened values; batching alpha (no OOD)");
    }
    for _ in 0..ws.initial_sumcheck.rounds {
        push(Body::Scalar(2 * KB), Shape::k(1), None, "WHIR sumcheck");
    }
    let mut prev_tree: u32 = 1;
    let mut rounds_now = r.len();
    let mut tail: Vec<RoundDef> = Vec::new();
    for rd in &ws.rounds {
        assert!(rd.ood_samples == ood0, "OOD samples per round equal the initial count");
        assert!(rd.query_draws > 0 && rd.query_pow_bits == 0 && rd.sumcheck.pow_bits == 0);
        let tree = (rounds_now + tail.len() + 1) as u32;
        let queries = Shape { nk: 1, widths: vec![rd.index_bits as u8; rd.query_draws], ..Default::default() };
        if ood0 == 1 {
            tail.push(RoundDef { body: Body::Real, shape: Shape::k(1), opens: None, label: "WHIR commitment; OOD point" });
            tail.push(RoundDef { body: Body::Scalar(KB), shape: queries, opens: Some(prev_tree), label: "OOD answer; query indices, gamma" });
        } else {
            tail.push(RoundDef { body: Body::Real, shape: queries, opens: Some(prev_tree), label: "WHIR commitment; query indices, gamma (no OOD)" });
        }
        for _ in 0..rd.sumcheck.rounds {
            tail.push(RoundDef { body: Body::Scalar(2 * KB), shape: Shape::k(1), opens: None, label: "WHIR sumcheck" });
        }
        prev_tree = tree;
    }
    assert!(ws.final_query_draws > 0 && ws.final_pow_bits == 0 && ws.final_sumcheck.pow_bits == 0);
    tail.push(RoundDef { body: Body::Scalar(ws.final_poly_len * KB), shape: Shape { widths: vec![ws.final_index_bits as u8; ws.final_query_draws], ..Default::default() }, opens: Some(prev_tree), label: "final polynomial; final query indices" });
    for _ in 0..ws.final_sumcheck.rounds {
        tail.push(RoundDef { body: Body::Scalar(2 * KB), shape: Shape::k(1), opens: None, label: "final sumcheck" });
    }
    r.extend(tail);
    rounds_now = r.len();
    let _ = rounds_now;
    let formal_len = r.iter().map(|d| d.shape.used()).max().unwrap();
    reg7::Table { profile, n, formal_len, rounds: r, strict_k: true }
}

// ---------------------------------------------------------------- transcript backend

/// The registered-round adapter (frontend and WHIR) over the hidden-u round table.
pub struct B9 {
    pub tr: reg7::Tr7,
    pub pcs: pcs::Pcs10,
    fold0: usize,
    pub leaf_calls: Arc<AtomicU64>,
}

/// WHIR schedule (start log inverse rate, round log inverse rates, folds) of the hidden-u lab
/// profiles: the registered r2 family up to 2^24; above it a lower start rate keeps the first
/// codeword in memory (see RESULTS-r9-hidden-u.md for the benchmark that chose it).
///
/// Round 10, dimensions 27..31 (N = 4096 .. 65536): chosen with aggregate/r10-check/whir_plan.py
/// among JohnsonBound schedules with no grinding whose WHIR ledger is at least 270 bits, for
/// the smallest estimated proof under the first-codeword budget of the 24 GB prover (start rate
/// 1/2 from dimension 29 on), with at most 6 variables left for the final polynomial (the
/// library's folding threshold). Dimension 31 is the round-10 review's corrected large-range
/// schedule (D.1): start 1, rates [2, 5, 8, 11], folds [6, 5, 5, 5, 5], target 272, whose
/// composed PCS figure is 269.27 bits.
pub fn schedule9(nv: usize) -> (usize, Vec<usize>, Vec<usize>) {
    match nv {
        25 => (3, vec![6, 8, 10], vec![6, 5, 5, 5]),
        26 => (2, vec![5, 8, 10], vec![6, 5, 5, 5]),
        27 => (2, vec![4, 7, 10], vec![6, 5, 5, 5]),
        28 => (2, vec![3, 6, 9], vec![7, 5, 5, 5]),
        29 => (1, vec![2, 5, 8, 11], vec![6, 5, 5, 5, 5]),
        30 => (1, vec![3, 6, 9], vec![7, 6, 6, 6]),
        31 => (1, vec![2, 5, 8, 11], vec![6, 5, 5, 5, 5]),
        v => pcs::profile(v),
    }
}

/// Unique-decoding schedules (per-term target 286, no grinding, no OOD). N = 2048, 16384 and
/// 65536 are the review ledger's candidates; the others follow the same family.
pub fn schedule_ud(nv: usize) -> (usize, Vec<usize>, Vec<usize>) {
    match nv {
        ..=21 => (2, vec![5, 8], vec![6, 5, 5]),
        22 => (2, vec![5, 8, 10], vec![6, 4, 4, 4]),
        23 => (2, vec![5, 8, 10], vec![6, 5, 4, 4]),
        24 => (2, vec![5, 8, 10], vec![6, 5, 5, 4]),
        25..=27 => (2, vec![5, 8, 10], vec![6, 5, 5, 5]),
        28 => (2, vec![5, 8, 10], vec![6, 6, 5, 5]),
        29 => (2, vec![5, 8, 10, 11], vec![6, 5, 5, 5, 3]),
        30 => (2, vec![5, 8, 10, 11], vec![6, 5, 5, 5, 4]),
        _ => (1, vec![2, 5, 8, 11], vec![6, 5, 5, 5, 5]),
    }
}

/// (schedule, soundness) of a round-10 lab profile at PCS dimension nv.
pub fn schedule_of(profile: u32, nv: usize) -> ((usize, Vec<usize>, Vec<usize>), pcs::Sec) {
    match fam_of(profile) {
        Fam::Unique => (schedule_ud(nv), pcs::Sec::unique()),
        Fam::Johnson => (schedule9(nv), pcs::Sec::johnson(nv)),
    }
}

pub fn make_pcs9(n: usize, profile: u32, tree: Arc<AtomicU32>, leaf_calls: Arc<AtomicU64>) -> (pcs::Pcs10, usize) {
    make_pcs9r(n, profile, tree, Default::default(), leaf_calls)
}

/// The round-10 lab PCS: the registered r2 schedule up to 2^24 cells for the Johnson family,
/// schedule_of above; the commitment scheme takes its tree contexts from `tree` (commit) and
/// `roots` (verify).
pub fn make_pcs9r(n: usize, profile: u32, tree: Arc<AtomicU32>, roots: crate::mmcs10::Roots, leaf_calls: Arc<AtomicU64>) -> (pcs::Pcs10, usize) {
    let nv = stacked_vars9(n);
    let (sch, sec) = if nv <= 24 && fam_of(profile) == Fam::Johnson { (pcs::profile(nv), pcs::Sec::johnson(nv)) } else { schedule_of(profile, nv) };
    pcs::make_pcs10(nv, NCLAIMS, sch, sec, profile, tree, roots, leaf_calls)
}

pub fn table_of9(profile: u32, n: usize, p: &pcs::Pcs10) -> reg7::Table {
    build_table9(profile, n, &p3_whir::WhirShape::new(&**p, NBATCH))
}

/// The registered table for a hidden-u lab profile, or None.
pub fn registered_table9(profile: u32, n: usize) -> Option<Arc<reg7::Table>> {
    let ok = n.is_power_of_two() && (32..=MAX_N).contains(&n) && (profile == lab_profile9(n) || profile == lab_chain_profile9(n));
    if !ok {
        return None;
    }
    let (p, _) = make_pcs9(n, profile, Arc::new(AtomicU32::new(0)), Arc::new(AtomicU64::new(0)));
    Some(Arc::new(table_of9(profile, n, &p)))
}

impl B9 {
    pub fn new(n: usize, profile: u32, x: &[u8], inject: pcs::Inject, table: Option<Arc<reg7::Table>>) -> Self {
        let tree = Arc::new(AtomicU32::new(0));
        let leaf_calls = Arc::new(AtomicU64::new(0));
        let roots: crate::mmcs10::Roots = Default::default();
        let (p, fold0) = make_pcs9r(n, profile, tree.clone(), roots.clone(), leaf_calls.clone());
        let table = table.unwrap_or_else(|| Arc::new(table_of9(profile, n, &p)));
        let mut tr = reg7::Tr7::new(table, x, tree, inject);
        tr.ch.roots = roots;
        B9 { tr, pcs: p, fold0, leaf_calls }
    }
}

impl Fs for B9 {
    fn absorb_ef(&mut self, x: EF) {
        self.tr.absorb_ef(x)
    }
    fn sample_ef(&mut self) -> EF {
        self.tr.sample_ef()
    }
    fn inject(&self) -> pcs::Inject {
        self.tr.ch.inject
    }
}

impl Backend for B9 {
    type PData = p3_whir::WhirProverData<F, EF, crate::mmcs10::Mmcs10, Layout>;
    type Proof = pcs::PcsProof10;
    const V7: bool = true;
    fn fold0(&self) -> usize {
        self.fold0
    }
    fn commit(&mut self, wit: Witness3) -> (Commitment, Self::PData) {
        use p3_commit::MultilinearPcs;
        self.pcs.commit(wit, &mut self.tr.ch).expect("commit")
    }
    fn observe_commitment(&mut self, c: &Commitment) {
        observe_commitment::<F, _, _>(&mut self.tr.ch, c.clone());
    }
    fn projection(&mut self) -> ProjSrc {
        ProjSrc::Values(self.tr.ch.sample_fq())
    }
    fn absorb_quotients(&mut self, _q: &[[i64; TRIALS]], bytes: &[u8]) {
        self.tr.ch.observe_bytes(bytes);
    }
    fn theta(&mut self) -> (EF, usize) {
        (self.tr.ch.sample_theta(), 0)
    }
    fn open_at(&mut self, pd: Self::PData, proto: &OpeningProtocol, pts: &[Point<EF>]) -> (Self::Proof, Vec<Vec<EF>>) {
        use p3_sumcheck::PrescribedPointPcs;
        let p = self.pcs.open_at(pd, proto, pts, &mut self.tr.ch).expect("open");
        let ev = p.evals.iter().map(|e| e.current().to_vec()).collect();
        (p, ev)
    }
    fn verify_at(&mut self, c: &Commitment, proof: &Self::Proof, proto: &OpeningProtocol, pts: &[Point<EF>]) -> Result<Vec<Vec<EF>>, String> {
        use p3_sumcheck::PrescribedPointPcs;
        self.pcs.verify_at(c, proof, proto, pts, &mut self.tr.ch).map(|v| v.iter().map(|e| e.current().to_vec()).collect()).map_err(|e| format!("{e:?}"))
    }
    fn transcript_error(&self) -> Option<String> {
        let ch = &self.tr.ch;
        match &ch.error {
            Some(e) => Some(e.clone()),
            None if !ch.finished() => Some(format!("transcript stopped at round {} of {}", ch.round(), ch.table().len())),
            None => None,
        }
    }
}

/// The five opening batches: table A {X, Y, S, B0..B3} at the master point, {T1..T8} at the
/// masked-output point, {T1..T8} at the input-link point, {B0..B3} at the bit-wiring point;
/// table B {m_even, m_odd} at the table point.
/// Every projection coefficient was drawn (the strict pool did not run short).
fn projection_complete(src: &ProjSrc, n: usize) -> bool {
    match src {
        ProjSrc::Values(v) => v.len() == TRIALS * (n + SLOTS),
        ProjSrc::Seed(_) => true,
    }
}

pub fn protocol9(log_dc: usize) -> OpeningProtocol {
    let t: Vec<usize> = (COL_T..COL_T + 8).collect();
    OpeningProtocol::new(vec![
        TableSpec::new(
            TableShape::new(log_dc, NCOL),
            vec![OpeningBatch::new((0..7).collect(), vec![]), OpeningBatch::new(t.clone(), vec![]), OpeningBatch::new(t, vec![]), OpeningBatch::new((COL_B..COL_B + 4).collect(), vec![])],
        ),
        TableSpec::new(TableShape::new(LOG_TAB, 2), vec![OpeningBatch::new(vec![0, 1], vec![])]),
    ])
}

fn p3_point(my: &[EF]) -> Point<EF> {
    Point::new(my.iter().rev().copied().collect::<Vec<_>>())
}

/// The WHIR transcript shape of the current family's lab profile for n signatures.
pub fn whir_shape9(n: usize) -> p3_whir::WhirShape {
    let (p, _) = make_pcs9(n, lab_profile9(n), Arc::new(AtomicU32::new(0)), Arc::new(AtomicU64::new(0)));
    p3_whir::WhirShape::new(&*p, NBATCH)
}

pub fn pcs_security_bits9(n: usize) -> (f64, f64) {
    use p3_sumcheck::PrescribedPointPcs;
    let nv = stacked_vars9(n);
    let (sch, sec) = schedule_of(lab_profile9(n), nv);
    let (p, _) = pcs::make_pcs_prof_sec(nv, NCLAIMS, sch, sec);
    let sec = p.prescribed_security(&protocol9(Tree::new(n).log_dc)).expect("security");
    (sec.error().bits(), sec.log2_max_candidates)
}

// ---------------------------------------------------------------- generic sumcheck

const MAXC: usize = 24;

/// Plain sumcheck of sum_b f(c_1(b), ..., c_k(b)) over {0,1}^nv, binding the top variable first.
/// A round sends h(0), h(2), ..., h(deg); the verifier sets h(1) = claim - h(0) and interpolates
/// on the nodes 0..deg. `base` columns are base-field, `ext` columns extension-field; f receives
/// them in that order. Returns the point (indexed by variable, LSB first) and the final values.
#[allow(clippy::too_many_arguments)]
pub fn gen_prove<T: Fs>(base: &[&[F]], ext: Vec<Vec<EF>>, deg: usize, mut claim: EF, f: &(dyn Fn(&[EF]) -> EF + Sync), tr: &mut T, msgs: &mut Vec<EF>) -> (Vec<EF>, Vec<EF>) {
    let nb = base.len();
    let nc = nb + ext.len();
    assert!(nc <= MAXC && deg < 16);
    let len = if nb > 0 { base[0].len() } else { ext[0].len() };
    let nv = len.trailing_zeros() as usize;
    assert!(base.iter().all(|c| c.len() == len) && ext.iter().all(|c| c.len() == len));
    let mut point = vec![EF::ZERO; nv];
    let mut cols: Vec<Vec<EF>> = Vec::new();
    let mut ext = Some(ext);
    for round in 0..nv {
        let h = (len >> round) / 2;
        let acc = {
            let get = |c: usize, i: usize| -> EF {
                if round == 0 {
                    if c < nb { efb(base[c][i]) } else { ext.as_ref().unwrap()[c - nb][i] }
                } else {
                    cols[c][i]
                }
            };
            (0..h)
                .into_par_iter()
                .with_min_len(256)
                .fold(
                    || [EF::ZERO; 16],
                    |mut acc, i| {
                        let mut lo = [EF::ZERO; MAXC];
                        let mut d = [EF::ZERO; MAXC];
                        for c in 0..nc {
                            let (a, b) = (get(c, i), get(c, i + h));
                            lo[c] = a;
                            d[c] = b - a;
                        }
                        acc[0] += f(&lo[..nc]);
                        let mut v = lo;
                        for c in 0..nc {
                            v[c] += d[c];
                        }
                        for t in 2..=deg {
                            for c in 0..nc {
                                v[c] += d[c];
                            }
                            acc[t] += f(&v[..nc]);
                        }
                        acc
                    },
                )
                .reduce(|| [EF::ZERO; 16], |a, b| core::array::from_fn(|k| a[k] + b[k]))
        };
        let mut msg = Vec::with_capacity(deg);
        msg.push(acc[0]);
        msg.extend_from_slice(&acc[2..=deg]);
        tr.absorb_efs(&msg);
        msgs.extend_from_slice(&msg);
        let r = tr.sample_ef();
        claim = gen_next(&msg, claim, r);
        point[nv - 1 - round] = r;
        if round == 0 {
            let fb = |v: &[F]| -> Vec<EF> { (0..h).into_par_iter().with_min_len(1 << 12).map(|i| r * (v[i + h] - v[i]) + v[i]).collect() };
            cols = base.iter().map(|c| fb(c)).collect();
            for mut c in ext.take().unwrap() {
                fold_ext(&mut c, r);
                cols.push(c);
            }
        } else {
            cols.iter_mut().for_each(|c| fold_ext(c, r));
        }
    }
    let finals: Vec<EF> = if nv == 0 { vec![] } else { cols.iter().map(|c| c[0]).collect() };
    debug_assert_eq!(claim, f(&finals));
    (point, finals)
}

fn fold_ext(v: &mut Vec<EF>, r: EF) {
    let h = v.len() / 2;
    let (lo, hi) = v.split_at_mut(h);
    lo.par_iter_mut().zip(hi.par_iter()).with_min_len(1 << 12).for_each(|(a, &b)| *a += r * (b - *a));
    v.truncate(h);
}

/// h(r) from the message [h(0), h(2), ..., h(deg)] and the claim h(0) + h(1).
pub fn gen_next(msg: &[EF], claim: EF, r: EF) -> EF {
    let mut nodes = Vec::with_capacity(msg.len() + 1);
    nodes.push(msg[0]);
    nodes.push(claim - msg[0]);
    nodes.extend_from_slice(&msg[1..]);
    lagrange(&nodes, r)
}

/// Verifier replay of gen_prove: returns the point and the final claim.
pub fn gen_verify<T: Fs>(rd: &mut keccak::Reader, nv: usize, deg: usize, mut claim: EF, tr: &mut T) -> Result<(Vec<EF>, EF), String> {
    let mut point = vec![EF::ZERO; nv];
    for round in 0..nv {
        let msg = rd.take(deg)?;
        tr.absorb_efs(&msg);
        let r = tr.sample_ef();
        claim = gen_next(&msg, claim, r);
        point[nv - 1 - round] = r;
    }
    Ok((point, claim))
}

// ---------------------------------------------------------------- master polynomial

/// Constants of the degree-8 master polynomial.
#[derive(Clone, Copy)]
pub struct MasterK {
    pub g: EF,
    pub gq: EF,
    pub gz: EF,
    pub gb: [EF; 4],
}

/// The master summand. v = [X, Y, S, B0, B1, B2, B3, wX, wY, zeta, rho, rho', eq_tau, omega].
/// With d0 = prod (1 - Bj), d15 = prod Bj, u = sum 2^j Bj, Kv = K - (a - 1) and Sv = start - st0
/// of class 2 (the region polynomials, affine in d0 and d15):
///   F = -g wY Kv + gQ [wX (K_X X - X^2) + wY (Y (a - 1) + Y Kv - Y^2)]
///       + eq_tau [gZ (S^3 - S) + sum_j gB_j (Bj^2 - Bj)] + omega S^2
///       + zeta X - rho Y - rho Sv - rho' u.
#[inline(always)]
pub fn master_f9(k: &MasterK, v: &[EF]) -> EF {
    let (x, y, s) = (v[0], v[1], v[2]);
    let b = [v[3], v[4], v[5], v[6]];
    let (wx, wy, ze, rh, rp, et, om) = (v[7], v[8], v[9], v[10], v[11], v[12], v[13]);
    let co2 = region::coeffs(2);
    let half = F::TWO.inverse();
    let s2 = s * s;
    let d0 = (EF::ONE - b[0]) * (EF::ONE - b[1]) * (EF::ONE - b[2]) * (EF::ONE - b[3]);
    let d15 = b[0] * b[1] * b[2] * b[3];
    let u = b[0] + b[1].double() + b[2] * F::from_u64(4) + b[3] * F::from_u64(8);
    let sp = (s + s2) * half;
    let kv = d0 * (EF::ONE - s2) + d15 * sp - s2 * F::from_u64(region::G as u64);
    let sv = s * co2.st[1] + s2 * co2.st[2] + d0 * (sp - EF::ONE);
    let am1 = F::from_u64((region::A - 1) as u64);
    let kx = F::from_u64(XK as u64);
    let mut bool_t = k.gz * (s2 * s - s);
    for j in 0..4 {
        bool_t += k.gb[j] * (b[j] * b[j] - b[j]);
    }
    -(k.g * wy * kv) + k.gq * (wx * (x * kx - x * x) + wy * (y * am1 + y * kv - y * y)) + et * bool_t + om * s2 + ze * x - rh * y - rh * sv - rp * u
}

/// r'_{j,i}[t] = ctr(alpha_j[i] eta_j[t] a mod q): the u coefficient of the modular relation,
/// reduced so that the integer lift stays far below p.
#[inline(always)]
pub fn r_prime(ch: &Challenges, j: usize, i: usize, t: usize) -> i64 {
    ctr(red(red(ch.alpha[j][i] as u64 * ch.eta[j][t] as u64) as u64 * A2 as u64))
}

/// The no-wrap bound of the hidden-u integer lift for a chunk of c signatures: the round-3 bound
/// plus the u term (|r'| <= (q-1)/2, 0 <= u <= 15, 2048 coefficients per signature).
pub fn lift_bound9(c: u128) -> u128 {
    let half = (mlnat::Q as u128 - 1) / 2;
    half * (1792 * c * 524_167 + 2048 * c * 523_777 + 2048 * c * 15 + 1) + ((mlnat::Q as u128) << proj::VBITS)
}

// ---------------------------------------------------------------- public sums

#[derive(Clone)]
struct Sums9 {
    d: [u64; TRIALS],
    ss: [i64; TRIALS],
    sr: [i64; TRIALS],
    pz: [EF; TRIALS],
    rr: [EF; TRIALS],
    rp: [EF; TRIALS],
    wx: EF,
}

fn sums9(i: usize, s_cent: &[i32], ch: &Challenges, bc: &[u32], eq_rho: &[EF], eq_r: Option<&[EF]>) -> Sums9 {
    let base = i * SLOTS;
    let mut o = Sums9 { d: [0; TRIALS], ss: [0; TRIALS], sr: [0; TRIALS], pz: [EF::ZERO; TRIALS], rr: [EF::ZERO; TRIALS], rp: [EF::ZERO; TRIALS], wx: EF::ZERO };
    for j in 0..TRIALS {
        o.d[j] = ch.d_part(j, i, bc);
        let s = &s_cent[j * L * N..(j + 1) * L * N];
        o.ss[j] = s.iter().map(|&v| v as i64).sum();
        o.sr[j] = (0..K * N).map(|t| ch.r_centered(j, i, t)).sum();
    }
    if let Some(er) = eq_r {
        for t in 0..L * N {
            o.wx += er[base + t] * eq_rho[base + t];
        }
        for j in 0..TRIALS {
            let s = &s_cent[j * L * N..(j + 1) * L * N];
            o.pz[j] = (0..L * N).map(|t| er[base + t] * fi(s[t] as i64)).sum();
            o.rr[j] = (0..K * N).map(|t| er[base + t] * fi(ch.r_centered(j, i, t))).sum();
            o.rp[j] = (0..K * N).map(|t| er[base + t] * fi(r_prime(ch, j, i, t))).sum();
        }
    }
    o
}

struct Agg9 {
    d: Vec<[u64; TRIALS]>,
    ss: Vec<[i128; TRIALS]>,
    sr: Vec<[i128; TRIALS]>,
    pz: Vec<[EF; TRIALS]>,
    rr: Vec<[EF; TRIALS]>,
    rp: Vec<[EF; TRIALS]>,
    wx: EF,
}

fn aggregate9(s: &[Sums9], n: usize) -> Agg9 {
    let nc = proj::chunks(n);
    let mut a = Agg9 { d: vec![[0; TRIALS]; nc], ss: vec![[0; TRIALS]; nc], sr: vec![[0; TRIALS]; nc], pz: vec![[EF::ZERO; TRIALS]; nc], rr: vec![[EF::ZERO; TRIALS]; nc], rp: vec![[EF::ZERO; TRIALS]; nc], wx: EF::ZERO };
    for (i, x) in s.iter().enumerate() {
        let c = i / CHUNK;
        for j in 0..TRIALS {
            a.d[c][j] = (a.d[c][j] + x.d[j]) % mlnat::Q as u64;
            a.ss[c][j] += x.ss[j] as i128;
            a.sr[c][j] += x.sr[j] as i128;
            a.pz[c][j] += x.pz[j];
            a.rr[c][j] += x.rr[j];
            a.rp[c][j] += x.rp[j];
        }
        a.wx += x.wx;
    }
    a
}

fn fi128(x: i128) -> F {
    F::from_u64(x.rem_euclid(crate::field::P as i128) as u64)
}

struct Ctx9 {
    n: usize,
    tree: Tree,
    theta: EF,
    rho: Vec<EF>,
    p_leaf: EF,
    q_leaf: EF,
    gp: EF,
    gq: EF,
    t_claim: EF,
    mk: MasterK,
    tau: Vec<EF>,
    omega: Vec<EF>,
    mu: Vec<[EF; TRIALS]>,
    quot: Vec<[i64; TRIALS]>,
    nu: Vec<u8>,
}

fn claimed_sum9(c: &Ctx9, a: &Agg9) -> EF {
    let th = c.theta;
    let th2 = th * th;
    let kxf = F::from_u64(XK as u64);
    let am1 = F::from_u64((region::A - 1) as u64);
    let (kx, ky, kt) = (c.tree.kx(&c.rho), c.tree.ky(&c.rho), c.tree.kt(&c.rho));
    let pad = c.rho[8] * c.rho[9] * c.rho[10];
    let xm = kx * (EF::ONE - pad);
    let pub_p = xm * (th.double() - efb(kxf)) + ky * (th.double() - efb(am1));
    let mut pub_q = xm * (th2 - th * kxf) + ky * (th2 - th * am1);
    let rt = c.tree.rho_t(&c.rho);
    let (mut m1, mut m2) = (EF::ZERO, EF::ZERO);
    for t in 0..rt.len() {
        let w = F::from_u64(1u64 << t);
        m1 += rt[t] * w;
        m2 += rt[t] * (w * w);
        for t2 in t + 1..rt.len() {
            m2 += rt[t] * rt[t2] * F::from_u64(2u64 << (t + t2));
        }
    }
    let four = F::from_u64(4);
    pub_q += kt * (th2 - th * (m1 * four + EF::ONE) + m2 * four + m1.double());
    pub_q += EF::ONE - xm - ky - kt;
    let mut s = c.gp * (c.p_leaf - kt * c.t_claim - pub_p) + c.gq * (c.q_leaf - pub_q);
    for i in 0..c.n {
        s += c.omega[i] * F::from_u8(c.nu[i]);
    }
    let st0 = region::coeffs(2).st[0];
    for ch in 0..proj::chunks(c.n) {
        for j in 0..TRIALS {
            let rhs = fi128(QI as i128 * c.quot[ch][j] as i128 + ctr(a.d[ch][j] as u32) as i128 + XOFF as i128 * a.ss[ch][j]) + st0 * fi128(a.sr[ch][j]);
            s += c.mu[ch][j] * rhs;
        }
    }
    s
}

/// The seven public master columns at the master point r.
fn public_at_r9(c: &Ctx9, a: &Agg9, r: &[EF]) -> [EF; 7] {
    let (kx, ky) = (c.tree.kx(&c.rho), c.tree.ky(&c.rho));
    let (mut pz, mut pr, mut pp) = (EF::ZERO, EF::ZERO, EF::ZERO);
    for ch in 0..proj::chunks(c.n) {
        for j in 0..TRIALS {
            pz += c.mu[ch][j] * a.pz[ch][j];
            pr += c.mu[ch][j] * a.rr[ch][j];
            pp += c.mu[ch][j] * a.rp[ch][j];
        }
    }
    let log_n = c.n.trailing_zeros() as usize;
    let eq_hi = eq_table(&r[11..11 + log_n]);
    let om: EF = (0..c.n).map(|i| c.omega[i] * eq_hi[i]).sum();
    [kx * a.wx, ky * eq_pts(r, &c.rho[..c.tree.log_dc]), pz, pr, pp, eq_pts(r, &c.tau), om]
}

fn build_public9(c: &Ctx9, s_all: &[i32], ch: &Challenges, eq_rho: &[EF]) -> Vec<Vec<EF>> {
    let dc = 1usize << c.tree.log_dc;
    let (kx, ky) = (c.tree.kx(&c.rho), c.tree.ky(&c.rho));
    let eq_tau = eq_table(&c.tau);
    let mut cols: Vec<Vec<EF>> = (0..7).map(|_| vec![EF::ZERO; dc]).collect();
    let per = TRIALS * L * N;
    {
        let mut slices: Vec<&mut [EF]> = cols.iter_mut().map(|v| v.as_mut_slice()).collect();
        let (a, rest) = slices.split_at_mut(1);
        let (b, rest) = rest.split_at_mut(1);
        let (z, rest) = rest.split_at_mut(1);
        let (rh, rest) = rest.split_at_mut(1);
        let (rp, rest) = rest.split_at_mut(1);
        let (et, om) = rest.split_at_mut(1);
        a[0].par_chunks_mut(SLOTS)
            .zip(b[0].par_chunks_mut(SLOTS))
            .zip(z[0].par_chunks_mut(SLOTS))
            .zip(rh[0].par_chunks_mut(SLOTS))
            .zip(rp[0].par_chunks_mut(SLOTS))
            .zip(et[0].par_chunks_mut(SLOTS))
            .zip(om[0].par_chunks_mut(SLOTS))
            .enumerate()
            .for_each(|(i, ((((((wx, wy), ze), rhv), rpv), etv), omv))| {
                let mu = &c.mu[i / CHUNK];
                let s = &s_all[i * per..(i + 1) * per];
                for t in 0..SLOTS {
                    let b = i * SLOTS + t;
                    let er = eq_rho[b];
                    if t < L * N {
                        wx[t] = kx * er;
                        let mut zp = EF::ZERO;
                        for j in 0..TRIALS {
                            zp += mu[j] * fi(s[j * L * N + t] as i64);
                        }
                        ze[t] = zp;
                    }
                    wy[t] = ky * er;
                    let (mut a1, mut a2) = (EF::ZERO, EF::ZERO);
                    for j in 0..TRIALS {
                        a1 += mu[j] * fi(ch.r_centered(j, i, t));
                        a2 += mu[j] * fi(r_prime(ch, j, i, t));
                    }
                    rhv[t] = a1;
                    rpv[t] = a2;
                    etv[t] = eq_tau[b];
                    omv[t] = c.omega[i];
                }
            });
    }
    cols
}

// ---------------------------------------------------------------- hash-side public data

/// Masked output part of slot 8: sum_i eq(r_i, i) sum_{s < 512} eq(r_s, s) (1 - 2 c_tilde_i[s]).
fn ct_mle(ct: &[u8], rs: &[EF], ri: &[EF]) -> EF {
    let es = eq_table(rs);
    let ei = eq_table(ri);
    let n = ei.len();
    (0..n)
        .into_par_iter()
        .map(|i| {
            let mut acc = EF::ZERO;
            for s in 0..CT_BITS {
                let bit = (ct[64 * i + s / 8] >> (s % 8)) & 1;
                if bit == 1 { acc -= es[s] } else { acc += es[s] }
            }
            ei[i] * acc
        })
        .sum()
}

/// Same for the public mu bits of block 0 (cells s < 512 of slot 0).
fn mu_mle(mus: &[[u8; 64]], rs: &[EF], ri: &[EF]) -> EF {
    let es = eq_table(rs);
    let ei = eq_table(ri);
    (0..mus.len())
        .into_par_iter()
        .map(|i| {
            let mut acc = EF::ZERO;
            for s in 0..CT_BITS {
                let bit = (mus[i][s / 8] >> (s % 8)) & 1;
                if bit == 1 { acc -= es[s] } else { acc += es[s] }
            }
            ei[i] * acc
        })
        .sum()
}

/// eq4(r, q) on the four slot coordinates.
fn eq_q(r: &[EF], q: usize) -> EF {
    crate::field::eq_at(r, q)
}

/// Point splits of a Keccak-batch point (s: 0..11, q: 11..15, i: 15..).
fn split_k(p: &[EF]) -> (&[EF], &[EF], &[EF]) {
    (&p[..LOGW], &p[LOGW..LOGW + LOGQ], &p[LOGW + LOGQ..])
}

/// The masked-output claim from the eight T openings and the public c_tilde.
fn masked_claim(o: &[EF], r0: &[EF], ct: &[u8]) -> EF {
    let (rs, rq, ri) = split_k(r0);
    let mut c: EF = (0..8).map(|q| eq_q(rq, q) * o[q]).sum();
    c += eq_q(rq, 8) * ct_mle(ct, rs, ri);
    c
}

/// MLE at a of b -> eq(r0, b) mask(b), mask = [q < 8] + [q = 8][s < 512].
fn mask_weight(a: &[EF], r0: &[EF]) -> EF {
    let (as_, aq, ai) = split_k(a);
    let (bs, bq, bi) = split_k(r0);
    let one = EF::ONE;
    let e_i = eq_pts(ai, bi);
    let e_all = eq_pts(as_, bs);
    let e_512 = eq_pts(&as_[..9], &bs[..9]) * (one - as_[9]) * (one - bs[9]) * (one - as_[10]) * (one - bs[10]);
    let q_lt8 = eq_pts(&aq[..3], &bq[..3]) * (one - aq[3]) * (one - bq[3]);
    let q_8 = (0..3).fold(one, |acc, t| acc * (one - aq[t]) * (one - bq[t])) * aq[3] * bq[3];
    e_i * (q_lt8 * e_all + q_8 * e_512)
}

/// Public s-patterns of the input link: a = [s < 1600], a8 = [s < 1600] (1 - 2 pad(s)) on the
/// rate, bp = -2 [s < 1088], cp = -2 [512 <= s < 1088].
fn link_patterns() -> [Vec<F>; 4] {
    let a = (0..W).map(|s| if s < STATE { F::ONE } else { F::ZERO }).collect();
    let a8 = (0..W).map(|s| if s >= STATE { F::ZERO } else if s < RATE_BITS && pad_bit(s) == 1 { -F::ONE } else { F::ONE }).collect();
    let bp = (0..W).map(|s| if s < RATE_BITS { -F::TWO } else { F::ZERO }).collect();
    let cp = (0..W).map(|s| if (CT_BITS..RATE_BITS).contains(&s) { -F::TWO } else { F::ZERO }).collect();
    [a, a8, bp, cp]
}

/// Public part of the input claim: slot 0 holds 1 - 2 mu on s < 512, 1 on 512 <= s < 1600 (the
/// U bits enter through the witness part).
fn link_public(r2: &[EF], mus: &[[u8; 64]]) -> EF {
    let (rs, rq, ri) = split_k(r2);
    let es = eq_table(rs);
    let ones: EF = es[CT_BITS..STATE].iter().copied().sum();
    eq_q(rq, 0) * (mu_mle(mus, rs, ri) + ones)
}

/// The input-link summand. v = [Wa, Wa8, Wb, Wc, T1..T8, U0..U7], with Wp(x) = eq(r2_si, x) p(s)
/// for the four public patterns p, and e_q = eq4(r2_q, q):
///   Wa sum_{q=1..7} e_q T_q + e_8 Wa8 T_8 + Wb sum_{q=1..7} e_q T_q U_q + e_0 Wc U_0  (degree 3).
#[inline(always)]
fn link_f(e: &[EF; 9], v: &[EF]) -> EF {
    let (wa, wa8, wb, wc) = (v[0], v[1], v[2], v[3]);
    let t = &v[4..12];
    let u = &v[12..20];
    let mut lin = EF::ZERO;
    let mut quad = EF::ZERO;
    for q in 1..8 {
        lin += e[q] * t[q - 1];
        quad += e[q] * t[q - 1] * u[q];
    }
    wa * lin + e[8] * wa8 * t[7] + wb * quad + e[0] * wc * u[0]
}

/// The four weighted-pattern MLEs at rho: eq(rho_i, r2_i) sum_s eq(rho_s, s) eq(r2_s, s) p(s).
fn link_weights_at(rho_x: &[EF], r2s: &[EF], r2i: &[EF]) -> [EF; 4] {
    let (rs, ri) = (&rho_x[..LOGW], &rho_x[LOGW..]);
    let ea = eq_table(rs);
    let eb = eq_table(r2s);
    let ei = eq_pts(ri, r2i);
    let pats = link_patterns();
    core::array::from_fn(|k| ei * (0..W).map(|s| ea[s] * eb[s] * pats[k][s]).sum::<EF>())
}

/// Bit-wiring weights over y = coefficient + 2048 plane: M(y) = gamma_q eq(rho_s, s) at the
/// unique (q, s) carrying that bit.
fn wiring_weights(gam: &[EF], rho_s: &[EF]) -> Vec<EF> {
    let es = eq_table(rho_s);
    (0..4 * SLOTS)
        .map(|y| {
            let (plane, coef) = (y / SLOTS, y % SLOTS);
            let (q, s) = upos_of(plane, coef);
            gam[q] * es[s]
        })
        .collect()
}

/// Re-indexed bit columns U_q(i, s) (q = 0..7) over x = s + 2048 i.
fn reindexed_bits(bits: &[Vec<F>; 4], n: usize) -> Vec<Vec<F>> {
    (0..8)
        .map(|q| {
            let mut v = vec![F::ZERO; n * SLOTS];
            v.par_chunks_mut(SLOTS).enumerate().for_each(|(i, row)| {
                for s in 0..RATE_BITS {
                    if let Src::U { plane, coef } = src_of(q, s) {
                        row[s] = bits[plane][i * SLOTS + coef];
                    }
                }
            });
            v
        })
        .collect()
}


// ---------------------------------------------------------------- low-memory Keccak trace

/// The low-memory prover path (checkpointed rounds, folded-input layer rounds, factored mask
/// weights). It produces the same certificate bytes; it is used from N = 512 on, or always with
/// H9_LOWMEM set.
fn low_memory(n: usize) -> bool {
    n >= 512 || std::env::var("H9_LOWMEM").is_ok()
}

/// Pack Keccak rows (16 slots per signature) to one 1600-bit state per real slot; None unless
/// every real slot is +-1 on the state cells and 0 on padding and every dummy slot is zero.
fn pack_rows(v: &[F], n: usize) -> Option<Vec<[u64; 25]>> {
    let out: Vec<Option<[u64; 25]>> = (0..16 * n)
        .into_par_iter()
        .map(|p| {
            let row = &v[p * W..(p + 1) * W];
            if p % 16 >= NPERM {
                return if row.iter().all(|&x| x == F::ZERO) { Some([0u64; 25]) } else { None };
            }
            keccak::decode(row)
        })
        .collect();
    out.into_iter().collect()
}

fn unpack_rows(pk: &[[u64; 25]], n: usize) -> Vec<F> {
    let mut v = vec![F::ZERO; 16 * n * W];
    v.par_chunks_mut(W).enumerate().for_each(|(p, row)| {
        if p % 16 < NPERM {
            for s in 0..STATE {
                row[s] = pm(state_bit(&pk[p], s));
            }
        }
    });
    v
}

/// Keccak layer inputs: all 73 arrays, or the 25 packed round boundaries with the two inner
/// layers of a round recomputed on demand.
enum Trace {
    Full(Vec<Vec<F>>),
    Packed { ck: Vec<Vec<[u64; 25]>>, cur: Option<(usize, Vec<F>, Vec<F>, Vec<F>)> },
}

impl Trace {
    fn build(inp: Vec<F>, n: usize, sp: &[keccak::Spec], lowmem: bool) -> Trace {
        let rows = 16 * n;
        if lowmem && pack_rows(&inp, n).is_some() {
            let mut ck = Vec::with_capacity(25);
            let mut cur = inp;
            for r in 0..24 {
                ck.push(pack_rows(&cur, n).expect("canonical round input"));
                let a = keccak::apply(&sp[3 * r], &cur, rows);
                drop(cur);
                let b = keccak::apply(&sp[3 * r + 1], &a, rows);
                drop(a);
                cur = keccak::apply(&sp[3 * r + 2], &b, rows);
            }
            ck.push(pack_rows(&cur, n).expect("canonical output"));
            Trace::Packed { ck, cur: None }
        } else {
            let mut layers = Vec::with_capacity(sp.len() + 1);
            layers.push(inp);
            for s in sp {
                let next = keccak::apply(s, layers.last().unwrap(), rows);
                layers.push(next);
            }
            Trace::Full(layers)
        }
    }
    fn output(&self, n: usize) -> Vec<F> {
        match self {
            Trace::Full(l) => l.last().unwrap().clone(),
            Trace::Packed { ck, .. } => unpack_rows(&ck[24], n),
        }
    }
    /// The input of layer k (called for k = 71 down to 0).
    fn input(&mut self, k: usize, n: usize, sp: &[keccak::Spec]) -> &[F] {
        match self {
            Trace::Full(l) => {
                l.truncate(k + 1);
                &l[k]
            }
            Trace::Packed { ck, cur } => {
                let r = k / 3;
                if cur.as_ref().map(|c| c.0) != Some(r) {
                    *cur = None;
                    let a0 = unpack_rows(&ck[r], n);
                    let a1 = keccak::apply(&sp[3 * r], &a0, 16 * n);
                    let a2 = keccak::apply(&sp[3 * r + 1], &a1, 16 * n);
                    *cur = Some((r, a0, a1, a2));
                }
                let c = cur.as_mut().unwrap();
                match k % 3 {
                    2 => &c.3,
                    1 => {
                        c.3 = Vec::new();
                        &c.2
                    }
                    _ => {
                        c.2 = Vec::new();
                        &c.1
                    }
                }
            }
        }
    }
}

/// The mask sumcheck with factored weights: while the signature bits are bound, eq over them is
/// split off and the (slot, cell) weight table stays small; the remaining 15 variables run the
/// plain sumcheck on folded columns. Same messages as gen_prove over [out, eq(r0, .) mask].
fn mask_prove_lm<T: Fs>(out: &[F], r0: &[EF], mut claim: EF, tr: &mut T, msgs: &mut Vec<EF>) -> (Vec<EF>, EF) {
    let nv = r0.len();
    let ln = nv - LOGW - LOGQ;
    let sq = 16 * W;
    let (rs, rq, ri) = split_k(r0);
    let es = eq_table(rs);
    let eqv = eq_table(rq);
    let wqs: Vec<EF> = (0..sq).map(|c| {
        let (q, s) = (c / W, c % W);
        if q < 8 || (q == 8 && s < CT_BITS) { eqv[q] * es[s] } else { EF::ZERO }
    }).collect();
    let mut point = vec![EF::ZERO; nv];
    let mut cf = EF::ONE;
    let mut vf: Vec<EF> = Vec::new();
    for m in (1..=ln).rev() {
        let half = 1usize << (m - 1);
        let first = vf.is_empty();
        let ep = eq_table(&ri[..m - 1]);
        let lsum = |hi: bool| -> EF {
            (0..half)
                .into_par_iter()
                .map(|ip| {
                    let row = ip + if hi { half } else { 0 };
                    let mut acc = EF::ZERO;
                    for c in 0..NPERM * W {
                        let w = wqs[c];
                        acc += w * if first { EF::from(out[row * sq + c]) } else { vf[row * sq + c] };
                    }
                    ep[ip] * acc
                })
                .sum()
        };
        let (l0, l1) = (lsum(false), lsum(true));
        let x = ri[m - 1];
        let h0 = cf * (EF::ONE - x) * l0;
        let h2 = cf * (x * F::from_u64(3) - EF::ONE) * (l1.double() - l0);
        let msg = [h0, h2];
        tr.absorb_efs(&msg);
        msgs.extend_from_slice(&msg);
        let r = tr.sample_ef();
        claim = gen_next(&msg, claim, r);
        point[LOGW + LOGQ + m - 1] = r;
        cf *= crate::field::eq1(x, r);
        let mut nf = vec![EF::ZERO; half * sq];
        nf.par_chunks_mut(sq).enumerate().for_each(|(ip, row)| {
            for c in 0..NPERM * W {
                let (lo, hi) = if first { (EF::from(out[ip * sq + c]), EF::from(out[(ip + half) * sq + c])) } else { (vf[ip * sq + c], vf[(ip + half) * sq + c]) };
                row[c] = lo + r * (hi - lo);
            }
        });
        vf = nf;
    }
    let col: Vec<EF> = if vf.is_empty() { out.iter().map(|&x| EF::from(x)).collect() } else { vf };
    let wcol: Vec<EF> = wqs.iter().map(|&w| cf * w).collect();
    let (pt15, fin) = gen_prove(&[], vec![col, wcol], 2, claim, &|v: &[EF]| v[0] * v[1], tr, msgs);
    point[..LOGW + LOGQ].copy_from_slice(&pt15);
    (point, fin[0])
}

/// The Keccak input layer, bit-packed (slot p = 16 i + q holds S_q xor block_q for q < 9; the
/// dummy slots are zero words and are never read). Only for canonical inputs (no in_extra).
fn packed_input(wit: &Wit9) -> keccak::kec10::PLayer {
    use keccak::kec10::WORDS;
    let n = wit.w.n;
    let mut bits = vec![0u64; 16 * n * WORDS];
    bits.par_chunks_mut(16 * WORDS).enumerate().for_each(|(i, sig)| {
        for q in 0..NPERM {
            let mut st = if q == 0 { [0u64; 25] } else { wit.states[i][q - 1] };
            xor_block(&mut st, &wit.blocks[i][q]);
            sig[q * WORDS..q * WORDS + 25].copy_from_slice(&st);
        }
    });
    keccak::kec10::PLayer { bits, support: (1 << 25) - 1 }
}

/// Active-slot sign conversion of the packed trace (hostile gate): unpacking the packed input
/// layer gives exactly the field-valued input rows (bit 0 -> +1, bit 1 -> -1, padding cells
/// and dummy slots -> 0). Returns (cells checked, cells equal).
pub fn sign_conversion_check(wit: &Wit9) -> (usize, usize) {
    let n = wit.w.n;
    let f = input_rows(wit);
    let u = keccak::kec10::unpack(&packed_input(wit), 16 * n, NPERM);
    (f.len(), f.iter().zip(&u).filter(|(a, b)| a == b).count())
}

/// The mask sumcheck from the packed output layer; same messages as `mask_prove_lm`. The
/// summand is linear in the output, so while the signature bits are bound it folds one scalar
/// per signature, A_i = sum_c w(c) out(i, c), instead of the 16 x 2048 cells; the folded cells
/// are then sum_i e_i out(i, c) with e the eq weights of the bound bits.
fn mask_prove_k10<T: Fs>(out: &keccak::kec10::PLayer, r0: &[EF], mut claim: EF, tr: &mut T, msgs: &mut Vec<EF>) -> (Vec<EF>, EF) {
    use keccak::kec10::WORDS;
    let nv = r0.len();
    let ln = nv - LOGW - LOGQ;
    let n = 1usize << ln;
    let sq = 16 * W;
    let (rs, rq, ri) = split_k(r0);
    let es = eq_table(rs);
    let eqv = eq_table(rq);
    let wqs: Vec<EF> = (0..sq).map(|c| {
        let (q, s) = (c / W, c % W);
        if q < 8 || (q == 8 && s < CT_BITS) { eqv[q] * es[s] } else { EF::ZERO }
    }).collect();
    let on_sup = |s: usize| out.support >> (s / 64) & 1 == 1;
    // Per (slot, word, byte): subset sums of the eight weights, for sum_{bit = 1} w.
    let nb = NPERM * WORDS * 8;
    let tabs: Vec<[EF; 256]> = (0..nb).into_par_iter().map(|t| {
        let (q, rest) = (t / (WORDS * 8), t % (WORDS * 8));
        let (w, by) = (rest / 8, rest % 8);
        let mut tab = [EF::ZERO; 256];
        for k in 0..8 {
            let c = q * W + 64 * w + 8 * by + k;
            for m in (1usize << k)..(2usize << k) {
                tab[m] = tab[m & !(1 << k)] + if on_sup(c % W) { wqs[c] } else { EF::ZERO };
            }
        }
        tab
    }).collect();
    let wsum: EF = (0..NPERM * W).filter(|&c| on_sup(c % W)).map(|c| wqs[c]).sum();
    let mut a: Vec<EF> = (0..n).into_par_iter().map(|i| {
        let mut neg = EF::ZERO;
        for q in 0..NPERM {
            let row = &out.bits[(16 * i + q) * WORDS..(16 * i + q + 1) * WORDS];
            for w in 0..WORDS {
                if out.support >> w & 1 == 0 {
                    continue;
                }
                for by in 0..8 {
                    let b = (row[w] >> (8 * by)) as u8 as usize;
                    if b != 0 {
                        neg += tabs[(q * WORDS + w) * 8 + by][b];
                    }
                }
            }
        }
        wsum - neg.double()
    }).collect();
    drop(tabs);
    let mut point = vec![EF::ZERO; nv];
    let mut cf = EF::ONE;
    for m in (1..=ln).rev() {
        let half = 1usize << (m - 1);
        let ep = eq_table(&ri[..m - 1]);
        let l0: EF = (0..half).into_par_iter().map(|ip| ep[ip] * a[ip]).sum();
        let l1: EF = (0..half).into_par_iter().map(|ip| ep[ip] * a[ip + half]).sum();
        let x = ri[m - 1];
        let h0 = cf * (EF::ONE - x) * l0;
        let h2 = cf * (x * F::from_u64(3) - EF::ONE) * (l1.double() - l0);
        let msg = [h0, h2];
        tr.absorb_efs(&msg);
        msgs.extend_from_slice(&msg);
        let r = tr.sample_ef();
        claim = gen_next(&msg, claim, r);
        point[LOGW + LOGQ + m - 1] = r;
        cf *= crate::field::eq1(x, r);
        let (lo, hi) = a.split_at_mut(half);
        lo.par_iter_mut().zip(hi.par_iter()).for_each(|(x, &y)| *x += r * (y - *x));
        a.truncate(half);
    }
    // col(c) = sum_i e_i out(i, c): E - 2 sum_{i: bit} e_i on the support of real slots.
    let e = eq_table(&point[LOGW + LOGQ..]);
    let esum: EF = e.par_iter().copied().sum();
    let chunk = (n / 256).max(8);
    let neg: Vec<EF> = (0..n.div_ceil(chunk)).into_par_iter().map(|cidx| {
        let mut acc = vec![EF::ZERO; NPERM * W];
        let mut tab = [EF::ZERO; 256];
        let (i0, i1) = (cidx * chunk, ((cidx + 1) * chunk).min(n));
        let mut i = i0;
        while i < i1 {
            let g = (i1 - i).min(8);
            for k in 0..g {
                for m in (1usize << k)..(2usize << k) {
                    tab[m] = tab[m & !(1 << k)] + e[i + k];
                }
            }
            for q in 0..NPERM {
                for w in 0..WORDS {
                    if out.support >> w & 1 == 0 {
                        continue;
                    }
                    let mut idx = [0u8; 64];
                    for k in 0..g {
                        let wd = out.bits[(16 * (i + k) + q) * WORDS + w];
                        for z in 0..64 {
                            idx[z] |= (((wd >> z) & 1) as u8) << k;
                        }
                    }
                    for z in 0..64 {
                        if idx[z] != 0 {
                            acc[q * W + 64 * w + z] += tab[idx[z] as usize];
                        }
                    }
                }
            }
            i += g;
        }
        acc
    }).reduce(|| vec![EF::ZERO; NPERM * W], |mut x, y| {
        x.iter_mut().zip(&y).for_each(|(a, b)| *a += *b);
        x
    });
    let mut col = vec![EF::ZERO; sq];
    for c in 0..NPERM * W {
        if on_sup(c % W) {
            col[c] = esum - neg[c].double();
        }
    }
    let wcol: Vec<EF> = wqs.iter().map(|&w| cf * w).collect();
    let (pt15, fin) = gen_prove(&[], vec![col, wcol], 2, claim, &|v: &[EF]| v[0] * v[1], tr, msgs);
    point[..LOGW + LOGQ].copy_from_slice(&pt15);
    (point, fin[0])
}

// ---------------------------------------------------------------- options and reports

/// Test-only switches. `Opts9::default()` is the protocol.
#[derive(Clone, Debug, Default)]
pub struct Opts9 {
    /// UNSAFE control (both sides): gamma_Z replaced by 0 after sampling.
    pub drop_ternarity: bool,
    /// UNSAFE control (both sides): the four Booleanity weights replaced by 0 after sampling.
    pub drop_booleanity: bool,
    /// Gruen round challenges replaced (both sides), as in round 4.
    pub inject: pcs::Inject,
    /// Added to the first quotient (prover only).
    pub quot_delta: i64,
    /// Record every begun round.
    pub log: bool,
    /// Prover only: send the product-of-MLE values for the re-indexed bit claims (the false
    /// shortcut) instead of the evaluations of the re-indexed columns.
    pub shortcut_bits: bool,
    /// Prover only: commit table A with these two columns exchanged.
    pub swap_cols: Option<(usize, usize)>,
    /// Prover only (hostile gate): after theta, use multiplicities with one unit moved between
    /// two table entries for the leaves and the table sumcheck (the committed ones unchanged).
    pub mult_after_theta: bool,
    /// Prover only (Fiat-Shamir tests): derive the coins from this round table instead of the
    /// registered one (another round-1 descriptor, or another profile id in the coin input).
    pub table_override: Option<TableOv>,
}

/// A round table carried by the test options.
#[derive(Clone)]
pub struct TableOv(pub Arc<reg7::Table>);

impl std::fmt::Debug for TableOv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TableOv(profile {:#010x}, {} rounds)", self.0.profile, self.0.len())
    }
}

pub struct Report9 {
    pub transcript_error: Option<String>,
    pub stats: reg7::Stats,
    pub rounds: usize,
    pub log: Option<Vec<reg7::Logged>>,
    pub quotient_inexact: usize,
    pub evals_match_whir: bool,
    pub keccak_ms: f64,
    /// Values at the input-link point used by the shortcut test: (true input claim, the product
    /// of multilinear evaluations at the same point).
    pub shortcut_probe: Option<(EF, EF)>,
}

// ---------------------------------------------------------------- prover

/// Prove a standalone lab statement under the lab profile.
pub fn prove_lab9(records: &[Record], wit: &Wit9, pubs: &[Pub9], nu: &[u8], tm: &mut Timer, o: &Opts9) -> (Cert9, Report9) {
    let n = records.len();
    let man = manifest_lab9(records);
    let ct: Vec<u8> = wit.ct.iter().flatten().copied().collect();
    let x = instance_lab9(lab_profile9(n), &man, records, &ct, nu);
    prove_stmt9(records, &man, &x, lab_profile9(n), wit, pubs, nu, tm, o)
}

#[allow(clippy::too_many_arguments)]
pub fn prove_stmt9(records: &[Record], man: &[u8], x: &[u8], profile: u32, wit: &Wit9, pubs: &[Pub9], nu: &[u8], tm: &mut Timer, o: &Opts9) -> (Cert9, Report9) {
    assert_eq!(man.len(), MANIFEST);
    let n = records.len();
    let mut b = B9::new(n, profile, x, o.inject, o.table_override.as_ref().map(|t| t.0.clone()));
    if o.log {
        b.tr.ch.log = Some(vec![]);
    }
    tm.lap("P0 raw instance absorbed, registered-round transcript init");
    let (c, mut rep) = prove_core9(&mut b, man.to_vec(), wit, pubs, nu, tm, o);
    rep.transcript_error = b.transcript_error();
    rep.stats = b.tr.ch.stats.clone();
    rep.rounds = b.tr.ch.table().len();
    rep.log = b.tr.ch.log.clone();
    (c, rep)
}

#[allow(clippy::too_many_arguments)]
fn prove_core9<B: Backend>(b: &mut B, man: Vec<u8>, wit: &Wit9, pubs: &[Pub9], nu: &[u8], tm: &mut Timer, o: &Opts9) -> (Cert9, Report9) {
    let w = &wit.w;
    let n = w.n;
    let ntt = Ntt::new();
    let tree = Tree::new(n);
    let co = region::all_coeffs();
    let dc = 1usize << tree.log_dc;
    let nc = proj::chunks(n);
    let log_n = n.trailing_zeros() as usize;

    // 1. One commitment: table A = X | Y | S | B0..B3 | T1..T8, table B = m_even | m_odd.
    let tcols = t_columns(wit);
    let nv = stacked_vars9(n);
    let mut order: Vec<&[F]> = vec![&w.x, &w.y, &w.s];
    for bp in &wit.bits {
        order.push(bp);
    }
    for c in &tcols {
        order.push(c);
    }
    if let Some((a, c)) = o.swap_cols {
        order.swap(a, c);
    }
    let mut ta = Vec::with_capacity(NCOL * dc);
    for c in &order {
        ta.extend_from_slice(c);
    }
    drop(order);
    let me: Vec<F> = w.m.iter().step_by(2).copied().collect();
    let mo: Vec<F> = w.m.iter().skip(1).step_by(2).copied().collect();
    let mut tb = Vec::with_capacity(2 << LOG_TAB);
    tb.extend_from_slice(&me);
    tb.extend_from_slice(&mo);
    let wit3 = Layout::new_witness(vec![Table::new(RowMajorMatrix::new(ta, dc)), Table::new(RowMajorMatrix::new(tb, 1 << LOG_TAB))], b.fold0());
    assert_eq!(wit3.num_variables(), nv);
    let (comm, pdata) = b.commit(wit3);
    tm.lap("P1 WHIR commit (one table of 15 columns + multiplicities)");

    // 2-3. Projections and integer lifts with the u term in the witness.
    let src = b.projection();
    // Round 10: a short F_q pool poisons the transcript and yields no coefficients; the prover
    // refuses to continue (it never pads).
    assert!(projection_complete(&src, n), "F_q projection pool short: the prover refuses to prove");
    let ch = src.challenges(&ntt, n);
    let per = TRIALS * L * N;
    let mut s_all = vec![0i32; n * per];
    s_all.par_chunks_mut(per).enumerate().for_each(|(i, out)| ch.s_centered(&ntt, &pubs[i].a_hat, i, out));
    let u_of = |i: usize, t: usize| -> i64 { (0..4).map(|j| (wit.bits[j][i * SLOTS + t].as_canonical_u64() as i64) << j).sum() };
    let e_parts: Vec<[i128; TRIALS]> = (0..n)
        .into_par_iter()
        .map(|i| {
            let base = i * SLOTS;
            let mut e = [0i128; TRIALS];
            for j in 0..TRIALS {
                let s = &s_all[i * per + j * L * N..i * per + (j + 1) * L * N];
                let mut acc: i128 = 0;
                for t in 0..L * N {
                    acc += s[t] as i128 * w.zi[base + t] as i128;
                }
                for t in 0..K * N {
                    acc -= ch.r_centered(j, i, t) as i128 * w.ei[base + t] as i128;
                    acc -= r_prime(&ch, j, i, t) as i128 * u_of(i, t) as i128;
                }
                e[j] = acc;
            }
            e
        })
        .collect();
    let mut dsum = vec![[0u64; TRIALS]; nc];
    for i in 0..n {
        for j in 0..TRIALS {
            dsum[i / CHUNK][j] = (dsum[i / CHUNK][j] + ch.d_part(j, i, &pubs[i].bc)) % mlnat::Q as u64;
        }
    }
    let mut quot = vec![[0i64; TRIALS]; nc];
    let mut qbytes = Vec::with_capacity(5 * TRIALS * nc);
    let mut inexact = 0usize;
    for c in 0..nc {
        for j in 0..TRIALS {
            let mut e: i128 = (c * CHUNK..((c + 1) * CHUNK).min(n)).map(|i| e_parts[i][j]).sum();
            e -= ctr(dsum[c][j] as u32) as i128;
            if e % QI as i128 != 0 {
                inexact += 1;
            }
            let lim = 1i128 << proj::VBITS;
            let mut v = (e.div_euclid(QI as i128)).clamp(-lim, lim - 1) as i64;
            if c == 0 && j == 0 {
                v += o.quot_delta;
            }
            quot[c][j] = v;
            qbytes.extend_from_slice(&proj::encode_quotient(v));
        }
    }
    b.absorb_quotients(&quot, &qbytes);
    tm.lap("P2 projections, integer lifts (u term r' in the witness), quotients");

    // 4. theta and the LogUp GKR (leaves use the class of the committed u).
    let (theta, _) = b.theta();
    let moved;
    let (w, me, mo) = if o.mult_after_theta {
        // Hostile gate: multiplicities chosen after theta (one unit moved from entry 0 to 1).
        let mut wm = w.clone();
        wm.m[0] -= F::ONE;
        wm.m[1] += F::ONE;
        moved = wm;
        let me2: Vec<F> = moved.m.iter().step_by(2).copied().collect();
        let mo2: Vec<F> = moved.m.iter().skip(1).step_by(2).copied().collect();
        (&moved, me2, mo2)
    } else {
        (w, me, mo)
    };
    let (lp, lq) = cert::leaves(&tree, w, theta, &co);
    let (gproof, gout) = gkr::prove(lp, lq, b);
    tm.lap("P3 LogUp leaves and fractional GKR");

    // 5. Leaf pair, T, and the joint block of weights.
    b.absorb_efs(&[gout.p, gout.q]);
    let gp = b.sample_ef();
    let gq = b.sample_ef();
    let rho = gout.point.clone();
    let rt = tree.rho_t(&rho);
    let eqt = eq_table(&rt);
    let (ta_, tb_): (Vec<EF>, Vec<EF>) = (0..1usize << LOG_TAB).into_par_iter().map(|j| (-(theta - efb(F::from_usize(2 * j + 1))), -(theta - efb(F::from_usize(2 * j))))).unzip();
    let t_claim: EF = (0..1usize << LOG_TAB).into_par_iter().map(|j| eqt[j] * (ta_[j] * me[j] + tb_[j] * mo[j])).sum();
    drop(eqt);
    b.absorb_ef(t_claim);
    let gz = b.sample_ef();
    let gb: [EF; 4] = core::array::from_fn(|_| b.sample_ef());
    let tau = b.sample_efs(tree.log_dc);
    let omega = b.sample_efs(n);
    let mu: Vec<[EF; TRIALS]> = (0..nc).map(|_| core::array::from_fn(|_| b.sample_ef())).collect();
    let r0 = b.sample_efs(nvk(n));
    let gz = if o.drop_ternarity { EF::ZERO } else { gz };
    let gb = if o.drop_booleanity { [EF::ZERO; 4] } else { gb };
    let mk = MasterK { g: gp + gq * theta, gq, gz, gb };
    let cx = Ctx9 { n, tree, theta, rho: rho.clone(), p_leaf: gout.p, q_leaf: gout.q, gp, gq, t_claim, mk, tau, omega, mu, quot, nu: nu.to_vec() };
    let eq_rho = eq_table(&rho[..tree.log_dc]);
    let sums: Vec<Sums9> = (0..n).into_par_iter().map(|i| sums9(i, &s_all[i * per..(i + 1) * per], &ch, &pubs[i].bc, &eq_rho, None)).collect();
    let agg = aggregate9(&sums, n);
    let claim = claimed_sum9(&cx, &agg);
    let pubcols = build_public9(&cx, &s_all, &ch, &eq_rho);
    drop(eq_rho);
    drop(s_all);
    tm.lap("P4a master weights, public columns, claimed sum");

    // 6. Master sumcheck, degree 8, over X, Y, S, B0..B3 and seven public columns.
    let mut mmsgs = Vec::new();
    let fm = |v: &[EF]| master_f9(&mk, v);
    let (mpoint, _mfin) = gen_prove(&[&w.x, &w.y, &w.s, &wit.bits[0], &wit.bits[1], &wit.bits[2], &wit.bits[3]], pubcols, MASTER_DEG, claim, &fm, b, &mut mmsgs);
    let master: Vec<Vec<EF>> = mmsgs.chunks(MASTER_DEG).map(|c| c.to_vec()).collect();
    tm.lap("P4b master sumcheck (degree 8)");
    let tout = sumcheck::table_prove(&rt, ta_, tb_, &me, &mo, t_claim, b);
    tm.lap("P4c table sumcheck");

    // 7. Keccak: trace, masked output, mask sumcheck, 72 layers.
    let tk = Instant::now();
    let rows = 16 * n;
    let logp = LOGQ + log_n;
    let sp = keccak::specs();
    let r2_v: (Vec<EF>, EF);
    // Round-10 path: packed trace and selection rounds, for canonical inputs (the dishonest
    // tests that override input cells take the reference paths).
    let k10 = keccak::kec10::on() && wit.in_extra.is_empty();
    let mut kmsgs: Vec<EF> = Vec::new();
    let (r0s, _, r0i) = split_k(&r0);
    let tpt: Vec<EF> = r0s.iter().chain(r0i.iter()).copied().collect();
    let o_vals: Vec<EF> = tcols.par_iter().map(|c| crate::field::mle_eval(c, &tpt)).collect();
    let ctb: Vec<u8> = wit.ct.iter().flatten().copied().collect();
    let mclaim = masked_claim(&o_vals, &r0, &ctb);
    if k10 {
        // The round-10 Keccak working set (packed trace, one folded layer) stays in memory.
        crate::alloc::suppress(std::env::var("H9_SPILL_KECCAK").map(|v| v != "1").unwrap_or(true));
        let mut tr10 = keccak::kec10::Trace10::build(packed_input(wit), rows, NPERM, &sp);
        tm.lap(&format!("P5a Keccak trace (16 N slots; 25 packed round boundaries, {} MiB)", tr10.bytes() >> 20));
        b.absorb_efs(&o_vals);
        kmsgs.extend_from_slice(&o_vals);
        let (r1, v1) = mask_prove_k10(tr10.output(), &r0, mclaim, b, &mut kmsgs);
        b.absorb_ef(v1);
        kmsgs.push(v1);
        tm.lap("P5b masked output and mask sumcheck");
        let (mut pt, mut v) = (r1, v1);
        for k in (0..sp.len()).rev() {
            let s = &sp[k];
            let eqs = eq_table(&pt[..LOGW]);
            let wts: Vec<Vec<EF>> = s.terms.iter().map(|t| (0..W).map(|i| match t.sel[i] { 0 => EF::ZERO, 1 => eqs[i], _ => -eqs[i] }).collect()).collect();
            let vin = tr10.input(k, &sp);
            let maps = keccak::kec10::gmaps(s);
            let (pt2, vals) = keccak::kec10::main_prove_k10(s, &maps, vin, &pt[LOGW..], wts, v, logp, NPERM, b, &mut kmsgs);
            pt = keccak::kec10::wiring_prove_k10(s, vin, &pt2, &vals, logp, NPERM, b, &mut kmsgs);
            v = *kmsgs.last().unwrap();
        }
        drop(tr10);
        crate::alloc::suppress(false);
        r2_v = (pt, v);
    } else {
        let lowmem = low_memory(n);
        let mut trace = Trace::build(input_rows(wit), n, &sp, lowmem);
        let packed = matches!(trace, Trace::Packed { .. });
        tm.lap(if packed { "P5a Keccak trace (16 N slots; 25 packed round boundaries)" } else { "P5a Keccak trace (16 N slots, 72 layers stored)" });
        b.absorb_efs(&o_vals);
        kmsgs.extend_from_slice(&o_vals);
        let (r1, v1) = {
            let out = trace.output(n);
            if packed {
                mask_prove_lm(&out, &r0, mclaim, b, &mut kmsgs)
            } else {
                let mut wm = eq_table(&r0);
                wm.par_chunks_mut(W).enumerate().for_each(|(p, row)| {
                    let q = p % 16;
                    for (s, x) in row.iter_mut().enumerate() {
                        if !(q < 8 || (q == 8 && s < CT_BITS)) {
                            *x = EF::ZERO;
                        }
                    }
                });
                let (r1, mfin) = gen_prove(&[&out], vec![wm], 2, mclaim, &|v: &[EF]| v[0] * v[1], b, &mut kmsgs);
                (r1, mfin[0])
            }
        };
        b.absorb_ef(v1);
        kmsgs.push(v1);
        tm.lap("P5b masked output and mask sumcheck");
        let (mut pt, mut v) = (r1, v1);
        let mut gpool: Vec<Vec<F>> = if packed { vec![] } else { (0..6).map(|_| vec![F::ZERO; rows * W]).collect() };
        let mut epool: Vec<Vec<EF>> = if packed { vec![] } else { (0..6).map(|_| Vec::with_capacity(rows / 2 * W)).collect() };
        for k in (0..sp.len()).rev() {
            let s = &sp[k];
            let vin = trace.input(k, n, &sp);
            let eqs = eq_table(&pt[..LOGW]);
            let wts: Vec<Vec<EF>> = s.terms.iter().map(|t| (0..W).map(|i| match t.sel[i] { 0 => EF::ZERO, 1 => eqs[i], _ => -eqs[i] }).collect()).collect();
            let (pt2, vals) = if packed {
                // Packed rows guarantee zero dummy slots; they stay zero while signature bits fold.
                let skip = |rows_now: usize, p: usize| rows_now > 16 && p % 16 >= NPERM;
                keccak::main_prove_lm(s, vin, &pt[LOGW..], wts, v, logp, b, &mut kmsgs, &skip)
            } else {
                for (j, (g, c)) in s.gathers.iter().zip(gpool.iter_mut()).enumerate() {
                    let act = &s.terms[s.owner[j]].active;
                    c.resize(rows * act.len(), F::ZERO);
                    c.par_chunks_mut(act.len()).enumerate().for_each(|(p, row)| {
                        let src = &vin[p * W..(p + 1) * W];
                        for (x, &a) in row.iter_mut().zip(act.iter()) {
                            *x = src[g[a as usize] as usize];
                        }
                    });
                }
                keccak::main_prove(s, &gpool, &mut epool, &pt[LOGW..], wts, v, logp, b, &mut kmsgs)
            };
            pt = keccak::wiring_prove(s, vin, &pt2, &vals, logp, b, &mut kmsgs);
            v = *kmsgs.last().unwrap();
        }
        drop(trace);
        drop(gpool);
        drop(epool);
        r2_v = (pt, v);
    }
    tm.lap("P5c Keccak GKR (72 layer reductions)");
    let (pt, v) = r2_v;

    // 8. Input link over x = (s, i): the input claim minus its public part.
    let r2 = pt;
    let (r2s, r2q, r2i) = split_k(&r2);
    let mus: Vec<[u8; 64]> = pubs.iter().map(|p| p.mu).collect();
    let lclaim = v - link_public(&r2, &mus);
    let e9: [EF; 9] = core::array::from_fn(|q| eq_q(r2q, q));
    let xpt: Vec<EF> = r2s.iter().chain(r2i.iter()).copied().collect();
    let weq = eq_table(&xpt);
    let pats = link_patterns();
    let ub = reindexed_bits(&wit.bits, n);
    // Shortcut probe (tests): the input claim against the false shortcut that evaluates the
    // XOR link on multilinear evaluations of T, U and the patterns at the same point.
    let probe = {
        let tv: Vec<EF> = tcols.iter().map(|c| crate::field::mle_eval(c, &xpt)).collect();
        let uv: Vec<EF> = ub.iter().map(|c| crate::field::mle_eval(c, &xpt)).collect();
        let es = eq_table(r2s);
        let mut vals: Vec<EF> = pats.iter().map(|p| (0..W).map(|s| es[s] * p[s]).sum()).collect();
        vals.extend_from_slice(&tv);
        vals.extend_from_slice(&uv);
        Some((v, link_public(&r2, &mus) + link_f(&e9, &vals)))
    };
    let ext: Vec<Vec<EF>> = pats.iter().map(|p| (0..n * SLOTS).into_par_iter().map(|x| weq[x] * p[x % SLOTS]).collect()).collect();
    drop(weq);
    let mut base: Vec<&[F]> = vec![];
    for c in &tcols {
        base.push(c);
    }
    for c in &ub {
        base.push(c);
    }
    // f receives base (T1..T8, U0..U7) first, then ext (Wa, Wa8, Wb, Wc).
    let fl = |vv: &[EF]| {
        let mut r = [EF::ZERO; 20];
        r[..4].copy_from_slice(&vv[16..20]);
        r[4..20].copy_from_slice(&vv[..16]);
        link_f(&e9, &r)
    };
    let (rho_x, lfin) = gen_prove(&base, ext, 3, lclaim, &fl, b, &mut kmsgs);
    let mut uvals: Vec<EF> = lfin[8..16].to_vec();
    if o.shortcut_bits {
        // False shortcut: U_q(rho) replaced by the bit-plane evaluation at rho (product of MLEs).
        uvals = (0..8).map(|q| crate::field::mle_eval(&wit.bits[q % 4], &rho_x)).collect();
    }
    b.absorb_efs(&uvals);
    kmsgs.extend_from_slice(&uvals);
    let gam = b.sample_efs(8);
    tm.lap("P5d input-link sumcheck");

    // 9. Bit wiring: sum_q gamma_q U_q(rho) = sum_y M(y) Bhat(y).
    let (rho_s, rho_i) = (&rho_x[..LOGW], &rho_x[LOGW..]);
    let mw = wiring_weights(&gam, rho_s);
    let ei = eq_table(rho_i);
    let bhat: Vec<EF> = (0..4 * SLOTS).into_par_iter().map(|y| {
        let (plane, coef) = (y / SLOTS, y % SLOTS);
        (0..n).map(|i| ei[i] * wit.bits[plane][i * SLOTS + coef]).sum()
    }).collect();
    let bclaim: EF = gam.iter().zip(&uvals).map(|(&g, &u)| g * u).sum();
    let (rho_w, _) = gen_prove(&[], vec![mw, bhat], 2, bclaim, &|v: &[EF]| v[0] * v[1], b, &mut kmsgs);
    tm.lap("P5e bit-wiring sumcheck");
    let keccak_ms = tk.elapsed().as_secs_f64() * 1e3;
    let _ = rho_i;

    // 10. One WHIR proof of the 29 openings.
    let bw_pt: Vec<EF> = rho_w[..LOGW].iter().chain(rho_x[LOGW..].iter()).copied().collect();
    let proto = protocol9(tree.log_dc);
    let (proof, ev) = b.open_at(pdata, &proto, &[p3_point(&mpoint), p3_point(&tpt), p3_point(&rho_x), p3_point(&bw_pt), p3_point(&tout.point)]);
    let ok = ev[1] == o_vals && ev[4] == tout.evals[..];
    let whir = bincode::serialize(&proof).unwrap();
    tm.lap("P6 WHIR opening (29 values, 5 points)");

    let mut kec = Vec::with_capacity(40 * kmsgs.len());
    kmsgs.iter().for_each(|x| crate::field::ef_to_bytes(x, &mut kec));
    assert_eq!(kmsgs.len(), kec_elems(n), "Keccak frontend length");
    let cert = Cert9 {
        manifest: man,
        ct: ctb,
        nu: nu.to_vec(),
        quot: qbytes,
        comm: words_to_bytes(&comm.roots()[0]),
        gkr: gproof,
        leaf_pair: [gout.p, gout.q],
        t_claim,
        master,
        table: tout.rounds,
        kec,
        whir,
    };
    let rep = Report9 { transcript_error: None, stats: Default::default(), rounds: 0, log: None, quotient_inexact: inexact, evals_match_whir: ok, keccak_ms, shortcut_probe: probe };
    (cert, rep)
}

// ---------------------------------------------------------------- verifier

pub fn verify_lab9(records: &[Record], bytes: &[u8], tm: &mut Timer, o: &Opts9) -> Result<(), Reject> {
    let n = records.len();
    let man = manifest_lab9(records);
    let table = registered_table9(lab_profile9(n), n).ok_or_else(|| Reject::Profile("no hidden-u lab profile for this count".into()))?;
    let cert = Cert9::from_bytes(n, bytes)?;
    let x = instance_lab9(table.profile, &man, records, &cert.ct, &cert.nu);
    verify_stmt9(records, &man, &x, table, bytes, tm, o).0
}

pub struct VInspect9 {
    pub stats: reg7::Stats,
    pub log: Option<Vec<reg7::Logged>>,
}

#[allow(clippy::too_many_arguments)]
pub fn verify_stmt9(records: &[Record], man: &[u8], x: &[u8], table: Arc<reg7::Table>, bytes: &[u8], tm: &mut Timer, o: &Opts9) -> (Result<(), Reject>, Option<VInspect9>) {
    let n = records.len();
    if table.n != n {
        return (Err(Reject::Profile(format!("profile {:#010x} fixes N = {}, statement has {n}", table.profile, table.n))), None);
    }
    let pre = || -> Result<(Cert9, pcs::PcsProof10), Reject> {
        let cert = Cert9::from_bytes(n, bytes)?;
        if cert.manifest != man {
            return Err(Reject::Manifest);
        }
        if let Some(i) = cert.nu.iter().position(|&v| v > NU_MAX) {
            return Err(Reject::HintCountByte(i));
        }
        let proof: pcs::PcsProof10 = bincode::deserialize(&cert.whir).map_err(|_| Reject::Parse("WHIR proof"))?;
        if bincode::serialize(&proof).map_err(|_| Reject::Parse("WHIR proof"))? != cert.whir {
            return Err(Reject::Parse("WHIR proof is not the canonical encoding (trailing or non-canonical bytes)"));
        }
        Ok((cert, proof))
    };
    let (cert, proof) = match pre() {
        Ok(v) => v,
        Err(e) => return (Err(e), None),
    };
    // The UNSAFE controls and the challenge injection reach a verifier only in lab-hooks builds.
    let inject = if cfg!(feature = "lab-hooks") { o.inject } else { pcs::Inject::Off };
    let mut b = B9::new(n, table.profile, x, inject, Some(table));
    if o.log {
        b.tr.ch.log = Some(vec![]);
    }
    let r = verify_core9(&mut b, records, &cert, &proof, tm, o);
    let r = match (r, b.transcript_error()) {
        (Ok(_), Some(e)) => Err(Reject::Transcript(e)),
        (r, _) => r,
    };
    (r, Some(VInspect9 { stats: b.tr.ch.stats.clone(), log: b.tr.ch.log.clone() }))
}

fn verify_core9<B: Backend>(b: &mut B, records: &[Record], cert: &Cert9, proof: &B::Proof, tm: &mut Timer, o: &Opts9) -> Result<(), Reject> {
    let n = records.len();
    let ntt = Ntt::new();
    let tree = Tree::new(n);
    let nc = proj::chunks(n);
    let log_n = n.trailing_zeros() as usize;
    let logp = LOGQ + log_n;
    let quot: Vec<[i64; TRIALS]> = (0..nc).map(|c| core::array::from_fn(|j| proj::decode_quotient(&cert.quot[5 * (c * TRIALS + j)..5 * (c * TRIALS + j) + 5]))).collect();
    let comm: Commitment = MerkleCap::new(vec![core::array::from_fn(|i| u64::from_le_bytes(cert.comm[8 * i..8 * i + 8].try_into().unwrap()))]);
    let cts: Vec<[u8; 64]> = cert.ct.chunks_exact(64).map(|c| c.try_into().unwrap()).collect();
    tm.lap("V0 parse, manifest, byte checks");

    // Transcript replay.
    b.observe_commitment(&comm);
    let src = b.projection();
    if !projection_complete(&src, n) {
        return Err(Reject::Transcript("F_q projection pool short".into()));
    }
    b.absorb_quotients(&quot, &cert.quot);
    let (theta, _) = b.theta();
    let gout = gkr::verify(&cert.gkr, tree.d, b).map_err(|e| Reject::Gkr(format!("{e:?}")))?;
    if cert.leaf_pair != [gout.p, gout.q] {
        return Err(Reject::LeafPair);
    }
    b.absorb_efs(&[gout.p, gout.q]);
    let gp = b.sample_ef();
    let gq = b.sample_ef();
    b.absorb_ef(cert.t_claim);
    let gz = b.sample_ef();
    let gb: [EF; 4] = core::array::from_fn(|_| b.sample_ef());
    let tau = b.sample_efs(tree.log_dc);
    let omega = b.sample_efs(n);
    let mu: Vec<[EF; TRIALS]> = (0..nc).map(|_| core::array::from_fn(|_| b.sample_ef())).collect();
    let r0 = b.sample_efs(nvk(n));
    let lab = cfg!(feature = "lab-hooks");
    let gz = if lab && o.drop_ternarity { EF::ZERO } else { gz };
    let gb = if lab && o.drop_booleanity { [EF::ZERO; 4] } else { gb };
    if cert.master.len() != tree.log_dc {
        return Err(Reject::Master("round count"));
    }
    let mut r = vec![EF::ZERO; tree.log_dc];
    let mut mrs = Vec::with_capacity(tree.log_dc);
    for (idx, h) in cert.master.iter().enumerate() {
        b.absorb_efs(h);
        let x = b.sample_ef();
        r[tree.log_dc - 1 - idx] = x;
        mrs.push(x);
    }
    let rt = tree.rho_t(&gout.point);
    let (spt, tfinal) = sumcheck::table_verify(&cert.table, &rt, cert.t_claim, b).ok_or(Reject::Table("round count"))?;

    // Keccak side.
    let kerr = |e: String| Reject::Hash(e);
    let mut rd = keccak::Reader::new(&cert.kec);
    let o_vals = rd.take(8).map_err(kerr)?;
    b.absorb_efs(&o_vals);
    let mclaim = masked_claim(&o_vals, &r0, &cert.ct);
    let (r1, mfinal) = gen_verify(&mut rd, nvk(n), 2, mclaim, b).map_err(kerr)?;
    let v1 = rd.take(1).map_err(kerr)?[0];
    if mfinal != mask_weight(&r1, &r0) * v1 {
        return Err(Reject::Hash("mask terminal check".into()));
    }
    b.absorb_ef(v1);
    let sp = keccak::specs();
    let (mut pt, mut v) = (r1, v1);
    for k in (0..sp.len()).rev() {
        let (pt2, vals) = keccak::main_verify(&sp[k], &pt, v, logp, b, &mut rd).map_err(kerr)?;
        (pt, v) = keccak::wiring_verify(&sp[k], &pt2, &vals, b, &mut rd).map_err(kerr)?;
    }
    let r2 = pt;
    let (r2s, r2q, r2i) = split_k(&r2);
    let mus: Vec<[u8; 64]> = records.par_iter().map(|rc| mlnat::mu_of(&mlnat::tr_of(&rc.pk), &rc.ctx, &rc.msg)).collect();
    let lclaim = v - link_public(&r2, &mus);
    let (rho_x, lfinal) = gen_verify(&mut rd, LOGW + log_n, 3, lclaim, b).map_err(kerr)?;
    let uvals = rd.take(8).map_err(kerr)?;
    b.absorb_efs(&uvals);
    let gam = b.sample_efs(8);
    let bclaim: EF = gam.iter().zip(&uvals).map(|(&g, &u)| g * u).sum();
    let (rho_w, bfinal) = gen_verify(&mut rd, LOG_BW, 2, bclaim, b).map_err(kerr)?;
    if rd.pos != cert.kec.len() {
        return Err(Reject::Parse("hash section length"));
    }
    tm.lap("V1 transcript replay (LogUp GKR, Keccak GKR, links)");

    // One WHIR verification.
    let tpt: Vec<EF> = r0[..LOGW].iter().chain(r0[LOGW + LOGQ..].iter()).copied().collect();
    let bw_pt: Vec<EF> = rho_w[..LOGW].iter().chain(rho_x[LOGW..].iter()).copied().collect();
    let proto = protocol9(tree.log_dc);
    let evals = b.verify_at(&comm, proof, &proto, &[p3_point(&r), p3_point(&tpt), p3_point(&rho_x), p3_point(&bw_pt), p3_point(&spt)]).map_err(Reject::Whir)?;
    if let Some(e) = b.transcript_error() {
        return Err(Reject::Transcript(e));
    }
    tm.lap("V2 WHIR verification (29 values)");
    let (mev, oev, iev, wev, tev) = (&evals[0], &evals[1], &evals[2], &evals[3], &evals[4]);

    // Table terminal.
    let jhat: EF = spt.iter().enumerate().map(|(t, &x)| x * F::from_u64(1u64 << t)).sum();
    if tfinal != -(theta - jhat.double() - EF::ONE) * tev[0] + -(theta - jhat.double()) * tev[1] {
        return Err(Reject::Table("terminal check"));
    }
    // Masked-output openings equal the transmitted values.
    if oev[..] != o_vals[..] {
        return Err(Reject::Hash("masked-output openings differ from the claimed values".into()));
    }
    // Input-link terminal: Weq(rho), the patterns at rho_s, T from WHIR, U from the transcript.
    let (rs, ri) = (&rho_x[..LOGW], &rho_x[LOGW..]);
    let mut lv: Vec<EF> = link_weights_at(&rho_x, r2s, r2i).to_vec();
    lv.extend_from_slice(iev);
    lv.extend_from_slice(&uvals);
    let e9: [EF; 9] = core::array::from_fn(|q| eq_q(r2q, q));
    if lfinal != link_f(&e9, &lv) {
        return Err(Reject::Hash("input-link terminal check".into()));
    }
    // Bit-wiring terminal: M(rho_w) times sum_j eq(rho_w_j, j) B_j(rho_w_c, rho_i).
    let mw = wiring_weights(&gam, rs);
    let mr: EF = eq_table(&rho_w).iter().zip(&mw).map(|(&a, &m)| a * m).sum();
    let bv: EF = (0..4).map(|j| crate::field::eq_at(&rho_w[LOGW..], j) * wev[j]).sum();
    let _ = ri;
    if bfinal != mr * bv {
        return Err(Reject::Hash("bit-wiring terminal check".into()));
    }
    tm.lap("V3 hash-side terminal checks");

    // Public ML-DSA data, claimed master sum, master chain and terminal.
    let ch = src.challenges(&ntt, n);
    let eq_rho = eq_table(&gout.point[..tree.log_dc]);
    let eq_r = eq_table(&r);
    let per = TRIALS * L * N;
    let sums: Vec<Sums9> = (0..n)
        .into_par_iter()
        .map(|i| {
            let p = derive_public9(&ntt, &records[i], &cts[i]);
            let mut s = vec![0i32; per];
            ch.s_centered(&ntt, &p.a_hat, i, &mut s);
            sums9(i, &s, &ch, &p.bc, &eq_rho, Some(&eq_r))
        })
        .collect();
    let agg = aggregate9(&sums, n);
    tm.lap("V4a public coefficients (ExpandA, mu, c from c_tilde, b, 14 projections, sums)");
    let mk = MasterK { g: gp + gq * theta, gq, gz, gb };
    let cx = Ctx9 { n, tree, theta, rho: gout.point.clone(), p_leaf: gout.p, q_leaf: gout.q, gp, gq, t_claim: cert.t_claim, mk, tau, omega, mu, quot, nu: cert.nu.clone() };
    let mut claim = claimed_sum9(&cx, &agg);
    for (h, &x) in cert.master.iter().zip(&mrs) {
        claim = gen_next(h, claim, x);
    }
    let pv = public_at_r9(&cx, &agg, &r);
    let mut vals = mev.clone();
    vals.extend_from_slice(&pv);
    if claim != master_f9(&mk, &vals) {
        return Err(Reject::Master("terminal check"));
    }
    tm.lap("V4b claimed sum, master chain, master terminal");
    Ok(())
}

// ---------------------------------------------------------------- lab chain statements

/// Lab chain manifest "QLYLB10C": the QLYAUTH4 field list with this magic, LE32(lab chain
/// profile id) and the digest field zero. The production chain verifier rejects the magic.
pub fn manifest_chain9(net: &[u8; 64], n: usize, parent: &crate::chain::Header, range: &[crate::chain::Header]) -> Vec<u8> {
    // The QLYAUTH4 field list, built directly (the QLYAUTH4 parameter digest is defined only for
    // its own sizes, and this field is zero here anyway).
    let first = range.first().expect("non-empty range");
    let last = range.last().unwrap();
    let mut m = Vec::with_capacity(MANIFEST);
    m.extend_from_slice(magics().1);
    m.extend_from_slice(&lab_chain_profile9(n).to_le_bytes());
    m.extend_from_slice(&[0u8; 64]);
    m.extend_from_slice(net);
    m.extend_from_slice(&first.height.to_le_bytes());
    m.extend_from_slice(&(range.len() as u32).to_le_bytes());
    m.extend_from_slice(&(n as u32).to_le_bytes());
    m.extend_from_slice(&parent.id);
    m.extend_from_slice(&last.id);
    m.extend_from_slice(&parent.acc);
    m.extend_from_slice(&last.acc);
    assert_eq!(m.len(), 348);
    m.resize(MANIFEST, 0);
    m
}

/// Lab chain instance: the QLYAUTH7 chain framing with c_tilde (0x0105) in place of U (0x0103).
pub fn instance_chain9(net: &[u8; 64], parent: &crate::chain::Header, range: &[crate::chain::Header], blocks: &[crate::chain::Block], records: &[Record], ct: &[u8], nu: &[u8]) -> Vec<u8> {
    let n = records.len();
    let man = manifest_chain9(net, n, parent, range);
    let mut x = Vec::new();
    x.extend_from_slice(b"Qlyphs/Archive/Instance/r10-chain-lab\0");
    x.extend_from_slice(&fs7::le32(lab_chain_profile9(n)));
    x.extend_from_slice(&fs7::frame(0x0100, &man));
    x.extend_from_slice(&fs7::frame(0x0101, &crate::chain::header104(parent)));
    x.extend_from_slice(&fs7::frame(0x0102, &crate::chain::block_section(range, blocks, records)));
    x.extend_from_slice(&fs7::frame(0x0105, ct));
    x.extend_from_slice(&fs7::frame(0x0104, nu));
    x
}

/// Lab chain verifier for hidden-u certificates: header linkage, replay with state-resolved
/// keys, every A[b] recomputed from the certificate's c_tilde, then the proof against the
/// derived manifest and raw instance. Only the lab chain profile is accepted here.
#[allow(clippy::too_many_arguments)]
pub fn verify_range9(net: &[u8; 64], parent: &crate::chain::Header, range: &[crate::chain::Header], blocks: &[crate::chain::Block], state: &crate::chain::State, bytes: &[u8], tm: &mut Timer, o: &Opts9) -> Result<(), Reject> {
    use crate::chain;
    if range.is_empty() || range.len() != blocks.len() {
        return Err(Reject::Chain("range shape".into()));
    }
    let mut prev = parent;
    for hd in range {
        if hd.parent != prev.id || hd.height != prev.height.wrapping_add(1) || hd.id != chain::header_id(&hd.parent, hd.height, &hd.acc) {
            return Err(Reject::Chain("header linkage".into()));
        }
        prev = hd;
    }
    let records = chain::replay(net, blocks, state)?;
    let n = records.len();
    if bytes.len() < 12 || &bytes[..8] != magics().1 {
        return Err(Reject::Profile("not a hidden-u lab chain certificate".into()));
    }
    let pid = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    let table = registered_table9(pid, n).filter(|t| t.profile == lab_chain_profile9(n)).ok_or_else(|| Reject::Profile(format!("unregistered profile {pid:#010x} for N = {n}")))?;
    let c = Cert9::from_bytes(n, bytes)?;
    let mut acc = parent.acc;
    let mut k = 0;
    for (hd, b) in range.iter().zip(blocks) {
        let entries: Vec<(&[u8], &[u8], [u8; 64])> = b.records.iter().enumerate().map(|(j, enc)| (enc.as_slice(), records[k + j].pk.as_slice(), c.ct[64 * (k + j)..64 * (k + j + 1)].try_into().unwrap())).collect();
        acc = chain::acc_next(net, hd.height, &acc, &chain::auth_root(net, hd.height, &entries));
        if acc != hd.acc {
            return Err(Reject::Chain(format!("accumulator mismatch at height {}", hd.height)));
        }
        k += b.records.len();
    }
    let x = instance_chain9(net, parent, range, blocks, &records, &c.ct, &c.nu);
    let man = manifest_chain9(net, n, parent, range);
    tm.lap("V-1 header linkage, replay, accumulators from c_tilde, raw instance");
    verify_stmt9(&records, &man, &x, table, bytes, tm, o).0
}

/// Reconstruct the canonical FIPS signature of signature i from the committed witness: z from X,
/// h from S, c_tilde public, and check that the committed bits hash to it.
pub fn reconstruct9(wit: &Wit9, rec: &Record, i: usize) -> Option<Vec<u8>> {
    let w = &wit.w;
    let base = i * SLOTS;
    let z: Vec<i64> = (0..L * N).map(|t| witness::as_int(w.x[base + t]) - XOFF).collect();
    let h: Vec<bool> = (0..K * N).map(|t| witness::as_int(w.s[base + t]) != 0).collect();
    let u: Vec<u8> = (0..K * N).map(|t| (0..4).map(|j| (wit.bits[j][base + t].as_canonical_u64() as u8) << j).sum()).collect();
    let mu = mlnat::mu_of(&mlnat::tr_of(&rec.pk), &rec.ctx, &rec.msg);
    if mlnat::c_tilde_of(&mu, &mlnat::w1_encode(&u)) != wit.ct[i] {
        return None;
    }
    mlnat::encode_sig(&wit.ct[i], &z, &h)
}

/// Hash-side self checks: the native sponge trace equals SHAKE256, the U-position map is a
/// bijection, the padding block, and the Keccak layer circuit on real trace rows.
pub fn selfcheck() -> Vec<(String, bool)> {
    let mut out = vec![];
    let mut mu = [0u8; 64];
    mlnat::shake256(&[b"r9h/selfcheck/mu"], &mut mu);
    let mut ub = vec![0u8; 1024];
    mlnat::shake256(&[b"r9h/selfcheck/u"], &mut ub);
    let tr = run_trace(&absorb_blocks(&mu, &ub));
    out.push(("nine-permutation trace output = SHAKE256(mu || U, 64)".into(), squeeze64(&tr[8]) == mlnat::c_tilde_of(&mu, &ub)));
    let mut seen = vec![false; 4 * SLOTS];
    let mut ok = true;
    let mut count = 0;
    for q in 0..8 {
        for s in 0..RATE_BITS {
            if let Src::U { plane, coef } = src_of(q, s) {
                count += 1;
                ok &= !seen[plane * SLOTS + coef];
                seen[plane * SLOTS + coef] = true;
                ok &= upos_of(plane, coef) == (q, s);
            }
        }
    }
    out.push((format!("U positions: {count} cells, bijective onto the 4 x 2048 bit cells, inverse map consistent"), ok && count == 4 * SLOTS && seen.iter().all(|&x| x)));
    // The bit planes reproduce w1Encode, low nibble first.
    let u = mlnat::w1_decode(&ub);
    let mut ok = true;
    for q in 0..8 {
        let bl = absorb_blocks(&mu, &ub)[q];
        for s in 0..RATE_BITS {
            let bit = (bl[s / 8] >> (s % 8)) & 1;
            match src_of(q, s) {
                Src::Mu(a, beta) => ok &= bit == (mu[a] >> beta) & 1,
                Src::U { plane, coef } => ok &= bit == (u[coef] >> plane) & 1,
                Src::None => ok = false,
            }
        }
    }
    out.push(("absorbed bits = mu bits and (u >> plane) & 1 at the mapped cells".into(), ok));
    let pb = pad_block(0x1f);
    out.push(("padding block 0x1f .. 0x80 (cells 0..4 and 1087)".into(), (0..RATE_BITS).filter(|&s| pad_bit(s) == 1).collect::<Vec<_>>() == vec![0, 1, 2, 3, 4, 1087] && pb[0] == 0x1f && pb[135] == 0x80));
    // The 72-layer circuit maps the trace inputs to the trace outputs.
    let mut rows = vec![F::ZERO; 16 * W];
    for q in 0..NPERM {
        let mut st = if q == 0 { [0u64; 25] } else { tr[q - 1] };
        xor_block(&mut st, &absorb_blocks(&mu, &ub)[q]);
        for s in 0..STATE {
            rows[q * W + s] = pm(state_bit(&st, s));
        }
    }
    let mut cur = rows;
    for s in keccak::specs() {
        cur = keccak::apply(&s, &cur, 16);
    }
    let mut ok = true;
    for q in 0..16 {
        for s in 0..W {
            let want = if q < NPERM && s < STATE { pm(state_bit(&tr[q], s)) } else { F::ZERO };
            ok &= cur[q * W + s] == want;
        }
    }
    out.push(("72-layer circuit on 16 slots: slots 0..8 = the nine states, padding cells and dummy slots 9..15 stay 0".into(), ok));
    // The XOR identity in +-1 encoding and the false MLE shortcut (two-point example).
    let s0 = [EF::ZERO, EF::ONE];
    let b0 = [EF::ONE, EF::ZERO];
    let r = EF::TWO;
    let mle = |v: &[EF; 2]| v[0] + r * (v[1] - v[0]);
    let x: [EF; 2] = core::array::from_fn(|k| s0[k] + b0[k] - (s0[k] * b0[k]).double());
    let lhs = mle(&x);
    let rhs = mle(&s0) + mle(&b0) - (mle(&s0) * mle(&b0)).double();
    out.push((format!("XOR MLE example s = (0,1), b = (1,0), r = 2: MLE(s xor b)(r) = {:?}, shortcut = {:?} (differ)", cert::ef_coords(&lhs)[0], cert::ef_coords(&rhs)[0]), lhs == EF::ONE && rhs == EF::from(F::from_u64(5))));
    out.push((format!("hidden-u lift bound at 512 signatures {} < p", lift_bound9(512)), lift_bound9(512) < crate::field::P as u128));
    out
}

pub fn ef_bytes(v: &[EF]) -> Vec<u8> {
    let mut b = Vec::new();
    v.iter().for_each(|x| crate::field::ef_to_bytes(x, &mut b));
    b
}

