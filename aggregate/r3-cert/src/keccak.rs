//! A GKR proof that P committed Keccak-f[1600] input states map to P committed output states,
//! over Goldilocks^5, with the r3-cert WHIR PCS and SHAKE256 transcript (round 4 section E,
//! step 4). No elliptic curves; no wrapper.
//!
//! Encoding: bit b is the field element 1 - 2b (so XOR is a product), one state per row of
//! W = 2048 cells: cell s = 64 (x + 5 y) + z for s < 1600, padding cells are 0. Cell index of
//! instance p is p * W + s; variables 0..11 are s, variables 11.. are p.
//!
//! Each round is three layers, each a map out[p][s] = sum_t sel_t(s) f_t(in[p][sigma_j(s)]):
//!  - theta-a: out = in on the state cells, and the 320 column products C[x][z] = prod_y A[x][y][z]
//!    on cells 1600..1920 (degree 5);
//!  - theta-b: A'[x][y][z] = A[x][y][z] C[x-1][z] C[x+1][z-1] (degree 3);
//!  - rho, pi, chi, iota: out = iota(s) B0 (1 - (1 + B1)(1 - B2)/2) with B0, B1, B2 the rho-pi
//!    images of A' at (X, Y), (X+1, Y), (X+2, Y) (degree 3).
//!
//! Layer reduction from a claim V_out(r) = v: one sumcheck over (p, s) of
//! eq(r_p, p) sum_t eq(r_s, s) sel_t(s) f_t(T(p, s)) with T_j(p, s) = in[p][sigma_j(s)]; the prover
//! sends every T_j at the final point; a random combination sum_j beta_j T_j(r') is reduced to
//! one claim on in by a degree-2 wiring sumcheck over s of in(r'_p, s') M(s'), with
//! M(s') = sum_j beta_j sum_{s : sigma_j(s) = s'} eq(r'_s, s), which the verifier computes.
//! The input is checked canonical by a zerocheck sum eq(tau, b) (in(b)^2 - [s < 1600]) = 0.
//! Openings: in at the last GKR point, in at the zerocheck point, out at the first point.

use std::time::Instant;

use p3_commit::MultilinearPcs;
use p3_field::{Algebra, BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;
use p3_multilinear_util::point::Point;
use p3_sumcheck::layout::{Layout as _, Table, observe_commitment};
use p3_sumcheck::{OpeningBatch, OpeningProtocol, PrescribedPointPcs, TableShape, TableSpec};
use p3_symmetric::MerkleCap;
use rayon::prelude::*;

use crate::cert::Timer;
use crate::field::{EF, F, ef_from_bytes, ef_to_bytes, eq_table, lagrange};
use crate::pcs::{self, Commitment, Layout, PcsProof, Tr, words_to_bytes};

pub const LOGW: usize = 11;
pub const W: usize = 1 << LOGW;
pub const STATE: usize = 1600;

const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];
/// rho offsets r[x][y].
const ROT: [[u32; 5]; 5] = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]];

#[inline]
fn idx(x: usize, y: usize, z: usize) -> usize {
    64 * (x + 5 * y) + z
}

#[derive(Clone, Debug)]
pub enum Kind {
    Lin(usize),
    Sq(usize),
    Prod(Vec<usize>),
    Chi([usize; 3]),
}

impl Kind {
    fn uses(&self) -> Vec<usize> {
        match self {
            Kind::Lin(j) | Kind::Sq(j) => vec![*j],
            Kind::Prod(js) => js.clone(),
            Kind::Chi(js) => js.to_vec(),
        }
    }
    fn degree(&self) -> usize {
        match self {
            Kind::Lin(_) => 1,
            Kind::Sq(_) => 2,
            Kind::Prod(js) => js.len(),
            Kind::Chi(_) => 3,
        }
    }
}

#[inline(always)]
fn eval_f<T: Algebra<F> + Copy>(k: &Kind, v: &[T]) -> T {
    match k {
        Kind::Lin(j) => v[*j],
        Kind::Sq(j) => v[*j] * v[*j],
        Kind::Prod(js) => js[1..].iter().fold(v[js[0]], |a, &j| a * v[j]),
        Kind::Chi([a, b, c]) => {
            let t = (T::ONE + v[*b]) * (T::ONE - v[*c]);
            v[*a] * (T::ONE - t * half())
        }
    }
}

#[inline(always)]
fn half() -> F {
    F::from_u64(0x7fff_ffff_8000_0001) // (p + 1) / 2
}

pub struct Term {
    pub sel: Vec<i8>,
    pub kind: Kind,
    /// Cells with sel != 0.
    pub active: Vec<u32>,
}

/// A layer. Gather j belongs to exactly one term (owner[j]) and is defined as
/// T_j(p, s) = in[p][sigma_j(s)] on that term's active cells and 0 elsewhere, so the prover stores
/// and folds it compactly; the wiring sum runs over the same active cells.
pub struct Spec {
    pub name: String,
    pub gathers: Vec<Vec<u16>>,
    pub terms: Vec<Term>,
    pub owner: Vec<usize>,
}

impl Spec {
    /// Degree of the layer polynomial in the committed values.
    pub fn deg_f(&self) -> usize {
        self.terms.iter().map(|t| t.kind.degree()).max().unwrap()
    }
    /// Degree of an s-round polynomial (the weight is linear in the round variable).
    pub fn d(&self) -> usize {
        self.deg_f() + 1
    }
    /// Frontend elements of one main sumcheck: p rounds (deg_f each, eq split off), s rounds
    /// (deg_f + 1 each), then the gathered values.
    pub fn main_elems(&self, logp: usize) -> usize {
        logp * self.deg_f() + LOGW * self.d() + self.gathers.len()
    }
    fn new(name: String, gathers: Vec<Vec<u16>>, terms: Vec<(Vec<i8>, Kind)>) -> Self {
        let terms = terms
            .into_iter()
            .map(|(sel, kind)| {
                let active = (0..W as u32).filter(|&s| sel[s as usize] != 0).collect();
                Term { sel, kind, active }
            })
            .collect::<Vec<Term>>();
        let mut owner = vec![usize::MAX; gathers.len()];
        for (ti, t) in terms.iter().enumerate() {
            for j in t.kind.uses() {
                assert_eq!(owner[j], usize::MAX, "a gather belongs to one term");
                owner[j] = ti;
            }
        }
        assert!(owner.iter().all(|&o| o != usize::MAX));
        Spec { name, gathers, terms, owner }
    }
}

fn identity() -> Vec<u16> {
    (0..W as u16).collect()
}

fn theta_a(round: usize) -> Spec {
    let mut g = vec![identity()];
    for y in 0..5 {
        let mut s = identity();
        for c in 0..320 {
            s[STATE + c] = idx(c / 64, y, c % 64) as u16;
        }
        g.push(s);
    }
    let sel_a: Vec<i8> = (0..W).map(|s| (s < STATE) as i8).collect();
    let sel_c: Vec<i8> = (0..W).map(|s| (STATE..STATE + 320).contains(&s) as i8).collect();
    Spec::new(format!("round {round} theta-a"), g, vec![(sel_a, Kind::Lin(0)), (sel_c, Kind::Prod(vec![1, 2, 3, 4, 5]))])
}

fn theta_b(round: usize) -> Spec {
    let (mut g1, mut g2) = (identity(), identity());
    for x in 0..5 {
        for y in 0..5 {
            for z in 0..64 {
                g1[idx(x, y, z)] = (STATE + 64 * ((x + 4) % 5) + z) as u16;
                g2[idx(x, y, z)] = (STATE + 64 * ((x + 1) % 5) + (z + 63) % 64) as u16;
            }
        }
    }
    let sel: Vec<i8> = (0..W).map(|s| (s < STATE) as i8).collect();
    Spec::new(format!("round {round} theta-b"), vec![identity(), g1, g2], vec![(sel, Kind::Prod(vec![0, 1, 2]))])
}

fn chi(round: usize) -> Spec {
    // B[X][Y] bit z = A'[x][y] bit (z - r[x][y]) with X = y, Y = 2x + 3y.
    let mut src = [[(0usize, 0usize); 5]; 5];
    for x in 0..5 {
        for y in 0..5 {
            src[y][(2 * x + 3 * y) % 5] = (x, y);
        }
    }
    let b = |xx: usize, yy: usize, z: usize| -> u16 {
        let (x, y) = src[xx][yy];
        idx(x, y, (z + 64 - ROT[x][y] as usize) % 64) as u16
    };
    let mut g = vec![identity(), identity(), identity()];
    for xx in 0..5 {
        for yy in 0..5 {
            for z in 0..64 {
                for (k, gk) in g.iter_mut().enumerate() {
                    gk[idx(xx, yy, z)] = b((xx + k) % 5, yy, z);
                }
            }
        }
    }
    let sel: Vec<i8> = (0..W).map(|s| if s >= STATE { 0 } else if s < 64 && (RC[round] >> s) & 1 == 1 { -1 } else { 1 }).collect();
    Spec::new(format!("round {round} rho-pi-chi-iota"), g, vec![(sel, Kind::Chi([0, 1, 2]))])
}

/// The 72 layers in forward order.
pub fn specs() -> Vec<Spec> {
    (0..24).flat_map(|r| [theta_a(r), theta_b(r), chi(r)]).collect()
}

fn bool_spec() -> Spec {
    Spec::new("booleanity".into(), vec![identity()], vec![(vec![1; W], Kind::Sq(0))])
}

/// out[p][s] = sum_t sel_t(s) f_t(in[p][sigma(s)]).
pub fn apply(spec: &Spec, inp: &[F], rows: usize) -> Vec<F> {
    let mut out = vec![F::ZERO; rows * W];
    out.par_chunks_mut(W).enumerate().for_each(|(p, o)| {
        let row = &inp[p * W..(p + 1) * W];
        let mut v = [F::ZERO; 8];
        for t in &spec.terms {
            let uses = t.kind.uses();
            for &s in &t.active {
                let s = s as usize;
                for &j in &uses {
                    v[j] = row[spec.gathers[j][s] as usize];
                }
                let f = eval_f(&t.kind, &v);
                o[s] += if t.sel[s] == 1 { f } else { -f };
            }
        }
    });
    out
}

/// Encode states (25 lanes) as rows.
pub fn encode(states: &[[u64; 25]]) -> Vec<F> {
    let mut v = vec![F::ZERO; states.len() * W];
    v.par_chunks_mut(W).zip(states.par_iter()).for_each(|(row, st)| {
        for s in 0..STATE {
            row[s] = if (st[s / 64] >> (s % 64)) & 1 == 1 { -F::ONE } else { F::ONE };
        }
    });
    v
}

/// Decode a row; None if a state cell is not +-1 or a padding cell is not 0.
pub fn decode(row: &[F]) -> Option<[u64; 25]> {
    let mut st = [0u64; 25];
    for s in 0..W {
        let v = row[s];
        if s < STATE {
            if v == -F::ONE {
                st[s / 64] |= 1 << (s % 64);
            } else if v != F::ONE {
                return None;
            }
        } else if v != F::ZERO {
            return None;
        }
    }
    Some(st)
}

// ---------------------------------------------------------------- sumchecks

const MAXJ: usize = 8;

/// Prover time split inside the main sumchecks (microseconds): round 1, EF rounds of phase A,
/// phase A folds, phase B.
/// Slot 4: the first fold alone (also included in slot 2).
pub static PROF: [std::sync::atomic::AtomicU64; 5] = [const { std::sync::atomic::AtomicU64::new(0) }; 5];
fn prof(i: usize, t: Instant) {
    PROF[i].fetch_add(t.elapsed().as_micros() as u64, std::sync::atomic::Ordering::Relaxed);
}

/// Prover-only switch (round 5 §A.2, §E): build the first round of every main sumcheck from
/// weighted value-pattern histograms and do the first fold by table selection. The round
/// messages, the transcript and the proof bytes are the same either way; the verifier is untouched.
pub static HIST: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

fn hist_on() -> bool {
    HIST.load(std::sync::atomic::Ordering::Relaxed)
}

#[path = "kec10.rs"]
pub mod kec10;

/// Operation counters, per thread, merged on demand. Counts are added once per row or per
/// buffer from the loop sizes (never per operation), so counting does not perturb the timing.
pub mod ops {
    use std::cell::Cell;
    pub const CATS: [&str; 6] = ["round 1 (base field)", "first fold", "phase-A rounds 2..", "phase-A folds 2.. and eq halving", "phase B (s rounds and folds)", "wiring sumchecks"];
    pub const KINDS: [&str; 5] = ["general EF*EF mul", "mixed EF*F mul", "EF add/sub", "table selection", "base F*F mul"];
    pub const R1: usize = 0;
    pub const F1: usize = 1;
    pub const RA: usize = 2;
    pub const FA: usize = 3;
    pub const PB: usize = 4;
    pub const WI: usize = 5;
    pub const GEN: usize = 0;
    pub const MIX: usize = 1;
    pub const ADD: usize = 2;
    pub const SEL: usize = 3;
    pub const BASE: usize = 4;
    pub type Counts = [[u64; 5]; 6];
    thread_local! {
        static C: Cell<Counts> = const { Cell::new([[0; 5]; 6]) };
    }
    #[inline]
    pub fn add(cat: usize, kind: usize, n: u64) {
        C.with(|c| {
            let mut v = c.get();
            v[cat][kind] += n;
            c.set(v);
        });
    }
    /// Sum and reset the counters of every rayon worker and of the calling thread.
    pub fn take() -> Counts {
        let mut s = C.with(|c| c.replace([[0; 5]; 6]));
        for part in rayon::broadcast(|_| C.with(|c| c.replace([[0; 5]; 6]))) {
            for (a, b) in s.iter_mut().zip(part.iter()) {
                for (x, y) in a.iter_mut().zip(b.iter()) {
                    *x += y;
                }
            }
        }
        s
    }
}

/// Field multiplications in one evaluation of a term polynomial: (by the T type, by an F constant).
fn f_mults(k: &Kind) -> (u64, u64) {
    match k {
        Kind::Lin(_) => (0, 0),
        Kind::Sq(_) => (1, 0),
        Kind::Prod(js) => (js.len() as u64 - 1, 0),
        Kind::Chi(_) => (2, 1),
    }
}

/// Canonical small-value code of a base-field cell: 0 for 1, 1 for -1, 2 for 0, 3 otherwise.
#[inline(always)]
fn code(v: F) -> usize {
    match v.as_canonical_u64() {
        1 => 0,
        0xffff_ffff_0000_0000 => 1,
        0 => 2,
        _ => 3,
    }
}

const CODE_VAL: [i64; 3] = [1, -1, 0];

/// Per-term pattern tables for the first round: the term polynomial at t = 0..=deg_f of every
/// value pattern, computed with the same `eval_f` as the direct path.
enum HTab {
    Lin,
    /// Products of +-1 values: key = sign * (d + 1) + flips, value sign * (1 - 2t)^flips.
    Prod { d: usize, tab: Vec<[F; MAXJ]> },
    /// Any other term: key = sum over its uses u of (radix lo + hi) radix^(2u) with lo, hi codes
    /// < radix (radix 2: values +-1 only, 64 keys for chi; radix 3 adds 0, 9 keys for the square).
    Pat { radix: usize, tab: Vec<[F; MAXJ]> },
}

fn hist_tables(spec: &Spec) -> Vec<HTab> {
    let df = spec.deg_f();
    let line = |lo: i64, hi: i64, t: usize| crate::field::fi(lo) + F::from_usize(t) * crate::field::fi(hi - lo);
    spec.terms
        .iter()
        .map(|t| match &t.kind {
            Kind::Lin(_) => HTab::Lin,
            Kind::Prod(js) => {
                let d = js.len();
                let tab = (0..2 * (d + 1))
                    .map(|key| {
                        let (sign, flips) = (key / (d + 1), key % (d + 1));
                        // A representative: the first `flips` uses flip from (-1)^sign... built
                        // from explicit endpoints so that eval_f defines the value.
                        let mut out = [F::ZERO; MAXJ];
                        for (k, o) in out.iter_mut().enumerate().take(df + 1) {
                            let mut v = [F::ZERO; MAXJ];
                            for (u, &j) in js.iter().enumerate() {
                                let lo = if u == 0 && sign == 1 { -1 } else { 1 };
                                let hi = if u < flips { -lo } else { lo };
                                v[j] = line(lo, hi, k);
                            }
                            *o = eval_f(&t.kind, &v);
                        }
                        out
                    })
                    .collect();
                HTab::Prod { d, tab }
            }
            k => {
                let uses = k.uses();
                let radix = if matches!(k, Kind::Sq(_)) { 3 } else { 2 };
                let r2: usize = radix * radix;
                let tab = (0..r2.pow(uses.len() as u32))
                    .map(|key| {
                        let mut out = [F::ZERO; MAXJ];
                        for (kk, o) in out.iter_mut().enumerate().take(df + 1) {
                            let mut v = [F::ZERO; MAXJ];
                            let mut rest = key;
                            for &j in &uses {
                                let (lo, hi) = (CODE_VAL[rest % r2 / radix], CODE_VAL[rest % radix]);
                                v[j] = line(lo, hi, kk);
                                rest /= r2;
                            }
                            *o = eval_f(k, &v);
                        }
                        out
                    })
                    .collect();
                HTab::Pat { radix, tab }
            }
        })
        .collect()
}

/// First round (base-field gathers) by histograms: per row pair p, the s-weights are summed into
/// one bucket per value pattern (additions only), then each bucket is scaled by the small
/// polynomial values of its pattern. Cells whose values are not +-1 (or 0 where the pattern
/// table allows it) take the direct path, so the result equals `round_a::<F>` for every input.
fn round_a_hist(spec: &Spec, g: &[Vec<F>], ep: &[EF], w: &[Vec<EF>], rows: usize, with1: bool, tabs: &[HTab]) -> [EF; MAXJ] {
    let df = spec.deg_f();
    let hr = rows / 2;
    let npts = df as u64 + with1 as u64;
    (0..hr)
        .into_par_iter()
        .map(|p| {
            let mut acc = [EF::ZERO; MAXJ];
            let (mut n_add, mut n_mix, mut n_base) = (0u64, 0u64, 0u64);
            for (ti, t) in spec.terms.iter().enumerate() {
                let m = t.active.len();
                let (lo_off, hi_off) = (p * m, (p + hr) * m);
                let ws = &w[ti];
                // Direct evaluation of one cell, exactly as round_a does it.
                let direct = |a: usize, acc: &mut [EF; MAXJ]| {
                    let mut vals = [[F::ZERO; MAXJ]; MAXJ];
                    for j in t.kind.uses() {
                        let (lo, hi) = (g[j][lo_off + a], g[j][hi_off + a]);
                        let dl = hi - lo;
                        vals[0][j] = lo;
                        vals[1][j] = hi;
                        let mut v = hi;
                        for row in vals.iter_mut().take(df + 1).skip(2) {
                            v += dl;
                            row[j] = v;
                        }
                    }
                    acc[0] += ws[a] * eval_f(&t.kind, &vals[0]);
                    if with1 {
                        acc[1] += ws[a] * eval_f(&t.kind, &vals[1]);
                    }
                    for k in 2..=df {
                        acc[k] += ws[a] * eval_f(&t.kind, &vals[k]);
                    }
                };
                match (&t.kind, &tabs[ti]) {
                    (Kind::Lin(j), HTab::Lin) => {
                        let col = &g[*j];
                        let (mut sl, mut sh) = (EF::ZERO, EF::ZERO);
                        for a in 0..m {
                            for (s, v) in [(&mut sl, col[lo_off + a]), (&mut sh, col[hi_off + a])] {
                                match code(v) {
                                    0 => *s += ws[a],
                                    1 => *s -= ws[a],
                                    2 => {}
                                    _ => {
                                        *s += ws[a] * v;
                                        n_mix += 1;
                                    }
                                }
                            }
                        }
                        n_add += 2 * m as u64 + 1 + 2 * (df as u64 + 1);
                        let d = sh - sl;
                        let mut v = sl;
                        for a in acc.iter_mut().take(df + 1) {
                            *a += v;
                            v += d;
                        }
                    }
                    (Kind::Prod(js), HTab::Prod { d, tab }) => {
                        let mut bucket = [EF::ZERO; 12];
                        for a in 0..m {
                            let (mut sign, mut flips, mut ok) = (0usize, 0usize, true);
                            for &j in js {
                                match (code(g[j][lo_off + a]), code(g[j][hi_off + a])) {
                                    (0, 0) => {}
                                    (1, 1) => sign ^= 1,
                                    (0, 1) => flips += 1,
                                    (1, 0) => {
                                        sign ^= 1;
                                        flips += 1;
                                    }
                                    _ => ok = false,
                                }
                            }
                            if ok {
                                bucket[sign * (d + 1) + flips] += ws[a];
                                n_add += 1;
                            } else {
                                direct(a, &mut acc);
                                n_mix += npts;
                                n_add += npts;
                                n_base += npts * (d - 1) as u64;
                            }
                        }
                        for (key, h) in bucket.iter().enumerate().take(2 * (d + 1)) {
                            collapse(&mut acc, *h, &tab[key], df, with1, &mut n_mix, &mut n_add);
                        }
                    }
                    (kind, HTab::Pat { radix, tab }) => {
                        let uses = kind.uses();
                        let mut bucket = [EF::ZERO; 64];
                        for a in 0..m {
                            let (mut key, mut mul, mut ok) = (0usize, 1usize, true);
                            for &j in &uses {
                                let (cl, ch) = (code(g[j][lo_off + a]), code(g[j][hi_off + a]));
                                if cl >= *radix || ch >= *radix {
                                    ok = false;
                                    break;
                                }
                                key += (radix * cl + ch) * mul;
                                mul *= radix * radix;
                            }
                            if ok {
                                bucket[key] += ws[a];
                                n_add += 1;
                            } else {
                                direct(a, &mut acc);
                                n_mix += npts;
                                n_add += npts;
                                n_base += npts * f_mults(kind).0;
                            }
                        }
                        for (key, h) in bucket.iter().enumerate().take(tab.len()) {
                            collapse(&mut acc, *h, &tab[key], df, with1, &mut n_mix, &mut n_add);
                        }
                    }
                    _ => unreachable!("table kind matches term kind"),
                }
            }
            ops::add(ops::R1, ops::ADD, n_add);
            ops::add(ops::R1, ops::MIX, n_mix);
            ops::add(ops::R1, ops::BASE, n_base);
            ops::add(ops::R1, ops::GEN, MAXJ as u64);
            let e = ep[p];
            core::array::from_fn(|k| e * acc[k])
        })
        .reduce(|| [EF::ZERO; MAXJ], |a, b| core::array::from_fn(|k| a[k] + b[k]))
}

/// acc[t] += h * f(t) at the points the direct path fills (t = 1 only when `with1`).
#[inline(always)]
fn collapse(acc: &mut [EF; MAXJ], h: EF, f: &[F; MAXJ], df: usize, with1: bool, n_mix: &mut u64, n_add: &mut u64) {
    if h == EF::ZERO {
        return;
    }
    for k in 0..=df {
        if k == 1 && !with1 {
            continue;
        }
        acc[k] += h * f[k];
        *n_mix += 1;
        *n_add += 1;
    }
}

/// First fold of a base-field buffer, r (hi - lo) + lo, by selection among the nine values
/// for lo, hi in {1, -1, 0}; other cells are computed directly.
fn fold_first(src: &[F], n: usize, r: EF, buf: &mut Vec<EF>, select: bool) {
    buf.clear();
    if !select {
        buf.par_extend((0..n).into_par_iter().with_min_len(1 << 12).map(|i| r * (src[i + n] - src[i]) + src[i]));
        ops::add(ops::F1, ops::MIX, n as u64);
        ops::add(ops::F1, ops::ADD, n as u64);
        return;
    }
    let tab: [EF; 9] = core::array::from_fn(|c| {
        let (lo, hi) = (crate::field::fi(CODE_VAL[c / 3]), crate::field::fi(CODE_VAL[c % 3]));
        r * (hi - lo) + lo
    });
    buf.par_extend((0..n).into_par_iter().with_min_len(1 << 12).map(|i| {
        let (lo, hi) = (src[i], src[i + n]);
        let (cl, ch) = (code(lo), code(hi));
        if cl < 3 && ch < 3 {
            tab[3 * cl + ch]
        } else {
            ops::add(ops::F1, ops::MIX, 1);
            ops::add(ops::F1, ops::ADD, 1);
            r * (hi - lo) + lo
        }
    }));
    ops::add(ops::F1, ops::SEL, n as u64);
}

/// Phase-A round (gathers and weights compact: index p * |active| + a). With the eq factor of the round variable split off (Gruen, normalized),
/// q(t) = sum_{p < rows/2} E'(p) sum_s sum_terms w_t(s) f_t(T(t, p, s)), returned at t = 0, 2, ...,
/// deg_f, and also at t = 1 when `with1` (otherwise slot 1 is meaningless).
fn round_a<T>(spec: &Spec, g: &[Vec<T>], ep: &[EF], w: &[Vec<EF>], rows: usize, with1: bool) -> [EF; MAXJ]
where
    T: Algebra<F> + Copy + Send + Sync,
    EF: Algebra<T>,
{
    let df = spec.deg_f();
    let hr = rows / 2;
    let base = std::mem::size_of::<T>() == std::mem::size_of::<F>();
    let cat = if base { ops::R1 } else { ops::RA };
    let npts = df as u64 + with1 as u64;
    // Operations per row pair, from the loop sizes.
    let (mut n_t, mut n_ws, mut n_f, mut n_add) = (0u64, 0u64, 0u64, MAXJ as u64);
    for t in &spec.terms {
        let m = t.active.len() as u64;
        let (fm, fc) = f_mults(&t.kind);
        if let Kind::Lin(_) = t.kind {
            n_ws += 2 * m;
            n_add += 2 * m + 1 + 2 * (df as u64 + 1);
        } else {
            let u = t.kind.uses().len() as u64;
            n_t += m * npts * fm;
            n_f += m * npts * fc;
            n_ws += m * npts;
            n_add += m * npts + if base { 0 } else { m * u * df as u64 };
        }
    }
    let count = move || {
        if base {
            ops::add(cat, ops::BASE, n_t + n_f);
            ops::add(cat, ops::MIX, n_ws);
        } else {
            ops::add(cat, ops::GEN, n_t + n_ws);
            ops::add(cat, ops::MIX, n_f);
        }
        ops::add(cat, ops::ADD, n_add);
        ops::add(cat, ops::GEN, MAXJ as u64);
    };
    (0..hr)
        .into_par_iter()
        .map(|p| {
            count();
            let mut acc = [EF::ZERO; MAXJ];
            let mut vals = [[T::ZERO; MAXJ]; MAXJ];
            for (ti, t) in spec.terms.iter().enumerate() {
                let m = t.active.len();
                let (lo_off, hi_off) = (p * m, (p + hr) * m);
                if let Kind::Lin(j) = t.kind {
                    // Linear term: two weighted sums, then the line through them.
                    let (mut sl, mut sh) = (EF::ZERO, EF::ZERO);
                    for a in 0..m {
                        let ws = w[ti][a];
                        sl += ws * g[j][lo_off + a];
                        sh += ws * g[j][hi_off + a];
                    }
                    let d = sh - sl;
                    let mut v = sl;
                    for a in acc.iter_mut().take(df + 1) {
                        *a += v;
                        v += d;
                    }
                    continue;
                }
                let uses = t.kind.uses();
                for a in 0..m {
                    for &j in &uses {
                        let lo = g[j][lo_off + a];
                        let hi = g[j][hi_off + a];
                        let dl = hi - lo;
                        vals[0][j] = lo;
                        vals[1][j] = hi;
                        let mut v = hi;
                        for row in vals.iter_mut().take(df + 1).skip(2) {
                            v += dl;
                            row[j] = v;
                        }
                    }
                    let ws = w[ti][a];
                    acc[0] += ws * eval_f(&t.kind, &vals[0]);
                    if with1 {
                        acc[1] += ws * eval_f(&t.kind, &vals[1]);
                    }
                    for k in 2..=df {
                        acc[k] += ws * eval_f(&t.kind, &vals[k]);
                    }
                }
            }
            let e = ep[p];
            core::array::from_fn(|k| e * acc[k])
        })
        .reduce(|| [EF::ZERO; MAXJ], |a, b| core::array::from_fn(|k| a[k] + b[k]))
}

/// One round binding the top s variable (p fully bound): h at the points 0, 2, ..., deg_f + 1.
fn round_b(spec: &Spec, g: &[Vec<EF>], w: &[Vec<EF>], cols: usize) -> Vec<EF> {
    let d = spec.d();
    let hc = cols / 2;
    let mut acc = [EF::ZERO; MAXJ];
    let mut vals = [[EF::ZERO; MAXJ]; MAXJ];
    for i in 0..hc {
        for (ti, t) in spec.terms.iter().enumerate() {
            let uses = t.kind.uses();
            for &j in &uses {
                let (lo, hi) = (g[j][i], g[j][i + hc]);
                let dl = hi - lo;
                vals[0][j] = lo;
                let mut v = hi + dl;
                vals[1][j] = v;
                for row in vals.iter_mut().take(d).skip(2) {
                    v += dl;
                    row[j] = v;
                }
            }
            let (wl, wh) = (w[ti][i], w[ti][i + hc]);
            let dw = wh - wl;
            acc[0] += wl * eval_f(&t.kind, &vals[0]);
            let mut wk = wh + dw;
            for k in 1..d {
                acc[k] += wk * eval_f(&t.kind, &vals[k]);
                wk += dw;
            }
        }
    }
    acc[..d].to_vec()
}

fn fold_half(v: &mut Vec<EF>, r: EF) {
    let h = v.len() / 2;
    let (lo, hi) = v.split_at_mut(h);
    lo.par_iter_mut().zip(hi.par_iter()).with_min_len(1 << 12).for_each(|(a, &b)| *a += r * (b - *a));
    v.truncate(h);
}

/// Marginalize the top variable of an eq table: E(p) <- E(p) + E(p + h).
fn halve_eq(v: &mut Vec<EF>) {
    let h = v.len() / 2;
    let (lo, hi) = v.split_at_mut(h);
    lo.par_iter_mut().zip(hi.par_iter()).with_min_len(1 << 12).for_each(|(a, &b)| *a += b);
    v.truncate(h);
}

fn interp(h: &[EF], claim: EF, r: EF) -> EF {
    let mut nodes = Vec::with_capacity(h.len() + 1);
    nodes.push(h[0]);
    nodes.push(claim - h[0]);
    nodes.extend_from_slice(&h[1..]);
    lagrange(&nodes, r)
}

/// Monomial coefficients of the polynomial through (t, v[t]), t = 0, ..., len - 1.
fn to_coeffs(v: &[EF]) -> Vec<EF> {
    let n = v.len();
    let mut out = vec![EF::ZERO; n];
    for i in 0..n {
        let mut poly = vec![F::ONE];
        let mut den = F::ONE;
        for j in 0..n {
            if j == i {
                continue;
            }
            let mut np = vec![F::ZERO; poly.len() + 1];
            for (k, &c) in poly.iter().enumerate() {
                np[k + 1] += c;
                np[k] -= c * F::from_usize(j);
            }
            poly = np;
            den *= crate::field::fi(i as i64 - j as i64);
        }
        let inv = den.inverse();
        for k in 0..n {
            out[k] += v[i] * (poly[k] * inv);
        }
    }
    out
}

/// Division-free phase-A recurrence: message [a1..a_D] of q, a0 = c - x (a1 + ... + a_D), next
/// claim q(r) (normalized: the factor eq1(x, r) is not multiplied in).
fn next_a(claim: EF, x: EF, msg: &[EF], r: EF) -> EF {
    let a0 = claim - x * msg.iter().copied().sum::<EF>();
    msg.iter().rev().fold(EF::ZERO, |acc, &a| (acc + a) * r) + a0
}

/// Main layer sumcheck. `rp` is the p part of the claim point. Gathers are in gpool[..ng]
/// (base field); epool holds the folded extension-field copies (reused across layers).
/// Returns the final point (variable-indexed, LSB first) and the T_j values.
#[allow(clippy::too_many_arguments)]
pub(crate) fn main_prove<T: crate::pcs::Fs>(spec: &Spec, gpool: &[Vec<F>], epool: &mut [Vec<EF>], rp: &[EF], mut w: Vec<Vec<EF>>, mut claim: EF, logp: usize, tr: &mut T, msgs: &mut Vec<EF>) -> (Vec<EF>, Vec<EF>) {
    let nv = logp + LOGW;
    let ng = spec.gathers.len();
    let df = spec.deg_f();
    let mut pt = vec![EF::ZERO; nv];
    let mut rows = 1usize << logp;
    let mut ep = eq_table(&rp[..logp - 1]);
    let wc: Vec<Vec<EF>> = spec.terms.iter().enumerate().map(|(ti, t)| t.active.iter().map(|&s| w[ti][s as usize]).collect()).collect();
    let msz: Vec<usize> = (0..ng).map(|j| spec.terms[spec.owner[j]].active.len()).collect();
    let mut first = true;
    let hist = hist_on();
    let tabs = if hist { hist_tables(spec) } else { vec![] };
    while rows > 1 {
        let var = LOGW + rows.trailing_zeros() as usize - 1;
        let x = rp[var - LOGW];
        let t0 = Instant::now();
        let mut q = if first && hist {
            round_a_hist(spec, &gpool[..ng], &ep, &wc, rows, x == EF::ZERO, &tabs)
        } else if first {
            round_a::<F>(spec, &gpool[..ng], &ep, &wc, rows, x == EF::ZERO)
        } else {
            round_a::<EF>(spec, &epool[..ng], &ep, &wc, rows, x == EF::ZERO)
        };
        prof(if first { 0 } else { 1 }, t0);
        if x != EF::ZERO {
            q[1] = (claim - (EF::ONE - x) * q[0]) * x.inverse();
        }
        let co = to_coeffs(&q[..=df]);
        debug_assert_eq!(co[0], claim - x * co[1..].iter().copied().sum::<EF>());
        let msg = &co[1..];
        tr.absorb_efs(msg);
        msgs.extend_from_slice(msg);
        let r = kec10::inject_r(tr.sample_ef(), x);
        claim = next_a(claim, x, msg, r);
        pt[var] = r;
        let t0 = Instant::now();
        if first {
            for (j, buf) in epool.iter_mut().enumerate().take(ng) {
                fold_first(&gpool[j], rows / 2 * msz[j], r, buf, hist);
            }
            prof(4, t0);
            first = false;
        } else {
            epool[..ng].iter_mut().for_each(|c| {
                ops::add(ops::FA, ops::GEN, c.len() as u64 / 2);
                ops::add(ops::FA, ops::ADD, c.len() as u64);
                fold_half(c, r)
            });
        }
        if ep.len() > 1 {
            ops::add(ops::FA, ops::ADD, ep.len() as u64 / 2);
            halve_eq(&mut ep);
        }
        prof(2, t0);
        rows /= 2;
    }
    let t0 = Instant::now();
    // Phase B on full-width rows (zero outside each gather's active cells).
    let mut g: Vec<Vec<EF>> = (0..ng)
        .map(|j| {
            let mut full = vec![EF::ZERO; W];
            for (a, &s) in spec.terms[spec.owner[j]].active.iter().enumerate() {
                full[s as usize] = epool[j][a];
            }
            full
        })
        .collect();
    let mut cols = W;
    while cols > 1 {
        let d = spec.d() as u64;
        for t in &spec.terms {
            let (fm, fc) = f_mults(&t.kind);
            let u = t.kind.uses().len() as u64;
            let hc = cols as u64 / 2;
            ops::add(ops::PB, ops::GEN, hc * d * (fm + 1));
            ops::add(ops::PB, ops::MIX, hc * d * fc);
            ops::add(ops::PB, ops::ADD, hc * (u * d + 2 * d));
        }
        ops::add(ops::PB, ops::GEN, (ng + w.len()) as u64 * cols as u64 / 2);
        ops::add(ops::PB, ops::ADD, (ng + w.len()) as u64 * cols as u64);
        let h = round_b(spec, &g, &w, cols);
        tr.absorb_efs(&h);
        msgs.extend_from_slice(&h);
        let r = tr.sample_ef();
        claim = interp(&h, claim, r);
        pt[cols.trailing_zeros() as usize - 1] = r;
        g.iter_mut().for_each(|c| fold_half(c, r));
        w.iter_mut().for_each(|c| fold_half(c, r));
        cols /= 2;
    }
    prof(3, t0);
    let vals: Vec<EF> = g.iter().map(|c| c[0]).collect();
    debug_assert_eq!(claim, spec.terms.iter().enumerate().map(|(ti, t)| w[ti][0] * eval_f(&t.kind, &vals)).sum::<EF>());
    tr.absorb_efs(&vals);
    msgs.extend_from_slice(&vals);
    (pt, vals)
}

/// Low-memory variant of `main_prove` with the same round messages and transcript: instead of
/// one compact array per gather it folds the layer input `vin` (rows x W) once and reads every
/// gather through its map, since folding over the slot variables commutes with the cell gather.
/// With `skip(p)` true for a row pair whose rows are both zero (fixed dummy slots), the pair adds
/// nothing and folds to zero, so it is skipped; the caller only passes rows that are zero.
#[allow(clippy::too_many_arguments)]
pub(crate) fn main_prove_lm<T: crate::pcs::Fs>(spec: &Spec, vin: &[F], rp: &[EF], mut w: Vec<Vec<EF>>, mut claim: EF, logp: usize, tr: &mut T, msgs: &mut Vec<EF>, skip: &(dyn Fn(usize, usize) -> bool + Sync)) -> (Vec<EF>, Vec<EF>) {
    let nv = logp + LOGW;
    let ng = spec.gathers.len();
    let df = spec.deg_f();
    let mut pt = vec![EF::ZERO; nv];
    let mut rows = 1usize << logp;
    let mut ep = eq_table(&rp[..logp - 1]);
    let wc: Vec<Vec<EF>> = spec.terms.iter().enumerate().map(|(ti, t)| t.active.iter().map(|&s| w[ti][s as usize]).collect()).collect();
    let mut vf: Vec<EF> = Vec::new();
    while rows > 1 {
        let var = LOGW + rows.trailing_zeros() as usize - 1;
        let x = rp[var - LOGW];
        let hr = rows / 2;
        let with1 = x == EF::ZERO;
        let first = vf.is_empty();
        let pair = |p: usize| -> [EF; MAXJ] {
            let mut acc = [EF::ZERO; MAXJ];
            if skip(rows, p) {
                return acc;
            }
            let get = |row: usize, c: usize| -> EF { if first { EF::from(vin[row * W + c]) } else { vf[row * W + c] } };
            let mut vals = [[EF::ZERO; MAXJ]; MAXJ];
            for (ti, t) in spec.terms.iter().enumerate() {
                let uses = t.kind.uses();
                if let Kind::Lin(j) = t.kind {
                    let (mut sl, mut sh) = (EF::ZERO, EF::ZERO);
                    for (a, &s) in t.active.iter().enumerate() {
                        let c = spec.gathers[j][s as usize] as usize;
                        sl += wc[ti][a] * get(p, c);
                        sh += wc[ti][a] * get(p + hr, c);
                    }
                    let d = sh - sl;
                    let mut v = sl;
                    for a in acc.iter_mut().take(df + 1) {
                        *a += v;
                        v += d;
                    }
                    continue;
                }
                for (a, &s) in t.active.iter().enumerate() {
                    for &j in &uses {
                        let c = spec.gathers[j][s as usize] as usize;
                        let (lo, hi) = (get(p, c), get(p + hr, c));
                        let dl = hi - lo;
                        vals[0][j] = lo;
                        vals[1][j] = hi;
                        let mut v = hi;
                        for row in vals.iter_mut().take(df + 1).skip(2) {
                            v += dl;
                            row[j] = v;
                        }
                    }
                    let ws = wc[ti][a];
                    acc[0] += ws * eval_f(&t.kind, &vals[0]);
                    if with1 {
                        acc[1] += ws * eval_f(&t.kind, &vals[1]);
                    }
                    for k in 2..=df {
                        acc[k] += ws * eval_f(&t.kind, &vals[k]);
                    }
                }
            }
            let e = ep[p];
            core::array::from_fn(|k| e * acc[k])
        };
        let mut q = (0..hr).into_par_iter().map(pair).reduce(|| [EF::ZERO; MAXJ], |a, b| core::array::from_fn(|k| a[k] + b[k]));
        if x != EF::ZERO {
            q[1] = (claim - (EF::ONE - x) * q[0]) * x.inverse();
        }
        let co = to_coeffs(&q[..=df]);
        let msg = &co[1..];
        tr.absorb_efs(msg);
        msgs.extend_from_slice(msg);
        let r = kec10::inject_r(tr.sample_ef(), x);
        claim = next_a(claim, x, msg, r);
        pt[var] = r;
        if first {
            let mut nf = vec![EF::ZERO; hr * W];
            nf.par_chunks_mut(W).enumerate().for_each(|(p, row)| {
                if skip(rows, p) {
                    return;
                }
                let (lo, hi) = (&vin[p * W..(p + 1) * W], &vin[(p + hr) * W..(p + hr + 1) * W]);
                for c in 0..W {
                    row[c] = r * (hi[c] - lo[c]) + lo[c];
                }
            });
            vf = nf;
        } else {
            let (lo, hi) = vf.split_at_mut(hr * W);
            lo.par_chunks_mut(W).zip(hi.par_chunks(W)).enumerate().for_each(|(p, (a, b))| {
                if skip(rows, p) {
                    return;
                }
                for c in 0..W {
                    a[c] += r * (b[c] - a[c]);
                }
            });
            vf.truncate(hr * W);
        }
        if ep.len() > 1 {
            halve_eq(&mut ep);
        }
        rows /= 2;
    }
    let mut g: Vec<Vec<EF>> = (0..ng)
        .map(|j| {
            let mut full = vec![EF::ZERO; W];
            for &s in &spec.terms[spec.owner[j]].active {
                full[s as usize] = vf[spec.gathers[j][s as usize] as usize];
            }
            full
        })
        .collect();
    let mut cols = W;
    while cols > 1 {
        let h = round_b(spec, &g, &w, cols);
        tr.absorb_efs(&h);
        msgs.extend_from_slice(&h);
        let r = tr.sample_ef();
        claim = interp(&h, claim, r);
        pt[cols.trailing_zeros() as usize - 1] = r;
        g.iter_mut().for_each(|c| fold_half(c, r));
        w.iter_mut().for_each(|c| fold_half(c, r));
        cols /= 2;
    }
    let vals: Vec<EF> = g.iter().map(|c| c[0]).collect();
    debug_assert_eq!(claim, spec.terms.iter().enumerate().map(|(ti, t)| w[ti][0] * eval_f(&t.kind, &vals)).sum::<EF>());
    tr.absorb_efs(&vals);
    msgs.extend_from_slice(&vals);
    (pt, vals)
}

/// Verifier side of main_prove: returns (point, T_j values) after the terminal check.
pub(crate) fn main_verify<T: crate::pcs::Fs>(spec: &Spec, r_in: &[EF], mut claim: EF, logp: usize, tr: &mut T, rd: &mut Reader) -> Result<(Vec<EF>, Vec<EF>), String> {
    let nv = logp + LOGW;
    let (d, df) = (spec.d(), spec.deg_f());
    let mut pt = vec![EF::ZERO; nv];
    for k in 0..logp {
        let var = LOGW + logp - 1 - k;
        let h = rd.take(df)?;
        tr.absorb_efs(&h);
        let r = tr.sample_ef();
        claim = next_a(claim, r_in[var], &h, r);
        pt[var] = r;
    }
    for k in 0..LOGW {
        let h = rd.take(d)?;
        tr.absorb_efs(&h);
        let r = tr.sample_ef();
        claim = interp(&h, claim, r);
        pt[LOGW - 1 - k] = r;
    }
    let vals = rd.take(spec.gathers.len())?;
    let (ea, eb) = (eq_table(&r_in[..LOGW]), eq_table(&pt[..LOGW]));
    let mut rhs = EF::ZERO;
    for t in &spec.terms {
        let wt: EF = t
            .active
            .iter()
            .map(|&s| {
                let s = s as usize;
                let v = ea[s] * eb[s];
                if t.sel[s] == 1 { v } else { -v }
            })
            .sum();
        rhs += wt * eval_f(&t.kind, &vals);
    }
    if claim != rhs {
        return Err(format!("{}: main terminal check", spec.name));
    }
    tr.absorb_efs(&vals);
    Ok((pt, vals))
}

fn wiring_m(spec: &Spec, r_s: &[EF], betas: &[EF]) -> Vec<EF> {
    let eqs = eq_table(r_s);
    let mut m = vec![EF::ZERO; W];
    for (j, gj) in spec.gathers.iter().enumerate() {
        for &s in &spec.terms[spec.owner[j]].active {
            m[gj[s as usize] as usize] += betas[j] * eqs[s as usize];
        }
    }
    m
}

/// Wiring sumcheck: reduce sum_j beta_j T_j(r') to one claim on the input layer.
pub(crate) fn wiring_prove<T: crate::pcs::Fs>(spec: &Spec, vin: &[F], pt: &[EF], vals: &[EF], logp: usize, tr: &mut T, msgs: &mut Vec<EF>) -> Vec<EF> {
    let betas = tr.sample_efs(spec.gathers.len());
    let mut claim: EF = betas.iter().zip(vals).map(|(&b, &v)| b * v).sum();
    let ep = eq_table(&pt[LOGW..]);
    let rows = 1usize << logp;
    let chunk = (rows / 64).max(1);
    let mut a: Vec<EF> = (0..rows.div_ceil(chunk))
        .into_par_iter()
        .map(|c| {
            let mut acc = vec![EF::ZERO; W];
            for p in c * chunk..((c + 1) * chunk).min(rows) {
                let row = &vin[p * W..(p + 1) * W];
                let e = ep[p];
                for s in 0..W {
                    acc[s] += e * row[s];
                }
            }
            acc
        })
        .reduce(|| vec![EF::ZERO; W], |mut x, y| {
            x.iter_mut().zip(&y).for_each(|(a, b)| *a += *b);
            x
        });
    ops::add(ops::WI, ops::MIX, (rows * W) as u64);
    ops::add(ops::WI, ops::ADD, (rows * W) as u64);
    ops::add(ops::WI, ops::GEN, (spec.terms.iter().map(|t| t.active.len() * t.kind.uses().len()).sum::<usize>() + (1 << LOGW) * 4 + rows) as u64);
    let mut m = wiring_m(spec, &pt[..LOGW], &betas);
    let mut ps = vec![EF::ZERO; LOGW];
    for v in (0..LOGW).rev() {
        let h = a.len() / 2;
        let (mut h0, mut h2) = (EF::ZERO, EF::ZERO);
        for i in 0..h {
            h0 += a[i] * m[i];
            h2 += (a[i + h].double() - a[i]) * (m[i + h].double() - m[i]);
        }
        let hh = [h0, h2];
        tr.absorb_efs(&hh);
        msgs.extend_from_slice(&hh);
        let r = tr.sample_ef();
        claim = interp(&hh, claim, r);
        ps[v] = r;
        fold_half(&mut a, r);
        fold_half(&mut m, r);
    }
    debug_assert_eq!(claim, a[0] * m[0]);
    tr.absorb_ef(a[0]);
    msgs.push(a[0]);
    let mut out = ps;
    out.extend_from_slice(&pt[LOGW..]);
    out
}

pub(crate) fn wiring_verify<T: crate::pcs::Fs>(spec: &Spec, pt: &[EF], vals: &[EF], tr: &mut T, rd: &mut Reader) -> Result<(Vec<EF>, EF), String> {
    let betas = tr.sample_efs(spec.gathers.len());
    let mut claim: EF = betas.iter().zip(vals).map(|(&b, &v)| b * v).sum();
    let mut ps = vec![EF::ZERO; LOGW];
    for v in (0..LOGW).rev() {
        let hh = rd.take(2)?;
        tr.absorb_efs(&hh);
        let r = tr.sample_ef();
        claim = interp(&hh, claim, r);
        ps[v] = r;
    }
    let vin = rd.take(1)?[0];
    let m = wiring_m(spec, &pt[..LOGW], &betas);
    let mr: EF = eq_table(&ps).iter().zip(&m).map(|(&a, &b)| a * b).sum();
    if claim != vin * mr {
        return Err(format!("{}: wiring terminal check", spec.name));
    }
    tr.absorb_ef(vin);
    let mut out = ps;
    out.extend_from_slice(&pt[LOGW..]);
    Ok((out, vin))
}

pub struct Reader<'a> {
    b: &'a [u8],
    pub pos: usize,
}
impl<'a> Reader<'a> {
    pub(crate) fn new(b: &'a [u8]) -> Self {
        Reader { b, pos: 0 }
    }
    pub(crate) fn take(&mut self, k: usize) -> Result<Vec<EF>, String> {
        (0..k)
            .map(|_| {
                let s = self.b.get(self.pos..self.pos + 40).ok_or("truncated")?;
                self.pos += 40;
                ef_from_bytes(s).ok_or_else(|| "non-canonical element".to_string())
            })
            .collect()
    }
}

/// Direct comparison of the histogram first round and first fold with the direct ones on
/// synthetic gathers (mostly +-1, some 0, some arbitrary values), every layer kind, with and
/// without the t = 1 slot. Returns (identical cases, cases).
pub fn hist_selfcheck() -> (usize, usize) {
    let mut st = 0x2545_f491_4f6c_dd1du64;
    let mut next = move || {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        st
    };
    let (mut same, mut total) = (0, 0);
    let rows = 8usize;
    for spec in [theta_a(0), theta_b(5), chi(3), bool_spec()] {
        let tabs = hist_tables(&spec);
        for mix in 0..3 {
            let g: Vec<Vec<F>> = (0..spec.gathers.len())
                .map(|j| {
                    let m = spec.terms[spec.owner[j]].active.len();
                    (0..rows * m)
                        .map(|_| {
                            let x = next();
                            match (mix, x % 64) {
                                (0, _) | (_, 2..) => if x & (1 << 20) == 0 { F::ONE } else { -F::ONE },
                                (1, _) => F::ZERO,
                                _ => F::from_u64(x >> 8),
                            }
                        })
                        .collect()
                })
                .collect();
            let mut rnd_ef = || EF::from_basis_coefficients_fn(|_| F::from_u64(next()));
            let ep: Vec<EF> = (0..rows / 2).map(|_| rnd_ef()).collect();
            let w: Vec<Vec<EF>> = spec.terms.iter().map(|t| (0..t.active.len()).map(|_| rnd_ef()).collect()).collect();
            for with1 in [false, true] {
                total += 1;
                same += (round_a::<F>(&spec, &g, &ep, &w, rows, with1) == round_a_hist(&spec, &g, &ep, &w, rows, with1, &tabs)) as usize;
            }
            let r = rnd_ef();
            let n = g[0].len() / 2;
            let (mut b0, mut b1) = (Vec::new(), Vec::new());
            fold_first(&g[0], n, r, &mut b0, false);
            fold_first(&g[0], n, r, &mut b1, true);
            total += 1;
            same += (b0 == b1) as usize;
        }
    }
    ops::take();
    (same, total)
}

// ---------------------------------------------------------------- top level

#[derive(Clone, Copy, Default)]
pub struct KOpts {
    /// UNSAFE control: skip the canonical-input zerocheck (prover and verifier).
    pub skip_booleanity: bool,
}

fn statement(logp: usize) -> Vec<u8> {
    format!(
        "qlyphs keccak-f1600 GKR kernel v1; instances 2^{logp}; +-1 encoding, 2048-cell rows, 72 layers (theta-a, theta-b, rho-pi-chi-iota); \
         Goldilocks^5; WHIR p3-whir=0.8.0 profile {:?}; one table [in, out]; openings in@gkr, in@zerocheck, out@r",
        pcs::profile(logp + LOGW + 1)
    )
    .into_bytes()
}

fn protocol(nv: usize) -> OpeningProtocol {
    OpeningProtocol::new(vec![TableSpec::new(
        TableShape::new(nv, 2),
        vec![OpeningBatch::new(vec![0], vec![]), OpeningBatch::new(vec![0], vec![]), OpeningBatch::new(vec![1], vec![])],
    )])
}

fn p3_point(my: &[EF]) -> Point<EF> {
    Point::new(my.iter().rev().copied().collect::<Vec<_>>())
}

pub struct ProveReport {
    pub frontend_elems: usize,
    pub whir_bytes: usize,
}

/// Prove that `out` = Keccak-f[1600](`inp`) row by row (the prover computes out itself unless
/// `out_override` is given, soundness tests only).
pub fn prove(inp: Vec<F>, logp: usize, o: KOpts, out_override: Option<&dyn Fn(&mut Vec<F>)>, tm: &mut Timer) -> (Vec<u8>, ProveReport) {
    let rows = 1usize << logp;
    let nv = logp + LOGW;
    let sp = specs();
    let mut layers = Vec::with_capacity(sp.len() + 1);
    layers.push(inp);
    for s in &sp {
        let next = apply(s, layers.last().unwrap(), rows);
        layers.push(next);
    }
    let mut out = layers.last().unwrap().clone();
    if let Some(f) = out_override {
        f(&mut out);
    }
    tm.lap("K0 witness: 72 layers (native, field values)");

    let (pcs_, fold0) = pcs::make_pcs(nv + 1, 3);
    let mut data = Vec::with_capacity(2 * rows * W);
    data.extend_from_slice(&layers[0]);
    data.extend_from_slice(&out);
    let wit = Layout::new_witness(vec![Table::new(RowMajorMatrix::new(data, rows * W))], fold0);
    let mut tr = Tr::new();
    tr.absorb_bytes(b"keccak-kernel-statement", &statement(logp));
    let (comm, pdata) = pcs_.commit(wit, &mut tr.ch).expect("commit");
    tm.lap("K1 WHIR commit [in, out]");

    let mut msgs = Vec::new();
    let r_out = tr.sample_efs(nv);
    let v_out = crate::field::mle_eval(&out, &r_out);
    tr.absorb_ef(v_out);
    msgs.push(v_out);
    drop(out);
    // Canonical input: sum eq(tau, b) in(b)^2 = sum_{s < 1600} eq(tau_s, s).
    let mut gpool: Vec<Vec<F>> = (0..6).map(|_| vec![F::ZERO; rows * W]).collect();
    let mut epool: Vec<Vec<EF>> = (0..6).map(|_| Vec::with_capacity(rows / 2 * W)).collect();
    let (r_z, v_z) = if o.skip_booleanity {
        (vec![EF::ZERO; nv], EF::ZERO)
    } else {
        let tau = tr.sample_efs(nv);
        let bs = bool_spec();
        let w = eq_table(&tau[..LOGW]);
        let claim: EF = w[..STATE].iter().copied().sum();
        gpool[0].par_iter_mut().zip(layers[0].par_iter()).for_each(|(a, &b)| *a = b);
        let (pt, vals) = main_prove(&bs, &gpool, &mut epool, &tau[LOGW..], vec![w], claim, logp, &mut tr, &mut msgs);
        (pt, vals[0])
    };
    tm.lap("K2 output claim, canonical-input zerocheck");

    let (mut t_main, mut t_wire) = (0.0, 0.0);
    let (mut pt, mut v) = (r_out.clone(), v_out);
    for k in (0..sp.len()).rev() {
        let s = &sp[k];
        let t = Instant::now();
        let vin = &layers[k];
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
        let eqs = eq_table(&pt[..LOGW]);
        let w: Vec<Vec<EF>> = s.terms.iter().map(|t| (0..W).map(|i| match t.sel[i] { 0 => EF::ZERO, 1 => eqs[i], _ => -eqs[i] }).collect()).collect();
        let (pt2, vals) = main_prove(s, &gpool, &mut epool, &pt[LOGW..], w, v, logp, &mut tr, &mut msgs);
        t_main += t.elapsed().as_secs_f64() * 1e3;
        let t = Instant::now();
        pt = wiring_prove(s, vin, &pt2, &vals, logp, &mut tr, &mut msgs);
        v = *msgs.last().unwrap();
        t_wire += t.elapsed().as_secs_f64() * 1e3;
        layers.truncate(k + 1);
    }
    debug_assert_eq!(v, crate::field::mle_eval(&layers[0], &pt));
    debug_assert!(o.skip_booleanity || v_z == crate::field::mle_eval(&layers[0], &r_z));
    tm.phases.push((format!("K3a GKR main sumchecks (72 layers, {t_main:.0} ms of the next line)"), 0.0, 0, 0, 0, 0));
    tm.phases.push((format!("K3b GKR wiring sumchecks ({t_wire:.0} ms of the next line)"), 0.0, 0, 0, 0, 0));
    tm.lap("K3 GKR (72 layer reductions)");
    drop(layers);
    drop(gpool);
    drop(epool);

    let proof = pcs_.open_at(pdata, &protocol(nv), &[p3_point(&pt), p3_point(&r_z), p3_point(&r_out)], &mut tr.ch).expect("open");
    let whir = bincode::serialize(&proof).unwrap();
    tm.lap("K4 WHIR opening (3 claims)");

    let mut bytes = Vec::new();
    bytes.extend_from_slice(&words_to_bytes(&comm.roots()[0]));
    bytes.extend_from_slice(&(msgs.len() as u32).to_le_bytes());
    msgs.iter().for_each(|x| ef_to_bytes(x, &mut bytes));
    bytes.extend_from_slice(&whir);
    (bytes, ProveReport { frontend_elems: msgs.len(), whir_bytes: whir.len() })
}

pub fn verify(logp: usize, o: KOpts, bytes: &[u8], tm: &mut Timer) -> Result<(), String> {
    let nv = logp + LOGW;
    let sp = specs();
    if bytes.len() < 68 {
        return Err("truncated".into());
    }
    let comm: Commitment = MerkleCap::new(vec![core::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))]);
    let nm = u32::from_le_bytes(bytes[64..68].try_into().unwrap()) as usize;
    let expect = 1 + if o.skip_booleanity { 0 } else { bool_spec().main_elems(logp) } + sp.iter().map(|s| s.main_elems(logp) + 2 * LOGW + 1).sum::<usize>();
    if nm != expect {
        return Err(format!("message count {nm} != {expect}"));
    }
    let mut rd = Reader { b: bytes, pos: 68 };
    let mut tr = Tr::new();
    tr.absorb_bytes(b"keccak-kernel-statement", &statement(logp));
    observe_commitment::<F, _, _>(&mut tr.ch, comm.clone());
    let r_out = tr.sample_efs(nv);
    let v_out = rd.take(1)?[0];
    tr.absorb_ef(v_out);
    let (r_z, v_z) = if o.skip_booleanity {
        (vec![EF::ZERO; nv], None)
    } else {
        let tau = tr.sample_efs(nv);
        let bs = bool_spec();
        let w = eq_table(&tau[..LOGW]);
        let claim: EF = w[..STATE].iter().copied().sum();
        let (pt, vals) = main_verify(&bs, &tau, claim, logp, &mut tr, &mut rd)?;
        (pt, Some(vals[0]))
    };
    let (mut pt, mut v) = (r_out.clone(), v_out);
    for k in (0..sp.len()).rev() {
        let (pt2, vals) = main_verify(&sp[k], &pt, v, logp, &mut tr, &mut rd)?;
        (pt, v) = wiring_verify(&sp[k], &pt2, &vals, &mut tr, &mut rd)?;
    }
    tm.lap("KV1 transcript replay, 72 layer checks");
    let proof: PcsProof = bincode::deserialize(&bytes[rd.pos..]).map_err(|_| "WHIR proof parse")?;
    if bincode::serialized_size(&proof).map_err(|_| "size")? as usize != bytes.len() - rd.pos {
        return Err("trailing bytes".into());
    }
    let (pcs_, _) = pcs::make_pcs(nv + 1, 3);
    let evals = pcs_.verify_at(&comm, &proof, &protocol(nv), &[p3_point(&pt), p3_point(&r_z), p3_point(&r_out)], &mut tr.ch).map_err(|e| format!("WHIR {e:?}"))?;
    tm.lap("KV2 WHIR verification (3 claims)");
    if evals[0].current()[0] != v {
        return Err("input opening != last GKR claim".into());
    }
    if let Some(vz) = v_z {
        if evals[1].current()[0] != vz {
            return Err("input opening != zerocheck claim".into());
        }
    }
    if evals[2].current()[0] != v_out {
        return Err("output opening != output claim".into());
    }
    Ok(())
}
