//! Round 10 prover path for the Keccak layers of the hidden-u certificate (prover only; the
//! messages, the transcript and the certificate bytes are those of `main_prove_lm` and
//! `wiring_prove`, and the verifier is untouched).
//!
//! - Trace: every layer is bit-packed (one 64-bit word per Keccak lane, bit 1 = field -1) and
//!   computed natively from the layer's lane maps; only the 25 round boundaries are stored and
//!   the two inner layers of a round are recomputed when the GKR reaches it. Rows are the 16 N
//!   slots p = 16 i + q; slots q >= `nreal` are the field-zero dummy rows, whose words are never
//!   read.
//! - Phase-A rounds 0 .. J-1 bind signature bits only. After j folds a cell's value depends on
//!   2^j input bits, so it is read from a table of the 2^(2^j) possible folded values
//!   (selection) instead of a stored extension-field array. Round 0 is evaluated in the base
//!   field. Dummy row pairs stay zero and are skipped, as in the reference.
//! - At round J the folded layer (rows / 2^J x 2048 cells) is materialized once by selection;
//!   the remaining rounds and phase B are those of `main_prove_lm`.
//! - Wiring: sum_p eq(p) in(p, s) = E - 2 sum_{p real, bit = 1} eq(p) on the support, with
//!   E = sum over real rows of eq(p).
//!
//! All of this is exact field arithmetic, so equal values are equal elements; `k10cmp`
//! compares every certificate byte with the reference path. The packed-layer, lane-map,
//! selection-table and subset-sum helpers come from the round-9 kernel prototype (hist9.rs).

use super::*;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
#[cfg(feature = "lab-hooks")]
use std::sync::atomic::AtomicU8;

/// Use this path for canonical inputs (H9_K10, default on; H9_K10=0 is the reference path).
pub static ON: AtomicBool = AtomicBool::new(true);
/// Phase-A round at which the folded layer is materialized (H9_K10_J, 1..=4; capped at log2 N).
pub static JMAT: AtomicUsize = AtomicUsize::new(4);
/// Weighted-histogram rounds (round 9 section D) for the phase-A rounds j < 3 where a term's
/// table fits (H9_K10_HIST=1; default off until its whole-kernel timing is measured).
pub static HIST: AtomicBool = AtomicBool::new(false);
/// Test-only challenge injection in the phase-A rounds of every Keccak layer, applied in both
/// prover paths after the challenge is sampled: 0 off (the protocol), 1 = 0, 2 = 1, 3 = 1/2,
/// 4 = (1 - x)/(1 - 2x) (eq1(x, r) = 0, exceptional Gruen), 5 = (1 + i)/2, 6 = a base-field
/// element, 7 = one of these chosen from the sample. Proofs made with injection do not verify.
#[cfg(feature = "lab-hooks")]
pub static INJECT: AtomicU8 = AtomicU8::new(0);
/// Time split (microseconds): trace, selection rounds, materialization, folded rounds and
/// phase B, wiring.
pub static PROF: [std::sync::atomic::AtomicU64; 5] = [const { std::sync::atomic::AtomicU64::new(0) }; 5];
pub const PROF_NAMES: [&str; 5] = ["packed trace", "selection rounds", "materialization", "folded rounds and phase B", "wiring"];

pub fn prof(i: usize, t: Instant) {
    PROF[i].fetch_add(t.elapsed().as_micros() as u64, Relaxed);
}

pub fn configure_from_env() -> String {
    if let Ok(v) = std::env::var("H9_K10") {
        ON.store(v != "0", Relaxed);
    }
    if let Ok(v) = std::env::var("H9_K10_HIST") {
        HIST.store(v == "1", Relaxed);
    }
    if let Ok(v) = std::env::var("H9_K10_J") {
        JMAT.store(v.parse::<usize>().expect("H9_K10_J").clamp(1, 4), Relaxed);
    }
    describe()
}

pub fn describe() -> String {
    if ON.load(Relaxed) {
        format!("round-10 Keccak path (packed trace, selection rounds, materialization at round {}, histogram rounds {})", JMAT.load(Relaxed), if HIST.load(Relaxed) { "on" } else { "off" })
    } else {
        "reference Keccak path (field-valued layers, folded arrays)".into()
    }
}

pub fn on() -> bool {
    ON.load(Relaxed)
}

/// Injection of a phase-A challenge (identity unless a test mode is set).
#[cfg(not(feature = "lab-hooks"))]
#[inline(always)]
pub fn inject_r(s: EF, _x: EF) -> EF {
    s
}

/// Injection of a phase-A challenge (identity unless a test mode is set; lab-hooks only).
#[cfg(feature = "lab-hooks")]
pub fn inject_r(s: EF, x: EF) -> EF {
    let mut mode = INJECT.load(Relaxed);
    if mode == 0 {
        return s;
    }
    let c0 = <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&s)[0].as_canonical_u64();
    if mode == 7 {
        mode = [0u8, 1, 2, 3, 4, 5, 6, 0][(c0 >> 13) as usize % 8];
    }
    match mode {
        1 => EF::ZERO,
        2 => EF::ONE,
        3 => EF::from(half()),
        4 if x.double() != EF::ONE => (EF::ONE - x) * (EF::ONE - x.double()).inverse(),
        5 => crate::pcs::vroot(),
        6 => EF::from(F::from_u64(c0)),
        _ => s,
    }
}

pub const WORDS: usize = W / 64;

// ---------------------------------------------------------------- lane maps and packed layers

/// A gather as a lane map: active word i of the owner term reads rotl(src[i], rot[i]).
pub struct GMap {
    pub words: Vec<usize>,
    pub src: Vec<usize>,
    pub rot: Vec<u32>,
}

/// Lane maps of every gather of a spec, derived from the cell maps (and checked: each active
/// word is whole and reads one source word under one rotation).
pub fn gmaps(spec: &Spec) -> Vec<GMap> {
    spec.gathers
        .iter()
        .enumerate()
        .map(|(j, g)| {
            let act = &spec.terms[spec.owner[j]].active;
            assert!(act.len() % 64 == 0);
            let words: Vec<usize> = act
                .chunks(64)
                .map(|c| {
                    let w = c[0] as usize / 64;
                    assert!(c.iter().enumerate().all(|(z, &s)| s as usize == 64 * w + z), "active cells are whole words");
                    w
                })
                .collect();
            let (mut src, mut rot) = (vec![], vec![]);
            for &w in &words {
                let s0 = g[64 * w] as usize;
                let sw = s0 / 64;
                let r = (64 - (s0 % 64) as u32) % 64;
                for z in 0..64 {
                    let s = g[64 * w + z] as usize;
                    assert_eq!(s / 64, sw, "one source word");
                    assert_eq!((z as u32 + 64 - (s % 64) as u32) % 64, r, "one rotation");
                }
                src.push(sw);
                rot.push(r);
            }
            GMap { words, src, rot }
        })
        .collect()
}

/// Bit-packed layer: rows x WORDS words; `support` = words that hold +-1 values (others are 0).
pub struct PLayer {
    pub bits: Vec<u64>,
    pub support: u32,
}

fn sign_masks(t: &Term) -> Vec<u64> {
    t.active.chunks(64).map(|c| c.iter().enumerate().fold(0u64, |m, (z, &s)| m | (((t.sel[s as usize] == -1) as u64) << z))).collect()
}

/// Native layer: out = sum_t sel_t f_t(gathers), in bits (product = xor, chi = b0 ^ (!b1 & b2)).
pub fn apply_packed(spec: &Spec, maps: &[GMap], inp: &PLayer, rows: usize) -> PLayer {
    for m in maps {
        assert!(m.src.iter().all(|&s| inp.support >> s & 1 == 1), "{}: gathers read the support only", spec.name);
    }
    let signs: Vec<Vec<u64>> = spec.terms.iter().map(sign_masks).collect();
    let mut bits = vec![0u64; rows * WORDS];
    let mut support = 0u32;
    for t in &spec.terms {
        for c in t.active.chunks(64) {
            support |= 1 << (c[0] / 64);
        }
    }
    bits.par_chunks_mut(WORDS).enumerate().for_each(|(p, o)| {
        let row = &inp.bits[p * WORDS..(p + 1) * WORDS];
        for (ti, t) in spec.terms.iter().enumerate() {
            let uses = t.kind.uses();
            let m0 = &maps[uses[0]];
            for i in 0..m0.words.len() {
                let g = |u: usize| row[maps[u].src[i]].rotate_left(maps[u].rot[i]);
                let f = match &t.kind {
                    Kind::Lin(j) => g(*j),
                    Kind::Prod(js) => js.iter().fold(0, |a, &j| a ^ g(j)),
                    Kind::Chi([a, b, c]) => g(*a) ^ (!g(*b) & g(*c)),
                    Kind::Sq(_) => 0,
                };
                o[m0.words[i]] = f ^ signs[ti][i];
            }
        }
    });
    PLayer { bits, support }
}

/// Field values of a packed layer (+-1 on the support, 0 elsewhere), dummy rows zero (tests).
pub fn unpack(l: &PLayer, rows: usize, nreal: usize) -> Vec<F> {
    let mut v = vec![F::ZERO; rows * W];
    v.par_chunks_mut(W).enumerate().for_each(|(p, o)| {
        if p % 16 >= nreal {
            return;
        }
        for w in 0..WORDS {
            if l.support >> w & 1 == 1 {
                let x = l.bits[p * WORDS + w];
                for z in 0..64 {
                    o[64 * w + z] = if x >> z & 1 == 1 { -F::ONE } else { F::ONE };
                }
            }
        }
    });
    v
}

/// SP16[b]: the eight bits of b spread to eight 16-bit lanes (lane z = bit z).
const fn spread16() -> [u128; 256] {
    let mut t = [0u128; 256];
    let mut b = 0;
    while b < 256 {
        let mut z = 0;
        while z < 8 {
            if b >> z & 1 == 1 {
                t[b] |= 1u128 << (16 * z);
            }
            z += 1;
        }
        b += 1;
    }
    t
}
static SP16: [u128; 256] = spread16();

/// Sixty-four 16-bit lanes (lane z = cell z of a word); `or_plane` puts bit z of `wd` at bit `sh`
/// of lane z.
#[inline(always)]
fn or_plane(acc: &mut [u128; 8], wd: u64, sh: u32) {
    for (g, a) in acc.iter_mut().enumerate() {
        *a |= SP16[(wd >> (8 * g)) as u8 as usize] << sh;
    }
}

#[inline(always)]
fn lanes(acc: &[u128; 8]) -> [u16; 64] {
    core::array::from_fn(|z| (acc[z / 8] >> (16 * (z % 8))) as u16)
}

#[inline(always)]
fn even_bits(x: usize, n: usize) -> usize {
    (0..n).fold(0, |a, k| a | (x >> (2 * k) & 1) << k)
}

#[inline(always)]
fn odd_bits(x: usize, n: usize) -> usize {
    (0..n).fold(0, |a, k| a | (x >> (2 * k + 1) & 1) << k)
}

/// Value tables of the folded Boolean values: vals[pattern of 2^j bits] (bit k = row offset
/// k R_j; bit 1 = -1), the next table from this one by the fold with r (lo + r (hi - lo)).
fn next_vals(v: &[EF], r: EF) -> Vec<EF> {
    let n = v.len().trailing_zeros() as usize;
    (0..v.len() * v.len())
        .into_par_iter()
        .with_min_len(1 << 10)
        .map(|pat| {
            let (lo, hi) = (v[even_bits(pat, n)], v[odd_bits(pat, n)]);
            lo + r * (hi - lo)
        })
        .collect()
}

/// The 64 folding patterns of one gathered word after j folds: bit k of lane z is cell z of
/// the gathered word in original row `p + k * step`.
#[inline(always)]
fn patterns(lay: &PLayer, m: &GMap, i: usize, p: usize, step: usize, j: usize) -> [u16; 64] {
    let mut acc = [0u128; 8];
    for k in 0..1usize << j {
        let wd = lay.bits[(p + k * step) * WORDS + m.src[i]].rotate_left(m.rot[i]);
        or_plane(&mut acc, wd, k as u32);
    }
    lanes(&acc)
}

// ---------------------------------------------------------------- trace

/// The packed Keccak trace: the 25 round boundaries, and the current round's two inner layers.
pub struct Trace10 {
    pub rows: usize,
    pub nreal: usize,
    ck: Vec<PLayer>,
    cur: Option<(usize, PLayer, PLayer)>,
    maps: Vec<Vec<GMap>>,
}

impl Trace10 {
    /// From the packed input layer (dummy rows zero). Layers are computed natively.
    pub fn build(input: PLayer, rows: usize, nreal: usize, sp: &[Spec]) -> Trace10 {
        let t0 = Instant::now();
        let maps: Vec<Vec<GMap>> = sp.iter().map(gmaps).collect();
        let mut ck = Vec::with_capacity(25);
        ck.push(input);
        for r in 0..24 {
            let a = apply_packed(&sp[3 * r], &maps[3 * r], ck.last().unwrap(), rows);
            let b = apply_packed(&sp[3 * r + 1], &maps[3 * r + 1], &a, rows);
            drop(a);
            let c = apply_packed(&sp[3 * r + 2], &maps[3 * r + 2], &b, rows);
            ck.push(c);
        }
        prof(0, t0);
        Trace10 { rows, nreal, ck, cur: None, maps }
    }
    pub fn output(&self) -> &PLayer {
        &self.ck[24]
    }
    pub fn maps(&self, k: usize) -> &[GMap] {
        &self.maps[k]
    }
    /// The input of layer k (called for k = 71 down to 0); frees what is no longer needed.
    pub fn input(&mut self, k: usize, sp: &[Spec]) -> &PLayer {
        let r = k / 3;
        if self.cur.as_ref().map(|c| c.0) != Some(r) {
            let t0 = Instant::now();
            self.cur = None;
            self.ck.truncate(r + 1);
            let a1 = apply_packed(&sp[3 * r], &self.maps[3 * r], &self.ck[r], self.rows);
            let a2 = apply_packed(&sp[3 * r + 1], &self.maps[3 * r + 1], &a1, self.rows);
            self.cur = Some((r, a1, a2));
            prof(0, t0);
        }
        let c = self.cur.as_ref().unwrap();
        match k % 3 {
            2 => &c.2,
            1 => &c.1,
            _ => &self.ck[r],
        }
    }
    /// Bytes held by the packed layers.
    pub fn bytes(&self) -> usize {
        (self.ck.len() + 2 * self.cur.is_some() as usize) * self.rows * WORDS * 8
    }
}

// ---------------------------------------------------------------- histogram rounds

/// Histogram rounds are tried for j < HROUNDS only.
const HROUNDS: usize = 3;

#[derive(Clone, Copy, PartialEq, Debug)]
enum Form {
    /// Endpoint classes: class = the 2^(j+1) bits of every factor; q(t) = sum_c G[c] f_c(t).
    E,
    /// Endpoint selections: for each sigma in {0,1}^d the alphabet tuple of the selected
    /// endpoints goes to bin H_|sigma|; q(t) = sum_k T_k t^k (1-t)^(d-k), T_k = sum H_k f.
    S,
}

/// The form for round j of a term, or None (the term selects in round j).
fn form(k: &Kind, j: usize) -> Option<Form> {
    if j >= HROUNDS {
        return None;
    }
    let d = k.uses().len();
    let multilinear = !matches!(k, Kind::Sq(_));
    if d << (j + 1) <= 12 {
        Some(Form::E)
    } else if multilinear && d << j <= 12 {
        Some(Form::S)
    } else {
        None
    }
}

/// Gathered planes of one gather: rows x |words| words, and which words read the support.
fn gplanes(m: &GMap, l: &PLayer, rows: usize) -> (Vec<u64>, Vec<bool>) {
    let mw = m.words.len();
    let mut buf = vec![0u64; rows * mw];
    buf.par_chunks_mut(mw).enumerate().for_each(|(p, o)| {
        let row = &l.bits[p * WORDS..(p + 1) * WORDS];
        for i in 0..mw {
            o[i] = row[m.src[i]].rotate_left(m.rot[i]);
        }
    });
    (buf, m.src.iter().map(|&s| l.support >> s & 1 == 1).collect())
}

/// t^k (1 - t)^(d - k) at a small integer t.
fn bern(t: usize, k: usize, d: usize) -> F {
    let (a, b) = (F::from_usize(t), F::ONE - F::from_usize(t));
    (0..k).fold(F::ONE, |x, _| x * a) * (0..d - k).fold(F::ONE, |x, _| x * b)
}

/// One histogram round of one term (the round-9 prototype, with the dummy row pairs skipped):
/// q(t) for t = 0..=df, summed over the real row pairs and the term's cells.
#[allow(clippy::too_many_arguments)]
fn hist_term(kind: &Kind, fm: Form, pl: &[&[u64]], live: &[bool], w: &[EF], vals: &[EF], j: usize, rows: usize, rp: &[EF], df: usize, nreal: usize) -> [EF; MAXJ] {
    let uses = kind.uses();
    let d = uses.len();
    let mw = live.len();
    let m = mw * 64;
    let hr = rows / 2;
    let nb = hr.trailing_zeros() as usize;
    let kb = 2usize << j;
    let ab = 1usize << j;
    let ncls = match fm {
        Form::E => 1usize << (d * kb),
        Form::S => (d + 1) << (d * ab),
    };
    let ca = 1usize << (d * ab);
    let threads = rayon::current_num_threads();
    let live_words = live.iter().filter(|&&x| x).count().max(1);
    let plan = |b: usize| {
        let blocks = 1usize << (nb - b);
        let chunks = (2 * threads).div_ceil(blocks).min(live_words).max(1);
        let collapse = if blocks == 1 { threads * ncls / 6 } else { blocks * chunks * ncls * 7 / 6 };
        ((1usize << b) * m + collapse, chunks)
    };
    // Blocks of at least 16 rows so that a block's rows share their slot pattern.
    let b = (4.min(nb)..=nb).min_by_key(|&b| plan(b).0).unwrap();
    let chunks = plan(b).1;
    let e_lo = eq_table(&rp[..b]);
    let e_hi = eq_table(&rp[b..nb]);
    let nlo = 1usize << b;
    let mut we = vec![EF::ZERO; nlo * m];
    we.par_chunks_mut(m).enumerate().for_each(|(l, o)| {
        for (x, &y) in o.iter_mut().zip(w) {
            *x = e_lo[l] * y;
        }
    });
    let lw: Vec<usize> = (0..mw).filter(|&i| live[i]).collect();
    let per = lw.len().div_ceil(chunks).max(1);
    let tasks: Vec<(usize, usize, usize)> = {
        let nlw = lw.len();
        (0..e_hi.len()).flat_map(move |ph| (0..nlw).step_by(per).map(move |c0| (ph, c0, (c0 + per).min(nlw))))
    }
    .collect();
    let single = e_hi.len() == 1;
    let g = tasks
        .par_iter()
        .fold(
            || (vec![EF::ZERO; if single { 0 } else { ncls }], vec![EF::ZERO; ncls]),
            |(mut gt, mut ga), &(ph, c0, c1)| {
                let dst: &mut Vec<EF> = if single {
                    &mut ga
                } else {
                    gt.iter_mut().for_each(|x| *x = EF::ZERO);
                    &mut gt
                };
                for l in 0..nlo {
                    let p = l | (ph << b);
                    if p % 16 >= nreal {
                        continue;
                    }
                    let wrow = &we[l * m..(l + 1) * m];
                    for &i in &lw[c0..c1] {
                        let ws = &wrow[i * 64..i * 64 + 64];
                        match fm {
                            Form::E => {
                                let mut acc = [0u128; 8];
                                for (fi, g) in pl.iter().enumerate() {
                                    for k in 0..kb {
                                        or_plane(&mut acc, g[(p + k * hr) * mw + i], (fi * kb + k) as u32);
                                    }
                                }
                                let cls = lanes(&acc);
                                for z in 0..64 {
                                    dst[cls[z] as usize] += ws[z];
                                }
                            }
                            Form::S => {
                                let mut lo = [[0u16; 64]; 6];
                                let mut hi = [[0u16; 64]; 6];
                                for (fi, g) in pl.iter().enumerate() {
                                    let (mut al, mut ah) = ([0u128; 8], [0u128; 8]);
                                    for k in 0..ab {
                                        let sh = (fi * ab + k) as u32;
                                        or_plane(&mut al, g[(p + 2 * k * hr) * mw + i], sh);
                                        or_plane(&mut ah, g[(p + (2 * k + 1) * hr) * mw + i], sh);
                                    }
                                    lo[fi] = lanes(&al);
                                    hi[fi] = lanes(&ah);
                                }
                                let mut sums = [0u32; 32];
                                for z in 0..64 {
                                    sums[0] = (0..d).fold(0, |a, fi| a | lo[fi][z] as u32);
                                    for fi in 0..d {
                                        let delta = (hi[fi][z] as u32).wrapping_sub(lo[fi][z] as u32);
                                        for mm in 0..1usize << fi {
                                            sums[mm | 1 << fi] = sums[mm].wrapping_add(delta);
                                        }
                                    }
                                    for (sg, &a) in sums.iter().enumerate().take(1 << d) {
                                        dst[(sg.count_ones() as usize) * ca + a as usize] += ws[z];
                                    }
                                }
                            }
                        }
                    }
                }
                if !single {
                    let e = e_hi[ph];
                    for (a, &x) in ga.iter_mut().zip(gt.iter()) {
                        *a += e * x;
                    }
                }
                (gt, ga)
            },
        )
        .map(|(_, ga)| ga)
        .reduce(
            || vec![EF::ZERO; ncls],
            |mut a, b| {
                a.iter_mut().zip(&b).for_each(|(x, y)| *x += *y);
                a
            },
        );
    let mut q = [EF::ZERO; MAXJ];
    match fm {
        Form::E => {
            let mask = (1usize << kb) - 1;
            q = (0..ncls)
                .into_par_iter()
                .with_min_len(64)
                .map(|c| {
                    let mut out = [EF::ZERO; MAXJ];
                    if g[c] == EF::ZERO {
                        return out;
                    }
                    let mut lohi = [(EF::ZERO, EF::ZERO); MAXJ];
                    for (fi, &u) in uses.iter().enumerate() {
                        let pat = c >> (fi * kb) & mask;
                        lohi[u] = (vals[even_bits(pat, ab)], vals[odd_bits(pat, ab)]);
                    }
                    for (t, o) in out.iter_mut().enumerate().take(df + 1) {
                        let mut v = [EF::ZERO; MAXJ];
                        for &u in &uses {
                            let (lo, hi) = lohi[u];
                            v[u] = lo + (hi - lo) * F::from_usize(t);
                        }
                        *o = g[c] * eval_f(kind, &v);
                    }
                    out
                })
                .reduce(|| [EF::ZERO; MAXJ], |a, b| core::array::from_fn(|k| a[k] + b[k]));
        }
        Form::S => {
            let amask = (1usize << ab) - 1;
            let fa: Vec<EF> = (0..ca)
                .into_par_iter()
                .with_min_len(64)
                .map(|a| {
                    let mut v = [EF::ZERO; MAXJ];
                    for (fi, &u) in uses.iter().enumerate() {
                        v[u] = vals[a >> (fi * ab) & amask];
                    }
                    eval_f(kind, &v)
                })
                .collect();
            let tk: Vec<EF> = (0..=d).map(|k| g[k * ca..(k + 1) * ca].iter().zip(&fa).map(|(&h, &f)| h * f).sum()).collect();
            for (t, o) in q.iter_mut().enumerate().take(df + 1) {
                *o = (0..=d).map(|k| tk[k] * bern(t, k, d)).sum();
            }
        }
    }
    q
}

// ---------------------------------------------------------------- main layer sumcheck

/// Round 0 from the packed layer, in the base field (the reference evaluates the same values).
#[allow(clippy::too_many_arguments)]
fn round0(spec: &Spec, maps: &[GMap], lay: &PLayer, ep: &[EF], wc: &[Vec<EF>], rows: usize, nreal: usize, with1: bool, mask: &[bool]) -> [EF; MAXJ] {
    let df = spec.deg_f();
    let hr = rows / 2;
    let pm = |b: u64| if b & 1 == 1 { -F::ONE } else { F::ONE };
    (0..hr)
        .into_par_iter()
        .filter(|&p| p % 16 < nreal)
        .map(|p| {
            let mut acc = [EF::ZERO; MAXJ];
            let mut vals = [[F::ZERO; MAXJ]; MAXJ];
            for (ti, t) in spec.terms.iter().enumerate() {
                if !mask[ti] {
                    continue;
                }
                let uses = t.kind.uses();
                let nw = t.active.len() / 64;
                if let Kind::Lin(j) = t.kind {
                    let m = &maps[j];
                    let (mut sl, mut sh) = (EF::ZERO, EF::ZERO);
                    for i in 0..nw {
                        let lo = lay.bits[p * WORDS + m.src[i]].rotate_left(m.rot[i]);
                        let hi = lay.bits[(p + hr) * WORDS + m.src[i]].rotate_left(m.rot[i]);
                        for z in 0..64 {
                            let ws = wc[ti][64 * i + z];
                            sl += ws * pm(lo >> z);
                            sh += ws * pm(hi >> z);
                        }
                    }
                    let d = sh - sl;
                    let mut v = sl;
                    for a in acc.iter_mut().take(df + 1) {
                        *a += v;
                        v += d;
                    }
                    continue;
                }
                for i in 0..nw {
                    let mut lw = [0u64; MAXJ];
                    let mut hw = [0u64; MAXJ];
                    for &j in &uses {
                        let m = &maps[j];
                        lw[j] = lay.bits[p * WORDS + m.src[i]].rotate_left(m.rot[i]);
                        hw[j] = lay.bits[(p + hr) * WORDS + m.src[i]].rotate_left(m.rot[i]);
                    }
                    for z in 0..64 {
                        for &j in &uses {
                            let lo = pm(lw[j] >> z);
                            let hi = pm(hw[j] >> z);
                            let dl = hi - lo;
                            vals[0][j] = lo;
                            vals[1][j] = hi;
                            let mut v = hi;
                            for row in vals.iter_mut().take(df + 1).skip(2) {
                                v += dl;
                                row[j] = v;
                            }
                        }
                        let ws = wc[ti][64 * i + z];
                        acc[0] += ws * eval_f(&t.kind, &vals[0]);
                        if with1 {
                            acc[1] += ws * eval_f(&t.kind, &vals[1]);
                        }
                        for k in 2..=df {
                            acc[k] += ws * eval_f(&t.kind, &vals[k]);
                        }
                    }
                }
            }
            let e = ep[p];
            core::array::from_fn(|k| e * acc[k])
        })
        .reduce(|| [EF::ZERO; MAXJ], |a, b| core::array::from_fn(|k| a[k] + b[k]))
}

/// Round j >= 1 by selection: the folded values of row pair (p, p + hr) are read from `vals`.
#[allow(clippy::too_many_arguments)]
fn round_sel(spec: &Spec, maps: &[GMap], lay: &PLayer, vals_t: &[EF], j: usize, ep: &[EF], wc: &[Vec<EF>], rows_j: usize, nreal: usize, with1: bool, mask: &[bool]) -> [EF; MAXJ] {
    let df = spec.deg_f();
    let hr = rows_j / 2;
    (0..hr)
        .into_par_iter()
        .filter(|&p| p % 16 < nreal)
        .map(|p| {
            let mut acc = [EF::ZERO; MAXJ];
            let mut vals = [[EF::ZERO; MAXJ]; MAXJ];
            for (ti, t) in spec.terms.iter().enumerate() {
                if !mask[ti] {
                    continue;
                }
                let uses = t.kind.uses();
                let nw = t.active.len() / 64;
                if let Kind::Lin(jj) = t.kind {
                    let m = &maps[jj];
                    let (mut sl, mut sh) = (EF::ZERO, EF::ZERO);
                    for i in 0..nw {
                        let lo = patterns(lay, m, i, p, rows_j, j);
                        let hi = patterns(lay, m, i, p + hr, rows_j, j);
                        for z in 0..64 {
                            let ws = wc[ti][64 * i + z];
                            sl += ws * vals_t[lo[z] as usize];
                            sh += ws * vals_t[hi[z] as usize];
                        }
                    }
                    let d = sh - sl;
                    let mut v = sl;
                    for a in acc.iter_mut().take(df + 1) {
                        *a += v;
                        v += d;
                    }
                    continue;
                }
                for i in 0..nw {
                    let mut lp = [[0u16; 64]; MAXJ];
                    let mut hp = [[0u16; 64]; MAXJ];
                    for &u in &uses {
                        lp[u] = patterns(lay, &maps[u], i, p, rows_j, j);
                        hp[u] = patterns(lay, &maps[u], i, p + hr, rows_j, j);
                    }
                    for z in 0..64 {
                        for &u in &uses {
                            let lo = vals_t[lp[u][z] as usize];
                            let hi = vals_t[hp[u][z] as usize];
                            let dl = hi - lo;
                            vals[0][u] = lo;
                            vals[1][u] = hi;
                            let mut v = hi;
                            for row in vals.iter_mut().take(df + 1).skip(2) {
                                v += dl;
                                row[u] = v;
                            }
                        }
                        let ws = wc[ti][64 * i + z];
                        acc[0] += ws * eval_f(&t.kind, &vals[0]);
                        if with1 {
                            acc[1] += ws * eval_f(&t.kind, &vals[1]);
                        }
                        for k in 2..=df {
                            acc[k] += ws * eval_f(&t.kind, &vals[k]);
                        }
                    }
                }
            }
            let e = ep[p];
            core::array::from_fn(|k| e * acc[k])
        })
        .reduce(|| [EF::ZERO; MAXJ], |a, b| core::array::from_fn(|k| a[k] + b[k]))
}

/// The folded layer after jj folds (rows_j x W cells): selection from the packed layer on the
/// support of real rows, zero elsewhere.
fn materialize(lay: &PLayer, vals_t: &[EF], jj: usize, rows_j: usize, nreal: usize) -> Vec<EF> {
    let mut vf = vec![EF::ZERO; rows_j * W];
    let ident = GMap { words: vec![], src: (0..WORDS).collect(), rot: vec![0; WORDS] };
    vf.par_chunks_mut(W).enumerate().for_each(|(p, out)| {
        if p % 16 >= nreal {
            return;
        }
        for w in 0..WORDS {
            if lay.support >> w & 1 == 0 {
                continue;
            }
            let pat = patterns(lay, &ident, w, p, rows_j, jj);
            for z in 0..64 {
                out[64 * w + z] = vals_t[pat[z] as usize];
            }
        }
    });
    vf
}

/// Main layer sumcheck from a packed layer; same messages as `main_prove_lm` on the unpacked
/// layer (dummy rows q >= nreal zero).
#[allow(clippy::too_many_arguments)]
pub fn main_prove_k10<T: crate::pcs::Fs>(spec: &Spec, maps: &[GMap], lay: &PLayer, rp: &[EF], mut w: Vec<Vec<EF>>, mut claim: EF, logp: usize, nreal: usize, tr: &mut T, msgs: &mut Vec<EF>) -> (Vec<EF>, Vec<EF>) {
    let nv = logp + LOGW;
    let ng = spec.gathers.len();
    let df = spec.deg_f();
    let mut pt = vec![EF::ZERO; nv];
    let mut rows = 1usize << logp;
    let logn = logp - 4;
    let jm = JMAT.load(Relaxed).min(logn).max(1);
    let mut ep = eq_table(&rp[..logp - 1]);
    let wc: Vec<Vec<EF>> = spec.terms.iter().enumerate().map(|(ti, t)| t.active.iter().map(|&s| w[ti][s as usize]).collect()).collect();
    let mut vals_t: Vec<EF> = vec![EF::ONE, -EF::ONE];
    let send = |q: &mut [EF; MAXJ], x: EF, claim: &mut EF, tr: &mut T, msgs: &mut Vec<EF>| -> EF {
        if x != EF::ZERO {
            q[1] = (*claim - (EF::ONE - x) * q[0]) * x.inverse();
        }
        let co = to_coeffs(&q[..=df]);
        let msg = &co[1..];
        tr.absorb_efs(msg);
        msgs.extend_from_slice(msg);
        let r = inject_r(tr.sample_ef(), x);
        *claim = next_a(*claim, x, msg, r);
        r
    };
    // Selection rounds (signature bits only, j < jm <= log2 N).
    let t0 = Instant::now();
    let hist_on = HIST.load(Relaxed);
    let mut planes: Option<Vec<(Vec<u64>, Vec<bool>)>> = if hist_on { Some(maps.iter().map(|m| gplanes(m, lay, rows)).collect()) } else { None };
    for j in 0..jm {
        let var = LOGW + rows.trailing_zeros() as usize - 1;
        let x = rp[var - LOGW];
        let with1 = x == EF::ZERO;
        // Terms whose histogram table fits take the histogram round; the others select.
        let hist: Vec<Option<Form>> = spec.terms.iter().map(|t| if hist_on { form(&t.kind, j) } else { None }).collect();
        let mask: Vec<bool> = hist.iter().map(|h| h.is_none()).collect();
        let mut q = if !mask.iter().any(|&m| m) {
            [EF::ZERO; MAXJ]
        } else if j == 0 {
            round0(spec, maps, lay, &ep, &wc, rows, nreal, with1, &mask)
        } else {
            round_sel(spec, maps, lay, &vals_t, j, &ep, &wc, rows, nreal, with1, &mask)
        };
        for (ti, t) in spec.terms.iter().enumerate() {
            if let Some(fm) = hist[ti] {
                let uses = t.kind.uses();
                let pl: Vec<&[u64]> = uses.iter().map(|&u| planes.as_ref().unwrap()[u].0.as_slice()).collect();
                let h = hist_term(&t.kind, fm, &pl, &planes.as_ref().unwrap()[uses[0]].1, &wc[ti], &vals_t, j, rows, rp, df, nreal);
                for k in 0..=df {
                    q[k] += h[k];
                }
            }
        }
        let r = send(&mut q, x, &mut claim, tr, msgs);
        pt[var] = r;
        vals_t = next_vals(&vals_t, r);
        if j + 1 >= HROUNDS {
            planes = None;
        }
        if ep.len() > 1 {
            halve_eq(&mut ep);
        }
        rows /= 2;
    }
    prof(1, t0);
    let t0 = Instant::now();
    let mut vf = materialize(lay, &vals_t, jm, rows, nreal);
    drop(vals_t);
    prof(2, t0);
    let t0 = Instant::now();
    let skip = |rows_now: usize, p: usize| rows_now > 16 && p % 16 >= nreal;
    while rows > 1 {
        let var = LOGW + rows.trailing_zeros() as usize - 1;
        let x = rp[var - LOGW];
        let hr = rows / 2;
        let with1 = x == EF::ZERO;
        let vfr = &vf;
        let pair = |p: usize| -> [EF; MAXJ] {
            let mut acc = [EF::ZERO; MAXJ];
            if skip(rows, p) {
                return acc;
            }
            let get = |row: usize, c: usize| -> EF { vfr[row * W + c] };
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
        let r = send(&mut q, x, &mut claim, tr, msgs);
        pt[var] = r;
        {
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
    prof(3, t0);
    (pt, vals)
}

// ---------------------------------------------------------------- wiring

/// For a packed layer: a[s] = sum_{p real} ep[p] in(p, s) = E - 2 sum_{p real, bit = 1} ep[p] on
/// the support, 0 elsewhere.
pub fn wiring_a_packed(l: &PLayer, ep: &[EF], rows: usize, nreal: usize) -> Vec<EF> {
    let chunk = (rows / 256).max(16);
    let (neg, e): (Vec<EF>, EF) = (0..rows.div_ceil(chunk))
        .into_par_iter()
        .map(|c| {
            let mut acc = vec![EF::ZERO; W];
            let mut esum = EF::ZERO;
            let mut tab = [EF::ZERO; 256];
            let (p0, p1) = (c * chunk, ((c + 1) * chunk).min(rows));
            // Groups of up to eight real rows; one table addition per cell per group.
            let real: Vec<usize> = (p0..p1).filter(|p| p % 16 < nreal).collect();
            for grp in real.chunks(8) {
                for (k, &p) in grp.iter().enumerate() {
                    esum += ep[p];
                    for msk in (1usize << k)..(2usize << k) {
                        tab[msk] = tab[msk & !(1 << k)] + ep[p];
                    }
                }
                for w in 0..WORDS {
                    if l.support >> w & 1 == 0 {
                        continue;
                    }
                    let mut lacc = [0u128; 8];
                    for (k, &p) in grp.iter().enumerate() {
                        or_plane(&mut lacc, l.bits[p * WORDS + w], k as u32);
                    }
                    let idx = lanes(&lacc);
                    for z in 0..64 {
                        if idx[z] != 0 {
                            acc[64 * w + z] += tab[idx[z] as usize];
                        }
                    }
                }
            }
            (acc, esum)
        })
        .reduce(
            || (vec![EF::ZERO; W], EF::ZERO),
            |(mut x, ex), (y, ey)| {
                x.iter_mut().zip(&y).for_each(|(a, b)| *a += *b);
                (x, ex + ey)
            },
        );
    (0..W).map(|s| if l.support >> (s / 64) & 1 == 1 { e - neg[s].double() } else { EF::ZERO }).collect()
}

/// Wiring sumcheck on a packed input layer; same messages as `wiring_prove`.
#[allow(clippy::too_many_arguments)]
pub fn wiring_prove_k10<T: crate::pcs::Fs>(spec: &Spec, vin: &PLayer, pt: &[EF], vals: &[EF], logp: usize, nreal: usize, tr: &mut T, msgs: &mut Vec<EF>) -> Vec<EF> {
    let t0 = Instant::now();
    let betas = tr.sample_efs(spec.gathers.len());
    let mut claim: EF = betas.iter().zip(vals).map(|(&b, &v)| b * v).sum();
    let ep = eq_table(&pt[LOGW..]);
    let rows = 1usize << logp;
    let mut a = wiring_a_packed(vin, &ep, rows, nreal);
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
    prof(4, t0);
    out
}

// ---------------------------------------------------------------- unit checks

/// Packed layers equal the field-valued layers of `apply` (64 random states as rows of one
/// signature block of 16 slots with `nreal` real slots), and the packed wiring sum equals the
/// field one. Returns (identical, cases).
pub fn selfcheck(seed: u64, nreal: usize) -> (usize, usize) {
    let mut st = seed | 1;
    let mut next = move || {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        st
    };
    let rows = 64usize;
    let sp = specs();
    let mut bits = vec![0u64; rows * WORDS];
    for p in 0..rows {
        if p % 16 < nreal {
            for l in 0..25 {
                bits[p * WORDS + l] = next();
            }
        }
    }
    let mut l = PLayer { bits, support: (1 << 25) - 1 };
    let mut f = unpack(&l, rows, nreal);
    let (mut same, mut total) = (0, 0);
    for s in &sp {
        let maps = gmaps(s);
        // Wiring sum on this layer at a random point.
        let pt: Vec<EF> = (0..6).map(|_| EF::from_basis_coefficients_fn(|_| F::from_u64(next()))).collect();
        let ep = eq_table(&pt);
        let a = wiring_a_packed(&l, &ep, rows, nreal);
        let b: Vec<EF> = (0..W).map(|c| (0..rows).map(|p| ep[p] * f[p * W + c]).sum()).collect();
        same += (a == b) as usize;
        total += 1;
        f = apply(s, &f, rows);
        // Dummy rows of the field layer are zero; compare real rows only.
        for p in 0..rows {
            if p % 16 >= nreal {
                f[p * W..(p + 1) * W].fill(F::ZERO);
            }
        }
        l = apply_packed(s, &maps, &l, rows);
        same += (unpack(&l, rows, nreal) == f) as usize;
        total += 1;
    }
    (same, total)
}

/// Exhaustive chi truth table under the declared encoding A = 1 - 2a (hostile gate): the layer
/// polynomial A (1 - (1 + B)(1 - C)/2) equals A (1 - B + C + BC) / 2 as a polynomial (checked at
/// random extension points) and, on the eight bit triples, the signed value of a ^ (!b & c).
/// Returns (passed, cases).
pub fn chi_truth_table(seed: u64) -> (usize, usize) {
    let (mut ok, mut tot) = (0, 0);
    let k = Kind::Chi([0, 1, 2]);
    let sg = |b: u64| if b == 1 { -F::ONE } else { F::ONE };
    for t in 0..8u64 {
        let (a, b, c) = (t & 1, t >> 1 & 1, t >> 2 & 1);
        let v = [sg(a), sg(b), sg(c)];
        ok += (eval_f(&k, &v) == sg(a ^ (!b & 1 & c))) as usize;
        tot += 1;
    }
    let mut st = seed | 1;
    let mut next = move || {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        st
    };
    for _ in 0..64 {
        let v: [EF; 3] = core::array::from_fn(|_| EF::from_basis_coefficients_fn(|_| F::from_u64(next())));
        let rhs = v[0] * (EF::ONE - v[1] + v[2] + v[1] * v[2]) * EF::from(half());
        ok += (eval_f(&k, &v) == rhs) as usize;
        tot += 1;
    }
    (ok, tot)
}

/// Every term of every layer vanishes on the field-zero vector (hostile gate: a skipped dummy
/// row pair contributes exactly zero). Returns (terms with f(0) = 0, terms).
pub fn zero_terms() -> (usize, usize) {
    let (mut ok, mut tot) = (0, 0);
    for s in specs() {
        for t in &s.terms {
            let z = [F::ZERO; MAXJ];
            ok += (eval_f(&t.kind, &z) == F::ZERO) as usize;
            tot += 1;
        }
    }
    (ok, tot)
}
