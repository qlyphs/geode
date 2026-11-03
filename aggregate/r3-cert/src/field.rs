//! Field types (Goldilocks and its quintic extension), conversions, equality tables and
//! Lagrange interpolation on small integer nodes.

use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField64};
use p3_goldilocks::Goldilocks;
use rayon::prelude::*;

pub type F = Goldilocks;
pub type EF = BinomialExtensionField<F, 5>;

pub const P: u64 = 0xffff_ffff_0000_0001;

#[inline(always)]
pub fn fi(x: i64) -> F {
    if x >= 0 { F::from_u64(x as u64) } else { -F::from_u64(x.unsigned_abs()) }
}

#[inline(always)]
pub fn efb(x: F) -> EF {
    EF::from(x)
}

pub fn ef_to_bytes(x: &EF, out: &mut Vec<u8>) {
    for c in <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(x) {
        out.extend_from_slice(&c.as_canonical_u64().to_le_bytes());
    }
}

/// Canonical decoding: rejects any coordinate >= p.
pub fn ef_from_bytes(b: &[u8]) -> Option<EF> {
    if b.len() != 40 {
        return None;
    }
    let mut cs = [F::ZERO; 5];
    for (i, c) in cs.iter_mut().enumerate() {
        let v = u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap());
        if v >= P {
            return None;
        }
        *c = F::from_u64(v);
    }
    EF::from_basis_coefficients_slice(&cs)
}

/// eq1(x, b) for a Boolean b, as a function of the variable value X: (1-x)(1-X) + xX.
#[inline(always)]
pub fn eq1(x: EF, y: EF) -> EF {
    x * y + (EF::ONE - x) * (EF::ONE - y)
}

/// eq(point, b) for every b in {0,1}^n, variable t bound to bit t of b (LSB first).
pub fn eq_table(point: &[EF]) -> Vec<EF> {
    eq_table_scaled(point, EF::ONE)
}

pub fn eq_table_scaled(point: &[EF], scale: EF) -> Vec<EF> {
    let n = point.len();
    let mut t = Vec::with_capacity(1 << n);
    t.push(scale);
    // Process the top variable first so that the last processed one lands on bit 0.
    for v in (0..n).rev() {
        let p = point[v];
        let old = std::mem::take(&mut t);
        let mut new = vec![EF::ZERO; old.len() * 2];
        if old.len() >= 1 << 14 {
            new.par_chunks_mut(2).zip(old.par_iter()).for_each(|(o, &e)| {
                let hi = e * p;
                o[0] = e - hi;
                o[1] = hi;
            });
        } else {
            for (o, &e) in new.chunks_mut(2).zip(old.iter()) {
                let hi = e * p;
                o[0] = e - hi;
                o[1] = hi;
            }
        }
        t = new;
    }
    t
}

/// Evaluate eq(point, b) at one Boolean vertex.
pub fn eq_at(point: &[EF], b: usize) -> EF {
    let mut r = EF::ONE;
    for (t, &p) in point.iter().enumerate() {
        r *= if (b >> t) & 1 == 1 { p } else { EF::ONE - p };
    }
    r
}

/// Product over all t of eq1(a_t, b_t) for two field points.
pub fn eq_pts(a: &[EF], b: &[EF]) -> EF {
    a.iter().zip(b).fold(EF::ONE, |acc, (&x, &y)| acc * eq1(x, y))
}

/// The value at r of the polynomial of degree < vals.len() through (i, vals[i]), i = 0, 1, ...
pub fn lagrange(vals: &[EF], r: EF) -> EF {
    let n = vals.len();
    let mut acc = EF::ZERO;
    for i in 0..n {
        let mut num = EF::ONE;
        let mut den = F::ONE;
        for j in 0..n {
            if j != i {
                num *= r - efb(F::from_usize(j));
                den *= fi(i as i64 - j as i64);
            }
        }
        acc += vals[i] * num * den.inverse();
    }
    acc
}

/// Multilinear evaluation of a dense table at a point (LSB-first convention).
///
/// The eq table is used as the tensor of its low and high halves, eq(b) = lo(b mod 2^s)
/// hi(b / 2^s), so no table of the full size is built; the value is the same field element
/// (the MLE at the point is one element, and the sum is exact).
pub fn mle_eval<T: Copy + Send + Sync>(vals: &[T], point: &[EF]) -> EF
where
    EF: core::ops::Mul<T, Output = EF>,
{
    let n = point.len();
    assert_eq!(vals.len(), 1usize << n);
    let s = n.min(12);
    let lo = eq_table(&point[..s]);
    let hi = eq_table(&point[s..]);
    vals.par_chunks(1usize << s)
        .zip(hi.par_iter())
        .map(|(row, &h)| {
            let inner: EF = lo.iter().zip(row.iter()).map(|(&e, &v)| e * v).sum();
            <EF as core::ops::Mul<EF>>::mul(h, inner)
        })
        .sum()
}

/// `mle_eval` of the table b -> g(b) of 2^point.len() entries, without storing it.
pub fn mle_eval_gen<T: Copy + Send + Sync>(g: &(dyn Fn(usize) -> T + Sync), point: &[EF]) -> EF
where
    EF: core::ops::Mul<T, Output = EF>,
{
    let n = point.len();
    let s = n.min(12);
    let lo = eq_table(&point[..s]);
    let hi = eq_table(&point[s..]);
    hi.par_iter()
        .enumerate()
        .map(|(h, &hv)| {
            let inner: EF = lo.iter().enumerate().map(|(l, &e)| e * g((h << s) | l)).sum();
            <EF as core::ops::Mul<EF>>::mul(hv, inner)
        })
        .sum()
}

/// The previous dense-table evaluation (tests compare it with `mle_eval`).
pub fn mle_eval_dense<T: Copy + Send + Sync>(vals: &[T], point: &[EF]) -> EF
where
    EF: core::ops::Mul<T, Output = EF>,
{
    let eq = eq_table(point);
    eq.par_iter().zip(vals.par_iter()).map(|(&e, &v)| e * v).sum()
}

/// Goldilocks reduction of a 128-bit value (result < 2^64, possibly not canonical).
#[inline(always)]
fn reduce128(x: u128) -> u64 {
    const EPS: u64 = 0xffff_ffff;
    let (lo, hi) = (x as u64, (x >> 64) as u64);
    let (hh, hl) = (hi >> 32, hi & EPS);
    let (mut t0, borrow) = lo.overflowing_sub(hh);
    if borrow {
        t0 = t0.wrapping_sub(EPS);
    }
    let t1 = hl * EPS;
    let (r, carry) = t0.overflowing_add(t1);
    r.wrapping_add(EPS * carry as u64)
}

/// Quintic extension multiplication (X^5 = 3) with one reduction per output coefficient: the
/// five products of each coefficient are summed in 128 bits plus a carry word, then reduced
/// (2^128 = -2^32 mod p). Same result as the p3 multiplication (checked by `fmul_selftest`).
#[inline(always)]
pub fn fmul(a: EF, b: EF) -> EF {
    let x = <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&a);
    let y = <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&b);
    let xv: [u64; 5] = core::array::from_fn(|i| x[i].as_canonical_u64());
    let yv: [u64; 5] = core::array::from_fn(|i| y[i].as_canonical_u64());
    let three = F::from_u64(3);
    let y3: [u64; 5] = core::array::from_fn(|i| (y[i] * three).as_canonical_u64());
    let mut out = [F::ZERO; 5];
    for (k, o) in out.iter_mut().enumerate() {
        let mut lo: u128 = 0;
        let mut carry: u64 = 0;
        for i in 0..5 {
            let yy = if i <= k { yv[k - i] } else { y3[k + 5 - i] };
            let (s, c) = lo.overflowing_add(xv[i] as u128 * yy as u128);
            lo = s;
            carry += c as u64;
        }
        *o = F::from_u64(reduce128(lo)) - F::from_u64(carry << 32);
    }
    EF::from_basis_coefficients_fn(|i| out[i])
}

/// Checks fmul against the p3 multiplication on pseudo-random inputs and edge values.
pub fn fmul_selftest() -> bool {
    let mut s = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let edge = [0u64, 1, 2, P - 1, P - 2, 0xffff_ffff, 1 << 32, P >> 1];
    (0..200_000).all(|t| {
        let mut c = || if t % 7 == 0 { F::from_u64(edge[(next() % 8) as usize]) } else { F::from_u64(next()) };
        let a = EF::from_basis_coefficients_fn(|_| c());
        let b = EF::from_basis_coefficients_fn(|_| c());
        fmul(a, b) == a * b
    })
}
