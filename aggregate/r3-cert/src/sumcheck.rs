//! The degree-four master sumcheck (round 3 section 2.5) and the degree-two table link.
//!
//! Master: sum_b F(b) with
//!   F = X(Z + C_X X) + Y(E + C_Y Y + S(D1 + D2 S)) + S(B1 + S(B2 + B3 S)),
//! three committed columns X, Y, S and nine public columns. A round sends h(0), h(2), h(3), h(4).
//! Table: sum_j eqT(j) (A(j) m_e(j) + B(j) m_o(j)); a round sends h(0), h(2).
//! Both bind the top variable first; the returned point is indexed by variable (LSB first).

use crate::field::{EF, F, lagrange};
use crate::pcs::Fs;
use p3_field::{Algebra, Field, PrimeCharacteristicRing};
use rayon::prelude::*;

const PAR: usize = 1 << 11;

/// Public columns in the order Z, CX, E, CY, D1, D2, B1, B2, B3.
pub type Pub = [Vec<EF>; 9];

#[inline(always)]
fn master_f<T: Copy>(x: T, y: T, s: T, p: &[EF; 9]) -> EF
where
    EF: Algebra<T>,
{
    let [z, cx, e, cy, d1, d2, b1, b2, b3] = *p;
    (z + cx * x) * x + (e + cy * y + (d1 + d2 * s) * s) * y + (b1 + (b2 + b3 * s) * s) * s
}

/// One master round over columns of size 2^m: h(0), h(2), h(3), h(4).
fn master_round<T: Field>(w: [&[T]; 3], p: &Pub) -> [EF; 4]
where
    EF: Algebra<T>,
{
    let h = w[0].len() / 2;
    (0..h)
        .into_par_iter()
        .with_min_len(PAR)
        .map(|i| {
            let mut wv = [[T::ZERO; 4]; 3];
            for c in 0..3 {
                let (a, b) = (w[c][i], w[c][i + h]);
                let dlt = b - a;
                let v2 = b + dlt;
                let v3 = v2 + dlt;
                wv[c] = [a, v2, v3, v3 + dlt];
            }
            let mut pv = [[EF::ZERO; 9]; 4];
            for c in 0..9 {
                let (a, b) = (p[c][i], p[c][i + h]);
                let dlt = b - a;
                let v2 = b + dlt;
                let v3 = v2 + dlt;
                pv[0][c] = a;
                pv[1][c] = v2;
                pv[2][c] = v3;
                pv[3][c] = v3 + dlt;
            }
            let mut out = [EF::ZERO; 4];
            for t in 0..4 {
                out[t] = master_f(wv[0][t], wv[1][t], wv[2][t], &pv[t]);
            }
            out
        })
        .reduce(|| [EF::ZERO; 4], |a, b| [a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3]])
}

fn fold_ext(v: &mut Vec<EF>, r: EF) {
    let h = v.len() / 2;
    let (lo, hi) = v.split_at_mut(h);
    lo.par_iter_mut().zip(hi.par_iter()).with_min_len(PAR).for_each(|(a, &b)| *a += r * (b - *a));
    v.truncate(h);
}

fn fold_base(v: &[F], r: EF) -> Vec<EF> {
    let h = v.len() / 2;
    (0..h).into_par_iter().with_min_len(PAR).map(|i| r * (v[i + h] - v[i]) + v[i]).collect()
}

pub struct MasterOut {
    pub rounds: Vec<[EF; 4]>,
    pub point: Vec<EF>,
    pub claim: EF,
    pub evals: [EF; 3],
}

/// Prove sum_b F(b) = claim. The witness columns are borrowed (base field), the public columns
/// are consumed and folded in place.
pub fn master_prove<T: Fs>(x: &[F], y: &[F], s: &[F], mut p: Pub, claim: EF, tr: &mut T) -> MasterOut {
    let nv = x.len().trailing_zeros() as usize;
    let mut claim = claim;
    let mut point = vec![EF::ZERO; nv];
    let mut rounds = Vec::with_capacity(nv);
    // Round 1 on the base-field witness.
    let h = master_round::<F>([x, y, s], &p);
    let mut step = |h: [EF; 4], claim: &mut EF, tr: &mut T| -> EF {
        tr.absorb_efs(&h);
        let r = tr.sample_ef();
        let h1 = *claim - h[0];
        *claim = lagrange(&[h[0], h1, h[1], h[2], h[3]], r);
        r
    };
    let r = step(h, &mut claim, tr);
    rounds.push(h);
    point[nv - 1] = r;
    let mut wx = fold_base(x, r);
    let mut wy = fold_base(y, r);
    let mut ws = fold_base(s, r);
    p.iter_mut().for_each(|c| fold_ext(c, r));
    for v in (0..nv - 1).rev() {
        let h = master_round::<EF>([&wx, &wy, &ws], &p);
        let r = step(h, &mut claim, tr);
        rounds.push(h);
        point[v] = r;
        fold_ext(&mut wx, r);
        fold_ext(&mut wy, r);
        fold_ext(&mut ws, r);
        p.iter_mut().for_each(|c| fold_ext(c, r));
    }
    let pv: [EF; 9] = core::array::from_fn(|c| p[c][0]);
    debug_assert_eq!(claim, master_f(wx[0], wy[0], ws[0], &pv));
    MasterOut { rounds, point, claim, evals: [wx[0], wy[0], ws[0]] }
}

/// Replay the master rounds: returns (point, final claim).
pub fn master_verify<T: Fs>(rounds: &[[EF; 4]], nv: usize, claim: EF, tr: &mut T) -> Option<(Vec<EF>, EF)> {
    if rounds.len() != nv {
        return None;
    }
    let mut claim = claim;
    let mut point = vec![EF::ZERO; nv];
    for (idx, h) in rounds.iter().enumerate() {
        tr.absorb_efs(h);
        let r = tr.sample_ef();
        let h1 = claim - h[0];
        claim = lagrange(&[h[0], h1, h[1], h[2], h[3]], r);
        point[nv - 1 - idx] = r;
    }
    Some((point, claim))
}

pub fn master_final(x: EF, y: EF, s: EF, p: &[EF; 9]) -> EF {
    master_f(x, y, s, p)
}

pub struct TableOut {
    pub rounds: Vec<[EF; 2]>,
    pub point: Vec<EF>,
    pub evals: [EF; 2],
}

/// Prove sum_j eq(rt, j) (A(j) me(j) + B(j) mo(j)) = claim. The summand has degree 3 per
/// variable; the eq factor of the round variable is split off as in the GKR layers, and a round
/// sends the coefficients [a1, a2] of the quadratic cofactor (division-free, see gkr.rs).
pub fn table_prove<T: Fs>(rt: &[EF], mut a: Vec<EF>, mut b: Vec<EF>, me: &[F], mo: &[F], claim: EF, tr: &mut T) -> TableOut {
    let nv = rt.len();
    let mut me: Vec<EF> = me.iter().map(|&v| EF::from(v)).collect();
    let mut mo: Vec<EF> = mo.iter().map(|&v| EF::from(v)).collect();
    let mut eq = crate::field::eq_table(&rt[..nv - 1]);
    let mut claim = claim;
    let mut point = vec![EF::ZERO; nv];
    let mut rounds = Vec::with_capacity(nv);
    for v in (0..nv).rev() {
        let h = a.len() / 2;
        let (c0, c1, c2) = (0..h)
            .into_par_iter()
            .with_min_len(PAR)
            .map(|i| {
                let a2 = a[i + h].double() - a[i];
                let b2 = b[i + h].double() - b[i];
                let m2 = me[i + h].double() - me[i];
                let o2 = mo[i + h].double() - mo[i];
                (eq[i] * (a[i] * me[i] + b[i] * mo[i]), eq[i] * (a[i + h] * me[i + h] + b[i + h] * mo[i + h]), eq[i] * (a2 * m2 + b2 * o2))
            })
            .reduce(|| (EF::ZERO, EF::ZERO, EF::ZERO), |x, y| (x.0 + y.0, x.1 + y.1, x.2 + y.2));
        let xt = rt[v];
        debug_assert_eq!(claim, (EF::ONE - xt) * c0 + xt * c1);
        let msg = crate::gkr::coeffs(c0, c1, c2);
        tr.absorb_efs(&msg);
        let r = tr.sample_round(Some(xt));
        claim = crate::gkr::next_claim(claim, xt, msg, r);
        rounds.push(msg);
        point[v] = r;
        for c in [&mut a, &mut b, &mut me, &mut mo] {
            fold_ext(c, r);
        }
        if v >= 1 {
            let hh = eq.len() / 2;
            let (lo, hi) = eq.split_at_mut(hh);
            lo.par_iter_mut().zip(hi.par_iter()).for_each(|(x, &y)| *x += y);
            eq.truncate(hh);
        }
    }
    debug_assert_eq!(claim, a[0] * me[0] + b[0] * mo[0]);
    TableOut { rounds, point, evals: [me[0], mo[0]] }
}

/// Replay the table rounds. Returns the point and the normalized final claim, which must equal
/// A(s) me(s) + B(s) mo(s).
pub fn table_verify<T: Fs>(rounds: &[[EF; 2]], rt: &[EF], claim: EF, tr: &mut T) -> Option<(Vec<EF>, EF)> {
    let nv = rt.len();
    if rounds.len() != nv {
        return None;
    }
    let mut claim = claim;
    let mut point = vec![EF::ZERO; nv];
    for (idx, h) in rounds.iter().enumerate() {
        tr.absorb_efs(h);
        let v = nv - 1 - idx;
        let xt = rt[v];
        let r = tr.sample_round(Some(xt));
        claim = crate::gkr::next_claim(claim, xt, *h, r);
        point[v] = r;
    }
    Some((point, claim))
}
