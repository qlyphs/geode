//! Fractional (LogUp) GKR over a binary tree of 2^d leaves (p, q).
//!
//! Layer k has 2^k fractions; node i of layer k combines children i and i + 2^k of layer k+1:
//! p = p_a q_b + p_b q_a, q = q_a q_b. The root must be 0 / (nonzero).
//! Each layer claim P_k(x) + lambda Q_k(x) is reduced by an eq-weighted sumcheck in which the
//! eq factor of the round variable is split off (Gruen). With x the claim coordinate of the
//! round variable and H(t) = a0 + a1 t + a2 t^2 the quadratic cofactor, the claim is
//! c = (1 - x) H(0) + x H(1) = a0 + x (a1 + a2). A round sends a1, a2; the verifier sets
//! a0 = c - x (a1 + a2), with no division, and the next claim is H(r) (normalized: the factor
//! eq1(x, r) is not multiplied in, so a challenge that zeroes it drops nothing). Then the four
//! child values are sent and a fresh beta extends the point by the new top variable.

use crate::field::{EF, eq_table};
use crate::pcs::Fs;
use p3_field::PrimeCharacteristicRing;
use rayon::prelude::*;

#[derive(Clone, Debug, PartialEq)]
pub struct Layer {
    pub rounds: Vec<[EF; 2]>,
    /// P(y*, 0), P(y*, 1), Q(y*, 0), Q(y*, 1).
    pub finals: [EF; 4],
}

#[derive(Clone, Debug, PartialEq)]
pub struct GkrProof {
    pub layers: Vec<Layer>,
}

impl GkrProof {
    pub fn num_elems(&self) -> usize {
        self.layers.iter().map(|l| 2 * l.rounds.len() + 4).sum()
    }
}

pub struct GkrOut {
    pub point: Vec<EF>,
    pub p: EF,
    pub q: EF,
}

const PAR: usize = 1 << 12;

/// The round message [a1, a2] of H from H(0), H(1), H(2) (the prover evaluates all three, so
/// it never divides by x either).
pub fn coeffs(h0: EF, h1: EF, h2: EF) -> [EF; 2] {
    let a2 = (h2 - h1.double() + h0).halve();
    [h1 - h0 - a2, a2]
}

/// Division-free normalized recurrence: a0 = c - x (a1 + a2), next claim H(r).
#[inline]
pub fn next_claim(claim: EF, x: EF, msg: [EF; 2], r: EF) -> EF {
    let [a1, a2] = msg;
    let a0 = claim - x * (a1 + a2);
    a0 + r * (a1 + r * a2)
}

/// Build all layers bottom-up. Returns layers[k] = (p, q) of size 2^k for k = 1..=d.
fn build_layers(p: Vec<EF>, q: Vec<EF>) -> Vec<(Vec<EF>, Vec<EF>)> {
    let d = p.len().trailing_zeros() as usize;
    let mut layers: Vec<(Vec<EF>, Vec<EF>)> = Vec::with_capacity(d + 1);
    layers.push((p, q));
    for _ in 0..d - 1 {
        let (cp, cq) = layers.last().unwrap();
        let h = cp.len() / 2;
        let mut np = vec![EF::ZERO; h];
        let mut nq = vec![EF::ZERO; h];
        np.par_iter_mut().zip(nq.par_iter_mut()).enumerate().with_min_len(PAR).for_each(|(i, (op, oq))| {
            let (pa, pb, qa, qb) = (cp[i], cp[i + h], cq[i], cq[i + h]);
            *op = pa * qb + pb * qa;
            *oq = qa * qb;
        });
        layers.push((np, nq));
    }
    layers.reverse();
    // layers[0] has 2 entries (layer 1), layers[d-1] is the leaves (layer d).
    layers
}

fn fold(v: &mut Vec<EF>, r: EF) {
    let h = v.len() / 2;
    let (lo, hi) = v.split_at_mut(h);
    lo.par_iter_mut().zip(hi.par_iter()).with_min_len(PAR).for_each(|(a, &b)| *a += r * (b - *a));
    v.truncate(h);
}

pub fn prove<T: Fs>(p_leaves: Vec<EF>, q_leaves: Vec<EF>, tr: &mut T) -> (GkrProof, GkrOut) {
    let d = p_leaves.len().trailing_zeros() as usize;
    assert!(d >= 2 && p_leaves.len() == 1 << d);
    let mut layers = build_layers(p_leaves, q_leaves);
    let mut proof = Vec::with_capacity(d);
    // Layer 1: send its two fractions; the root is their sum.
    let (p1, q1) = std::mem::take(&mut layers[0]);
    let finals = [p1[0], p1[1], q1[0], q1[1]];
    tr.absorb_efs(&finals);
    proof.push(Layer { rounds: vec![], finals });
    let beta = tr.sample_round(None);
    let mut x = vec![beta];
    let mut cp = p1[0] + beta * (p1[1] - p1[0]);
    let mut cq = q1[0] + beta * (q1[1] - q1[0]);
    for k in 1..d {
        // Claim on layer k at x (k vars); children are layer k+1 = layers[k].
        let lambda = tr.sample_ef();
        let (pk1, qk1) = std::mem::take(&mut layers[k]);
        let half = 1usize << k;
        let mut pa = pk1;
        let pb = pa.split_off(half);
        let mut qa = qk1;
        let qb = qa.split_off(half);
        let (mut pb, mut qb) = (pb, qb);
        let mut eq = if k >= 2 { eq_table(&x[..k - 1]) } else { vec![EF::ONE] };
        let mut claim = cp + lambda * cq;
        let mut rs = vec![EF::ZERO; k];
        let mut rounds = Vec::with_capacity(k);
        for m in (1..=k).rev() {
            let h = 1usize << (m - 1);
            let (h0, h1, h2) = (0..h)
                .into_par_iter()
                .with_min_len(PAR)
                .map(|i| {
                    let (a0, a1, b0, b1) = (pa[i], pa[i + h], pb[i], pb[i + h]);
                    let (c0_, c1_, d0, d1) = (qa[i], qa[i + h], qb[i], qb[i + h]);
                    let a2 = a1.double() - a0;
                    let b2 = b1.double() - b0;
                    let cc2 = c1_.double() - c0_;
                    let d2 = d1.double() - d0;
                    let g0 = a0 * d0 + c0_ * (b0 + lambda * d0);
                    let g1 = a1 * d1 + c1_ * (b1 + lambda * d1);
                    let g2 = a2 * d2 + cc2 * (b2 + lambda * d2);
                    (eq[i] * g0, eq[i] * g1, eq[i] * g2)
                })
                .reduce(|| (EF::ZERO, EF::ZERO, EF::ZERO), |a, b| (a.0 + b.0, a.1 + b.1, a.2 + b.2));
            let xt = x[m - 1];
            debug_assert_eq!(claim, (EF::ONE - xt) * h0 + xt * h1);
            let msg = coeffs(h0, h1, h2);
            tr.absorb_efs(&msg);
            rounds.push(msg);
            let r = tr.sample_round(Some(xt));
            claim = next_claim(claim, xt, msg, r);
            rs[m - 1] = r;
            fold(&mut pa, r);
            fold(&mut pb, r);
            fold(&mut qa, r);
            fold(&mut qb, r);
            if m >= 2 {
                let hh = eq.len() / 2;
                let (lo, hi) = eq.split_at_mut(hh);
                lo.par_iter_mut().zip(hi.par_iter()).with_min_len(PAR).for_each(|(a, &b)| *a += b);
                eq.truncate(hh);
            }
        }
        let finals = [pa[0], pb[0], qa[0], qb[0]];
        debug_assert_eq!(claim, finals[0] * finals[3] + finals[1] * finals[2] + lambda * finals[2] * finals[3]);
        tr.absorb_efs(&finals);
        proof.push(Layer { rounds, finals });
        let beta = tr.sample_round(None);
        cp = finals[0] + beta * (finals[1] - finals[0]);
        cq = finals[2] + beta * (finals[3] - finals[2]);
        x = rs;
        x.push(beta);
    }
    (GkrProof { layers: proof }, GkrOut { point: x, p: cp, q: cq })
}

#[derive(Debug)]
pub enum GkrError {
    Shape,
    RootNumeratorNonzero,
    RootDenominatorZero,
    LayerMismatch(usize),
}

pub fn verify<T: Fs>(proof: &GkrProof, d: usize, tr: &mut T) -> Result<GkrOut, GkrError> {
    if proof.layers.len() != d {
        return Err(GkrError::Shape);
    }
    let l0 = &proof.layers[0];
    if !l0.rounds.is_empty() {
        return Err(GkrError::Shape);
    }
    let [pa, pb, qa, qb] = l0.finals;
    tr.absorb_efs(&l0.finals);
    if pa * qb + pb * qa != EF::ZERO {
        return Err(GkrError::RootNumeratorNonzero);
    }
    if qa * qb == EF::ZERO {
        return Err(GkrError::RootDenominatorZero);
    }
    let beta = tr.sample_round(None);
    let mut x = vec![beta];
    let mut cp = pa + beta * (pb - pa);
    let mut cq = qa + beta * (qb - qa);
    for k in 1..d {
        let layer = &proof.layers[k];
        if layer.rounds.len() != k {
            return Err(GkrError::Shape);
        }
        let lambda = tr.sample_ef();
        let mut claim = cp + lambda * cq;
        let mut rs = vec![EF::ZERO; k];
        for (idx, m) in (1..=k).rev().enumerate() {
            let msg = layer.rounds[idx];
            tr.absorb_efs(&msg);
            let xt = x[m - 1];
            let r = tr.sample_round(Some(xt));
            claim = next_claim(claim, xt, msg, r);
            rs[m - 1] = r;
        }
        let [pa, pb, qa, qb] = layer.finals;
        if claim != pa * qb + pb * qa + lambda * qa * qb {
            return Err(GkrError::LayerMismatch(k));
        }
        tr.absorb_efs(&layer.finals);
        let beta = tr.sample_round(None);
        cp = pa + beta * (pb - pa);
        cq = qa + beta * (qb - qa);
        x = rs;
        x.push(beta);
    }
    Ok(GkrOut { point: x, p: cp, q: cq })
}
