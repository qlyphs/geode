//! Witness generation (round 3 section 2.4): per signature, z and the public u become the
//! committed cells X, Y, S and the shared 2^20-entry multiplicity table m.
//!
//! Cell b = i * 2048 + p * 256 + k. X: p < 7 holds z_p[k] + 524167, p = 7 is ignored padding.
//! Y, S: p is the K index, e = ctr(A z - c 2^13 t1 - a u) = Y + start(u, S).

use crate::field::{F, fi};
use crate::mlnat::{self, K, L, N, Ntt, Record, SigPublic, ctr};
use crate::region::{self, T, XK, XOFF};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use rayon::prelude::*;

pub const SLOTS: usize = 2048;

/// What a signer hands to the prover for one record: the response z and the public u.
#[derive(Clone)]
pub struct SigInput {
    pub z: Vec<i64>,
    pub u: Vec<u8>,
}

/// Which constraints a witness violates, counted directly on the integers (diagnostics only).
#[derive(Default, Debug, Clone)]
pub struct Violations {
    pub z_out_of_range: usize,
    pub e_out_of_region: usize,
    pub sigs_over_omega: usize,
    pub max_hints: usize,
}

#[derive(Clone)]
pub struct Witness {
    pub n: usize,
    pub x: Vec<F>,
    pub y: Vec<F>,
    pub s: Vec<F>,
    /// Integer z (0 on padding) and e, for the integer lifts.
    pub zi: Vec<i32>,
    pub ei: Vec<i32>,
    /// Per-cell class of u (0: u = 0, 1: u = 15, 2: other), for the Y cells.
    pub class: Vec<u8>,
    pub m: Vec<F>,
    /// True per-signature hint counts sum_j S^2.
    pub counts: Vec<u8>,
    pub viol: Violations,
}

/// The FIPS path for an honest raw signature: decode, w'_approx, u = UseHint(h, w').
pub fn input_from_raw(ntt: &Ntt, rec: &Record, sig: &[u8]) -> SigInput {
    let (ct, z, h) = mlnat::decode_sig(sig).expect("signature decodes");
    let (rho, _) = mlnat::decode_pk(&rec.pk);
    let a_hat = mlnat::expand_a(&rho);
    let b = mlnat::b_of(ntt, &rec.pk, &ct);
    let w = mlnat::w_approx(ntt, &a_hat, &z, &b);
    let u = (0..K * N).map(|t| mlnat::use_hint(h[t], w[t]) as u8).collect();
    SigInput { z, u }
}

/// Build the witness and the public data. All signatures are processed in parallel.
pub fn build(ntt: &Ntt, records: &[Record], inputs: &[SigInput]) -> (Witness, Vec<SigPublic>) {
    let n = records.len();
    let d = n * SLOTS;
    let per: Vec<(SigPublic, Vec<i32>, Vec<i32>)> = records
        .par_iter()
        .zip(inputs.par_iter())
        .map(|(rec, inp)| {
            let pubd = mlnat::derive_public(ntt, rec, &inp.u);
            // w - a u where w = A z - b: derive_public's bu already holds b + a u.
            let w = mlnat::w_approx(ntt, &pubd.a_hat, &inp.z, &pubd.bu);
            let e: Vec<i32> = w.iter().map(|&v| ctr(v) as i32).collect();
            let z: Vec<i32> = inp.z.iter().map(|&v| v as i32).collect();
            (pubd, z, e)
        })
        .collect();
    let mut x = vec![F::ZERO; d];
    let mut y = vec![F::ZERO; d];
    let mut s = vec![F::ZERO; d];
    let mut zi = vec![0i32; d];
    let mut ei = vec![0i32; d];
    let mut class = vec![0u8; d];
    let mut counts = vec![0u8; n];
    let mut viol = Violations::default();
    for (i, ((_, z, e), inp)) in per.iter().zip(inputs).enumerate() {
        let base = i * SLOTS;
        for l in 0..L {
            for k in 0..N {
                let zz = z[l * N + k] as i64;
                if zz.abs() >= mlnat::ZB {
                    viol.z_out_of_range += 1;
                }
                x[base + l * N + k] = fi(zz + XOFF);
                zi[base + l * N + k] = zz as i32;
            }
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
        }
        viol.max_hints = viol.max_hints.max(hints);
        if hints > mlnat::OMEGA {
            viol.sigs_over_omega += 1;
        }
        counts[i] = hints.min(255) as u8;
    }
    let m = multiplicities(&x, &y, &s, &class, n);
    let pubs = per.into_iter().map(|(p, _, _)| p).collect();
    (Witness { n, x, y, s, zi, ei, class, m, counts, viol }, pubs)
}

pub fn as_int(v: F) -> i64 {
    let u = v.as_canonical_u64();
    if u > crate::field::P / 2 { -((crate::field::P - u) as i64) } else { u as i64 }
}

/// Counts of each table value among the four query families; values outside the table are
/// not counted (an honest prover on a broken witness). K(u, S) is evaluated with the field
/// coefficients, so a non-integer selector (soundness tests) is counted as the lookup sees it.
pub fn multiplicities(x: &[F], y: &[F], s: &[F], class: &[u8], n: usize) -> Vec<F> {
    let co = region::all_coeffs();
    let mut cnt = vec![0u64; T];
    let mut add = |v: i64| {
        if (0..T as i64).contains(&v) {
            cnt[v as usize] += 1;
        }
    };
    for i in 0..n {
        for t in 0..SLOTS {
            let b = i * SLOTS + t;
            if t < L * N {
                let xv = as_int(x[b]);
                add(xv);
                add(XK - xv);
            }
            let yv = as_int(y[b]);
            let c = &co[class[b] as usize];
            let kv = as_int(c.k[0] + (c.k[1] + c.k[2] * s[b]) * s[b]);
            add(yv);
            add(kv - yv);
        }
    }
    cnt.into_iter().map(F::from_u64).collect()
}

/// Rebuild the canonical FIPS signature of record i from the committed witness and public u.
pub fn reconstruct(w: &Witness, rec: &Record, u: &[u8], i: usize) -> Option<Vec<u8>> {
    let base = i * SLOTS;
    let z: Vec<i64> = (0..L * N).map(|t| as_int(w.x[base + t]) - XOFF).collect();
    let h: Vec<bool> = (0..K * N).map(|t| as_int(w.s[base + t]) != 0).collect();
    let tr = mlnat::tr_of(&rec.pk);
    let mu = mlnat::mu_of(&tr, &rec.ctx, &rec.msg);
    let ct = mlnat::c_tilde_of(&mu, &mlnat::w1_encode(u));
    mlnat::encode_sig(&ct, &z, &h)
}
