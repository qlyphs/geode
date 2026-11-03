//! A relaxed ML-DSA-87 signer for the soundness tests. It produces (z, u) pairs that satisfy the
//! exact modular relation A z - c 2^13 t1 - a u = e (mod q) with c = SampleInBall(H(mu || u)),
//! and break exactly one bound on purpose: one response coefficient at +-524168, one residual
//! outside its region, or 76 hints. Keys use the public-key format (rho, t1) with s1, s2 drawn
//! uniformly from [-2, 2]; nothing else of KeyGen matters to the verifier.

use crate::mlnat::{self, A2, GAMMA1, K, L, N, Ntt, Poly, Q, Record, ctr, modq, red, shake256};
use crate::region;
use crate::witness::SigInput;
use rayon::prelude::*;
use sha3::Shake256;
use sha3::digest::{ExtendableOutput, Update, XofReader};

pub struct RKey {
    pub pk: Vec<u8>,
    a_hat: Vec<Poly>,
    s1_hat: Vec<Poly>,
    tr: [u8; 64],
}

fn stream(seed: &[u8], label: &[u8], idx: u64) -> impl XofReader {
    let mut h = Shake256::default();
    h.update(b"r3-cert/relaxed/");
    h.update(label);
    h.update(seed);
    h.update(&idx.to_le_bytes());
    h.finalize_xof()
}

fn small(rd: &mut impl XofReader, n: usize) -> Vec<i64> {
    let mut v = Vec::with_capacity(n);
    let mut b = [0u8; 1];
    while v.len() < n {
        rd.read(&mut b);
        if b[0] < 250 {
            v.push((b[0] % 5) as i64 - 2);
        }
    }
    v
}

pub fn keygen(ntt: &Ntt, seed: &[u8]) -> RKey {
    let mut rho = [0u8; 32];
    shake256(&[b"r3-cert/relaxed/rho", seed], &mut rho);
    let a_hat = mlnat::expand_a(&rho);
    let s1 = small(&mut stream(seed, b"s1", 0), L * N);
    let s2 = small(&mut stream(seed, b"s2", 0), K * N);
    let s1_hat: Vec<Poly> = (0..L)
        .map(|l| {
            let mut p = [0u32; N];
            for j in 0..N {
                p[j] = modq(s1[l * N + j]);
            }
            ntt.fwd(&mut p);
            p
        })
        .collect();
    let mut t1 = vec![0u32; K * N];
    for k in 0..K {
        let mut acc = [0u32; N];
        for j in 0..N {
            let mut s = 0u64;
            for l in 0..L {
                s += a_hat[k * L + l][j] as u64 * s1_hat[l][j] as u64;
            }
            acc[j] = red(s);
        }
        ntt.inv(&mut acc);
        for j in 0..N {
            let t = modq(acc[j] as i64 + s2[k * N + j]) as i64;
            // Power2Round: t0 = t mod+- 2^13, t1 = (t - t0) / 2^13.
            let m = t & 8191;
            let t0 = if m > 4096 { m - 8192 } else { m };
            t1[k * N + j] = ((t - t0) >> 13) as u32;
        }
    }
    let pk = mlnat::encode_pk(&rho, &t1);
    let tr = mlnat::tr_of(&pk);
    RKey { pk, a_hat, s1_hat, tr }
}

#[derive(Clone, Copy, Debug)]
pub enum Mode {
    /// Everything within the FIPS bounds (control).
    Valid,
    /// Exactly one response coefficient equal to sign * 524168.
    ZEdge(i64),
    /// Exactly one residual outside its region (u moved by 2 at one coefficient).
    ResidualOut,
    /// Exactly this many hints, everything else valid.
    Hints(usize),
}

pub struct Signed {
    pub input: SigInput,
    pub attempts: u64,
    pub hints: usize,
    pub max_abs_z: i64,
    pub out_of_region: usize,
}

fn try_sign(ntt: &Ntt, key: &RKey, mu: &[u8; 64], mode: Mode, seed: &[u8], attempt: u64, bumps: usize) -> Option<Signed> {
    let mut rd = stream(seed, b"y", attempt);
    let mut y = vec![0i64; L * N];
    let mut b3 = [0u8; 3];
    for v in y.iter_mut() {
        rd.read(&mut b3);
        let x = (b3[0] as i64 | (b3[1] as i64) << 8 | (b3[2] as i64) << 16) & 0xf_ffff;
        *v = GAMMA1 - x;
    }
    let w = mlnat::w_approx(ntt, &key.a_hat, &y, &vec![0u32; K * N]);
    let mut u: Vec<u8> = w.iter().map(|&x| mlnat::decompose(x).0 as u8).collect();
    let mut target = None;
    match mode {
        Mode::ResidualOut => {
            let p = (0..K * N).find(|&t| (1..=12).contains(&u[t]))?;
            u[p] += 2;
            target = Some(p);
        }
        Mode::Hints(_) => {
            let mut left = bumps;
            for t in 0..K * N {
                if left == 0 {
                    break;
                }
                let r0 = mlnat::decompose(w[t]).1;
                if (1..=13).contains(&u[t]) && r0 > region::G / 4 && r0 < 3 * region::G / 4 {
                    u[t] += 1;
                    left -= 1;
                }
            }
        }
        _ => {}
    }
    let tr = mlnat::tr_of(&key.pk);
    let _ = tr;
    let ct = mlnat::c_tilde_of(mu, &mlnat::w1_encode(&u));
    let mut c = mlnat::sample_in_ball(&ct);
    ntt.fwd(&mut c);
    let mut z = y.clone();
    for l in 0..L {
        let mut p = [0u32; N];
        for j in 0..N {
            p[j] = red(c[j] as u64 * key.s1_hat[l][j] as u64);
        }
        ntt.inv(&mut p);
        for j in 0..N {
            z[l * N + j] += ctr(p[j]);
        }
    }
    let max_abs_z = z.iter().map(|v| v.abs()).max().unwrap();
    let over: Vec<usize> = (0..L * N).filter(|&t| z[t].abs() >= mlnat::ZB).collect();
    match mode {
        Mode::ZEdge(sg) => {
            if over.len() != 1 || z[over[0]] != sg * mlnat::ZB {
                return None;
            }
        }
        _ => {
            if !over.is_empty() {
                return None;
            }
        }
    }
    let b = mlnat::b_of(ntt, &key.pk, &ct);
    let wp = mlnat::w_approx(ntt, &key.a_hat, &z, &b);
    let mut out_of_region = 0;
    let mut hints = 0;
    for t in 0..K * N {
        let cl = region::class_of(u[t]);
        let e = ctr(modq(wp[t] as i64 - A2 * u[t] as i64));
        if !region::in_region(cl, e) {
            out_of_region += 1;
            if target != Some(t) {
                return None;
            }
            continue;
        }
        let s = region::selector_of(cl, e);
        hints += (s * s) as usize;
    }
    match mode {
        Mode::ResidualOut => {
            if out_of_region != 1 || hints > mlnat::OMEGA {
                return None;
            }
        }
        Mode::Hints(h) => {
            if hints != h {
                return None;
            }
        }
        _ => {
            if hints > mlnat::OMEGA {
                return None;
            }
        }
    }
    Some(Signed { input: SigInput { z, u }, attempts: attempt + 1, hints, max_abs_z, out_of_region })
}

/// Sign (rec.ctx, rec.msg) under the relaxed rules. Attempts run in parallel batches; the
/// smallest accepted attempt index is returned, so the result is deterministic.
pub fn sign(ntt: &Ntt, key: &RKey, ctx: &[u8], msg: &[u8], mode: Mode, seed: &[u8]) -> Signed {
    let mu = mlnat::mu_of(&key.tr, ctx, msg);
    let mut bumps = 0usize;
    let mut start = 0u64;
    loop {
        let batch = 4096u64;
        let found = (start..start + batch).into_par_iter().filter_map(|a| try_sign(ntt, key, &mu, mode, seed, a, bumps)).min_by_key(|s| s.attempts);
        if let Some(s) = found {
            return s;
        }
        if let Mode::Hints(h) = mode {
            // Calibrate the number of deliberate hints from one valid-mode attempt's natural count.
            if let Some(v) = (start..start + 64).find_map(|a| try_sign(ntt, key, &mu, Mode::Valid, seed, a, 0)) {
                bumps = h.saturating_sub(v.hints);
            }
        }
        start += batch;
        assert!(start < 1 << 26, "relaxed signer did not converge");
    }
}

pub fn record(key: &RKey, idx: u64) -> Record {
    Record { pk: key.pk.clone(), ctx: crate::batch::xof(b"relaxed-ctx", idx, 17), msg: crate::batch::xof(b"relaxed-msg", idx, 40) }
}

pub fn q_check() -> bool {
    Q == 8_380_417
}
