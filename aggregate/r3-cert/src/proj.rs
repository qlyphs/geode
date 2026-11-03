//! The fourteen mod-q projections (round 2 section 2.2, round 3 sections 3.1 and 3.2).
//!
//! For trial j: alpha^(j) in F_q^N (one scalar per signature), eta^(j) in F_q^2048.
//! r_{j,i} = alpha_i eta, s_{j,i} = alpha_i A_i^dagger eta (adjoint by slot reversal),
//! d_{j,c} = sum_{i in chunk c} <r_{j,i}, b_i + a u_i>. Everything is reduced mod q and then
//! centered before it enters Goldilocks.

use crate::mlnat::{K, L, N, Ntt, Poly, Q, ctr, red, shake256};
use sha3::Shake256;
use sha3::digest::{ExtendableOutput, Update, XofReader};

pub const TRIALS: usize = 14;
pub const CHUNK: usize = 512;
/// Quotient range: -2^39 <= V < 2^39, encoded LE5(V + 2^39).
pub const VBITS: u32 = 39;

pub fn chunks(n: usize) -> usize {
    n.div_ceil(CHUNK)
}

pub struct Challenges {
    pub alpha: Vec<Vec<u32>>,
    pub eta: Vec<Vec<u32>>,
    pub eta_hat: Vec<Vec<u32>>,
}

/// Calls of the QLYAUTH4 projection XOF (gate 2 of round 7: profile 0x00070001 makes none).
pub static PROJ_XOF_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn sample_fq(seed: &[u8; 64], label: &[u8], j: usize, n: usize) -> Vec<u32> {
    PROJ_XOF_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let mut h = Shake256::default();
    h.update(b"r3-cert/proj-challenge");
    h.update(seed);
    h.update(label);
    h.update(&(j as u32).to_le_bytes());
    let mut rd = h.finalize_xof();
    let mut v = Vec::with_capacity(n);
    let mut buf = [0u8; 3];
    while v.len() < n {
        rd.read(&mut buf);
        let x = (buf[0] as u32 | (buf[1] as u32) << 8 | (buf[2] as u32) << 16) & 0x7f_ffff;
        if x < Q {
            v.push(x);
        }
    }
    v
}

impl Challenges {
    pub fn sample(ntt: &Ntt, seed: &[u8; 64], nsig: usize) -> Self {
        let alpha: Vec<Vec<u32>> = (0..TRIALS).map(|j| sample_fq(seed, b"alpha", j, nsig)).collect();
        let eta: Vec<Vec<u32>> = (0..TRIALS).map(|j| sample_fq(seed, b"eta", j, K * N)).collect();
        Self::finish(ntt, alpha, eta)
    }

    /// Profile 0x00070001 (spec §5.3): the decoded F_q pool of round 1, partitioned as
    /// trial 0: alpha[0..N], eta[0..2048], trial 1: ..., trial 13.
    pub fn from_values(ntt: &Ntt, v: &[u32], nsig: usize) -> Self {
        let per = nsig + K * N;
        assert_eq!(v.len(), TRIALS * per);
        let alpha = (0..TRIALS).map(|j| v[j * per..j * per + nsig].to_vec()).collect();
        let eta = (0..TRIALS).map(|j| v[j * per + nsig..(j + 1) * per].to_vec()).collect();
        Self::finish(ntt, alpha, eta)
    }

    fn finish(ntt: &Ntt, alpha: Vec<Vec<u32>>, eta: Vec<Vec<u32>>) -> Self {
        let eta_hat = eta
            .iter()
            .map(|e| {
                let mut h = e.clone();
                for k in 0..K {
                    ntt.fwd(&mut h[k * N..(k + 1) * N]);
                }
                h
            })
            .collect();
        Challenges { alpha, eta, eta_hat }
    }

    /// ctr(s_{j,i}) for all 14 trials, 1,792 coefficients each, flattened [j][l * 256 + j'].
    /// The adjoint uses NTT(f(X^-1))[j] = NTT(f)[255 - j] (round 3 section 3.2).
    pub fn s_centered(&self, ntt: &Ntt, a_hat: &[Poly], i: usize, out: &mut [i32]) {
        debug_assert_eq!(out.len(), TRIALS * L * N);
        for j in 0..TRIALS {
            let al = self.alpha[j][i] as u64;
            let eh = &self.eta_hat[j];
            for l in 0..L {
                let mut acc = [0u32; N];
                for (t, a) in acc.iter_mut().enumerate() {
                    let mut s = 0u64;
                    for k in 0..K {
                        s += a_hat[k * L + l][N - 1 - t] as u64 * eh[k * N + t] as u64;
                    }
                    *a = red(s);
                }
                ntt.inv(&mut acc);
                let o = &mut out[(j * L + l) * N..(j * L + l + 1) * N];
                for t in 0..N {
                    o[t] = ctr(red(acc[t] as u64 * al)) as i32;
                }
            }
        }
    }

    #[inline(always)]
    pub fn r_centered(&self, j: usize, i: usize, slot: usize) -> i64 {
        ctr(red(self.alpha[j][i] as u64 * self.eta[j][slot] as u64))
    }

    /// alpha_i <eta, bu_i> mod q.
    pub fn d_part(&self, j: usize, i: usize, bu: &[u32]) -> u64 {
        let mut s = 0u64;
        for (e, b) in self.eta[j].iter().zip(bu) {
            s = (s + *e as u64 * *b as u64) % Q as u64;
        }
        s * self.alpha[j][i] as u64 % Q as u64
    }
}

pub fn encode_quotient(v: i64) -> [u8; 5] {
    let w = (v + (1i64 << VBITS)) as u64;
    assert!(w < 1 << 40);
    w.to_le_bytes()[..5].try_into().unwrap()
}

pub fn decode_quotient(b: &[u8]) -> i64 {
    let mut w = [0u8; 8];
    w[..5].copy_from_slice(b);
    u64::from_le_bytes(w) as i64 - (1i64 << VBITS)
}

/// The deterministic no-wrap bound of section 3.1 for a chunk of c signatures.
pub fn lift_bound(c: u128) -> u128 {
    let half = (Q as u128 - 1) / 2;
    half * (1792 * c * 524_167 + 2048 * c * 523_777 + 1) + ((Q as u128) << VBITS)
}

/// Self-test of the slot-reversal adjoint against the coefficient-domain definition.
pub fn adjoint_selftest(ntt: &Ntt) -> bool {
    let mut seed = [0u8; 64];
    shake256(&[b"r3-cert/adjoint-selftest"], &mut seed);
    let f = sample_fq(&seed, b"f", 0, N);
    let mut fh = f.clone();
    ntt.fwd(&mut fh);
    let mut star = crate::mlnat::adjoint_coeff(&f).to_vec();
    ntt.fwd(&mut star);
    (0..N).all(|j| star[j] == fh[N - 1 - j])
}
