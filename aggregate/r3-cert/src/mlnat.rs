//! Native ML-DSA-87 arithmetic for the certificate: FIPS 204 encodings, NTT, ExpandA,
//! SampleInBall, mu and c_tilde, and the per-signature public data the verifier derives.

use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Shake128, Shake256};

pub const Q: u32 = 8_380_417;
pub const QI: i64 = Q as i64;
pub const HALF: i64 = (QI - 1) / 2;
pub const DBITS: u32 = 13;
pub const TAU: usize = 60;
pub const GAMMA1: i64 = 1 << 19;
pub const GAMMA2: i64 = (QI - 1) / 32;
pub const BETA: i64 = 120;
pub const OMEGA: usize = 75;
pub const K: usize = 8;
pub const L: usize = 7;
pub const N: usize = 256;
pub const PK_BYTES: usize = 32 + K * 320;
pub const SIG_BYTES: usize = 64 + L * 640 + OMEGA + K;
/// a = 2 gamma2, q = 16 a + 1.
pub const A2: i64 = 2 * GAMMA2;
/// Strict response bound: |z| < ZB.
pub const ZB: i64 = GAMMA1 - BETA;

pub type Poly = [u32; N];

pub fn shake256(parts: &[&[u8]], out: &mut [u8]) {
    let mut h = Shake256::default();
    for p in parts {
        h.update(p);
    }
    h.finalize_xof().read(out);
}

#[inline(always)]
pub fn red(x: u64) -> u32 {
    (x % Q as u64) as u32
}
#[inline(always)]
pub fn ctr(x: u32) -> i64 {
    let x = x as i64;
    if x > HALF { x - QI } else { x }
}
#[inline(always)]
pub fn modq(x: i64) -> u32 {
    x.rem_euclid(QI) as u32
}

fn powq(mut b: u64, mut e: u64) -> u64 {
    let mut r = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % Q as u64;
        }
        b = b * b % Q as u64;
        e >>= 1;
    }
    r
}

/// The FIPS 204 NTT (Algorithm 41) and inverse (Algorithm 42), logical FIPS slot order.
pub struct Ntt {
    z: [u32; N],
}

impl Default for Ntt {
    fn default() -> Self {
        Self::new()
    }
}

impl Ntt {
    pub fn new() -> Self {
        let mut z = [0u32; N];
        for (k, zk) in z.iter_mut().enumerate() {
            *zk = powq(1753, (k as u8).reverse_bits() as u64) as u32;
        }
        Ntt { z }
    }
    pub fn fwd(&self, w: &mut [u32]) {
        let mut k = 0;
        let mut len = 128;
        while len >= 1 {
            let mut start = 0;
            while start < N {
                k += 1;
                let zk = self.z[k] as u64;
                for j in start..start + len {
                    let t = red(zk * w[j + len] as u64);
                    w[j + len] = (w[j] + Q - t) % Q;
                    w[j] = (w[j] + t) % Q;
                }
                start += 2 * len;
            }
            len /= 2;
        }
    }
    pub fn inv(&self, w: &mut [u32]) {
        let mut k = N;
        let mut len = 1;
        while len < N {
            let mut start = 0;
            while start < N {
                k -= 1;
                let zeta = (Q - self.z[k]) as u64;
                for j in start..start + len {
                    let t = w[j];
                    w[j] = (t + w[j + len]) % Q;
                    w[j + len] = red(zeta * ((t + Q - w[j + len]) % Q) as u64);
                }
                start += 2 * len;
            }
            len *= 2;
        }
        for c in w.iter_mut() {
            *c = red(*c as u64 * 8_347_681);
        }
    }
}

/// Schoolbook product in Z_q[X]/(X^256 + 1): the independent reference for self-tests.
pub fn negacyclic(a: &[u32], b: &[u32]) -> Poly {
    let mut acc = [0i128; N];
    for i in 0..N {
        if a[i] == 0 {
            continue;
        }
        for j in 0..N {
            let p = a[i] as i128 * b[j] as i128;
            if i + j < N { acc[i + j] += p } else { acc[i + j - N] -= p }
        }
    }
    acc.map(|v| v.rem_euclid(Q as i128) as u32)
}

/// Coefficient-domain adjoint a(X^-1) mod X^256 + 1 (reference for the slot-reversal identity).
pub fn adjoint_coeff(a: &[u32]) -> Poly {
    let mut r = [0u32; N];
    r[0] = a[0];
    for j in 1..N {
        r[j] = (Q - a[N - j]) % Q;
    }
    r
}

fn bits_le(bytes: &[u8], width: usize, count: usize) -> Vec<u32> {
    (0..count)
        .map(|i| {
            let mut v = 0u32;
            for b in 0..width {
                let bit = i * width + b;
                v |= (((bytes[bit / 8] >> (bit % 8)) & 1) as u32) << b;
            }
            v
        })
        .collect()
}

fn pack_le(vals: &[u32], width: usize, out: &mut [u8]) {
    out.iter_mut().for_each(|b| *b = 0);
    for (i, &v) in vals.iter().enumerate() {
        for b in 0..width {
            if (v >> b) & 1 == 1 {
                let bit = i * width + b;
                out[bit / 8] |= 1 << (bit % 8);
            }
        }
    }
}

/// ExpandA (FIPS 204 Algorithm 32): A_hat[r][s] in NTT form, flattened as r * L + s.
pub fn expand_a(rho: &[u8]) -> Vec<Poly> {
    let mut out = vec![[0u32; N]; K * L];
    for r in 0..K {
        for s in 0..L {
            let mut h = Shake128::default();
            h.update(rho);
            h.update(&[s as u8, r as u8]);
            let mut rd = h.finalize_xof();
            let poly = &mut out[r * L + s];
            let mut k = 0;
            let mut buf = [0u8; 3 * 56];
            while k < N {
                rd.read(&mut buf);
                for c in buf.chunks_exact(3) {
                    let v = (c[0] as u32 | (c[1] as u32) << 8 | (c[2] as u32) << 16) & 0x7f_ffff;
                    if v < Q && k < N {
                        poly[k] = v;
                        k += 1;
                    }
                }
            }
        }
    }
    out
}

/// pk = rho || SimpleBitPack(t1, 10 bits).
pub fn decode_pk(pk: &[u8]) -> ([u8; 32], Vec<u32>) {
    assert_eq!(pk.len(), PK_BYTES);
    let rho: [u8; 32] = pk[..32].try_into().unwrap();
    (rho, bits_le(&pk[32..], 10, K * N))
}

pub fn encode_pk(rho: &[u8; 32], t1: &[u32]) -> Vec<u8> {
    let mut pk = vec![0u8; PK_BYTES];
    pk[..32].copy_from_slice(rho);
    pack_le(t1, 10, &mut pk[32..]);
    pk
}

pub fn tr_of(pk: &[u8]) -> [u8; 64] {
    let mut tr = [0u8; 64];
    shake256(&[pk], &mut tr);
    tr
}

/// mu = H(tr || 0 || |ctx| || ctx || M, 64): pure mode with a context.
pub fn mu_of(tr: &[u8; 64], ctx: &[u8], msg: &[u8]) -> [u8; 64] {
    assert!(ctx.len() <= 255);
    let mut mu = [0u8; 64];
    shake256(&[tr, &[0, ctx.len() as u8], ctx, msg], &mut mu);
    mu
}

/// w1Encode for gamma2 = (q-1)/32: two 4-bit coefficients per byte, low nibble first.
pub fn w1_encode(u: &[u8]) -> Vec<u8> {
    assert_eq!(u.len(), K * N);
    (0..K * N / 2).map(|j| u[2 * j] | (u[2 * j + 1] << 4)).collect()
}

pub fn w1_decode(b: &[u8]) -> Vec<u8> {
    assert_eq!(b.len(), K * N / 2);
    b.iter().flat_map(|&x| [x & 15, x >> 4]).collect()
}

pub fn c_tilde_of(mu: &[u8; 64], w1enc: &[u8]) -> [u8; 64] {
    let mut c = [0u8; 64];
    shake256(&[mu, w1enc], &mut c);
    c
}

/// SampleInBall (FIPS 204 Algorithm 29), coefficients in {-1, 0, 1} mod q.
pub fn sample_in_ball(c_tilde: &[u8]) -> Poly {
    let mut h = Shake256::default();
    h.update(c_tilde);
    let mut rd = h.finalize_xof();
    let mut s = [0u8; 8];
    rd.read(&mut s);
    let mut signs = u64::from_le_bytes(s);
    let mut c = [0u32; N];
    for i in N - TAU..N {
        let mut j = [0u8; 1];
        loop {
            rd.read(&mut j);
            if j[0] as usize <= i {
                break;
            }
        }
        c[i] = c[j[0] as usize];
        c[j[0] as usize] = if signs & 1 == 1 { Q - 1 } else { 1 };
        signs >>= 1;
    }
    c
}

/// Decompose (FIPS 204 Algorithm 36) for gamma2 = (q-1)/32: (r1, r0).
pub fn decompose(r: u32) -> (u32, i64) {
    let m = (r as i64) % A2;
    let r0 = if m > GAMMA2 { m - A2 } else { m };
    if r as i64 - r0 == QI - 1 { (0, r0 - 1) } else { (((r as i64 - r0) / A2) as u32, r0) }
}

pub fn use_hint(h: bool, r: u32) -> u32 {
    let (r1, r0) = decompose(r);
    if !h {
        r1
    } else if r0 > 0 {
        (r1 + 1) % 16
    } else {
        (r1 + 15) % 16
    }
}

/// HintBitUnpack (FIPS 204 Algorithm 21). None when the encoding is malformed.
pub fn hint_unpack(y: &[u8]) -> Option<Vec<bool>> {
    let mut h = vec![false; K * N];
    let mut index = 0usize;
    for i in 0..K {
        let end = y[OMEGA + i] as usize;
        if end < index || end > OMEGA {
            return None;
        }
        let first = index;
        while index < end {
            if index > first && y[index - 1] >= y[index] {
                return None;
            }
            h[i * N + y[index] as usize] = true;
            index += 1;
        }
    }
    if y[index..OMEGA].iter().any(|&b| b != 0) {
        return None;
    }
    Some(h)
}

/// HintBitPack (FIPS 204 Algorithm 20). None when more than omega hints are set.
pub fn hint_pack(h: &[bool]) -> Option<Vec<u8>> {
    let mut y = vec![0u8; OMEGA + K];
    let mut index = 0;
    for i in 0..K {
        for j in 0..N {
            if h[i * N + j] {
                if index >= OMEGA {
                    return None;
                }
                y[index] = j as u8;
                index += 1;
            }
        }
        y[OMEGA + i] = index as u8;
    }
    Some(y)
}

/// sigDecode: (c_tilde, z, h). z is centered; None when the hint encoding is malformed.
pub fn decode_sig(sig: &[u8]) -> Option<([u8; 64], Vec<i64>, Vec<bool>)> {
    if sig.len() != SIG_BYTES {
        return None;
    }
    let ct: [u8; 64] = sig[..64].try_into().unwrap();
    let z = bits_le(&sig[64..64 + 640 * L], 20, L * N).into_iter().map(|v| GAMMA1 - v as i64).collect();
    let h = hint_unpack(&sig[64 + 640 * L..])?;
    Some((ct, z, h))
}

/// sigEncode. None when z does not fit the 20-bit encoding or there are more than omega hints.
pub fn encode_sig(ct: &[u8; 64], z: &[i64], h: &[bool]) -> Option<Vec<u8>> {
    let mut s = vec![0u8; SIG_BYTES];
    s[..64].copy_from_slice(ct);
    let enc: Vec<u32> = z.iter().map(|&v| GAMMA1 - v).map(|v| if (0..1 << 20).contains(&v) { Some(v as u32) } else { None }).collect::<Option<_>>()?;
    pack_le(&enc, 20, &mut s[64..64 + 640 * L]);
    s[64 + 640 * L..].copy_from_slice(&hint_pack(h)?);
    Some(s)
}

/// One authorization record of the statement: public key, context and message.
#[derive(Clone)]
pub struct Record {
    pub pk: Vec<u8>,
    pub ctx: Vec<u8>,
    pub msg: Vec<u8>,
}

/// What the verifier derives for one signature from (record, public u): A_hat and
/// bu = c 2^13 t1 + a u mod q in the coefficient domain, index k * 256 + j.
pub struct SigPublic {
    pub a_hat: Vec<Poly>,
    pub bu: Vec<u32>,
}

/// Derive A_hat and b + a u from the record and its public u (one byte per coefficient, 0..15).
pub fn derive_public(ntt: &Ntt, rec: &Record, u: &[u8]) -> SigPublic {
    let (rho, t1) = decode_pk(&rec.pk);
    let a_hat = expand_a(&rho);
    let tr = tr_of(&rec.pk);
    let mu = mu_of(&tr, &rec.ctx, &rec.msg);
    let ct = c_tilde_of(&mu, &w1_encode(u));
    let mut c = sample_in_ball(&ct);
    ntt.fwd(&mut c);
    let mut bu = vec![0u32; K * N];
    for k in 0..K {
        let mut t = [0u32; N];
        for j in 0..N {
            t[j] = t1[k * N + j] << DBITS;
        }
        ntt.fwd(&mut t);
        for j in 0..N {
            t[j] = red(t[j] as u64 * c[j] as u64);
        }
        ntt.inv(&mut t);
        for j in 0..N {
            bu[k * N + j] = red(t[j] as u64 + (A2 as u64) * u[k * N + j] as u64);
        }
    }
    SigPublic { a_hat, bu }
}

/// w'_approx = A z - c 2^13 t1 mod q (coefficient domain), the FIPS verifier's value.
pub fn w_approx(ntt: &Ntt, a_hat: &[Poly], z: &[i64], b: &[u32]) -> Vec<u32> {
    let zh: Vec<Poly> = (0..L)
        .map(|l| {
            let mut p = [0u32; N];
            for j in 0..N {
                p[j] = modq(z[l * N + j]);
            }
            ntt.fwd(&mut p);
            p
        })
        .collect();
    let mut w = vec![0u32; K * N];
    for k in 0..K {
        let mut acc = [0u32; N];
        for j in 0..N {
            let mut s = 0u64;
            for l in 0..L {
                s += a_hat[k * L + l][j] as u64 * zh[l][j] as u64;
            }
            acc[j] = red(s);
        }
        ntt.inv(&mut acc);
        for j in 0..N {
            w[k * N + j] = (acc[j] + Q - b[k * N + j]) % Q;
        }
    }
    w
}

/// b = c 2^13 t1 alone (no a u term), used by witness generation before u is known.
pub fn b_of(ntt: &Ntt, pk: &[u8], c_tilde: &[u8; 64]) -> Vec<u32> {
    let (_, t1) = decode_pk(pk);
    let mut c = sample_in_ball(c_tilde);
    ntt.fwd(&mut c);
    let mut b = vec![0u32; K * N];
    for k in 0..K {
        let mut t = [0u32; N];
        for j in 0..N {
            t[j] = t1[k * N + j] << DBITS;
        }
        ntt.fwd(&mut t);
        for j in 0..N {
            t[j] = red(t[j] as u64 * c[j] as u64);
        }
        ntt.inv(&mut t);
        b[k * N..(k + 1) * N].copy_from_slice(&t);
    }
    b
}
