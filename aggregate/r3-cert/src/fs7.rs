//! Profile 0x00070001 (manifest QLYAUTH7): the full-commitment-history BCS transcript of
//! Chiesa-Fenzi (TCC 2024), as specified in the round-7 design notes.
//!
//! This module holds the parts that do not depend on p3:
//! - the primitive encodings and framing (spec §2.2, §3.4);
//! - the coin descriptor and the fixed-pool decoders for K, theta, F_q and query indices (§5);
//! - the singleton Merkle leaf hash of the global Merkle oracle (§3.1);
//! - the coin derivation, one SHAKE256 call per registered round over the raw instance and the
//!   full root history, computed incrementally with a prefix squeeze (§3.4), and a simple
//!   full-preimage reference used by the acceptance gate;
//! - the inline reference test vectors (§9, profile 0xffffffff).

use sha3::digest::{Digest, ExtendableOutput, Update, XofReader};
use sha3::{Sha3_512, Shake256};

pub const DOMAIN: &[u8] = b"Qlyphs/Archive/CF24/v1\0";
pub const INSTANCE_DOMAIN: &[u8] = b"Qlyphs/Archive/Instance/v7\0";
/// The production profile (N = 2048, chain statement, manifest QLYAUTH7).
pub const PROFILE_V7: u32 = 0x0007_0001;
/// The codec test profile of §9; every verifier rejects it.
pub const PROFILE_TEST: u32 = 0xffff_ffff;
/// Common formal coin-block length of profile 0x00070001 (the projection pool of round 1).
pub const COIN_BYTES_V7: usize = 173_568;

const P: u64 = 0xffff_ffff_0000_0001;
const Q: u64 = 8_380_417;

pub fn le16(x: u16) -> [u8; 2] {
    x.to_le_bytes()
}
pub fn le32(x: u32) -> [u8; 4] {
    x.to_le_bytes()
}
pub fn le64(x: u64) -> [u8; 8] {
    x.to_le_bytes()
}

/// F(tag, bytes) = LE16(tag) || LE64(len(bytes)) || bytes.
pub fn frame(tag: u16, v: &[u8]) -> Vec<u8> {
    let mut o = Vec::with_capacity(10 + v.len());
    o.extend_from_slice(&le16(tag));
    o.extend_from_slice(&le64(v.len() as u64));
    o.extend_from_slice(v);
    o
}

pub fn shake(parts: &[&[u8]], n: usize) -> Vec<u8> {
    let mut h = Shake256::default();
    for p in parts {
        h.update(p);
    }
    let mut out = vec![0u8; n];
    h.finalize_xof().read(&mut out);
    out
}

// ---------------------------------------------------------------- coin descriptor and decoders

/// What one registered round requests from its coin block (§3.4).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Shape {
    /// Ordinary K-elements.
    pub nk: usize,
    /// One theta in K \ F_p.
    pub theta: bool,
    /// Elements of F_q.
    pub nq: usize,
    /// One query index per entry, of that many bits.
    pub widths: Vec<u8>,
    /// F_q pool slack in 3-byte words. 0 is the QLYAUTH7 rule (fixed slack 512, zero padding
    /// when short); a nonzero value is the round-10 lab rule: that slack, and a pool that runs
    /// short is an error (`Decoded::short`), never padded.
    pub qslack: u32,
}

pub const THETA_POOL: usize = 376;

impl Shape {
    pub fn k(nk: usize) -> Self {
        Shape { nk, ..Default::default() }
    }
    /// Desc = LE32(nk) || u8(theta) || LE32(nq) || LE32(len(widths)) || bytes(widths).
    pub fn descriptor(&self) -> Vec<u8> {
        let mut d = Vec::with_capacity(13 + self.widths.len());
        d.extend_from_slice(&le32(self.nk as u32));
        d.push(self.theta as u8);
        d.extend_from_slice(&le32(self.nq as u32));
        d.extend_from_slice(&le32(self.widths.len() as u32));
        d.extend_from_slice(&self.widths);
        if self.qslack != 0 {
            // Round-10 lab shapes only: the slack is part of what the coins are derived for.
            d.extend_from_slice(&le32(self.qslack));
        }
        d
    }
    pub fn k_pool(&self) -> usize {
        if self.nk > 0 { 8 * (5 * self.nk + 32) } else { 0 }
    }
    pub fn q_pool(&self) -> usize {
        let slack = if self.qslack == 0 { 512 } else { self.qslack as usize };
        if self.nq > 0 { 3 * (self.nq + slack) } else { 0 }
    }
    /// Bytes of the block the decoder reads: K pool, theta pool, F_q pool, 4 B per index (§5.5).
    pub fn used(&self) -> usize {
        self.k_pool() + if self.theta { THETA_POOL } else { 0 } + self.q_pool() + 4 * self.widths.len()
    }
}

/// The round-10 F_q slack for `nq` coefficients: 512 + ceil(nq / 400) words. With rejection
/// probability (2^23 - q) / 2^23 < 2^-10 per word, the pool runs short with probability below
/// 2^-768 for every nq up to 2^24 (aggregate/r10-check/qpool.py computes the tail exactly).
pub fn qslack10(nq: usize) -> u32 {
    (512 + nq.div_ceil(400)) as u32
}

/// Test-only: make every strict F_q pool look one coefficient short (both sides must reject).
pub static FORCE_SHORT_Q: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Accept the first `count` candidates of `width` bytes (little endian, masked) below `modulus`,
/// scanning the whole fixed pool; pad with zeros. No refill.
pub fn pool(raw: &[u8], count: usize, width: usize, modulus: u64, mask: u64) -> Vec<u64> {
    let mut acc = Vec::with_capacity(count);
    for c in raw.chunks_exact(width) {
        let mut w = [0u8; 8];
        w[..width].copy_from_slice(c);
        let x = u64::from_le_bytes(w) & mask;
        if x < modulus && acc.len() < count {
            acc.push(x);
        }
    }
    acc.resize(count, 0);
    acc
}

/// The typed values of one coin block, as canonical integers.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Decoded {
    pub k: Vec<[u64; 5]>,
    pub theta: Option<[u64; 5]>,
    pub q: Vec<u32>,
    pub idx: Vec<u32>,
    /// A strict (round-10) F_q pool held fewer than nq accepted words; `q` is then truncated.
    pub short: bool,
}

/// Accepted candidates without padding (strict pools).
fn pool_strict(raw: &[u8], count: usize, width: usize, modulus: u64, mask: u64) -> Vec<u64> {
    let mut acc = Vec::with_capacity(count);
    for c in raw.chunks_exact(width) {
        if acc.len() == count {
            break;
        }
        let mut w = [0u8; 8];
        w[..width].copy_from_slice(c);
        let x = u64::from_le_bytes(w) & mask;
        if x < modulus {
            acc.push(x);
        }
    }
    acc
}

/// Decode a block (§5). `raw` may be the used prefix or the whole formal block; the suffix is
/// ignored. Panics if `raw` is shorter than the used prefix (a caller bug, never data).
pub fn decode(raw: &[u8], s: &Shape) -> Decoded {
    assert!(raw.len() >= s.used(), "coin block shorter than its decoder");
    let mut off = 0usize;
    let mut take = |n: usize| {
        let r = &raw[off..off + n];
        off += n;
        r
    };
    let mut out = Decoded::default();
    if s.nk > 0 {
        let a = pool(take(s.k_pool()), 5 * s.nk, 8, P, u64::MAX);
        out.k = a.chunks_exact(5).map(|c| [c[0], c[1], c[2], c[3], c[4]]).collect();
    }
    if s.theta {
        let a = pool(take(THETA_POOL), 15, 8, P, u64::MAX);
        let cands: Vec<[u64; 5]> = a.chunks_exact(5).map(|c| [c[0], c[1], c[2], c[3], c[4]]).collect();
        out.theta = Some(cands.into_iter().find(|c| c[1..].iter().any(|&x| x != 0)).unwrap_or([0, 1, 0, 0, 0]));
    }
    if s.nq > 0 {
        if s.qslack == 0 {
            out.q = pool(take(s.q_pool()), s.nq, 3, Q, 0x7f_ffff).into_iter().map(|x| x as u32).collect();
        } else {
            let mut q: Vec<u32> = pool_strict(take(s.q_pool()), s.nq, 3, Q, 0x7f_ffff).into_iter().map(|x| x as u32).collect();
            if FORCE_SHORT_Q.load(std::sync::atomic::Ordering::Relaxed) {
                q.truncate(s.nq - 1);
            }
            out.short = q.len() < s.nq;
            out.q = q;
        }
    }
    for &b in &s.widths {
        assert!((1..=31).contains(&b), "index width");
        let w = u32::from_le_bytes(take(4).try_into().unwrap());
        out.idx.push(w & ((1u32 << b) - 1));
    }
    out
}

// ---------------------------------------------------------------- global Merkle oracle (§3.1)

pub const KIND_ROW: u8 = 0x00;
pub const KIND_SCALAR: u8 = 0x01;

/// LeafHash(Symbol) = H64(0x80 || LE32(profile) || LE32(round) || kind || LE32(len) || payload).
pub fn leaf_hash(profile: u32, round: u32, kind: u8, payload: &[u8]) -> [u8; 64] {
    let mut h = Shake256::default();
    h.update(&[0x80]);
    h.update(&le32(profile));
    h.update(&le32(round));
    h.update(&[kind]);
    h.update(&le32(payload.len() as u32));
    h.update(payload);
    let mut out = [0u8; 64];
    h.finalize_xof().read(&mut out);
    out
}

/// NodeHash(left, right) = H64(0x81 || left || right).
pub fn node_hash(l: &[u8; 64], r: &[u8; 64]) -> [u8; 64] {
    let mut h = Shake256::default();
    h.update(&[0x81]);
    h.update(l);
    h.update(r);
    let mut out = [0u8; 64];
    h.finalize_xof().read(&mut out);
    out
}

/// Round-10 lab node hash (one independent vector-commitment oracle per committed tree):
/// H64(0x81 || LE32(profile) || LE16(tree commit round) || left || right), 135 bytes, one
/// SHAKE256 block.
pub fn node_hash_tree(profile: u32, tree: u16, l: &[u8; 64], r: &[u8; 64]) -> [u8; 64] {
    let mut h = Shake256::default();
    h.update(&[0x81]);
    h.update(&le32(profile));
    h.update(&le16(tree));
    h.update(l);
    h.update(r);
    let mut out = [0u8; 64];
    h.finalize_xof().read(&mut out);
    out
}

/// Round-10 checks of the strict pool and the tree-separated node hash: (description, pass).
pub fn r10_selfcheck() -> Vec<(String, bool)> {
    let mut v = vec![];
    let s = Shape { nq: 8, qslack: qslack10(8), ..Default::default() };
    let d = decode(&vec![0xff; s.used()], &s);
    v.push(("strict pool of rejected words: short, not padded".to_string(), d.short && d.q.is_empty()));
    let legacy = Shape { nq: 8, ..Default::default() };
    v.push(("legacy pool of rejected words: padded with zeros (QLYAUTH7 rule kept)".to_string(), !decode(&vec![0xff; legacy.used()], &legacy).short && decode(&vec![0xff; legacy.used()], &legacy).q == vec![0; 8]));
    let ok: Vec<u8> = (0..s.used()).map(|i| if i % 3 == 2 { 0 } else { 1 }).collect();
    let d = decode(&ok, &s);
    v.push(("strict pool of accepted words: full".to_string(), !d.short && d.q.len() == 8));
    v.push(("strict descriptor differs from the legacy one".to_string(), s.descriptor() != Shape { nq: 8, ..Default::default() }.descriptor()));
    v.push(("legacy descriptor unchanged (13 bytes + widths)".to_string(), legacy.descriptor().len() == 13));
    let (l, r) = ([7u8; 64], [9u8; 64]);
    v.push(("same (L, R) under tree rounds 1 and 2: different digests".to_string(), node_hash_tree(0xfff9_100b, 1, &l, &r) != node_hash_tree(0xfff9_100b, 2, &l, &r)));
    v.push(("same (L, R) under two profiles: different digests".to_string(), node_hash_tree(0xfff9_100b, 1, &l, &r) != node_hash_tree(0xfff9_110b, 1, &l, &r)));
    v.push(("tree-separated node differs from the QLYAUTH7 node".to_string(), node_hash_tree(0xfff9_100b, 1, &l, &r) != node_hash(&l, &r)));
    for (nq, need) in [(14 * (2048 + 2048), 512usize), (14 * (16384 + 2048), 960), (14 * (65536 + 2048), 2112)] {
        v.push((format!("qslack10({nq}) = {} >= {need} (failure <= 2^-768)", qslack10(nq)), qslack10(nq) as usize >= need));
    }
    v
}

/// The root of a length-one tree holding a round's scalar body.
pub fn singleton_root(profile: u32, round: u32, body: &[u8]) -> [u8; 64] {
    leaf_hash(profile, round, KIND_SCALAR, body)
}

// ---------------------------------------------------------------- coin derivation (§3.4)

/// Entry(j) = F(16, LE32(j) || root_j[64] || 0x00), the last byte being SaltEnc(zero salt).
pub fn entry(j: u32, root: &[u8; 64]) -> Vec<u8> {
    let mut v = Vec::with_capacity(69);
    v.extend_from_slice(&le32(j));
    v.extend_from_slice(root);
    v.push(0x00);
    frame(16, &v)
}

/// The incremental implementation the specification allows: the domain, profile and framed
/// instance are absorbed once, each history entry is appended to the unfinalized state, and a
/// round clones the state, appends its descriptor, round number and formal output length, and
/// squeezes only the prefix its decoder reads.
#[derive(Clone)]
pub struct CoinState {
    profile: u32,
    formal_len: u64,
    base: Shake256,
    rounds: u32,
}

impl CoinState {
    pub fn new(profile: u32, formal_len: usize, statement: &[u8]) -> Self {
        let mut base = Shake256::default();
        base.update(DOMAIN);
        base.update(&le32(profile));
        base.update(&le16(1));
        base.update(&le64(statement.len() as u64));
        base.update(statement);
        CoinState { profile, formal_len: formal_len as u64, base, rounds: 0 }
    }
    pub fn profile(&self) -> u32 {
        self.profile
    }
    pub fn formal_len(&self) -> usize {
        self.formal_len as usize
    }
    pub fn rounds(&self) -> u32 {
        self.rounds
    }
    /// Append Entry(j); j must be the next round.
    pub fn push(&mut self, j: u32, root: &[u8; 64]) {
        assert_eq!(j, self.rounds + 1, "history entries in round order");
        self.base.update(&entry(j, root));
        self.rounds = j;
    }
    /// The first `n` bytes of C_i for the last pushed round i.
    pub fn block(&self, s: &Shape, n: usize) -> Vec<u8> {
        assert!(n as u64 <= self.formal_len);
        let mut h = self.base.clone();
        h.update(&frame(3, &s.descriptor()));
        h.update(&le32(self.rounds));
        h.update(&le64(self.formal_len));
        let mut out = vec![0u8; n];
        h.finalize_xof().read(&mut out);
        out
    }
}

/// The literal full-preimage computation of C_i (no state reuse, full formal length).
pub fn reference_block(profile: u32, formal_len: usize, statement: &[u8], roots: &[[u8; 64]], s: &Shape) -> Vec<u8> {
    let i = roots.len() as u32;
    let mut pre = Vec::with_capacity(DOMAIN.len() + 4 + 10 + statement.len() + 79 * roots.len() + 64);
    pre.extend_from_slice(DOMAIN);
    pre.extend_from_slice(&le32(profile));
    pre.extend_from_slice(&frame(1, statement));
    for (j, r) in roots.iter().enumerate() {
        pre.extend_from_slice(&entry(j as u32 + 1, r));
    }
    pre.extend_from_slice(&frame(3, &s.descriptor()));
    pre.extend_from_slice(&le32(i));
    pre.extend_from_slice(&le64(formal_len as u64));
    shake(&[&pre], formal_len)
}

// ---------------------------------------------------------------- §9 test vectors

/// The inline reference program (§9), ported: profile 0xffffffff, 1,572-byte blocks,
/// three singleton rounds. Returns the printed lines and whether every assertion held.
pub fn vectors() -> (String, bool) {
    const LEN: usize = 1572;
    let statement = b"abc";
    let shapes = [Shape::k(1), Shape { theta: true, ..Default::default() }, Shape { nq: 8, widths: vec![22, 20, 15], ..Default::default() }];
    let bodies: [&[u8]; 3] = [b"", &(0u8..16).collect::<Vec<u8>>(), b"xyz"];
    let mut out = String::new();
    let mut ok = true;
    let mut st = CoinState::new(PROFILE_TEST, LEN, statement);
    let mut roots = vec![];
    let mut blocks = vec![];
    for (i, (s, body)) in shapes.iter().zip(bodies.iter()).enumerate() {
        let r = (i + 1) as u32;
        let root = singleton_root(PROFILE_TEST, r, body);
        roots.push(root);
        st.push(r, &root);
        let raw = st.block(s, LEN);
        // The incremental derivation equals the literal full preimage.
        ok &= raw == reference_block(PROFILE_TEST, LEN, statement, &roots, s);
        // A prefix squeeze is a prefix of the full block.
        ok &= st.block(s, s.used()) == raw[..s.used()];
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        out += &format!("round={r} bytes={} used={} head={}\n", raw.len(), s.used(), hex(&raw[..16]));
        out += &format!("sha3_512={}\n", hex(&Sha3_512::digest(&raw)));
        let d = decode(&raw, s);
        let join = |v: &[u64]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
        if !d.k.is_empty() {
            out += &format!("K={}\n", join(&d.k[0]));
        }
        if let Some(t) = d.theta {
            out += &format!("theta={}\n", join(&t));
        }
        if !d.q.is_empty() {
            out += &format!("q={}\n", join(&d.q.iter().map(|&x| x as u64).collect::<Vec<_>>()));
        }
        if !d.idx.is_empty() {
            out += &format!("indices={}\n", join(&d.idx.iter().map(|&x| x as u64).collect::<Vec<_>>()));
        }
        ok &= d == decode(&raw[..s.used()], s);
        blocks.push(raw);
    }
    // Fallbacks and boundaries.
    ok &= decode(&[0xff; 296], &Shape::k(1)).k == vec![[0; 5]];
    ok &= decode(&[0; 376], &shapes[1]).theta == Some([0, 1, 0, 0, 0]);
    ok &= decode(&vec![0xff; 3 * (8 + 512)], &Shape { nq: 8, ..Default::default() }).q == vec![0; 8];
    ok &= pool(&[le64(P - 1), le64(P)].concat(), 2, 8, P, u64::MAX) == vec![P - 1, 0];
    ok &= pool(&[&(Q - 1).to_le_bytes()[..3], &Q.to_le_bytes()[..3]].concat(), 2, 3, Q, 0x7f_ffff) == vec![Q - 1, 0];
    // Full-history sensitivity: changing root 1 or the statement changes every block.
    let mut changed = roots.clone();
    changed[0] = singleton_root(PROFILE_TEST, 1, b"changed");
    for i in 1..=3 {
        ok &= reference_block(PROFILE_TEST, LEN, statement, &changed[..i], &shapes[i - 1]) != blocks[i - 1];
        ok &= reference_block(PROFILE_TEST, LEN, b"abd", &roots[..i], &shapes[i - 1]) != blocks[i - 1];
    }
    if ok {
        out += "PASS fallback, boundary, prefix, and full-history tests\n";
    }
    (out, ok)
}

/// The expected output of the reference program, as committed in `aggregate/r7-check/`.
pub const EXPECTED_VECTORS: &str = include_str!("../../r7-check/expected.txt");
