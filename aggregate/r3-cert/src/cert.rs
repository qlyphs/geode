//! The epoch authorization certificate: statement binding, commitment, projections and integer
//! lifts, fractional GKR with paired leaves, master and table sumchecks, five WHIR openings,
//! serialization, and the verifier that recomputes every public term.
//!
//! Transcript order (round 3 section 2.5):
//!  1. manifest (statement digest), public u, hint counts, then the WHIR commitment;
//!  2. projection seed; 3. quotients; 4. theta, fractional GKR;
//!  5. bottom GKR claims, then gamma_P, gamma_Q; 6. table claim T;
//!  7. gamma_Z, tau, omega, mu; 8. master and table sumchecks; 9. WHIR opening of 5 claims.

use std::sync::Arc;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::time::Instant;

use p3_commit::MultilinearPcs;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;
use p3_multilinear_util::point::Point;
use p3_sumcheck::layout::{Layout as _, Table, observe_commitment};
use p3_sumcheck::{OpeningBatch, OpeningProtocol, PrescribedPointPcs, TableShape, TableSpec};
use p3_symmetric::MerkleCap;
use rayon::prelude::*;

use crate::field::{EF, F, eq1, eq_pts, eq_table, ef_from_bytes, ef_to_bytes, efb, fi};
use crate::gkr::{self, GkrProof, Layer};
use crate::mlnat::{self, K, L, N, Ntt, QI, Record, SigPublic, ctr};
use crate::pcs::{self, Commitment, Fs, Layout, PcsProof, Tr, shake64, words_to_bytes};
use crate::{fs7, reg7};
use crate::proj::{self, CHUNK, Challenges, TRIALS};
use crate::region::{self, Coeffs, XK, XOFF};
use crate::sumcheck::{self, Pub};
use crate::witness::{SLOTS, Witness};

pub const LOG_TAB: usize = 19;
pub const MANIFEST: usize = 512;
pub const NU_MAX: u8 = 75;

// ---------------------------------------------------------------- layout of the GKR leaves

/// Leaf tree: X region (D leaves), Y region (D leaves), 2^19 paired table leaves, neutral rest.
/// At N = 2048 the table leaves sit in the 2^19 ignored X padding slots (tree = 2D leaves).
#[derive(Clone, Copy, Debug)]
pub struct Tree {
    pub d: usize,
    pub log_dc: usize,
    pub x_off: usize,
    pub y_off: usize,
    pub embedded: bool,
    pub t_off: usize,
}

impl Tree {
    pub fn new(n: usize) -> Self {
        assert!(n.is_power_of_two() && n >= 32);
        let log_dc = 11 + n.trailing_zeros() as usize;
        let dc = 1usize << log_dc;
        let tab = 1usize << LOG_TAB;
        let ceil = |v: usize| v.next_power_of_two().trailing_zeros() as usize;
        if 256 * n == tab {
            Tree { d: log_dc + 1, log_dc, x_off: 0, y_off: dc, embedded: true, t_off: 0 }
        } else if dc >= tab {
            Tree { d: ceil(2 * dc + tab), log_dc, x_off: 0, y_off: dc, embedded: false, t_off: 2 * dc }
        } else {
            Tree { d: ceil(tab + 2 * dc), log_dc, x_off: tab, y_off: tab + dc, embedded: false, t_off: 0 }
        }
    }
    fn kappa(&self, rho: &[EF], off: usize, ls: usize) -> EF {
        (ls..self.d).fold(EF::ONE, |a, t| a * if (off >> t) & 1 == 1 { rho[t] } else { EF::ONE - rho[t] })
    }
    pub fn kx(&self, rho: &[EF]) -> EF {
        self.kappa(rho, self.x_off, self.log_dc)
    }
    pub fn ky(&self, rho: &[EF]) -> EF {
        self.kappa(rho, self.y_off, self.log_dc)
    }
    pub fn kt(&self, rho: &[EF]) -> EF {
        if self.embedded { self.kx(rho) * rho[8] * rho[9] * rho[10] } else { self.kappa(rho, self.t_off, LOG_TAB) }
    }
    pub fn rho_t(&self, rho: &[EF]) -> Vec<EF> {
        if self.embedded {
            rho[..8].iter().chain(rho[11..self.log_dc].iter()).copied().collect()
        } else {
            rho[..LOG_TAB].to_vec()
        }
    }
}

#[inline(always)]
fn table_leaf(theta: EF, th2: EF, j: usize, me: F, mo: F) -> (EF, EF) {
    let j2 = F::from_usize(2 * j);
    let p = -(theta * (me + mo)) + efb(me * (j2 + F::ONE) + mo * j2);
    let q = th2 - theta * F::from_usize(4 * j + 1) + efb(F::from_usize(4 * j * j + 2 * j));
    (p, q)
}

struct SendPtr<T>(*mut T);
unsafe impl<T> Send for SendPtr<T> {}
unsafe impl<T> Sync for SendPtr<T> {}
impl<T> SendPtr<T> {
    #[inline(always)]
    unsafe fn at(&self, i: usize) -> *mut T {
        unsafe { self.0.add(i) }
    }
}

pub(crate) fn leaves(tree: &Tree, w: &Witness, theta: EF, co: &[Coeffs; 3]) -> (Vec<EF>, Vec<EF>) {
    let size = 1usize << tree.d;
    let dc = 1usize << tree.log_dc;
    let mut p = vec![EF::ZERO; size];
    let mut q = vec![EF::ONE; size];
    let th2 = theta * theta;
    let kx = F::from_u64(XK as u64);
    let px = theta.double() - efb(kx);
    let qx0 = th2 - theta * kx;
    let (pp, qp) = (SendPtr(p.as_mut_ptr()), SendPtr(q.as_mut_ptr()));
    (0..dc).into_par_iter().with_min_len(1 << 12).for_each(|b| {
        let slot = b & (SLOTS - 1);
        let (xp, xq) = if slot < L * N {
            let x = w.x[b];
            (px, qx0 + efb(x * (kx - x)))
        } else if tree.embedded {
            let j = ((b >> 11) << 8) | (b & 255);
            table_leaf(theta, th2, j, w.m[2 * j], w.m[2 * j + 1])
        } else {
            (EF::ZERO, EF::ONE)
        };
        let c = &co[w.class[b] as usize];
        let (y, s) = (w.y[b], w.s[b]);
        let kk = c.k[0] + (c.k[1] + c.k[2] * s) * s;
        let yp = theta.double() - efb(kk);
        let yq = th2 - theta * kk + efb(y * (kk - y));
        unsafe {
            *pp.at(tree.x_off + b) = xp;
            *qp.at(tree.x_off + b) = xq;
            *pp.at(tree.y_off + b) = yp;
            *qp.at(tree.y_off + b) = yq;
        }
    });
    if !tree.embedded {
        (0..1usize << LOG_TAB).into_par_iter().with_min_len(1 << 12).for_each(|j| {
            let (a, b) = table_leaf(theta, th2, j, w.m[2 * j], w.m[2 * j + 1]);
            unsafe {
                *pp.at(tree.t_off + j) = a;
                *qp.at(tree.t_off + j) = b;
            }
        });
    }
    (p, q)
}

// ---------------------------------------------------------------- statement and manifest

pub fn statement_digest(records: &[Record]) -> [u8; 64] {
    let mut buf = Vec::new();
    buf.extend_from_slice(&(records.len() as u32).to_le_bytes());
    for (i, r) in records.iter().enumerate() {
        assert_eq!(r.pk.len(), mlnat::PK_BYTES);
        assert!(r.ctx.len() <= 255);
        buf.extend_from_slice(&(i as u32).to_le_bytes());
        buf.push(r.ctx.len() as u8);
        buf.extend_from_slice(&r.ctx);
        buf.extend_from_slice(&(r.msg.len() as u32).to_le_bytes());
        buf.extend_from_slice(&r.msg);
        buf.extend_from_slice(&r.pk);
    }
    shake64(&[b"r3-cert/statement", &buf])
}

pub fn parameter_digest(n: usize) -> [u8; 64] {
    let tree = Tree::new(n);
    let s = format!(
        "r3-cert v1; Goldilocks^5 (x^5-3); WHIR p3-whir=0.8.0 JohnsonBound 272 pow 0 profile {:?}; \
         SHAKE256-64 merkle 0x00/0x01, FS 0x02; trials {TRIALS}; chunk {CHUNK}; V 40-bit; \
         table 2^20 paired; tree {:?}; layout X|Y|S (2^{}) + m_even|m_odd (2^19)",
        pcs::profile(stacked_vars(n)),
        tree,
        tree.log_dc
    );
    shake64(&[s.as_bytes()])
}

pub fn manifest(records: &[Record]) -> Vec<u8> {
    let n = records.len();
    let mut m = Vec::with_capacity(MANIFEST);
    m.extend_from_slice(b"QLYAUTH3");
    m.extend_from_slice(&3u32.to_le_bytes());
    m.extend_from_slice(&parameter_digest(n));
    m.extend_from_slice(&(n as u32).to_le_bytes());
    m.extend_from_slice(&statement_digest(records));
    m.extend_from_slice(&(proj::chunks(n) as u32).to_le_bytes());
    m.resize(MANIFEST, 0);
    m
}

/// Lab manifest for standalone statements under the QLYAUTH7 transcript: "QLYLAB07",
/// LE32(lab profile id), 64 reserved zero bytes, LE4 N, the statement digest, LE4 chunk count,
/// zero padding. Lab only; the chain uses QLYAUTH7 (chain::manifest_v7).
pub fn manifest_lab7(records: &[Record]) -> Vec<u8> {
    let n = records.len();
    let mut m = Vec::with_capacity(MANIFEST);
    m.extend_from_slice(b"QLYLAB07");
    m.extend_from_slice(&reg7::lab_profile(n).to_le_bytes());
    m.extend_from_slice(&[0u8; 64]);
    m.extend_from_slice(&(n as u32).to_le_bytes());
    m.extend_from_slice(&statement_digest(records));
    m.extend_from_slice(&(proj::chunks(n) as u32).to_le_bytes());
    m.resize(MANIFEST, 0);
    m
}

/// The manifest a standalone statement is proven against under `o`.
pub fn manifest_for(records: &[Record], o: &Opts) -> Vec<u8> {
    if o.v7 { manifest_lab7(records) } else { manifest(records) }
}

/// 4-byte profile identifier of the registry entry for n signatures: "Q4" || version || log2 cells.
pub fn profile_id(n: usize) -> u32 {
    u32::from_le_bytes([b'Q', b'4', 1, stacked_vars(n) as u8])
}

pub fn stacked_vars(n: usize) -> usize {
    let dc = n * SLOTS;
    (3 * dc + (2 << LOG_TAB)).next_power_of_two().trailing_zeros() as usize
}

pub fn pcs_security_bits(n: usize) -> (f64, f64) {
    let (pcs_, _) = pcs::make_pcs(stacked_vars(n), 5);
    let sec = pcs_.prescribed_security(&protocol(Tree::new(n).log_dc)).expect("security");
    (sec.error().bits(), sec.log2_max_candidates)
}

fn protocol(log_dc: usize) -> OpeningProtocol {
    OpeningProtocol::new(vec![
        TableSpec::new(TableShape::new(log_dc, 3), vec![OpeningBatch::new(vec![0, 1, 2], vec![])]),
        TableSpec::new(TableShape::new(LOG_TAB, 2), vec![OpeningBatch::new(vec![0, 1], vec![])]),
    ])
}

fn p3_point(my: &[EF]) -> Point<EF> {
    Point::new(my.iter().rev().copied().collect::<Vec<_>>())
}

// ---------------------------------------------------------------- certificate

#[derive(Clone)]
pub struct Cert {
    pub manifest: Vec<u8>,
    pub u: Vec<u8>,
    pub nu: Vec<u8>,
    pub quot: Vec<u8>,
    pub comm: [u8; 64],
    pub gkr: GkrProof,
    /// QLYAUTH7 only: the explicit (P_leaf, Q_leaf) pair of round 279 (80 bytes).
    pub leaf_pair: Option<[EF; 2]>,
    pub t_claim: EF,
    pub master: Vec<[EF; 4]>,
    pub table: Vec<[EF; 2]>,
    pub whir: Vec<u8>,
}

#[derive(Debug, Default, Clone)]
pub struct Sizes {
    pub manifest: usize,
    pub u: usize,
    pub nu: usize,
    pub quot: usize,
    pub comm: usize,
    pub gkr: usize,
    pub leaf_pair: usize,
    pub t_claim: usize,
    pub master: usize,
    pub table: usize,
    pub whir_len: usize,
    pub whir: usize,
    pub whir_evals: usize,
    pub total: usize,
}

impl Cert {
    pub fn to_bytes(&self) -> (Vec<u8>, Sizes) {
        let mut b = Vec::new();
        let mut sz = Sizes::default();
        let mut mark = |b: &Vec<u8>, last: &mut usize| {
            let v = b.len() - *last;
            *last = b.len();
            v
        };
        let mut last = 0;
        b.extend_from_slice(&self.manifest);
        sz.manifest = mark(&b, &mut last);
        b.extend_from_slice(&self.u);
        sz.u = mark(&b, &mut last);
        b.extend_from_slice(&self.nu);
        sz.nu = mark(&b, &mut last);
        b.extend_from_slice(&self.quot);
        sz.quot = mark(&b, &mut last);
        b.extend_from_slice(&self.comm);
        sz.comm = mark(&b, &mut last);
        for l in &self.gkr.layers {
            for r in &l.rounds {
                r.iter().for_each(|x| ef_to_bytes(x, &mut b));
            }
            l.finals.iter().for_each(|x| ef_to_bytes(x, &mut b));
        }
        sz.gkr = mark(&b, &mut last);
        if let Some(lp) = &self.leaf_pair {
            lp.iter().for_each(|x| ef_to_bytes(x, &mut b));
        }
        sz.leaf_pair = mark(&b, &mut last);
        ef_to_bytes(&self.t_claim, &mut b);
        sz.t_claim = mark(&b, &mut last);
        for r in &self.master {
            r.iter().for_each(|x| ef_to_bytes(x, &mut b));
        }
        sz.master = mark(&b, &mut last);
        for r in &self.table {
            r.iter().for_each(|x| ef_to_bytes(x, &mut b));
        }
        sz.table = mark(&b, &mut last);
        b.extend_from_slice(&(self.whir.len() as u32).to_le_bytes());
        sz.whir_len = mark(&b, &mut last);
        b.extend_from_slice(&self.whir);
        sz.whir = mark(&b, &mut last);
        sz.whir_evals = 5 * 40;
        sz.total = b.len();
        (b, sz)
    }

    /// Strict parsing for a statement of n records: exact lengths, canonical field elements,
    /// no trailing bytes.
    pub fn from_bytes(n: usize, b: &[u8]) -> Result<Cert, Reject> {
        Self::from_bytes_v(n, b, false)
    }

    /// `v7`: the QLYAUTH7 layout, with the 80-byte (P_leaf, Q_leaf) pair after the GKR section.
    pub fn from_bytes_v(n: usize, b: &[u8], v7: bool) -> Result<Cert, Reject> {
        let tree = Tree::new(n);
        let mut cur = 0usize;
        let mut take = |cur: &mut usize, len: usize| -> Result<Vec<u8>, Reject> {
            if *cur + len > b.len() {
                return Err(Reject::Parse("truncated"));
            }
            let s = b[*cur..*cur + len].to_vec();
            *cur += len;
            Ok(s)
        };
        let manifest = take(&mut cur, MANIFEST)?;
        let u = take(&mut cur, 1024 * n)?;
        let nu = take(&mut cur, n)?;
        let quot = take(&mut cur, 5 * TRIALS * proj::chunks(n))?;
        let comm: [u8; 64] = take(&mut cur, 64)?.try_into().unwrap();
        let rd = |cur: &mut usize| -> Result<EF, Reject> {
            if *cur + 40 > b.len() {
                return Err(Reject::Parse("truncated"));
            }
            let v = ef_from_bytes(&b[*cur..*cur + 40]).ok_or(Reject::Parse("non-canonical field element"))?;
            *cur += 40;
            Ok(v)
        };
        let mut layers = Vec::with_capacity(tree.d);
        for k in 0..tree.d {
            let mut rounds = Vec::with_capacity(k);
            for _ in 0..k {
                rounds.push([rd(&mut cur)?, rd(&mut cur)?]);
            }
            let finals = [rd(&mut cur)?, rd(&mut cur)?, rd(&mut cur)?, rd(&mut cur)?];
            layers.push(Layer { rounds, finals });
        }
        let leaf_pair = if v7 { Some([rd(&mut cur)?, rd(&mut cur)?]) } else { None };
        let t_claim = rd(&mut cur)?;
        let mut master = Vec::with_capacity(tree.log_dc);
        for _ in 0..tree.log_dc {
            master.push([rd(&mut cur)?, rd(&mut cur)?, rd(&mut cur)?, rd(&mut cur)?]);
        }
        let mut table = Vec::with_capacity(LOG_TAB);
        for _ in 0..LOG_TAB {
            table.push([rd(&mut cur)?, rd(&mut cur)?]);
        }
        if cur + 4 > b.len() {
            return Err(Reject::Parse("truncated"));
        }
        let wl = u32::from_le_bytes(b[cur..cur + 4].try_into().unwrap()) as usize;
        cur += 4;
        if cur + wl != b.len() {
            return Err(Reject::Parse("length mismatch / trailing bytes"));
        }
        let whir = b[cur..].to_vec();
        Ok(Cert { manifest, u, nu, quot, comm, gkr: GkrProof { layers }, leaf_pair, t_claim, master, table, whir })
    }
}

#[derive(Debug, Clone)]
pub enum Reject {
    Parse(&'static str),
    Manifest,
    HintCountByte(usize),
    Gkr(String),
    Master(&'static str),
    Table(&'static str),
    Whir(String),
    Chain(String),
    /// Unregistered or mismatched profile.
    Profile(String),
    /// QLYAUTH7 round 279: the transmitted pair differs from the derived one.
    LeafPair,
    /// QLYAUTH7: the registered-round adapter was poisoned or did not finish.
    Transcript(String),
    /// Hidden-u lab profiles: a hash-side (Keccak GKR or link) check failed.
    Hash(String),
}

/// (current, lifetime peak) physical footprint of this process in bytes (macOS rusage v4).
#[cfg(target_os = "macos")]
pub fn footprint() -> (u64, u64) {
    let mut info: libc::rusage_info_v4 = unsafe { std::mem::zeroed() };
    let rc = unsafe { libc::proc_pid_rusage(std::process::id() as i32, libc::RUSAGE_INFO_V4, &mut info as *mut _ as *mut libc::rusage_info_t) };
    if rc == 0 { (info.ri_phys_footprint, info.ri_lifetime_max_phys_footprint) } else { (0, 0) }
}

/// (current, lifetime peak) resident set of this process in bytes (Linux: VmRSS, VmHWM). The
/// resident set includes file pages of SSD-backed arrays that are currently in RAM.
#[cfg(not(target_os = "macos"))]
pub fn footprint() -> (u64, u64) {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let kb = |k: &str| s.lines().find(|l| l.starts_with(k)).and_then(|l| l.split_whitespace().nth(1)).and_then(|v| v.parse::<u64>().ok()).unwrap_or(0) * 1024;
    (kb("VmRSS:"), kb("VmHWM:"))
}

/// (bytes read from storage, bytes written to storage) by this process so far (Linux
/// /proc/self/io read_bytes, write_bytes; zero elsewhere).
pub fn disk_io() -> (u64, u64) {
    let s = std::fs::read_to_string("/proc/self/io").unwrap_or_default();
    let v = |k: &str| s.lines().find(|l| l.starts_with(k)).and_then(|l| l.split_whitespace().nth(1)).and_then(|v| v.parse::<u64>().ok()).unwrap_or(0);
    (v("read_bytes:"), v("write_bytes:"))
}

pub struct Timer {
    /// (phase, ms, footprint at end, lifetime peak footprint at end, peak live heap within
    /// the phase, live heap at end)
    pub phases: Vec<(String, f64, u64, u64, usize, usize)>,
    /// Per phase: (bytes read, bytes written) from storage within the phase, live SSD-backed
    /// bytes at the end, and the process resident peak so far.
    pub io: Vec<(u64, u64, usize, u64)>,
    t: Instant,
    io0: (u64, u64),
}
impl Timer {
    pub fn new() -> Self {
        crate::alloc::reset_peak();
        Timer { phases: vec![], io: vec![], t: Instant::now(), io0: disk_io() }
    }
    pub fn lap(&mut self, name: &str) {
        let ms = self.t.elapsed().as_secs_f64() * 1e3;
        let (cur, peak) = footprint();
        let (live, hpeak) = crate::alloc::heap();
        self.phases.push((name.to_string(), ms, cur, peak, hpeak, live));
        let io = disk_io();
        self.io.push((io.0.saturating_sub(self.io0.0), io.1.saturating_sub(self.io0.1), crate::alloc::spill().0, peak));
        if std::env::var("H9_PROGRESS").is_ok() {
            // Live progress for long runs (stderr; the full table is printed at the end).
            eprintln!("progress: {ms:.0} ms, live {} MiB, disk-backed {} MiB, read {} MiB, written {} MiB: {name}", live >> 20, crate::alloc::spill().0 >> 20, (io.0.saturating_sub(self.io0.0)) >> 20, (io.1.saturating_sub(self.io0.1)) >> 20);
        }
        self.io0 = io;
        crate::alloc::reset_peak();
        self.t = Instant::now();
    }
    pub fn total(&self) -> f64 {
        self.phases.iter().map(|p| p.1).sum()
    }
}
impl Default for Timer {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------- public sums (shared formulas)

/// Per-signature public sums. The eqR-weighted fields are filled only by the verifier.
#[derive(Clone)]
struct SigSums {
    d: [u64; TRIALS],
    ss: [i64; TRIALS],
    sr: [[i64; 3]; TRIALS],
    srho: [EF; 3],
    pz: [EF; TRIALS],
    rr: [[EF; 3]; TRIALS],
    wx: EF,
    wy: [EF; 3],
}

#[allow(clippy::too_many_arguments)]
fn sig_sums(i: usize, s_cent: &[i32], ch: &Challenges, bu: &[u32], u: &[u8], eq_rho: &[EF], eq_r: Option<&[EF]>) -> SigSums {
    let base = i * SLOTS;
    let mut out = SigSums {
        d: [0; TRIALS],
        ss: [0; TRIALS],
        sr: [[0; 3]; TRIALS],
        srho: [EF::ZERO; 3],
        pz: [EF::ZERO; TRIALS],
        rr: [[EF::ZERO; 3]; TRIALS],
        wx: EF::ZERO,
        wy: [EF::ZERO; 3],
    };
    for t in 0..K * N {
        out.srho[region::class_of(u[t])] += eq_rho[base + t];
    }
    for j in 0..TRIALS {
        out.d[j] = ch.d_part(j, i, bu);
        let s = &s_cent[j * L * N..(j + 1) * L * N];
        out.ss[j] = s.iter().map(|&v| v as i64).sum();
        for t in 0..K * N {
            out.sr[j][region::class_of(u[t])] += ch.r_centered(j, i, t);
        }
    }
    if let Some(er) = eq_r {
        for t in 0..L * N {
            out.wx += er[base + t] * eq_rho[base + t];
        }
        for t in 0..K * N {
            out.wy[region::class_of(u[t])] += er[base + t] * eq_rho[base + t];
        }
        for j in 0..TRIALS {
            let s = &s_cent[j * L * N..(j + 1) * L * N];
            out.pz[j] = (0..L * N).map(|t| er[base + t] * fi(s[t] as i64)).sum();
            let mut acc = [EF::ZERO; 3];
            for t in 0..K * N {
                acc[region::class_of(u[t])] += er[base + t] * fi(ch.r_centered(j, i, t));
            }
            out.rr[j] = acc;
        }
    }
    out
}

/// Chunk-level aggregation of the signature sums.
struct Agg {
    d: Vec<[u64; TRIALS]>,
    ss: Vec<[i128; TRIALS]>,
    sr: Vec<[[i128; 3]; TRIALS]>,
    pz: Vec<[EF; TRIALS]>,
    rr: Vec<[[EF; 3]; TRIALS]>,
    srho: [EF; 3],
    wx: EF,
    wy: [EF; 3],
}

fn aggregate(sums: &[SigSums], n: usize) -> Agg {
    let nc = proj::chunks(n);
    let mut a = Agg {
        d: vec![[0; TRIALS]; nc],
        ss: vec![[0; TRIALS]; nc],
        sr: vec![[[0; 3]; TRIALS]; nc],
        pz: vec![[EF::ZERO; TRIALS]; nc],
        rr: vec![[[EF::ZERO; 3]; TRIALS]; nc],
        srho: [EF::ZERO; 3],
        wx: EF::ZERO,
        wy: [EF::ZERO; 3],
    };
    for (i, s) in sums.iter().enumerate() {
        let c = i / CHUNK;
        for j in 0..TRIALS {
            a.d[c][j] = (a.d[c][j] + s.d[j]) % mlnat::Q as u64;
            a.ss[c][j] += s.ss[j] as i128;
            for cl in 0..3 {
                a.sr[c][j][cl] += s.sr[j][cl] as i128;
                a.rr[c][j][cl] += s.rr[j][cl];
            }
            a.pz[c][j] += s.pz[j];
        }
        for cl in 0..3 {
            a.srho[cl] += s.srho[cl];
            a.wy[cl] += s.wy[cl];
        }
        a.wx += s.wx;
    }
    a
}

fn fi128(x: i128) -> F {
    let p = crate::field::P as i128;
    F::from_u64(x.rem_euclid(p) as u64)
}

/// Everything the claimed master sum and its terminal check depend on, after step 7.
struct Ctx {
    n: usize,
    tree: Tree,
    theta: EF,
    rho: Vec<EF>,
    p_leaf: EF,
    q_leaf: EF,
    gp: EF,
    gq: EF,
    t_claim: EF,
    gz: EF,
    tau: Vec<EF>,
    omega: Vec<EF>,
    mu: Vec<[EF; TRIALS]>,
    quot: Vec<[i64; TRIALS]>,
    nu: Vec<u8>,
}

fn claimed_sum(c: &Ctx, a: &Agg, co: &[Coeffs; 3]) -> EF {
    let th = c.theta;
    let th2 = th * th;
    let kxf = F::from_u64(XK as u64);
    let (kx, ky, kt) = (c.tree.kx(&c.rho), c.tree.ky(&c.rho), c.tree.kt(&c.rho));
    let pad = c.rho[8] * c.rho[9] * c.rho[10];
    let xm = kx * (EF::ONE - pad);
    let mut pub_p = xm * (th.double() - efb(kxf));
    let mut pub_q = xm * (th2 - th * kxf);
    for cl in 0..3 {
        pub_p += ky * a.srho[cl] * (th.double() - efb(co[cl].k[0]));
        pub_q += ky * a.srho[cl] * (th2 - th * co[cl].k[0]);
    }
    let rt = c.tree.rho_t(&c.rho);
    let mut m1 = EF::ZERO;
    let mut m2 = EF::ZERO;
    for t in 0..rt.len() {
        let w = F::from_u64(1u64 << t);
        m1 += rt[t] * w;
        m2 += rt[t] * (w * w);
        for t2 in t + 1..rt.len() {
            m2 += rt[t] * rt[t2] * F::from_u64(2u64 << (t + t2));
        }
    }
    let four = F::from_u64(4);
    pub_q += kt * (th2 - th * (m1 * four + EF::ONE) + m2 * four + m1.double());
    pub_q += EF::ONE - xm - ky - kt;
    let mut s = c.gp * (c.p_leaf - kt * c.t_claim - pub_p) + c.gq * (c.q_leaf - pub_q);
    for i in 0..c.n {
        s += c.omega[i] * F::from_u8(c.nu[i]);
    }
    for ch in 0..proj::chunks(c.n) {
        for j in 0..TRIALS {
            let mut rhs = fi128(QI as i128 * c.quot[ch][j] as i128 + ctr(a.d[ch][j] as u32) as i128 + XOFF as i128 * a.ss[ch][j]);
            for cl in 0..3 {
                rhs += co[cl].st[0] * fi128(a.sr[ch][j][cl]);
            }
            s += c.mu[ch][j] * rhs;
        }
    }
    s
}

/// The nine public multilinear extensions at the master point r.
fn public_at_r(c: &Ctx, a: &Agg, co: &[Coeffs; 3], r: &[EF]) -> [EF; 9] {
    let (kx, ky) = (c.tree.kx(&c.rho), c.tree.ky(&c.rho));
    let kxf = F::from_u64(XK as u64);
    let wx = kx * a.wx;
    let wy: [EF; 3] = core::array::from_fn(|cl| ky * a.wy[cl]);
    let mut pz = EF::ZERO;
    let mut pr = [EF::ZERO; 3];
    for ch in 0..proj::chunks(c.n) {
        for j in 0..TRIALS {
            pz += c.mu[ch][j] * a.pz[ch][j];
            for cl in 0..3 {
                pr[cl] += c.mu[ch][j] * a.rr[ch][j][cl];
            }
        }
    }
    let sum_k = |idx: usize| -> EF { (0..3).map(|cl| wy[cl] * co[cl].k[idx]).sum() };
    let sum_st = |idx: usize| -> EF { (0..3).map(|cl| pr[cl] * co[cl].st[idx]).sum() };
    let eqrt = eq_pts(r, &c.tau);
    let log_n = c.n.trailing_zeros() as usize;
    let eq_hi = eq_table(&r[11..11 + log_n]);
    let om: EF = (0..c.n).map(|i| c.omega[i] * eq_hi[i]).sum();
    let wy_all: EF = wy.iter().copied().sum();
    let pr_all: EF = pr.iter().copied().sum();
    let g = c.gp + c.gq * c.theta;
    [
        c.gq * wx * kxf + pz,
        -(c.gq * wx),
        c.gq * sum_k(0) - pr_all,
        -(c.gq * wy_all),
        c.gq * sum_k(1),
        c.gq * sum_k(2),
        -(g * sum_k(1)) - c.gz * eqrt - sum_st(1),
        -(g * sum_k(2)) + om - sum_st(2),
        c.gz * eqrt,
    ]
}

// ---------------------------------------------------------------- transcript backends

/// Projection challenge source: the QLYAUTH4 seed of its separate XOF, or (QLYAUTH7) the
/// decoded F_q pool of registered round 1.
pub enum ProjSrc {
    Seed([u8; 64]),
    Values(Vec<u32>),
}

impl ProjSrc {
    pub fn challenges(&self, ntt: &Ntt, n: usize) -> Challenges {
        match self {
            ProjSrc::Seed(s) => Challenges::sample(ntt, s, n),
            ProjSrc::Values(v) => Challenges::from_values(ntt, v, n),
        }
    }
    /// A 64-byte identifier of the projection challenges (the seed, or a digest of the pool).
    pub fn id(&self) -> [u8; 64] {
        match self {
            ProjSrc::Seed(s) => *s,
            ProjSrc::Values(v) => {
                let b: Vec<u8> = v.iter().flat_map(|x| x.to_le_bytes()).collect();
                shake64(&[b"r3-cert/proj-values", &b])
            }
        }
    }
}

pub type Witness3 = p3_sumcheck::layout::Witness<F>;

/// What the prover and verifier need from a profile: its transcript (frontend calls through
/// `Fs`) and its PCS bound to that transcript.
pub trait Backend: Fs {
    type PData;
    type Proof: serde::Serialize + serde::de::DeserializeOwned;
    const V7: bool;
    fn fold0(&self) -> usize;
    fn commit(&mut self, wit: Witness3) -> (Commitment, Self::PData);
    fn observe_commitment(&mut self, c: &Commitment);
    fn projection(&mut self) -> ProjSrc;
    fn absorb_quotients(&mut self, q: &[[i64; TRIALS]], bytes: &[u8]);
    fn theta(&mut self) -> (EF, usize);
    fn open_at(&mut self, pd: Self::PData, proto: &OpeningProtocol, pts: &[Point<EF>]) -> (Self::Proof, Vec<Vec<EF>>);
    fn verify_at(&mut self, c: &Commitment, proof: &Self::Proof, proto: &OpeningProtocol, pts: &[Point<EF>]) -> Result<Vec<Vec<EF>>, String>;
    fn transcript_error(&self) -> Option<String>;
}

/// QLYAUTH3 / QLYAUTH4: one SerializingChallenger64 over SHAKE256, frontend and WHIR.
pub struct B4 {
    pub tr: Tr,
    pub pcs: pcs::Pcs,
    fold0: usize,
}

impl B4 {
    pub fn new(n: usize, alt: bool, inject: pcs::Inject, man: &[u8], ubytes: &[u8], nu: &[u8]) -> Self {
        let nv = stacked_vars(n);
        let (pcs, fold0) = if alt { pcs::make_pcs_alt(nv, 5) } else { pcs::make_pcs(nv, 5) };
        let mut tr = Tr::new();
        tr.inject = inject;
        bind_statement(&mut tr, man, ubytes, nu);
        B4 { tr, pcs, fold0 }
    }
}

impl Fs for B4 {
    fn absorb_ef(&mut self, x: EF) {
        self.tr.absorb_ef(x)
    }
    fn sample_ef(&mut self) -> EF {
        self.tr.sample_ef()
    }
    fn inject(&self) -> pcs::Inject {
        self.tr.inject
    }
}

impl Backend for B4 {
    type PData = p3_whir::WhirProverData<F, EF, pcs::MyMmcs, Layout>;
    type Proof = PcsProof;
    const V7: bool = false;
    fn fold0(&self) -> usize {
        self.fold0
    }
    fn commit(&mut self, wit: Witness3) -> (Commitment, Self::PData) {
        self.pcs.commit(wit, &mut self.tr.ch).expect("commit")
    }
    fn observe_commitment(&mut self, c: &Commitment) {
        observe_commitment::<F, _, _>(&mut self.tr.ch, c.clone());
    }
    fn projection(&mut self) -> ProjSrc {
        ProjSrc::Seed(self.tr.sample_seed())
    }
    fn absorb_quotients(&mut self, q: &[[i64; TRIALS]], _bytes: &[u8]) {
        for c in q {
            for &v in c {
                self.tr.absorb_u64((v + (1i64 << proj::VBITS)) as u64);
            }
        }
    }
    fn theta(&mut self) -> (EF, usize) {
        self.tr.sample_theta()
    }
    fn open_at(&mut self, pd: Self::PData, proto: &OpeningProtocol, pts: &[Point<EF>]) -> (Self::Proof, Vec<Vec<EF>>) {
        let p = self.pcs.open_at(pd, proto, pts, &mut self.tr.ch).expect("open");
        let ev = p.evals.iter().map(|e| e.current().to_vec()).collect();
        (p, ev)
    }
    fn verify_at(&mut self, c: &Commitment, proof: &Self::Proof, proto: &OpeningProtocol, pts: &[Point<EF>]) -> Result<Vec<Vec<EF>>, String> {
        self.pcs.verify_at(c, proof, proto, pts, &mut self.tr.ch).map(|v| v.iter().map(|e| e.current().to_vec()).collect()).map_err(|e| format!("{e:?}"))
    }
    fn transcript_error(&self) -> Option<String> {
        None
    }
}

/// QLYAUTH7: the registered-round adapter (frontend and WHIR) and the global Merkle oracle.
pub struct B7 {
    pub tr: reg7::Tr7,
    pub pcs: pcs::Pcs7,
    fold0: usize,
    pub leaf_calls: Arc<AtomicU64>,
}

/// The round table a PCS configuration induces for profile `profile` and n signatures.
pub fn table_of(profile: u32, n: usize, pcs: &pcs::Pcs7) -> reg7::Table {
    reg7::build_table(profile, n, &reg7::front(n), &p3_whir::WhirShape::new(&**pcs, 2))
}

/// The registered round table, or None for an unregistered profile or a count it does not fix.
/// Production registers 0x00070001 at N = 2048 only; `lab` admits the lab profiles 0xfff700xx.
pub fn registered_table(profile: u32, n: usize, lab: bool) -> Option<Arc<reg7::Table>> {
    let ok = if lab { n.is_power_of_two() && (32..=2048).contains(&n) && profile == reg7::lab_profile(n) } else { profile == fs7::PROFILE_V7 && n == 2048 };
    if !ok {
        return None;
    }
    let (p, _) = pcs::make_pcs7(stacked_vars(n), 5, false, profile, Arc::new(AtomicU32::new(0)), Arc::new(AtomicU64::new(0)));
    let t = table_of(profile, n, &p);
    if profile == fs7::PROFILE_V7 {
        // The registration (spec §2.1, §4): 354 rounds, 350 singletons, L = 173,568, 365,136 used.
        assert!(t.len() == 354 && t.scalar_rounds() == 350 && t.formal_len == fs7::COIN_BYTES_V7 && t.used_total() == 365_136, "profile 0x00070001 table");
    }
    Some(Arc::new(t))
}

impl B7 {
    /// `table`: the verifier's registered table; None builds the prover's own from its PCS.
    pub fn new(n: usize, profile: u32, x: &[u8], alt: bool, inject: pcs::Inject, table: Option<Arc<reg7::Table>>) -> Self {
        let tree = Arc::new(AtomicU32::new(0));
        let leaf_calls = Arc::new(AtomicU64::new(0));
        let (pcs, fold0) = pcs::make_pcs7(stacked_vars(n), 5, alt, profile, tree.clone(), leaf_calls.clone());
        let table = table.unwrap_or_else(|| Arc::new(table_of(profile, n, &pcs)));
        let tr = reg7::Tr7::new(table, x, tree, inject);
        B7 { tr, pcs, fold0, leaf_calls }
    }
}

impl Fs for B7 {
    fn absorb_ef(&mut self, x: EF) {
        self.tr.absorb_ef(x)
    }
    fn sample_ef(&mut self) -> EF {
        self.tr.sample_ef()
    }
    fn inject(&self) -> pcs::Inject {
        self.tr.ch.inject
    }
}

impl Backend for B7 {
    type PData = p3_whir::WhirProverData<F, EF, reg7::Mmcs7, Layout>;
    type Proof = pcs::PcsProof7;
    const V7: bool = true;
    fn fold0(&self) -> usize {
        self.fold0
    }
    fn commit(&mut self, wit: Witness3) -> (Commitment, Self::PData) {
        self.pcs.commit(wit, &mut self.tr.ch).expect("commit")
    }
    fn observe_commitment(&mut self, c: &Commitment) {
        observe_commitment::<F, _, _>(&mut self.tr.ch, c.clone());
    }
    fn projection(&mut self) -> ProjSrc {
        ProjSrc::Values(self.tr.ch.sample_fq())
    }
    fn absorb_quotients(&mut self, _q: &[[i64; TRIALS]], bytes: &[u8]) {
        self.tr.ch.observe_bytes(bytes);
    }
    fn theta(&mut self) -> (EF, usize) {
        (self.tr.ch.sample_theta(), 0)
    }
    fn open_at(&mut self, pd: Self::PData, proto: &OpeningProtocol, pts: &[Point<EF>]) -> (Self::Proof, Vec<Vec<EF>>) {
        let p = self.pcs.open_at(pd, proto, pts, &mut self.tr.ch).expect("open");
        let ev = p.evals.iter().map(|e| e.current().to_vec()).collect();
        (p, ev)
    }
    fn verify_at(&mut self, c: &Commitment, proof: &Self::Proof, proto: &OpeningProtocol, pts: &[Point<EF>]) -> Result<Vec<Vec<EF>>, String> {
        self.pcs.verify_at(c, proof, proto, pts, &mut self.tr.ch).map(|v| v.iter().map(|e| e.current().to_vec()).collect()).map_err(|e| format!("{e:?}"))
    }
    fn transcript_error(&self) -> Option<String> {
        let ch = &self.tr.ch;
        match &ch.error {
            Some(e) => Some(e.clone()),
            None if !ch.finished() => Some(format!("transcript stopped at round {} of {}", ch.round(), ch.table().len())),
            None => None,
        }
    }
}

/// Adapter instrumentation after a QLYAUTH7 run (prover or verifier).
#[derive(Clone)]
pub struct Inspect7 {
    pub table: Arc<reg7::Table>,
    pub stats: reg7::Stats,
    pub log: Option<Vec<reg7::Logged>>,
    pub leaf_calls: u64,
    pub error: Option<String>,
}

impl Inspect7 {
    fn of(b: &B7) -> Self {
        Inspect7 { table: Arc::new(b.tr.ch.table().clone()), stats: b.tr.ch.stats.clone(), log: b.tr.ch.log.clone(), leaf_calls: b.leaf_calls.load(Ordering::Relaxed), error: b.transcript_error() }
    }
}

// ---------------------------------------------------------------- prover

pub struct ProverReport {
    pub theta_rejections: usize,
    pub gkr_leaves_log: usize,
    pub stacked_vars: usize,
    pub quotient_inexact: usize,
    pub max_abs_v: i64,
    pub evals_match_whir: bool,
    pub seed: [u8; 64],
    pub theta: EF,
    /// QLYAUTH7 only: a poisoned or unfinished registered-round transcript.
    pub transcript_error: Option<String>,
    /// QLYAUTH7 only: adapter instrumentation.
    pub inspect: Option<Inspect7>,
}

/// Test-only deviations from the protocol. `Opts::default()` is the protocol; every soundness
/// control that weakens it is selected here, on both the prover and the verifier side, so the
/// statement, the profile and the challenge schedule stay identical.
#[derive(Clone, Debug, Default)]
pub struct Opts {
    /// Added to the first quotient (soundness tests only).
    pub quot_delta: i64,
    /// UNSAFE control: the S^3 = S zerocheck weight gamma_Z is still sampled, then replaced by 0.
    pub drop_ternarity: bool,
    /// Gruen round challenges replaced by fixed values (both sides).
    pub inject: pcs::Inject,
    /// Prover only: commit or open with a layout other than the verifier-derived one.
    pub layout: LayoutVariant,
    /// Standalone statements under the QLYAUTH7 transcript (lab profile 0xfff700xx) instead of
    /// QLYAUTH3/QLYAUTH4.
    pub v7: bool,
    /// QLYAUTH7: record every begun round (root, body, coin prefix) for the acceptance gates.
    pub log7: bool,
}

/// Prover-side layout deviations; the verifier always derives the canonical layout.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub enum LayoutVariant {
    #[default]
    Canonical,
    /// [m_even, m_odd] committed as the first table, [X, Y, S] second.
    SwapTables,
    /// Columns committed as [Y, X, S].
    SwapColumns,
    /// Columns opened in the order [Y, X, S].
    ClaimOrder,
    /// WHIR profile with another folding schedule than the registry's.
    Profile,
}

/// Statement binding, step 1 of the transcript: the verifier-derived manifest, public u and
/// hint counts, each as a domain-separated digest, before any challenge.
pub fn bind_statement(tr: &mut Tr, manifest: &[u8], ubytes: &[u8], nu: &[u8]) {
    tr.absorb_bytes(b"manifest", manifest);
    tr.absorb_bytes(b"public-u", ubytes);
    tr.absorb_bytes(b"hint-counts", nu);
}

/// The verifier's first frontend challenges for a statement and certificate bytes: the
/// projection seed (after statement and commitment) and theta (after the quotients).
pub fn prefix_challenges(records: &[Record], bytes: &[u8]) -> Result<([u8; 64], EF), Reject> {
    prefix_challenges_with(&manifest(records), records.len(), bytes)
}

pub fn prefix_challenges_with(man: &[u8], n: usize, bytes: &[u8]) -> Result<([u8; 64], EF), Reject> {
    let cert = Cert::from_bytes(n, bytes)?;
    let mut tr = Tr::new();
    bind_statement(&mut tr, man, &cert.u, &cert.nu);
    let comm: Commitment = MerkleCap::new(vec![core::array::from_fn(|i| u64::from_le_bytes(cert.comm[8 * i..8 * i + 8].try_into().unwrap()))]);
    observe_commitment::<F, _, _>(&mut tr.ch, comm);
    let seed = tr.sample_seed();
    for c in 0..proj::chunks(n) {
        for j in 0..TRIALS {
            let k = 5 * (c * TRIALS + j);
            tr.absorb_u64((proj::decode_quotient(&cert.quot[k..k + 5]) + (1i64 << proj::VBITS)) as u64);
        }
    }
    Ok((seed, tr.sample_theta().0))
}

/// QLYAUTH7: the first two registered blocks for an instance X and certificate bytes: an
/// identifier of the round-1 projection values and the round-2 theta.
pub fn prefix_challenges7(table: Arc<reg7::Table>, x: &[u8], n: usize, bytes: &[u8]) -> Result<([u8; 64], EF), Reject> {
    let cert = Cert::from_bytes_v(n, bytes, true)?;
    let mut reg = reg7::Reg::new(table, x, Arc::new(AtomicU32::new(0)));
    reg.observe_root(cert.comm);
    let id = ProjSrc::Values(reg.sample_fq()).id();
    reg.observe_bytes(&cert.quot);
    let th = reg.sample_theta();
    match reg.error {
        Some(e) => Err(Reject::Transcript(e)),
        None => Ok((id, th)),
    }
}

pub fn ubytes_of(u: &[u8], n: usize) -> Vec<u8> {
    (0..n).flat_map(|i| mlnat::w1_encode(&u[i * SLOTS..(i + 1) * SLOTS])).collect()
}

pub fn prove(records: &[Record], u: &[u8], nu: &[u8], w: &Witness, pubs: &[SigPublic], tm: &mut Timer) -> (Cert, ProverReport) {
    prove_opts(records, u, nu, w, pubs, tm, &Opts::default())
}

pub fn prove_with(records: &[Record], u: &[u8], nu: &[u8], w: &Witness, pubs: &[SigPublic], tm: &mut Timer, quot_delta: i64) -> (Cert, ProverReport) {
    prove_opts(records, u, nu, w, pubs, tm, &Opts { quot_delta, ..Opts::default() })
}

/// Standalone statement: QLYAUTH3 (v4 transcript), or with `o.v7` the lab QLYAUTH7 profile.
pub fn prove_opts(records: &[Record], u: &[u8], nu: &[u8], w: &Witness, pubs: &[SigPublic], tm: &mut Timer, o: &Opts) -> (Cert, ProverReport) {
    if o.v7 {
        let n = records.len();
        let man = manifest_lab7(records);
        let x = reg7::instance_lab(reg7::lab_profile(n), &man, records, &ubytes_of(u, n), nu);
        prove_stmt7(records, &man, &x, reg7::lab_profile(n), u, nu, w, pubs, tm, o)
    } else {
        prove_stmt(records, &manifest(records), u, nu, w, pubs, tm, o)
    }
}

/// Prove against a given manifest under the QLYAUTH4 transcript (the v3 statement digest
/// manifest, or the v4 chain manifest).
#[allow(clippy::too_many_arguments)]
pub fn prove_stmt(records: &[Record], man: &[u8], u: &[u8], nu: &[u8], w: &Witness, pubs: &[SigPublic], tm: &mut Timer, o: &Opts) -> (Cert, ProverReport) {
    assert_eq!(man.len(), MANIFEST);
    let n = records.len();
    let ubytes = ubytes_of(u, n);
    let mut b = B4::new(n, o.layout == LayoutVariant::Profile, o.inject, man, &ubytes, nu);
    tm.lap("P0 statement digest, manifest, transcript init");
    prove_core(&mut b, records, man.to_vec(), ubytes, u, nu, w, pubs, tm, o)
}

/// Prove under profile `profile` of the QLYAUTH7 transcript: `x` is the raw public instance
/// (spec §2.4), `man` the QLYAUTH7 (or lab) manifest inside it.
#[allow(clippy::too_many_arguments)]
pub fn prove_stmt7(records: &[Record], man: &[u8], x: &[u8], profile: u32, u: &[u8], nu: &[u8], w: &Witness, pubs: &[SigPublic], tm: &mut Timer, o: &Opts) -> (Cert, ProverReport) {
    assert_eq!(man.len(), MANIFEST);
    let n = records.len();
    let ubytes = ubytes_of(u, n);
    let mut b = B7::new(n, profile, x, o.layout == LayoutVariant::Profile, o.inject, None);
    if o.log7 {
        b.tr.ch.log = Some(vec![]);
    }
    tm.lap("P0 raw instance absorbed, registered-round transcript init");
    let (c, mut rep) = prove_core(&mut b, records, man.to_vec(), ubytes, u, nu, w, pubs, tm, o);
    rep.inspect = Some(Inspect7::of(&b));
    (c, rep)
}

#[allow(clippy::too_many_arguments)]
fn prove_core<B: Backend>(b: &mut B, records: &[Record], man: Vec<u8>, ubytes: Vec<u8>, u: &[u8], nu: &[u8], w: &Witness, pubs: &[SigPublic], tm: &mut Timer, o: &Opts) -> (Cert, ProverReport) {
    let quot_delta = o.quot_delta;
    let n = records.len();
    let ntt = Ntt::new();
    let tree = Tree::new(n);
    let co = region::all_coeffs();
    let dc = 1usize << tree.log_dc;
    let nc = proj::chunks(n);
    let _ = u;

    // 1. Commitment to X | Y | S and m_even | m_odd.
    let nv = stacked_vars(n);
    let mut ta = Vec::with_capacity(3 * dc);
    if o.layout == LayoutVariant::SwapColumns {
        ta.extend_from_slice(&w.y);
        ta.extend_from_slice(&w.x);
    } else {
        ta.extend_from_slice(&w.x);
        ta.extend_from_slice(&w.y);
    }
    ta.extend_from_slice(&w.s);
    let me: Vec<F> = w.m.iter().step_by(2).copied().collect();
    let mo: Vec<F> = w.m.iter().skip(1).step_by(2).copied().collect();
    let mut tb = Vec::with_capacity(2 << LOG_TAB);
    tb.extend_from_slice(&me);
    tb.extend_from_slice(&mo);
    let (t_a, t_b) = (Table::new(RowMajorMatrix::new(ta, dc)), Table::new(RowMajorMatrix::new(tb, 1 << LOG_TAB)));
    let swap = o.layout == LayoutVariant::SwapTables;
    let wit = Layout::new_witness(if swap { vec![t_b, t_a] } else { vec![t_a, t_b] }, b.fold0());
    assert_eq!(wit.num_variables(), nv);
    let (comm, pdata) = b.commit(wit);
    tm.lap("P1 WHIR commit (2^nv cells)");

    // 2-3. Projections, integer lifts per 512-signature chunk, quotients.
    let src = b.projection();
    let seed_out = src.id();
    let ch = src.challenges(&ntt, n);
    let per = TRIALS * L * N;
    let mut s_all = vec![0i32; n * per];
    s_all.par_chunks_mut(per).enumerate().for_each(|(i, out)| ch.s_centered(&ntt, &pubs[i].a_hat, i, out));
    tm.lap("P2 projections (s = alpha A^dagger eta, 98 inverse NTTs per signature)");
    let e_parts: Vec<[i128; TRIALS]> = (0..n)
        .into_par_iter()
        .map(|i| {
            let base = i * SLOTS;
            let mut e = [0i128; TRIALS];
            for j in 0..TRIALS {
                let s = &s_all[i * per + j * L * N..i * per + (j + 1) * L * N];
                let mut acc: i64 = 0;
                for t in 0..L * N {
                    acc += s[t] as i64 * w.zi[base + t] as i64;
                }
                for t in 0..K * N {
                    acc -= ch.r_centered(j, i, t) * w.ei[base + t] as i64;
                }
                e[j] = acc as i128;
            }
            e
        })
        .collect();
    let mut dsum = vec![[0u64; TRIALS]; nc];
    for i in 0..n {
        for j in 0..TRIALS {
            dsum[i / CHUNK][j] = (dsum[i / CHUNK][j] + ch.d_part(j, i, &pubs[i].bu)) % mlnat::Q as u64;
        }
    }
    let mut quot = vec![[0i64; TRIALS]; nc];
    let mut qbytes = Vec::with_capacity(5 * TRIALS * nc);
    let (mut inexact, mut maxv) = (0usize, 0i64);
    for c in 0..nc {
        for j in 0..TRIALS {
            let mut e: i128 = 0;
            for i in c * CHUNK..((c + 1) * CHUNK).min(n) {
                e += e_parts[i][j];
            }
            e -= ctr(dsum[c][j] as u32) as i128;
            if e % QI as i128 != 0 {
                inexact += 1;
            }
            let lim = 1i128 << proj::VBITS;
            let mut v = (e.div_euclid(QI as i128)).clamp(-lim, lim - 1) as i64;
            if c == 0 && j == 0 {
                v += quot_delta;
            }
            maxv = maxv.max(v.abs());
            quot[c][j] = v;
            qbytes.extend_from_slice(&proj::encode_quotient(v));
        }
    }
    b.absorb_quotients(&quot, &qbytes);
    tm.lap("P3 integer lifts and quotients");

    // 4. theta and fractional GKR.
    let (theta, rej) = b.theta();
    let (lp, lq) = leaves(&tree, w, theta, &co);
    tm.lap("P4a paired leaves");
    let (gproof, gout) = gkr::prove(lp, lq, b);
    tm.lap("P4b fractional GKR");

    // 5-7. The bottom claims (QLYAUTH7: also sent explicitly, round 279), T, the weights.
    b.absorb_efs(&[gout.p, gout.q]);
    let gp = b.sample_ef();
    let gq = b.sample_ef();
    let rho = gout.point.clone();
    let rt = tree.rho_t(&rho);
    let eqt = eq_table(&rt);
    let (ta_, tb_): (Vec<EF>, Vec<EF>) = (0..1usize << LOG_TAB)
        .into_par_iter()
        .map(|j| (-(theta - efb(F::from_usize(2 * j + 1))), -(theta - efb(F::from_usize(2 * j)))))
        .unzip();
    let t_claim: EF = (0..1usize << LOG_TAB).into_par_iter().map(|j| eqt[j] * (ta_[j] * me[j] + tb_[j] * mo[j])).sum();
    b.absorb_ef(t_claim);
    let gz = b.sample_ef();
    let gz = if o.drop_ternarity { EF::ZERO } else { gz };
    let tau = b.sample_efs(tree.log_dc);
    let omega = b.sample_efs(n);
    let mu: Vec<[EF; TRIALS]> = (0..nc).map(|_| core::array::from_fn(|_| b.sample_ef())).collect();
    let eq_rho = eq_table(&rho[..tree.log_dc]);
    let sums: Vec<SigSums> = (0..n)
        .into_par_iter()
        .map(|i| sig_sums(i, &s_all[i * per..(i + 1) * per], &ch, &pubs[i].bu, &u[i * SLOTS..(i + 1) * SLOTS], &eq_rho, None))
        .collect();
    let agg = aggregate(&sums, n);
    let cx = Ctx { n, tree, theta, rho: rho.clone(), p_leaf: gout.p, q_leaf: gout.q, gp, gq, t_claim, gz, tau: tau.clone(), omega: omega.clone(), mu: mu.clone(), quot: quot.clone(), nu: nu.to_vec() };
    let claim = claimed_sum(&cx, &agg, &co);
    let pubcols = build_public(&cx, w, &s_all, &ch, &eq_rho, &co);
    drop(eq_rho);
    tm.lap("P5a master weights, public coefficient columns, claimed sum");
    let mout = sumcheck::master_prove(&w.x, &w.y, &w.s, pubcols, claim, b);
    tm.lap("P5b master sumcheck (degree 4)");
    drop(eqt);
    let tout = sumcheck::table_prove(&rt, ta_, tb_, &me, &mo, t_claim, b);
    tm.lap("P5c table sumcheck (degree 2)");

    // 9. Five openings in one WHIR proof.
    let (proof, evals_ok) = match o.layout {
        LayoutVariant::SwapTables => {
            let proto = OpeningProtocol::new(vec![
                TableSpec::new(TableShape::new(LOG_TAB, 2), vec![OpeningBatch::new(vec![0, 1], vec![])]),
                TableSpec::new(TableShape::new(tree.log_dc, 3), vec![OpeningBatch::new(vec![0, 1, 2], vec![])]),
            ]);
            (b.open_at(pdata, &proto, &[p3_point(&tout.point), p3_point(&mout.point)]).0, false)
        }
        LayoutVariant::ClaimOrder => {
            let proto = OpeningProtocol::new(vec![
                TableSpec::new(TableShape::new(tree.log_dc, 3), vec![OpeningBatch::new(vec![1, 0, 2], vec![])]),
                TableSpec::new(TableShape::new(LOG_TAB, 2), vec![OpeningBatch::new(vec![0, 1], vec![])]),
            ]);
            (b.open_at(pdata, &proto, &[p3_point(&mout.point), p3_point(&tout.point)]).0, false)
        }
        _ => {
            let proto = protocol(tree.log_dc);
            let (proof, ev) = b.open_at(pdata, &proto, &[p3_point(&mout.point), p3_point(&tout.point)]);
            let ok = ev[0] == mout.evals[..] && ev[1] == tout.evals[..];
            (proof, ok)
        }
    };
    let whir = bincode::serialize(&proof).unwrap();
    tm.lap("P6 WHIR opening (5 claims)");

    let comm_bytes = words_to_bytes(&comm.roots()[0]);
    let leaf_pair = if B::V7 { Some([gout.p, gout.q]) } else { None };
    let cert = Cert { manifest: man, u: ubytes, nu: nu.to_vec(), quot: qbytes, comm: comm_bytes, gkr: gproof, leaf_pair, t_claim, master: mout.rounds, table: tout.rounds, whir };
    let rep = ProverReport {
        theta_rejections: rej,
        gkr_leaves_log: tree.d,
        stacked_vars: nv,
        quotient_inexact: inexact,
        max_abs_v: maxv,
        evals_match_whir: evals_ok,
        seed: seed_out,
        theta,
        transcript_error: b.transcript_error(),
        inspect: None,
    };
    (cert, rep)
}

fn build_public(c: &Ctx, w: &Witness, s_all: &[i32], ch: &Challenges, eq_rho: &[EF], co: &[Coeffs; 3]) -> Pub {
    let dc = 1usize << c.tree.log_dc;
    let (kx, ky) = (c.tree.kx(&c.rho), c.tree.ky(&c.rho));
    let kxf = F::from_u64(XK as u64);
    let eq_tau = eq_table(&c.tau);
    let mut cols: Pub = core::array::from_fn(|_| vec![EF::ZERO; dc]);
    let ptrs: Vec<SendPtr<EF>> = cols.iter_mut().map(|v| SendPtr(v.as_mut_ptr())).collect();
    let g = c.gp + c.gq * c.theta;
    let per = TRIALS * L * N;
    (0..c.n).into_par_iter().for_each(|i| {
        let mu = &c.mu[i / CHUNK];
        let om = c.omega[i];
        let s = &s_all[i * per..(i + 1) * per];
        for t in 0..SLOTS {
            let b = i * SLOTS + t;
            let er = eq_rho[b];
            let (wx, zp) = if t < L * N {
                let mut zp = EF::ZERO;
                for j in 0..TRIALS {
                    zp += mu[j] * fi(s[j * L * N + t] as i64);
                }
                (kx * er, zp)
            } else {
                (EF::ZERO, EF::ZERO)
            };
            let mut rp = EF::ZERO;
            for j in 0..TRIALS {
                rp += mu[j] * fi(ch.r_centered(j, i, t));
            }
            let wy = ky * er;
            let k = &co[w.class[b] as usize];
            let et = eq_tau[b];
            let vals = [
                c.gq * wx * kxf + zp,
                -(c.gq * wx),
                c.gq * wy * k.k[0] - rp,
                -(c.gq * wy),
                c.gq * wy * k.k[1],
                c.gq * wy * k.k[2],
                -(g * wy * k.k[1]) - c.gz * et - rp * k.st[1],
                -(g * wy * k.k[2]) + om - rp * k.st[2],
                c.gz * et,
            ];
            for (col, v) in vals.into_iter().enumerate() {
                unsafe { *ptrs[col].at(b) = v };
            }
        }
    });
    cols
}

// ---------------------------------------------------------------- verifier

pub struct VerifyReport {
    pub theta_rejections: usize,
}

pub fn verify(records: &[Record], bytes: &[u8], tm: &mut Timer) -> Result<VerifyReport, Reject> {
    verify_opts(records, bytes, tm, &Opts::default())
}

/// Standalone statement: QLYAUTH3 (v4 transcript), or with `o.v7` the lab QLYAUTH7 profile.
pub fn verify_opts(records: &[Record], bytes: &[u8], tm: &mut Timer, o: &Opts) -> Result<VerifyReport, Reject> {
    if o.v7 {
        verify_lab7(records, bytes, tm, o).0
    } else {
        verify_stmt(records, &manifest(records), bytes, tm, o)
    }
}

/// The lab QLYAUTH7 verifier for standalone statements, with the adapter's instrumentation.
pub fn verify_lab7(records: &[Record], bytes: &[u8], tm: &mut Timer, o: &Opts) -> (Result<VerifyReport, Reject>, Option<Inspect7>) {
    let n = records.len();
    let man = manifest_lab7(records);
    let Some(table) = registered_table(reg7::lab_profile(n), n, true) else {
        return (Err(Reject::Profile("no lab profile for this count".into())), None);
    };
    let cert = match Cert::from_bytes_v(n, bytes, true) {
        Ok(c) => c,
        Err(e) => return (Err(e), None),
    };
    let x = reg7::instance_lab(table.profile, &man, records, &cert.u, &cert.nu);
    verify_stmt7(records, &man, &x, table, bytes, tm, o)
}

/// Verify against a verifier-derived manifest `man` under the QLYAUTH4 transcript.
pub fn verify_stmt(records: &[Record], man: &[u8], bytes: &[u8], tm: &mut Timer, o: &Opts) -> Result<VerifyReport, Reject> {
    let n = records.len();
    let cert = Cert::from_bytes(n, bytes)?;
    if cert.manifest != man {
        return Err(Reject::Manifest);
    }
    if let Some(i) = cert.nu.iter().position(|&v| v > NU_MAX) {
        return Err(Reject::HintCountByte(i));
    }
    let proof: PcsProof = bincode::deserialize(&cert.whir).map_err(|_| Reject::Parse("WHIR proof"))?;
    // bincode ignores trailing input: re-measure so one proof has exactly one accepted encoding.
    if bincode::serialized_size(&proof).map_err(|_| Reject::Parse("WHIR proof"))? as usize != cert.whir.len() {
        return Err(Reject::Parse("WHIR proof trailing bytes"));
    }
    let mut b = B4::new(n, false, o.inject, man, &cert.u, &cert.nu);
    verify_core(&mut b, records, &cert, &proof, tm, o)
}

/// Verify under a registered QLYAUTH7 table: `x` is the verifier-synthesized raw instance and
/// `man` the verifier-derived manifest inside it.
pub fn verify_stmt7(records: &[Record], man: &[u8], x: &[u8], table: Arc<reg7::Table>, bytes: &[u8], tm: &mut Timer, o: &Opts) -> (Result<VerifyReport, Reject>, Option<Inspect7>) {
    let n = records.len();
    if table.n != n {
        return (Err(Reject::Profile(format!("profile {:#010x} fixes N = {}, statement has {n}", table.profile, table.n))), None);
    }
    let pre = || -> Result<(Cert, pcs::PcsProof7), Reject> {
        let cert = Cert::from_bytes_v(n, bytes, true)?;
        if cert.manifest != man {
            return Err(Reject::Manifest);
        }
        if let Some(i) = cert.nu.iter().position(|&v| v > NU_MAX) {
            return Err(Reject::HintCountByte(i));
        }
        // Canonical parsing (gate 4): every field word decodes canonically (Goldilocks rejects
        // values >= p), and the proof must re-encode to exactly the received bytes.
        let proof: pcs::PcsProof7 = bincode::deserialize(&cert.whir).map_err(|_| Reject::Parse("WHIR proof"))?;
        if bincode::serialize(&proof).map_err(|_| Reject::Parse("WHIR proof"))? != cert.whir {
            return Err(Reject::Parse("WHIR proof is not the canonical encoding (trailing or non-canonical bytes)"));
        }
        Ok((cert, proof))
    };
    let (cert, proof) = match pre() {
        Ok(v) => v,
        Err(e) => return (Err(e), None),
    };
    let mut b = B7::new(n, table.profile, x, false, o.inject, Some(table));
    if o.log7 {
        b.tr.ch.log = Some(vec![]);
    }
    let r = verify_core(&mut b, records, &cert, &proof, tm, o);
    let r = match (r, b.transcript_error()) {
        (Ok(_), Some(e)) => Err(Reject::Transcript(e)),
        (r, _) => r,
    };
    (r, Some(Inspect7::of(&b)))
}

fn verify_core<B: Backend>(b: &mut B, records: &[Record], cert: &Cert, proof: &B::Proof, tm: &mut Timer, o: &Opts) -> Result<VerifyReport, Reject> {
    let n = records.len();
    let ntt = Ntt::new();
    let tree = Tree::new(n);
    let co = region::all_coeffs();
    let nc = proj::chunks(n);
    let u: Vec<u8> = (0..n).flat_map(|i| mlnat::w1_decode(&cert.u[i * 1024..(i + 1) * 1024])).collect();
    let quot: Vec<[i64; TRIALS]> = (0..nc).map(|c| core::array::from_fn(|j| proj::decode_quotient(&cert.quot[5 * (c * TRIALS + j)..5 * (c * TRIALS + j) + 5]))).collect();
    let comm: Commitment = MerkleCap::new(vec![core::array::from_fn(|i| u64::from_le_bytes(cert.comm[8 * i..8 * i + 8].try_into().unwrap()))]);
    tm.lap("V0 parse, manifest, statement digest, byte checks");

    // Transcript replay (challenges only).
    b.observe_commitment(&comm);
    let src = b.projection();
    b.absorb_quotients(&quot, &cert.quot);
    let (theta, rej) = b.theta();
    let gout = gkr::verify(&cert.gkr, tree.d, b).map_err(|e| Reject::Gkr(format!("{e:?}")))?;
    if B::V7 {
        // Round 279: the transmitted pair must equal the pair derived from the GKR transcript;
        // the derived pair is what the verifier uses.
        if cert.leaf_pair != Some([gout.p, gout.q]) {
            return Err(Reject::LeafPair);
        }
    }
    b.absorb_efs(&[gout.p, gout.q]);
    let gp = b.sample_ef();
    let gq = b.sample_ef();
    b.absorb_ef(cert.t_claim);
    let gz = b.sample_ef();
    let gz = if o.drop_ternarity { EF::ZERO } else { gz };
    let tau = b.sample_efs(tree.log_dc);
    let omega = b.sample_efs(n);
    let mu: Vec<[EF; TRIALS]> = (0..nc).map(|_| core::array::from_fn(|_| b.sample_ef())).collect();
    // The master rounds are absorbed here; their claims are chained once the public sums exist.
    let mut r = vec![EF::ZERO; tree.log_dc];
    if cert.master.len() != tree.log_dc {
        return Err(Reject::Master("round count"));
    }
    let mut mrs = Vec::with_capacity(tree.log_dc);
    for (idx, h) in cert.master.iter().enumerate() {
        b.absorb_efs(h);
        let x = b.sample_ef();
        r[tree.log_dc - 1 - idx] = x;
        mrs.push(x);
    }
    let rt = tree.rho_t(&gout.point);
    let (spt, tfinal) = sumcheck::table_verify(&cert.table, &rt, cert.t_claim, b).ok_or(Reject::Table("round count"))?;
    tm.lap("V1 transcript replay, fractional GKR verification");

    let proto = protocol(tree.log_dc);
    let evals = b.verify_at(&comm, proof, &proto, &[p3_point(&r), p3_point(&spt)]).map_err(Reject::Whir)?;
    if let Some(e) = b.transcript_error() {
        return Err(Reject::Transcript(e));
    }
    let (xr, yr, sr) = (evals[0][0], evals[0][1], evals[0][2]);
    let (mer, mor) = (evals[1][0], evals[1][1]);
    tm.lap("V2 WHIR verification (5 claims)");

    // Table terminal check.
    let jhat: EF = spt.iter().enumerate().map(|(t, &x)| x * F::from_u64(1u64 << t)).sum();
    let a_s = -(theta - jhat.double() - EF::ONE);
    let b_s = -(theta - jhat.double());
    if tfinal != a_s * mer + b_s * mor {
        return Err(Reject::Table("terminal check"));
    }

    // Public coefficients: per signature, recompute A, mu, c_tilde(u), c, b + a u, the
    // projections, and every eq-weighted sum the claimed sum and the terminal check need.
    let ch = src.challenges(&ntt, n);
    let eq_rho = eq_table(&gout.point[..tree.log_dc]);
    let eq_r = eq_table(&r);
    tm.lap("V3a projection challenges, eq tables");
    let per = TRIALS * L * N;
    let sums: Vec<SigSums> = (0..n)
        .into_par_iter()
        .map(|i| {
            let ui = &u[i * SLOTS..(i + 1) * SLOTS];
            let pubd = mlnat::derive_public(&ntt, &records[i], ui);
            let mut s = vec![0i32; per];
            ch.s_centered(&ntt, &pubd.a_hat, i, &mut s);
            sig_sums(i, &s, &ch, &pubd.bu, ui, &eq_rho, Some(&eq_r))
        })
        .collect();
    let agg = aggregate(&sums, n);
    tm.lap("V3b public coefficients (ExpandA, mu, c, b, 14 projections, eq-weighted sums)");

    let cx = Ctx { n, tree, theta, rho: gout.point.clone(), p_leaf: gout.p, q_leaf: gout.q, gp, gq, t_claim: cert.t_claim, gz, tau, omega, mu, quot, nu: cert.nu.clone() };
    let mut claim = claimed_sum(&cx, &agg, &co);
    for (h, &x) in cert.master.iter().zip(&mrs) {
        claim = crate::field::lagrange(&[h[0], claim - h[0], h[1], h[2], h[3]], x);
    }
    let pv = public_at_r(&cx, &agg, &co, &r);
    if claim != sumcheck::master_final(xr, yr, sr, &pv) {
        return Err(Reject::Master("terminal check"));
    }
    tm.lap("V4 claimed sum, master chain, terminal checks");
    let _ = eq1;
    Ok(VerifyReport { theta_rejections: rej })
}

pub fn ef_coords(x: &EF) -> Vec<u64> {
    <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(x).iter().map(|c| c.as_canonical_u64()).collect()
}

