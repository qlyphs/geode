//! Independent adversarial review of profile 0x00070001 (QLYAUTH7) at N = 2048: mutated
//! certificates and statements against the chain verifier, each expected to be rejected.
//!
//! Command: `r3-cert attack7`. Nothing here changes verifier code; every test goes through
//! `chain::verify_range` with the default options.

use crate::cert::{self, Reject, Timer};
use crate::chain;
use crate::field::{EF, F, ef_from_bytes, ef_to_bytes};
use crate::fs7;
use crate::mlnat::{Ntt, Record};
use crate::pcs;
use crate::witness::{self, SigInput};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use rayon::prelude::*;

const P: u64 = 0xffff_ffff_0000_0001;

struct Ctx {
    ch: chain::Chain,
    nb: usize,
    pass: usize,
    total: usize,
    accepts: Vec<String>,
}

impl Ctx {
    fn verify(&self, bytes: &[u8]) -> Result<cert::VerifyReport, Reject> {
        let mut tv = Timer::new();
        chain::verify_range(&self.ch.net, &self.ch.anchor, &self.ch.headers[..self.nb], &self.ch.blocks[..self.nb], &self.ch.state, bytes, &mut tv)
    }
    fn expect(&mut self, name: &str, res: Result<cert::VerifyReport, Reject>, accept: bool) {
        self.total += 1;
        let ok = res.is_ok() == accept;
        self.pass += ok as usize;
        let verdict = match &res {
            Ok(_) => "ACCEPT".to_string(),
            Err(e) => format!("REJECT {}", short(e)),
        };
        if res.is_ok() && !accept {
            self.accepts.push(name.to_string());
        }
        println!("[{}] {name}: {verdict}", if ok { "PASS" } else { "FAIL" });
    }
    fn reject(&mut self, name: &str, bytes: &[u8]) {
        let r = self.verify(bytes);
        self.expect(name, r, false);
    }
}

fn short(e: &Reject) -> String {
    let s = format!("{e:?}");
    if s.len() > 110 { format!("{}...", &s[..110]) } else { s }
}

/// Prove the first `nb` blocks under profile 0x00070001 with optional prover-side deviations:
/// `nu_tweak` edits the published hint counts (and so the raw instance), `o` carries test
/// options for the prover only (the verifier always runs the protocol).
fn prove7(ch: &chain::Chain, nb: usize, nu_tweak: &dyn Fn(&mut Vec<u8>), o: &cert::Opts) -> (Vec<u8>, cert::Sizes) {
    let ntt = Ntt::new();
    let r = 0..nb;
    let parent = &ch.anchor;
    let records: Vec<Record> = chain::replay(&ch.net, &ch.blocks[r.clone()], &ch.state).unwrap();
    let sigs: Vec<Vec<u8>> = ch.blocks[r.clone()].iter().flat_map(|b| b.sigs.clone()).collect();
    let man = chain::manifest_v7(&ch.net, records.len(), parent, &ch.headers[r.clone()]);
    let inputs: Vec<SigInput> = records.par_iter().zip(sigs.par_iter()).map(|(rc, sg)| witness::input_from_raw(&ntt, rc, sg)).collect();
    let (w, pubs) = witness::build(&ntt, &records, &inputs);
    let u: Vec<u8> = inputs.iter().flat_map(|i| i.u.clone()).collect();
    let mut nu: Vec<u8> = w.counts.iter().map(|&c| c.min(cert::NU_MAX)).collect();
    nu_tweak(&mut nu);
    let x = chain::instance_v7(&ch.net, parent, &ch.headers[r.clone()], &ch.blocks[r.clone()], &records, &cert::ubytes_of(&u, records.len()), &nu);
    let mut tp = Timer::new();
    let (c, rep) = cert::prove_stmt7(&records, &man, &x, fs7::PROFILE_V7, &u, &nu, &w, &pubs, &mut tp, o);
    if let Some(e) = &rep.transcript_error {
        println!("  (prover transcript error: {e})");
    }
    c.to_bytes()
}

fn prove4(ch: &chain::Chain, nb: usize) -> Vec<u8> {
    let ntt = Ntt::new();
    let r = 0..nb;
    let records: Vec<Record> = chain::replay(&ch.net, &ch.blocks[r.clone()], &ch.state).unwrap();
    let sigs: Vec<Vec<u8>> = ch.blocks[r.clone()].iter().flat_map(|b| b.sigs.clone()).collect();
    let man = chain::manifest_v4(&ch.net, records.len(), &ch.anchor, &ch.headers[r.clone()]);
    let inputs: Vec<SigInput> = records.par_iter().zip(sigs.par_iter()).map(|(rc, sg)| witness::input_from_raw(&ntt, rc, sg)).collect();
    let (w, pubs) = witness::build(&ntt, &records, &inputs);
    let u: Vec<u8> = inputs.iter().flat_map(|i| i.u.clone()).collect();
    let nu: Vec<u8> = w.counts.iter().map(|&c| c.min(cert::NU_MAX)).collect();
    let mut tp = Timer::new();
    let (c, _) = cert::prove_stmt(&records, &man, &u, &nu, &w, &pubs, &mut tp, &cert::Opts::default());
    c.to_bytes().0
}

/// Section offsets of a QLYAUTH7 certificate.
struct Off {
    u: usize,
    nu: usize,
    quot: usize,
    comm: usize,
    gkr: usize,
    pair: usize,
    t: usize,
    master: usize,
    table: usize,
    wlen: usize,
    whir: usize,
}

fn offsets(s: &cert::Sizes) -> Off {
    let u = s.manifest;
    let nu = u + s.u;
    let quot = nu + s.nu;
    let comm = quot + s.quot;
    let gkr = comm + s.comm;
    let pair = gkr + s.gkr;
    let t = pair + s.leaf_pair;
    let master = t + s.t_claim;
    let table = master + s.master;
    let wlen = table + s.table;
    let whir = wlen + 4;
    Off { u, nu, quot, comm, gkr, pair, t, master, table, wlen, whir }
}

/// Deterministic positions (no randomness: the run is reproducible).
fn positions(start: usize, len: usize, count: usize, salt: u64) -> Vec<usize> {
    let mut v = Vec::with_capacity(count);
    let mut x = 0x9e37_79b9_7f4a_7c15u64 ^ salt;
    for _ in 0..count {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        v.push(start + (x as usize) % len);
    }
    v
}

fn with_whir(bytes: &[u8], o: &Off, f: &dyn Fn(&mut pcs::PcsProof7)) -> Vec<u8> {
    let mut proof: pcs::PcsProof7 = bincode::deserialize(&bytes[o.whir..]).unwrap();
    f(&mut proof);
    let w = bincode::serialize(&proof).unwrap();
    let mut out = bytes[..o.wlen].to_vec();
    out.extend_from_slice(&(w.len() as u32).to_le_bytes());
    out.extend_from_slice(&w);
    out
}

fn put_ef(b: &mut [u8], at: usize, x: EF) {
    let mut v = Vec::with_capacity(40);
    ef_to_bytes(&x, &mut v);
    b[at..at + 40].copy_from_slice(&v);
}

fn get_ef(b: &[u8], at: usize) -> EF {
    ef_from_bytes(&b[at..at + 40]).unwrap()
}

pub fn run() {
    let (nb, per_block) = (16usize, 128usize);
    let n = nb * per_block;
    println!("# r3-cert attack7: independent review of profile 0x00070001 at N = {n}");
    let net = chain::network_id(b"attack7");
    let ch = chain::build(net, chain::genesis(&net), 0, nb, per_block, 0);
    let mut cx = Ctx { ch, nb, pass: 0, total: 0, accepts: vec![] };

    let (honest, sz) = prove7(&cx.ch, nb, &|_| {}, &cert::Opts::default());
    let o = offsets(&sz);
    let r = cx.verify(&honest);
    cx.expect("A0 honest QLYAUTH7 certificate", r, true);

    // A1 profile selection and confusion.
    for (name, pid) in [("lab id 0xfff7000b", 0xfff7_000bu32), ("codec test id 0xffffffff", 0xffff_ffff), ("0x00070002", 0x0007_0002), ("0x00070000", 0x0007_0000), ("QLYAUTH4 id 0x18013451", cert::profile_id(n))] {
        let mut b = honest.clone();
        b[8..12].copy_from_slice(&pid.to_le_bytes());
        cx.reject(&format!("A1 manifest profile id -> {name}"), &b);
    }
    for magic in [b"QLYAUTH4", b"QLYLAB07", b"QLYAUTH3", b"qlyauth7"] {
        let mut b = honest.clone();
        b[..8].copy_from_slice(magic);
        cx.reject(&format!("A1 manifest magic -> {}", String::from_utf8_lossy(magic)), &b);
    }
    {
        // QLYAUTH7 certificate presented as QLYAUTH4: magic, id and digest rewritten, leaf pair removed.
        let mut b = honest.clone();
        b[..cert::MANIFEST].copy_from_slice(&chain::manifest_v4(&net, n, &cx.ch.anchor, &cx.ch.headers[..nb]));
        b.drain(o.pair..o.pair + 80);
        cx.reject("A1 QLYAUTH7 proof relabelled QLYAUTH4 (manifest rewritten, pair removed)", &b);
    }
    {
        // QLYAUTH4 certificate of the same range relabelled QLYAUTH7, with the pair it would derive.
        let v4 = prove4(&cx.ch, nb);
        let r4 = cx.verify(&v4);
        cx.expect("A1 honest QLYAUTH4 certificate of the same range (control)", r4, true);
        let mut b = v4.clone();
        b[..cert::MANIFEST].copy_from_slice(&chain::manifest_v7(&net, n, &cx.ch.anchor, &cx.ch.headers[..nb]));
        // The v4 GKR's last finals give a pair; any pair is fine since the GKR replay fails first.
        let pair = honest[o.pair..o.pair + 80].to_vec();
        let mut c = b[..o.pair].to_vec();
        c.extend_from_slice(&pair);
        c.extend_from_slice(&b[o.pair..]);
        cx.reject("A1 QLYAUTH4 proof relabelled QLYAUTH7 (manifest rewritten, pair inserted)", &c);
    }

    // A2 framing: lengths and trailing bytes.
    {
        let mut b = honest.clone();
        b.push(0);
        cx.reject("A2 one trailing byte after the certificate", &b);
        let b = honest[..honest.len() - 1].to_vec();
        cx.reject("A2 certificate truncated by one byte", &b);
        let mut b = honest.clone();
        b.push(0);
        let wl = u32::from_le_bytes(b[o.wlen..o.wlen + 4].try_into().unwrap()) + 1;
        b[o.wlen..o.wlen + 4].copy_from_slice(&wl.to_le_bytes());
        cx.reject("A2 byte appended inside the WHIR proof, length raised", &b);
        let b: Vec<u8> = [&honest[..o.pair], &honest[o.t..]].concat();
        cx.reject("A2 QLYAUTH7 certificate without the 80-byte pair", &b);
        let b: Vec<u8> = [&honest[..o.t], &honest[o.pair..o.t], &honest[o.t..]].concat();
        cx.reject("A2 pair duplicated (160 bytes)", &b);
    }

    // A3 the explicit (P_leaf, Q_leaf) pair.
    {
        let p = get_ef(&honest, o.pair);
        let q = get_ef(&honest, o.pair + 40);
        let cases: [(&str, EF, EF); 5] = [("P_leaf + 1", p + EF::ONE, q), ("Q_leaf + 1", p, q + EF::ONE), ("pair swapped", q, p), ("pair zero", EF::ZERO, EF::ZERO), ("pair scaled by 2 (same fraction)", p.double(), q.double())];
        for (name, a, c) in cases {
            let mut b = honest.clone();
            put_ef(&mut b, o.pair, a);
            put_ef(&mut b, o.pair + 40, c);
            cx.reject(&format!("A3 leaf pair: {name}"), &b);
        }
    }

    // A4 non-canonical field encodings: a coefficient >= p in each 40-byte section.
    {
        assert!(ef_from_bytes(&[&P.to_le_bytes()[..], &[0u8; 32][..]].concat()).is_none());
        for (name, at) in [("GKR layer-0 final", o.gkr), ("leaf pair", o.pair), ("T", o.t), ("master round 0", o.master), ("table round 0", o.table)] {
            let mut b = honest.clone();
            let c0 = u64::from_le_bytes(b[at..at + 8].try_into().unwrap());
            // c0 + p if it fits (same residue), else 2^64 - 1.
            let v = if c0 < u64::MAX - P { c0 + P } else { u64::MAX };
            b[at..at + 8].copy_from_slice(&v.to_le_bytes());
            cx.reject(&format!("A4 coefficient >= p in {name} (c0 {} -> {v:#x})", if c0 < u64::MAX - P { "same residue" } else { "large" }), &b);
        }
        // The same residue inside the WHIR proof: find the first 8-byte word of the evals tail
        // (OpeningBatch current values sit near the end of the encoding).
        let mut b = honest.clone();
        let mut done = false;
        for at in (o.whir..b.len() - 8).rev() {
            let c = u64::from_le_bytes(b[at..at + 8].try_into().unwrap());
            if c < (1u64 << 31) && c > 64 && at > b.len() - 400 {
                b[at..at + 8].copy_from_slice(&(c + P).to_le_bytes());
                done = true;
                break;
            }
        }
        if done {
            cx.reject("A4 small WHIR word replaced by word + p (same residue)", &b);
        }
    }

    // A5 hint counts and other statement bytes.
    {
        let mut b = honest.clone();
        b[o.nu + 17] = 76;
        cx.reject("A5 nu_17 = 76 (out of range)", &b);
        let mut b = honest.clone();
        b[o.nu + 17] = if b[o.nu + 17] > 0 { b[o.nu + 17] - 1 } else { 1 };
        cx.reject("A5 nu_17 changed by one in the certificate only", &b);
        let mut b = honest.clone();
        b[o.nu + 17] = b[o.nu + 17].wrapping_add(1);
        b[o.nu + 18] = b[o.nu + 18].wrapping_sub(1);
        cx.reject("A5 nu_17 + 1 and nu_18 - 1 (sum preserved)", &b);
        let mut b = honest.clone();
        b.swap(o.nu + 17, o.nu + 18);
        if b != honest {
            cx.reject("A5 nu_17 and nu_18 swapped", &b);
        }
        let mut b = honest.clone();
        b[o.u + 1024 * 5 + 3] ^= 0x10;
        cx.reject("A5 one nibble of U_5 changed", &b);
        let mut b = honest.clone();
        b[300] ^= 1;
        cx.reject("A5 reserved manifest byte set", &b);
        let mut b = honest.clone();
        b[20] ^= 1;
        cx.reject("A5 reserved former digest byte set", &b);
    }

    // A6 reordering of transmitted rounds.
    {
        let mut b = honest.clone();
        let (a, c) = (o.master, o.master + 160);
        let r0 = b[a..a + 160].to_vec();
        let r1 = b[c..c + 160].to_vec();
        b[a..a + 160].copy_from_slice(&r1);
        b[c..c + 160].copy_from_slice(&r0);
        cx.reject("A6 master rounds 0 and 1 swapped", &b);
        let mut b = honest.clone();
        let r0 = b[o.table..o.table + 80].to_vec();
        let r1 = b[o.table + 80..o.table + 160].to_vec();
        b[o.table..o.table + 80].copy_from_slice(&r1);
        b[o.table + 80..o.table + 160].copy_from_slice(&r0);
        cx.reject("A6 table rounds 0 and 1 swapped", &b);
        let mut b = honest.clone();
        let q0 = b[o.quot..o.quot + 5].to_vec();
        let q1 = b[o.quot + 5..o.quot + 10].to_vec();
        b[o.quot..o.quot + 5].copy_from_slice(&q1);
        b[o.quot + 5..o.quot + 10].copy_from_slice(&q0);
        cx.reject("A6 quotients V_0,0 and V_0,1 swapped", &b);
        // Two last GKR finals of the last layer: (Pa, Pb) swapped with (Qa, Qb).
        let fin = o.pair - 160;
        let mut b = honest.clone();
        let pp = b[fin..fin + 80].to_vec();
        let qq = b[fin + 80..fin + 160].to_vec();
        b[fin..fin + 80].copy_from_slice(&qq);
        b[fin + 80..fin + 160].copy_from_slice(&pp);
        cx.reject("A6 last GKR finals: (Pa, Pb) and (Qa, Qb) swapped", &b);
    }

    // A7 WHIR proof structure (decode, edit, re-encode canonically).
    {
        type Wf = dyn Fn(&mut pcs::PcsProof7);
        let cases: Vec<(&str, Box<Wf>)> = vec![
            ("round 0 pow witness = 1", Box::new(|p: &mut pcs::PcsProof7| p.whir.rounds[0].pow_witness = F::ONE)),
            ("round 2 pow witness = 1", Box::new(|p: &mut pcs::PcsProof7| p.whir.rounds[2].pow_witness = F::ONE)),
            ("final pow witness = 1", Box::new(|p: &mut pcs::PcsProof7| p.whir.final_pow_witness = F::ONE)),
            ("initial sumcheck pow witness vector [0]", Box::new(|p: &mut pcs::PcsProof7| p.whir.initial_sumcheck.pow_witnesses.push(F::ZERO))),
            ("round 1 sumcheck pow witness vector [0]", Box::new(|p: &mut pcs::PcsProof7| p.whir.rounds[1].sumcheck.pow_witnesses.push(F::ZERO))),
            ("final sumcheck removed", Box::new(|p: &mut pcs::PcsProof7| p.whir.final_sumcheck = None)),
            ("final polynomial removed", Box::new(|p: &mut pcs::PcsProof7| p.whir.final_poly = None)),
            ("round 1 commitment removed", Box::new(|p: &mut pcs::PcsProof7| p.whir.rounds[1].commitment = None)),
            ("extra initial OOD answer", Box::new(|p: &mut pcs::PcsProof7| p.whir.initial_ood_answers.push(EF::ONE))),
            ("extra OOD answer in round 0", Box::new(|p: &mut pcs::PcsProof7| p.whir.rounds[0].ood_answers.push(EF::ONE))),
            ("initial OOD answer + 1", Box::new(|p: &mut pcs::PcsProof7| p.whir.initial_ood_answers[0] += EF::ONE)),
            ("extra initial sumcheck round", Box::new(|p: &mut pcs::PcsProof7| {
                let x = p.whir.initial_sumcheck.polynomial_evaluations[0];
                p.whir.initial_sumcheck.polynomial_evaluations.push(x)
            })),
            ("initial sumcheck rounds 0 and 1 swapped", Box::new(|p: &mut pcs::PcsProof7| p.whir.initial_sumcheck.polynomial_evaluations.swap(0, 1))),
            ("evals: X(r) + 1", Box::new(|p: &mut pcs::PcsProof7| {
                let mut c = p.evals[0].current().to_vec();
                c[0] += EF::ONE;
                p.evals[0] = p3_sumcheck::OpeningBatch::new(c, p.evals[0].next().to_vec());
            })),
            ("evals: X(r) and Y(r) swapped", Box::new(|p: &mut pcs::PcsProof7| {
                let mut c = p.evals[0].current().to_vec();
                c.swap(0, 1);
                p.evals[0] = p3_sumcheck::OpeningBatch::new(c, p.evals[0].next().to_vec());
            })),
            ("evals: successor value added to batch 1", Box::new(|p: &mut pcs::PcsProof7| {
                let c = p.evals[1].current().to_vec();
                p.evals[1] = p3_sumcheck::OpeningBatch::new(c, vec![EF::ONE]);
            })),
            ("evals: batch 0 and batch 1 swapped", Box::new(|p: &mut pcs::PcsProof7| p.evals.swap(0, 1))),
            ("evals: third batch duplicated", Box::new(|p: &mut pcs::PcsProof7| {
                let x = p.evals[1].clone();
                p.evals.push(x)
            })),
            ("final polynomial coefficient 0 + 1", Box::new(|p: &mut pcs::PcsProof7| {
                p.whir.final_poly.as_mut().unwrap().as_mut_slice()[0] += EF::ONE;
            })),
            ("round 0 query opening: first row duplicated over the second", Box::new(|p: &mut pcs::PcsProof7| {
                if let p3_whir::pcs::proof::QueryOpenings::Extension(o) = &mut p.whir.rounds[0].openings {
                    let r0 = o.rows[0].clone();
                    o.rows[1] = r0;
                } else if let p3_whir::pcs::proof::QueryOpenings::Base(o) = &mut p.whir.rounds[0].openings {
                    let r0 = o.rows[0].clone();
                    o.rows[1] = r0;
                }
            })),
            ("round 0 query opening: one value + 1", Box::new(|p: &mut pcs::PcsProof7| {
                match &mut p.whir.rounds[0].openings {
                    p3_whir::pcs::proof::QueryOpenings::Base(o) => o.rows[3][5] += F::ONE,
                    p3_whir::pcs::proof::QueryOpenings::Extension(o) => o.rows[3][5] += EF::ONE,
                }
            })),
            ("final query opening: one value + 1", Box::new(|p: &mut pcs::PcsProof7| {
                match &mut p.whir.final_openings {
                    p3_whir::pcs::proof::QueryOpenings::Base(o) => o.rows[0][0] += F::ONE,
                    p3_whir::pcs::proof::QueryOpenings::Extension(o) => o.rows[0][0] += EF::ONE,
                }
            })),
            ("round 0 query opening: extra row", Box::new(|p: &mut pcs::PcsProof7| {
                match &mut p.whir.rounds[0].openings {
                    p3_whir::pcs::proof::QueryOpenings::Base(o) => { let r = o.rows[0].clone(); o.rows.push(r) }
                    p3_whir::pcs::proof::QueryOpenings::Extension(o) => { let r = o.rows[0].clone(); o.rows.push(r) }
                }
            })),
        ];
        // Control: decode and re-encode without change is accepted.
        let same = with_whir(&honest, &o, &|_| {});
        let r = cx.verify(&same);
        cx.expect("A7 control: WHIR proof decoded and re-encoded unchanged", r, true);
        for (name, f) in cases {
            let b = with_whir(&honest, &o, &*f);
            cx.reject(&format!("A7 WHIR {name}"), &b);
        }
    }

    // A8 byte-flip sweep over every section (deterministic positions).
    {
        let end = honest.len();
        let secs: [(&str, usize, usize, usize); 12] = [
            ("manifest", 0, o.u, 12),
            ("U", o.u, o.nu, 12),
            ("nu", o.nu, o.quot, 8),
            ("quotients", o.quot, o.comm, 16),
            ("commitment", o.comm, o.gkr, 8),
            ("GKR", o.gkr, o.pair, 48),
            ("leaf pair", o.pair, o.t, 8),
            ("T", o.t, o.master, 6),
            ("master", o.master, o.table, 24),
            ("table", o.table, o.wlen, 16),
            ("WHIR length", o.wlen, o.whir, 4),
            ("WHIR proof", o.whir, end, 300),
        ];
        let mut sweep_total = 0;
        let mut sweep_rej = 0;
        let mut kinds: std::collections::BTreeMap<String, usize> = Default::default();
        for (k, (name, a, z, cnt)) in secs.iter().enumerate() {
            for (j, pos) in positions(*a, z - a, *cnt, k as u64 * 1000 + 7).into_iter().enumerate() {
                let mut b = honest.clone();
                b[pos] ^= 1u8 << (j % 8);
                let r = cx.verify(&b);
                sweep_total += 1;
                match &r {
                    Ok(_) => {
                        println!("[FAIL] A8 flip in {name} at byte {pos} bit {}: ACCEPT", j % 8);
                        cx.accepts.push(format!("A8 {name} byte {pos}"));
                    }
                    Err(e) => {
                        sweep_rej += 1;
                        let key = format!("{name}: {}", short(e).split('(').next().unwrap_or(""));
                        *kinds.entry(key).or_default() += 1;
                    }
                }
            }
        }
        cx.total += 1;
        cx.pass += (sweep_rej == sweep_total) as usize;
        println!("[{}] A8 byte-flip sweep: {sweep_rej}/{sweep_total} rejected", if sweep_rej == sweep_total { "PASS" } else { "FAIL" });
        for (k, v) in kinds {
            println!("    {v:>4} x {k}");
        }
    }

    // A9 dishonest provers under the full QLYAUTH7 transcript (valid transcript, false statement).
    {
        let (b, _) = prove7(&cx.ch, nb, &|nu| nu[9] = if nu[9] < 75 { nu[9] + 1 } else { nu[9] - 1 }, &cert::Opts::default());
        cx.reject("A9 prover publishes nu_9 off by one (instance X built with it)", &b);
        let (b, _) = prove7(&cx.ch, nb, &|nu| {
            if nu[9] < 75 && nu[10] > 0 {
                nu[9] += 1;
                nu[10] -= 1;
            } else {
                nu[9] = nu[9].wrapping_sub(1);
                nu[10] += 1;
            }
        }, &cert::Opts::default());
        cx.reject("A9 prover publishes nu_9 + 1, nu_10 - 1 (total preserved)", &b);
        let (b, _) = prove7(&cx.ch, nb, &|_| {}, &cert::Opts { quot_delta: 1, ..Default::default() });
        cx.reject("A9 prover shifts quotient V_0,0 by one", &b);
        let (b, _) = prove7(&cx.ch, nb, &|_| {}, &cert::Opts { drop_ternarity: true, ..Default::default() });
        // Honest witness: dropping gamma_Z on the prover side only changes the master claim.
        cx.reject("A9 prover drops the ternarity weight (verifier keeps it)", &b);
        for (name, inj) in [("Zero", pcs::Inject::Zero), ("One", pcs::Inject::One), ("Half", pcs::Inject::Half)] {
            let (b, _) = prove7(&cx.ch, nb, &|_| {}, &cert::Opts { inject: inj, ..Default::default() });
            cx.reject(&format!("A9 prover uses injected Gruen challenges {name} (verifier samples)"), &b);
        }
    }

    // A10 coin derivation cross-checks (no certificate): the adapter's incremental derivation
    // over a different statement or history must differ, and the instance must bind its parts.
    {
        let table = cert::registered_table(fs7::PROFILE_V7, n, false).unwrap();
        let lab = cert::registered_table(crate::reg7::lab_profile(n), n, true).unwrap();
        let same_rounds = table.rounds == lab.rounds;
        println!("  lab table at N = {n} has the same rounds as 0x00070001: {same_rounds} (coins still differ by profile)");
        let x1 = b"instance-a".to_vec();
        let s = fs7::Shape::k(1);
        let mut a = fs7::CoinState::new(fs7::PROFILE_V7, table.formal_len, &x1);
        let mut l = fs7::CoinState::new(lab.profile, lab.formal_len, &x1);
        a.push(1, &[0; 64]);
        l.push(1, &[0; 64]);
        let ok = a.block(&s, 296) != l.block(&s, 296);
        cx.total += 1;
        cx.pass += ok as usize;
        println!("[{}] A10 production and lab coin blocks differ on the same instance and root", if ok { "PASS" } else { "FAIL" });
        // Framing ambiguity check: F(0x0103, U) || F(0x0104, nu) cannot be re-split.
        let i1 = crate::reg7::instance_chain(fs7::PROFILE_V7, b"m", b"p", b"bs", b"uu", b"n");
        let i2 = crate::reg7::instance_chain(fs7::PROFILE_V7, b"m", b"p", b"bs", b"u", b"un");
        let ok = i1 != i2;
        cx.total += 1;
        cx.pass += ok as usize;
        println!("[{}] A10 instance framing separates U and nu", if ok { "PASS" } else { "FAIL" });
    }

    let _ = <EF as BasedVectorSpace<F>>::DIMENSION;
    let _ = F::ZERO.as_canonical_u64();
    println!("ATTACK7 SUMMARY: {}/{} behave as expected; unexpected ACCEPT: {:?}", cx.pass, cx.total, cx.accepts);
}
