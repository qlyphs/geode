//! Acceptance tests of the hidden-u certificate (round 9, build 2) at a lab size: honest
//! controls, the hash-side attacks of the plan, the false product-of-MLE shortcut, and the
//! existing response, ternarity, hint-budget, key, context, statement, byte-level, Gruen,
//! layout and range-binding tests ported to the hidden-u lab profiles. Command: `h9tests [N]`.

use std::sync::Arc;
use std::sync::atomic::AtomicU32;

use p3_field::PrimeCharacteristicRing;
use rayon::prelude::*;

use crate::cert::{Reject, Timer};
use crate::chain::{self, Chain};
use crate::field::{EF, F, fi};
use crate::hidden::{self, Opts9, SigIn9, Wit9};
use crate::mlnat::{self, K, N, Ntt, Record};
use crate::region;
use crate::relaxed;
use crate::witness::SLOTS;

pub struct Tally {
    pub pass: usize,
    pub total: usize,
    pub unexpected: Vec<String>,
}

impl Tally {
    fn expect(&mut self, name: &str, res: &Result<(), Reject>, accept: bool) {
        self.total += 1;
        let ok = res.is_ok() == accept;
        self.pass += ok as usize;
        if !ok {
            self.unexpected.push(name.to_string());
        }
        let v = match res {
            Ok(_) => "ACCEPT".to_string(),
            Err(e) => format!("REJECT {e:?}"),
        };
        println!("[{}] {name}: {v}", if ok { "PASS" } else { "FAIL" });
    }
    fn check(&mut self, name: &str, ok: bool) {
        self.total += 1;
        self.pass += ok as usize;
        if !ok {
            self.unexpected.push(name.to_string());
        }
        println!("[{}] {name}", if ok { "PASS" } else { "FAIL" });
    }
}

#[derive(Clone)]
struct Case {
    records: Vec<Record>,
    inputs: Vec<SigIn9>,
    raw: Vec<Option<Vec<u8>>>,
}

type WT<'a> = Option<&'a (dyn Fn(&mut Wit9) + Sync)>;
type NT<'a> = Option<&'a dyn Fn(&mut Vec<u8>)>;

struct Out {
    bytes: Vec<u8>,
    sz: hidden::Sizes9,
    res: Result<(), Reject>,
    rep: hidden::Report9,
}

/// Prove the lab statement with the given inputs; `wt` mutates the witness, `nt` receives the
/// true counts and returns the published ones (default min(count, 75)). The same options are
/// applied to the verifier (only the UNSAFE controls and the Gruen injection reach it).
fn run(c: &Case, wt: WT, nt: NT, o: &Opts9) -> Out {
    let ntt = Ntt::new();
    let (mut wit, pubs) = hidden::build9(&ntt, &c.records, &c.inputs);
    if let Some(f) = wt {
        f(&mut wit);
    }
    let nu: Vec<u8> = match nt {
        Some(f) => {
            let mut v = wit.w.counts.clone();
            f(&mut v);
            v
        }
        None => wit.w.counts.iter().map(|&x| x.min(crate::cert::NU_MAX)).collect(),
    };
    let mut po = o.clone();
    po.log = true;
    let (cert, rep) = hidden::prove_lab9(&c.records, &wit, &pubs, &nu, &mut Timer::new(), &po);
    if let Some(e) = &rep.transcript_error {
        println!("  (prover transcript error: {e})");
    }
    let (bytes, sz) = cert.to_bytes();
    let vo = Opts9 { drop_ternarity: o.drop_ternarity, drop_booleanity: o.drop_booleanity, inject: o.inject, ..Default::default() };
    let res = hidden::verify_lab9(&c.records, &bytes, &mut Timer::new(), &vo);
    Out { bytes, sz, res, rep }
}

fn verify(c: &Case, bytes: &[u8]) -> Result<(), Reject> {
    hidden::verify_lab9(&c.records, bytes, &mut Timer::new(), &Opts9::default())
}

/// Replace the sponge trace of signature i by the one of `blocks` (states and committed T
/// recomputed), as a prover that hashes other bytes would.
fn set_trace(w: &mut Wit9, i: usize, blocks: [[u8; hidden::RATE]; hidden::NPERM]) {
    w.blocks[i] = blocks;
    w.states[i] = hidden::run_trace(&blocks);
    w.t_states[i] = core::array::from_fn(|k| w.states[i][k]);
}

fn ubytes_of(u: &[u8]) -> Vec<u8> {
    mlnat::w1_encode(u)
}

/// High nibble first (the wrong nibble order).
fn nibble_swapped(w1: &[u8]) -> Vec<u8> {
    w1.iter().map(|&b| b.rotate_left(4)).collect()
}

/// Bits reversed inside each nibble (the wrong bit order).
fn bit_reversed(w1: &[u8]) -> Vec<u8> {
    let rev = |x: u8| ((x & 1) << 3) | ((x & 2) << 1) | ((x & 4) >> 1) | ((x & 8) >> 3);
    w1.iter().map(|&b| rev(b & 15) | (rev(b >> 4) << 4)).collect()
}

fn hash_with_pad(mu: &[u8; 64], w1: &[u8], suffix: u8) -> [u8; 64] {
    let mut b = hidden::absorb_blocks(mu, w1);
    b[8] = hidden::pad_block(suffix);
    hidden::squeeze64(&hidden::run_trace(&b)[8])
}

/// The alternative decomposition at one hint cell of signature i: (u, e, S = +1) becomes
/// (u + 1, e - a, S = 0). Every arithmetic constraint holds for the new u, the hint count drops
/// by one, and c_tilde is unchanged: the committed bits now disagree with the hashed U.
fn alt_decomposition(w: &mut Wit9, i: usize) -> usize {
    let base = i * SLOTS;
    let t = (0..K * N)
        .find(|&t| {
            let b = base + t;
            let u: u64 = (0..4).map(|j| (w.bits[j][b] == F::ONE) as u64 * (1 << j)).sum();
            w.w.s[b] == F::ONE && (1..=13).contains(&u)
        })
        .expect("a hint cell with 1 <= u <= 13");
    let b = base + t;
    let u: u8 = (0..4).map(|j| ((w.bits[j][b] == F::ONE) as u8) << j).sum();
    let ua = u + 1;
    for j in 0..4 {
        w.bits[j][b] = F::from_u8((ua >> j) & 1);
    }
    let e = w.w.ei[b] as i64 - region::A;
    let cl = region::class_of(ua);
    assert!(region::in_region(cl, e) && region::selector_of(cl, e) == 0);
    w.w.ei[b] = e as i32;
    w.w.s[b] = F::ZERO;
    w.w.y[b] = fi(e - region::start_int(cl, 0));
    w.w.class[b] = cl as u8;
    w.w.counts[i] -= 1;
    hidden::recount(w);
    t
}

/// A cell of signature i with u = 5, bits (1, 0, 1, 0) replaced by (1, 2, 0, 0): u, d0, d15 and
/// every arithmetic value are unchanged, B1 = 2 is not Boolean.
fn non_boolean(w: &mut Wit9, i: usize) -> usize {
    let base = i * SLOTS;
    let t = (0..K * N).find(|&t| (0..4).map(|j| ((w.bits[j][base + t] == F::ONE) as u8) << j).sum::<u8>() == 5).expect("a coefficient with u = 5");
    w.bits[1][base + t] = F::TWO;
    w.bits[2][base + t] = F::ZERO;
    t
}

fn honest_case(ntt: &Ntt, n: usize, offset: u64) -> Case {
    let (records, sigs) = crate::batch::libcrux_batch(n, offset);
    let inputs = records.par_iter().zip(sigs.par_iter()).map(|(r, s)| hidden::input_from_raw9(ntt, r, s)).collect();
    Case { records, inputs, raw: sigs.into_iter().map(Some).collect() }
}

/// The round-1 projection pool and the round-2 theta that a verifier derives for an instance,
/// a commitment and quotient bytes.
fn prefix9(table: Arc<crate::reg7::Table>, x: &[u8], comm: [u8; 64], quot: &[u8]) -> (Vec<u32>, EF) {
    let mut reg = crate::reg7::Reg::new(table, x, Arc::new(AtomicU32::new(0)));
    reg.observe_root(comm);
    let q = reg.sample_fq();
    reg.observe_bytes(quot);
    (q, reg.sample_theta())
}

pub fn run_all(n: usize) {
    println!("# hidden-u acceptance tests, N = {n}, lab profile {:#010x}, lab chain profile {:#010x}", hidden::lab_profile9(n), hidden::lab_chain_profile9(n));
    println!("uptime at start: {}", crate::uptime());
    let ntt = Ntt::new();
    let mut t = Tally { pass: 0, total: 0, unexpected: vec![] };
    let base = honest_case(&ntt, n, 1000);
    let d = Opts9::default();

    // ---------------------------------------------------------------- A. controls
    println!("## A. honest controls, extraction, profile isolation");
    let h = run(&base, None, None, &d);
    t.expect("honest certificate", &h.res, true);
    {
        let (vr, vi) = {
            let man = hidden::manifest_lab9(&base.records);
            let c = hidden::Cert9::from_bytes(n, &h.bytes).unwrap();
            let x = hidden::instance_lab9(hidden::lab_profile9(n), &man, &base.records, &c.ct, &c.nu);
            let table = hidden::registered_table9(hidden::lab_profile9(n), n).unwrap();
            hidden::verify_stmt9(&base.records, &man, &x, table, &h.bytes, &mut Timer::new(), &Opts9 { log: true, ..Default::default() })
        };
        let vi = vi.unwrap();
        let (pl, vl) = (h.rep.log.as_ref().unwrap(), vi.log.as_ref().unwrap());
        let same = pl.len() == vl.len() && pl.iter().zip(vl).all(|(a, b)| a.root == b.root && a.body == b.body && a.prefix == b.prefix);
        t.check(&format!("prover and verifier round logs identical ({} rounds: roots, bodies, coin prefixes); verify {}", pl.len(), vr.is_ok()), same && vr.is_ok() && pl.len() == h.rep.rounds);
        let s = &vi.stats;
        t.check(&format!("registered calls only: {} FS derivations, {} coin bytes, {} singleton hashes, {} p3 seeds declined, {} grinding calls, {} plain bit samples", s.fs_calls, s.fs_bytes, s.singleton_hashes, s.seeds_declined, s.grind_calls, s.bits_calls), s.grind_calls == 0 && s.bits_calls == 0 && s.fs_calls == h.rep.rounds && s.fs_calls == h.rep.stats.fs_calls);
    }
    {
        let (wit, _) = hidden::build9(&ntt, &base.records, &base.inputs);
        let ok = (0..n).into_par_iter().filter(|&i| hidden::reconstruct9(&wit, &base.records[i], i).map(|s| Some(&s) == base.raw[i].as_ref() && crate::batch::libcrux_verify(&base.records[i], &s)).unwrap_or(false)).count();
        t.check(&format!("canonical extraction: signatures rebuilt from (X, S, bit planes, public c_tilde) equal the originals and are accepted by libcrux: {ok}/{n}"), ok == n);
    }
    t.check("registry: no hidden-u table for the production id, the QLYAUTH7 lab id, or another count", hidden::registered_table9(crate::fs7::PROFILE_V7, n).is_none() && hidden::registered_table9(crate::reg7::lab_profile(n), n).is_none() && hidden::registered_table9(hidden::lab_profile9(n), n * 2).is_none());
    {
        let mut bad = h.bytes.clone();
        bad[8..12].copy_from_slice(&crate::reg7::lab_profile(n).to_le_bytes());
        t.expect("hidden-u certificate relabelled with the QLYAUTH7 lab id", &verify(&base, &bad), false);
        let r = crate::cert::verify_opts(&base.records, &h.bytes, &mut Timer::new(), &crate::cert::Opts { v7: true, ..Default::default() }).map(|_| ());
        t.expect("hidden-u certificate given to the QLYAUTH7 lab verifier", &r, false);
    }
    let ctl = run(&base, None, None, &Opts9 { drop_booleanity: true, ..Default::default() });
    t.expect("honest certificate under the UNSAFE no-Booleanity control (the control is complete)", &ctl.res, true);

    // ---------------------------------------------------------------- B. hash side
    println!("## B. hash-side attacks (relaxed key in slot 0 unless stated)");
    let key = relaxed::keygen(&ntt, b"r9h-key-0");
    let rec = relaxed::record(&key, 0);
    let with = |s: &relaxed::Signed| -> Case {
        let mut c = base.clone();
        c.records[0] = rec.clone();
        c.inputs[0] = SigIn9 { z: s.input.z.clone(), u: s.input.u.clone(), ct: s.ct };
        c.raw[0] = None;
        c
    };
    let sv = relaxed::sign(&ntt, &key, &rec.ctx, &rec.msg, relaxed::Mode::Valid, b"r9h-valid");
    let valid = with(&sv);
    t.expect("control: relaxed signer, true SHAKE256 challenge, all bounds respected", &run(&valid, None, None, &d).res, true);
    let mu0 = mlnat::mu_of(&key.tr(), &rec.ctx, &rec.msg);
    // Wrong suffix: c_tilde = Keccak sponge of mu || U with SHA3's 0x06 suffix.
    {
        let s = relaxed::sign_h(&ntt, &key, &rec.ctx, &rec.msg, relaxed::Mode::Valid, b"r9h-suffix", &|mu, w1| hash_with_pad(mu, w1, 0x06));
        let c = with(&s);
        let blk = {
            let mut b = hidden::absorb_blocks(&mu0, &ubytes_of(&s.input.u));
            b[8] = hidden::pad_block(0x06);
            b
        };
        let tw = move |w: &mut Wit9| set_trace(w, 0, blk);
        t.expect("wrong SHAKE suffix: c_tilde from the 0x06-padded sponge, prover's trace uses that padding block", &run(&c, Some(&tw), None, &d).res, false);
    }
    // Omitted padding permutation: c_tilde = first 64 bytes of S_8.
    {
        let s = relaxed::sign_h(&ntt, &key, &rec.ctx, &rec.msg, relaxed::Mode::Valid, b"r9h-nopad", &|mu, w1| hidden::squeeze64(&hidden::run_trace(&hidden::absorb_blocks(mu, w1))[7]));
        let c = with(&s);
        t.expect("omitted padding permutation: c_tilde = first 64 bytes of S_8, honest nine-permutation trace", &run(&c, None, None, &d).res, false);
        let tw = |w: &mut Wit9| {
            // The prover makes slot 8 an identity-like claim: its input row equals S_8 (no pad).
            let st = w.states[0][7];
            w.blocks[0][8] = [0u8; hidden::RATE];
            w.states[0][8] = {
                let mut x = st;
                ::keccak::f1600(&mut x);
                x
            };
        };
        t.expect("omitted padding: prover also drops the padding block from slot 8", &run(&c, Some(&tw), None, &d).res, false);
    }
    // Wrong nibble order and wrong bit order.
    for (label, enc) in [("wrong nibble order: U encoded high nibble first", nibble_swapped as fn(&[u8]) -> Vec<u8>), ("wrong bit order: bits reversed inside each nibble", bit_reversed)] {
        let s = relaxed::sign_h(&ntt, &key, &rec.ctx, &rec.msg, relaxed::Mode::Valid, label.as_bytes(), &move |mu, w1| mlnat::c_tilde_of(mu, &enc(w1)));
        let c = with(&s);
        let blk = hidden::absorb_blocks(&mu0, &enc(&ubytes_of(&s.input.u)));
        let tw = move |w: &mut Wit9| set_trace(w, 0, blk);
        t.expect(&format!("{label}; c_tilde and the prover's trace use that encoding, the bits are the true u"), &run(&c, Some(&tw), None, &d).res, false);
    }
    // Swapped intermediate states and permutation slots.
    t.expect("committed states T3 and T4 exchanged (columns swapped), honest trace", &run(&base, None, None, &Opts9 { swap_cols: Some((hidden::COL_T + 2, hidden::COL_T + 3)), ..Default::default() }).res, false);
    {
        let tw = |w: &mut Wit9| {
            w.t_states[0].swap(2, 3);
        };
        t.expect("signature 0 only: committed T3 and T4 exchanged", &run(&base, Some(&tw), None, &d).res, false);
        let tw = |w: &mut Wit9| {
            // Slots 3 and 4 exchanged in the trace: slot 3 computes permutation 5 and slot 4
            // permutation 4; the committed states stay in order.
            let (s2, s3) = (w.states[0][2], w.states[0][3]);
            let (b3, b4) = (w.blocks[0][3], w.blocks[0][4]);
            w.states[0][2] = s3;
            w.states[0][3] = s2;
            w.blocks[0][3] = b4;
            w.blocks[0][4] = b3;
        };
        t.expect("permutation slots 3 and 4 of signature 0 exchanged in the trace", &run(&base, Some(&tw), None, &d).res, false);
        let tw = |w: &mut Wit9| {
            w.blocks.swap(0, 1);
            w.states.swap(0, 1);
            w.t_states.swap(0, 1);
        };
        t.expect("sponge traces of signatures 0 and 1 exchanged (states, blocks and committed T)", &run(&base, Some(&tw), None, &d).res, false);
    }
    // Capacity-only mutations.
    {
        let cap = 1088 + 77;
        let tw = move |w: &mut Wit9| w.t_states[0][3][cap / 64] ^= 1 << (cap % 64);
        t.expect("capacity-only mutation: one capacity bit of committed T4 flipped", &run(&base, Some(&tw), None, &d).res, false);
        let tw = move |w: &mut Wit9| {
            let mut s = w.states[0][3];
            s[cap / 64] ^= 1 << (cap % 64);
            w.states[0][3] = s;
            for q in 4..hidden::NPERM {
                let mut x = w.states[0][q - 1];
                hidden::xor_block(&mut x, &w.blocks[0][q]);
                ::keccak::f1600(&mut x);
                w.states[0][q] = x;
            }
            w.t_states[0] = core::array::from_fn(|k| w.states[0][k]);
        };
        t.expect("capacity-only mutation of S4 carried through the rest of the sponge (consistent trace and T)", &run(&base, Some(&tw), None, &d).res, false);
        let tw = move |w: &mut Wit9| w.states[0][4][cap / 64] ^= 1 << (cap % 64);
        t.expect("capacity bit of the slot-5 input changed, committed T5 unchanged (capacity not carried)", &run(&base, Some(&tw), None, &d).res, false);
    }
    // Non-Boolean bits.
    {
        let tw = |w: &mut Wit9| {
            non_boolean(w, 0);
        };
        t.expect("non-Boolean bit: u = 5 as (1, 2, 0, 0) (arithmetic unchanged), honest trace", &run(&base, Some(&tw), None, &d).res, false);
        t.expect("same witness under the UNSAFE no-Booleanity control (the hash link still binds the bits)", &run(&base, Some(&tw), None, &Opts9 { drop_booleanity: true, ..Default::default() }).res, false);
        let tw = |w: &mut Wit9| {
            let t0 = non_boolean(w, 0);
            // The prover feeds the field bit into the slot carrying it: in = T (1 - 2 B).
            let (q, s) = hidden::upos_of(1, t0);
            let st = if q == 0 { [0u64; 25] } else { w.states[0][q - 1] };
            let tb = if hidden::state_bit(&st, s) == 1 { -F::ONE } else { F::ONE };
            w.in_extra.push((q, s, tb * (F::ONE - F::TWO.double())));
        };
        t.expect("non-Boolean bit also fed into the Keccak input (in = T (1 - 2 B) with B = 2)", &run(&base, Some(&tw), None, &d).res, false);
    }
    // Nonzero padded coordinates and dummy slots.
    {
        let tw = |w: &mut Wit9| w.t_extra.push((0, 1, 1700, F::ONE));
        t.expect("nonzero padded coordinate of committed T2 (cell 1700)", &run(&base, Some(&tw), None, &d).res, false);
        let tw = |w: &mut Wit9| w.in_extra.push((2, 1700, F::ONE));
        t.expect("nonzero padded coordinate of the slot-2 Keccak input row (cell 1700; the layers ignore it)", &run(&base, Some(&tw), None, &d).res, false);
        let tw = |w: &mut Wit9| w.in_extra.push((12, 5, F::ONE));
        t.expect("nonzero cell in dummy slot 12 of signature 0", &run(&base, Some(&tw), None, &d).res, false);
    }
    // Different u used by the arithmetic and the hash.
    {
        let tw = |w: &mut Wit9| {
            alt_decomposition(w, 3);
        };
        let (wa, _) = hidden::build9(&ntt, &base.records, &base.inputs);
        let mut wa = wa;
        let cell = alt_decomposition(&mut wa, 3);
        println!("  alternative decomposition at signature 3, coefficient {cell}: (u, e, S=1) -> (u+1, e-a, S=0); every arithmetic bound holds, hint count {}", wa.w.counts[3]);
        t.expect("different u: arithmetic and bits use u_a (alternative decomposition), the hash trace uses the true U", &run(&base, Some(&tw), None, &d).res, false);
        let tw = |w: &mut Wit9| {
            alt_decomposition(w, 3);
            let u: Vec<u8> = (0..K * N).map(|t| (0..4).map(|j| ((w.bits[j][3 * SLOTS + t] == F::ONE) as u8) << j).sum()).collect();
            let mu = mlnat::mu_of(&mlnat::tr_of(&base.records[3].pk), &base.records[3].ctx, &base.records[3].msg);
            set_trace(w, 3, hidden::absorb_blocks(&mu, &mlnat::w1_encode(&u)));
        };
        t.expect("u_a everywhere (arithmetic, bits, trace), c_tilde unchanged", &run(&base, Some(&tw), None, &d).res, false);
    }
    // The false product-of-MLE shortcut.
    {
        let (v, sc) = h.rep.shortcut_probe.unwrap();
        t.check(&format!("false shortcut on the honest certificate: input claim {:?}.. vs XOR link evaluated on multilinear evaluations {:?}.. (a verifier using it rejects honest proofs)", crate::cert::ef_coords(&v)[0], crate::cert::ef_coords(&sc)[0]), v != sc);
        let (wit, _) = hidden::build9(&ntt, &base.records, &base.inputs);
        let nv = (n * SLOTS).trailing_zeros() as usize;
        let mut st = 0x9e37_79b9_7f4a_7c15u64;
        let pt: Vec<EF> = (0..nv)
            .map(|_| {
                st ^= st << 13;
                st ^= st >> 7;
                st ^= st << 17;
                EF::from(F::from_u64(st)) + EF::from(F::from_u64(st.rotate_left(17))) * crate::pcs::vroot()
            })
            .collect();
        let d0: Vec<F> = (0..n * SLOTS).map(|b| (0..4).fold(F::ONE, |a, j| a * (F::ONE - wit.bits[j][b]))).collect();
        let mle_d0 = crate::field::mle_eval(&d0, &pt);
        let prod = (0..4).fold(EF::ONE, |a, j| a * (EF::ONE - crate::field::mle_eval(&wit.bits[j], &pt)));
        t.check("false shortcut for d0 = prod (1 - Bj): MLE(d0)(r) != prod (1 - MLE(Bj)(r)) on honest bits", mle_d0 != prod);
        t.expect("prover sends shortcut values for the re-indexed bit claims", &run(&base, None, None, &Opts9 { shortcut_bits: true, ..Default::default() }).res, false);
    }

    // ---------------------------------------------------------------- C. ported tests
    println!("## C. ported response, ternarity, hint-budget, statement, byte, Gruen, layout tests");
    for (label, mode, accept) in [
        ("out-of-range z = +524168 (one coefficient; relation and all other bounds exact)", relaxed::Mode::ZEdge(1), false),
        ("out-of-range z = -524168 (one coefficient; relation and all other bounds exact)", relaxed::Mode::ZEdge(-1), false),
        ("residual outside its region (u moved by 2 at one coefficient; all else exact)", relaxed::Mode::ResidualOut, false),
    ] {
        let s = relaxed::sign(&ntt, &key, &rec.ctx, &rec.msg, mode, label.as_bytes());
        t.expect(label, &run(&with(&s), None, None, &d).res, accept);
    }
    {
        let mut c = base.clone();
        c.inputs[0].z[5] += mlnat::QI;
        t.expect("z coefficient + q (mod-q relation unchanged, range only)", &run(&c, None, None, &d).res, false);
    }
    {
        let s = relaxed::sign(&ntt, &key, &rec.ctx, &rec.msg, relaxed::Mode::Hints(76), b"r9h-hints-76");
        let c = with(&s);
        let f = |nu: &mut Vec<u8>| {
            nu[0] -= 1;
            nu[1] += 1;
        };
        t.expect("signature 0 has 76 hints, published nu_0 = 75 and nu_1 + 1 (total unchanged)", &run(&c, None, Some(&f), &d).res, false);
        let keep = |_: &mut Vec<u8>| {};
        t.expect("signature 0 has 76 hints, published nu_0 = 76", &run(&c, None, Some(&keep), &d).res, false);
    }
    // Statement mutations against the honest certificate, with and without the rewritten manifest.
    let mutate: [(&str, fn(&mut Vec<Record>)); 3] = [
        ("records 0 and 1 reordered", |s| s.swap(0, 1)),
        ("contexts of records 0 and 1 swapped", |s| {
            let c0 = s[0].ctx.clone();
            s[0].ctx = s[1].ctx.clone();
            s[1].ctx = c0;
        }),
        ("public keys of records 0 and 1 swapped", |s| {
            let p0 = s[0].pk.clone();
            s[0].pk = s[1].pk.clone();
            s[1].pk = p0;
        }),
    ];
    for (label, f) in mutate {
        let mut st = base.records.clone();
        f(&mut st);
        let c = Case { records: st.clone(), ..base.clone() };
        t.expect(&format!("honest certificate, {label} in the statement"), &verify(&c, &h.bytes), false);
        let mut bad = h.bytes.clone();
        bad[..crate::cert::MANIFEST].copy_from_slice(&hidden::manifest_lab9(&st));
        t.expect(&format!("honest certificate + rewritten manifest, {label}"), &verify(&c, &bad), false);
        let c2 = Case { records: st, inputs: base.inputs.clone(), raw: base.raw.clone() };
        t.expect(&format!("{label}: prover runs on the resulting witness (witness in the original order)"), &run(&c2, None, None, &d).res, false);
    }
    {
        let mut c = base.clone();
        c.inputs[0].u[100] = (c.inputs[0].u[100] + 1) % 16;
        t.expect("wrong u: one nibble of u_0 changed, prover runs on the resulting witness", &run(&c, None, None, &d).res, false);
    }
    {
        let yq = |w: &mut Wit9| {
            let b = 3 * SLOTS + 77;
            w.w.y[b] += F::from_u64(mlnat::Q as u64);
            w.w.ei[b] += mlnat::Q as i32;
            hidden::recount(w);
        };
        t.expect("residual cell Y + q (mod-q relation unchanged, range only)", &run(&base, Some(&yq), None, &d).res, false);
        let ms = |w: &mut Wit9| {
            let k = (0..w.w.m.len()).find(|&k| w.w.m[k] != F::ZERO).unwrap();
            w.w.m[k] -= F::ONE;
            w.w.m[k + 1] += F::ONE;
        };
        t.expect("multiplicity table: one count moved from t to t+1", &run(&base, Some(&ms), None, &d).res, false);
        t.expect("one lift quotient V + 1, everything else honest", &run(&base, None, None, &Opts9 { quot_delta: 1, ..Default::default() }).res, false);
        let sm = |w: &mut Wit9| {
            let a = (0..SLOTS).find(|&k| w.w.s[k] != F::ZERO).unwrap();
            let b = (0..SLOTS).find(|&k| w.w.s[k] == F::ZERO).unwrap();
            w.w.s.swap(a, b);
        };
        t.expect("selector moved between two cells of signature 0 (count unchanged)", &run(&base, Some(&sm), None, &d).res, false);
        let lastx = |w: &mut Wit9| {
            let b = (n - 1) * SLOTS + 7 * 256 - 1;
            w.w.x[b] += F::ONE;
            hidden::recount(w);
        };
        t.expect("final real X coordinate (last signature, z_6[255]) + 1, multiplicities recounted", &run(&base, Some(&lastx), None, &d).res, false);
        let lasty = |w: &mut Wit9| {
            let b = n * SLOTS - 1;
            w.w.y[b] += F::ONE;
            hidden::recount(w);
        };
        t.expect("final residual coordinate (last signature, slot 2047) + 1, multiplicities recounted", &run(&base, Some(&lasty), None, &d).res, false);
        let lastb = |w: &mut Wit9| {
            let b = n * SLOTS - 1;
            w.bits[3][b] = F::ONE - w.bits[3][b];
        };
        t.expect("final bit of the last signature flipped (B3 at slot 2047)", &run(&base, Some(&lastb), None, &d).res, false);
    }
    // Ternarity isolation (round 4 A.2): S = 1/2 at four hint-zero cells.
    {
        let tw = |w: &mut Wit9| {
            crate::inject_half_from(&mut w.w, 0);
        };
        t.expect("S = 1/2 at four interior hint-zero cells, full verifier", &run(&base, Some(&tw), None, &d).res, false);
        let ctl = Opts9 { drop_ternarity: true, ..Default::default() };
        t.expect("same witness, UNSAFE control without the S^3 = S weight (same statement, profile, schedule)", &run(&base, Some(&tw), None, &ctl).res, true);
        t.expect("honest batch, UNSAFE ternarity control (the control is complete)", &run(&base, None, None, &ctl).res, true);
    }
    // Layout: columns committed in another order.
    t.expect("columns committed as [Y, X, S, ...]", &run(&base, None, None, &Opts9 { swap_cols: Some((0, 1)), ..Default::default() }).res, false);
    t.expect("bit planes B0 and B1 committed in the other order", &run(&base, None, None, &Opts9 { swap_cols: Some((hidden::COL_B, hidden::COL_B + 1)), ..Default::default() }).res, false);
    // Gruen exceptional challenges (LogUp GKR rounds and betas, table rounds; both sides).
    {
        use crate::pcs::Inject;
        let tw = |w: &mut Wit9| {
            crate::inject_half_from(&mut w.w, 0);
        };
        let ms = |w: &mut Wit9| {
            let k = (0..w.w.m.len()).find(|&k| w.w.m[k] != F::ZERO).unwrap();
            w.w.m[k] -= F::ONE;
            w.w.m[k + 1] += F::ONE;
        };
        for mode in [Inject::Zero, Inject::One, Inject::Half, Inject::EqZero, Inject::Vroot] {
            let o = Opts9 { inject: mode, ..Default::default() };
            let hb = run(&base, None, None, &o);
            t.expect(&format!("{mode:?}: honest certificate"), &hb.res, true);
            t.expect(&format!("{mode:?}: S = 1/2 witness"), &run(&base, Some(&tw), None, &o).res, false);
            t.expect(&format!("{mode:?}: one multiplicity moved"), &run(&base, Some(&ms), None, &o).res, false);
            let vo = Opts9 { inject: mode, ..Default::default() };
            let off = hb.sz.offset("LogUp GKR") + (0..5).map(|k| (2 * k + 4) * 40).sum::<usize>() + 2 * 40;
            let mut bad = hb.bytes.clone();
            bad[off] ^= 4;
            t.expect(&format!("{mode:?}: LogUp GKR layer 5, round 2, a1 tampered"), &hidden::verify_lab9(&base.records, &bad, &mut Timer::new(), &vo), false);
            let off = hb.sz.offset("table sumcheck") + 3 * 80;
            let mut bad = hb.bytes.clone();
            bad[off] ^= 4;
            t.expect(&format!("{mode:?}: table round 4, a1 tampered"), &hidden::verify_lab9(&base.records, &bad, &mut Timer::new(), &vo), false);
        }
    }
    // Tampered bytes: two positions in every component, sixteen in the WHIR proof.
    for (name, len) in h.sz.parts.clone() {
        if len == 0 || name == "WHIR length" {
            continue;
        }
        let off = h.sz.offset(&name);
        let picks: Vec<usize> = if name == "WHIR proof" { (0..16).map(|k| off + (len * (2 * k + 1)) / 32).collect() } else { vec![off + len / 3, off + len - 1] };
        for p in picks {
            let mut bad = h.bytes.clone();
            bad[p] ^= 0x04;
            t.expect(&format!("tampered byte {p} ({name})"), &verify(&base, &bad), false);
        }
    }
    {
        let mut bad = h.bytes.clone();
        bad.push(0);
        t.expect("one trailing byte appended", &verify(&base, &bad), false);
        let wl = h.sz.get("WHIR proof");
        let at = h.bytes.len() - 4 - wl;
        let mut bad = h.bytes.clone();
        bad[at..at + 4].copy_from_slice(&((wl + 1) as u32).to_le_bytes());
        bad.push(0);
        t.expect("byte appended inside the WHIR proof, length raised", &verify(&base, &bad), false);
    }
    // Challenge-prefix sensitivity: every statement component reaches the first coin block.
    {
        let table = hidden::registered_table9(hidden::lab_profile9(n), n).unwrap();
        let c = hidden::Cert9::from_bytes(n, &h.bytes).unwrap();
        let x_of = |recs: &[Record], man: &[u8], ct: &[u8], nu: &[u8]| hidden::instance_lab9(hidden::lab_profile9(n), man, recs, ct, nu);
        let man0 = hidden::manifest_lab9(&base.records);
        let (q0, th0) = prefix9(table.clone(), &x_of(&base.records, &man0, &c.ct, &c.nu), c.comm, &c.quot);
        type Mut = fn(&mut Record, usize);
        let fields: [(&str, Mut); 3] = [("message", |r, _| r.msg[0] ^= 1), ("context", |r, _| r.ctx[0] ^= 1), ("public key", |r, i| r.pk[100 + i] ^= 1)];
        for (label, f) in fields {
            let changed = (0..n)
                .into_par_iter()
                .filter(|&i| {
                    let mut st = base.records.clone();
                    f(&mut st[i], i);
                    prefix9(table.clone(), &x_of(&st, &hidden::manifest_lab9(&st), &c.ct, &c.nu), c.comm, &c.quot).0 != q0
                })
                .count();
            t.check(&format!("each record's {label} (one bit): round-1 projection pool changed in {changed}/{n}"), changed == n);
        }
        let changed = (0..n)
            .into_par_iter()
            .filter(|&i| {
                let mut ct = c.ct.clone();
                ct[64 * i + i % 64] ^= 1;
                prefix9(table.clone(), &x_of(&base.records, &man0, &ct, &c.nu), c.comm, &c.quot).0 != q0
            })
            .count();
        t.check(&format!("each signature's public c_tilde (one bit): pool changed in {changed}/{n}"), changed == n);
        let changed = (0..n)
            .into_par_iter()
            .filter(|&i| {
                let mut nu = c.nu.clone();
                nu[i] ^= 1;
                prefix9(table.clone(), &x_of(&base.records, &man0, &c.ct, &nu), c.comm, &c.quot).0 != q0
            })
            .count();
        t.check(&format!("each hint count (+-1): pool changed in {changed}/{n}"), changed == n);
        let changed = (0..64)
            .into_par_iter()
            .filter(|&k| {
                let mut cm = c.comm;
                cm[k] ^= 1;
                prefix9(table.clone(), &x_of(&base.records, &man0, &c.ct, &c.nu), cm, &c.quot).0 != q0
            })
            .count();
        t.check(&format!("initial commitment (each of 64 bytes): pool changed in {changed}/64"), changed == 64);
        let changed = (0..crate::cert::MANIFEST)
            .into_par_iter()
            .filter(|&k| {
                let mut m = man0.clone();
                m[k] ^= 1;
                prefix9(table.clone(), &x_of(&base.records, &m, &c.ct, &c.nu), c.comm, &c.quot).0 != q0
            })
            .count();
        t.check(&format!("manifest (each of 512 bytes): pool changed in {changed}/512"), changed == 512);
        let nq = c.quot.len() / 5;
        let changed = (0..nq)
            .filter(|&k| {
                let mut qb = c.quot.clone();
                qb[5 * k] ^= 1;
                let (q, th) = prefix9(table.clone(), &x_of(&base.records, &man0, &c.ct, &c.nu), c.comm, &qb);
                q == q0 && th != th0
            })
            .count();
        t.check(&format!("each lift quotient (+-1): pool unchanged, theta changed in {changed}/{nq}"), changed == nq);
    }

    // ---------------------------------------------------------------- D. range binding
    if n == 128 {
        range_binding(&mut t);
    }

    // ---------------------------------------------------------------- E. round-10 profile rules
    r10_rules(&mut t, &base, &h.bytes);

    // ---------------------------------------------------------------- F. Fiat-Shamir on GKR
    fs_on_gkr(&mut t, &base, &h.bytes);

    // ---------------------------------------------------------------- G. hostile gates (r10 review E)
    hostile_gates(&mut t, &base, &h.bytes);

    println!("H9 TESTS SUMMARY: {}/{} behave as expected", t.pass, t.total);
    if !t.unexpected.is_empty() {
        println!("unexpected: {:?}", t.unexpected);
    }
    println!("uptime at end: {}", crate::uptime());
}

fn quiet_panic<R>(f: impl FnOnce() -> R) -> std::thread::Result<R> {
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    std::panic::set_hook(hook);
    r
}

/// Prove the lab statement for `records` with an explicit raw instance (and options), from the
/// witness of `c`; returns the certificate bytes or None if the prover refused (panicked).
fn prove_with_x(c: &Case, records: &[Record], x: &[u8], o: &Opts9) -> Option<Vec<u8>> {
    let ntt = Ntt::new();
    let (wit, pubs) = hidden::build9(&ntt, &c.records, &c.inputs);
    let nu: Vec<u8> = wit.w.counts.iter().map(|&v| v.min(crate::cert::NU_MAX)).collect();
    let man = hidden::manifest_lab9(records);
    let n = records.len();
    quiet_panic(|| hidden::prove_stmt9(records, &man, x, hidden::lab_profile9(n), &wit, &pubs, &nu, &mut Timer::new(), o).0.to_bytes().0).ok()
}

/// Round-10 profile rules: the strict F_q pool (REQ-2) and the tree-separated node hash (REQ-1).
fn r10_rules(t: &mut Tally, base: &Case, honest: &[u8]) {
    use std::sync::atomic::Ordering::Relaxed;
    println!("## E. round-10 profile rules: strict F_q pool, tree-separated Merkle nodes");
    for (name, ok) in crate::fs7::r10_selfcheck() {
        t.check(&name, ok);
    }
    let n = base.records.len();
    let table = hidden::registered_table9(hidden::lab_profile9(n), n).unwrap();
    let s1 = &table.def(1).shape;
    t.check(&format!("round 1 registers nq = {} with slack {} (512 + ceil(nq / 400))", s1.nq, s1.qslack), s1.qslack == crate::fs7::qslack10(s1.nq) && s1.qslack as usize > 512);
    crate::fs7::FORCE_SHORT_Q.store(true, Relaxed);
    let refused = {
        let ntt = Ntt::new();
        let (wit, pubs) = hidden::build9(&ntt, &base.records, &base.inputs);
        let nu: Vec<u8> = wit.w.counts.iter().map(|&v| v.min(crate::cert::NU_MAX)).collect();
        quiet_panic(|| hidden::prove_lab9(&base.records, &wit, &pubs, &nu, &mut Timer::new(), &Opts9::default())).is_err()
    };
    t.check("forced-short F_q pool: the prover refuses (no padding)", refused);
    let r = verify(base, honest);
    crate::fs7::FORCE_SHORT_Q.store(false, Relaxed);
    t.expect("forced-short F_q pool: the verifier rejects the honest certificate", &r, false);
    t.expect("pool rule restored: the honest certificate verifies again", &verify(base, honest), true);
    // A prover that hashes every Merkle node with the witness tree's round (1).
    crate::reg7::NODE_ROUND_OVERRIDE.store(1, Relaxed);
    let x = {
        let man = hidden::manifest_lab9(&base.records);
        let c = hidden::Cert9::from_bytes(n, honest).unwrap();
        hidden::instance_lab9(hidden::lab_profile9(n), &man, &base.records, &c.ct, &c.nu)
    };
    let forged = prove_with_x(base, &base.records, &x, &Opts9::default());
    crate::reg7::NODE_ROUND_OVERRIDE.store(0, Relaxed);
    match forged {
        Some(b) => {
            t.check("fold-tree nodes hashed with the witness tree's round: the commitment roots change", b[..b.len().min(honest.len())] != honest[..b.len().min(honest.len())]);
            t.expect("fold-tree nodes hashed with the witness tree's round: rejected", &verify(base, &b), false);
        }
        None => t.check("fold-tree nodes hashed with the witness tree's round: prover ran", false),
    }
}

/// Fiat-Shamir on GKR (KRS25, eprint 2025/118; the round-10 review's T-FS1 .. T-FS5).
fn fs_on_gkr(t: &mut Tally, base: &Case, honest: &[u8]) {
    use sha3::{Digest, Sha3_512};
    println!("## F. Fiat-Shamir on GKR: the raw instance is absorbed in full, before the first coin");
    let n = base.records.len();
    let c = hidden::Cert9::from_bytes(n, honest).unwrap();
    let man = hidden::manifest_lab9(&base.records);
    let x = hidden::instance_lab9(hidden::lab_profile9(n), &man, &base.records, &c.ct, &c.nu);
    // T-FS1: coins derived with the instance frame replaced by an empty frame.
    {
        let mut xe = Vec::new();
        xe.extend_from_slice(b"Qlyphs/Archive/Instance/r10-lab\0");
        xe.extend_from_slice(&crate::fs7::le32(hidden::lab_profile9(n)));
        xe.extend_from_slice(&crate::fs7::frame(0x0100, &man));
        xe.extend_from_slice(&crate::fs7::frame(0x0110, &[]));
        xe.extend_from_slice(&crate::fs7::frame(0x0105, &c.ct));
        xe.extend_from_slice(&crate::fs7::frame(0x0104, &c.nu));
        let r = prove_with_x(base, &base.records, &xe, &Opts9::default()).map(|b| verify(base, &b)).unwrap_or(Ok(()));
        t.expect("T-FS1 coins derived with the records frame replaced by an empty frame", &r, false);
    }
    // T-FS2: digest-only absorption.
    {
        let xd = Sha3_512::digest(&x).to_vec();
        let r = prove_with_x(base, &base.records, &xd, &Opts9::default()).map(|b| verify(base, &b)).unwrap_or(Ok(()));
        t.expect("T-FS2 coins derived from SHA3-512(instance) instead of the instance", &r, false);
    }
    // T-FS3: one statement byte changed against the unchanged proof, manifest re-derived.
    {
        let table = hidden::registered_table9(hidden::lab_profile9(n), n).unwrap();
        let q0 = prefix9(table.clone(), &x, c.comm, &c.quot).0;
        let x_of = |recs: &[Record], ct: &[u8], nu: &[u8]| hidden::instance_lab9(hidden::lab_profile9(n), &hidden::manifest_lab9(recs), recs, ct, nu);
        let muts: [(&str, Box<dyn Fn(&mut Record)>); 3] = [("message", Box::new(|r: &mut Record| r.msg[0] ^= 1)), ("context", Box::new(|r: &mut Record| r.ctx[0] ^= 1)), ("public key", Box::new(|r: &mut Record| r.pk[100] ^= 1))];
        for (what, f) in muts.iter() {
            let mut recs = base.records.clone();
            f(&mut recs[n / 2]);
            let r = hidden::verify_lab9(&recs, honest, &mut Timer::new(), &Opts9::default());
            t.expect(&format!("T-FS3 one {what} byte of record {} changed, proof kept", n / 2), &r, false);
            t.check(&format!("T-FS3 ({what}): the round-1 coin prefix changes"), prefix9(table.clone(), &x_of(&recs, &c.ct, &c.nu), c.comm, &c.quot).0 != q0);
        }
        let mut b = honest.to_vec();
        b[crate::cert::MANIFEST + 64 * 3 + 5] ^= 1;
        t.expect("T-FS3 one c_tilde byte changed, proof kept", &verify(base, &b), false);
        let mut ct = c.ct.clone();
        ct[64 * 3 + 5] ^= 1;
        t.check("T-FS3 (c_tilde): the round-1 coin prefix changes", prefix9(table.clone(), &x_of(&base.records, &ct, &c.nu), c.comm, &c.quot).0 != q0);
        let mut b = honest.to_vec();
        let pos = crate::cert::MANIFEST + 64 * n + 7;
        b[pos] = if b[pos] == 0 { 1 } else { b[pos] - 1 };
        t.expect("T-FS3 one hint count changed, proof kept", &verify(base, &b), false);
        let mut nu = c.nu.clone();
        nu[7] = b[pos];
        t.check("T-FS3 (hint count): the round-1 coin prefix changes", prefix9(table.clone(), &x_of(&base.records, &c.ct, &nu), c.comm, &c.quot).0 != q0);
    }
    // T-FS4: the prover derives the coins for x, then proves records 0 and 1 swapped.
    {
        let mut sw = base.clone();
        sw.records.swap(0, 1);
        sw.inputs.swap(0, 1);
        let r = prove_with_x(&sw, &base.records, &x, &Opts9::default());
        match r {
            Some(b) => {
                t.expect("T-FS4 records swapped after the round-1 coins (verified against x)", &verify(base, &b), false);
                t.expect("T-FS4 the same proof against the swapped statement", &hidden::verify_lab9(&sw.records, &b, &mut Timer::new(), &Opts9::default()), false);
            }
            None => t.check("T-FS4 the prover refused the swapped witness (counts as rejection)", true),
        }
    }
    // T-FS5: coins from another round-1 descriptor, or another profile id in the coin input.
    {
        let table = hidden::registered_table9(hidden::lab_profile9(n), n).unwrap();
        let mut t1 = (*table).clone();
        t1.rounds[0].shape.qslack += 1;
        t1.formal_len = t1.rounds.iter().map(|d| d.shape.used()).max().unwrap();
        let r = prove_with_x(base, &base.records, &x, &Opts9 { table_override: Some(hidden::TableOv(Arc::new(t1))), ..Default::default() }).map(|b| verify(base, &b)).unwrap_or(Ok(()));
        t.expect("T-FS5 coins derived for another round-1 descriptor (slack + 1)", &r, false);
        let mut t2 = (*table).clone();
        t2.profile ^= 0x200;
        let r = prove_with_x(base, &base.records, &x, &Opts9 { table_override: Some(hidden::TableOv(Arc::new(t2))), ..Default::default() }).map(|b| verify(base, &b)).unwrap_or(Ok(()));
        t.expect("T-FS5 coins derived with the other family's profile id in the coin input", &r, false);
    }
}

/// Hostile gates of the round-10 review (section E).
fn hostile_gates(t: &mut Tally, base: &Case, honest: &[u8]) {
    use p3_field::{Field, TwoAdicField};
    use std::sync::atomic::Ordering::Relaxed;
    println!("## G. hostile gates (round-10 review, section E)");
    let n = base.records.len();
    let d = Opts9::default();
    // Coordinated non-Boolean planes: B0 = 1/2 and B1 = (1 + sqrt 2)/2 at one cell, so
    // (B0^2 - B0) + (B1^2 - B1) = -1/4 + 1/4 = 0: an unweighted sum would not see them.
    {
        let z8 = F::two_adic_generator(3);
        let sqrt2 = z8 + z8.exp_u64(7);
        let h = F::TWO.inverse();
        let b0 = h;
        let b1 = (F::ONE + sqrt2) * h;
        let cancel = (b0 * b0 - b0) + (b1 * b1 - b1);
        t.check(&format!("coordinated planes: sqrt2^2 = 2 ({}), B0 = 1/2, B1 = (1 + sqrt 2)/2, unweighted Booleanity sum at the cell = 0 ({})", sqrt2 * sqrt2 == F::TWO, cancel == F::ZERO), sqrt2 * sqrt2 == F::TWO && cancel == F::ZERO);
        let tw = move |w: &mut Wit9| {
            w.bits[0][5] = b0;
            w.bits[1][5] = b1;
        };
        t.expect("coordinated non-Boolean planes cancelling under a fixed sum (Booleanity uses four independent weights)", &run(base, Some(&tw), None, &d).res, false);
    }
    // Multiplicities chosen after theta.
    t.expect("multiplicities moved after theta (committed ones unchanged)", &run(base, None, None, &Opts9 { mult_after_theta: true, ..Default::default() }).res, false);
    // An opened value changed after alpha: the last 40 bytes of the WHIR proof are an opening.
    {
        let c = hidden::Cert9::from_bytes(n, honest).unwrap();
        let off = honest.len() - c.whir.len();
        for (k, name) in [(1usize, "last opened value"), (41, "second-to-last opened value")] {
            let mut b = honest.to_vec();
            b[off + c.whir.len() - k] ^= 1;
            t.expect(&format!("opening value changed after alpha ({name})"), &verify(base, &b), false);
        }
    }
    // Active-slot sign conversion of the packed trace.
    {
        let ntt = Ntt::new();
        let (wit, _) = hidden::build9(&ntt, &base.records, &base.inputs);
        let (a, b) = hidden::sign_conversion_check(&wit);
        t.check(&format!("sign conversion: packed input layer unpacks to the field input rows (bit 0 -> +1, 1 -> -1, padding and dummy slots -> 0): {b}/{a} cells"), a == b);
    }
    let (a, b) = crate::keccak::kec10::chi_truth_table(0x51ed);
    t.check(&format!("chi under A = 1 - 2a: truth table (8 triples) and A(1 - B + C + BC)/2 at 64 random points: {a}/{b}"), a == b);
    let (a, b) = crate::keccak::kec10::zero_terms();
    t.check(&format!("every layer term vanishes on the zero vector (skipped dummy pairs contribute 0): {a}/{b}"), a == b);
    // Per-tree hash domains: every hash of a commitment under its own commit round.
    {
        crate::reg7::TREE_COUNTS.lock().unwrap().clear();
        crate::reg7::COUNT.store(true, Relaxed);
        let o = run(base, None, None, &d);
        crate::reg7::COUNT.store(false, Relaxed);
        let m = std::mem::take(&mut *crate::reg7::TREE_COUNTS.lock().unwrap());
        let table = hidden::registered_table9(hidden::lab_profile9(n), n).unwrap();
        let reals: Vec<u32> = table.rounds.iter().enumerate().filter(|(_, x)| x.body == crate::reg7::Body::Real).map(|(i, _)| (i + 1) as u32).collect();
        let ok = o.res.is_ok() && m.keys().all(|k| reals.contains(k)) && reals.iter().all(|r| m.contains_key(r));
        t.check(&format!("per-tree hash domains: hashes only under the {} registered commit rounds {:?}, each tree hashed (prover and verifier counted together: {:?})", reals.len(), reals, m), ok);
    }
}

/// Prove a lab chain range of 16 blocks; `attack` may change the prover's records and
/// signatures before the witness is built.
fn prove_range9(ch: &Chain, r: std::ops::Range<usize>, attack: &dyn Fn(&mut Vec<Record>, &mut Vec<Vec<u8>>)) -> Vec<u8> {
    let ntt = Ntt::new();
    let parent = if r.start == 0 { &ch.anchor } else { &ch.headers[r.start - 1] };
    let mut records = chain::replay(&ch.net, &ch.blocks[r.clone()], &ch.state).unwrap();
    let mut sigs: Vec<Vec<u8>> = ch.blocks[r.clone()].iter().flat_map(|b| b.sigs.clone()).collect();
    attack(&mut records, &mut sigs);
    let n = records.len();
    let inputs: Vec<SigIn9> = records.par_iter().zip(sigs.par_iter()).map(|(rc, sg)| hidden::input_from_raw9(&ntt, rc, sg)).collect();
    let (wit, pubs) = hidden::build9(&ntt, &records, &inputs);
    let nu: Vec<u8> = wit.w.counts.iter().map(|&c| c.min(crate::cert::NU_MAX)).collect();
    let man = hidden::manifest_chain9(&ch.net, n, parent, &ch.headers[r.clone()]);
    let ct: Vec<u8> = wit.ct.iter().flatten().copied().collect();
    let x = hidden::instance_chain9(&ch.net, parent, &ch.headers[r.clone()], &ch.blocks[r.clone()], &records, &ct, &nu);
    let (c, rep) = hidden::prove_stmt9(&records, &man, &x, hidden::lab_chain_profile9(n), &wit, &pubs, &nu, &mut Timer::new(), &Opts9::default());
    if let Some(e) = &rep.transcript_error {
        println!("  (prover transcript error: {e})");
    }
    c.to_bytes().0
}

fn range_binding(t: &mut Tally) {
    println!("## D. range binding (lab chain profile, 16 blocks x 8 records)");
    let nb = 16;
    let per = 8;
    let n = nb * per;
    let net = chain::network_id(b"r9h-lab");
    let ch = chain::build(net, chain::genesis(&net), 0, 2 * nb, per, 0);
    let range = 0..nb;
    let hdrs = &ch.headers[range.clone()];
    let blocks = &ch.blocks[range.clone()];
    let none = |_: &mut Vec<Record>, _: &mut Vec<Vec<u8>>| {};
    let d = Opts9::default();
    let vr = |anchor: &chain::Header, h: &[chain::Header], b: &[chain::Block], st: &chain::State, bytes: &[u8]| hidden::verify_range9(&net, anchor, h, b, st, bytes, &mut Timer::new(), &d);
    let bytes = prove_range9(&ch, range.clone(), &none);
    t.expect("honest certificate for heights 0..15", &vr(&ch.anchor, hdrs, blocks, &ch.state, &bytes), true);
    let r = chain::verify_range(&net, &ch.anchor, hdrs, blocks, &ch.state, &bytes, &mut Timer::new()).map(|_| ());
    t.expect("the production chain verifier on the hidden-u lab certificate", &r, false);
    let mut sw = ch.blocks.clone();
    sw[2].records.swap(0, 1);
    sw[2].sigs.swap(0, 1);
    t.expect("replayed bodies with records 0 and 1 of block 2 reordered", &vr(&ch.anchor, hdrs, &sw[range.clone()], &ch.state, &bytes), false);
    let mut st = ch.state.clone();
    let victim = (chain::sender(per as u64 + 3), 0u64);
    st.keys.insert(victim, ch.state.keys[&(chain::sender(per as u64 + 4), 0)].clone());
    t.expect("state resolves one record to another key", &vr(&ch.anchor, hdrs, blocks, &st, &bytes), false);
    let mut hb = hdrs.to_vec();
    hb[7].acc[0] ^= 1;
    let mut prev = ch.anchor.id;
    for hd in hb.iter_mut() {
        hd.parent = prev;
        hd.id = chain::header_id(&hd.parent, hd.height, &hd.acc);
        prev = hd.id;
    }
    t.expect("header A[7] changed (ids relinked)", &vr(&ch.anchor, &hb, blocks, &ch.state, &bytes), false);
    let anchor_b = {
        let acc = chain::h(b"fork-b-parent", &net);
        chain::Header { height: u64::MAX, parent: [1; 32], acc, id: chain::header_id(&[1; 32], u64::MAX, &acc) }
    };
    let fb = chain::build(net, anchor_b.clone(), 0, nb, per, 0);
    t.expect("cross-fork: same bodies on another parent", &vr(&anchor_b, &fb.headers, &fb.blocks, &fb.state, &bytes), false);
    let mut rw = bytes.clone();
    rw[..crate::cert::MANIFEST].copy_from_slice(&hidden::manifest_chain9(&net, n, &anchor_b, &fb.headers));
    t.expect("cross-fork with the manifest rewritten to fork B", &vr(&anchor_b, &fb.headers, &fb.blocks, &fb.state, &rw), false);
    let r2 = nb..2 * nb;
    t.expect("certificate for heights 0..15 checked as heights 16..31", &vr(&ch.headers[nb - 1], &ch.headers[r2.clone()], &ch.blocks[r2.clone()], &ch.state, &bytes), false);
    let mut rw = bytes.clone();
    rw[..crate::cert::MANIFEST].copy_from_slice(&hidden::manifest_chain9(&net, n, &ch.headers[nb - 1], &ch.headers[r2.clone()]));
    t.expect("the same with the manifest rewritten to heights 16..31", &vr(&ch.headers[nb - 1], &ch.headers[r2.clone()], &ch.blocks[r2], &ch.state, &rw), false);
    let reorder = |r: &mut Vec<Record>, s: &mut Vec<Vec<u8>>| {
        r.swap(2 * per, 2 * per + 1);
        s.swap(2 * per, 2 * per + 1);
    };
    let b2 = prove_range9(&ch, range.clone(), &reorder);
    t.expect("prover proves block 2 with records 0 and 1 reordered (valid proof of the permuted list)", &vr(&ch.anchor, hdrs, blocks, &ch.state, &b2), false);
    let g = 256u64.min(n as u64 - 1) & !255;
    let g = if g == 0 { (0..n as u64).find(|&x| chain::rotated(x)).unwrap_or(0) } else { g };
    let oldkey = move |r: &mut Vec<Record>, s: &mut Vec<Vec<u8>>| {
        let kp = chain::keypair(g, 0, b"");
        let i = g as usize;
        r[i].pk = kp.verification_key.as_slice().to_vec();
        s[i] = libcrux_ml_dsa::ml_dsa_87::sign(&kp.signing_key, &r[i].msg, &r[i].ctx, [7u8; 32]).unwrap().as_slice().to_vec();
    };
    println!("  key rotation: transaction {g} rotated: {}", chain::rotated(g));
    let b3 = prove_range9(&ch, range.clone(), &oldkey);
    t.expect("prover authorizes a record with the rotated-out epoch-0 key (valid signature under that key)", &vr(&ch.anchor, hdrs, blocks, &ch.state, &b3), false);
    let mut bad = bytes.clone();
    let off = crate::cert::MANIFEST + 64 * 9;
    bad[off] ^= 1;
    t.expect("one c_tilde bit of record 9 changed in the certificate (accumulator)", &vr(&ch.anchor, hdrs, blocks, &ch.state, &bad), false);
}
