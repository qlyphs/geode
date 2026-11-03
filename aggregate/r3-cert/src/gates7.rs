//! Round 7 acceptance gates (spec end of §9) for profile 0x00070001 at N = 2048, on the
//! synthetic chain (16 blocks x 128 records). Gate 5 (the soundness suites rerun under the new
//! transcript) is `soundness v7`, `r4 v7` and `chain 128 v7`.

use std::sync::atomic::Ordering;
use std::time::Instant;

use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use rayon::prelude::*;

use crate::cert::{self, Reject, Timer};
use crate::field::{EF, F, ef_to_bytes};
use crate::fs7::{self, CoinState, PROFILE_V7};
use crate::mlnat::Record;
use crate::reg7::{self, Body};
use crate::{chain, mlnat, proj, witness};

fn check(name: &str, ok: bool, tally: &mut (usize, usize)) {
    tally.1 += 1;
    tally.0 += ok as usize;
    println!("[{}] {name}", if ok { "PASS" } else { "FAIL" });
}

fn efs(xs: &[EF]) -> Vec<u8> {
    let mut b = Vec::with_capacity(40 * xs.len());
    xs.iter().for_each(|x| ef_to_bytes(x, &mut b));
    b
}

fn verdict(r: &Result<cert::VerifyReport, Reject>) -> String {
    match r {
        Ok(_) => "ACCEPT".into(),
        Err(e) => format!("REJECT {e:?}"),
    }
}

pub fn run() {
    println!("# r3-cert round 7 acceptance gates, profile 0x00070001 (QLYAUTH7), N = 2048");
    println!("uptime at start: {}", crate::uptime());
    let mut tally = (0usize, 0usize);
    let (nb, per_block) = (16usize, 128usize);
    let n = nb * per_block;
    let net = chain::network_id(b"r7-gates");
    let t = Instant::now();
    let ch = chain::build(net, chain::genesis(&net), 0, nb, per_block, 0);
    println!("chain: {nb} blocks x {per_block} records built and node-validated in {:.0} ms", t.elapsed().as_secs_f64() * 1e3);

    // The registration.
    let table = cert::registered_table(PROFILE_V7, n, false).expect("profile 0x00070001 is registered at N = 2048");
    println!("-- registered round table: {} rounds, {} scalar singletons, formal L = {} B, decoder prefixes {} B in total", table.len(), table.scalar_rounds(), table.formal_len, table.used_total());
    let mut prev = "";
    let mut start = 1;
    for i in 1..=table.len() + 1 {
        let l = if i <= table.len() { table.def(i).label } else { "" };
        if l != prev {
            if !prev.is_empty() {
                let d = table.def(start);
                let range = if i - 1 > start { format!("{start}-{}", i - 1) } else { format!("{start}") };
                let body = match d.body {
                    Body::Real => "real tree".to_string(),
                    Body::Scalar(b) => format!("{b} B body"),
                };
                let idx = if d.shape.widths.is_empty() { String::new() } else { format!(", {} indices of {} bits", d.shape.widths.len(), d.shape.widths[0]) };
                println!("  {range:>9}  {prev}: {body}; nk {}{}{}{}; used {} B{}", d.shape.nk, if d.shape.theta { ", theta" } else { "" }, if d.shape.nq > 0 { format!(", nq {}", d.shape.nq) } else { String::new() }, idx, d.shape.used(), d.opens.map(|t| format!("; opens the tree of round {t}")).unwrap_or_default());
            }
            prev = l;
            start = i;
        }
    }
    let d = |i: usize| table.def(i);
    check(
        "round table matches spec §4 (279 explicit pair, 280 nk = 2127, 322 empty, 330/337/344 real, 331/338/345/350 indices 141x22/80x20/62x17/51x15 with gamma except 350, 350 body 16 K, 354 rounds)",
        table.len() == 354
            && d(279).body == Body::Scalar(80)
            && d(279).shape.nk == 2
            && d(280).shape.nk == 2127
            && d(322).body == Body::Scalar(0)
            && d(323).body == Body::Scalar(240)
            && [1, 330, 337, 344].iter().all(|&i| d(i).body == Body::Real)
            && (d(331).shape.widths == vec![22u8; 141] && d(331).shape.nk == 1 && d(331).opens == Some(1))
            && (d(338).shape.widths == vec![20u8; 80] && d(338).opens == Some(330))
            && (d(345).shape.widths == vec![17u8; 62] && d(345).opens == Some(337))
            && (d(350).shape.widths == vec![15u8; 51] && d(350).shape.nk == 0 && d(350).body == Body::Scalar(640) && d(350).opens == Some(344))
            && d(1).shape.nq == 57_344
            && d(2).shape.theta,
        &mut tally,
    );

    // Honest proof and verification with the adapters' logs.
    let ntt = mlnat::Ntt::new();
    let parent = &ch.anchor;
    let hdrs = &ch.headers[..];
    let records: Vec<Record> = chain::replay(&net, &ch.blocks, &ch.state).unwrap();
    let sigs: Vec<Vec<u8>> = ch.blocks.iter().flat_map(|b| b.sigs.clone()).collect();
    let inputs: Vec<witness::SigInput> = records.par_iter().zip(sigs.par_iter()).map(|(r, s)| witness::input_from_raw(&ntt, r, s)).collect();
    let (w, pubs) = witness::build(&ntt, &records, &inputs);
    let u: Vec<u8> = inputs.iter().flat_map(|i| i.u.clone()).collect();
    let nu: Vec<u8> = w.counts.iter().map(|&c| c.min(cert::NU_MAX)).collect();
    let ubytes = cert::ubytes_of(&u, n);
    let man = chain::manifest_v7(&net, n, parent, hdrs);
    let x = chain::instance_v7(&net, parent, hdrs, &ch.blocks, &records, &ubytes, &nu);
    println!("raw instance X: {} bytes (manifest, parent Header104, block section with {} AuthRecords and state keys, U, nu)", x.len(), n);
    let xof0 = proj::PROJ_XOF_CALLS.load(Ordering::Relaxed);
    let o = cert::Opts { log7: true, ..Default::default() };
    let mut tp = Timer::new();
    let (c, rep) = cert::prove_stmt7(&records, &man, &x, PROFILE_V7, &u, &nu, &w, &pubs, &mut tp, &o);
    drop(w);
    let (bytes, sz) = c.to_bytes();
    let mut tv = Timer::new();
    let (res, vins) = chain::verify_range_inspect(&net, parent, hdrs, &ch.blocks, &ch.state, &bytes, &mut tv, &o);
    let xof1 = proj::PROJ_XOF_CALLS.load(Ordering::Relaxed);
    println!("prover {:.0} ms, verifier {:.0} ms; certificate {} B (leaf pair {} B); VERIFY: {}", tp.total(), tv.total(), sz.total, sz.leaf_pair, verdict(&res));
    check("honest certificate accepted by the chain verifier under 0x00070001", res.is_ok() && rep.transcript_error.is_none(), &mut tally);
    let pins = rep.inspect.clone().expect("prover inspection");
    let vins = vins.expect("verifier inspection");
    let plog = pins.log.clone().unwrap();
    let vlog = vins.log.clone().unwrap();

    // Gate 1: exact agreement on all 354 blocks, full-preimage reference vs incremental/prefix.
    println!("## gate 1: full-preimage reference vs incremental prefix implementation, all {} blocks", table.len());
    let roots: Vec<[u8; 64]> = vlog.iter().map(|l| l.root).collect();
    let t = Instant::now();
    let reference: Vec<Vec<u8>> = (1..=table.len()).into_par_iter().map(|i| fs7::reference_block(PROFILE_V7, table.formal_len, &x, &roots[..i], &table.def(i).shape)).collect();
    let tref = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let mut st = CoinState::new(PROFILE_V7, table.formal_len, &x);
    let mut full_eq = 0;
    for i in 1..=table.len() {
        st.push(i as u32, &roots[i - 1]);
        full_eq += (st.block(&table.def(i).shape, table.formal_len) == reference[i - 1]) as usize;
    }
    let tinc = t.elapsed().as_secs_f64();
    let prefix_eq = (1..=table.len()).filter(|&i| vlog[i - 1].prefix.len() == table.def(i).shape.used() && vlog[i - 1].prefix[..] == reference[i - 1][..table.def(i).shape.used()]).count();
    let pv_eq = plog.len() == vlog.len() && plog.iter().zip(&vlog).all(|(a, b)| a.root == b.root && a.body == b.body && a.prefix == b.prefix);
    println!("  reference: {} preimages of {} to {} bytes, {} B squeezed each ({tref:.2} s, 11 threads); incremental full blocks ({tinc:.2} s)", table.len(), x.len() + 79 + 64, x.len() + 79 * 354 + 64, table.formal_len);
    check(&format!("incremental implementation, full formal length, equals the reference on {full_eq}/{} blocks", table.len()), full_eq == table.len(), &mut tally);
    check(&format!("prefixes the verifier's adapter squeezed equal the reference prefix on {prefix_eq}/{} blocks", table.len()), prefix_eq == table.len(), &mut tally);
    check("prover and verifier adapters derived identical roots, bodies and prefixes in all rounds", pv_eq, &mut tally);

    // Gate 2: exactly the registered calls.
    println!("## gate 2: registered challenge calls only");
    for (side, ins) in [("prover", &pins), ("verifier", &vins)] {
        let s = &ins.stats;
        println!("  {side}: FS calls {}, coin bytes {}, singleton leaf hashes {}, p3 domain seeds declined {}, grinding calls {}, plain bit samples {}, Merkle leaf hashes {}, error {:?}", s.fs_calls, s.fs_bytes, s.singleton_hashes, s.seeds_declined, s.grind_calls, s.bits_calls, ins.leaf_calls, ins.error);
        check(
            &format!("{side}: exactly 354 SHAKE256 coin derivations, one per registered round, 365,136 bytes in total (no refill), 350 singleton hashes, no grinding or plain bit sample, every slot consumed"),
            s.fs_calls == 354 && s.fs_bytes == 365_136 && s.singleton_hashes == 350 && s.grind_calls == 0 && s.bits_calls == 0 && ins.error.is_none() && ins.log.as_ref().unwrap().len() == 354,
            &mut tally,
        );
        check(&format!("{side}: every p3 DomainSeparator seed declined ({} seeds), none absorbed", s.seeds_declined), s.seeds_declined > 0, &mut tally);
    }
    check(&format!("no separate projection XOF in prove + verify (QLYAUTH4 XOF calls: {})", xof1 - xof0), xof1 == xof0, &mut tally);
    let a = proj::PROJ_XOF_CALLS.load(Ordering::Relaxed);
    let _ = proj::Challenges::sample(&ntt, &[0u8; 64], 32);
    check("control: the counter sees the QLYAUTH4 projection XOF (28 calls for one challenge set)", proj::PROJ_XOF_CALLS.load(Ordering::Relaxed) - a == 28, &mut tally);

    // Gate 3: every root reconstructible from the wire.
    println!("## gate 3: roots reconstructed from the certificate bytes alone");
    let wire_roots = wire_roots(&bytes, n, &table);
    match wire_roots {
        Err(e) => check(&format!("wire walker: {e}"), false, &mut tally),
        Ok((wr, singles)) => {
            let same = (1..=table.len()).filter(|&i| wr[i - 1] == roots[i - 1]).count();
            check(&format!("{singles} singleton roots recomputed from wire bodies (incl. the 80-byte pair at 279 and the empty body at 322) and 4 real roots read from the wire: {same}/{} equal the verifier's history", table.len()), singles == 350 && same == 354, &mut tally);
        }
    }

    // Gate 4: canonical parsing and profile registration.
    println!("## gate 4: canonical parsing, trailing bytes, unregistered profiles");
    let verify = |b: &[u8]| chain::verify_range(&net, parent, hdrs, &ch.blocks, &ch.state, b, &mut Timer::new());
    let full = cert::Cert::from_bytes_v(n, &bytes, true).unwrap();
    let whir_off = bytes.len() - full.whir.len();
    let fe = sz.manifest + sz.u + sz.nu + sz.quot + sz.comm;
    let mut case = |name: &str, b: Vec<u8>, want: &dyn Fn(&Reject) -> bool, tally: &mut (usize, usize)| {
        let r = verify(&b);
        let ok = matches!(&r, Err(e) if want(e));
        check(&format!("{name}: {}", verdict(&r)), ok, tally);
    };
    let parse = |e: &Reject| matches!(e, Reject::Parse(_));
    let any = |_: &Reject| true;
    let profile = |e: &Reject| matches!(e, Reject::Profile(_));
    let mut b = bytes.clone();
    b.push(0);
    case("one trailing byte", b, &parse, &mut tally);
    let mut b = bytes.clone();
    b[whir_off - 4..whir_off].copy_from_slice(&((full.whir.len() + 1) as u32).to_le_bytes());
    b.push(0);
    case("one byte appended inside the WHIR proof, length raised", b, &parse, &mut tally);
    let mut b = bytes.clone();
    b[fe..fe + 8].copy_from_slice(&fs7::le64(crate::field::P));
    case("frontend: first GKR coefficient set to p (non-canonical)", b, &parse, &mut tally);
    // Non-canonical words at chosen positions inside the WHIR proof: plant a sentinel value in
    // one field word of the decoded proof, re-encode, then overwrite the sentinel's 8 bytes with
    // p + 5 (>= p). The re-encoding has the honest length, so only the word is non-canonical.
    let proof: crate::pcs::PcsProof7 = bincode::deserialize(&full.whir).unwrap();
    type Plant = fn(&mut crate::pcs::PcsProof7, F);
    let sites: [(&str, Plant); 7] = [
        ("initial OOD answer", |p, s| p.whir.initial_ood_answers[0] = set_c0(p.whir.initial_ood_answers[0], s)),
        ("opened value X(r)", |p, s| plant_eval(p, s)),
        ("initial sumcheck message", |p, s| p.whir.initial_sumcheck.polynomial_evaluations[0][0] = set_c0(p.whir.initial_sumcheck.polynomial_evaluations[0][0], s)),
        ("opened base-field row (initial tree)", |p, s| plant_row(p, s, 0)),
        ("opened extension row (round-1 tree)", |p, s| plant_row(p, s, 1)),
        ("round-2 OOD answer", |p, s| p.whir.rounds[1].ood_answers[0] = set_c0(p.whir.rounds[1].ood_answers[0], s)),
        ("final polynomial value", |p, s| plant_final(p, s)),
    ];
    let sentinel = F::from_u64(0x1234_5678_9abc_def0);
    for (name, plant) in sites {
        let mut p = proof.clone();
        plant(&mut p, sentinel);
        let enc = bincode::serialize(&p).unwrap();
        let pat = sentinel.as_canonical_u64().to_le_bytes();
        let hits: Vec<usize> = enc.windows(8).enumerate().filter(|(_, w)| *w == pat).map(|(i, _)| i).collect();
        if hits.len() != 1 || enc.len() != full.whir.len() {
            check(&format!("{name}: sentinel located once ({} hits)", hits.len()), false, &mut tally);
            continue;
        }
        let mut enc_nc = enc.clone();
        enc_nc[hits[0]..hits[0] + 8].copy_from_slice(&(crate::field::P + 5).to_le_bytes());
        let mut b = bytes[..whir_off].to_vec();
        b.extend_from_slice(&enc_nc);
        case(&format!("WHIR {name} word set to p + 5 (non-canonical)"), b, &parse, &mut tally);
        let mut b = bytes[..whir_off].to_vec();
        b.extend_from_slice(&enc);
        case(&format!("WHIR {name} word changed to a canonical value"), b, &any, &mut tally);
    }
    let reenc = |f: &dyn Fn(&mut crate::pcs::PcsProof7)| {
        let mut p = proof.clone();
        f(&mut p);
        let enc = bincode::serialize(&p).unwrap();
        let mut b = bytes[..whir_off - 4].to_vec();
        b.extend_from_slice(&(enc.len() as u32).to_le_bytes());
        b.extend_from_slice(&enc);
        b
    };
    case("nonzero grinding witness of WHIR round 0 (pow bits 0)", reenc(&|p| p.whir.rounds[0].pow_witness = F::from_u64(1)), &any, &mut tally);
    case("nonzero final grinding witness", reenc(&|p| p.whir.final_pow_witness = F::from_u64(1)), &any, &mut tally);
    case("grinding witnesses inserted into a zero-difficulty sumcheck", reenc(&|p| p.whir.initial_sumcheck.pow_witnesses = vec![F::from_u64(0); 6]), &any, &mut tally);
    case("final polynomial removed (None)", reenc(&|p| p.whir.final_poly = None), &any, &mut tally);
    let mut setid = |name: &str, magic: &[u8; 8], id: u32, want: &dyn Fn(&Reject) -> bool, tally: &mut (usize, usize)| {
        let mut b = bytes.clone();
        b[..8].copy_from_slice(magic);
        b[8..12].copy_from_slice(&id.to_le_bytes());
        case(name, b, want, tally);
    };
    setid("profile id 0xffffffff (codec test profile)", b"QLYAUTH7", fs7::PROFILE_TEST, &profile, &mut tally);
    setid("profile id 0x00070002 (unregistered)", b"QLYAUTH7", 0x0007_0002, &profile, &mut tally);
    setid("lab profile 0xfff7000b at the chain verifier", b"QLYAUTH7", reg7::lab_profile(2048), &profile, &mut tally);
    setid("magic QLYAUTH5", b"QLYAUTH5", PROFILE_V7, &profile, &mut tally);
    setid("QLYAUTH7 certificate relabelled QLYAUTH4", b"QLYAUTH4", cert::profile_id(n), &any, &mut tally);
    check("registry: 0x00070001 fixes N = 2048 (no table at 1024), 0xffffffff and lab ids are not production profiles", cert::registered_table(PROFILE_V7, 1024, false).is_none() && cert::registered_table(fs7::PROFILE_TEST, 2048, false).is_none() && cert::registered_table(reg7::lab_profile(2048), 2048, false).is_none(), &mut tally);
    let mut b = bytes.clone();
    b[fe + sz.gkr] ^= 1;
    case("explicit (P_leaf, Q_leaf) pair: one bit flipped", b, &|e| matches!(e, Reject::LeafPair), &mut tally);

    println!("GATES7 SUMMARY: {}/{} checks pass", tally.0, tally.1);
    println!("uptime at end: {}", crate::uptime());
}

fn set_c0(x: EF, s: F) -> EF {
    let mut c: Vec<F> = <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&x).to_vec();
    c[0] = s;
    EF::from_basis_coefficients_slice(&c).unwrap()
}

fn plant_eval(p: &mut crate::pcs::PcsProof7, s: F) {
    let cur: Vec<EF> = p.evals[0].current().to_vec();
    let mut v = cur.clone();
    v[0] = set_c0(v[0], s);
    let next = p.evals[0].next().to_vec();
    p.evals[0] = p3_sumcheck::OpeningBatch::new(v, next);
}

fn plant_row(p: &mut crate::pcs::PcsProof7, s: F, round: usize) {
    match &mut p.whir.rounds[round].openings {
        p3_whir::QueryOpenings::Base(o) => o.rows[0][0] = s,
        p3_whir::QueryOpenings::Extension(o) => o.rows[0][0] = set_c0(o.rows[0][0], s),
    }
}

fn plant_final(p: &mut crate::pcs::PcsProof7, s: F) {
    let mut v = p.whir.final_poly.as_ref().unwrap().as_slice().to_vec();
    v[0] = set_c0(v[0], s);
    p.whir.final_poly = Some(p3_multilinear_util::poly::Poly::new(v));
}

/// Walk the certificate bytes (§7 layout plus the 80-byte pair) and the decoded WHIR proof, and
/// return every round's root: singleton roots recomputed from the wire bodies, real roots as
/// read. Uses no prover or verifier state.
fn wire_roots(bytes: &[u8], n: usize, table: &reg7::Table) -> Result<(Vec<[u8; 64]>, usize), String> {
    let fr = reg7::front(n);
    fn take_at<'a>(bytes: &'a [u8], cur: &mut usize, len: usize) -> &'a [u8] {
        let s = &bytes[*cur..*cur + len];
        *cur += len;
        s
    }
    let mut cur = cert::MANIFEST + 1024 * n + n;
    let take = |cur: &mut usize, len: usize| take_at(bytes, cur, len);
    let quot = take(&mut cur, 5 * fr.trials * fr.chunks).to_vec();
    let comm: [u8; 64] = take(&mut cur, 64).try_into().unwrap();
    let mut bodies: Vec<Option<Vec<u8>>> = vec![None, Some(quot)];
    bodies.push(Some(take(&mut cur, 160).to_vec()));
    for k in 1..fr.d {
        for _ in 0..k {
            bodies.push(Some(take(&mut cur, 80).to_vec()));
        }
        bodies.push(Some(take(&mut cur, 160).to_vec()));
    }
    bodies.push(Some(take(&mut cur, 80).to_vec()));
    bodies.push(Some(take(&mut cur, 40).to_vec()));
    for _ in 0..fr.log_dc {
        bodies.push(Some(take(&mut cur, 160).to_vec()));
    }
    for _ in 0..fr.log_tab {
        bodies.push(Some(take(&mut cur, 80).to_vec()));
    }
    let wl = u32::from_le_bytes(take(&mut cur, 4).try_into().unwrap()) as usize;
    if cur + wl != bytes.len() {
        return Err("WHIR length".into());
    }
    let proof: crate::pcs::PcsProof7 = bincode::deserialize(&bytes[cur..]).map_err(|e| format!("{e}"))?;
    let w = &proof.whir;
    bodies.push(Some(vec![]));
    let mut b323 = efs(&w.initial_ood_answers);
    for e in &proof.evals {
        b323.extend(efs(e.current()));
    }
    bodies.push(Some(b323));
    for h in &w.initial_sumcheck.polynomial_evaluations {
        bodies.push(Some(efs(h)));
    }
    let mut real = vec![(1usize, comm)];
    for rd in &w.rounds {
        let c = rd.commitment.as_ref().ok_or("round commitment missing")?;
        real.push((bodies.len() + 1, reg7::to_bytes(&c.roots()[0])));
        bodies.push(None);
        bodies.push(Some(efs(&rd.ood_answers)));
        for h in &rd.sumcheck.polynomial_evaluations {
            bodies.push(Some(efs(h)));
        }
    }
    bodies.push(Some(efs(w.final_poly.as_ref().ok_or("final polynomial missing")?.as_slice())));
    for h in &w.final_sumcheck.as_ref().ok_or("final sumcheck missing")?.polynomial_evaluations {
        bodies.push(Some(efs(h)));
    }
    if bodies.len() != table.len() {
        return Err(format!("{} rounds on the wire, {} registered", bodies.len(), table.len()));
    }
    let mut singles = 0;
    let mut roots = Vec::with_capacity(bodies.len());
    for (i, b) in bodies.iter().enumerate() {
        match b {
            Some(b) => {
                singles += 1;
                roots.push(fs7::singleton_root(table.profile, (i + 1) as u32, b));
            }
            None => roots.push(real.iter().find(|r| r.0 == i + 1).ok_or("real root position")?.1),
        }
    }
    Ok((roots, singles))
}
