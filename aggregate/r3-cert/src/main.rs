//! r3-cert: build and measure the round 3 epoch authorization certificate on real ML-DSA-87
//! signatures. Commands: `selftest`, `run <N>`, `soundness`, `verify <N> <file>`, and for round 4
//! `r4` (section A tests), `chain <per_block>` (accumulator binding, 16 blocks),
//! `keccak <log2 P> [tests]` (Keccak-f[1600] kernel), `bench-ef` (extension multiply cost).

mod cert;
mod chain;
mod field;
mod fs7;
mod alloc;
mod attack7;
mod attack8;
mod batch;
mod gates7;
mod gkr;
mod h9tests;
mod hidden;
mod whirbench;
mod keccak;
mod mlnat;
mod pcs;
mod proj;
mod reg7;
mod region;
mod relaxed;
mod route8;
mod sumcheck;
mod witness;

use std::time::Instant;

#[global_allocator]
static GLOBAL: alloc::Counting = alloc::Counting;

use cert::{Reject, Timer};
use field::{EF, F};
use mlnat::{K, N, Ntt, Record};
use p3_field::{Field, PrimeCharacteristicRing};
use rayon::prelude::*;
use witness::{SLOTS, SigInput};

fn uptime() -> String {
    std::process::Command::new("uptime").output().map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string()).unwrap_or_default()
}

fn print_timer(label: &str, t: &Timer) {
    println!("-- {label} phases (wall clock ms | peak live heap MiB within phase | live heap MiB at end | process footprint (RSS) MiB at end | read MiB | written MiB | SSD-backed MiB at end | RSS peak MiB so far) --");
    for (k, (name, ms, cur, _peak, hpeak, hlive)) in t.phases.iter().enumerate() {
        let io = t.io.get(k).map(|&(r, w, sp, pk)| format!(" | {:>8.0} | {:>8.0} | {:>7.0} | {:>7.0}", r as f64 / 1048576.0, w as f64 / 1048576.0, sp as f64 / 1048576.0, pk as f64 / 1048576.0)).unwrap_or_default();
        println!("  {ms:>10.1} | {:>7.0} | {:>7.0} | {:>7.0}{io}  {name}", *hpeak as f64 / 1048576.0, *hlive as f64 / 1048576.0, *cur as f64 / 1048576.0);
    }
    let (rd, wr) = t.io.iter().fold((0u64, 0u64), |a, x| (a.0 + x.0, a.1 + x.1));
    println!("  storage traffic over all {label} phases: read {:.2} GiB, written {:.2} GiB; SSD-backed peak {:.2} GiB", rd as f64 / 1073741824.0, wr as f64 / 1073741824.0, alloc::spill().1 as f64 / 1073741824.0);
    let hp = t.phases.iter().map(|p| p.4).max().unwrap_or(0);
    println!("  peak live heap over all {label} phases: {:.0} MiB = {:.2} GiB", hp as f64 / 1048576.0, hp as f64 / 1073741824.0);
    println!("  {:>10.1}  TOTAL {label}", t.total());
}

fn selftest() {
    let ntt = Ntt::new();
    println!("adjoint slot reversal NTT(f(X^-1))[j] = NTT(f)[255-j]: {}", proj::adjoint_selftest(&ntt));
    // Basis polynomials too (the identity is linear, the basis covers the ring).
    let mut all = true;
    for b in 0..N {
        let mut f = [0u32; N];
        f[b] = 1;
        let mut fh = f;
        ntt.fwd(&mut fh);
        let mut st = mlnat::adjoint_coeff(&f);
        ntt.fwd(&mut st);
        all &= (0..N).all(|j| st[j] == fh[N - 1 - j]);
    }
    println!("adjoint slot reversal on all 256 basis polynomials: {all}");
    let p = field::P as u128;
    println!("lift bound 512: {} < p {}; 1024: {}; 2048 (with 2^41 range it fails in the doc; here 2^39): {}", proj::lift_bound(512), proj::lift_bound(512) < p, proj::lift_bound(1024) < p, proj::lift_bound(2048) < p);
    // Ternary regions against UseHint, exhaustively (as r3-check/ternary.c).
    let mut checked = 0u64;
    let mut ok = true;
    for u in 0..16u8 {
        let cl = region::class_of(u);
        let mut next = -region::A + 1 - (u == 0) as i64;
        for s in -1..=1i64 {
            let lo = region::start_int(cl, s);
            let k = region::width_int(cl, s);
            ok &= lo == next && k >= 0 && (k as usize) < region::T;
            for yv in 0..=k {
                let e = lo + yv;
                let r = mlnat::modq(region::A * u as i64 + e);
                ok &= mlnat::use_hint(s != 0, r) as u8 == u;
                ok &= region::selector_of(cl, e) == s;
                checked += 1;
            }
            next = lo + k + 1;
        }
        ok &= next == region::A + (u == 15) as i64 + 1;
    }
    println!("ternary cover vs UseHint: {checked} residuals, all ok: {ok} (doc: 16760834)");
    // Field coefficients equal the integer definitions.
    let co = region::all_coeffs();
    let mut cok = true;
    for cl in 0..3 {
        for s in -1..=1i64 {
            let sf = field::fi(s);
            cok &= co[cl].k[0] + (co[cl].k[1] + co[cl].k[2] * sf) * sf == field::fi(region::width_int(cl, s));
            cok &= co[cl].st[0] + (co[cl].st[1] + co[cl].st[2] * sf) * sf == field::fi(region::start_int(cl, s));
        }
    }
    println!("quadratic coefficient tables match start/K definitions: {cok}");

    // GKR on a zero-sum random fraction list, and a non-zero one.
    let mut tr = pcs::Tr::new();
    let d = 10;
    let vals = tr.sample_efs(1 << (d - 1));
    let dens = tr.sample_efs(1 << (d - 1));
    let mut pl = vec![EF::ZERO; 1 << d];
    let mut ql = vec![EF::ONE; 1 << d];
    for i in 0..1 << (d - 1) {
        pl[2 * i] = vals[i];
        ql[2 * i] = dens[i];
        pl[2 * i + 1] = -vals[i];
        ql[2 * i + 1] = dens[i];
    }
    let (pr, out) = gkr::prove(pl.clone(), ql.clone(), &mut pcs::Tr::new());
    let vo = gkr::verify(&pr, d, &mut pcs::Tr::new());
    let direct_p = field::mle_eval(&pl, &out.point);
    let direct_q = field::mle_eval(&ql, &out.point);
    println!("GKR zero-sum: verify ok {}, bottom claims equal direct MLE {}", vo.is_ok(), direct_p == out.p && direct_q == out.q);
    pl[3] += EF::ONE;
    let (pr, _) = gkr::prove(pl, ql, &mut pcs::Tr::new());
    println!("GKR non-zero sum rejected: {:?}", gkr::verify(&pr, d, &mut pcs::Tr::new()).err());
}

struct Batch {
    records: Vec<Record>,
    inputs: Vec<SigInput>,
    raw: Vec<Option<Vec<u8>>>,
}

fn honest_batch(ntt: &Ntt, n: usize, offset: u64) -> Batch {
    let (records, sigs) = batch::libcrux_batch(n, offset);
    let inputs: Vec<SigInput> = records.par_iter().zip(sigs.par_iter()).map(|(r, s)| witness::input_from_raw(ntt, r, s)).collect();
    Batch { records, inputs, raw: sigs.into_iter().map(Some).collect() }
}

/// Round 7: run the standalone suites (soundness, r4) under the QLYAUTH7 transcript (lab profile
/// 0xfff700xx) and the chain suite under profile 0x00070001, instead of QLYAUTH3/QLYAUTH4.
static V7: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

fn v7() -> bool {
    V7.load(std::sync::atomic::Ordering::Relaxed)
}

/// The protocol options of the current mode.
fn opts_m() -> cert::Opts {
    cert::Opts { v7: v7(), ..Default::default() }
}

fn verify_m(records: &[Record], bytes: &[u8], tv: &mut Timer) -> Result<cert::VerifyReport, Reject> {
    cert::verify_opts(records, bytes, tv, &opts_m())
}

/// First applicable challenges (projection identifier, theta) under the current mode, for a
/// given manifest.
fn prefix_m(man: &[u8], records: &[Record], bytes: &[u8]) -> ([u8; 64], EF) {
    let n = records.len();
    if v7() {
        let c = cert::Cert::from_bytes_v(n, bytes, true).unwrap();
        let x = reg7::instance_lab(reg7::lab_profile(n), man, records, &c.u, &c.nu);
        cert::prefix_challenges7(cert::registered_table(reg7::lab_profile(n), n, true).unwrap(), &x, n, bytes).unwrap()
    } else {
        cert::prefix_challenges_with(man, n, bytes).unwrap()
    }
}

type Out = (Vec<u8>, cert::Sizes, Timer, Timer, Result<cert::VerifyReport, Reject>, cert::ProverReport, witness::Violations);

fn prove_verify(b: &Batch, nu_override: Option<&dyn Fn(&mut Vec<u8>)>) -> Out {
    prove_verify_t(b, nu_override, None, 0)
}

/// The prover publishes nu_i = min(count_i, 75) unless overridden, so that a broken witness
/// reaches the proof checks rather than the byte check. `tweak` mutates the witness after
/// generation (multiplicities are recounted), `quot_delta` shifts one quotient.
fn prove_verify_t(b: &Batch, nu_override: Option<&dyn Fn(&mut Vec<u8>)>, tweak: Option<&dyn Fn(&mut witness::Witness)>, quot_delta: i64) -> Out {
    prove_verify_o(b, nu_override, tweak, &cert::Opts { quot_delta, ..opts_m() })
}

/// The same with explicit test options, applied identically to the prover and the verifier.
fn prove_verify_o(b: &Batch, nu_override: Option<&dyn Fn(&mut Vec<u8>)>, tweak: Option<&dyn Fn(&mut witness::Witness)>, o: &cert::Opts) -> Out {
    let ntt = Ntt::new();
    let mut tp = Timer::new();
    let (mut w, pubs) = witness::build(&ntt, &b.records, &b.inputs);
    if let Some(t) = tweak {
        t(&mut w);
    }
    tp.lap("P-1 witness generation (A, mu, c, b; e, S, Y; multiplicities)");
    let u: Vec<u8> = b.inputs.iter().flat_map(|i| i.u.clone()).collect();
    let mut nu: Vec<u8> = w.counts.iter().map(|&c| c.min(cert::NU_MAX)).collect();
    if let Some(f) = nu_override {
        nu = w.counts.clone();
        f(&mut nu);
    }
    let (c, rep) = cert::prove_opts(&b.records, &u, &nu, &w, &pubs, &mut tp, o);
    let viol = w.viol.clone();
    drop(w);
    drop(pubs);
    let (bytes, sizes) = c.to_bytes();
    let mut tv = Timer::new();
    let res = cert::verify_opts(&b.records, &bytes, &mut tv, o);
    (bytes, sizes, tp, tv, res, rep, viol)
}

fn run(n: usize) {
    println!("# r3-cert run N = {n}");
    println!("uptime at start: {}", uptime());
    println!("rayon threads: {}", rayon::current_num_threads());
    let ntt = Ntt::new();
    let t = Instant::now();
    let b = honest_batch(&ntt, n, 0);
    println!("libcrux-ml-dsa 0.0.11: {n} distinct keys, pure-mode signatures with contexts of 1..255 B ({:.0} ms incl. keygen and u derivation)", t.elapsed().as_secs_f64() * 1e3);
    let distinct = {
        let mut pks: Vec<&Vec<u8>> = b.records.iter().map(|r| &r.pk).collect();
        pks.sort();
        pks.dedup();
        pks.len()
    };
    let lib_ok = b.records.par_iter().zip(b.raw.par_iter()).filter(|(r, s)| batch::libcrux_verify(r, s.as_ref().unwrap())).count();
    println!("distinct public keys {distinct}; libcrux verify of the originals {lib_ok}/{n}");

    // Witness, and reconstruction of every signature from it.
    let t = Instant::now();
    let (w, _) = witness::build(&ntt, &b.records, &b.inputs);
    let wt = t.elapsed().as_secs_f64() * 1e3;
    let u: Vec<u8> = b.inputs.iter().flat_map(|i| i.u.clone()).collect();
    let recon: Vec<(bool, bool, bool)> = (0..n)
        .into_par_iter()
        .map(|i| {
            let s = witness::reconstruct(&w, &b.records[i], &u[i * SLOTS..(i + 1) * SLOTS], i);
            match s {
                Some(s) => {
                    let raw = b.raw[i].as_ref().unwrap();
                    let fips_hints = mlnat::decode_sig(raw).unwrap().2.iter().filter(|&&h| h).count();
                    (&s == raw, batch::libcrux_verify(&b.records[i], &s), fips_hints == w.counts[i] as usize)
                }
                None => (false, false, false),
            }
        })
        .collect();
    let max_m = w.m.iter().map(|v| p3_field::PrimeField64::as_canonical_u64(v)).max().unwrap();
    println!(
        "witness: X, Y, S {} cells each, m 2^20 ({wt:.0} ms); violations {:?}; max hints {}, max multiplicity {max_m}",
        n * SLOTS,
        w.viol,
        w.viol.max_hints
    );
    println!(
        "reconstructed from witness: byte-identical {}/{n}, libcrux accepts {}/{n}, hint count = FIPS hint count {}/{n}",
        recon.iter().filter(|r| r.0).count(),
        recon.iter().filter(|r| r.1).count(),
        recon.iter().filter(|r| r.2).count()
    );
    drop(w);

    println!("uptime before prove: {}", uptime());
    let (bytes, sz, tp, tv, res, rep, _) = prove_verify(&b, None);
    print_timer("prover", &tp);
    println!(
        "prover report: stacked PCS domain 2^{}, GKR leaves 2^{}, theta rejections {}, inexact quotients {}, max |V| {} (2^{:.2}), WHIR evals = sumcheck evals {}",
        rep.stacked_vars,
        rep.gkr_leaves_log,
        rep.theta_rejections,
        rep.quotient_inexact,
        rep.max_abs_v,
        (rep.max_abs_v.max(1) as f64).log2(),
        rep.evals_match_whir
    );
    print_timer("verifier", &tv);
    println!("VERIFY: {}", match &res { Ok(_) => "ACCEPT".to_string(), Err(e) => format!("REJECT {e:?}") });
    let frontend = sz.gkr + sz.t_claim + sz.master + sz.table;
    println!("-- certificate bytes --");
    println!("  manifest            {:>10}", sz.manifest);
    println!("  public u            {:>10}", sz.u);
    println!("  hint counts         {:>10}", sz.nu);
    println!("  lift quotients      {:>10}", sz.quot);
    println!("  commitment          {:>10}", sz.comm);
    println!("  frontend GKR        {:>10}  ({} extension elements)", sz.gkr, sz.gkr / 40);
    println!("  frontend T claim    {:>10}", sz.t_claim);
    println!("  frontend master     {:>10}  ({} rounds x 4)", sz.master, sz.master / 160);
    println!("  frontend table      {:>10}  ({} rounds x 2)", sz.table, sz.table / 80);
    println!("  WHIR length field   {:>10}", sz.whir_len);
    println!("  WHIR proof (bincode, incl. 5 opened values = 200 B + framing) {:>10}", sz.whir);
    println!("  frontend subtotal   {:>10}", frontend);
    println!("  TOTAL               {:>10}  = {:.1} B/signature (raw signatures {} B = {} B/signature)", sz.total, sz.total as f64 / n as f64, n * mlnat::SIG_BYTES, mlnat::SIG_BYTES);
    println!("  total bytes == serialized length {}", bytes.len() == sz.total);
    let (bits, cand) = cert::pcs_security_bits(n);
    println!("p3-whir prescribed_security for this 5-claim protocol: {bits:.5} bits (log2 candidates {cand:.3})");
    let path = format!("{}/cert-{n}.bin", std::env::var("R3_OUT").unwrap_or_else(|_| ".".into()));
    std::fs::write(&path, &bytes).unwrap();
    println!("certificate written to {path} ({} B)", bytes.len());
    println!("uptime at end: {}", uptime());
}

fn report(name: &str, res: &Result<cert::VerifyReport, Reject>, viol: Option<&witness::Violations>, expect_accept: bool) -> bool {
    let verdict = match res {
        Ok(_) => "ACCEPT".to_string(),
        Err(e) => format!("REJECT {e:?}"),
    };
    let pass = res.is_ok() == expect_accept;
    println!("[{}] {name}: {verdict}{}", if pass { "PASS" } else { "FAIL" }, viol.map(|v| format!(" | witness violations {v:?}")).unwrap_or_default());
    pass
}

fn soundness() {
    let n = 128;
    println!("# r3-cert soundness tests, N = {n} (127 libcrux signatures + the record under test)");
    println!("transcript: {}", if v7() { "QLYAUTH7 registered-round transcript (round 7)" } else { "QLYAUTH3/QLYAUTH4 sponge transcript" });
    println!("uptime at start: {}", uptime());
    let ntt = Ntt::new();
    let base = honest_batch(&ntt, n, 1000);
    let mut passes = 0;
    let mut total = 0;
    let mut tally = |p: bool| {
        total += 1;
        if p {
            passes += 1;
        }
    };

    // Control: honest batch.
    let (bytes, sz, _, _, res, _, viol) = prove_verify(&base, None);
    tally(report("control: 128 honest libcrux signatures", &res, Some(&viol), true));

    // Relaxed signer instances, each in slot 0.
    let key = relaxed::keygen(&ntt, b"key-0");
    let rec = relaxed::record(&key, 0);
    let with = |inp: SigInput, r: Record| -> Batch {
        let mut b = Batch { records: base.records.clone(), inputs: base.inputs.clone(), raw: base.raw.clone() };
        b.records[0] = r;
        b.inputs[0] = inp;
        b.raw[0] = None;
        b
    };
    for (label, mode, accept) in [
        ("control: relaxed signer, all bounds respected", relaxed::Mode::Valid, true),
        ("out-of-range z = +524168 (one coefficient; relation and all other bounds exact)", relaxed::Mode::ZEdge(1), false),
        ("out-of-range z = -524168 (one coefficient; relation and all other bounds exact)", relaxed::Mode::ZEdge(-1), false),
        ("residual outside its region (u moved by 2 at one coefficient; all else exact)", relaxed::Mode::ResidualOut, false),
    ] {
        let t = Instant::now();
        let s = relaxed::sign(&ntt, &key, &rec.ctx, &rec.msg, mode, label.as_bytes());
        println!("  relaxed signer {mode:?}: {} attempts, {:.0} ms, hints {}, max |z| {}, residuals out of region {}", s.attempts, t.elapsed().as_secs_f64() * 1e3, s.hints, s.max_abs_z, s.out_of_region);
        let b = with(s.input, rec.clone());
        let (_, _, _, _, res, _, viol) = prove_verify(&b, None);
        tally(report(label, &res, Some(&viol), accept));
    }

    // Projection-consistent out-of-range z: z += q leaves every mod-q relation intact.
    {
        let mut b = Batch { records: base.records.clone(), inputs: base.inputs.clone(), raw: base.raw.clone() };
        b.inputs[0].z[5] += mlnat::QI;
        let (_, _, _, _, res, rep, viol) = prove_verify(&b, None);
        println!("  (z += q: inexact quotients {} -> the projections alone cannot see it)", rep.quotient_inexact);
        tally(report("z coefficient + q (mod-q relation unchanged, range only)", &res, Some(&viol), false));
    }

    // Per-signature hint count 76, total unchanged.
    {
        let t = Instant::now();
        let s = relaxed::sign(&ntt, &key, &rec.ctx, &rec.msg, relaxed::Mode::Hints(76), b"hints-76");
        println!("  relaxed signer Hints(76): {} attempts, {:.0} ms, hints {}", s.attempts, t.elapsed().as_secs_f64() * 1e3, s.hints);
        let b = with(s.input, rec.clone());
        let f = |nu: &mut Vec<u8>| {
            nu[0] -= 1;
            nu[1] += 1;
        };
        let (_, _, _, _, res, _, viol) = prove_verify(&b, Some(&f));
        tally(report("signature 0 has 76 hints, published nu_0 = 75 and nu_1 + 1 (total unchanged)", &res, Some(&viol), false));
        let keep = |_: &mut Vec<u8>| {};
        let (_, _, _, _, res, _, _) = prove_verify(&b, Some(&keep));
        tally(report("signature 0 has 76 hints, published nu_0 = 76", &res, None, false));
    }

    // Statement mutations against the honest certificate.
    let mut tv = Timer::new();
    let mut st = base.records.clone();
    st.swap(0, 1);
    tally(report("honest certificate, records 0 and 1 reordered in the statement", &verify_m(&st, &bytes, &mut tv), None, false));
    let mut st = base.records.clone();
    let c0 = st[0].ctx.clone();
    st[0].ctx = st[1].ctx.clone();
    st[1].ctx = c0;
    tally(report("honest certificate, contexts of records 0 and 1 swapped", &verify_m(&st, &bytes, &mut tv), None, false));
    let mut st = base.records.clone();
    let p0 = st[0].pk.clone();
    st[0].pk = st[1].pk.clone();
    st[1].pk = p0;
    tally(report("honest certificate, public keys of records 0 and 1 swapped", &verify_m(&st, &bytes, &mut tv), None, false));

    // The same statement mutations with the manifest rewritten to match the mutated statement,
    // so the rejection has to come from the transcript and the recomputed public terms.
    for (label, st) in [
        ("honest certificate + rewritten manifest, records 0 and 1 reordered", {
            let mut st = base.records.clone();
            st.swap(0, 1);
            st
        }),
        ("honest certificate + rewritten manifest, contexts 0 and 1 swapped", {
            let mut st = base.records.clone();
            let c0 = st[0].ctx.clone();
            st[0].ctx = st[1].ctx.clone();
            st[1].ctx = c0;
            st
        }),
        ("honest certificate + rewritten manifest, public keys 0 and 1 swapped", {
            let mut st = base.records.clone();
            let p0 = st[0].pk.clone();
            st[0].pk = st[1].pk.clone();
            st[1].pk = p0;
            st
        }),
    ] {
        let mut bad = bytes.clone();
        bad[..cert::MANIFEST].copy_from_slice(&cert::manifest_for(&st, &opts_m()));
        tally(report(label, &verify_m(&st, &bad, &mut tv), None, false));
    }

    // Witness-level tweaks on the honest batch.
    {
        let yq = |w: &mut witness::Witness| {
            let b = 3 * SLOTS + 77;
            w.y[b] += F::from_u64(mlnat::Q as u64);
            w.ei[b] += mlnat::Q as i32;
            w.m = witness::multiplicities(&w.x, &w.y, &w.s, &w.class, w.counts.len());
        };
        let (_, _, _, _, res, rep, _) = prove_verify_t(&base, None, Some(&yq), 0);
        println!("  (Y += q: inexact quotients {})", rep.quotient_inexact);
        tally(report("residual cell Y + q (mod-q relation unchanged, range only)", &res, None, false));
        let ms = |w: &mut witness::Witness| {
            let t = (0..w.m.len()).find(|&t| w.m[t] != F::ZERO).unwrap();
            w.m[t] -= F::ONE;
            w.m[t + 1] += F::ONE;
        };
        let (_, _, _, _, res, _, _) = prove_verify_t(&base, None, Some(&ms), 0);
        tally(report("multiplicity table: one count moved from t to t+1", &res, None, false));
        let (_, _, _, _, res, _, _) = prove_verify_t(&base, None, None, 1);
        tally(report("one lift quotient V + 1, everything else honest", &res, None, false));
        let sm = |w: &mut witness::Witness| {
            // A hint moved between two cells of signature 0 keeps nu_0 but breaks e = Y + start(S).
            let a = (0..SLOTS).find(|&t| w.s[t] != F::ZERO).unwrap();
            let b = (0..SLOTS).find(|&t| w.s[t] == F::ZERO).unwrap();
            w.s.swap(a, b);
        };
        let (_, _, _, _, res, _, _) = prove_verify_t(&base, None, Some(&sm), 0);
        tally(report("selector moved between two cells of signature 0 (count unchanged)", &res, None, false));
    }

    // Re-proving mutated statements with the original (z, u).
    {
        let mut b = Batch { records: base.records.clone(), inputs: base.inputs.clone(), raw: base.raw.clone() };
        b.inputs[0].u[100] = (b.inputs[0].u[100] + 1) % 16;
        let (_, _, _, _, res, _, viol) = prove_verify(&b, None);
        tally(report("wrong u: one nibble of u_0 changed, prover runs on the resulting witness", &res, Some(&viol), false));
        let mut b = Batch { records: base.records.clone(), inputs: base.inputs.clone(), raw: base.raw.clone() };
        b.records.swap(0, 1);
        let (_, _, _, _, res, _, viol) = prove_verify(&b, None);
        tally(report("reordered records (0 <-> 1) with the witness in the original order", &res, Some(&viol), false));
        let mut b = Batch { records: base.records.clone(), inputs: base.inputs.clone(), raw: base.raw.clone() };
        let c0 = b.records[0].ctx.clone();
        b.records[0].ctx = b.records[1].ctx.clone();
        b.records[1].ctx = c0;
        let (_, _, _, _, res, _, viol) = prove_verify(&b, None);
        tally(report("contexts 0 <-> 1 swapped, prover runs on the resulting witness", &res, Some(&viol), false));
        let mut b = Batch { records: base.records.clone(), inputs: base.inputs.clone(), raw: base.raw.clone() };
        let p0 = b.records[0].pk.clone();
        b.records[0].pk = b.records[1].pk.clone();
        b.records[1].pk = p0;
        let (_, _, _, _, res, _, viol) = prove_verify(&b, None);
        tally(report("public keys 0 <-> 1 swapped, prover runs on the resulting witness", &res, Some(&viol), false));
    }

    // Tampered certificate bytes: one flipped bit in each component, several in WHIR.
    let regions = [
        ("manifest", 0usize, sz.manifest),
        ("public u", sz.manifest, sz.u),
        ("hint counts", sz.manifest + sz.u, sz.nu),
        ("quotients", sz.manifest + sz.u + sz.nu, sz.quot),
        ("commitment", sz.manifest + sz.u + sz.nu + sz.quot, sz.comm),
    ];
    let fe = sz.manifest + sz.u + sz.nu + sz.quot + sz.comm;
    let regions2 = [
        ("GKR", fe, sz.gkr),
        ("table claim T", fe + sz.gkr + sz.leaf_pair, sz.t_claim),
        ("master sumcheck", fe + sz.gkr + sz.leaf_pair + sz.t_claim, sz.master),
        ("table sumcheck", fe + sz.gkr + sz.leaf_pair + sz.t_claim + sz.master, sz.table),
        ("WHIR proof", fe + sz.gkr + sz.leaf_pair + sz.t_claim + sz.master + sz.table + sz.whir_len, sz.whir),
    ];
    // QLYAUTH7 only: the explicit (P_leaf, Q_leaf) pair of round 279 (2 extra tests).
    let regions3: Vec<(&str, usize, usize)> = if sz.leaf_pair > 0 { vec![("explicit leaf pair", fe + sz.gkr, sz.leaf_pair)] } else { vec![] };
    for (name, off, len) in regions.iter().chain(regions2.iter()).chain(regions3.iter()) {
        let picks: Vec<usize> = if *name == "WHIR proof" { (0..16).map(|k| off + (len * (2 * k + 1)) / 32).collect() } else { vec![off + len / 3, off + len - 1] };
        for p in picks {
            let mut bad = bytes.clone();
            bad[p] ^= 0x04;
            let r = verify_m(&base.records, &bad, &mut tv);
            tally(report(&format!("tampered byte {p} ({name})"), &r, None, false));
        }
    }
    let mut bad = bytes.clone();
    bad.push(0);
    tally(report("one trailing byte appended", &verify_m(&base.records, &bad, &mut tv), None, false));
    // The WHIR proof is the last field, after its u32 length: append a byte inside it and raise the
    // length to match, so only the proof decoder can notice.
    let whir_len = cert::Cert::from_bytes_v(base.records.len(), &bytes, v7()).expect("honest certificate parses").whir.len();
    let at = bytes.len() - 4 - whir_len;
    let mut bad = bytes.clone();
    bad[at..at + 4].copy_from_slice(&((whir_len + 1) as u32).to_le_bytes());
    bad.push(0);
    tally(report("byte appended inside the WHIR proof, length raised", &verify_m(&base.records, &bad, &mut tv), None, false));
    let _ = (F::ZERO, K);
    println!("SOUNDNESS SUMMARY: {passes}/{total} tests behave as expected");
    println!("uptime at end: {}", uptime());
}

/// Verify a certificate file in a fresh process (clean memory measurement). The statement is
/// regenerated deterministically (same keys, messages and contexts as `run`).
fn verify_file(n: usize, path: &str) {
    println!("# r3-cert verify N = {n}, {path}");
    println!("uptime at start: {}", uptime());
    let (records, _) = batch::libcrux_batch(n, 0);
    let bytes = std::fs::read(path).unwrap();
    let mut tv = Timer::new();
    let res = cert::verify(&records, &bytes, &mut tv);
    print_timer("verifier (fresh process)", &tv);
    println!("VERIFY: {}", match &res { Ok(_) => "ACCEPT".to_string(), Err(e) => format!("REJECT {e:?}") });
}

/// Round 4, section A.2: S <- 1/2 (a field element) at four hint-zero cells of one signature
/// with interior u and -32735 <= e <= 261888; Y <- e + 32735; z, e, u unchanged; multiplicities
/// recounted; that signature's count + 1. Applied after witness::build, i.e. below every check
/// the honest builder makes. Returns (signature, cells) and checks that only ternarity breaks.
fn inject_half(w: &mut witness::Witness) -> (usize, Vec<usize>) {
    inject_half_from(w, 0)
}

/// The same mutation on the first eligible signature with index >= `from` (round 8: the
/// production profile places it in the fourth 512-signature chunk).
pub(crate) fn inject_half_from(w: &mut witness::Witness, from: usize) -> (usize, Vec<usize>) {
    let co = region::all_coeffs();
    let half = F::TWO.inverse();
    let i = (from..w.n).find(|&i| w.counts[i] <= 74).expect("a signature with at most 74 hints");
    let base = i * SLOTS;
    let cells: Vec<usize> = (0..K * N)
        .map(|t| base + t)
        .filter(|&b| w.class[b] == 2 && w.s[b] == F::ZERO && (-32735..=261888).contains(&(w.ei[b] as i64)))
        .take(4)
        .collect();
    assert_eq!(cells.len(), 4);
    for &b in &cells {
        w.s[b] = half;
        w.y[b] = field::fi(w.ei[b] as i64 + 32735);
    }
    w.m = witness::multiplicities(&w.x, &w.y, &w.s, &w.class, w.n);
    w.counts[i] += 1;
    // Everything except ternarity still holds, checked on the mutated cells.
    let c = &co[2];
    for &b in &cells {
        let (s, y) = (w.s[b], w.y[b]);
        let k = c.k[0] + (c.k[1] + c.k[2] * s) * s;
        let st = c.st[0] + (c.st[1] + c.st[2] * s) * s;
        let (yi, ki) = (witness::as_int(y), witness::as_int(k));
        assert!((0..region::T as i64).contains(&yi) && (0..region::T as i64).contains(&(ki - yi)));
        assert_eq!(y + st, field::fi(w.ei[b] as i64), "e = Y + start(S) preserved");
        assert_ne!(s * s * s, s, "S^3 != S");
        assert_eq!(ki, 458_303);
    }
    let s2: F = (0..K * N).map(|t| w.s[base + t] * w.s[base + t]).sum();
    assert_eq!(s2, F::from_u8(w.counts[i]), "sum S^2 = published count");
    (i, cells.iter().map(|b| b - base).collect())
}

fn r4_half_selector(base: &Batch, tally: &mut dyn FnMut(bool)) {
    println!("## A.2 isolated S^3 = S test");
    let shown = std::sync::Mutex::new(None);
    let tw = |w: &mut witness::Witness| {
        let r = inject_half(w);
        *shown.lock().unwrap() = Some((r.clone(), w.counts[r.0], w.viol.clone()));
    };
    let (_, _, _, _, res, _, _) = prove_verify_o(base, None, Some(&tw), &opts_m());
    let ((i, cells), cnt, viol) = shown.lock().unwrap().clone().unwrap();
    println!("  signature {i}, cells {cells:?}: S <- 1/2, Y <- e + 32735, count {} -> {cnt}; integer-witness violations {viol:?}", cnt - 1);
    println!("  checked: Y and K - Y in [0, 2^20), K = 458303, e = Y + start(S), sum S^2 = count, S^3 != S");
    tally(report("S = 1/2 at four interior hint-zero cells, full verifier", &res, None, false));
    let ctl = cert::Opts { drop_ternarity: true, ..opts_m() };
    let (_, _, _, _, res, _, _) = prove_verify_o(base, None, Some(&tw), &ctl);
    tally(report("same witness, UNSAFE control without the S^3 = S zerocheck (same statement, profile, schedule)", &res, None, true));
    let (_, _, _, _, res, _, _) = prove_verify_o(base, None, None, &ctl);
    tally(report("honest batch, UNSAFE control (the control itself is complete)", &res, None, true));
}

/// Section A.1: every statement component must enter Fiat-Shamir before the first challenge that
/// depends on it. For each mutation, recompute the verifier's first frontend challenges.
fn r4_prefix(base: &Batch, tally: &mut dyn FnMut(bool)) {
    println!("## A.1 challenge-prefix sensitivity");
    let n = base.records.len();
    let (bytes, sz, _, _, res, rep, _) = prove_verify(base, None);
    tally(report("honest certificate", &res, None, true));
    let (seed0, th0) = prefix_m(&cert::manifest_for(&base.records, &opts_m()), &base.records, &bytes);
    tally(report_bool("verifier-derived projection seed and theta equal the prover's", seed0 == rep.seed && th0 == rep.theta));
    let seed_of = |recs: &[Record], b: &[u8]| prefix_m(&cert::manifest_for(recs, &opts_m()), recs, b);
    let mut line = |label: &str, total: usize, changed: usize, tally: &mut dyn FnMut(bool)| {
        tally(report_bool(&format!("{label}: first applicable challenge changed in {changed}/{total} mutations"), changed == total));
    };
    type Mutate = fn(&mut Record, usize);
    let fields: [(&str, Mutate); 3] = [
        ("each record's message (one bit), projection seed", |r, _| r.msg[0] ^= 1),
        ("each record's context (one bit), projection seed", |r, _| r.ctx[0] ^= 1),
        ("each record's public key (one bit of t1), projection seed", |r, i| r.pk[100 + i] ^= 1),
    ];
    for (label, f) in fields {
        let changed = (0..n)
            .into_par_iter()
            .filter(|&i| {
                let mut st = base.records.clone();
                f(&mut st[i], i);
                seed_of(&st, &bytes).0 != seed0
            })
            .count();
        line(label, n, changed, tally);
    }
    let flip = |off: usize, bit: u8| -> ([u8; 64], EF) {
        let mut b = bytes.clone();
        b[off] ^= bit;
        seed_of(&base.records, &b)
    };
    let u_off = sz.manifest;
    let nu_off = u_off + sz.u;
    let q_off = nu_off + sz.nu;
    let c_off = q_off + sz.quot;
    let changed = (0..n).into_par_iter().filter(|&i| flip(u_off + 1024 * i + i % 1024, 1).0 != seed0).count();
    line("each signature's public u (one bit), projection seed", n, changed, tally);
    let changed = (0..n).into_par_iter().filter(|&i| flip(nu_off + i, 1).0 != seed0).count();
    line("each signature's published hint count (+-1), projection seed", n, changed, tally);
    let changed = (0..64).into_par_iter().filter(|&k| flip(c_off + k, 1).0 != seed0).count();
    line("initial commitment (each of 64 bytes), projection seed", 64, changed, tally);
    let man = cert::manifest_for(&base.records, &opts_m());
    let changed = (0..cert::MANIFEST)
        .into_par_iter()
        .filter(|&k| {
            let mut m = man.clone();
            m[k] ^= 1;
            prefix_m(&m, &base.records, &bytes).0 != seed0
        })
        .count();
    line("manifest (each of 512 bytes: magic, backend/profile id, parameter and layout digest, count N, statement digest, chunk count, reserved)", cert::MANIFEST, changed, tally);
    let nq = sz.quot / 5;
    let changed = (0..nq).filter(|&k| { let (s, t) = flip(q_off + 5 * k, 1); s == seed0 && t != th0 }).count();
    line("each lift quotient (+-1): seed unchanged, theta changed", nq, changed, tally);
}

fn report_bool(name: &str, ok: bool) -> bool {
    println!("[{}] {name}", if ok { "PASS" } else { "FAIL" });
    ok
}

/// Section A.1 (Gruen): inject the round challenges 0, 1, 1/2 and ones that zero eq1(x, r).
fn r4_gruen(base: &Batch, tally: &mut dyn FnMut(bool)) {
    use pcs::Inject;
    println!("## A.1 Gruen exceptional challenges (GKR rounds and betas, table rounds; both sides)");
    println!("  v = (1 + i)/2 with i^2 = -1: eq1(v, v) = {:?}", field::eq1(pcs::vroot(), pcs::vroot()) == EF::ZERO);
    let ms = |w: &mut witness::Witness| {
        let t = (0..w.m.len()).find(|&t| w.m[t] != F::ZERO).unwrap();
        w.m[t] -= F::ONE;
        w.m[t + 1] += F::ONE;
    };
    let tw = |w: &mut witness::Witness| {
        inject_half(w);
    };
    for mode in [Inject::Zero, Inject::One, Inject::Half, Inject::EqZero, Inject::Vroot] {
        let o = cert::Opts { inject: mode, ..opts_m() };
        let (bytes, sz, _, _, res, _, _) = prove_verify_o(base, None, None, &o);
        tally(report(&format!("{mode:?}: honest certificate (no inverse-of-zero path)"), &res, None, true));
        let (_, _, _, _, res, _, _) = prove_verify_o(base, None, Some(&tw), &o);
        tally(report(&format!("{mode:?}: S = 1/2 witness"), &res, None, false));
        let (_, _, _, _, res, _, _) = prove_verify_o(base, None, Some(&ms), &o);
        tally(report(&format!("{mode:?}: one multiplicity moved"), &res, None, false));
        let fe = sz.manifest + sz.u + sz.nu + sz.quot + sz.comm;
        let off = fe + (0..5).map(|k| (2 * k + 4) * 40).sum::<usize>() + 2 * 40;
        let mut bad = bytes.clone();
        bad[off] ^= 4;
        let mut tv = Timer::new();
        tally(report(&format!("{mode:?}: GKR layer 5, round 2, a1 tampered"), &cert::verify_opts(&base.records, &bad, &mut tv, &o), None, false));
        let off = fe + sz.gkr + sz.leaf_pair + sz.t_claim + sz.master + 3 * 80;
        let mut bad = bytes.clone();
        bad[off] ^= 4;
        tally(report(&format!("{mode:?}: table round 4, a1 tampered"), &cert::verify_opts(&base.records, &bad, &mut tv, &o), None, false));
    }
}

/// Section A.1: a prover that commits or opens with another layout, claim order or profile than
/// the verifier-derived one.
fn r4_layout(base: &Batch, tally: &mut dyn FnMut(bool)) {
    use cert::LayoutVariant as V;
    println!("## A.1 layout, claim-order and profile mismatches (prover deviates, verifier canonical)");
    for v in [V::SwapTables, V::SwapColumns, V::ClaimOrder, V::Profile] {
        let o = cert::Opts { layout: v, ..opts_m() };
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let ntt = Ntt::new();
            let (w, pubs) = witness::build(&ntt, &base.records, &base.inputs);
            let u: Vec<u8> = base.inputs.iter().flat_map(|i| i.u.clone()).collect();
            let nu: Vec<u8> = w.counts.iter().map(|&c| c.min(cert::NU_MAX)).collect();
            let (c, _) = cert::prove_opts(&base.records, &u, &nu, &w, &pubs, &mut Timer::new(), &o);
            c.to_bytes().0
        }));
        let Ok(bytes) = r else {
            tally(report_bool(&format!("{v:?}: prover could not produce a certificate"), false));
            continue;
        };
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify_m(&base.records, &bytes, &mut Timer::new())));
        match res {
            Ok(r) => tally(report(&format!("{v:?}"), &r, None, false)),
            Err(_) => tally(report_bool(&format!("{v:?}: REJECT (verifier panicked inside p3; counted as rejection)"), true)),
        }
    }
}

/// Section A.1: the FS-bound manifest must not contain the transport length.
fn r4_manifest_length(tally: &mut dyn FnMut(bool)) {
    println!("## A.1 manifest vs transport length");
    let ntt = Ntt::new();
    let mut lens = vec![];
    let mut ok = true;
    for off in [0u64, 1000, 2000] {
        let b = honest_batch(&ntt, 128, off);
        let pre = cert::manifest_for(&b.records, &opts_m());
        let (bytes, sz, _, _, res, _, _) = prove_verify(&b, None);
        ok &= res.is_ok() && bytes[..cert::MANIFEST] == pre[..] && pre[8 + 4 + 64 + 4 + 64 + 4..].iter().all(|&x| x == 0);
        lens.push(sz.whir);
    }
    println!("  WHIR proof lengths for three statements of 128 signatures: {lens:?} (data dependent)");
    tally(report_bool("manifest = function of the records only, computed before proving, reserved bytes zero; the 4-byte WHIR length is never absorbed", ok && (lens[0] != lens[1] || lens[1] != lens[2])));
}

/// Prove a certificate for blocks `r` of `ch` (parent = header before r.start). `attack` may
/// change the prover's record list and signatures before the witness is built; the manifest is
/// always the honest one for the range.
fn prove_range(ch: &chain::Chain, r: std::ops::Range<usize>, attack: &dyn Fn(&mut Vec<Record>, &mut Vec<Vec<u8>>)) -> (Vec<u8>, cert::Sizes, Timer) {
    let ntt = Ntt::new();
    let parent = if r.start == 0 { &ch.anchor } else { &ch.headers[r.start - 1] };
    let mut records = chain::replay(&ch.net, &ch.blocks[r.clone()], &ch.state).unwrap();
    let mut sigs: Vec<Vec<u8>> = ch.blocks[r.clone()].iter().flat_map(|b| b.sigs.clone()).collect();
    attack(&mut records, &mut sigs);
    let man = if v7() { chain::manifest_v7(&ch.net, records.len(), parent, &ch.headers[r.clone()]) } else { chain::manifest_v4(&ch.net, records.len(), parent, &ch.headers[r.clone()]) };
    let mut tp = Timer::new();
    let inputs: Vec<SigInput> = records.par_iter().zip(sigs.par_iter()).map(|(rc, sg)| witness::input_from_raw(&ntt, rc, sg)).collect();
    let (w, pubs) = witness::build(&ntt, &records, &inputs);
    tp.lap("P-1 witness generation");
    let u: Vec<u8> = inputs.iter().flat_map(|i| i.u.clone()).collect();
    let nu: Vec<u8> = w.counts.iter().map(|&c| c.min(cert::NU_MAX)).collect();
    let (c, rep) = if v7() {
        // The raw instance: the honest blocks of the range, with the keys the prover used.
        let x = chain::instance_v7(&ch.net, parent, &ch.headers[r.clone()], &ch.blocks[r.clone()], &records, &cert::ubytes_of(&u, records.len()), &nu);
        cert::prove_stmt7(&records, &man, &x, fs7::PROFILE_V7, &u, &nu, &w, &pubs, &mut tp, &cert::Opts::default())
    } else {
        cert::prove_stmt(&records, &man, &u, &nu, &w, &pubs, &mut tp, &cert::Opts::default())
    };
    if let Some(e) = &rep.transcript_error {
        println!("  prover transcript error: {e}");
    }
    drop(w);
    let (bytes, sz) = c.to_bytes();
    (bytes, sz, tp)
}

fn chain_cmd(per_block: usize) {
    let nb = 16;
    let n = nb * per_block;
    println!("# r3-cert chain binding (round 4 section D.3): {nb} blocks x {per_block} records = {n} signatures");
    println!("transcript: {}", if v7() { "QLYAUTH7 registered-round transcript (round 7)" } else { "QLYAUTH3/QLYAUTH4 sponge transcript" });
    println!("uptime at start: {}", uptime());
    let net = chain::network_id(b"r4-lab");
    let t = Instant::now();
    let ch = chain::build(net, chain::genesis(&net), 0, 2 * nb, per_block, 0);
    println!("chain: {} blocks built and node-validated (native verification, c_tilde from signatures, A[b]) in {:.0} ms; {} keys in state ({} rotated senders)", 2 * nb, t.elapsed().as_secs_f64() * 1e3, ch.state.keys.len(), (0..(2 * n) as u64).filter(|&g| chain::rotated(g)).count());
    let (mut passes, mut total) = (0, 0);
    let mut tally = |p: bool| {
        total += 1;
        passes += p as usize;
    };
    let range = 0..nb;
    let hdrs = &ch.headers[range.clone()];
    let blocks = &ch.blocks[range.clone()];
    let none = |_: &mut Vec<Record>, _: &mut Vec<Vec<u8>>| {};

    // Node side: an invalid sidecar invalidates the witness package, not the header.
    {
        let mut bad = ch.blocks[3].clone();
        bad.sigs[5][100] ^= 1;
        let r1 = chain::node_accumulator(&net, 3, &ch.headers[2].acc, &bad, &ch.state);
        let r2 = chain::node_accumulator(&net, 3, &ch.headers[2].acc, &ch.blocks[3], &ch.state);
        tally(report_bool(&format!("invalid sidecar for block 3 rejected ({:?}), replacement witness accepted and matches the unchanged header A[3]: {}", r1.as_ref().err(), r2.as_ref().ok() == Some(&ch.headers[3].acc)), r1.is_err() && r2.ok() == Some(ch.headers[3].acc)));
    }

    let (bytes, sz, tp) = prove_range(&ch, range.clone(), &none);
    print_timer("prover", &tp);
    let mut tv = Timer::new();
    let res = chain::verify_range(&net, &ch.anchor, hdrs, blocks, &ch.state, &bytes, &mut tv);
    print_timer("verifier", &tv);
    tally(report("honest certificate for heights 0..15", &res, None, true));
    println!("-- certificate bytes: total {} = {:.1} B/signature (manifest {}, u {}, nu {}, quotients {}, commitment {}, GKR {}, T {}, master {}, table {}, WHIR {} + 4)", sz.total, sz.total as f64 / n as f64, sz.manifest, sz.u, sz.nu, sz.quot, sz.comm, sz.gkr, sz.t_claim, sz.master, sz.table, sz.whir);
    println!("-- header accumulators outside the certificate: {nb} x 64 = {} B; certificate + headers = {} B = {:.4} B/signature", nb * 64, sz.total + nb * 64, (sz.total + nb * 64) as f64 / n as f64);

    // Statement-side attacks against the honest certificate.
    let mut sw = ch.blocks.clone();
    sw[2].records.swap(0, 1);
    sw[2].sigs.swap(0, 1);
    tally(report("replayed bodies with records 0 and 1 of block 2 reordered", &chain::verify_range(&net, &ch.anchor, hdrs, &sw[range.clone()], &ch.state, &bytes, &mut tv), None, false));
    let mut st = ch.state.clone();
    let victim = (chain::sender(per_block as u64 + 3), 0u64);
    st.keys.insert(victim, ch.state.keys[&(chain::sender(per_block as u64 + 4), 0)].clone());
    tally(report("state resolves one record to another key (substituted state key)", &chain::verify_range(&net, &ch.anchor, hdrs, blocks, &st, &bytes, &mut tv), None, false));
    let mut hb = hdrs.to_vec();
    hb[7].acc[0] ^= 1;
    let mut prev = ch.anchor.id;
    for hd in hb.iter_mut() {
        hd.parent = prev;
        hd.id = chain::header_id(&hd.parent, hd.height, &hd.acc);
        prev = hd.id;
    }
    tally(report("header A[7] changed (header ids relinked)", &chain::verify_range(&net, &ch.anchor, &hb, blocks, &ch.state, &bytes, &mut tv), None, false));

    // Cross-fork: the same bodies on a different parent.
    let anchor_b = { let acc = chain::h(b"fork-b-parent", &net); chain::Header { height: u64::MAX, parent: [1; 32], acc, id: chain::header_id(&[1; 32], u64::MAX, &acc) } };
    let fb = chain::build(net, anchor_b.clone(), 0, nb, per_block, 0);
    tally(report("cross-fork: certificate of fork A checked on fork B (same bodies, other parent)", &chain::verify_range(&net, &anchor_b, &fb.headers, &fb.blocks, &fb.state, &bytes, &mut tv), None, false));
    let mut rw = bytes.clone();
    rw[..cert::MANIFEST].copy_from_slice(&if v7() { chain::manifest_v7(&net, n, &anchor_b, &fb.headers) } else { chain::manifest_v4(&net, n, &anchor_b, &fb.headers) });
    tally(report("cross-fork with the manifest rewritten to fork B", &chain::verify_range(&net, &anchor_b, &fb.headers, &fb.blocks, &fb.state, &rw, &mut tv), None, false));

    // Another range of the same chain.
    let r2 = nb..2 * nb;
    tally(report("certificate for heights 0..15 checked as heights 16..31", &chain::verify_range(&net, &ch.headers[nb - 1], &ch.headers[r2.clone()], &ch.blocks[r2.clone()], &ch.state, &bytes, &mut tv), None, false));
    let mut rw = bytes.clone();
    rw[..cert::MANIFEST].copy_from_slice(&if v7() { chain::manifest_v7(&net, n, &ch.headers[nb - 1], &ch.headers[r2.clone()]) } else { chain::manifest_v4(&net, n, &ch.headers[nb - 1], &ch.headers[r2.clone()]) });
    tally(report("the same with the manifest rewritten to heights 16..31", &chain::verify_range(&net, &ch.headers[nb - 1], &ch.headers[r2.clone()], &ch.blocks[r2], &ch.state, &rw, &mut tv), None, false));

    // Prover-side attacks: a valid proof for a different (AuthRecord, key, c_tilde) list.
    let reorder = |r: &mut Vec<Record>, s: &mut Vec<Vec<u8>>| {
        r.swap(2 * per_block, 2 * per_block + 1);
        s.swap(2 * per_block, 2 * per_block + 1);
    };
    let (b2, _, _) = prove_range(&ch, range.clone(), &reorder);
    tally(report("prover proves block 2 with records 0 and 1 reordered (valid proof of the permuted list)", &chain::verify_range(&net, &ch.anchor, hdrs, blocks, &ch.state, &b2, &mut tv), None, false));
    let g = 256u64.min(n as u64 - 1) & !255;
    let net2 = net;
    let oldkey = move |r: &mut Vec<Record>, s: &mut Vec<Vec<u8>>| {
        let kp = chain::keypair(g, 0, b"");
        let i = g as usize;
        r[i].pk = kp.verification_key.as_slice().to_vec();
        let rnd = [7u8; 32];
        s[i] = libcrux_ml_dsa::ml_dsa_87::sign(&kp.signing_key, &r[i].msg, &r[i].ctx, rnd).unwrap().as_slice().to_vec();
        let _ = net2;
    };
    println!("  key rotation: sender of transaction {g} is registered under epochs 0 and 1, its record names epoch 1");
    let (b3, _, _) = prove_range(&ch, range.clone(), &oldkey);
    tally(report("prover authorizes an epoch-1 record with the rotated-out epoch-0 key (valid signature under that key)", &chain::verify_range(&net, &ch.anchor, hdrs, blocks, &ch.state, &b3, &mut tv), None, false));
    println!("CHAIN SUMMARY: {passes}/{total} tests behave as expected");
    println!("uptime at end: {}", uptime());
}

/// Round 4 section E step 4: prove 2^logp Keccak-f[1600] permutations; negative tests when
/// `tests` is set.
fn print_ops(c: &keccak::ops::Counts) {
    println!("  operation counts (millions; thread-local counters, from loop sizes):");
    println!("    {:<34} {}", "", keccak::ops::KINDS.map(|k| format!("{k:>18}")).join(""));
    for (cat, row) in keccak::ops::CATS.iter().zip(c.iter()) {
        println!("    {cat:<34} {}", row.map(|v| format!("{:>18.2}", v as f64 / 1e6)).join(""));
    }
}

/// Set the prover-only histogram switch from KECCAK_HIST (1 = optimized first round and fold).
fn keccak_mode() -> &'static str {
    let on = std::env::var("KECCAK_HIST").map(|v| v == "1").unwrap_or(false);
    keccak::HIST.store(on, std::sync::atomic::Ordering::Relaxed);
    if on { "optimized (first-round histograms, selection fold)" } else { "baseline (direct first round and fold)" }
}

/// Round 5 acceptance: the optimized prover must produce the same bytes as the baseline.
fn keccak_cmp(logp: usize) {
    use keccak::KOpts;
    let p = 1usize << logp;
    println!("# keccak first-round histogram acceptance, P = {p}");
    println!("uptime at start: {}", uptime());
    let (same, total) = keccak::hist_selfcheck();
    println!("direct comparison of the first round (q at t = 0..deg) and the first fold on synthetic gathers: {same}/{total} identical");
    let states: Vec<[u64; 25]> = (0..p).map(|i| core::array::from_fn(|l| u64::from_le_bytes(batch::xof(b"keccak-input", (i * 25 + l) as u64, 8).try_into().unwrap()))).collect();
    let prove = |hist: bool, inp: Vec<F>, ov: Option<&dyn Fn(&mut Vec<F>)>| {
        keccak::HIST.store(hist, std::sync::atomic::Ordering::Relaxed);
        let t = Instant::now();
        let (b, rep) = keccak::prove(inp, logp, KOpts::default(), ov, &mut Timer::new());
        let ms = t.elapsed().as_secs_f64() * 1e3;
        keccak::ops::take();
        (b, rep, ms)
    };
    let (b0, rep, t0) = prove(false, keccak::encode(&states), None);
    let (b1, _, t1) = prove(true, keccak::encode(&states), None);
    let fe = 68 + 40 * rep.frontend_elems;
    let first_diff = b0.iter().zip(&b1).position(|(a, b)| a != b);
    println!("honest: baseline {} B ({t0:.0} ms), optimized {} B ({t1:.0} ms); frontend (all round polynomials, {} elements) identical: {}; complete proof identical: {}; first differing byte: {first_diff:?}",
        b0.len(), b1.len(), rep.frontend_elems, b0.len() >= fe && b1.len() >= fe && b0[..fe] == b1[..fe], b0 == b1);
    keccak::HIST.store(true, std::sync::atomic::Ordering::Relaxed);
    println!("optimized proof verifies: {:?}", keccak::verify(logp, KOpts::default(), &b1, &mut Timer::new()));
    // Adversarial witnesses take the direct path cell by cell: the bytes must still agree.
    let mut nb = keccak::encode(&states);
    nb[5 * keccak::W + 77] = F::TWO;
    let mut pad = keccak::encode(&states);
    pad[3 * keccak::W + 1700] = F::ONE;
    let flip = |o: &mut Vec<F>| o[17 * keccak::W + 900] = -o[17 * keccak::W + 900];
    for (name, inp, ov) in [("non-boolean input cell", nb, None), ("non-canonical padding cell", pad, None), ("one output bit flipped", keccak::encode(&states), Some(&flip as &dyn Fn(&mut Vec<F>)))] {
        let (a, _, _) = prove(false, inp.clone(), ov);
        let (b, _, _) = prove(true, inp, ov);
        println!("{name}: complete proof identical: {}", a == b);
    }
    keccak::HIST.store(false, std::sync::atomic::Ordering::Relaxed);
    println!("uptime at end: {}", uptime());
}

fn keccak_cmd(logp: usize, tests: bool) {
    use keccak::KOpts;
    let p = 1usize << logp;
    println!("prover mode: {}", keccak_mode());
    println!("# keccak kernel: {p} Keccak-f[1600] permutations, GKR over Goldilocks^5 + WHIR (p3-whir 0.8.0), SHAKE256 transcript");
    println!("uptime at start: {}", uptime());
    println!("rayon threads: {}", rayon::current_num_threads());
    let states: Vec<[u64; 25]> = (0..p).map(|i| core::array::from_fn(|l| u64::from_le_bytes(batch::xof(b"keccak-input", (i * 25 + l) as u64, 8).try_into().unwrap()))).collect();
    let t = Instant::now();
    let native: Vec<[u64; 25]> = states.iter().map(|s| {
        let mut x = *s;
        ::keccak::f1600(&mut x);
        x
    }).collect();
    println!("native keccak::f1600 (crate keccak 0.1.6) on {p} states: {:.2} ms", t.elapsed().as_secs_f64() * 1e3);
    // The layer circuit against the native permutation, every instance.
    let sp = keccak::specs();
    let mut v = keccak::encode(&states);
    for s in &sp {
        v = keccak::apply(s, &v, p);
    }
    let ok = (0..p).filter(|&i| keccak::decode(&v[i * keccak::W..(i + 1) * keccak::W]) == Some(native[i])).count();
    println!("layer circuit (72 layers) output = native Keccak-f[1600]: {ok}/{p}");
    drop(v);
    let degs: Vec<usize> = sp.iter().take(3).map(|s| s.d()).collect();
    println!("round polynomial degrees per round (theta-a, theta-b, chi): {degs:?}; gathers {:?}", sp.iter().take(3).map(|s| s.gathers.len()).collect::<Vec<_>>());
    println!("uptime before prove: {}", uptime());
    let mut tp = Timer::new();
    let (bytes, rep) = keccak::prove(keccak::encode(&states), logp, KOpts::default(), None, &mut tp);
    print_timer("keccak prover", &tp);
    let pf = |i: usize| keccak::PROF[i].load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e3;
    println!("  main-sumcheck split (ms, summed over 73 sumchecks): round 1 (base) {:.0}, phase-A EF rounds {:.0}, phase-A folds {:.0} (of which first fold {:.0}), phase B {:.0}", pf(0), pf(1), pf(2), pf(4), pf(3));
    print_ops(&keccak::ops::take());
    let mut tv = Timer::new();
    let res = keccak::verify(logp, KOpts::default(), &bytes, &mut tv);
    print_timer("keccak verifier", &tv);
    println!("VERIFY: {}", match &res { Ok(_) => "ACCEPT".into(), Err(e) => format!("REJECT {e}") });
    println!(
        "-- proof bytes: total {} = commitment 64 + count 4 + frontend {} elements x 40 = {} + WHIR {} ; {:.1} B/permutation",
        bytes.len(),
        rep.frontend_elems,
        rep.frontend_elems * 40,
        rep.whir_bytes,
        bytes.len() as f64 / p as f64
    );
    println!("-- prover {:.1} ms per {p} permutations = {:.1} ms per 1024", tp.total(), tp.total() * 1024.0 / p as f64);
    if !tests {
        println!("uptime at end: {}", uptime());
        return;
    }
    let (mut passes, mut total) = (0, 0);
    let mut tally = |ok: bool| {
        total += 1;
        passes += ok as usize;
    };
    tally(report_bool(&format!("honest proof: {}", if res.is_ok() { "ACCEPT" } else { "REJECT" }), res.is_ok()));
    let run = |inp: Vec<F>, o: KOpts, ov: Option<&dyn Fn(&mut Vec<F>)>| -> Result<(), String> {
        let (b, _) = keccak::prove(inp, logp, o, ov, &mut Timer::new());
        keccak::verify(logp, o, &b, &mut Timer::new())
    };
    let show = |name: &str, r: &Result<(), String>, expect_ok: bool| -> bool {
        let ok = r.is_ok() == expect_ok;
        println!("[{}] {name}: {}", if ok { "PASS" } else { "FAIL" }, match r { Ok(_) => "ACCEPT".into(), Err(e) => format!("REJECT {e}") });
        ok
    };
    let flip = |o: &mut Vec<F>| o[17 * keccak::W + 900] = -o[17 * keccak::W + 900];
    tally(show("committed output with one bit flipped (instance 17, cell 900)", &run(keccak::encode(&states), KOpts::default(), Some(&flip)), false));
    let swap = |o: &mut Vec<F>| {
        let (a, b) = o.split_at_mut(keccak::W);
        a.swap_with_slice(&mut b[..keccak::W]);
    };
    tally(show("committed outputs of instances 0 and 1 swapped", &run(keccak::encode(&states), KOpts::default(), Some(&swap)), false));
    let mut pad = keccak::encode(&states);
    pad[3 * keccak::W + 1700] = F::ONE;
    tally(show("non-canonical padding cell (instance 3, cell 1700 = 1; never read by the circuit)", &run(pad.clone(), KOpts::default(), None), false));
    let ctl = KOpts { skip_booleanity: true };
    tally(show("same, UNSAFE control without the canonical-input zerocheck", &run(pad, ctl, None), true));
    let mut nb = keccak::encode(&states);
    nb[5 * keccak::W + 77] = F::TWO;
    tally(show("non-boolean input cell (instance 5, cell 77 = 2), honest GKR on the field values", &run(nb.clone(), KOpts::default(), None), false));
    tally(show("same, UNSAFE control without the canonical-input zerocheck", &run(nb, ctl, None), true));
    for (name, off) in [("output claim", 68usize), ("first booleanity round", 68 + 40), ("a GKR layer message (middle of the stream)", 68 + 40 * (rep.frontend_elems / 2))] {
        let mut b = bytes.clone();
        b[off + 3] ^= 0x10;
        tally(show(&format!("tampered byte in {name}"), &keccak::verify(logp, KOpts::default(), &b, &mut Timer::new()), false));
    }
    let mut b = bytes.clone();
    b[68 + 40 * rep.frontend_elems + 40] ^= 1;
    tally(show("tampered byte in the WHIR proof", &keccak::verify(logp, KOpts::default(), &b, &mut Timer::new()), false));
    let mut b = bytes.clone();
    b.push(0);
    tally(show("one trailing byte", &keccak::verify(logp, KOpts::default(), &b, &mut Timer::new()), false));
    println!("KECCAK SUMMARY: {passes}/{total} tests behave as expected");
    println!("uptime at end: {}", uptime());
}

fn r4() {
    let n = 128;
    println!("# r3-cert round 4 tests, N = {n}");
    println!("transcript: {}", if v7() { "QLYAUTH7 registered-round transcript (round 7)" } else { "QLYAUTH3/QLYAUTH4 sponge transcript" });
    println!("uptime at start: {}", uptime());
    let ntt = Ntt::new();
    let base = honest_batch(&ntt, n, 1000);
    let (mut passes, mut total) = (0, 0);
    let mut tally = |p: bool| {
        total += 1;
        passes += p as usize;
    };
    r4_half_selector(&base, &mut tally);
    r4_prefix(&base, &mut tally);
    r4_gruen(&base, &mut tally);
    r4_layout(&base, &mut tally);
    r4_manifest_length(&mut tally);
    println!("R4 SUMMARY: {passes}/{total} tests behave as expected");
    println!("uptime at end: {}", uptime());
}

/// Round 7 measurements: prove and verify the 2,048-signature chain range (16 blocks x 128) under
/// the current transcript (QLYAUTH4, or QLYAUTH7 with `v7`), then write the certificate for a
/// fresh-process verification (`chainverify`).
fn chain_measure() {
    let (nb, per_block) = (16usize, 128usize);
    let n = nb * per_block;
    println!("# r3-cert chain measurement, {nb} blocks x {per_block} records = {n} signatures");
    println!("transcript: {}", if v7() { "QLYAUTH7, profile 0x00070001" } else { "QLYAUTH4" });
    println!("uptime at start: {}", uptime());
    println!("rayon threads: {}", rayon::current_num_threads());
    let net = chain::network_id(b"r7-measure");
    let t = Instant::now();
    let ch = chain::build(net, chain::genesis(&net), 0, nb, per_block, 0);
    println!("chain built and node-validated in {:.0} ms (not counted)", t.elapsed().as_secs_f64() * 1e3);
    let none = |_: &mut Vec<Record>, _: &mut Vec<Vec<u8>>| {};
    let (bytes, sz, tp) = prove_range(&ch, 0..nb, &none);
    print_timer("prover", &tp);
    let mut tv = Timer::new();
    let res = chain::verify_range(&net, &ch.anchor, &ch.headers, &ch.blocks, &ch.state, &bytes, &mut tv);
    print_timer("verifier (in process)", &tv);
    println!("VERIFY: {}", match &res { Ok(_) => "ACCEPT".to_string(), Err(e) => format!("REJECT {e:?}") });
    println!("-- certificate bytes --");
    for (k, v) in [("manifest", sz.manifest), ("public u", sz.u), ("hint counts", sz.nu), ("lift quotients", sz.quot), ("commitment", sz.comm), ("GKR", sz.gkr), ("explicit leaf pair", sz.leaf_pair), ("T", sz.t_claim), ("master", sz.master), ("table", sz.table), ("WHIR length field", sz.whir_len), ("WHIR proof", sz.whir)] {
        println!("  {k:<20}{v:>10}");
    }
    println!("  TOTAL               {:>10}  = {:.2} B/signature; with the {} B of header accumulators {:.2} B/signature", sz.total, sz.total as f64 / n as f64, nb * 64, (sz.total + nb * 64) as f64 / n as f64);
    let path = format!("{}/chain-cert-{}.bin", std::env::var("R3_OUT").unwrap_or_else(|_| ".".into()), if v7() { "v7" } else { "v4" });
    std::fs::write(&path, &bytes).unwrap();
    println!("certificate written to {path} ({} B, sha256 via shasum)", bytes.len());
    println!("uptime at end: {}", uptime());
}

/// Fresh-process verification of a `chainmeasure` certificate (profile chosen by its manifest).
fn chain_verify(path: &str) {
    let (nb, per_block) = (16usize, 128usize);
    println!("# r3-cert chain verify, {path}");
    println!("uptime at start: {}", uptime());
    let net = chain::network_id(b"r7-measure");
    let t = Instant::now();
    let ch = chain::build(net, chain::genesis(&net), 0, nb, per_block, 0);
    println!("chain rebuilt in {:.0} ms (not counted)", t.elapsed().as_secs_f64() * 1e3);
    let bytes = std::fs::read(path).unwrap();
    let (cur0, _) = cert::footprint();
    let mut tv = Timer::new();
    let res = chain::verify_range(&net, &ch.anchor, &ch.headers, &ch.blocks, &ch.state, &bytes, &mut tv);
    print_timer("verifier (fresh process)", &tv);
    let (_, peak) = cert::footprint();
    println!("process footprint before verification {:.0} MiB, lifetime peak {:.0} MiB", cur0 as f64 / 1048576.0, peak as f64 / 1048576.0);
    println!("VERIFY: {}", match &res { Ok(_) => "ACCEPT".to_string(), Err(e) => format!("REJECT {e:?}") });
}

/// Round 7, deliverable 1: the inline reference vectors (§9), reproduced byte for byte.
fn vectors7() {
    let (out, ok) = fs7::vectors();
    print!("{out}");
    let same = out == fs7::EXPECTED_VECTORS;
    println!("output identical to aggregate/r7-check/expected.txt: {same}");
    println!("VECTORS7: {}", if ok && same { "PASS" } else { "FAIL" });
}

fn h9_self() {
    println!("# hidden-u self checks");
    let mut all = true;
    for (name, ok) in hidden::selfcheck() {
        println!("[{}] {name}", if ok { "PASS" } else { "FAIL" });
        all &= ok;
    }
    println!("HIDDEN-U SELF CHECKS: {}", if all { "all pass" } else { "FAILURES" });
}

/// Honest hidden-u certificate at N signatures: prove, verify, sizes by component, timings,
/// canonical extraction checked by libcrux.
fn h9_run(n: usize) {
    println!("# hidden-u certificate (lab profile {:#010x}), N = {n}", hidden::lab_profile9(n));
    println!("uptime at start: {}", uptime());
    println!("rayon threads: {}", rayon::current_num_threads());
    let ntt = Ntt::new();
    let (records, sigs) = batch::libcrux_batch(n, 0);
    let inputs: Vec<hidden::SigIn9> = records.par_iter().zip(sigs.par_iter()).map(|(r, s)| hidden::input_from_raw9(&ntt, r, s)).collect();
    let mut tp = Timer::new();
    let (wit, pubs) = hidden::build9(&ntt, &records, &inputs);
    tp.lap("P-1 witness (z, e, S, Y, bits, nine-permutation sponge traces, multiplicities)");
    println!("witness violations: {:?}", wit.w.viol);
    let ext_ok = (0..n).into_par_iter().filter(|&i| hidden::reconstruct9(&wit, &records[i], i).map(|s| s == sigs[i] && batch::libcrux_verify(&records[i], &s)).unwrap_or(false)).count();
    println!("canonical signatures rebuilt from the committed witness (z, h, bits -> c_tilde check): identical to the originals and accepted by libcrux: {ext_ok}/{n}");
    let nu: Vec<u8> = wit.w.counts.iter().map(|&c| c.min(cert::NU_MAX)).collect();
    let (c, rep) = hidden::prove_lab9(&records, &wit, &pubs, &nu, &mut tp, &hidden::Opts9::default());
    drop(wit);
    drop(pubs);
    print_timer("prover", &tp);
    println!("prover transcript error: {:?}; rounds {}; FS calls {}; coin bytes {}; singleton hashes {}; seeds declined {}; grinding {}; plain bit samples {}", rep.transcript_error, rep.rounds, rep.stats.fs_calls, rep.stats.fs_bytes, rep.stats.singleton_hashes, rep.stats.seeds_declined, rep.stats.grind_calls, rep.stats.bits_calls);
    println!("quotients inexact: {}; WHIR evals equal frontend claims: {}", rep.quotient_inexact, rep.evals_match_whir);
    let (bytes, sz) = c.to_bytes();
    let mut tv = Timer::new();
    let res = hidden::verify_lab9(&records, &bytes, &mut tv, &hidden::Opts9::default());
    print_timer("verifier", &tv);
    println!("VERIFY: {}", match &res { Ok(_) => "ACCEPT".to_string(), Err(e) => format!("REJECT {e:?}") });
    println!("-- certificate bytes by component (exact):");
    for (k, v) in &sz.parts {
        println!("  {v:>10}  {k}");
    }
    println!("  {:>10}  TOTAL = {:.2} B/signature", sz.total, sz.total as f64 / n as f64);
    let (bits, cands) = hidden::pcs_security_bits9(n);
    println!("WHIR prescribed security for the 29-value protocol (p3 planner, JohnsonBound, per-term target 272): {bits:.2} bits; log2 max candidates {cands:.2}");
    let path = format!("{}/h9-cert-{n}.bin", std::env::var("R3_OUT").unwrap_or_else(|_| ".".into()));
    if std::fs::write(&path, &bytes).is_ok() {
        println!("certificate written to {path}");
    }
    println!("uptime at end: {}", uptime());
}

/// Host description for transcripts (Linux: CPU model, cgroup limits; elsewhere a short line).
fn host_line() -> String {
    let rd = |p: &str| std::fs::read_to_string(p).map(|s| s.trim().to_string()).unwrap_or_else(|_| "-".into());
    let model = rd("/proc/cpuinfo").lines().find(|l| l.starts_with("model name")).map(|l| l.split(':').nth(1).unwrap_or("").trim().to_string()).unwrap_or_else(|| "-".into());
    let mem = rd("/proc/meminfo").lines().next().unwrap_or("").to_string();
    format!("cpu {model}; {} logical CPUs visible; {mem}; cgroup memory.max {}; cpu.max {}; {}", std::thread::available_parallelism().map(|n| n.get()).unwrap_or(0), rd("/sys/fs/cgroup/memory.max"), rd("/sys/fs/cgroup/cpu.max"), alloc::describe()) + "; " + &keccak::kec10::describe()
}

/// The lab chain of `n` records in full blocks of 128 (one block every 2 s on the WAN lab
/// network): N / 128 blocks on top of the genesis of network "r10-large-n", global transactions
/// 0 .. N-1. Every key and signature comes from chain::keypair / chain::sign with deterministic
/// SHAKE256 seeds (chain-keygen/2g+epoch, chain-sign/g), signed by libcrux-ml-dsa 0.0.11, and
/// verified natively when the block is built.
fn large_chain(n: usize) -> chain::Chain {
    assert!(n % 128 == 0, "full blocks of 128");
    let net = chain::network_id(b"r10-large-n");
    chain::build(net, chain::genesis(&net), 0, n / 128, 128, 0)
}

/// Prove the lab chain range of N records (round-10 lab chain profile) and write the
/// certificate; `H9_INPROC_VERIFY=1` also verifies it in this process.
fn h9chain_run(n: usize) {
    println!("# hidden-u chain-range certificate (lab chain profile {:#010x}, family {:?}), N = {n}, {} blocks of 128", hidden::lab_chain_profile9(n), hidden::family(), n / 128);
    println!("host: {}", host_line());
    println!("uptime at start: {}", uptime());
    println!("rayon threads: {}", rayon::current_num_threads());
    let t0 = Instant::now();
    let ch = large_chain(n);
    println!("chain built ({} blocks, {} signatures signed and natively verified): {:.1} s", ch.blocks.len(), n, t0.elapsed().as_secs_f64());
    let ntt = Ntt::new();
    let mut tp = Timer::new();
    let parent = &ch.anchor;
    let records = chain::replay(&ch.net, &ch.blocks, &ch.state).unwrap();
    let sigs: Vec<Vec<u8>> = ch.blocks.iter().flat_map(|b| b.sigs.clone()).collect();
    let inputs: Vec<hidden::SigIn9> = records.par_iter().zip(sigs.par_iter()).map(|(rc, sg)| hidden::input_from_raw9(&ntt, rc, sg)).collect();
    drop(sigs);
    let (wit, pubs) = hidden::build9(&ntt, &records, &inputs);
    drop(inputs);
    tp.lap("P-1 replay, witness (z, e, S, Y, bits, nine-permutation sponge traces, multiplicities)");
    println!("witness violations: {:?}", wit.w.viol);
    let nu: Vec<u8> = wit.w.counts.iter().map(|&c| c.min(cert::NU_MAX)).collect();
    let man = hidden::manifest_chain9(&ch.net, n, parent, &ch.headers);
    let ct: Vec<u8> = wit.ct.iter().flatten().copied().collect();
    let x = hidden::instance_chain9(&ch.net, parent, &ch.headers, &ch.blocks, &records, &ct, &nu);
    drop(ct);
    let tprove = Instant::now();
    let (c, rep) = hidden::prove_stmt9(&records, &man, &x, hidden::lab_chain_profile9(n), &wit, &pubs, &nu, &mut tp, &hidden::Opts9::default());
    let prove_s = tprove.elapsed().as_secs_f64();
    drop(wit);
    drop(pubs);
    print_timer("prover", &tp);
    println!("prover wall clock (prove_stmt9 only): {prove_s:.1} s; throughput {:.2} signatures/s", n as f64 / prove_s);
    println!("prover transcript error: {:?}; rounds {}; FS calls {}; coin bytes {}; singleton hashes {}; seeds declined {}; grinding {}; plain bit samples {}", rep.transcript_error, rep.rounds, rep.stats.fs_calls, rep.stats.fs_bytes, rep.stats.singleton_hashes, rep.stats.seeds_declined, rep.stats.grind_calls, rep.stats.bits_calls);
    println!("quotients inexact: {}; WHIR evals equal frontend claims: {}", rep.quotient_inexact, rep.evals_match_whir);
    let (bytes, sz) = c.to_bytes();
    println!("-- certificate bytes by component (exact):");
    for (k, v) in &sz.parts {
        println!("  {v:>10}  {k}");
    }
    println!("  {:>10}  TOTAL = {:.2} B/signature (headers add 64 B per block = {:.2} B/signature)", sz.total, sz.total as f64 / n as f64, 64.0 * (n / 128) as f64 / n as f64);
    let (bits, cands) = hidden::pcs_security_bits9(n);
    let nv = hidden::stacked_vars9(n);
    let (sch, sec) = hidden::schedule_of(hidden::lab_chain_profile9(n), nv);
    println!("WHIR: dimension {nv}, schedule {sch:?}, {sec:?}; prescribed security (p3 planner, composed, 29-value protocol): {bits:.2} bits; log2 max candidates {cands:.2}");
    let shape = hidden::whir_shape9(n);
    println!("WHIR queries per phase (library): {:?} + final {}", shape.rounds.iter().map(|r| r.query_draws).collect::<Vec<_>>(), shape.final_query_draws);
    let dir = std::env::var("R3_OUT").unwrap_or_else(|_| ".".into());
    let path = format!("{dir}/h9chain-cert-{n}-{:08x}.bin", hidden::lab_chain_profile9(n));
    if std::fs::write(&path, &bytes).is_ok() {
        println!("certificate written to {path}");
    }
    if std::env::var("H9_INPROC_VERIFY").is_ok() {
        let mut tv = Timer::new();
        let res = hidden::verify_range9(&ch.net, parent, &ch.headers, &ch.blocks, &ch.state, &bytes, &mut tv, &hidden::Opts9::default());
        print_timer("verifier (same process)", &tv);
        println!("VERIFY: {}", match &res { Ok(_) => "ACCEPT".to_string(), Err(e) => format!("REJECT {e:?}") });
    }
    println!("uptime at end: {}", uptime());
}

/// Fresh-process verification of a chain-range certificate written by h9chain.
fn h9chain_verify(n: usize, path: &str) {
    println!("# hidden-u chain-range verify in a fresh process, N = {n}, {path}");
    println!("host: {}", host_line());
    println!("uptime at start: {}", uptime());
    let t0 = Instant::now();
    let ch = large_chain(n);
    println!("chain rebuilt for the verifier's inputs (not timed below): {:.1} s", t0.elapsed().as_secs_f64());
    let bytes = std::fs::read(path).unwrap();
    let mut tv = Timer::new();
    let t1 = Instant::now();
    let res = hidden::verify_range9(&ch.net, &ch.anchor, &ch.headers, &ch.blocks, &ch.state, &bytes, &mut tv, &hidden::Opts9::default());
    let vs = t1.elapsed().as_secs_f64();
    print_timer("verifier (fresh process)", &tv);
    println!("verifier wall clock: {:.1} ms", vs * 1e3);
    println!("VERIFY: {}", match &res { Ok(_) => "ACCEPT".to_string(), Err(e) => format!("REJECT {e:?}") });
    println!("uptime at end: {}", uptime());
}

/// Round-10 Keccak path against the reference prover: complete hidden-u certificates compared
/// byte for byte, for each N in `ns`, `seeds` batches each, and the challenge injections in
/// `modes` (kec10::INJECT; 0 is the protocol). At N < 512 the reference is run twice, with the
/// stored-layer path and with the low-memory path.
fn k10cmp(ns: &[usize], seeds: u64, modes: &[u8]) {
    use std::sync::atomic::Ordering::Relaxed;
    use keccak::kec10;
    println!("# round-10 Keccak prover path: byte equality of complete hidden-u certificates with the reference prover");
    println!("host: {}", host_line());
    println!("uptime at start: {}", uptime());
    let (mut pass, mut total) = (0usize, 0usize);
    for seed in 0..4u64 {
        let (a, b) = kec10::selfcheck(0x9e37_79b9_7f4a_7c15 ^ seed, 9);
        println!("packed layers = field layers and packed wiring sum = field wiring sum (64 rows, 9 real slots of 16, seed {seed}): {a}/{b}");
        pass += (a == b) as usize;
        total += 1;
    }
    let names = ["protocol (random extension challenges)", "0", "1", "1/2", "eq1(x,r)=0 (exceptional Gruen)", "(1+i)/2", "base field", "mixed per round"];
    let ntt = Ntt::new();
    for &n in ns {
        for seed in 0..seeds {
            let (records, sigs) = batch::libcrux_batch(n, 50_000 + seed * 100_000);
            let inputs: Vec<hidden::SigIn9> = records.par_iter().zip(sigs.par_iter()).map(|(r, s)| hidden::input_from_raw9(&ntt, r, s)).collect();
            let (wit, pubs) = hidden::build9(&ntt, &records, &inputs);
            let nu: Vec<u8> = wit.w.counts.iter().map(|&c| c.min(cert::NU_MAX)).collect();
            for &m in modes {
                kec10::INJECT.store(m, Relaxed);
                let mut prove = |r10: bool, lowmem: bool| -> (Vec<u8>, f64) {
                    kec10::ON.store(r10, Relaxed);
                    unsafe {
                        if lowmem { std::env::set_var("H9_LOWMEM", "1") } else { std::env::remove_var("H9_LOWMEM") }
                    }
                    let t = Instant::now();
                    let (c, _) = hidden::prove_lab9(&records, &wit, &pubs, &nu, &mut Timer::new(), &hidden::Opts9::default());
                    (c.to_bytes().0, t.elapsed().as_secs_f64())
                };
                let (b10, t10) = prove(true, false);
                let (blm, tlm) = prove(false, true);
                let mut line = format!("N = {n}, seed {seed}, challenges {}: r10 {} B in {t10:.1} s, reference (low-memory) {} B in {tlm:.1} s: {}", names[m as usize], b10.len(), blm.len(), if b10 == blm { "IDENTICAL" } else { "DIFFERENT" });
                pass += (b10 == blm) as usize;
                total += 1;
                if b10 != blm {
                    line += &format!(" (first difference at byte {:?})", b10.iter().zip(&blm).position(|(x, y)| x != y));
                }
                if n < 512 {
                    let (bfull, tf) = prove(false, false);
                    line += &format!("; reference (stored layers) {tf:.1} s: {}", if bfull == b10 { "IDENTICAL" } else { "DIFFERENT" });
                    pass += (bfull == b10) as usize;
                    total += 1;
                }
                if m == 0 {
                    kec10::INJECT.store(0, Relaxed);
                    let v = hidden::verify_lab9(&records, &b10, &mut Timer::new(), &hidden::Opts9::default());
                    line += &format!("; r10 certificate verifies: {}", v.is_ok());
                    pass += v.is_ok() as usize;
                    total += 1;
                }
                println!("{line}");
            }
            println!("N = {n} seed {seed} done: {pass}/{total} so far | {}", uptime());
        }
    }
    kec10::INJECT.store(0, Relaxed);
    kec10::ON.store(true, Relaxed);
    println!("K10 EQUALITY SUMMARY: {pass}/{total}");
    println!("uptime at end: {}", uptime());
}

fn main() {
    if std::env::args().any(|a| a == "v7") {
        V7.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    let args: Vec<String> = std::env::args().collect();
    keccak::kec10::configure_from_env();
    match args.get(1).map(|s| s.as_str()) {
        Some("selftest") => selftest(),
        Some("h9self") => h9_self(),
        Some("digests") => digests(),
        Some("whirbench") => {
            let list = |k: usize| -> Vec<usize> { args[k].split(',').map(|x| x.parse().unwrap()).collect() };
            whirbench::run(args[2].parse().unwrap(), (args[3].parse().unwrap(), list(4), list(5)))
        }
        Some("h9tests") => h9tests::run_all(args.get(2).map_or(128, |s| s.parse().unwrap())),
        Some("h9verify") => {
            let n: usize = args[2].parse().unwrap();
            println!("# hidden-u verify in a fresh process, N = {n}, {}", args[3]);
            println!("uptime at start: {}", uptime());
            let (records, _) = batch::libcrux_batch(n, 0);
            let bytes = std::fs::read(&args[3]).unwrap();
            let mut tv = Timer::new();
            let res = hidden::verify_lab9(&records, &bytes, &mut tv, &hidden::Opts9::default());
            print_timer("verifier (fresh process)", &tv);
            println!("VERIFY: {}", match &res { Ok(_) => "ACCEPT".to_string(), Err(e) => format!("REJECT {e:?}") });
        }
        Some("h9") => h9_run(args.get(2).map_or(128, |s| s.parse().unwrap())),
        Some("h9chain") => h9chain_run(args[2].parse().unwrap()),
        Some("h9chainverify") => h9chain_verify(args[2].parse().unwrap(), &args[3]),
        Some("host") => println!("{}", host_line()),
        Some("sched") => {
            // Library-derived WHIR schedules of the round-10 lab profiles, both families.
            for fam in [hidden::Fam::Johnson, hidden::Fam::Unique] {
                hidden::set_family(fam);
                for lg in 5..=16 {
                    let n = 1usize << lg;
                    let nv = hidden::stacked_vars9(n);
                    let (sch, sec) = hidden::schedule_of(hidden::lab_profile9(n), nv);
                    let r = std::panic::catch_unwind(|| {
                        let (bits, cands) = hidden::pcs_security_bits9(n);
                        let sh = hidden::whir_shape9(n);
                        (bits, cands, sh.commitment_ood_samples, sh.rounds.iter().map(|r| r.query_draws).collect::<Vec<_>>(), sh.final_query_draws)
                    });
                    match r {
                        Ok((bits, cands, ood, q, qf)) => println!("{fam:?} N = {n}: profile {:#010x}, dimension {nv}, schedule {sch:?}, {sec:?}: composed {bits:.2} bits, log2 max candidates {cands:.2}, OOD samples {ood}, queries {q:?} + final {qf}", hidden::lab_profile9(n)),
                        Err(_) => println!("{fam:?} N = {n}: dimension {nv}, schedule {sch:?}: NO CONFIG"),
                    }
                }
            }
        }
        Some("k10cmp") => {
            let list = |k: usize| -> Vec<usize> { args[k].split(',').map(|x| x.parse().unwrap()).collect() };
            let modes: Vec<u8> = list(4).into_iter().map(|m| m as u8).collect();
            k10cmp(&list(2), args[3].parse().unwrap(), &modes)
        }
        Some("r10self") => {
            for (k, ok) in fs7::r10_selfcheck() {
                println!("[{}] {k}", if ok { "PASS" } else { "FAIL" });
            }
        }
        Some("vectors7") => vectors7(),
        Some("gates7") => gates7::run(),
        Some("attack7") => attack7::run(),
        Some("attack8") => attack8::run(),
        Some("route8") => route8::run(),
        Some("chainmeasure") => chain_measure(),
        Some("chainverify") => chain_verify(&args[2]),
        Some("run") => run(args.get(2).map_or(128, |s| s.parse().unwrap())),
        Some("soundness") => soundness(),
        Some("r4") => r4(),
        Some("bench-ef") => {
            println!("fmul == p3 mul on 200,000 inputs: {}", field::fmul_selftest());
            let n = 1usize << 12;
            let a: Vec<EF> = (0..n).map(|i| EF::from(F::from_u64(i as u64 * 0x9e37_79b9 + 7)) * pcs::vroot() + EF::from(F::from_u64(i as u64))).collect();
            let b: Vec<EF> = a.iter().rev().copied().collect();
            for (name, fast) in [("p3 quintic mul", false), ("lazy-reduction fmul", true)] {
                let t = Instant::now();
                let mut acc = EF::ZERO;
                for _ in 0..4096 {
                    for i in 0..n {
                        acc += if fast { field::fmul(a[i], b[i]) } else { a[i] * b[i] };
                    }
                }
                println!("{name}: {:.2} ns per multiply-add, single thread ({:?})", t.elapsed().as_secs_f64() * 1e9 / (4096 * n) as f64, acc == EF::ZERO);
            }
        }
        Some("keccak-cmp") => keccak_cmp(args.get(2).map_or(10, |s| s.parse().unwrap())),
        Some("keccak") => keccak_cmd(args.get(2).map_or(10, |s| s.parse().unwrap()), args.get(3).map(|s| s == "tests").unwrap_or(false)),
        Some("chain") => chain_cmd(args.get(2).map_or(8, |s| s.parse().unwrap())),
        Some("verify") => verify_file(args[2].parse().unwrap(), &args[3]),
        _ => eprintln!("usage: r3-cert selftest | run <N> | soundness [v7] | verify <N> <file> | r4 [v7] | chain <per_block> [v7] | vectors7 | gates7 | attack7 | attack8 | route8 | keccak <log2 P> [tests] | bench-ef"),
    }
}

/// Byte-identity check: SHA3-256 of a QLYAUTH3/QLYAUTH4-transcript certificate and a QLYAUTH7
/// lab certificate at N = 128 (libcrux batch, offset 0) and of a Keccak kernel proof at P = 256.
fn digests() {
    use sha3::{Digest, Sha3_256};
    let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
    let ntt = Ntt::new();
    let b = honest_batch(&ntt, 128, 0);
    let (w, pubs) = witness::build(&ntt, &b.records, &b.inputs);
    let u: Vec<u8> = b.inputs.iter().flat_map(|i| i.u.clone()).collect();
    let nu: Vec<u8> = w.counts.iter().map(|&c| c.min(cert::NU_MAX)).collect();
    for v7 in [false, true] {
        let (c, _) = cert::prove_opts(&b.records, &u, &nu, &w, &pubs, &mut Timer::new(), &cert::Opts { v7, ..Default::default() });
        let bytes = c.to_bytes().0;
        let ok = cert::verify_opts(&b.records, &bytes, &mut Timer::new(), &cert::Opts { v7, ..Default::default() }).is_ok();
        println!("DIGEST {} N=128: {} B, verify {ok}, sha3-256 {}", if v7 { "QLYAUTH7-lab-0xfff70007" } else { "QLYAUTH3-QLYAUTH4-transcript" }, bytes.len(), hex(&Sha3_256::digest(&bytes)));
    }
    let p = 256usize;
    let states: Vec<[u64; 25]> = (0..p).map(|i| core::array::from_fn(|l| u64::from_le_bytes(batch::xof(b"keccak-input", (i * 25 + l) as u64, 8).try_into().unwrap()))).collect();
    let (bytes, _) = keccak::prove(keccak::encode(&states), 8, keccak::KOpts::default(), None, &mut Timer::new());
    let ok = keccak::verify(8, keccak::KOpts::default(), &bytes, &mut Timer::new()).is_ok();
    println!("DIGEST keccak-kernel P=256: {} B, verify {ok}, sha3-256 {}", bytes.len(), hex(&Sha3_256::digest(&bytes)));
}
