//! The round registry of the hidden-u lab profiles (round-10 review, §A.4 and §F): one row per
//! registered round with its phase, layer, round index, remaining variables, maintained claim,
//! polynomial degrees before and after normalization, sent coefficients, coin block,
//! terminal identity and claim-merge degree; then the opening shape, the projection coin block,
//! the whole-coin blocks and the compiler census. The rows are built from the protocol
//! structure and asserted equal, round by round, to the table the verifier enforces
//! (`hidden::build_table9`); with a run, every logged verifier round (body length, coin prefix)
//! is also checked against them. Command: `h9registry <N> [run]`.

use std::sync::Arc;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};

use crate::cert::{Timer, Tree, LOG_TAB};
use crate::fs7::Shape;
use crate::hidden::{self, Fam, NCLAIMS};
use crate::keccak::{self, LOGW};
use crate::reg7::{self, Body};

const KB: usize = 40;

#[derive(Clone, Debug)]
pub struct Row {
    pub phase: &'static str,
    pub layer: String,
    pub round: usize,
    pub vars_remaining: String,
    pub claim: String,
    pub deg_before: String,
    pub deg_after: String,
    /// Prover message of the round: extension elements (or a Merkle root).
    pub sent: String,
    pub body: Body,
    pub shape: Shape,
    pub terminal: String,
    pub merge: String,
}

#[allow(clippy::too_many_arguments)]
fn row(phase: &'static str, layer: String, round: usize, vars: String, claim: &str, db: String, da: String, sent: String, body: Body, shape: Shape, terminal: &str, merge: &str) -> Row {
    Row { phase, layer, round, vars_remaining: vars, claim: claim.into(), deg_before: db, deg_after: da, sent, body, shape, terminal: terminal.into(), merge: merge.into() }
}

fn s(x: usize) -> String {
    x.to_string()
}

/// The annotated rows of the lab profile for n signatures (same order as build_table9).
pub fn rows(profile: u32, n: usize) -> Vec<Row> {
    let fr = reg7::front(n);
    let logp = hidden::LOGQ + n.trailing_zeros() as usize;
    let nvx = LOGW + n.trailing_zeros() as usize;
    let nvk = hidden::nvk(n);
    let (p, _) = hidden::make_pcs9(n, profile, Arc::new(AtomicU32::new(0)), Arc::new(AtomicU64::new(0)));
    let ws = p3_whir::WhirShape::new(&*p, hidden::NBATCH);
    let tbl = hidden::table_of9(profile, n, &p);
    let mut r: Vec<Row> = vec![];
    let k = |n: usize| Shape::k(n);
    let nq = fr.trials * (n + fr.slots);
    r.push(row("commitment", "-".into(), 1, "-".into(), "-", "-".into(), "-".into(), "Merkle root of table A | table B (one WHIR commitment)".into(), Body::Real, tbl.rounds[0].shape.clone(), "-", "-"));
    let _ = nq;
    r.push(row("projections", "-".into(), 1, "-".into(), "quotients of the 14 integer lifts", "-".into(), "-".into(), format!("{} quotient bytes", 5 * fr.trials * fr.chunks), Body::Scalar(5 * fr.trials * fr.chunks), Shape { theta: true, ..Default::default() }, "-", "-"));
    // LogUp GKR: layer k claim P_k + lambda Q_k at a point of k variables.
    r.push(row("LogUp GKR", "1".into(), 0, "1".into(), "root = P_1(0)/Q_1(0) + P_1(1)/Q_1(1)", "-".into(), "-".into(), "4 (P_1(0), P_1(1), Q_1(0), Q_1(1))".into(), Body::Scalar(4 * KB), k(2), "root numerator 0, denominator nonzero", "beta_0: line through layer-1 values (degree 1); lambda_1: P + lambda Q (degree 1)"));
    for lk in 1..fr.d {
        for m in 0..lk {
            r.push(row("LogUp GKR", s(lk + 1), m + 1, s(lk - m), "P_k(x) + lambda Q_k(x), normalized (eq factor of the round variable split off)", "3".into(), "2".into(), "2 (a1, a2; a0 = c - x(a1 + a2))".into(), Body::Scalar(2 * KB), k(1), if m + 1 == lk { "H(r) = (Pa Qb + Pb Qa) + lambda Qa Qb from the four finals (next row)" } else { "-" }, "-"));
        }
        let last = lk + 1 == fr.d;
        r.push(row("LogUp GKR", s(lk + 1), 0, "0".into(), "finals of layer k+1", "-".into(), "-".into(), "4 (Pa, Pb, Qa, Qb)".into(), Body::Scalar(4 * KB), k(if last { 1 } else { 2 }), "terminal of the layer above checked from these four values", if last { "beta: line through the leaf pair (degree 1)" } else { "beta: line (degree 1); lambda: P + lambda Q (degree 1)" }));
    }
    r.push(row("LogUp leaves", "-".into(), 0, "-".into(), "leaf pair at the GKR point", "-".into(), "-".into(), "2 (P_leaf, Q_leaf)".into(), Body::Scalar(2 * KB), k(2), "P_leaf, Q_leaf equal the GKR output", "gamma_P, gamma_Q: P + gamma Q merge into the master claim (degree 1)"));
    let cnt = 1 + 4 + fr.log_dc + n + fr.chunks * fr.trials + nvk;
    r.push(row("master weights", "-".into(), 0, "-".into(), "table claim T", "-".into(), "-".into(), "1 (T)".into(), Body::Scalar(KB), k(cnt), "-", "gamma_Z, gamma_B0..3 (independent weights), tau, omega, mu, r0"));
    for m in 0..fr.log_dc {
        r.push(row("master sumcheck", "-".into(), m + 1, s(fr.log_dc - m), "sum of the degree-8 master summand (eq_tau inside the summand)", "8".into(), "8".into(), "8 (h(0), h(2..8))".into(), Body::Scalar(hidden::MASTER_DEG * KB), k(1), if m + 1 == fr.log_dc { "master_f9(X, Y, S, B0..3 from WHIR; public columns from the verifier) = claim" } else { "-" }, "-"));
    }
    for m in 0..fr.log_tab {
        r.push(row("table sumcheck", "-".into(), m + 1, s(fr.log_tab - m), "T = sum eq(rho_T, j)(a_j m_e + b_j m_o)", "2".into(), "2".into(), "2".into(), Body::Scalar(2 * KB), k(1), if m + 1 == fr.log_tab { "eq * (a m_e + b m_o) with m_e, m_o from WHIR" } else { "-" }, "-"));
    }
    for v in 0..nvk {
        let first = v == 0;
        let sig = v < nvk - LOGW - hidden::LOGQ;
        r.push(row("mask sumcheck", "-".into(), v + 1, s(nvk - v), "sum eq(r0, b) mask(b) out(b) (masked output claim from 8 T openings and public c_tilde)", "2".into(), "2".into(), if first { "10 (8 T openings, then h(0), h(2))".into() } else { "2 (h(0), h(2))".into() }, Body::Scalar(if first { 10 * KB } else { 2 * KB }), k(1), if v + 1 == nvk { "out(r1) * (eq mask)(r1), eq mask in closed form" } else { "-" }, if first { "8 T openings fixed before the first mask challenge" } else if sig { "-" } else { "-" }));
    }
    let sp = keccak::specs();
    let nl = sp.len();
    for (li, s_) in sp.iter().enumerate().rev() {
        let (df, d, ng) = (s_.deg_f(), s_.d(), s_.gathers.len());
        let lname = format!("{} ({li})", s_.name);
        for m in 0..logp {
            let first = m == 0;
            r.push(row("Keccak GKR main", lname.clone(), m + 1, s(logp + LOGW - m), "V_out(r) = sum eq(r_p, p) sum_t eq(r_s, s) sel_t(s) f_t(T(p, s)), normalized in p", s(df + 1), s(df), if first { format!("{} (incoming claim value, a1..a{df}; a0 = c - x sum)", df + 1) } else { format!("{df} (a1..a{df})") }, Body::Scalar((df + first as usize) * KB), k(1), "-", if first && li + 1 == nl { "incoming claim = mask output out(r1)" } else if first { "incoming claim = wiring terminal value a(r) of the layer above" } else { "-" }));
        }
        for m in 0..LOGW {
            r.push(row("Keccak GKR main", lname.clone(), logp + m + 1, s(LOGW - m), "same, s variables (weight linear in the round variable)", s(d), s(d), format!("{d} (h(0), h(2..{}))", d), Body::Scalar(d * KB), k(1), "-", "-"));
        }
        r.push(row("Keccak GKR main", lname.clone(), 0, "0".into(), "gathered values T_j(r')", "-".into(), "-".into(), format!("{ng} (T_j)"), Body::Scalar(ng * KB), k(ng), "sum_t w_t(r') f_t(T_j) = claim", "betas: sum_j beta_j T_j(r') (degree 1 in each beta)"));
        for m in 0..LOGW {
            r.push(row("Keccak GKR wiring", lname.clone(), m + 1, s(LOGW - m), "sum_j beta_j T_j(r') = sum_s' in(r'_p, s') M(s')", "2".into(), "2".into(), "2 (h(0), h(2))".into(), Body::Scalar(2 * KB), k(1), if m + 1 == LOGW { "a(r) M(r), M computed by the verifier, a(r) sent next" } else { "-" }, "-"));
        }
    }
    for v in 0..nvx {
        let first = v == 0;
        r.push(row("input link", "-".into(), v + 1, s(nvx - v), "in(r2) - PUB(r2) = sum_x [Wa sum e_q T_q + e8 Wa8 T8 + Wb sum e_q T_q U_q + e0 Wc U_0]", "3".into(), "3".into(), if first { "4 (last wiring value a(r), h(0), h(2), h(3))".into() } else { "3 (h(0), h(2), h(3))".into() }, Body::Scalar(if first { 4 * KB } else { 3 * KB }), k(1), if v + 1 == nvx { "link_f at rho_x with T from WHIR and U_q sent next" } else { "-" }, "-"));
    }
    r.push(row("bit wiring", "-".into(), 0, "-".into(), "re-indexed bit claims U_q(rho)", "-".into(), "-".into(), "8 (U_0..U_7)".into(), Body::Scalar(8 * KB), k(8), "-", "gamma_q: sum_q gamma_q U_q(rho) (degree 1)"));
    for m in 0..hidden::LOG_BW {
        r.push(row("bit wiring", "-".into(), m + 1, s(hidden::LOG_BW - m), "sum_q gamma_q U_q(rho) = sum_y M(y) Bhat(y)", "2".into(), "2".into(), "2".into(), Body::Scalar(2 * KB), k(1), if m + 1 == hidden::LOG_BW { "M(rho_w) Bhat(rho_w), Bhat from one WHIR opening of B0..B3" } else { "-" }, "-"));
    }
    let ood = ws.commitment_ood_samples;
    if ood == 1 {
        r.push(row("WHIR", "initial".into(), 0, s(ws.num_variables), "-", "-".into(), "-".into(), "0".into(), Body::Scalar(0), k(1), "-", "OOD point (one virtual claim)"));
        r.push(row("WHIR", "initial".into(), 0, s(ws.num_variables), "sum_i alpha^i eval_i over 29 openings, then the OOD claim (alpha^29)", "-".into(), "-".into(), "30 (OOD answer, 29 opened values)".into(), Body::Scalar((1 + NCLAIMS) * KB), k(1), "-", "alpha: batching power polynomial of degree 29"));
    } else {
        r.push(row("WHIR", "initial".into(), 0, s(ws.num_variables), "sum_i alpha^i eval_i over 29 openings (no OOD claim)", "-".into(), "-".into(), "29 (opened values)".into(), Body::Scalar(NCLAIMS * KB), k(1), "-", "alpha: batching power polynomial of degree 28"));
    }
    let mut vars = ws.num_variables;
    for m in 0..ws.initial_sumcheck.rounds {
        r.push(row("WHIR sumcheck", "initial".into(), m + 1, s(vars - m), "batched claim (quadratic)", "2".into(), "2".into(), "2".into(), Body::Scalar(2 * KB), k(1), "-", "-"));
    }
    vars -= ws.initial_sumcheck.rounds;
    let mut prev_tree = 1u32;
    for (ri, rd) in ws.rounds.iter().enumerate() {
        let tree = (r.len() + 1) as u32;
        let q = Shape { nk: 1, widths: vec![rd.index_bits as u8; rd.query_draws], ..Default::default() };
        if ood == 1 {
            r.push(row("WHIR", format!("round {}", ri + 1), 0, s(vars), "-", "-".into(), "-".into(), "Merkle root (folded codeword)".into(), Body::Real, k(1), "-", "OOD point"));
            r.push(row("WHIR", format!("round {}", ri + 1), 0, s(vars), "-", "-".into(), "-".into(), "1 (OOD answer)".into(), Body::Scalar(KB), q, &format!("{} query rows of tree {prev_tree} ({} index bits)", rd.query_draws, rd.index_bits), "gamma: batches OOD and query claims (powers)"));
        } else {
            r.push(row("WHIR", format!("round {}", ri + 1), 0, s(vars), "-", "-".into(), "-".into(), "Merkle root (folded codeword)".into(), Body::Real, q, &format!("{} query rows of tree {prev_tree} ({} index bits)", rd.query_draws, rd.index_bits), "gamma: batches the query claims (powers)"));
        }
        for m in 0..rd.sumcheck.rounds {
            r.push(row("WHIR sumcheck", format!("round {}", ri + 1), m + 1, s(vars - m), "batched claim (quadratic)", "2".into(), "2".into(), "2".into(), Body::Scalar(2 * KB), k(1), "-", "-"));
        }
        vars -= rd.sumcheck.rounds;
        prev_tree = tree;
    }
    r.push(row("WHIR", "final".into(), 0, s(vars), "-", "-".into(), "-".into(), format!("{} (final polynomial)", ws.final_poly_len), Body::Scalar(ws.final_poly_len * KB), Shape { widths: vec![ws.final_index_bits as u8; ws.final_query_draws], ..Default::default() }, &format!("{} final query rows of tree {prev_tree}", ws.final_query_draws), "-"));
    for m in 0..ws.final_sumcheck.rounds {
        r.push(row("WHIR sumcheck", "final".into(), m + 1, s(vars - m), "final claim", "2".into(), "2".into(), "2".into(), Body::Scalar(2 * KB), k(1), if m + 1 == ws.final_sumcheck.rounds { "final polynomial at the folded point" } else { "-" }, "-"));
    }
    // The registry must be the enforced table.
    assert_eq!(r.len(), tbl.len(), "registry rows vs registered rounds");
    for (i, (a, b)) in r.iter().zip(&tbl.rounds).enumerate() {
        assert_eq!(a.body, b.body, "round {}: body ({} / {})", i + 1, a.phase, b.label);
        assert_eq!(a.shape, b.shape, "round {}: coin shape ({} / {})", i + 1, a.phase, b.label);
    }
    r
}

fn shape_str(s: &Shape) -> String {
    let mut v = vec![];
    if s.nk > 0 {
        v.push(format!("{} K", s.nk));
    }
    if s.theta {
        v.push("theta".into());
    }
    if s.nq > 0 {
        v.push(format!("{} F_q (slack {})", s.nq, s.qslack));
    }
    if !s.widths.is_empty() {
        v.push(format!("{} indices of {} bits", s.widths.len(), s.widths[0]));
    }
    if v.is_empty() { "none".into() } else { v.join(" + ") }
}

/// Print the registry; with `run`, prove and verify one honest lab certificate and check every
/// logged round against the rows.
pub fn print(n: usize, run: bool) {
    let profile = hidden::lab_profile9(n);
    let rs = rows(profile, n);
    let tbl = hidden::registered_table9(profile, n).expect("registered");
    println!("# round registry, lab profile {profile:#010x} ({:?}), N = {n}: {} registered rounds (equal to the verifier's table, row by row)", hidden::family(), rs.len());
    println!("# columns: round | phase | layer | index | variables remaining | maintained claim | degree before normalization | after | sent | body bytes | coin block (shape; raw bytes) | terminal identity | claim merge");
    for (i, r) in rs.iter().enumerate() {
        let body = match r.body {
            Body::Real => "root".into(),
            Body::Scalar(b) => b.to_string(),
        };
        println!("{} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {}; {} | {} | {}", i + 1, r.phase, r.layer, r.round, r.vars_remaining, r.claim, r.deg_before, r.deg_after, r.sent, body, shape_str(&r.shape), r.shape.used(), r.terminal, r.merge);
    }
    // Opening shape.
    let tree = Tree::new(n);
    let ws = hidden::whir_shape9(n);
    println!("## opening shape (one WHIR proof)");
    println!("table A: 2^{} rows x 15 columns [X, Y, S, B0..B3, T1..T8]; table B: 2^{LOG_TAB} rows x 2 columns [m_even, m_odd]", tree.log_dc);
    println!("batch 1: table A columns X, Y, S, B0, B1, B2, B3 at the master point (7 scalar claims)");
    println!("batch 2: table A columns T1..T8 at the masked-output point (r0_s, r0_i) (8 scalar claims; values sent in the first mask round)");
    println!("batch 3: table A columns T1..T8 at the input-link point rho_x (8 scalar claims)");
    println!("batch 4: table A columns B0..B3 at the bit-wiring point (rho_w_c, rho_i) (4 scalar claims)");
    println!("batch 5: table B columns m_even, m_odd at the table point (2 scalar claims)");
    println!("total: 29 scalar claims at 5 points; OOD claims: {}; batching sum = sum_i alpha^i eval_i over the concrete openings in stacked-placement order, then the OOD claims at the next powers: power polynomial of degree {}", ws.commitment_ood_samples, NCLAIMS + ws.commitment_ood_samples - 1);
    println!("all 29 values and the 5 points are fixed (absorbed) before alpha is drawn: see the round whose body holds them and whose coin is alpha");
    println!("## coin blocks");
    let s1 = &tbl.def(1).shape;
    println!("projection block (atomic, round 1): {} F_q coefficients, 3-byte words, slack {} words, {} raw bytes; short pool = reject (no padding)", s1.nq, s1.qslack, s1.used());
    let kinds: std::collections::BTreeMap<String, usize> = tbl.rounds.iter().fold(Default::default(), |mut m, d| {
        *m.entry(shape_str(&d.shape)).or_default() += 1;
        m
    });
    for (k, v) in &kinds {
        println!("whole-coin blocks of shape [{k}]: {v} rounds");
    }
    let rmin = tbl.rounds.iter().map(|d| d.shape.used()).min().unwrap();
    let argmin = tbl.rounds.iter().position(|d| d.shape.used() == rmin).unwrap() + 1;
    let h = std::iter::once(ws.rounds.first().map(|r| r.index_bits).unwrap_or(ws.final_index_bits)).chain(ws.rounds.iter().map(|r| r.index_bits)).chain(std::iter::once(ws.final_index_bits)).max().unwrap();
    let qv_queries: usize = ws.rounds.iter().map(|r| r.query_draws).sum::<usize>() + ws.final_query_draws;
    println!("## census (derived from the table and the WHIR shape)");
    println!("k (registered rounds) = {}; real trees = {}; formal coin length = {} bytes; minimum raw coin block = {} bytes = {} bits (round {argmin}, {}); Merkle depth h (largest tree) = {h}; query rows opened = {qv_queries}", tbl.len(), tbl.rounds.iter().filter(|d| d.body == Body::Real).count(), tbl.formal_len, rmin, 8 * rmin, tbl.def(argmin).label);
    println!("LogUp table placement (frozen): {} (depth d = {}, GKR proof {} B = 40 d (d + 3))", if tree.embedded { "embedded in the unused leaf positions" } else { "separate, after the occurrence leaves" }, tree.d, 40 * tree.d * (tree.d + 3));
    if run {
        use rayon::prelude::*;
        let ntt = crate::mlnat::Ntt::new();
        let (records, sigs) = crate::batch::libcrux_batch(n, 0);
        let inputs: Vec<hidden::SigIn9> = records.par_iter().zip(sigs.par_iter()).map(|(r, s)| hidden::input_from_raw9(&ntt, r, s)).collect();
        let (wit, pubs) = hidden::build9(&ntt, &records, &inputs);
        let nu: Vec<u8> = wit.w.counts.iter().map(|&c| c.min(crate::cert::NU_MAX)).collect();
        reg7::NODE_CALLS.store(0, Ordering::Relaxed);
        reg7::TREE_COUNTS.lock().unwrap().clear();
        reg7::COUNT.store(true, Ordering::Relaxed);
        let (c, prep) = hidden::prove_lab9(&records, &wit, &pubs, &nu, &mut Timer::new(), &hidden::Opts9 { log: true, ..Default::default() });
        let pnodes = reg7::NODE_CALLS.swap(0, Ordering::Relaxed);
        let pleaves = reg7::LEAF_CALLS.swap(0, Ordering::Relaxed);
        let ptrees = std::mem::take(&mut *reg7::TREE_COUNTS.lock().unwrap());
        let bytes = c.to_bytes().0;
        let man = hidden::manifest_lab9(&records);
        let x = hidden::instance_lab9(profile, &man, &records, &c.ct, &c.nu);
        let (vr, vi) = hidden::verify_stmt9(&records, &man, &x, tbl.clone(), &bytes, &mut Timer::new(), &hidden::Opts9 { log: true, ..Default::default() });
        let vnodes = reg7::NODE_CALLS.swap(0, Ordering::Relaxed);
        let vleaves = reg7::LEAF_CALLS.swap(0, Ordering::Relaxed);
        let vtrees = std::mem::take(&mut *reg7::TREE_COUNTS.lock().unwrap());
        reg7::COUNT.store(false, Ordering::Relaxed);
        let vi = vi.unwrap();
        let vl = vi.log.as_ref().unwrap();
        let mut ok = vl.len() == rs.len() && vr.is_ok();
        for (i, (l, d)) in vl.iter().zip(&tbl.rounds).enumerate() {
            let body_ok = match d.body {
                Body::Real => l.body.is_empty(),
                Body::Scalar(b) => l.body.len() == b,
            };
            if !body_ok || l.prefix.len() != d.shape.used() {
                println!("MISMATCH round {}: body {} prefix {}", i + 1, l.body.len(), l.prefix.len());
                ok = false;
            }
        }
        let st = &vi.stats;
        println!("## run (N = {n}, honest certificate {} B): verifier {}; {} logged verifier rounds, every body length and coin prefix equal to the registry: {ok}", bytes.len(), if vr.is_ok() { "ACCEPT" } else { "REJECT" }, vl.len());
        println!("verifier oracle calls q_V (M): {} coin derivations + {} singleton hashes + {vleaves} Merkle leaf hashes + {vnodes} Merkle node hashes = {}", st.fs_calls, st.singleton_hashes, st.fs_calls + st.singleton_hashes + vleaves as usize + vnodes as usize);
        println!("prover oracle calls q_P (M): {} coin derivations + {} singleton hashes + {pleaves} Merkle leaf hashes + {pnodes} Merkle node hashes = {}", prep.stats.fs_calls, prep.stats.singleton_hashes, prep.stats.fs_calls + prep.stats.singleton_hashes + pleaves as usize + pnodes as usize);
        // Per-tree hash domains: every leaf and node hash of a commitment used that tree's own
        // commit round (a tree of R rows has R leaf hashes and R - 1 node hashes).
        let reals: Vec<u32> = tbl.rounds.iter().enumerate().filter(|(_, d)| d.body == Body::Real).map(|(i, _)| (i + 1) as u32).collect();
        let mut barrier = ptrees.keys().all(|t| reals.contains(t)) && vtrees.keys().all(|t| reals.contains(t));
        for (t, (l, nd)) in &ptrees {
            println!("prover tree {t}: {l} leaf hashes, {nd} node hashes (R - 1 = {})", l.saturating_sub(1));
            barrier &= *nd + 1 == *l;
        }
        for (t, (l, nd)) in &vtrees {
            println!("verifier tree {t}: {l} leaf hashes, {nd} node hashes");
        }
        println!("per-tree hash domains (prover: R leaves and R - 1 nodes under the tree's own round; prover and verifier only under registered commit rounds): {barrier}");
    }
}
