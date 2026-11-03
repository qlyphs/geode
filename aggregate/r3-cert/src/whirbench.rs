//! WHIR schedule benchmark for the hidden-u commitment shape: table A of 15 columns of 2^log_dc
//! cells and table B of 2 x 2^19, 29 claims at 5 points, under an explicit (start rate, round
//! rates, folds) schedule. It reports the p3 planner's query counts and composed security, the
//! codeword size of every phase, commit, open and verify times, peak live heap, and proof bytes.
//! Command: `whirbench <N> <start> <r1,r2,..> <f0,f1,..>`.

use p3_commit::MultilinearPcs;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_multilinear_util::point::Point;
use p3_sumcheck::PrescribedPointPcs;
use p3_sumcheck::layout::{Layout as _, Table, observe_commitment};
use rayon::prelude::*;

use crate::cert::{LOG_TAB, Timer, Tree};
use crate::field::{EF, F};
use crate::hidden::{self, NCLAIMS, NCOL};
use crate::pcs::{self, Layout, Tr};

fn p3_point(my: &[EF]) -> Point<EF> {
    Point::new(my.iter().rev().copied().collect::<Vec<_>>())
}

pub fn run(n: usize, prof: (usize, Vec<usize>, Vec<usize>)) {
    let tree = Tree::new(n);
    let log_dc = tree.log_dc;
    let dc = 1usize << log_dc;
    let nv = hidden::stacked_vars9(n);
    println!("# WHIR schedule benchmark: N = {n}, committed 2^{nv} cells (15 x 2^{log_dc} + 2 x 2^19), {NCLAIMS} claims at 5 points");
    println!("schedule: start log inverse rate {}, round log inverse rates {:?}, folds {:?}; JohnsonBound, per-term target 272, grinding 0", prof.0, prof.1, prof.2);
    println!("uptime at start: {}", crate::uptime());
    let (p, fold0) = pcs::make_pcs_prof(nv, NCLAIMS, prof.clone());
    let ws = p3_whir::WhirShape::new(&*p, hidden::NBATCH);
    let sec = p.prescribed_security(&hidden::protocol9(log_dc)).expect("security");
    println!("p3 prescribed security (composed, internal IOP, excludes hashing): {:.2} bits; log2 max candidates {:.2}", sec.error().bits(), sec.log2_max_candidates);
    let mut dom = nv + prof.0;
    let mut vars = nv;
    println!("phase 0: base-field codeword 2^{dom} words = {:.3} GiB; initial sumcheck {} rounds", (1u64 << dom) as f64 * 8.0 / (1u64 << 30) as f64, ws.initial_sumcheck.rounds);
    let mut f = fold0;
    for (k, rd) in ws.rounds.iter().enumerate() {
        vars -= f;
        dom = vars + rd.log_inv_rate;
        println!("phase {}: extension codeword 2^{dom} words = {:.3} GiB; {} queries of {} bits into the previous codeword; sumcheck {} rounds", k + 1, (1u64 << dom) as f64 * 40.0 / (1u64 << 30) as f64, rd.query_draws, rd.index_bits, rd.sumcheck.rounds);
        f = rd.sumcheck.rounds;
    }
    println!("final: polynomial of {} coefficients, {} queries of {} bits, final sumcheck {} rounds", ws.final_poly_len, ws.final_query_draws, ws.final_index_bits, ws.final_sumcheck.rounds);

    let mut tm = Timer::new();
    let mut st = 0x2545_f491_4f6c_dd1du64;
    let mut next = move || {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        st
    };
    let seed = next();
    let ta: Vec<F> = (0..NCOL * dc).into_par_iter().map(|i| F::from_u64((i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ seed)).collect();
    let tb: Vec<F> = (0..2usize << LOG_TAB).into_par_iter().map(|i| F::from_u64((i as u64).wrapping_mul(0xbf58_476d_1ce4_e5b9) ^ seed)).collect();
    let wit = Layout::new_witness(vec![Table::new(RowMajorMatrix::new(ta, dc)), Table::new(RowMajorMatrix::new(tb, 1 << LOG_TAB))], fold0);
    tm.lap("witness (random field values of the committed shape)");
    let mut tr = Tr::new();
    let (comm, pdata) = p.commit(wit, &mut tr.ch).expect("commit");
    tm.lap("WHIR commit");
    let pts_of = |tr: &mut Tr| -> Vec<Point<EF>> { [log_dc, log_dc, log_dc, log_dc, LOG_TAB].iter().map(|&k| p3_point(&tr.sample_efs(k))).collect() };
    let pts = pts_of(&mut tr);
    let proof = p.open_at(pdata, &hidden::protocol9(log_dc), &pts, &mut tr.ch).expect("open");
    let bytes = bincode::serialize(&proof).unwrap();
    tm.lap("WHIR opening (29 values, 5 points)");
    let mut tv = Tr::new();
    observe_commitment::<F, _, _>(&mut tv.ch, comm.clone());
    let pv = pts_of(&mut tv);
    let back: pcs::PcsProof = bincode::deserialize(&bytes).unwrap();
    let ok = p.verify_at(&comm, &back, &hidden::protocol9(log_dc), &pv, &mut tv.ch).is_ok();
    tm.lap("WHIR verification");
    crate::print_timer("whir", &tm);
    println!("WHIR proof bytes: {} ({:.1} B per signature); verify {ok}", bytes.len(), bytes.len() as f64 / n as f64);
    let _ = EF::ZERO;
    println!("uptime at end: {}", crate::uptime());
}
