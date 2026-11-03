//! The ternary residual regions of the round 3 design (section 2.2) and their field coefficients.
//!
//! For a residual coefficient with public u, S in {-1, 0, 1} selects one of three disjoint
//! intervals; e = Y + start(u, S) and Y, K(u, S) - Y must both lie in [0, 2^20).
//! start and K are quadratic in S: start = st0 + st1 S + st2 S^2, K = k0 + k1 S + k2 S^2.

use crate::field::{F, fi};
use crate::mlnat::{A2, GAMMA2};
use p3_field::{Field, PrimeCharacteristicRing};

pub const G: i64 = GAMMA2;
pub const A: i64 = A2;
/// z = X - XOFF; X and XK - X are looked up.
pub const XOFF: i64 = 524_167;
pub const XK: i64 = 1_048_334;
pub const LOG_T: usize = 20;
pub const T: usize = 1 << LOG_T;

/// 0: u = 0, 1: u = 15, 2: any other u.
#[inline(always)]
pub fn class_of(u: u8) -> usize {
    match u {
        0 => 0,
        15 => 1,
        _ => 2,
    }
}

fn d0d15(class: usize) -> (i64, i64) {
    match class {
        0 => (1, 0),
        1 => (0, 1),
        _ => (0, 0),
    }
}

/// Integer start(u, S) and width K(u, S), straight from the definitions with L, R.
pub fn start_int(class: usize, s: i64) -> i64 {
    let (d0, _) = d0d15(class);
    let l = (s * s - s) / 2;
    let r = (s * s + s) / 2;
    -G + 1 - d0 - G * l + (A + d0) * r
}
pub fn width_int(class: usize, s: i64) -> i64 {
    let (d0, d15) = d0d15(class);
    let l = (s * s - s) / 2;
    let r = (s * s + s) / 2;
    A - 1 + d0 - (G + d0) * l + (-G - d0 + d15) * r
}

/// The selector the honest prover picks for residual e (any integer; out-of-region e still
/// gets a selector so that a broken witness can be fed to the prover).
pub fn selector_of(class: usize, e: i64) -> i64 {
    let (d0, _) = d0d15(class);
    if e < -G + 1 - d0 {
        -1
    } else if e > G {
        1
    } else {
        0
    }
}

/// True when e lies in the exact FIPS acceptance region for this u.
pub fn in_region(class: usize, e: i64) -> bool {
    let (d0, d15) = d0d15(class);
    -A + 1 - d0 <= e && e <= A + d15
}

/// Field coefficients per class: [k0, k1, k2, st0, st1, st2].
#[derive(Clone, Copy)]
pub struct Coeffs {
    pub k: [F; 3],
    pub st: [F; 3],
}

pub fn coeffs(class: usize) -> Coeffs {
    let (d0, d15) = d0d15(class);
    let inv2 = F::TWO.inverse();
    Coeffs {
        k: [fi(A - 1 + d0), fi(d15) * inv2, fi(-G - d0) + fi(d15) * inv2],
        st: [fi(-G + 1 - d0), fi(G + A + d0) * inv2, fi(A + d0 - G) * inv2],
    }
}

pub fn all_coeffs() -> [Coeffs; 3] {
    [coeffs(0), coeffs(1), coeffs(2)]
}
