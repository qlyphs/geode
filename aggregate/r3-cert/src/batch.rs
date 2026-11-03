//! Real ML-DSA-87 signatures from libcrux-ml-dsa 0.0.11: distinct keys, pure mode with contexts,
//! deterministic seeds.

use crate::mlnat::{Record, shake256};
use libcrux_ml_dsa::ml_dsa_87 as m87;
use rayon::prelude::*;

pub fn xof(domain: &[u8], idx: u64, len: usize) -> Vec<u8> {
    let mut out = vec![0u8; len];
    shake256(&[b"qlyphs-r3-cert/", domain, &idx.to_le_bytes()], &mut out);
    out
}

/// n records signed by n distinct keys. Message i has 32 + (i mod 97) bytes, context
/// 1 + (2 i mod 255) bytes. Returns the records and the raw signatures.
pub fn libcrux_batch(n: usize, offset: u64) -> (Vec<Record>, Vec<Vec<u8>>) {
    let v: Vec<(Record, Vec<u8>)> = (0..n)
        .into_par_iter()
        .map(|i| {
            let idx = offset + i as u64;
            let kseed: [u8; 32] = xof(b"keygen", idx, 32).try_into().unwrap();
            let rnd: [u8; 32] = xof(b"sign-rnd", idx, 32).try_into().unwrap();
            let kp = m87::generate_key_pair(kseed);
            let msg = xof(b"message", idx, 32 + (i % 97));
            let ctx = xof(b"context", idx, 1 + (i * 2) % 255);
            let sig = m87::sign(&kp.signing_key, &msg, &ctx, rnd).expect("sign");
            (Record { pk: kp.verification_key.as_slice().to_vec(), ctx, msg }, sig.as_slice().to_vec())
        })
        .collect();
    v.into_iter().unzip()
}

pub fn libcrux_verify(rec: &Record, sig: &[u8]) -> bool {
    let Ok(pk): Result<[u8; 2592], _> = rec.pk.clone().try_into() else { return false };
    let Ok(sg): Result<[u8; 4627], _> = sig.to_vec().try_into() else { return false };
    m87::verify(&m87::MLDSA87VerificationKey::new(pk), &rec.msg, &rec.ctx, &m87::MLDSA87Signature::new(sg)).is_ok()
}
