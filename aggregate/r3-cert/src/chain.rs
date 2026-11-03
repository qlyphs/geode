//! Authorization records, per-block authorization roots and the chained authorization
//! accumulator of the round 4 chain-spec section (§D.1-§D.5), on synthetic headers, and the
//! certificate statement that binds a block range to them.
//!
//! The certificate verifier never takes a key from the certificate: it replays the block bodies,
//! resolves each key from state, recomputes c_tilde = H(mu || w1Encode(u)) from the certificate's
//! public u, recomputes every A[b] and compares it with the header, and only then checks the proof
//! against a manifest it derives from the headers.

use std::collections::BTreeMap;

use rayon::prelude::*;
use sha3::digest::{Digest, ExtendableOutput, Update, XofReader};
use sha3::{Sha3_256, Shake256};

use crate::batch::xof;
use crate::cert::{self, Reject, Timer};
use crate::mlnat::{self, Record};
use libcrux_ml_dsa::ml_dsa_87 as m87;

/// H(tag, x) = SHAKE256("Qlyphs/Archive/v1\0" || len(tag):u8 || tag || len(x):u64 || x, 64).
pub fn h(tag: &[u8], x: &[u8]) -> [u8; 64] {
    let mut s = Shake256::default();
    s.update(b"Qlyphs/Archive/v1\0");
    s.update(&[tag.len() as u8]);
    s.update(tag);
    s.update(&(x.len() as u64).to_le_bytes());
    s.update(x);
    let mut out = [0u8; 64];
    s.finalize_xof().read(&mut out);
    out
}

pub fn network_id(label: &[u8]) -> [u8; 64] {
    h(b"lab-network", label)
}

#[derive(Clone, Debug, PartialEq)]
pub struct AuthRecord {
    pub sender: [u8; 20],
    pub key_epoch: u64,
    pub context: Vec<u8>,
    pub payload: Vec<u8>,
}

impl AuthRecord {
    /// 0x51 || 0x01 || sender[20] || key_epoch:u64 || ctx_len:u8 || ctx || payload_len:u32 || payload
    pub fn encode(&self) -> Vec<u8> {
        assert!(self.context.len() <= 255);
        let mut b = vec![0x51, 0x01];
        b.extend_from_slice(&self.sender);
        b.extend_from_slice(&self.key_epoch.to_le_bytes());
        b.push(self.context.len() as u8);
        b.extend_from_slice(&self.context);
        b.extend_from_slice(&(self.payload.len() as u32).to_le_bytes());
        b.extend_from_slice(&self.payload);
        b
    }
    /// Strict decoding: version, lengths, no trailing bytes.
    pub fn decode(b: &[u8]) -> Option<Self> {
        if b.len() < 2 + 20 + 8 + 1 + 4 || b[0] != 0x51 || b[1] != 0x01 {
            return None;
        }
        let sender: [u8; 20] = b[2..22].try_into().ok()?;
        let key_epoch = u64::from_le_bytes(b[22..30].try_into().ok()?);
        let cl = b[30] as usize;
        let ctx_end = 31 + cl;
        if b.len() < ctx_end + 4 {
            return None;
        }
        let pl = u32::from_le_bytes(b[ctx_end..ctx_end + 4].try_into().ok()?) as usize;
        if b.len() != ctx_end + 4 + pl {
            return None;
        }
        Some(AuthRecord { sender, key_epoch, context: b[31..ctx_end].to_vec(), payload: b[ctx_end + 4..].to_vec() })
    }
}

/// M = "Qlyphs/Auth/v1\0" || network_id || AuthRecord.
pub fn signed_message(net: &[u8; 64], rec: &[u8]) -> Vec<u8> {
    let mut m = b"Qlyphs/Auth/v1\0".to_vec();
    m.extend_from_slice(net);
    m.extend_from_slice(rec);
    m
}

/// Synthetic header: the fields this section needs. The proof-of-work preimage is modelled by
/// the identifier, which covers the parent, the height and A[b].
#[derive(Clone, Debug, PartialEq)]
pub struct Header {
    pub height: u64,
    pub parent: [u8; 32],
    pub acc: [u8; 64],
    pub id: [u8; 32],
}

pub fn header_id(parent: &[u8; 32], height: u64, acc: &[u8; 64]) -> [u8; 32] {
    let mut s = Sha3_256::new();
    Digest::update(&mut s, b"qlyphs-lab/header/v1");
    Digest::update(&mut s, parent);
    Digest::update(&mut s, height.to_le_bytes());
    Digest::update(&mut s, acc);
    s.finalize().into()
}

/// Key registry: (sender, key_epoch) -> 2592-byte verification key.
#[derive(Clone, Default)]
pub struct State {
    pub keys: BTreeMap<([u8; 20], u64), Vec<u8>>,
}

/// One block: encoded AuthRecords and the fresh witness package (one signature per record).
#[derive(Clone)]
pub struct Block {
    pub records: Vec<Vec<u8>>,
    pub sigs: Vec<Vec<u8>>,
}

pub struct Chain {
    pub net: [u8; 64],
    /// Parent of the first block (anchor), then one header per block.
    pub anchor: Header,
    pub headers: Vec<Header>,
    pub blocks: Vec<Block>,
    pub state: State,
}

/// block_auth = net || b || count:u32 || per tx: index:u32 || len:u32 || AuthRecord || pk || c_tilde
pub fn auth_root(net: &[u8; 64], height: u64, entries: &[(&[u8], &[u8], [u8; 64])]) -> [u8; 64] {
    let mut b = Vec::new();
    b.extend_from_slice(net);
    b.extend_from_slice(&height.to_le_bytes());
    b.extend_from_slice(&(entries.len() as u32).to_le_bytes());
    for (i, (rec, pk, ct)) in entries.iter().enumerate() {
        assert_eq!(pk.len(), mlnat::PK_BYTES);
        b.extend_from_slice(&(i as u32).to_le_bytes());
        b.extend_from_slice(&(rec.len() as u32).to_le_bytes());
        b.extend_from_slice(rec);
        b.extend_from_slice(pk);
        b.extend_from_slice(ct);
    }
    h(b"block", &b)
}

pub fn acc_next(net: &[u8; 64], height: u64, prev: &[u8; 64], root: &[u8; 64]) -> [u8; 64] {
    let mut x = Vec::with_capacity(64 + 8 + 128);
    x.extend_from_slice(net);
    x.extend_from_slice(&height.to_le_bytes());
    x.extend_from_slice(prev);
    x.extend_from_slice(root);
    h(b"accumulator", &x)
}

pub fn genesis(net: &[u8; 64]) -> Header {
    let acc = h(b"genesis", net);
    Header { height: u64::MAX, parent: [0; 32], acc, id: header_id(&[0; 32], u64::MAX, &acc) }
}

/// A key for (sender index g, epoch): deterministic seeds.
pub fn keypair(g: u64, epoch: u64, salt: &[u8]) -> m87::MLDSA87KeyPair {
    let seed: [u8; 32] = xof(&[b"chain-keygen/".as_slice(), salt].concat(), 2 * g + epoch, 32).try_into().unwrap();
    m87::generate_key_pair(seed)
}

pub fn sender(g: u64) -> [u8; 20] {
    xof(b"chain-sender", g, 20).try_into().unwrap()
}

/// Senders with g % 256 == 0 rotated their key: epoch 0 and epoch 1 are registered and their
/// record is authorized under epoch 1.
pub fn rotated(g: u64) -> bool {
    g % 256 == 0
}

fn sign(kp: &m87::MLDSA87KeyPair, m: &[u8], ctx: &[u8], g: u64, salt: &[u8]) -> Vec<u8> {
    let rnd: [u8; 32] = xof(&[b"chain-sign/".as_slice(), salt].concat(), g, 32).try_into().unwrap();
    m87::sign(&kp.signing_key, m, ctx, rnd).expect("sign").as_slice().to_vec()
}

/// The record of global transaction g.
pub fn record_of(g: u64) -> AuthRecord {
    AuthRecord {
        sender: sender(g),
        key_epoch: rotated(g) as u64,
        context: xof(b"chain-context", g, ((g * 7) % 256) as usize),
        payload: xof(b"chain-payload", g, 32 + (g % 97) as usize),
    }
}

/// Build `nblocks` blocks of `per_block` records on top of `anchor`, starting at global
/// transaction `g0`. Every node-side step of §D.4 runs: native verification of each signature,
/// c_tilde = first 64 bytes of the signature, auth_root, A[b], header.
pub fn build(net: [u8; 64], anchor: Header, start_height: u64, nblocks: usize, per_block: usize, g0: u64) -> Chain {
    let mut state = State::default();
    let mut blocks = Vec::with_capacity(nblocks);
    let mut headers = Vec::with_capacity(nblocks);
    let mut prev = anchor.clone();
    for b in 0..nblocks {
        let height = start_height + b as u64;
        let txs: Vec<(Vec<u8>, Vec<u8>, Vec<u8>, Vec<(u64, Vec<u8>)>)> = (0..per_block)
            .into_par_iter()
            .map(|i| {
                let g = g0 + (b * per_block + i) as u64;
                let rec = record_of(g);
                let enc = rec.encode();
                let mut reg = vec![(0u64, keypair(g, 0, b"").verification_key.as_slice().to_vec())];
                let kp = if rotated(g) {
                    let k1 = keypair(g, 1, b"");
                    reg.push((1, k1.verification_key.as_slice().to_vec()));
                    k1
                } else {
                    keypair(g, 0, b"")
                };
                let m = signed_message(&net, &enc);
                let sig = sign(&kp, &m, &rec.context, g, b"");
                (enc, kp.verification_key.as_slice().to_vec(), sig, reg)
            })
            .collect();
        let mut recs = Vec::with_capacity(per_block);
        let mut sigs = Vec::with_capacity(per_block);
        for (i, (enc, _, sig, reg)) in txs.into_iter().enumerate() {
            let g = g0 + (b * per_block + i) as u64;
            for (e, pk) in reg {
                state.keys.insert((sender(g), e), pk);
            }
            recs.push(enc);
            sigs.push(sig);
        }
        let block = Block { records: recs, sigs };
        let acc = node_accumulator(&net, height, &prev.acc, &block, &state).expect("fresh witness validation");
        let hd = Header { height, parent: prev.id, acc, id: header_id(&prev.id, height, &acc) };
        headers.push(hd.clone());
        blocks.push(block);
        prev = hd;
    }
    Chain { net, anchor, headers, blocks, state }
}

/// Fresh witness validation (§D.4): verify every signature natively against the state key and
/// compute A[b] with c_tilde = the signature's first 64 bytes.
pub fn node_accumulator(net: &[u8; 64], height: u64, prev: &[u8; 64], block: &Block, state: &State) -> Result<[u8; 64], String> {
    if block.sigs.len() != block.records.len() {
        return Err("witness package size".into());
    }
    let mut entries = Vec::with_capacity(block.records.len());
    for (enc, sig) in block.records.iter().zip(&block.sigs) {
        let rec = AuthRecord::decode(enc).ok_or("record encoding")?;
        let pk = state.keys.get(&(rec.sender, rec.key_epoch)).ok_or("unknown key")?;
        let r = Record { pk: pk.clone(), ctx: rec.context.clone(), msg: signed_message(net, enc) };
        if !crate::batch::libcrux_verify(&r, sig) {
            return Err("native verification".into());
        }
        entries.push((enc.as_slice(), pk.as_slice(), sig[..64].try_into().unwrap()));
    }
    Ok(acc_next(net, height, prev, &auth_root(net, height, &entries)))
}

/// Replay: decode each record and resolve its key from state, in block and transaction order.
pub fn replay(net: &[u8; 64], blocks: &[Block], state: &State) -> Result<Vec<Record>, Reject> {
    let mut out = Vec::new();
    for b in blocks {
        for enc in &b.records {
            let rec = AuthRecord::decode(enc).ok_or(Reject::Chain("record encoding".into()))?;
            let pk = state.keys.get(&(rec.sender, rec.key_epoch)).ok_or(Reject::Chain("unknown key".into()))?;
            out.push(Record { pk: pk.clone(), ctx: rec.context, msg: signed_message(net, enc) });
        }
    }
    Ok(out)
}

/// The 512-byte manifest of §D.5.
pub fn manifest_v4(net: &[u8; 64], n: usize, parent: &Header, range: &[Header]) -> Vec<u8> {
    let first = range.first().expect("non-empty range");
    let last = range.last().unwrap();
    let mut m = Vec::with_capacity(cert::MANIFEST);
    m.extend_from_slice(b"QLYAUTH4");
    m.extend_from_slice(&cert::profile_id(n).to_le_bytes());
    m.extend_from_slice(&cert::parameter_digest(n));
    m.extend_from_slice(net);
    m.extend_from_slice(&first.height.to_le_bytes());
    m.extend_from_slice(&(range.len() as u32).to_le_bytes());
    m.extend_from_slice(&(n as u32).to_le_bytes());
    m.extend_from_slice(&parent.id);
    m.extend_from_slice(&last.id);
    m.extend_from_slice(&parent.acc);
    m.extend_from_slice(&last.acc);
    assert_eq!(m.len(), 348);
    m.resize(cert::MANIFEST, 0);
    m
}

/// The 512-byte QLYAUTH7 manifest (spec §2.3): magic "QLYAUTH7", LE32(0x00070001), the former
/// parameter-digest field reserved and zero, then the QLYAUTH4 fields, then 164 zero bytes.
pub fn manifest_v7(net: &[u8; 64], n: usize, parent: &Header, range: &[Header]) -> Vec<u8> {
    let mut m = manifest_v4(net, n, parent, range);
    m[..8].copy_from_slice(b"QLYAUTH7");
    m[8..12].copy_from_slice(&crate::fs7::PROFILE_V7.to_le_bytes());
    m[12..76].fill(0);
    m
}

/// Header104 = parent_id[32] || LE64(height) || accumulator[64].
pub fn header104(h: &Header) -> Vec<u8> {
    let mut b = Vec::with_capacity(104);
    b.extend_from_slice(&h.parent);
    b.extend_from_slice(&h.height.to_le_bytes());
    b.extend_from_slice(&h.acc);
    b
}

/// BlockSection = LE32(block_count) || per block: Header104 || LE32(record_count) || per record:
/// LE32(len) || AuthRecord || state-resolved key[2592]. `records` are the replayed records (their
/// keys come from state, never from a certificate).
pub fn block_section(range: &[Header], blocks: &[Block], records: &[Record]) -> Vec<u8> {
    let mut b = Vec::new();
    b.extend_from_slice(&(blocks.len() as u32).to_le_bytes());
    let mut k = 0;
    for (hd, bl) in range.iter().zip(blocks) {
        b.extend_from_slice(&header104(hd));
        b.extend_from_slice(&(bl.records.len() as u32).to_le_bytes());
        for enc in &bl.records {
            b.extend_from_slice(&(enc.len() as u32).to_le_bytes());
            b.extend_from_slice(enc);
            b.extend_from_slice(&records[k].pk);
            k += 1;
        }
    }
    b
}

/// The raw public instance X of profile 0x00070001 (spec §2.4), synthesized from the verifier's
/// inputs and the certificate's public u and hint counts.
#[allow(clippy::too_many_arguments)]
pub fn instance_v7(net: &[u8; 64], parent: &Header, range: &[Header], blocks: &[Block], records: &[Record], ubytes: &[u8], nu: &[u8]) -> Vec<u8> {
    let man = manifest_v7(net, records.len(), parent, range);
    crate::reg7::instance_chain(crate::fs7::PROFILE_V7, &man, &header104(parent), &block_section(range, blocks, records), ubytes, nu)
}

/// Recompute c_tilde from the certificate's public u and every A[b]; compare with the headers.
fn check_accumulators(net: &[u8; 64], parent: &Header, range: &[Header], blocks: &[Block], records: &[Record], ubytes: &[u8]) -> Result<(), Reject> {
    let n = records.len();
    let cts: Vec<[u8; 64]> = (0..n)
        .into_par_iter()
        .map(|i| {
            let mu = mlnat::mu_of(&mlnat::tr_of(&records[i].pk), &records[i].ctx, &records[i].msg);
            mlnat::c_tilde_of(&mu, &ubytes[1024 * i..1024 * (i + 1)])
        })
        .collect();
    let mut acc = parent.acc;
    let mut k = 0;
    for (hd, b) in range.iter().zip(blocks) {
        let entries: Vec<(&[u8], &[u8], [u8; 64])> = b.records.iter().enumerate().map(|(j, enc)| (enc.as_slice(), records[k + j].pk.as_slice(), cts[k + j])).collect();
        acc = acc_next(net, hd.height, &acc, &auth_root(net, hd.height, &entries));
        if acc != hd.acc {
            return Err(Reject::Chain(format!("accumulator mismatch at height {}", hd.height)));
        }
        k += b.records.len();
    }
    Ok(())
}

/// Verify a certificate for the block range `range` (headers) whose parent header is `parent`.
/// Steps: header linkage; replay with state-derived keys; c_tilde from the certificate's public u;
/// every A[b] recomputed and compared; the proof checked against the derived manifest. The
/// profile is selected by the certificate's manifest magic and profile id: QLYAUTH4, or
/// QLYAUTH7 with a registered profile id (0x00070001); anything else is rejected first.
pub fn verify_range(net: &[u8; 64], parent: &Header, range: &[Header], blocks: &[Block], state: &State, bytes: &[u8], tm: &mut Timer) -> Result<cert::VerifyReport, Reject> {
    verify_range_inspect(net, parent, range, blocks, state, bytes, tm, &cert::Opts::default()).0
}

#[allow(clippy::too_many_arguments)]
pub fn verify_range_inspect(net: &[u8; 64], parent: &Header, range: &[Header], blocks: &[Block], state: &State, bytes: &[u8], tm: &mut Timer, o: &cert::Opts) -> (Result<cert::VerifyReport, Reject>, Option<cert::Inspect7>) {
    let pre = || -> Result<(Vec<Record>, Option<std::sync::Arc<crate::reg7::Table>>), Reject> {
        if range.is_empty() || range.len() != blocks.len() {
            return Err(Reject::Chain("range shape".into()));
        }
        let mut prev = parent;
        for hd in range {
            if hd.parent != prev.id || hd.height != prev.height.wrapping_add(1) || hd.id != header_id(&hd.parent, hd.height, &hd.acc) {
                return Err(Reject::Chain("header linkage".into()));
            }
            prev = hd;
        }
        let records = replay(net, blocks, state)?;
        let n = records.len();
        if bytes.len() < 12 {
            return Err(Reject::Parse("truncated"));
        }
        let table = match &bytes[..8] {
            b"QLYAUTH4" => None,
            b"QLYAUTH7" => {
                let pid = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
                Some(cert::registered_table(pid, n, false).ok_or_else(|| Reject::Profile(format!("unregistered profile {pid:#010x} for N = {n}")))?)
            }
            _ => return Err(Reject::Profile("unregistered manifest magic".into())),
        };
        let c = cert::Cert::from_bytes_v(n, bytes, table.is_some())?;
        check_accumulators(net, parent, range, blocks, &records, &c.u)?;
        Ok((records, table))
    };
    let (records, table) = match pre() {
        Ok(v) => v,
        Err(e) => return (Err(e), None),
    };
    let n = records.len();
    match table {
        None => {
            tm.lap("V-1 header linkage, replay, c_tilde from u, accumulators");
            let man = manifest_v4(net, n, parent, range);
            (cert::verify_stmt(&records, &man, bytes, tm, o), None)
        }
        Some(table) => {
            let c = cert::Cert::from_bytes_v(n, bytes, true).expect("parsed above");
            let x = instance_v7(net, parent, range, blocks, &records, &c.u, &c.nu);
            drop(c);
            tm.lap("V-1 header linkage, replay, c_tilde from u, accumulators, raw instance X");
            let man = manifest_v7(net, n, parent, range);
            cert::verify_stmt7(&records, &man, &x, table, bytes, tm, o)
        }
    }
}
