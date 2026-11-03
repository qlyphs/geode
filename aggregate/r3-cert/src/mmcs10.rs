//! The Merkle commitment scheme of the round-10 lab profiles: the QLYAUTH7 leaf framing and the
//! tree-separated node hash (REQ-1), with the tree's hash context captured once per operation.
//!
//! Every operation builds its own inner `MerkleTreeMmcs` whose leaf and node hashers carry the
//! tree id by value, so all parallel hashing tasks of one commitment or one verification see
//! one immutable context:
//! - commit: the tree id is the registered round that commits the tree, read once from the
//!   adapter's routing cell at the start of the commitment;
//! - verify: the tree id is the round whose observed root is the commitment being opened (from
//!   the adapter's root registry), independent of any ambient routing state; an unknown or
//!   ambiguous root is rejected.
//! A round id that does not fit LE16 is rejected before narrowing.

use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use p3_commit::{BatchOpening, BatchOpeningRef, Mmcs};
use p3_field::PrimeField64;
use p3_matrix::{Dimensions, Matrix};
use p3_merkle_tree::{MerkleTree, MerkleTreeError, MerkleTreeMmcs};
use p3_symmetric::{CryptographicHasher, MerkleCap, PseudoCompressionFunction};

use crate::field::F;
use crate::fs7;
use crate::reg7::{self, to_bytes, to_words};

/// Leaf hasher with a fixed tree id (QLYAUTH7 leaf framing, kind 0x00).
#[derive(Clone)]
pub struct LeafT {
    pub profile: u32,
    pub tree: u32,
    pub calls: Arc<AtomicU64>,
}

impl CryptographicHasher<F, [u64; 8]> for LeafT {
    fn hash_iter<I: IntoIterator<Item = F>>(&self, input: I) -> [u64; 8] {
        let mut row = Vec::with_capacity(1280);
        for x in input {
            row.extend_from_slice(&x.as_canonical_u64().to_le_bytes());
        }
        self.calls.fetch_add(1, Ordering::Relaxed);
        reg7::count(self.tree, true);
        to_words(&fs7::leaf_hash(self.profile, self.tree, fs7::KIND_ROW, &row))
    }
}

/// Node hasher with a fixed tree id: H64(0x81 || LE32(profile) || LE16(tree) || L || R).
#[derive(Clone)]
pub struct NodeT {
    pub profile: u32,
    pub tree: u16,
}

impl PseudoCompressionFunction<[u64; 8], 2> for NodeT {
    fn compress(&self, input: [[u64; 8]; 2]) -> [u64; 8] {
        reg7::count(self.tree as u32, false);
        let o = reg7::node_round_override();
        let t = if o != 0 { o as u16 } else { self.tree };
        to_words(&fs7::node_hash_tree(self.profile, t, &to_bytes(&input[0]), &to_bytes(&input[1])))
    }
}

pub type Inner = MerkleTreeMmcs<F, u64, LeafT, NodeT, 2, 8>;

/// Root registry of one transcript: (registered round, observed root).
pub type Roots = Arc<Mutex<Vec<(u32, [u8; 64])>>>;

#[derive(Clone)]
pub struct Mmcs10 {
    pub profile: u32,
    /// The adapter's routing cell, read once at the start of a commitment.
    pub cell: Arc<AtomicU32>,
    pub roots: Roots,
    pub calls: Arc<AtomicU64>,
}

/// A round id as the LE16 tree id of the node hash; out-of-range ids are rejected first.
pub fn narrow(t: u32) -> Result<u16, String> {
    if t == 0 {
        return Err("no registered tree".into());
    }
    u16::try_from(t).map_err(|_| format!("tree round {t} does not fit LE16"))
}

impl Mmcs10 {
    fn inner(&self, tree: u32) -> Result<Inner, String> {
        let t16 = narrow(tree)?;
        Ok(Inner::new(LeafT { profile: self.profile, tree, calls: self.calls.clone() }, NodeT { profile: self.profile, tree: t16 }, 0))
    }
    /// The tree whose observed root is `commit` (exactly one).
    fn tree_of(&self, commit: &MerkleCap<F, [u64; 8]>) -> Result<u32, String> {
        if commit.roots().len() != 1 {
            return Err("commitment cap of height > 0".into());
        }
        let root = to_bytes(&commit.roots()[0]);
        let reg = self.roots.lock().unwrap();
        let hits: Vec<u32> = reg.iter().filter(|(_, r)| *r == root).map(|(t, _)| *t).collect();
        match hits.as_slice() {
            [t] => Ok(*t),
            [] => Err("opening of a root that was never observed".into()),
            _ => Err("the same root observed in several rounds".into()),
        }
    }
    fn commit_inner(&self) -> Inner {
        let t = self.cell.load(Ordering::Relaxed);
        self.inner(t).expect("commitment outside a registered tree")
    }
}

fn verr(_e: String) -> MerkleTreeError {
    // A tree-context failure (unknown root, ambiguous root, round id out of range) rejects the
    // opening as a commitment mismatch.
    MerkleTreeError::CapMismatch
}

impl Mmcs<F> for Mmcs10 {
    type ProverData<M> = MerkleTree<F, u64, M, 2, 8>;
    type Commitment = MerkleCap<F, [u64; 8]>;
    type Proof = <Inner as Mmcs<F>>::Proof;
    type MultiProof = <Inner as Mmcs<F>>::MultiProof;
    type Error = MerkleTreeError;

    fn commit<M: Matrix<F>>(&self, inputs: Vec<M>) -> (Self::Commitment, Self::ProverData<M>) {
        self.commit_inner().commit(inputs)
    }

    fn open_batch<M: Matrix<F>>(&self, index: usize, prover_data: &Self::ProverData<M>) -> BatchOpening<F, Self> {
        // Opening reads stored digests only; the hashers are not used.
        let (v, p) = self.inner(1).unwrap().open_batch(index, prover_data).unpack();
        BatchOpening::new(v, p)
    }

    fn get_matrices<'a, M: Matrix<F>>(&self, prover_data: &'a Self::ProverData<M>) -> Vec<&'a M> {
        self.inner(1).unwrap().get_matrices(prover_data)
    }

    fn verify_batch(&self, commit: &Self::Commitment, dimensions: &[Dimensions], index: usize, batch_opening: BatchOpeningRef<'_, F, Self>) -> Result<(), Self::Error> {
        let t = self.tree_of(commit).map_err(verr)?;
        self.inner(t).map_err(verr)?.verify_batch(commit, dimensions, index, BatchOpeningRef::new(batch_opening.opened_values, batch_opening.opening_proof))
    }

    fn open_multi_batch<M: Matrix<F>>(&self, indices: &[usize], prover_data: &Self::ProverData<M>) -> (Vec<Vec<Vec<F>>>, Self::MultiProof) {
        self.inner(1).unwrap().open_multi_batch(indices, prover_data)
    }

    fn verify_multi_batch<R: AsRef<[F]> + PartialEq>(&self, commit: &Self::Commitment, dimensions: &[Dimensions], indices: &[usize], opened_values: &[Vec<R>], proof: &Self::MultiProof) -> Result<(), Self::Error> {
        let t = self.tree_of(commit).map_err(verr)?;
        self.inner(t).map_err(verr)?.verify_multi_batch(commit, dimensions, indices, opened_values, proof)
    }
}
