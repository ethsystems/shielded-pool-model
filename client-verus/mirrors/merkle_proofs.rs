//! Merkle proof generators at ethsystems/pocs
//! a04b8b38969dfc2ee64de47edee7e396454204a8, `pocs/private-payment/shielded-pool/src/lib/adapters/merkle_tree.rs`:
//!   CommitmentTree::generate_commitment_proof     97-119
//!   AttestationTree::generate_attestation_proof   155-177
//! (region sha256 values: source/manifest.json). A REVIEWED MIRROR, verified by Verus with
//! --no-cheating. It is NOT the shipped lean-imt or alloy code.
//!
//! Stand-ins (faithfulness READ, not proved):
//! - `HashedLeanIMT<32, PoseidonHash>` (zk-kit-lean-imt 0.1.1) is a trait parameter
//!   `T: LeanImtTree`; `CommitmentTree(T)` / `AttestationTree(T)` gain `<T>`. Its contract:
//!   `generate_proof` is a function of the tree and the index (abstract spec `proof_of`), and an
//!   Ok proof has at most 64 siblings (lean_imt.rs:188-220 pushes at most one sibling per
//!   level, and the depth of a tree of usize-many leaves is at most 64: read). Nothing is
//!   assumed about membership, the root, or the hash.
//! - `MerkleProof<32>` keeps its four fields (lean_imt.rs:316-325).
//! - The 5-line iterator chain `proof.siblings.iter().map(|s| B256::from_slice(s)).collect()`
//!   moves unchanged (plus a closure contract) into the helper `siblings_to_b256(&Vec<[u8; 32]>)`,
//!   called as `siblings_to_b256(&proof.siblings)`. In place, this Verus release did not apply
//!   the collect() postcondition (probe runs, not kept here; cause not isolated; the same
//!   chain over a `&Vec` parameter verifies). `B256::from_slice` is the stand-in with the
//!   length-32 precondition, met because siblings are [u8; 32].
//! - `decode_path` (merkle_tree.rs:58-68, the Aeneas-covered function) is copied verbatim as a
//!   helper; its loop gets an invariant. Premise, as in byte_records.rs: usize::BITS == 64.
//! - Merkle proof records keep their four fields; serde derives are dropped.
use vstd::prelude::*;

verus! {

pub struct B256(pub [u8; 32]);

impl B256 {
    pub fn from_slice(src: &[u8]) -> (r: B256)
        requires src.len() == 32,
        ensures r.0@ == src@,
    {
        let mut out = [0u8; 32];
        let mut i: usize = 0;
        while i < 32
            invariant i <= 32, src.len() == 32, out@.len() == 32,
                forall|j: int| 0 <= j < i ==> out@[j] == src@[j],
            decreases 32 - i,
        {
            out[i] = src[i];
            i += 1;
        }
        assert(out@ =~= src@);
        B256(out)
    }
}

pub struct CommitmentMerkleProof {
    pub path: Vec<B256>,
    pub indices: Vec<u8>,
    pub leaf_index: u64,
    pub proof_length: usize,
}

pub struct AttestationMerkleProof {
    pub path: Vec<B256>,
    pub indices: Vec<u8>,
    pub leaf_index: u64,
    pub proof_length: usize,
}

pub struct MerkleProof {
    pub root: [u8; 32],
    pub leaf: [u8; 32],
    pub index: usize,
    pub siblings: Vec<[u8; 32]>,
}

#[derive(Debug)]
pub enum LeanIMTError {
    IndexOutOfBounds,
}

/// zk-kit-lean-imt 0.1.1 HashedLeanIMT as a parameter (see the header).
pub trait LeanImtTree {
    spec fn proof_of(&self, index: usize) -> Result<MerkleProof, LeanIMTError>;
    fn generate_proof(&self, index: usize) -> (r: Result<MerkleProof, LeanIMTError>)
        ensures
            r == self.proof_of(index),
            r is Ok ==> r->Ok_0.siblings@.len() <= 64;
}

pub open spec fn bit(index: usize, i: int) -> u8 {
    ((index >> (i as usize)) & 1usize) as u8
}

fn decode_path(index: usize, path_len: usize) -> (r: Vec<u8>)
    requires usize::BITS == 64, path_len <= 64,
    ensures r@.len() == path_len, forall|i: int| 0 <= i < path_len ==> #[trigger] r@[i] == bit(index, i),
{
    let mut path = Vec::with_capacity(path_len);

    for i in 0..path_len
        invariant path_len <= 64, usize::BITS == 64, path@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] path@[j] == bit(index, j),
    {
        // extract bits from LSB to MSB
        let bit = ((index >> i) & 1) as u8;
        path.push(bit);
    }

    path
}

/// The record built from one lean-imt proof: siblings in order as B256 words, direction
/// bits decoded from the PROOF's compressed index (not from leaf_index), the caller's
/// leaf_index, and proof_length = number of siblings.
pub open spec fn record_ok(path: Seq<B256>, indices: Seq<u8>, rec_leaf: u64, proof_length: usize,
                           p: MerkleProof, leaf_index: u64) -> bool {
    &&& path.len() == p.siblings@.len()
    &&& forall|i: int| 0 <= i < path.len() ==> (#[trigger] path[i]).0@ == p.siblings@[i]@
    &&& indices.len() == p.siblings@.len()
    &&& forall|i: int| 0 <= i < indices.len() ==> #[trigger] indices[i] == bit(p.index, i)
    &&& rec_leaf == leaf_index
    &&& proof_length == p.siblings@.len()
}

/// Stand-in for the iterator chain `proof.siblings.iter().map(|s| B256::from_slice(s)).collect()`.
pub fn siblings_to_b256(siblings: &Vec<[u8; 32]>) -> (r: Vec<B256>)
    ensures r@.len() == siblings@.len(), forall|i: int| 0 <= i < r@.len() ==> (#[trigger] r@[i]).0@ == siblings@[i]@,
{
    siblings.iter().map(|s: &[u8; 32]| -> (r: B256) ensures r.0@ == s@ { B256::from_slice(s) }).collect()
}

pub struct CommitmentTree<T: LeanImtTree>(pub T);

impl<T: LeanImtTree> CommitmentTree<T> {
    /// Generate a merkle proof for the leaf at the given index.
    pub fn generate_commitment_proof(
        &self,
        leaf_index: u64,
    ) -> (r: Option<CommitmentMerkleProof>)
        requires usize::BITS == 64,
        ensures
            self.0.proof_of(leaf_index as usize) is Err ==> r is None,
            self.0.proof_of(leaf_index as usize) is Ok ==> (r is Some && record_ok(r->Some_0.path@, r->Some_0.indices@,
                r->Some_0.leaf_index, r->Some_0.proof_length, self.0.proof_of(leaf_index as usize)->Ok_0, leaf_index)),
    {
        let proof = self.0.generate_proof(leaf_index as usize).ok()?;

        let path: Vec<B256> = siblings_to_b256(&proof.siblings);

        let indices: Vec<u8> = decode_path(proof.index, proof.siblings.len());

        let proof_length = path.len();

        Some(CommitmentMerkleProof {
            path,
            indices,
            leaf_index,
            proof_length,
        })
    }
}

pub struct AttestationTree<T: LeanImtTree>(pub T);

impl<T: LeanImtTree> AttestationTree<T> {
    /// Generate a merkle proof for the leaf at the given index.
    pub fn generate_attestation_proof(
        &self,
        leaf_index: u64,
    ) -> (r: Option<AttestationMerkleProof>)
        requires usize::BITS == 64,
        ensures
            self.0.proof_of(leaf_index as usize) is Err ==> r is None,
            self.0.proof_of(leaf_index as usize) is Ok ==> (r is Some && record_ok(r->Some_0.path@, r->Some_0.indices@,
                r->Some_0.leaf_index, r->Some_0.proof_length, self.0.proof_of(leaf_index as usize)->Ok_0, leaf_index)),
    {
        let proof = self.0.generate_proof(leaf_index as usize).ok()?;

        let path: Vec<B256> = siblings_to_b256(&proof.siblings);

        let indices: Vec<u8> = decode_path(proof.index, proof.siblings.len());

        let proof_length = path.len();

        Some(AttestationMerkleProof {
            path,
            indices,
            leaf_index,
            proof_length,
        })
    }
}

fn main() {
}

} // verus!
