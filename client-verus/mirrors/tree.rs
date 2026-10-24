//! Thin reviewed delegates. These contracts do not verify lean-imt.
//! The four target bodies retain the original one-line calls. Generic dependency contracts
//! specify only forwarding. All insertion, hashing, storage and root semantics remain abstract.
use vstd::prelude::*;
verus! {
pub trait LeanImt: Sized {
 spec fn model(&self) -> int;
 spec fn inserted(state: int,leaf: Seq<u8>) -> int;
 spec fn root_of(state: int) -> Option<[u8;32]>;
 fn insert(&mut self,leaf: &[u8;32])
 ensures final(self).model() == Self::inserted(old(self).model(),leaf@);
 fn root(&self) -> (r: Option<[u8;32]>) ensures r == Self::root_of(self.model());
}
pub struct CommitmentTree<T: LeanImt>(pub T);
pub struct AttestationTree<T: LeanImt>(pub T);
impl<T: LeanImt> CommitmentTree<T> {
pub fn insert(&mut self,leaf: &[u8;32])
 ensures final(self).0.model() == T::inserted(old(self).0.model(),leaf@),
 // STRENGTH CommitmentTree_insert
{self.0.insert(leaf);}
}
impl<T: LeanImt> CommitmentTree<T> {
pub fn root(&self) -> (r: Option<[u8;32]>)
 ensures r == T::root_of(self.0.model()),
 // STRENGTH CommitmentTree_root
{self.0.root()}
}
impl<T: LeanImt> AttestationTree<T> {
pub fn insert(&mut self,leaf: &[u8;32])
 ensures final(self).0.model() == T::inserted(old(self).0.model(),leaf@),
 // STRENGTH AttestationTree_insert
{self.0.insert(leaf);}
}
impl<T: LeanImt> AttestationTree<T> {
pub fn root(&self) -> (r: Option<[u8;32]>)
 ensures r == T::root_of(self.0.model()),
 // STRENGTH AttestationTree_root
{self.0.root()}
}
fn main() {}
}
