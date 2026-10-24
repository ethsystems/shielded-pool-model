use vstd::prelude::*;
verus! {
pub trait Effect {
 spec fn value(x: u64) -> u64;
 async fn run(x: u64) -> (r: u64) ensures r == Self::value(x);
}
fn main() {}
}
