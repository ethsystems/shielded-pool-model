use vstd::prelude::*;
verus! {
async fn effect(x: u64) -> (r: u64) ensures r == x { x }
async fn wrapper(x: u64) -> (r: u64) ensures r == x { effect(x).await }
fn main() {}
}
