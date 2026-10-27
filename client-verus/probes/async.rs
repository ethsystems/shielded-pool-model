use vstd::prelude::*;
verus! {
async fn wrapper(x: u64) -> (r: u64) ensures r == x { x }
fn main() {}
}
