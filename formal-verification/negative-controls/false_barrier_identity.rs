use vstd::prelude::*;
verus! {
proof fn false_barrier_identity(a: int, b: int, ts: int)
    ensures (ts-a) - (ts-b) == a-b,
{}
}
fn main() {}
