use vstd::prelude::*;
verus! {
proof fn false_lower_forward_implies_lower_reverse(
    a: int, b: int, ts: int, a2: int, b2: int, ts2: int)
    requires ts >= a, ts >= b, ts2 >= a2, ts2 >= b2,
             ts2-a2 < ts-a,
    ensures ts2-b2 < ts-b,
{}
}
fn main() {}
