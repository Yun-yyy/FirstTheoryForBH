use vstd::prelude::*;
verus! {
proof fn false_capacity_identifies_state(x: int, y: int)
    requires x >= 0, y >= 0, 4*x + y == 4,
    ensures x == 1 && y == 0,
{}
}
fn main() {}
