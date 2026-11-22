use vstd::prelude::*;
verus! {
proof fn false_unconditional_quantum_bound(a: int, b: int, t: int, l: int,
                                          x: int, y: int)
    requires a-l > 0,
    ensures a*x*x + b*y*y - 2*t*x*y >= l*(x*x+y*y),
{}
}
fn main() {}
