use vstd::prelude::*;
verus! {
proof fn false_antibonding_improves_bond(nb: int, na: int, t: int)
    requires nb == 2, na == 0, t > 0,
    ensures (nb-(na+1))*t > (nb-na)*t,
{}
}
fn main() {}
