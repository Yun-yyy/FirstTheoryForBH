//! Exact, conditional mathematical proofs linked to the borohydride review.
//! int denotes unbounded mathematical integers, not machine integers.
//! Rational energies and amplitudes are encoded using positive common
//! denominators. See README.md for the physical model and trust boundary.
use vstd::prelude::*;

verus! {

pub open spec fn norm2(x: int, y: int) -> int { x*x + y*y }
pub open spec fn energy(a: int, b: int, t: int, x: int, y: int) -> int {
    a*x*x + b*y*y - 2*t*x*y
}
pub open spec fn stabilization(nb: int, na: int, t: int) -> int {
    (nb-na)*t
}
pub open spec fn capacity(x: int, y: int) -> int { 4*x+y }
// Atom inventory (Mg, B, H) in amounts of the five named species.
pub open spec fn inventory(mgbh4: int, mgh2: int, boron: int, h2: int, mg: int)
    -> (int, int, int)
{
    (mgbh4+mgh2+mg, 2*mgbh4+boron, 8*mgbh4+2*mgh2+2*h2)
}

// Q1. A rational lower-bound certificate for a general real 2x2 Hermitian H.
// No eigenvalue, normalized amplitude, or desired conclusion is assumed.
proof fn assoc(a: int, b: int, c: int) by (nonlinear_arith)
    ensures (a*b)*c == a*(b*c),
{}
proof fn comm(a: int, b: int) by (nonlinear_arith)
    ensures a*b == b*a,
{}
proof fn distribute(a: int, b: int, c: int) by (nonlinear_arith)
    ensures a*(b+c) == a*b+a*c, a*(b-c) == a*b-a*c,
{}
proof fn product_four(a: int, b: int, c: int, d: int)
    ensures (a*b)*(c*d) == (a*c)*(b*d),
{
    assoc(a,b,c*d); assoc(b,c,d); comm(b,c);
    assoc(c,b,d); assoc(a,c,b*d);
}
proof fn difference_square(p: int, q: int) by (nonlinear_arith)
    ensures (p-q)*(p-q) == p*p-2*(p*q)+q*q,
{}
proof fn double_product(a: int, b: int, c: int) by (nonlinear_arith)
    ensures a*(2*b*c) == 2*((a*b)*c),
{}
proof fn complete_square_identity(aa: int, bb: int, t: int, x: int, y: int)
    ensures aa*(aa*x*x+bb*y*y-2*t*x*y)
        == (aa*x-t*y)*(aa*x-t*y)+(aa*bb-t*t)*y*y,
{
    let xx = x*x;
    let yy = y*y;
    let xy = x*y;
    assoc(aa,x,x); assoc(bb,y,y); assoc(2*t,x,y);
    distribute(aa,aa*xx+bb*yy,2*t*xy);
    distribute(aa,aa*xx,bb*yy);
    assoc(aa,aa,xx); assoc(aa,bb,yy);
    double_product(aa,t,xy);
    assert(aa*(aa*x*x+bb*y*y-2*t*x*y)
        == (aa*aa)*xx+(aa*bb)*yy-2*((aa*t)*xy));

    difference_square(aa*x,t*y);
    product_four(aa,x,aa,x);
    product_four(aa,x,t,y);
    product_four(t,y,t,y);
    assert((aa*x-t*y)*(aa*x-t*y)
        == (aa*aa)*xx-2*((aa*t)*xy)+(t*t)*yy);

    assoc(aa*bb-t*t,y,y);
    comm(aa*bb-t*t,yy);
    distribute(yy,aa*bb,t*t);
    comm(yy,aa*bb); comm(yy,t*t);
    assert((aa*bb-t*t)*y*y == (aa*bb)*yy-(t*t)*yy);
}

pub proof fn two_orbital_real_lower_bound(
    a: int, b: int, t: int, l: int, x: int, y: int)
    requires a-l > 0, (a-l)*(b-l)-t*t >= 0,
    ensures energy(a,b,t,x,y) >= l*norm2(x,y),
{
    let aa = a-l;
    let bb = b-l;
    let det = aa*bb-t*t;
    let gap = energy(a,b,t,x,y)-l*norm2(x,y);
    assert(gap == aa*x*x+bb*y*y-2*t*x*y)
        by (nonlinear_arith)
        requires aa == a-l, bb == b-l,
                 gap == a*x*x+b*y*y-2*t*x*y-l*(x*x+y*y);
    complete_square_identity(aa,bb,t,x,y);
    assert(aa*gap == (aa*x-t*y)*(aa*x-t*y) + det*y*y);
    assert((aa*x-t*y)*(aa*x-t*y) >= 0) by (nonlinear_arith);
    assert(det*y*y >= 0) by (nonlinear_arith) requires det >= 0;
    assert(aa*gap >= 0);
    assert(gap >= 0) by (nonlinear_arith) requires aa > 0, aa*gap >= 0;
}

// Complex amplitudes psi=(xr+i*xi, yr+i*yi), real H entries.
pub proof fn two_orbital_complex_lower_bound(
    a: int, b: int, t: int, l: int,
    xr: int, xi: int, yr: int, yi: int)
    requires a-l > 0, (a-l)*(b-l)-t*t >= 0,
    ensures
        energy(a,b,t,xr,yr)+energy(a,b,t,xi,yi)
            >= l*(norm2(xr,yr)+norm2(xi,yi)),
{
    two_orbital_real_lower_bound(a,b,t,l,xr,yr);
    two_orbital_real_lower_bound(a,b,t,l,xi,yi);
    assert(l*norm2(xr,yr)+l*norm2(xi,yi)
        == l*(norm2(xr,yr)+norm2(xi,yi))) by (nonlinear_arith);
}

// Q2. Symmetric special case: universal lower bound and an attaining vector.
pub proof fn symmetric_ground_state(e: int, t: int, x: int, y: int)
    requires t > 0,
    ensures
        energy(e,e,t,x,y) >= (e-t)*norm2(x,y),
        norm2(1,1) > 0,
        energy(e,e,t,1,1) == (e-t)*norm2(1,1),
{
    assert((e-(e-t))*(e-(e-t))-t*t == 0) by (nonlinear_arith);
    two_orbital_real_lower_bound(e,e,t,e-t,x,y);
}

pub proof fn symmetric_eigenstates(e: int, t: int) by (nonlinear_arith)
    requires t > 0,
    ensures
        e-t < e+t,
        e*1-t*1 == (e-t)*1,
        -t*1+e*1 == (e-t)*1,
        e*1-t*(-1) == (e+t)*1,
        -t*1+e*(-1) == (e+t)*(-1),
        energy(e,e,t,1,-1) == (e+t)*norm2(1,-1),
{}

pub proof fn symmetric_complex_ground_state(
    e: int, t: int, xr: int, xi: int, yr: int, yi: int)
    requires t > 0,
    ensures
        energy(e,e,t,xr,yr)+energy(e,e,t,xi,yi)
          >= (e-t)*(norm2(xr,yr)+norm2(xi,yi)),
        energy(e,e,t,1,1) == (e-t)*norm2(1,1),
        norm2(1,1) > 0,
{
    assert((e-(e-t))*(e-(e-t))-t*t == 0) by (nonlinear_arith);
    two_orbital_complex_lower_bound(e,e,t,e-t,xr,xi,yr,yi);
    symmetric_ground_state(e,t,1,1);
}

pub proof fn orbital_energy_stabilization_bridge(e: int, t: int, nb: int, na: int)
    by (nonlinear_arith)
    ensures nb*(e-t)+na*(e+t) == (nb+na)*e-stabilization(nb,na,t),
{}

// Q3. Fixed-orbital hopping stabilization, not an actual dissociation barrier.
pub proof fn opposite_electron_changes_reduce_stabilization(
    nb: int, na: int, t: int) by (nonlinear_arith)
    requires 1 <= nb <= 2, 0 <= na < 2, t > 0,
    ensures
        stabilization(nb-1,na,t) == stabilization(nb,na,t)-t,
        stabilization(nb,na+1,t) == stabilization(nb,na,t)-t,
        stabilization(nb-1,na,t) < stabilization(nb,na,t),
        stabilization(nb,na+1,t) < stabilization(nb,na,t),
{}

// T1. Purely algebraic, valid for any common energy/free-energy reference.
pub proof fn barrier_identity(a: int, b: int, ts: int)
    ensures (ts-a)-(ts-b) == b-a,
{}

pub proof fn endpoint_preserving_catalysis(a: int, b: int, ts: int, d: int)
    requires d > 0, ts-d >= a, ts-d >= b,
    ensures
        (ts-d-a) == (ts-a)-d,
        (ts-d-b) == (ts-b)-d,
        (ts-d-a) < (ts-a),
        (ts-d-b) < (ts-b),
        (ts-d-a)-(ts-d-b) == b-a,
{
    barrier_identity(a,b,ts-d);
}

// T2. Explicit witness, independent of failure of an attempted general proof.
pub proof fn forward_improves_reverse_worsens_witness()
    ensures
        10-0 >= 0, 10-0 >= 0,
        8-0 >= 0, 8-(-5) >= 0,
        8-0 < 10-0,
        8-(-5) > 10-0,
{}

// M1. Ratios are represented by cross-multiplication, never integer division.
pub proof fn active_mass_capacity_bound(h: int, active: int, total: int)
    requires 0 <= h <= active, active <= total, total > 0,
    ensures 0 <= h, h <= active, h <= total,
{}

pub proof fn inert_mass_dilution(h: int, active: int, host: int)
    by (nonlinear_arith)
    requires h >= 0, active > 0, host >= 0,
    ensures
        active+host > 0,
        h*active <= h*(active+host),
        h > 0 && host > 0 ==> h*active < h*(active+host),
{}

// Observation non-injectivity in an explicitly abstract mixture model.
pub proof fn same_capacity_different_state_witness()
    ensures capacity(1,0) == capacity(0,4),
            capacity(1,0) == 4,
            1 != 0, 0 != 4,
{}

pub proof fn observation_has_multiple_states()
    ensures exists|x1: int, y1: int, x2: int, y2: int|
        x1 >= 0 && y1 >= 0 && x2 >= 0 && y2 >= 0
        && capacity(x1,y1) == capacity(x2,y2)
        && (x1 != x2 || y1 != y2),
{
    same_capacity_different_state_witness();
    assert(1 >= 0 && 0 >= 0 && 0 >= 0 && 4 >= 0
        && capacity(1,0) == capacity(0,4) && (1 != 0 || 0 != 4));
}

// M3. Coefficients count atoms; conservation is not reaction feasibility.
pub proof fn magnesium_borohydride_partition(n: int)
    requires n >= 0,
    ensures
        inventory(n,0,0,0,0) == inventory(0,n,2*n,3*n,0),
{}

pub proof fn magnesium_hydride_cycle_balance(n: int)
    requires n >= 0,
    ensures inventory(0,n,0,0,0) == inventory(0,0,0,n,n),
{}

// Independent exact counterexamples for every intentionally false control.
pub proof fn negative_control_witnesses()
    ensures
        (2-0)-(2-1) != 0-1,
        capacity(0,4) == 4 && !(0 == 1 && 4 == 0),
        stabilization(2,1,1) < stabilization(2,0,1),
        energy(1,1,2,1,1) < 0*norm2(1,1),
        1-0 > 0,                 // missing determinant permits false bound
{}

// Concrete satisfiable examples for the main conditional theorem families.
pub proof fn model_preconditions_have_witnesses()
    ensures
        3-2 > 0 && (3-2)*(4-2)-1*1 >= 0,
        1 <= 2 <= 2 && 0 <= 0 < 2 && 1 > 0,
        2 > 0 && 10-2 >= 0 && 10-2 >= 1,
        0 <= 1 <= 7 && 7 <= 10 && 10 > 0,
        1 >= 0 && 7 > 0 && 3 >= 0,
{}
}

fn main() {}
