use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::todd_coxeter::*;
use crate::finite::coset_table_complete;
use crate::completeness::*;
use crate::coset_group::*;
use crate::schreier::*;

verus! {

///  A group specified by carrier size, multiplication, inverse, and identity.
///  Elements are natural numbers in {0..carrier_size-1}.
pub struct GroupSpec {
    pub carrier_size: nat,
    pub mul: spec_fn(nat, nat) -> nat,
    pub inv: spec_fn(nat) -> nat,
    pub id: nat,
}

///  A GroupSpec satisfies the group axioms on {0..carrier_size-1}.
pub open spec fn group_axioms_valid(g: GroupSpec) -> bool {
    let n = g.carrier_size;
    //  Identity is in carrier
    &&& g.id < n
    //  Closure under multiplication
    &&& (forall|a: nat, b: nat| #![trigger (g.mul)(a, b)]
        a < n && b < n ==> (g.mul)(a, b) < n)
    //  Closure under inverse
    &&& (forall|a: nat| a < n ==> #[trigger] (g.inv)(a) < n)
    //  Associativity
    &&& (forall|a: nat, b: nat, c: nat| #![trigger (g.mul)((g.mul)(a, b), c)]
        a < n && b < n && c < n ==>
        (g.mul)((g.mul)(a, b), c) == (g.mul)(a, (g.mul)(b, c)))
    //  Left identity
    &&& (forall|a: nat| a < n ==> #[trigger] (g.mul)(g.id, a) == a)
    //  Right identity
    &&& (forall|a: nat| a < n ==> #[trigger] (g.mul)(a, g.id) == a)
    //  Left inverse
    &&& (forall|a: nat| a < n ==> (g.mul)(#[trigger] (g.inv)(a), a) == g.id)
    //  Right inverse
    &&& (forall|a: nat| #![trigger (g.inv)(a)]
        a < n ==> (g.mul)(a, (g.inv)(a)) == g.id)
}

///  Build a GroupSpec from a coset table.
///  Elements are coset indices, identity is coset 0.
pub open spec fn coset_group_spec(t: CosetTable, p: Presentation) -> GroupSpec {
    GroupSpec {
        carrier_size: t.num_cosets,
        mul: |a: nat, b: nat| coset_mul(t, a, b),
        inv: |a: nat| coset_inv(t, a),
        id: 0nat,
    }
}

//  ─── Helper lemmas ───────────────────────────────────────────────────────────

///  coset_mul result is in bounds.
proof fn lemma_coset_mul_in_bounds(t: CosetTable, a: nat, b: nat)
    requires
        coset_table_wf(t),
        coset_table_complete(t),
        a < t.num_cosets,
        coset_reachable(t, b),
    ensures
        coset_mul(t, a, b) < t.num_cosets,
{
    let w_b = coset_rep(t, b);
    //  coset_reachable → coset_rep has valid columns
    lemma_trace_complete(t, a, w_b);
}

///  coset_inv result is in bounds.
proof fn lemma_coset_inv_in_bounds(t: CosetTable, a: nat)
    requires
        coset_table_wf(t),
        coset_table_complete(t),
        t.num_cosets > 0,
        coset_reachable(t, a),
    ensures
        coset_inv(t, a) < t.num_cosets,
{
    let w_a = coset_rep(t, a);
    lemma_columns_to_word_valid(w_a, t.num_gens);
    crate::word::lemma_inverse_word_valid(w_a, t.num_gens);
    lemma_valid_word_columns(inverse_word(w_a), t.num_gens);
    lemma_trace_complete(t, 0, inverse_word(w_a));
}

//  ─── Main theorem ────────────────────────────────────────────────────────────

///  The coset group satisfies all group axioms.
pub proof fn lemma_coset_group_satisfies_axioms(t: CosetTable, p: Presentation)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        has_schreier_system(t, p),
        t.num_cosets > 0,
        all_cosets_reachable(t),
    ensures
        group_axioms_valid(coset_group_spec(t, p)),
{
    let g = coset_group_spec(t, p);
    let n = t.num_cosets;

    //  Identity in carrier
    assert(g.id == 0nat);
    assert(g.id < n);

    //  Closure under multiplication
    assert forall|a: nat, b: nat| #![trigger (g.mul)(a, b)]
        a < n && b < n
        implies (g.mul)(a, b) < n
    by {
        lemma_coset_mul_in_bounds(t, a, b);
    }

    //  Closure under inverse
    assert forall|a: nat| a < n
        implies #[trigger] (g.inv)(a) < n
    by {
        lemma_coset_inv_in_bounds(t, a);
    }

    //  Associativity
    assert forall|a: nat, b: nat, c: nat| #![trigger (g.mul)((g.mul)(a, b), c)]
        a < n && b < n && c < n
        implies (g.mul)((g.mul)(a, b), c) == (g.mul)(a, (g.mul)(b, c))
    by {
        lemma_coset_mul_in_bounds(t, b, c);
        let bc = coset_mul(t, b, c);
        assert(bc < n);
        assert(coset_reachable(t, bc));
        lemma_coset_mul_assoc(t, p, a, b, c);
    }

    //  Left identity
    assert forall|a: nat| a < n
        implies #[trigger] (g.mul)(g.id, a) == a
    by {
        lemma_coset_mul_identity_left(t, p, a);
    }

    //  Right identity
    lemma_coset_0_reachable(t);
    assert forall|a: nat| a < n
        implies #[trigger] (g.mul)(a, g.id) == a
    by {
        lemma_coset_0_reachable(t);
        lemma_coset_mul_identity_right(t, p, a);
    }

    //  Left inverse
    assert forall|a: nat| a < n
        implies (g.mul)(#[trigger] (g.inv)(a), a) == g.id
    by {
        lemma_coset_inv_in_bounds(t, a);
        let inv_a = coset_inv(t, a);
        assert(inv_a < n);
        assert(coset_reachable(t, inv_a));
        lemma_coset_inv_left(t, p, a);
    }

    //  Right inverse
    assert forall|a: nat| #![trigger (g.inv)(a)]
        a < n
        implies (g.mul)(a, (g.inv)(a)) == g.id
    by {
        lemma_coset_inv_in_bounds(t, a);
        let inv_a = coset_inv(t, a);
        assert(inv_a < n);
        assert(coset_reachable(t, inv_a));
        lemma_coset_inv_right(t, p, a);
    }
}

} //  verus!
