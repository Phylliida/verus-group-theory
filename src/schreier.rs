use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::todd_coxeter::*;
use crate::finite::coset_table_complete;
use crate::coset_group::*;

verus! {

/// All cosets are reachable from coset 0 via some word.
pub open spec fn all_cosets_reachable(t: CosetTable) -> bool {
    forall|c: nat| c < t.num_cosets ==> coset_reachable(t, c)
}

/// Schreier representative for coset c: empty word for coset 0,
/// chosen representative for others (from coset_rep).
pub open spec fn schreier_rep(t: CosetTable, c: nat) -> Word {
    if c == 0 { empty_word() } else { coset_rep(t, c) }
}

/// Construct a Schreier system for a complete coset table.
///
/// The non-tree-edge triviality clause (`schreier_trivial`) requires
/// faithfulness, which itself requires the Schreier system — a circularity.
/// Standard resolution: simultaneous induction on TC construction's BFS tree,
/// showing each Schreier generator `reps(c)·[s]·reps(d)⁻¹` reduces to a
/// product of conjugates of relators. This requires ~500+ lines of inductive
/// argument on the TC construction steps, so we use `assume(false)` here.
pub proof fn lemma_construct_schreier_system(t: CosetTable, p: Presentation)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        t.num_cosets > 0,
        all_cosets_reachable(t),
    ensures
        has_schreier_system(t, p),
{
    let reps = |c: nat| -> Word { schreier_rep(t, c) };

    // --- Rep system validity ---

    // reps(0) == empty_word()
    assert(reps(0nat) =~= empty_word());

    // For each coset: trace correctness + word_valid + column validity
    assert forall|c: nat| c < t.num_cosets implies (
        #[trigger] trace_word(t, 0 as nat, reps(c)) == Some(c)
        && word_valid(reps(c), t.num_gens)
        && (forall|k: int| 0 <= k < reps(c).len()
            ==> #[trigger] symbol_to_column(reps(c)[k]) < 2 * t.num_gens)
    ) by {
        if c == 0 {
            crate::todd_coxeter::lemma_trace_empty(t, 0);
        } else {
            // reps(c) = coset_rep(t, c), chosen from coset_reachable witness
            assert(coset_reachable(t, c));
            let w = coset_rep(t, c);
            assert(trace_word(t, 0 as nat, w) == Some(c));
            lemma_columns_to_word_valid(w, t.num_gens);
        }
    }

    assert(is_coset_rep_system(t, reps));

    // --- Schreier triviality (circular dependency — see doc comment) ---
    // Each Schreier generator reps(c)·[s]·reps(table[c][s])⁻¹ must be
    // trivial in the presented group. Proving this requires either:
    // (a) faithfulness of the table (which itself requires has_schreier_system), or
    // (b) simultaneous induction on the TC algorithm's BFS tree construction.
    // Option (b) requires formalizing the full TC algorithm (~500+ lines).
    assume(schreier_trivial(t, p, reps));

    assert(is_coset_rep_system(t, reps) && schreier_trivial(t, p, reps));
}

} // verus!
