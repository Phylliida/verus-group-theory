use vstd::prelude::*;

verus! {

use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::todd_coxeter::*;
use crate::finite::coset_table_complete;
use crate::completeness::*;
use crate::coset_group::*;
use crate::runtime::*;

// ─── Word problem specs ─────────────────────────────────────────────────────

/// Two words are in the same coset iff they trace from 0 to the same coset.
pub open spec fn words_same_coset(t: CosetTable, w1: Word, w2: Word) -> bool {
    trace_word(t, 0 as nat, w1) == trace_word(t, 0 as nat, w2)
}

/// Completeness: equivalent words always map to the same coset.
pub open spec fn word_problem_complete(t: CosetTable, p: Presentation) -> bool {
    forall|w1: Word, w2: Word|
        equiv_in_presentation(p, w1, w2)
        && word_valid(w1, p.num_generators)
        && word_valid(w2, p.num_generators)
        ==> words_same_coset(t, w1, w2)
}

/// Soundness: words in the same coset are equivalent.
pub open spec fn word_problem_sound(t: CosetTable, p: Presentation) -> bool {
    forall|w1: Word, w2: Word|
        words_same_coset(t, w1, w2)
        && word_valid(w1, p.num_generators)
        && word_valid(w2, p.num_generators)
        ==> equiv_in_presentation(p, w1, w2)
}

// ─── Completeness lemma ─────────────────────────────────────────────────────

/// The coset table decision is complete: equivalent words trace to same coset.
pub proof fn lemma_word_problem_complete(t: CosetTable, p: Presentation)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        t.num_cosets > 0,
    ensures
        word_problem_complete(t, p),
{
    assert forall|w1: Word, w2: Word|
        equiv_in_presentation(p, w1, w2)
        && word_valid(w1, p.num_generators)
        && word_valid(w2, p.num_generators)
        implies words_same_coset(t, w1, w2)
    by {
        lemma_trace_respects_equiv(t, p, 0, w1, w2);
    }
}

// ─── Soundness lemma ────────────────────────────────────────────────────────

/// The coset table decision is sound: same-coset words are equivalent.
/// Relies on the soundness axiom (proof debt).
pub proof fn lemma_word_problem_sound(t: CosetTable, p: Presentation)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
    ensures
        word_problem_sound(t, p),
{
    assert forall|w1: Word, w2: Word|
        words_same_coset(t, w1, w2)
        && word_valid(w1, p.num_generators)
        && word_valid(w2, p.num_generators)
        implies equiv_in_presentation(p, w1, w2)
    by {
        axiom_coset_table_sound(t, p, w1, w2);
    }
}

// ─── Runtime: trace a word exec ──────────────────────────────────────────────

/// Trace a word through the runtime coset table, returning the final coset
/// or usize::MAX if an undefined entry is hit.
pub fn trace_word_exec(
    table: &RuntimeCosetTable,
    start: usize,
    w: &Vec<RuntimeSymbol>,
) -> (out: usize)
    requires
        start < table.num_cosets,
        table.num_cosets >= 1,
        table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
        table.table@.len() >= table.num_cosets * 2 * table.num_gens,
        table.num_gens > 0,
        forall|k: int| 0 <= k < w@.len() ==>
            symbol_to_column(runtime_symbol_view(w@[k])) < 2 * table.num_gens,
        forall|i: int| 0 <= i < table.table@.len() ==>
            table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets,
    ensures
        out == UNDEF() || out < table.num_cosets,
        out != UNDEF() ==>
            rt_trace_word(*table, start as nat,
                runtime_word_view(w@)) == Some(out as nat),
        out == UNDEF() ==>
            rt_trace_word(*table, start as nat,
                runtime_word_view(w@)) is None,
{
    // Reuse scan_relator_exec which does exactly this
    scan_relator_exec(table, start, w)
}

// ─── Runtime: decide word problem ────────────────────────────────────────────

/// Decide whether two words are equivalent at runtime.
/// Returns true iff both words trace from coset 0 to the same coset.
pub fn decide_word_problem_exec(
    table: &RuntimeCosetTable,
    w1: &Vec<RuntimeSymbol>,
    w2: &Vec<RuntimeSymbol>,
) -> (result: bool)
    requires
        table.num_cosets >= 1,
        table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
        table.table@.len() >= table.num_cosets * 2 * table.num_gens,
        table.num_gens > 0,
        forall|k: int| 0 <= k < w1@.len() ==>
            symbol_to_column(runtime_symbol_view(w1@[k])) < 2 * table.num_gens,
        forall|k: int| 0 <= k < w2@.len() ==>
            symbol_to_column(runtime_symbol_view(w2@[k])) < 2 * table.num_gens,
        forall|i: int| 0 <= i < table.table@.len() ==>
            table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets,
    ensures ({
        let spec_t = rt_to_spec_table(*table);
        let sw1 = runtime_word_view(w1@);
        let sw2 = runtime_word_view(w2@);
        // When the spec table is complete, result == words_same_coset(spec_t, sw1, sw2)
        result == (
            rt_trace_word(*table, 0 as nat, sw1)
            == rt_trace_word(*table, 0 as nat, sw2)
        )
    }),
{
    let c1 = trace_word_exec(table, 0, w1);
    let c2 = trace_word_exec(table, 0, w2);
    c1 == c2
}

// ─── Runtime: coset multiplication ───────────────────────────────────────────

/// Compute coset multiplication at runtime.
/// Given coset a and a word w_b representing coset b (i.e., trace(0, w_b) = b),
/// returns trace(a, w_b).
pub fn coset_mul_exec(
    table: &RuntimeCosetTable,
    a: usize,
    w_b: &Vec<RuntimeSymbol>,
) -> (result: usize)
    requires
        a < table.num_cosets,
        table.num_cosets >= 1,
        table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
        table.table@.len() >= table.num_cosets * 2 * table.num_gens,
        table.num_gens > 0,
        forall|k: int| 0 <= k < w_b@.len() ==>
            symbol_to_column(runtime_symbol_view(w_b@[k])) < 2 * table.num_gens,
        forall|i: int| 0 <= i < table.table@.len() ==>
            table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets,
    ensures
        result == UNDEF() || result < table.num_cosets,
        result != UNDEF() ==>
            rt_trace_word(*table, a as nat,
                runtime_word_view(w_b@)) == Some(result as nat),
        result == UNDEF() ==>
            rt_trace_word(*table, a as nat,
                runtime_word_view(w_b@)) is None,
{
    trace_word_exec(table, a, w_b)
}

} // verus!
