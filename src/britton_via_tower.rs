// Britton's Lemma via Tower Construction
//
// Translates HNN extension derivations to tower derivations.
// Faithful to Lyndon-Schupp Chapter IV: the tower unfolds the HNN extension
// by replacing the stable letter with explicit copies of the base group.
//
// Key insight: the HNN relator t⁻¹·a_i·t·inv(b_i) at level k corresponds
// exactly to the AFP identification relator shift(a_i, k·ng)·inv(shift(b_i, (k+1)·ng))
// at tower junction k↔k+1.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::hnn::*;
use crate::tower::*;

verus! {

// ============================================================
// Part A: Level tracking (textbook Lyndon-Schupp Ch. IV)
// ============================================================

/// Level at position j: cumulative count of Gen(ng) minus Inv(ng) in w[0..j).
/// This gives the "copy number" that the symbol at position j belongs to.
/// For a base word (no stable letters), level is always 0.
pub open spec fn level_at(data: HNNData, w: Word, j: int) -> int
    decreases j,
{
    let ng = data.base.num_generators;
    if j <= 0 {
        0
    } else if w[(j - 1) as int] == Symbol::Gen(ng) {
        level_at(data, w, j - 1) + 1
    } else if w[(j - 1) as int] == Symbol::Inv(ng) {
        level_at(data, w, j - 1) - 1
    } else {
        level_at(data, w, j - 1)
    }
}

/// Whether symbol s is the stable letter t or t⁻¹.
pub open spec fn is_stable(data: HNNData, s: Symbol) -> bool {
    let ng = data.base.num_generators;
    s == Symbol::Gen(ng) || s == Symbol::Inv(ng)
}

// ============================================================
// Part B: Word translation (textbook: strip stable letters, shift by level)
// ============================================================

/// Translate an HNN word to a tower word.
/// - Stable letters (t, t⁻¹) are REMOVED (they encode level changes, not generators)
/// - Base symbol Gen(i)/Inv(i) at level k becomes Gen(i + k·ng)/Inv(i + k·ng)
pub open spec fn translate_word(data: HNNData, w: Word) -> Word
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
        empty_word()
    } else {
        let s = w.first();
        let rest_translated = translate_word(data, w.drop_first());
        if is_stable(data, s) {
            rest_translated
        } else {
            let lev = level_at(data, w, 0);
            let shifted_s = match s {
                Symbol::Gen(i) => Symbol::Gen((i + lev * ng) as nat),
                Symbol::Inv(i) => Symbol::Inv((i + lev * ng) as nat),
            };
            concat(Seq::new(1, |_j: int| shifted_s), rest_translated)
        }
    }
}

// ============================================================
// Part C: Key lemma — base words translate to themselves
// ============================================================

/// For a base word (no stable letters), level is always 0.
proof fn lemma_base_word_level_zero(data: HNNData, w: Word, j: int)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        0 <= j <= w.len(),
    ensures
        level_at(data, w, j) == 0,
    decreases j,
{
    let ng = data.base.num_generators;
    if j <= 0 {
    } else {
        lemma_base_word_level_zero(data, w, j - 1);
        let s = w[(j - 1) as int];
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
    }
}

/// A base word translates to itself (identity translation).
pub proof fn lemma_translate_base_word(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        translate_word(data, w) =~= w,
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); assert(!is_stable(data, s)); }
            Symbol::Inv(i) => { assert(i < ng); assert(!is_stable(data, s)); }
        }
        lemma_base_word_level_zero(data, w, 0);
        assert(word_valid(w.drop_first(), ng));
        lemma_translate_base_word(data, w.drop_first());
    }
}

/// The empty word translates to the empty word.
pub proof fn lemma_translate_empty(data: HNNData)
    ensures
        translate_word(data, empty_word()) =~= empty_word(),
{
}

// ============================================================
// Part D: Derivation lifting — equiv in p1 → equiv in free_product(p1, p2)
// ============================================================

/// A single derivation step valid in p1 is also valid in free_product(p1, p2).
/// Proof: FreeReduce is word-only. FreeExpand uses more generators (OK since n1 ≤ n1+n2).
/// Relator insert/delete: p1.relators are a prefix of fp.relators.
proof fn lemma_step_valid_in_fp_left(
    p1: Presentation, p2: Presentation,
    w: Word, step: DerivationStep,
)
    requires
        apply_step(p1, w, step) is Some,
    ensures
        apply_step(free_product(p1, p2), w, step) == apply_step(p1, w, step),
{
    let fp = free_product(p1, p2);
    let n1 = p1.num_generators;
    match step {
        DerivationStep::FreeReduce { position } => {
            // has_cancellation_at is word-only, same in both
        },
        DerivationStep::FreeExpand { position, symbol } => {
            // symbol_valid(s, n1) → symbol_valid(s, n1+n2)
            assert(symbol_valid(symbol, fp.num_generators)) by {
                match symbol {
                    Symbol::Gen(i) => {}
                    Symbol::Inv(i) => {}
                }
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            // p1.relators[idx] == fp.relators[idx] for idx < p1.relators.len()
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
            assert(get_relator(fp, relator_index, inverted)
                == get_relator(p1, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
            assert(get_relator(fp, relator_index, inverted)
                == get_relator(p1, relator_index, inverted));
        },
    }
}

/// A full derivation valid in p1 is also valid in free_product(p1, p2).
proof fn lemma_derivation_valid_in_fp_left(
    p1: Presentation, p2: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(p1, steps, w1) == Some(w2),
    ensures
        derivation_produces(free_product(p1, p2), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let w_mid = apply_step(p1, w1, steps.first()).unwrap();
        lemma_step_valid_in_fp_left(p1, p2, w1, steps.first());
        lemma_derivation_valid_in_fp_left(p1, p2, steps.drop_first(), w_mid, w2);
    }
}

/// Equivalence in p1 implies equivalence in free_product(p1, p2).
pub proof fn lemma_left_embeds_in_fp(
    p1: Presentation, p2: Presentation, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(p1, w1, w2),
    ensures
        equiv_in_presentation(free_product(p1, p2), w1, w2),
{
    let d: Derivation = choose|d: Derivation| derivation_valid(p1, d, w1, w2);
    lemma_derivation_valid_in_fp_left(p1, p2, d.steps, w1, w2);
    // Witness for the existential in equiv_in_presentation
    let d_fp = Derivation { steps: d.steps };
    assert(derivation_valid(free_product(p1, p2), d_fp, w1, w2));
}

/// Equivalence in tower(k) implies equivalence in tower(m) for k ≤ m.
/// Proof by induction: tower(m) = AFP(tower(m-1), base) extends tower(m-1) via free product + add_relators.
pub proof fn lemma_tower_monotone(
    data: HNNData, k: nat, m: nat, w1: Word, w2: Word,
)
    requires
        hnn_data_valid(data),
        k <= m,
        equiv_in_presentation(tower_presentation(data, k), w1, w2),
    ensures
        equiv_in_presentation(tower_presentation(data, m), w1, w2),
    decreases m - k,
{
    if k == m {
    } else {
        // tower(k+1) = AFP(tower_afp_data(k)) = add_relators(fp(tower(k), base), ident_relators)
        // Step 1: lift from tower(k) to fp(tower(k), base)
        let afp_data = tower_afp_data(data, k);
        lemma_left_embeds_in_fp(afp_data.p1, afp_data.p2, w1, w2);
        // Step 2: lift from fp to tower(k+1) via add_relators
        crate::quotient::lemma_add_relators_preserves_equiv(
            free_product(afp_data.p1, afp_data.p2),
            amalgamation_relators(afp_data),
            w1, w2);
        // Now have: equiv in tower(k+1)
        // Step 3: recurse to reach tower(m)
        lemma_tower_monotone(data, k + 1, m, w1, w2);
    }
}

// ============================================================
// Part E: Tower relator correspondence
// ============================================================

/// A base relator at copy k is equiv to ε in tower(m) when k ≤ m.
pub proof fn lemma_base_relator_in_tower(
    data: HNNData, m: nat, k: nat, r: int,
)
    requires
        hnn_data_valid(data),
        k <= m,
        0 <= r < data.base.relators.len(),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            shift_word(data.base.relators[r], k * data.base.num_generators),
            empty_word()),
    decreases m,
{
    let ng = data.base.num_generators;
    if k == 0 && m == 0 {
        // tower(0) = base, shift by 0 = identity
        assert(shift_word(data.base.relators[r], 0) =~= data.base.relators[r]);
        lemma_relator_is_identity(data.base, r);
    } else if k < m {
        // Relator is in tower(prev) ⊂ tower(m) via monotonicity
        if k == 0 {
            // Base relator at copy 0 in tower(1): use base ⊂ tower(1)
            assert(shift_word(data.base.relators[r], 0) =~= data.base.relators[r]);
            lemma_relator_is_identity(data.base, r);
            lemma_tower_monotone(data, 0, m, data.base.relators[r], empty_word());
        } else {
            lemma_base_relator_in_tower(data, (m - 1) as nat, k, r);
            lemma_tower_monotone(data, (m - 1) as nat, m,
                shift_word(data.base.relators[r], k * ng), empty_word());
        }
    } else {
        // k == m > 0: relator is in the NEW copy (right factor of the AFP at level m)
        let prev = (m - 1) as nat;
        let afp_data = tower_afp_data(data, prev);
        // In free_product(tower(prev), base): base relators are shifted by tower(prev).num_generators
        // tower(prev).num_generators = m * ng (from lemma_tower_num_generators)
        lemma_tower_num_generators(data, prev);
        assert(afp_data.p1.num_generators == m * ng);
        // shift_relators(base.relators, m*ng)[r] = shift_word(base.relators[r], m*ng)
        // This is a relator of free_product(tower(prev), base) at the right offset
        // fp.relators = tower(prev).relators + shift_relators(base.relators, m*ng)
        let fp = free_product(afp_data.p1, afp_data.p2);
        let fp_idx = (afp_data.p1.relators.len() + r) as nat;
        assert(fp.relators[fp_idx as int]
            == shift_word(data.base.relators[r], m * ng));
        lemma_relator_is_identity(fp, fp_idx as int);
        // Lift from fp to tower(m) = add_relators(fp, ident_relators)
        crate::quotient::lemma_add_relators_preserves_equiv(
            fp, amalgamation_relators(afp_data),
            shift_word(data.base.relators[r], m * ng), empty_word());
    }
}

/// An identification relator at junction k↔k+1 is equiv to ε in tower(m) when k+1 ≤ m.
pub proof fn lemma_ident_relator_in_tower(
    data: HNNData, m: nat, k: nat, i: int,
)
    requires
        hnn_data_valid(data),
        k + 1 <= m,
        0 <= i < data.associations.len() as int,
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            amalgamation_relator(tower_afp_data(data, k), i),
            empty_word()),
    decreases m,
{
    let prev = (m - 1) as nat;
    let afp_data = tower_afp_data(data, prev);
    let fp = free_product(afp_data.p1, afp_data.p2);

    if k == prev {
        // Junction k = m-1: identification relator added directly at level m
        crate::quotient::lemma_each_added_relator_is_identity(
            fp, amalgamation_relators(afp_data), i);
    } else {
        // k < prev: relator is in tower(prev) ⊂ tower(m)
        lemma_ident_relator_in_tower(data, prev, k, i);
        lemma_tower_monotone(data, prev, m,
            amalgamation_relator(tower_afp_data(data, k), i), empty_word());
    }
}

} // verus!
