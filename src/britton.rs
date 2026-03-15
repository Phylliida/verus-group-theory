use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;

verus! {

// ============================================================
// Britton's Lemma (HNN Injectivity)
// ============================================================
//
// Britton's Lemma is the fundamental injectivity theorem for HNN extensions:
//
//   If w is a word using only base generators, and w ≡ ε in the HNN
//   extension G*, then w ≡ ε in the base group G.
//
// Equivalently: the natural inclusion G → G* is injective.
//
// This is the most technically demanding single theorem in combinatorial
// group theory. The full proof requires analyzing derivation sequences
// and showing that stable letters can always be eliminated from
// derivations between base words.

// ============================================================
// Stable letter analysis
// ============================================================

/// Count the number of stable letter symbols in a word.
/// Counts both Gen(n) and Inv(n) where n = data.base.num_generators.
pub open spec fn stable_letter_count(w: Word, n: nat) -> nat
    decreases w.len(),
{
    if w.len() == 0 {
        0
    } else {
        let rest_count = stable_letter_count(w.drop_first(), n);
        if generator_index(w.first()) == n {
            rest_count + 1
        } else {
            rest_count
        }
    }
}

/// A word is a "base word" if it contains no stable letters.
pub open spec fn is_base_word(w: Word, n: nat) -> bool {
    stable_letter_count(w, n) == 0
}

/// A word using only base generators (word_valid for base) is a base word.
pub proof fn lemma_base_word_characterization(w: Word, n: nat)
    requires
        word_valid(w, n),
    ensures
        is_base_word(w, n),
    decreases w.len(),
{
    if w.len() > 0 {
        let rest = w.drop_first();
        assert(word_valid(rest, n)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies symbol_valid(#[trigger] rest[i], n)
            by {
                assert(rest[i] == w[i + 1]);
            }
        }
        lemma_base_word_characterization(rest, n);
        assert(symbol_valid(w.first(), n));
        assert(generator_index(w.first()) < n);
    }
}

/// A base word that is word_valid for n+1 generators is word_valid for n generators.
/// (Combines: no stable letters at index n + all indices < n+1 → all indices < n.)
pub proof fn lemma_base_word_valid_downgrade(w: Word, n: nat)
    requires
        is_base_word(w, n),
        word_valid(w, n + 1),
    ensures
        word_valid(w, n),
    decreases w.len(),
{
    if w.len() > 0 {
        let rest = w.drop_first();

        // First symbol has index < n+1 and index != n, so index < n
        assert(symbol_valid(w.first(), n + 1));
        assert(generator_index(w.first()) < n + 1);
        if generator_index(w.first()) == n {
            assert(stable_letter_count(w, n) >= 1);
            assert(false);
        }
        assert(generator_index(w.first()) < n);
        assert(symbol_valid(w.first(), n));

        // Rest is also base word and valid for n+1
        assert(stable_letter_count(w, n) == stable_letter_count(rest, n));
        assert(is_base_word(rest, n));
        assert(word_valid(rest, n + 1)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies symbol_valid(#[trigger] rest[i], n + 1)
            by {
                assert(rest[i] == w[i + 1]);
            }
        }
        lemma_base_word_valid_downgrade(rest, n);

        // Combine: first symbol valid + rest valid → whole word valid
        assert forall|i: int| 0 <= i < w.len()
            implies symbol_valid(#[trigger] w[i], n)
        by {
            if i == 0 {
            } else {
                assert(w[i] == rest[i - 1]);
            }
        }
    }
}

/// The empty word is a base word.
pub proof fn lemma_empty_is_base_word(n: nat)
    ensures
        is_base_word(empty_word(), n),
{
}

// ============================================================
// Britton's Lemma — Axiom
// ============================================================
//
// The full algebraic proof of Britton's Lemma involves:
// 1. Defining the "t-length" of intermediate words in a derivation
// 2. Showing each step changes t-count by at most 2
// 3. A "peak analysis" argument: if a derivation introduces then
//    removes stable letters, the segment can be simplified
// 4. Induction on the total t-exposure of the derivation
//
// This proof is deferred. The axiom is strictly weaker than
// axiom_higman_embedding and is a standard theorem in
// combinatorial group theory.

/// Britton's Lemma: if a base word is trivial in the HNN extension,
/// it is trivial in the base group.
///
/// Equivalently: the natural inclusion G → G* = ⟨G, t | t⁻¹aᵢt = bᵢ⟩
/// is injective (on the group level).
#[verifier::external_body]
pub proof fn axiom_britton_lemma(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
}

// ============================================================
// Derived forms
// ============================================================

/// Britton's Lemma (equivalence form): if two base words are equivalent
/// in the HNN extension, they are equivalent in the base group.
pub proof fn lemma_hnn_injective(data: HNNData, w1: Word, w2: Word)
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators),
        word_valid(w2, data.base.num_generators),
        presentation_valid(data.base),
        equiv_in_presentation(hnn_presentation(data), w1, w2),
    ensures
        equiv_in_presentation(data.base, w1, w2),
{
    let hp = hnn_presentation(data);
    let bp = data.base;
    let n = bp.num_generators;

    // w1 ≡ w2 in G* implies w1 · w2⁻¹ ≡ ε in G*
    // Proof: w1 ≡ w2 → w1 · w2⁻¹ ≡ w2 · w2⁻¹ ≡ ε
    lemma_equiv_concat_left(hp, w1, w2, inverse_word(w2));
    lemma_word_inverse_right(hp, w2);
    lemma_equiv_transitive(hp, concat(w1, inverse_word(w2)), concat(w2, inverse_word(w2)), empty_word());

    // w1 · w2⁻¹ is a base word (word_valid for base)
    lemma_inverse_word_valid(w2, n);
    lemma_concat_word_valid(w1, inverse_word(w2), n);

    // Apply Britton's Lemma: w1 · w2⁻¹ ≡ ε in G
    axiom_britton_lemma(data, concat(w1, inverse_word(w2)));

    // w1 · w2⁻¹ ≡ ε in G → w1 ≡ w2 in G
    // Proof: w1 · w2⁻¹ ≡ ε → w1 · w2⁻¹ · w2 ≡ w2 → w1 · ε ≡ w2... no, simpler:
    // w1 · w2⁻¹ ≡ ε
    // w1 · w2⁻¹ · w2 ≡ ε · w2 = w2
    lemma_equiv_concat_left(bp, concat(w1, inverse_word(w2)), empty_word(), w2);
    assert(concat(empty_word(), w2) =~= w2);
    lemma_equiv_refl(bp, w2);
    lemma_equiv_transitive(bp, concat(concat(w1, inverse_word(w2)), w2), concat(empty_word(), w2), w2);

    // w1 · (w2⁻¹ · w2) = (w1 · w2⁻¹) · w2 by assoc
    assert(concat(concat(w1, inverse_word(w2)), w2) =~= concat(w1, concat(inverse_word(w2), w2)));

    // w2⁻¹ · w2 ≡ ε
    lemma_word_inverse_left(bp, w2);

    // w1 · (w2⁻¹ · w2) ≡ w1 · ε = w1
    lemma_equiv_concat_right(bp, w1, concat(inverse_word(w2), w2), empty_word());
    assert(concat(w1, empty_word()) =~= w1);
    lemma_equiv_refl(bp, w1);
    lemma_equiv_transitive(bp, concat(w1, concat(inverse_word(w2), w2)), concat(w1, empty_word()), w1);

    // word_valid needed for symmetric
    lemma_concat_word_valid(w1, concat(inverse_word(w2), w2), n);

    // Chain: w1 ≡ w1 · (w2⁻¹ · w2) = (w1 · w2⁻¹) · w2 ≡ w2
    lemma_equiv_symmetric(bp, concat(w1, concat(inverse_word(w2), w2)), w1);
    lemma_equiv_transitive(bp, w1, concat(w1, concat(inverse_word(w2), w2)), w2);
}

/// Britton's Lemma (contrapositive form): if two base words are
/// NOT equivalent in the base group, they are NOT equivalent in the HNN extension.
pub proof fn lemma_hnn_separates(data: HNNData, w1: Word, w2: Word)
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators),
        word_valid(w2, data.base.num_generators),
        presentation_valid(data.base),
        !equiv_in_presentation(data.base, w1, w2),
    ensures
        !equiv_in_presentation(hnn_presentation(data), w1, w2),
{
    // Contrapositive of lemma_hnn_injective
    if equiv_in_presentation(hnn_presentation(data), w1, w2) {
        lemma_hnn_injective(data, w1, w2);
        assert(false);
    }
}

} // verus!
