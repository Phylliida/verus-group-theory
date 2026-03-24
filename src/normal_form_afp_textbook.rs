// Textbook AFP injectivity via reduced sequences (Lyndon-Schupp Ch. IV).
//
// Phase 1: Definitions only. All spec fns, no proof obligations.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::normal_form_amalgamated::{
    in_left_subgroup, in_right_subgroup,
    same_left_coset, same_right_coset,
    unshift_sym,
};
use crate::benign::*;
use crate::shortlex::*;

verus! {

// ============================================================
// Part A: Helpers
// ============================================================

/// The K-word generators for the left factor (u_i words).
pub open spec fn a_words(data: AmalgamatedData) -> Seq<Word> {
    Seq::new(data.identifications.len(), |i: int| data.identifications[i].0)
}

/// The K-word generators for the right factor (v_i words).
pub open spec fn b_words(data: AmalgamatedData) -> Seq<Word> {
    Seq::new(data.identifications.len(), |i: int| data.identifications[i].1)
}

/// Number of identification generators.
pub open spec fn k_size(data: AmalgamatedData) -> nat {
    data.identifications.len() as nat
}

// ============================================================
// Part B: Shortlex-canonical coset representatives
// ============================================================

/// Shortlex-minimum word in the left A-coset of g.
/// This is the canonical coset representative: same coset → same rep.
pub open spec fn left_canonical_rep(data: AmalgamatedData, g: Word) -> Word {
    choose|rep: Word|
        word_valid(rep, data.p1.num_generators)
        && same_left_coset(data, g, rep)
        && (forall|rep2: Word|
            word_valid(rep2, data.p1.num_generators)
            && same_left_coset(data, g, rep2)
            ==> !shortlex_lt(rep2, rep))
}

/// The subgroup part: a K-word h such that g ≡ concat(rep, embed_a(h)) in G₁.
pub open spec fn left_h_part(data: AmalgamatedData, g: Word) -> Word {
    choose|h: Word|
        word_valid(h, k_size(data))
        && equiv_in_presentation(data.p1,
            g,
            concat(left_canonical_rep(data, g), apply_embedding(a_words(data), h)))
}

/// Shortlex-minimum word in the right B-coset of g.
pub open spec fn right_canonical_rep(data: AmalgamatedData, g: Word) -> Word {
    choose|rep: Word|
        word_valid(rep, data.p2.num_generators)
        && same_right_coset(data, g, rep)
        && (forall|rep2: Word|
            word_valid(rep2, data.p2.num_generators)
            && same_right_coset(data, g, rep2)
            ==> !shortlex_lt(rep2, rep))
}

/// The subgroup part for G₂.
pub open spec fn right_h_part(data: AmalgamatedData, g: Word) -> Word {
    choose|h: Word|
        word_valid(h, k_size(data))
        && equiv_in_presentation(data.p2,
            g,
            concat(right_canonical_rep(data, g), apply_embedding(b_words(data), h)))
}

// ============================================================
// Part B2: Well-ordering and transversal existence
// ============================================================

/// Well-ordering principle for nats: any inhabited predicate has a minimum.
proof fn lemma_nat_well_ordering(p: spec_fn(nat) -> bool, bound: nat)
    requires
        p(bound),
    ensures
        exists|m: nat| m <= bound && p(m) && (forall|k: nat| k < m ==> !p(k)),
    decreases bound,
{
    if bound == 0 {
        // p(0) holds, and there's no k < 0
    } else {
        if exists|k: nat| k < bound && p(k) {
            let smaller: nat = choose|k: nat| k < bound && p(k);
            lemma_nat_well_ordering(p, smaller);
        } else {
            // No k < bound with p(k), so bound is the minimum
        }
    }
}

/// The minimum length of any valid word in the same left coset as g.
/// Well-defined because g.len() is an upper bound and min over nats exists.
pub open spec fn min_coset_length_left(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat|
        (exists|w: Word| word_valid(w, data.p1.num_generators)
            && same_left_coset(data, g, w)
            && w.len() == l)
        && (forall|w2: Word| word_valid(w2, data.p1.num_generators)
            && same_left_coset(data, g, w2) ==> w2.len() >= l)
}

/// The generated subgroup is closed under equivalence.
proof fn lemma_in_subgroup_equiv(
    p: Presentation, gens: Seq<Word>, w1: Word, w2: Word,
)
    requires
        in_generated_subgroup(p, gens, w1),
        equiv_in_presentation(p, w1, w2),
    ensures
        in_generated_subgroup(p, gens, w2),
{
    // w1 is in subgroup: exists factors with concat_all(factors) ≡ w1
    // w1 ≡ w2, so by transitivity: concat_all(factors) ≡ w2
    let factors: Seq<Word> = choose|factors: Seq<Word>|
        #[trigger] factors_from_generators(gens, factors)
        && equiv_in_presentation(p, concat_all(factors), w1);
    crate::presentation::lemma_equiv_transitive(
        p, concat_all(factors), w1, w2);
}

/// The left coset of g contains g itself (reflexivity).
proof fn lemma_same_left_coset_reflexive(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        same_left_coset(data, g, g),
{
    let inv_g = inverse_word(g);
    let product = concat(inv_g, g);
    let p1 = data.p1;
    let n1 = p1.num_generators;
    // concat(inv(g), g) ≡ ε in G₁
    crate::presentation_lemmas::lemma_word_inverse_left(p1, g);
    // ε is in the generated subgroup
    crate::benign::lemma_identity_in_generated_subgroup(p1, a_words(data));
    // We need: in_generated_subgroup(p1, a_words, product)
    // = in_generated_subgroup(p1, a_words, concat(inv(g), g))
    // From: ε ≡ product, and ε is in the subgroup
    // Need symmetry: product ≡ ε => ε ≡ product (for equiv closure)
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(g, n1);
    crate::word::lemma_concat_word_valid(inv_g, g, n1);
    // product is word_valid
    // Now get: equiv(ε, product) from equiv(product, ε) + symmetry
    // Actually equiv(product, ε) is what lemma_word_inverse_left gives.
    // For subgroup closure we need: in_subgroup(ε) && equiv(ε, product) => in_subgroup(product)
    // lemma_equiv_symmetric gives equiv(ε, product) from equiv(product, ε)
    crate::presentation::lemma_equiv_symmetric(p1, product, empty_word());
    lemma_in_subgroup_equiv(p1, a_words(data), empty_word(), product);
}

// ============================================================
// Part C: Syllable type and reduced state
// ============================================================

/// A syllable: a non-trivial coset representative from one factor.
pub struct Syllable {
    pub is_left: bool,
    pub rep: Word,
}

/// Well-formed reduced state.
pub open spec fn state_valid(data: AmalgamatedData, h: Word, syllables: Seq<Syllable>) -> bool {
    let k = k_size(data);
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;

    &&& word_valid(h, k)
    &&& (forall|i: int| 0 <= i < syllables.len() - 1 ==>
        (#[trigger] syllables[i]).is_left != (#[trigger] syllables[i + 1]).is_left)
    &&& (forall|i: int| 0 <= i < syllables.len() ==> ({
        let syl = #[trigger] syllables[i];
        if syl.is_left {
            word_valid(syl.rep, n1) && !(syl.rep =~= empty_word())
            && !in_left_subgroup(data, syl.rep)
        } else {
            word_valid(syl.rep, n2) && !(syl.rep =~= empty_word())
            && !in_right_subgroup(data, syl.rep)
        }
    }))
}

// ============================================================
// Part D: Single-symbol action
// ============================================================

/// Apply a single G₁ symbol to the state.
/// product = concat([s], embed_a(h)) in G₁
/// Decompose: new_rep = left_canonical_rep(product), new_h = left_h_part(product)
/// Then handle syllable structure.
pub open spec fn act_left_sym(
    data: AmalgamatedData,
    s: Symbol,  // a G₁ symbol (gen_index < n1)
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
    let new_h = left_h_part(data, product);
    let new_rep = left_canonical_rep(data, product);

    if new_rep =~= empty_word() {
        // Product is in the subgroup
        (new_h, syllables)
    } else if syllables.len() == 0 || !syllables.first().is_left {
        // Prepend new left syllable (different factor or empty)
        (new_h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: new_rep }) + syllables)
    } else {
        // Merge: first syllable is also left
        let merged = concat(new_rep, syllables.first().rep);
        let merged_h = left_h_part(data, merged);
        let merged_rep = left_canonical_rep(data, merged);
        let combined_h = concat(merged_h, new_h);

        if merged_rep =~= empty_word() {
            // Merge absorbed into subgroup
            (combined_h, syllables.drop_first())
        } else {
            // Replace first syllable
            (combined_h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep })
                + syllables.drop_first())
        }
    }
}

/// Apply a single G₂ symbol to the state. Symmetric to left.
pub open spec fn act_right_sym(
    data: AmalgamatedData,
    s: Symbol,  // a G₂ symbol (local, already unshifted)
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let new_h = right_h_part(data, product);
    let new_rep = right_canonical_rep(data, product);

    if new_rep =~= empty_word() {
        (new_h, syllables)
    } else if syllables.len() == 0 || syllables.first().is_left {
        (new_h, Seq::new(1, |_i: int| Syllable { is_left: false, rep: new_rep }) + syllables)
    } else {
        let merged = concat(new_rep, syllables.first().rep);
        let merged_h = right_h_part(data, merged);
        let merged_rep = right_canonical_rep(data, merged);
        let combined_h = concat(merged_h, new_h);

        if merged_rep =~= empty_word() {
            (combined_h, syllables.drop_first())
        } else {
            (combined_h, Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
                + syllables.drop_first())
        }
    }
}

/// Apply an AFP symbol to the state. Dispatches to left or right.
pub open spec fn act_sym(
    data: AmalgamatedData,
    s: Symbol,  // AFP symbol (gen_index < n1+n2)
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let n1 = data.p1.num_generators;
    if generator_index(s) < n1 {
        act_left_sym(data, s, h, syllables)
    } else {
        act_right_sym(data, unshift_sym(s, n1), h, syllables)
    }
}

/// Apply an AFP word to the state (left-to-right, one symbol at a time).
pub open spec fn act_word(
    data: AmalgamatedData,
    w: Word,
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>)
    decreases w.len(),
{
    if w.len() == 0 {
        (h, syllables)
    } else {
        let (new_h, new_syls) = act_sym(data, w.first(), h, syllables);
        act_word(data, w.drop_first(), new_h, new_syls)
    }
}

} // verus!
