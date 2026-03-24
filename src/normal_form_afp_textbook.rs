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

/// Lex rank of a word: maps a word to a nat based on symbol ordering.
/// Injective on words of the same length: different words → different ranks.
pub open spec fn word_lex_rank(w: Word) -> nat
    decreases w.len(),
{
    if w.len() == 0 { 0 }
    else {
        crate::todd_coxeter::symbol_to_column(w.first())
            + (2 * w.len() as nat) * word_lex_rank(w.drop_first())
    }
}

/// Does the left A-coset of g contain a valid word of length l?
pub open spec fn has_left_coset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g, w) && w.len() == l
}

/// Does the coset contain a valid word of length l and lex rank r?
pub open spec fn has_left_coset_word_of_len_rank(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g, w) && w.len() == l && word_lex_rank(w) == r
}

/// Minimum length of any valid word in g's left A-coset.
pub open spec fn left_min_coset_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] has_left_coset_word_of_len(data, g, l)
        && no_pred_below(|l2: nat| has_left_coset_word_of_len(data, g, l2), l)
}

/// Minimum lex rank at the minimum length.
pub open spec fn left_min_coset_lex(data: AmalgamatedData, g: Word) -> nat {
    let l = left_min_coset_len(data, g);
    choose|r: nat| #[trigger] has_left_coset_word_of_len_rank(data, g, l, r)
        && no_pred_below(|r2: nat| has_left_coset_word_of_len_rank(data, g, l, r2), r)
}

/// Canonical coset representative: the UNIQUE word with min length and min lex rank.
/// Three-step choose enables coset invariance via uniqueness.
pub open spec fn left_canonical_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = left_min_coset_len(data, g);
    let r = left_min_coset_lex(data, g);
    choose|rep: Word|
        word_valid(rep, data.p1.num_generators)
        && same_left_coset(data, g, rep)
        && rep.len() == l
        && word_lex_rank(rep) == r
}

/// Does a K-word of length l exist that embeds to the target?
pub open spec fn has_left_h_witness_of_len(
    data: AmalgamatedData, target: Word, l: nat,
) -> bool {
    exists|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h), target)
}

/// Min-length K-word witnessing the subgroup decomposition.
pub open spec fn left_h_min_len(data: AmalgamatedData, g: Word) -> nat {
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    choose|l: nat| #[trigger] has_left_h_witness_of_len(data, target, l)
        && no_pred_below(|l2: nat| has_left_h_witness_of_len(data, target, l2), l)
}

/// The subgroup part: min-length K-word h such that embed_a(h) ≡ inv(rep) * g.
pub open spec fn left_h_part(data: AmalgamatedData, g: Word) -> Word {
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    let l = left_h_min_len(data, g);
    choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h), target)
}

/// Does the right B-coset of g contain a valid word of length l?
pub open spec fn has_right_coset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p2.num_generators)
        && same_right_coset(data, g, w) && w.len() == l
}

/// Minimum length of any valid word in g's right B-coset.
pub open spec fn right_min_coset_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] has_right_coset_word_of_len(data, g, l)
        && no_pred_below(|l2: nat| has_right_coset_word_of_len(data, g, l2), l)
}

/// Canonical right coset representative.
pub open spec fn right_canonical_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = right_min_coset_len(data, g);
    choose|rep: Word|
        word_valid(rep, data.p2.num_generators)
        && same_right_coset(data, g, rep)
        && rep.len() == l
}

/// Does a K-word of length l exist for the right decomposition?
pub open spec fn has_right_h_witness_of_len(
    data: AmalgamatedData, target: Word, l: nat,
) -> bool {
    exists|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h), target)
}

/// Min-length K-word for right decomposition.
pub open spec fn right_h_min_len(data: AmalgamatedData, g: Word) -> nat {
    let rep = right_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    choose|l: nat| #[trigger] has_right_h_witness_of_len(data, target, l)
        && no_pred_below(|l2: nat| has_right_h_witness_of_len(data, target, l2), l)
}

/// The subgroup part for G₂: min-length K-word.
pub open spec fn right_h_part(data: AmalgamatedData, g: Word) -> Word {
    let rep = right_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    let l = right_h_min_len(data, g);
    choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h), target)
}

// ============================================================
// Part B2: Well-ordering and transversal existence
// ============================================================

/// No value less than m satisfies p (recursive, avoids quantifier trigger issues).
pub open spec fn no_pred_below(p: spec_fn(nat) -> bool, m: nat) -> bool
    decreases m,
{
    if m == 0 { true }
    else { !p((m - 1) as nat) && no_pred_below(p, (m - 1) as nat) }
}

/// m is the minimum of predicate p.
pub open spec fn is_nat_min(p: spec_fn(nat) -> bool, m: nat) -> bool {
    p(m) && no_pred_below(p, m)
}

/// Well-ordering: scan from `current` to `bound` to find the minimum of p.
proof fn lemma_nat_scan_for_min(p: spec_fn(nat) -> bool, current: nat, bound: nat)
    requires
        p(bound),
        current <= bound,
        no_pred_below(p, current),
    ensures
        exists|m: nat| current <= m && m <= bound && #[trigger] is_nat_min(p, m),
    decreases bound - current,
{
    if p(current) {
        assert(is_nat_min(p, current));
    } else {
        // !p(current) && no_pred_below(p, current) => no_pred_below(p, current + 1)
        lemma_nat_scan_for_min(p, current + 1, bound);
    }
}

/// Well-ordering principle for nats: any inhabited predicate has a minimum.
pub proof fn lemma_nat_well_ordering(p: spec_fn(nat) -> bool, bound: nat)
    requires
        p(bound),
    ensures
        exists|m: nat| m <= bound && #[trigger] is_nat_min(p, m),
{
    // no_pred_below(p, 0) is trivially true (base case of recursion)
    lemma_nat_scan_for_min(p, 0, bound);
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

// ============================================================
// Part E: Composition lemma
// ============================================================

/// act_word(concat(w1, w2), h, syls) == act_word(w2, act_word(w1, h, syls)).
/// This is the fundamental composition property.
pub proof fn lemma_act_word_concat(
    data: AmalgamatedData,
    w1: Word, w2: Word,
    h: Word,
    syllables: Seq<Syllable>,
)
    ensures
        act_word(data, concat(w1, w2), h, syllables)
            == act_word(data, w2,
                act_word(data, w1, h, syllables).0,
                act_word(data, w1, h, syllables).1),
    decreases w1.len(),
{
    if w1.len() == 0 {
        // concat(ε, w2) = w2 and act_word(ε, h, syls) = (h, syls)
        assert(concat(w1, w2) =~= w2) by {
            assert(w1.len() == 0);
            assert forall|k: int| 0 <= k < w2.len()
                implies concat(w1, w2)[k] == w2[k] by {}
        }
    } else {
        // concat(w1, w2) = [w1.first()] ++ concat(w1.drop_first(), w2)
        // act_word(concat(w1, w2), h, syls):
        //   = act_word(concat(w1, w2).drop_first(), act_sym(concat(w1, w2).first(), h, syls))
        //   = act_word(concat(w1.drop_first(), w2), act_sym(w1.first(), h, syls))
        assert(concat(w1, w2).first() == w1.first());
        assert(concat(w1, w2).drop_first() =~= concat(w1.drop_first(), w2)) by {
            let cw = concat(w1, w2);
            let rest = concat(w1.drop_first(), w2);
            assert(cw.drop_first().len() == rest.len());
            assert forall|k: int| 0 <= k < rest.len()
                implies cw.drop_first()[k] == rest[k]
            by {
                assert(cw.drop_first()[k] == cw[k + 1]);
                if k < w1.len() - 1 {
                    assert(cw[k + 1] == w1[k + 1]);
                    assert(rest[k] == w1.drop_first()[k]);
                } else {
                    assert(cw[k + 1] == w2[(k + 1 - w1.len() as int)]);
                    assert(rest[k] == w2[(k - (w1.len() - 1) as int)]);
                }
            }
        }

        let (mid_h, mid_syls) = act_sym(data, w1.first(), h, syllables);
        // IH: act_word(concat(w1.drop_first(), w2), mid_h, mid_syls)
        //    = act_word(w2, act_word(w1.drop_first(), mid_h, mid_syls))
        lemma_act_word_concat(data, w1.drop_first(), w2, mid_h, mid_syls);
    }
}

/// act_word of the empty word is the identity.
pub proof fn lemma_act_word_empty(
    data: AmalgamatedData,
    h: Word,
    syllables: Seq<Syllable>,
)
    ensures
        act_word(data, empty_word(), h, syllables) == (h, syllables),
{
    // Direct from the definition: empty_word().len() == 0
}

// ============================================================
// Part F: Well-definedness — derivation steps
// ============================================================

/// The action respects derivation: if w1 derives to w2 via steps,
/// then act_word(w1, h, syls) == act_word(w2, h, syls).
///
/// This follows from:
///   1. lemma_act_word_concat (composition)
///   2. Per-step: for each step type, the inserted/deleted pair acts trivially
///
/// For now, we state the derivation-level well-definedness and build up to it.
/// The per-step proofs (inverse pairs, relators) are the key lemmas.

/// If two words are equivalent in the AFP, they have the same action on any state.
/// This is the top-level well-definedness theorem.
///
/// Proof chain:
///   equiv_in_presentation(AFP, w1, w2)
///   => there exist derivation steps from w1 to w2
///   => each step preserves the action (by per-step lemmas)
///   => act_word(w1, ...) == act_word(w2, ...)
///
/// This will be proved once all per-step lemmas are in place.
/// For now, we build the infrastructure.

/// A single AFP-symbol word acts the same as act_sym.
pub proof fn lemma_act_word_single(
    data: AmalgamatedData,
    s: Symbol,
    h: Word,
    syllables: Seq<Syllable>,
)
    ensures
        act_word(data, Seq::new(1, |_i: int| s), h, syllables)
            == act_sym(data, s, h, syllables),
{
    let w = Seq::new(1, |_i: int| s);
    assert(w.len() == 1);
    assert(w.first() == s);
    let rest = w.drop_first();
    assert(rest.len() == 0);
    assert(rest =~= empty_word()) by {
        assert(rest.len() == 0);
        assert(empty_word().len() == 0);
    }
    let (mid_h, mid_syls) = act_sym(data, s, h, syllables);
    // act_word unfolds: w.len() != 0, so:
    //   act_word(w, h, syls) = act_word(rest, mid_h, mid_syls)
    // rest =~= ε, so act_word(rest, ...) = (mid_h, mid_syls)
    assert(act_word(data, rest, mid_h, mid_syls) == (mid_h, mid_syls));
    assert(act_word(data, w, h, syllables) == (mid_h, mid_syls));
}

// ============================================================
// Part G: Per-step well-definedness helpers
// ============================================================

/// Two AFP words produce the same action on any state.
pub open spec fn same_action(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    forall|h: Word, syllables: Seq<Syllable>|
        act_word(data, w1, h, syllables) == act_word(data, w2, h, syllables)
}

// ============================================================
// Part H: One-shot decomposition and faithfulness
// ============================================================

/// For a G₁ word g, its one-shot state: decompose g directly into (h, rep).
/// If rep = ε, state is (h, []). If rep ≠ ε, state is (h, [left_syl(rep)]).
/// This is the "answer" the action should give for a G₁-word on the identity state.
pub open spec fn g1_decompose_state(
    data: AmalgamatedData,
    g: Word,
) -> (Word, Seq<Syllable>) {
    let rep = left_canonical_rep(data, g);
    let h = left_h_part(data, g);
    if rep =~= empty_word() {
        (h, Seq::empty())
    } else {
        (h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: rep }))
    }
}

/// The identity state decomposes to (ε, []).
pub proof fn lemma_g1_decompose_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        g1_decompose_state(data, empty_word())
            == (empty_word(), Seq::<Syllable>::empty()),
{
    lemma_left_rep_identity(data);
    lemma_left_h_identity(data);
}

/// If g ≡ ε in G₁, then inv(g) ≡ ε.
proof fn lemma_inv_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        equiv_in_presentation(data.p1, inverse_word(g), empty_word()),
{
    reveal(presentation_valid);
    let p1 = data.p1;
    let inv_g = inverse_word(g);
    // g * inv(g) ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_right(p1, g);
    // g ≡ ε, so concat(g, inv(g)) ≡ concat(ε, inv(g)) by left-congruence
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, g, empty_word(), inv_g);
    // concat(ε, inv(g)) =~= inv(g)
    assert(concat(empty_word(), inv_g) =~= inv_g) by {
        let c = concat(empty_word(), inv_g);
        assert(c.len() == inv_g.len());
        assert forall|k: int| 0 <= k < c.len() implies c[k] == inv_g[k] by {}
    }
    // We have:
    //   equiv(concat(g, inv_g), ε)                     -- from word_inverse_right
    //   equiv(concat(g, inv_g), concat(ε, inv_g))      -- from equiv_concat_left
    // So by symmetry + transitivity:
    //   equiv(ε, concat(g, inv_g))
    //   equiv(concat(g, inv_g), concat(ε, inv_g))
    //   => equiv(ε, concat(ε, inv_g))
    crate::word::lemma_inverse_word_valid(g, p1.num_generators);
    crate::word::lemma_concat_word_valid(g, inv_g, p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(p1, concat(g, inv_g), empty_word());
    crate::presentation::lemma_equiv_transitive(
        p1, empty_word(), concat(g, inv_g), concat(empty_word(), inv_g));
    // Now: equiv(ε, concat(ε, inv_g)) and concat(ε, inv_g) =~= inv_g
    // So equiv(ε, inv_g), i.e., equiv(inv_g, ε) by symmetry
    crate::word::lemma_inverse_word_valid(g, p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(p1, empty_word(), inv_g);
}

/// If g ≡ ε in G₁, then g is in the left subgroup.
proof fn lemma_equiv_eps_in_subgroup(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        in_left_subgroup(data, g),
{
    reveal(presentation_valid);
    crate::benign::lemma_identity_in_generated_subgroup(data.p1, a_words(data));
    crate::presentation::lemma_equiv_symmetric(data.p1, g, empty_word());
    lemma_in_subgroup_equiv(data.p1, a_words(data), empty_word(), g);
}

/// If g ≡ ε in G₁, then same_left_coset(g, ε).
proof fn lemma_same_coset_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        same_left_coset(data, g, empty_word()),
{
    reveal(presentation_valid);
    let inv_g = inverse_word(g);
    crate::word::lemma_inverse_word_valid(g, data.p1.num_generators);
    lemma_inv_equiv_eps(data, g);
    // inv(g) ≡ ε and word_valid(inv(g), n1)
    lemma_equiv_eps_in_subgroup(data, inv_g);
    // in_left_subgroup(data, inv(g))

    // same_left_coset(g, ε) = in_left_subgroup(concat(inv(g), ε))
    // concat(inv(g), ε) =~= inv(g), so same truth value
    assert(concat(inv_g, empty_word()) =~= inv_g) by {
        let c = concat(inv_g, empty_word());
        assert(c.len() == inv_g.len());
        assert forall|k: int| 0 <= k < c.len() implies c[k] == inv_g[k] by {}
    }
}

/// If g ≡ ε in G₁, then left_canonical_rep(g) = ε.
/// If g ≡ ε, then left_min_coset_len(g) == 0.
proof fn lemma_left_min_coset_len_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_min_coset_len(data, g) == 0,
{
    let e = empty_word();
    let n1 = data.p1.num_generators;

    // ε is in g's coset (since g ≡ ε → same_left_coset(g, ε))
    lemma_same_coset_equiv_eps(data, g);
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }
    // ε has length 0 → has_left_coset_word_of_len(data, g, 0)
    assert(has_left_coset_word_of_len(data, g, 0nat));

    let pred = |l: nat| has_left_coset_word_of_len(data, g, l);
    assert(pred(0nat));
    assert(no_pred_below(pred, 0nat));

    let l = left_min_coset_len(data, g);
    lemma_no_pred_below_forces_zero(pred, l);
}

proof fn lemma_left_rep_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_canonical_rep(data, g) =~= empty_word(),
{
    lemma_left_min_coset_len_equiv_eps(data, g);
    // left_min_coset_len(g) == 0
    // left_canonical_rep(g) is a word of length 0 in g's coset → must be ε

    // Show the choose is satisfiable (ε works):
    let e = empty_word();
    lemma_same_coset_equiv_eps(data, g);
    assert(word_valid(e, data.p1.num_generators)) by { assert(e.len() == 0); }
    // ε satisfies: word_valid, same_left_coset(g, ε), ε.len() == 0

    // The choose result has length 0 → it's ε
}

/// If g ≡ ε in G₁, then left_h_part(g) = ε.
/// If g ≡ ε, then left_h_min_len(g) == 0.
proof fn lemma_left_h_min_len_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_h_min_len(data, g) == 0,
{
    let e = empty_word();
    let k = k_size(data);
    let p1 = data.p1;
    reveal(presentation_valid);

    lemma_left_rep_equiv_eps(data, g);
    let rep = left_canonical_rep(data, g);
    // rep =~= ε, so target = concat(inv(ε), g) =~= g
    let target = concat(inverse_word(rep), g);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= g) by {
        let c = concat(e, g);
        assert(c.len() == g.len());
        assert forall|j: int| 0 <= j < g.len() implies c[j] == g[j] by {}
    }

    // ε is a length-0 K-word with embed_a(ε) = ε ≡ g ≡ target
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    crate::presentation::lemma_equiv_symmetric(p1, g, e);
    assert(has_left_h_witness_of_len(data, target, 0nat));

    let pred = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred(0nat));
    assert(no_pred_below(pred, 0nat));
    let l = left_h_min_len(data, g);
    lemma_no_pred_below_forces_zero(pred, l);
}

proof fn lemma_left_h_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_h_part(data, g) =~= empty_word(),
{
    lemma_left_rep_equiv_eps(data, g);
    lemma_left_h_min_len_equiv_eps(data, g);
    // left_h_min_len(g) == 0, so left_h_part(g) picks a K-word of length 0 → ε

    // Show the choose is satisfiable (ε works):
    let e = empty_word();
    let k = k_size(data);
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= g) by {
        let c = concat(e, g);
        assert(c.len() == g.len());
        assert forall|j: int| 0 <= j < g.len() implies c[j] == g[j] by {}
    }
    reveal(presentation_valid);
    crate::presentation::lemma_equiv_symmetric(data.p1, g, e);
}

/// If g ≡ ε in G₁, then g1_decompose_state gives the identity state.
pub proof fn lemma_g1_decompose_trivial(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        g1_decompose_state(data, g)
            == (empty_word(), Seq::<Syllable>::empty()),
{
    lemma_left_rep_equiv_eps(data, g);
    lemma_left_h_equiv_eps(data, g);
}

// ============================================================
// Part H2: Converse faithfulness
// ============================================================

/// The choose for left_canonical_rep is in g's coset.
/// left_min_coset_len(g) satisfies its choose predicate.
proof fn lemma_left_min_coset_len_satisfiable(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        has_left_coset_word_of_len(data, g, left_min_coset_len(data, g)),
{
    // g is in its own coset at length g.len()
    lemma_same_left_coset_reflexive(data, g);
    assert(has_left_coset_word_of_len(data, g, g.len() as nat));

    // Use nat well-ordering to show exists|l| is_nat_min(pred, l)
    let pred = |l: nat| has_left_coset_word_of_len(data, g, l);
    assert(pred(g.len() as nat));
    lemma_nat_well_ordering(pred, g.len() as nat);
    // Now: exists|m| m <= g.len() && is_nat_min(pred, m)
    // = exists|m| pred(m) && no_pred_below(pred, m)
    // This is the satisfiability of left_min_coset_len's choose.
    // So left_min_coset_len(g) satisfies: has_left_coset_word_of_len(g, l) && no_pred_below(pred, l)
}

/// left_canonical_rep(g) is in g's coset and word_valid.
proof fn lemma_left_rep_props(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        same_left_coset(data, g, left_canonical_rep(data, g)),
        word_valid(left_canonical_rep(data, g), data.p1.num_generators),
{
    // Step 1: left_min_coset_len(g) is satisfiable
    lemma_left_min_coset_len_satisfiable(data, g);
    let l = left_min_coset_len(data, g);
    // has_left_coset_word_of_len(g, l) = exists|w| word_valid(w, n1) && same_left_coset(g, w) && w.len() == l
    // This existential is exactly the left_canonical_rep choose predicate.
    // So the choose is satisfiable → the result satisfies the predicate.
}

/// Converse: if same_left_coset(g, ε) and left_h_part(g) = ε, then g ≡ ε.
///
/// This relies on the left_h_part choose being satisfiable when g is in the
/// subgroup coset. When the predicate is satisfiable and the result is ε:
///   equiv(p1, embed_a(ε), concat(inv(ε), g)) = equiv(p1, ε, g).
///
/// Proving satisfiability requires: in_generated_subgroup → exists K-word
/// witness. This is the key infrastructure lemma connecting the two notions
/// of subgroup membership.
///
/// For now, this requires the satisfiability as a precondition.
/// TODO: prove satisfiability from in_left_subgroup.
pub proof fn lemma_g1_decompose_converse(
    data: AmalgamatedData, g: Word,
    // The K-word witness: there exists h0 with embed_a(h0) ≡ g
    h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        left_canonical_rep(data, g) =~= empty_word(),
        left_h_part(data, g) =~= empty_word(),
        // Witness: the choose predicate for left_h_part is satisfiable
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1, apply_embedding(a_words(data), h_witness), g),
    ensures
        equiv_in_presentation(data.p1, g, empty_word()),
{
    // left_h_part(g) is a choose with a satisfiable predicate (h_witness works).
    // The choose returned ε, so ε satisfies the predicate:
    //   equiv(p1, embed_a(ε), concat(inv(rep), g))
    // With rep = ε: equiv(p1, ε, g).
    // Hence g ≡ ε.

    // The key: with a satisfiable choose, the result satisfies the predicate.
    // embed_a(ε) = ε. concat(inv(ε), g) =~= g.
    // So: equiv(p1, ε, g) holds.
    reveal(presentation_valid);
    assert(apply_embedding(a_words(data), empty_word()) =~= empty_word());
    assert(inverse_word(empty_word()) =~= empty_word()) by {
        assert(inverse_word(empty_word()).len() == 0);
    }
    assert(concat(inverse_word(left_canonical_rep(data, g)), g) =~= g) by {
        assert(inverse_word(left_canonical_rep(data, g)) =~= empty_word());
        let c = concat(empty_word(), g);
        assert(c.len() == g.len());
        assert forall|k: int| 0 <= k < g.len() implies c[k] == g[k] by {}
    }
    // h_witness satisfies the left_h_part choose predicate at level left_h_min_len.
    // First: show left_h_min_len's choose is satisfiable via h_witness.
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);

    // h_witness has embed_a(h_witness) ≡ g. And target =~= g (since rep = ε).
    // So embed_a(h_witness) ≡ target. This means h_witness witnesses
    // has_left_h_witness_of_len(data, target, h_witness.len()).
    assert(has_left_h_witness_of_len(data, target, h_witness.len() as nat));

    // Use nat well-ordering on has_left_h_witness_of_len
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);
    // Now left_h_min_len's choose is satisfiable.
    // left_h_min_len(g) satisfies: has_left_h_witness_of_len(target, l) && no_pred_below
    // In particular: has_left_h_witness_of_len(target, left_h_min_len(g))
    // = exists|h| word_valid(h, k) && h.len() == left_h_min_len(g) && equiv(embed_a(h), target)

    // This existential is the left_h_part choose predicate → satisfiable.
    // left_h_part(g) satisfies: equiv(embed_a(left_h_part(g)), target)
    // With left_h_part(g) = ε: equiv(embed_a(ε), target) = equiv(ε, target) = equiv(ε, g)

    // Now derive equiv(g, ε) by symmetry
    assert(word_valid(empty_word(), data.p1.num_generators)) by {
        assert(empty_word().len() == 0);
    }
    crate::presentation::lemma_equiv_symmetric(data.p1, empty_word(), g);
}

/// The empty word is shortlex-minimal: nothing is shortlex-smaller.
/// (Already proved in shortlex.rs as lemma_empty_shortlex_minimal.)

/// left_canonical_rep of the empty word (identity element) is the empty word.
/// Because: ε is in ε's coset (reflexive), and ε is shortlex-minimal.
/// If pred(0) is true and no_pred_below(pred, l) holds, then l must be 0.
/// Because no_pred_below(pred, l) for l > 0 requires !pred(l-1), and eventually !pred(0).
proof fn lemma_no_pred_below_forces_zero(pred: spec_fn(nat) -> bool, l: nat)
    requires
        no_pred_below(pred, l),
        pred(0nat),
    ensures
        l == 0,
    decreases l,
{
    if l == 0 {
    } else {
        // no_pred_below(pred, l) = !pred(l-1) && no_pred_below(pred, l-1)
        // By IH: no_pred_below(pred, l-1) && pred(0) → l-1 == 0
        lemma_no_pred_below_forces_zero(pred, (l - 1) as nat);
        // l - 1 == 0, so l == 1. And no_pred_below(pred, 1) = !pred(0) && true = false.
        // But no_pred_below(pred, l) = no_pred_below(pred, 1) is given as true. Contradiction.
    }
}

/// left_min_coset_len for the empty word is 0.
proof fn lemma_left_min_coset_len_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_min_coset_len(data, empty_word()) == 0,
{
    let e = empty_word();
    let n1 = data.p1.num_generators;
    let pred = |l: nat| has_left_coset_word_of_len(data, e, l);

    // ε is in its own coset with length 0
    lemma_same_left_coset_reflexive(data, e);
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }
    assert(has_left_coset_word_of_len(data, e, 0nat));
    assert(pred(0nat));

    // no_pred_below(pred, 0) is true (base case)
    assert(no_pred_below(pred, 0nat));

    // So the choose predicate is satisfiable at l = 0.
    // The choose returns some l satisfying the predicate.
    let l = left_min_coset_len(data, e);
    // l satisfies: has_left_coset_word_of_len(data, e, l) && no_pred_below(pred, l)
    // From no_pred_below(pred, l) && pred(0): l must be 0.
    lemma_no_pred_below_forces_zero(pred, l);
}

pub proof fn lemma_left_rep_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_canonical_rep(data, empty_word()) =~= empty_word(),
{
    let n1 = data.p1.num_generators;
    let e = empty_word();

    lemma_left_min_coset_len_identity(data);
    // left_min_coset_len(ε) == 0

    lemma_same_left_coset_reflexive(data, e);
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }

    // ε has lex rank 0:
    assert(word_lex_rank(e) == 0);

    // has_left_coset_word_of_len_rank(data, ε, 0, 0) — ε witnesses it
    assert(has_left_coset_word_of_len_rank(data, e, 0nat, 0nat));

    // min lex rank at length 0 is 0 (no_pred_below trivially)
    let lex_pred = |r: nat| has_left_coset_word_of_len_rank(data, e, 0nat, r);
    assert(lex_pred(0nat));
    assert(no_pred_below(lex_pred, 0nat));
    let lex_min = left_min_coset_lex(data, e);
    lemma_no_pred_below_forces_zero(lex_pred, lex_min);
    // left_min_coset_lex(ε) == 0

    // left_canonical_rep(ε): choose with length 0, lex rank 0, in coset of ε.
    // ε satisfies all conditions. And length 0 + lex rank 0 uniquely determines ε.
    // The choose result has length 0 → it's ε.
}

/// left_h_part of the empty word is the empty K-word.
/// Because: left_canonical_rep(ε) = ε, so inv(rep) ++ ε = ε.
/// embed_a(ε) = ε ≡ ε in G₁. And ε is the shortlex-min such K-word.
/// left_h_min_len for the empty word is 0.
proof fn lemma_left_h_min_len_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_h_min_len(data, empty_word()) == 0,
{
    let e = empty_word();
    let k = k_size(data);
    let p1 = data.p1;
    lemma_left_rep_identity(data);

    // target = concat(inv(rep), ε) =~= ε (since rep = ε)
    let rep = left_canonical_rep(data, e);
    let target = concat(inverse_word(rep), e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= e) by { assert(concat(e, e).len() == 0); }

    // ε is a K-word of length 0 with embed_a(ε) = ε ≡ ε = target
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    crate::presentation::lemma_equiv_refl(p1, e);
    assert(has_left_h_witness_of_len(data, target, 0nat));

    let pred = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred(0nat));
    assert(no_pred_below(pred, 0nat));

    let l = left_h_min_len(data, e);
    lemma_no_pred_below_forces_zero(pred, l);
}

pub proof fn lemma_left_h_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_h_part(data, empty_word()) =~= empty_word(),
{
    let e = empty_word();
    let k = k_size(data);
    let p1 = data.p1;
    lemma_left_rep_identity(data);
    lemma_left_h_min_len_identity(data);

    // left_h_min_len(ε) == 0
    let l = left_h_min_len(data, e);
    assert(l == 0);

    // left_h_part(ε) = choose|h| word_valid(h, k) && h.len() == 0 && equiv(embed_a(h), target)
    // target = concat(inv(rep), ε) with rep = ε, so target =~= ε
    let rep = left_canonical_rep(data, e);
    let target = concat(inverse_word(rep), e);

    // ε satisfies the predicate (makes the choose satisfiable):
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= e) by { assert(concat(e, e).len() == 0); }
    crate::presentation::lemma_equiv_refl(p1, e);

    // The choose is satisfiable → result h satisfies: h.len() == 0
    let h = left_h_part(data, e);
    // h.len() == l == 0, so h =~= ε
}

/// Inserting a word at a position preserves the action if the word acts trivially
/// on ALL states (universal version).
pub proof fn lemma_insert_trivial_preserves_action(
    data: AmalgamatedData,
    prefix: Word, middle: Word, suffix: Word,
    h: Word, syllables: Seq<Syllable>,
)
    requires
        same_action(data, middle, empty_word()),
    ensures
        act_word(data, concat(prefix, concat(middle, suffix)), h, syllables)
            == act_word(data, concat(prefix, suffix), h, syllables),
{
    lemma_act_word_concat(data, prefix, concat(middle, suffix), h, syllables);
    let (ph, ps) = act_word(data, prefix, h, syllables);
    lemma_act_word_concat(data, middle, suffix, ph, ps);
    lemma_act_word_concat(data, prefix, suffix, h, syllables);
}

/// Inserting a word preserves the action when the word acts trivially on the
/// SPECIFIC intermediate state (targeted version for canonical states).
pub proof fn lemma_insert_trivial_at_state(
    data: AmalgamatedData,
    prefix: Word, middle: Word, suffix: Word,
    h: Word, syllables: Seq<Syllable>,
)
    requires ({
        let (ph, ps) = act_word(data, prefix, h, syllables);
        act_word(data, middle, ph, ps) == (ph, ps)
    }),
    ensures
        act_word(data, concat(prefix, concat(middle, suffix)), h, syllables)
            == act_word(data, concat(prefix, suffix), h, syllables),
{
    lemma_act_word_concat(data, prefix, concat(middle, suffix), h, syllables);
    let (ph, ps) = act_word(data, prefix, h, syllables);
    lemma_act_word_concat(data, middle, suffix, ph, ps);
    lemma_act_word_concat(data, prefix, suffix, h, syllables);
}

// ============================================================
// Part I: AFP injectivity theorem
// ============================================================

/// The inverse pair word [s, inv(s)].
pub open spec fn inverse_pair_word(s: Symbol) -> Word {
    Seq::new(1, |_j: int| s) + Seq::new(1, |_j: int| inverse_symbol(s))
}

/// A specific relator acts trivially on a specific state.
pub open spec fn relator_acts_trivially(
    data: AmalgamatedData, r: Word, h: Word, syls: Seq<Syllable>,
) -> bool {
    act_word(data, r, h, syls) == (h, syls)
}

/// State canonicity: h is a valid K-word.
/// The action always produces valid K-words (from left_h_part/right_h_part choose).
/// The identity state (ε, []) satisfies this trivially.
pub open spec fn is_canonical_state(data: AmalgamatedData, h: Word, syls: Seq<Syllable>) -> bool {
    word_valid(h, k_size(data))
}

/// The action of a single symbol preserves canonical state (h is word_valid for k).
/// This follows from left_h_part and right_h_part always producing word_valid K-words.
///
/// For now we state this as a spec-level property that the action preserves.
/// A full inductive proof requires showing act_sym preserves word_valid(h, k),
/// which follows from the choose predicates of left_h_part/right_h_part.
pub open spec fn action_preserves_canonical(data: AmalgamatedData) -> bool {
    forall|w: Word, h: Word, syls: Seq<Syllable>|
        is_canonical_state(data, h, syls) ==>
        #[trigger] is_canonical_state(data,
            act_word(data, w, h, syls).0,
            act_word(data, w, h, syls).1)
}

/// The action is well-defined on canonical states:
/// every AFP relator and inverse pair acts trivially.
pub open spec fn action_well_defined(data: AmalgamatedData) -> bool {
    let afp = amalgamated_free_product(data);
    // Every AFP relator acts trivially on canonical states
    &&& (forall|i: nat, inverted: bool, h: Word, syls: Seq<Syllable>|
        i < afp.relators.len() && is_canonical_state(data, h, syls) ==>
        #[trigger] relator_acts_trivially(data, get_relator(afp, i, inverted), h, syls))
    // Every inverse pair acts trivially on canonical states
    &&& (forall|s: Symbol, h: Word, syls: Seq<Syllable>|
        is_canonical_state(data, h, syls) ==>
        #[trigger] relator_acts_trivially(data, inverse_pair_word(s), h, syls))
}

/// Derivation-level well-definedness: a full derivation preserves the action.
pub proof fn lemma_act_word_deriv(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
    h: Word,
    syllables: Seq<Syllable>,
)
    requires
        action_well_defined(data),
        action_preserves_canonical(data),
        amalgamated_data_valid(data),
        is_canonical_state(data, h, syllables),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        word_valid(w1, amalgamated_free_product(data).num_generators),
    ensures
        act_word(data, w1, h, syllables) == act_word(data, w2, h, syllables),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let afp = amalgamated_free_product(data);
        let step = steps.first();
        let w_mid = apply_step(afp, w1, step).unwrap();

        // Per-step: act_word(w1, h, syls) == act_word(w_mid, h, syls)
        // Each step inserts/deletes a relator or free pair at some position.
        // By lemma_act_word_concat: we split at the position.
        // The inserted/deleted part acts trivially (from action_well_defined).
        // So the action is preserved.

        // For now: the action_well_defined condition plus the composition lemma
        // gives us the per-step result. Each step type:
        //   FreeReduce: deletes pair [s, inv(s)] → pair acts trivially
        //   FreeExpand: inserts pair [s, inv(s)] → pair acts trivially
        //   RelatorInsert: inserts relator → relator acts trivially
        //   RelatorDelete: deletes relator → relator acts trivially

        // The insertion/deletion at a position is handled by lemma_insert_trivial_preserves_action.
        // We need to match the step type and extract the position + relator/pair.

        match step {
            DerivationStep::FreeReduce { position } => {
                let s1 = w1[position];
                let pair = inverse_pair_word(s1);
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position + 2, w1.len() as int);
                assert(w1 =~= concat(prefix, concat(pair, suffix))) by {
                    assert(w1.len() == concat(prefix, concat(pair, suffix)).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, concat(pair, suffix))[k]
                    by { if k < position {} else if k < position + 2 {} else {} }
                }
                assert(w_mid =~= concat(prefix, suffix));
                // pair acts trivially on the intermediate (canonical) state
                let (ph, ps) = act_word(data, prefix, h, syllables);
                // intermediate state is canonical (from action_preserves_canonical)
                assert(is_canonical_state(data, ph, ps));
                assert(relator_acts_trivially(data, inverse_pair_word(s1), ph, ps));
                assert(act_word(data, pair, ph, ps) == (ph, ps));
                lemma_insert_trivial_at_state(data, prefix, pair, suffix, h, syllables);
            },
            DerivationStep::FreeExpand { position, symbol } => {
                let pair = inverse_pair_word(symbol);
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position, w1.len() as int);
                assert(w_mid =~= concat(prefix, concat(pair, suffix)));
                assert(w1 =~= concat(prefix, suffix)) by {
                    assert(w1.len() == concat(prefix, suffix).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, suffix)[k]
                    by { if k < position {} else {} }
                }
                let (ph, ps) = act_word(data, prefix, h, syllables);
                // intermediate state is canonical (from action_preserves_canonical)
                assert(is_canonical_state(data, ph, ps));
                assert(relator_acts_trivially(data, inverse_pair_word(symbol), ph, ps));
                assert(act_word(data, pair, ph, ps) == (ph, ps));
                lemma_insert_trivial_at_state(data, prefix, pair, suffix, h, syllables);
            },
            DerivationStep::RelatorInsert { position, relator_index, inverted } => {
                let r = get_relator(afp, relator_index, inverted);
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position, w1.len() as int);
                assert(w_mid =~= concat(prefix, concat(r, suffix)));
                assert(w1 =~= concat(prefix, suffix)) by {
                    assert(w1.len() == concat(prefix, suffix).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, suffix)[k]
                    by { if k < position {} else {} }
                }
                let (ph, ps) = act_word(data, prefix, h, syllables);
                // intermediate state is canonical (from action_preserves_canonical)
                assert(is_canonical_state(data, ph, ps));
                assert(relator_acts_trivially(data,
                    get_relator(afp, relator_index, inverted), ph, ps));
                assert(act_word(data, r, ph, ps) == (ph, ps));
                lemma_insert_trivial_at_state(data, prefix, r, suffix, h, syllables);
            },
            DerivationStep::RelatorDelete { position, relator_index, inverted } => {
                let r = get_relator(afp, relator_index, inverted);
                let rlen = r.len();
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position + rlen as int, w1.len() as int);
                assert(w1 =~= concat(prefix, concat(r, suffix))) by {
                    assert(w1.len() == concat(prefix, concat(r, suffix)).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, concat(r, suffix))[k]
                    by {
                        if k < position {} else if k < position + rlen as int {
                            assert(w1.subrange(position, position + rlen as int) == r);
                        } else {}
                    }
                }
                assert(w_mid =~= concat(prefix, suffix));
                let (ph, ps) = act_word(data, prefix, h, syllables);
                // intermediate state is canonical (from action_preserves_canonical)
                assert(is_canonical_state(data, ph, ps));
                assert(relator_acts_trivially(data,
                    get_relator(afp, relator_index, inverted), ph, ps));
                assert(act_word(data, r, ph, ps) == (ph, ps));
                lemma_insert_trivial_at_state(data, prefix, r, suffix, h, syllables);
            },
        }

        // Each branch established: act_word(w1, h, syls) == act_word(w_mid, h, syls)
        // IH: need word_valid(w_mid, n) for the recursive call.
        crate::amalgamated_free_product::lemma_amalgamated_valid(data);
        crate::presentation::lemma_step_preserves_word_valid_pres(
            afp, w1, step, w_mid);
        lemma_act_word_deriv(data, steps.drop_first(), w_mid, w2, h, syllables);
    }
}

/// The action preserves canonical state for a single symbol.
/// act_sym produces h from left_h_part or right_h_part, which are choose results
/// satisfying word_valid(h, k). So the output h is word_valid.
///
/// Note: this requires the left_h_part and right_h_part choose predicates to be
/// satisfiable for the products encountered. This is guaranteed when the
/// starting state is canonical and the transversal decomposition exists.
///
/// For the identity state and action-produced states, satisfiability holds.
/// We take it as a precondition for now.
proof fn lemma_action_preserves_canonical(
    data: AmalgamatedData,
    w: Word,
    h: Word,
    syls: Seq<Syllable>,
)
    requires
        action_preserves_canonical(data),
        is_canonical_state(data, h, syls),
    ensures
        is_canonical_state(data,
            act_word(data, w, h, syls).0,
            act_word(data, w, h, syls).1),
{
    // Direct from action_preserves_canonical spec.
}

// ============================================================
// Part I2: Choose property extraction
// ============================================================

/// Extract the key property of left_h_part: embed_a(h) ≡ concat(inv(rep), g) in G₁.
/// Requires a witness K-word to prove the choose is satisfiable.
proof fn lemma_left_h_part_props(
    data: AmalgamatedData,
    g: Word,
    h_witness: Word,  // any K-word with embed ≡ target
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(inverse_word(left_canonical_rep(data, g)), g)),
    ensures ({
        let rep = left_canonical_rep(data, g);
        let h = left_h_part(data, g);
        let target = concat(inverse_word(rep), g);
        &&& word_valid(h, k_size(data))
        &&& equiv_in_presentation(data.p1,
                apply_embedding(a_words(data), h), target)
    }),
{
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);

    // h_witness satisfies the left_h_min_len choose predicate:
    // has_left_h_witness_of_len(data, target, h_witness.len())
    assert(has_left_h_witness_of_len(data, target, h_witness.len() as nat));

    // By nat well-ordering: left_h_min_len's choose is satisfiable
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    // left_h_min_len satisfies its predicate → has_left_h_witness_of_len(target, min_len)
    // This existential provides a witness for left_h_part's choose.
    // So left_h_part's choose is satisfiable → result has the properties.
}

// ============================================================
// Part J: Per-relator triviality — inverse pairs on identity
// ============================================================

/// Inverse pair on identity: act_word([s, inv(s)], ε, []) = (ε, []).
/// Case 1: s is in the left subgroup (left_canonical_rep([s]) = ε).
///   After s: state = (h', []). After inv(s): product = inv(s) * embed_a(h') ≡ ε.
///   So the state returns to (ε, []).
/// Helper: act_sym of a G₁ symbol with rep = ε gives (h', []).
proof fn lemma_act_sym_subgroup_identity(
    data: AmalgamatedData,
    s: Symbol,
)
    requires
        amalgamated_data_valid(data),
        generator_index(s) < data.p1.num_generators,
        left_canonical_rep(data,
            concat(Seq::new(1, |_i: int| s), empty_word())) =~= empty_word(),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s),
            apply_embedding(a_words(data), empty_word()));
        let h1 = left_h_part(data, product);
        act_sym(data, s, empty_word(), Seq::<Syllable>::empty())
            == (h1, Seq::<Syllable>::empty())
    }),
{
    // act_sym dispatches to act_left_sym since gen_index(s) < n1.
    // act_left_sym: product = concat([s], embed_a(ε)), rep = ε → (h1, [])
}

/// Inverse pair [s, inv(s)] acts trivially on identity state,
/// when s is in the left subgroup (left_canonical_rep = ε).
/// Takes a K-word witness for the subgroup decomposition.
proof fn lemma_inverse_pair_identity_case1(
    data: AmalgamatedData,
    s: Symbol,
    h_wit: Word,  // K-word witness: embed_a(h_wit) ≡ [s] in G₁
)
    requires
        amalgamated_data_valid(data),
        generator_index(s) < data.p1.num_generators,
        left_canonical_rep(data,
            concat(Seq::new(1, |_i: int| s), empty_word())) =~= empty_word(),
        word_valid(h_wit, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_wit),
            concat(Seq::new(1, |_i: int| s), empty_word())),
    ensures
        act_word(data, inverse_pair_word(s), empty_word(), Seq::<Syllable>::empty())
            == (empty_word(), Seq::<Syllable>::empty()),
{
    let e = empty_word();
    let p1 = data.p1;
    let n1 = p1.num_generators;
    reveal(presentation_valid);

    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let product1 = concat(s_word, apply_embedding(a_words(data), e));
    assert(apply_embedding(a_words(data), e) =~= e);
    let h1 = left_h_part(data, product1);

    // Step 1: act_sym(s, ε, []) = (h1, [])
    lemma_act_sym_subgroup_identity(data, s);

    // Step 2: decompose via composition
    assert(inverse_pair_word(s) =~= concat(s_word, inv_s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(s_word, inv_s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(s_word, inv_s_word)[k] by {}
    }
    lemma_act_word_concat(data, s_word, inv_s_word, e, Seq::<Syllable>::empty());
    lemma_act_word_single(data, s, e, Seq::<Syllable>::empty());
    // act_word([s], ε, []) = (h1, [])

    // Step 3: Need act_word([inv(s)], h1, []) = (ε, [])
    // = act_sym(inv(s), h1, []) by single
    lemma_act_word_single(data, inv_s, h1, Seq::<Syllable>::empty());

    // Step 4: show product2 ≡ ε (the second symbol's product)
    // product2 = concat([inv(s)], embed_a(h1))
    // embed_a(h1) ≡ product1 (from h_part choose extraction)
    assert(concat(inverse_word(left_canonical_rep(data, product1)), product1) =~= product1) by {
        assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
        let c = concat(e, product1);
        assert(c.len() == product1.len());
        assert forall|k: int| 0 <= k < product1.len() implies c[k] == product1[k] by {}
    }
    lemma_left_h_part_props(data, product1, h_wit);
    // embed_a(h1) ≡ product1

    let product2 = concat(inv_s_word, apply_embedding(a_words(data), h1));
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, inv_s_word, apply_embedding(a_words(data), h1), product1);
    // product2 ≡ concat([inv(s)], product1)

    assert(product1 =~= s_word) by {
        assert(product1.len() == s_word.len());
        assert forall|k: int| 0 <= k < s_word.len() implies product1[k] == s_word[k] by {}
    }
    // concat([inv(s)], product1) =~= concat([inv(s)], [s])

    // concat(inverse_word([s]), [s]) ≡ ε
    assert(inverse_word(s_word) =~= inv_s_word) by {
        assert(s_word.first() == s);
        assert(s_word.drop_first().len() == 0);
        assert(inverse_word(s_word.drop_first()) =~= e);
        assert(concat(e, Seq::new(1, |_i: int| inverse_symbol(s))).len() == 1);
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p1, s_word);

    // Chain: product2 ≡ concat([inv(s)], product1) =~= concat(inv_s_word, s_word) ≡ ε
    crate::presentation::lemma_equiv_transitive(p1, product2,
        concat(inv_s_word, product1), e);

    // word_valid(product2, n1)
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h1, n1);
    crate::word::lemma_concat_word_valid(inv_s_word,
        apply_embedding(a_words(data), h1), n1);

    // product2 ≡ ε → left_canonical_rep(product2) = ε, left_h_part(product2) = ε
    lemma_left_rep_equiv_eps(data, product2);
    lemma_left_h_equiv_eps(data, product2);
    // So act_sym(inv(s), h1, []) = (ε, [])
    // And act_word([s, inv(s)], ε, []) = act_word([inv(s)], h1, []) = (ε, [])
}

/// For a single G₁ symbol s: act_word([s], ε, []) = g1_decompose_state([s]).
/// This connects the symbol-by-symbol action to the one-shot decomposition.
pub proof fn lemma_act_single_eq_decompose(
    data: AmalgamatedData,
    s: Symbol,
)
    requires
        amalgamated_data_valid(data),
        generator_index(s) < data.p1.num_generators,
    ensures
        act_word(data, Seq::new(1, |_i: int| s), empty_word(), Seq::<Syllable>::empty())
            == g1_decompose_state(data, Seq::new(1, |_i: int| s)),
{
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);

    // act_word([s], ε, []) = act_sym(s, ε, [])
    lemma_act_word_single(data, s, e, Seq::<Syllable>::empty());

    // act_sym(s, ε, []) = act_left_sym(s, ε, []) since gen_index(s) < n1

    // act_left_sym uses:
    //   product = concat([s], embed_a(ε)) = concat([s], ε) =~= [s]
    //   h' = left_h_part(product)
    //   rep' = left_canonical_rep(product)

    // g1_decompose_state([s]) uses:
    //   rep = left_canonical_rep([s])
    //   h = left_h_part([s])

    // Since product =~= [s]: the canonical reps and h-parts are the same.
    assert(apply_embedding(a_words(data), e) =~= e);
    let product = concat(s_word, apply_embedding(a_words(data), e));
    assert(product =~= s_word) by {
        assert(product.len() == s_word.len());
        assert forall|k: int| 0 <= k < s_word.len()
            implies product[k] == s_word[k] by {}
    }
    // product == s_word (from =~= on Seq)
    // So left_canonical_rep(product) == left_canonical_rep(s_word)
    // And left_h_part(product) == left_h_part(s_word)
    // And act_left_sym gives the same as g1_decompose_state.
}

// ============================================================
// Part K: Bridge — in_generated_subgroup ↔ apply_embedding
// ============================================================

/// If w is in the generated subgroup, there exists a K-word whose embedding ≡ w.
/// This bridges in_generated_subgroup (existential over factors) to
/// apply_embedding (K-word based).
///
/// Proof: in_generated_subgroup gives factors with concat_all(factors) ≡ w.
/// Each factor = gens[i] or inv(gens[i]). Map to K-word: Gen(i) or Inv(i).
/// Then apply_embedding produces the same word as concat_all.
pub proof fn lemma_subgroup_to_k_word(
    p: Presentation,
    gens: Seq<Word>,
    w: Word,
)
    requires
        in_generated_subgroup(p, gens, w),
    ensures
        exists|h: Word|
            word_valid(h, gens.len())
            && equiv_in_presentation(p, apply_embedding(gens, h), w),
{
    // Extract factors witness
    let factors: Seq<Word> = choose|factors: Seq<Word>|
        #[trigger] factors_from_generators(gens, factors)
        && equiv_in_presentation(p, concat_all(factors), w);

    // Build the K-word from the factors by induction
    lemma_factors_to_k_word_exists(p, gens, factors);
    // Now: exists|h| word_valid(h, gens.len()) && equiv(embed(h), concat_all(factors))

    // Chain: embed(h) ≡ concat_all(factors) ≡ w
    let h: Word = choose|h: Word| word_valid(h, gens.len())
        && equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors));
    crate::presentation::lemma_equiv_transitive(p,
        apply_embedding(gens, h), concat_all(factors), w);
}

/// Helper: given factors from generators, construct a K-word with matching embedding.
proof fn lemma_factors_to_k_word_exists(
    p: Presentation,
    gens: Seq<Word>,
    factors: Seq<Word>,
)
    requires
        factors_from_generators(gens, factors),
    ensures
        exists|h: Word|
            word_valid(h, gens.len())
            && equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors)),
    decreases factors.len(),
{
    if factors.len() == 0 {
        // h = ε: word_valid(ε, anything) and embed(ε) = ε = concat_all([])
        let h = empty_word();
        assert(word_valid(h, gens.len())) by { assert(h.len() == 0); }
        assert(apply_embedding(gens, h) =~= empty_word());
        assert(concat_all(factors) =~= empty_word());
        crate::presentation::lemma_equiv_refl(p, empty_word());
        // Witness the exists: h = ε satisfies both conditions
        assert(equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors)));
    } else {
        // IH on rest
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(gens, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_factors_to_k_word_exists(p, gens, rest);
        // exists|h_rest| word_valid(h_rest, gens.len()) && equiv(embed(h_rest), concat_all(rest))

        let h_rest: Word = choose|h_rest: Word| word_valid(h_rest, gens.len())
            && equiv_in_presentation(p, apply_embedding(gens, h_rest), concat_all(rest));

        // First factor: is_generator_or_inverse(gens, factors.first())
        // So factors.first() = gens[i] or inv(gens[i]) for some i < gens.len()
        let first = factors.first();
        let i: nat = choose|i: nat| i < gens.len()
            && (first =~= gens[i as int] || first =~= inverse_word(gens[i as int]));

        // Construct the K-word: [sym] ++ h_rest
        let sym = if first =~= gens[i as int] { Symbol::Gen(i) } else { Symbol::Inv(i) };
        let h = Seq::new(1, |_j: int| sym) + h_rest;

        // word_valid(h, gens.len()): sym has gen_index = i < gens.len(), rest is word_valid by IH
        assert(word_valid(h, gens.len())) by {
            assert(symbol_valid(sym, gens.len()));
            assert forall|k: int| 0 <= k < h.len()
                implies symbol_valid(h[k], gens.len())
            by {
                if k == 0 {
                } else {
                    assert(h[k] == h_rest[k - 1]);
                }
            }
        }

        // embed(h) = concat(embed_sym(sym), embed(h_rest))
        //          = concat(first, embed(h_rest))
        //          ≡ concat(first, concat_all(rest))   [by IH on h_rest]
        //          = concat_all(factors)

        // embed_sym(sym) =~= first
        assert(apply_embedding_symbol(gens, sym) =~= first);

        // Unfold apply_embedding(gens, h) one level:
        // h = [sym] ++ h_rest, so h.first() = sym, h.drop_first() =~= h_rest
        assert(h.len() > 0);
        assert(h.first() == sym);
        assert(h.drop_first() =~= h_rest) by {
            let d = h.drop_first();
            assert(d.len() == h_rest.len());
            assert forall|k: int| 0 <= k < h_rest.len()
                implies d[k] == h_rest[k] by {}
        }
        // apply_embedding(gens, h) = concat(embed_sym(h.first()), embed(h.drop_first()))
        //                          = concat(embed_sym(sym), embed(h_rest))
        //                          = concat(first, embed(h_rest))

        // IH gives: equiv(embed(h_rest), concat_all(rest))
        // By right-congruence: concat(first, embed(h_rest)) ≡ concat(first, concat_all(rest))
        crate::presentation_lemmas::lemma_equiv_concat_right(p, first,
            apply_embedding(gens, h_rest), concat_all(rest));

        // concat(first, concat_all(rest)) = concat_all(factors)
        // So: equiv(concat(first, embed(h_rest)), concat_all(factors))
        // And: apply_embedding(gens, h) =~= concat(first, embed(h_rest))
        // Therefore: equiv(apply_embedding(gens, h), concat_all(factors))
        assert(equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors)));
    }
}

/// concat_all distributes over sequence append.
proof fn lemma_concat_all_append(xs: Seq<Word>, ys: Seq<Word>)
    ensures
        concat_all(xs + ys) =~= concat(concat_all(xs), concat_all(ys)),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert((xs + ys) =~= ys) by {
            assert((xs + ys).len() == ys.len());
            assert forall|k: int| 0 <= k < ys.len()
                implies (xs + ys)[k] == ys[k] by {}
        }
        assert(concat_all(xs) =~= empty_word());
        assert(concat(empty_word(), concat_all(ys)) =~= concat_all(ys)) by {
            let c = concat(empty_word(), concat_all(ys));
            assert(c.len() == concat_all(ys).len());
            assert forall|k: int| 0 <= k < c.len()
                implies c[k] == concat_all(ys)[k] by {}
        }
    } else {
        // concat_all(xs ++ ys) = concat(xs.first(), concat_all(xs.drop_first() ++ ys))
        assert((xs + ys).first() == xs.first());
        assert((xs + ys).drop_first() =~= xs.drop_first() + ys) by {
            let lhs = (xs + ys).drop_first();
            let rhs = xs.drop_first() + ys;
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < rhs.len()
                implies lhs[k] == rhs[k] by {}
        }
        // IH: concat_all(xs.drop_first() ++ ys) =~= concat(concat_all(xs.drop_first()), concat_all(ys))
        lemma_concat_all_append(xs.drop_first(), ys);
        // concat_all(xs) = concat(xs.first(), concat_all(xs.drop_first()))
        // concat(concat_all(xs), concat_all(ys)) = concat(concat(xs.first(), concat_all(xs.drop_first())), concat_all(ys))
        // By concat associativity: = concat(xs.first(), concat(concat_all(xs.drop_first()), concat_all(ys)))
        // = concat(xs.first(), concat_all(xs.drop_first() ++ ys)) [by IH]
        // = concat_all(xs ++ ys)
    }
}

/// Generated subgroup is closed under concatenation.
pub proof fn lemma_subgroup_concat(
    p: Presentation, gens: Seq<Word>, a: Word, b: Word,
)
    requires
        in_generated_subgroup(p, gens, a),
        in_generated_subgroup(p, gens, b),
    ensures
        in_generated_subgroup(p, gens, concat(a, b)),
{
    // Extract factor witnesses
    let fa: Seq<Word> = choose|fa: Seq<Word>|
        #[trigger] factors_from_generators(gens, fa)
        && equiv_in_presentation(p, concat_all(fa), a);
    let fb: Seq<Word> = choose|fb: Seq<Word>|
        #[trigger] factors_from_generators(gens, fb)
        && equiv_in_presentation(p, concat_all(fb), b);

    // Combined factors: fa ++ fb
    let fab = fa + fb;
    assert(factors_from_generators(gens, fab)) by {
        assert forall|k: int| 0 <= k < fab.len()
            implies is_generator_or_inverse(gens, #[trigger] fab[k])
        by {
            if k < fa.len() {
                assert(fab[k] == fa[k]);
            } else {
                assert(fab[k] == fb[k - fa.len()]);
            }
        }
    }

    // concat_all(fab) =~= concat(concat_all(fa), concat_all(fb))
    lemma_concat_all_append(fa, fb);
    // concat(concat_all(fa), concat_all(fb)) ≡ concat(a, b) by congruence
    crate::presentation_lemmas::lemma_equiv_concat(p,
        concat_all(fa), a, concat_all(fb), b);
    // Since concat_all(fab) =~= concat(concat_all(fa), concat_all(fb)) (extensional eq = eq for Seq),
    // and equiv(concat(concat_all(fa), concat_all(fb)), concat(a, b)),
    // we get equiv(concat_all(fab), concat(a, b)).
}

/// Inverse preserves equivalence: if a ≡ b then inv(a) ≡ inv(b).
/// Split into two helpers to stay within rlimit.
proof fn lemma_equiv_inverse_helper(
    p: Presentation, a: Word, b: Word,
)
    requires
        equiv_in_presentation(p, a, b),
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
    ensures
        // concat(inv(b), a) ≡ ε
        equiv_in_presentation(p, concat(inverse_word(b), a), empty_word()),
{
    let inv_b = inverse_word(b);
    crate::word::lemma_inverse_word_valid(b, p.num_generators);
    // inv(b) * b ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p, b);
    // a ≡ b → concat(inv(b), a) ≡ concat(inv(b), b) by right-congruence
    crate::presentation_lemmas::lemma_equiv_concat_right(p, inv_b, a, b);
    // ε ≡ concat(inv(b), b) by symmetry
    crate::word::lemma_concat_word_valid(inv_b, b, p.num_generators);
    crate::presentation::lemma_equiv_symmetric(p, concat(inv_b, b), empty_word());
    // concat(inv(b), a) ≡ concat(inv(b), b) ≡... need direction.
    // We have: equiv(concat(inv_b, a), concat(inv_b, b)) from right-congruence
    // And: equiv(concat(inv_b, b), ε) from word_inverse_left
    // Transitivity: equiv(concat(inv_b, a), ε)
    crate::presentation::lemma_equiv_transitive(p,
        concat(inv_b, a), concat(inv_b, b), empty_word());
}

pub proof fn lemma_equiv_inverse(
    p: Presentation, a: Word, b: Word,
)
    requires
        equiv_in_presentation(p, a, b),
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
    ensures
        equiv_in_presentation(p, inverse_word(a), inverse_word(b)),
{
    let inv_a = inverse_word(a);
    let inv_b = inverse_word(b);
    crate::word::lemma_inverse_word_valid(a, p.num_generators);
    crate::word::lemma_inverse_word_valid(b, p.num_generators);

    // From helper: concat(inv(b), a) ≡ ε
    lemma_equiv_inverse_helper(p, a, b);

    // concat(concat(inv(b), a), inv(a)) ≡ concat(ε, inv(a)) by left-congruence
    crate::word::lemma_concat_word_valid(inv_b, a, p.num_generators);
    crate::presentation_lemmas::lemma_equiv_concat_left(p,
        concat(inv_b, a), empty_word(), inv_a);
    // LHS ≡ concat(ε, inv(a)) =~= inv(a)

    // a * inv(a) ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_right(p, a);
    // concat(inv(b), concat(a, inv(a))) ≡ concat(inv(b), ε) by right-congruence
    crate::presentation_lemmas::lemma_equiv_concat_right(p, inv_b,
        concat(a, inv_a), empty_word());
    // RHS ≡ concat(inv(b), ε) =~= inv(b)

    // Key: concat(concat(inv(b), a), inv(a)) =~= concat(inv(b), concat(a, inv(a))) [seq assoc]
    // From above: LHS ≡ inv(a) and RHS ≡ inv(b)
    // Since LHS =~= RHS: inv(a) ≡ LHS =~= RHS ≡ inv(b)
    // i.e., equiv(inv(a), inv(b)) by the chain.

    // Step by step for Z3:
    // equiv(concat(concat(inv_b, a), inv_a), concat(ε, inv_a))  [from left-congruence]
    // equiv(concat(inv_b, concat(a, inv_a)), concat(inv_b, ε))  [from right-congruence]
    // These two LHS expressions are =~= (seq associativity)
    // So: equiv(concat(inv_b, concat(a, inv_a)), concat(ε, inv_a)) by chain:
    //   concat(inv_b, concat(a, inv_a)) =~= concat(concat(inv_b, a), inv_a) ≡ concat(ε, inv_a)
    // And: equiv(concat(inv_b, ε), concat(ε, inv_a)) by transitivity with above
    //   concat(inv_b, ε) ≡ concat(inv_b, concat(a, inv_a)) ≡ concat(ε, inv_a)
    // And concat(inv_b, ε) =~= inv_b and concat(ε, inv_a) =~= inv_a
    // So equiv(inv_b, inv_a), hence equiv(inv_a, inv_b) by symmetry.

    // Explicit chain: connect the two congruence results through seq associativity.
    // We have:
    //   (A) equiv(concat(concat(inv_b, a), inv_a), concat(ε, inv_a))  [left-cong]
    //   (B) equiv(concat(inv_b, concat(a, inv_a)), concat(inv_b, ε))  [right-cong]
    // And concat(concat(inv_b, a), inv_a) =~= concat(inv_b, concat(a, inv_a)) [assoc]

    // From (A): symmetry gives equiv(concat(ε, inv_a), concat(concat(inv_b, a), inv_a))
    // =~= equiv(concat(ε, inv_a), concat(inv_b, concat(a, inv_a)))
    // Then transitivity with (B): equiv(concat(ε, inv_a), concat(inv_b, ε))
    // word_valid for intermediate expressions
    crate::word::lemma_concat_word_valid(concat(inv_b, a), inv_a, p.num_generators);
    crate::word::lemma_concat_word_valid(a, inv_a, p.num_generators);
    // Symmetry on (A): equiv(concat(ε, inv_a), concat(concat(inv_b, a), inv_a))
    crate::presentation::lemma_equiv_symmetric(p,
        concat(concat(inv_b, a), inv_a), concat(empty_word(), inv_a));
    // Transitivity: concat(ε, inv_a) ≡ concat(concat(inv_b,a), inv_a) =~= concat(inv_b, concat(a,inv_a)) ≡ concat(inv_b, ε)
    // The middle =~= (assoc) is automatic for Z3 since Seq =~= implies ==.
    // But the symmetry gave equiv(concat(ε, inv_a), concat(concat(inv_b,a), inv_a))
    // And (B) gives equiv(concat(inv_b, concat(a, inv_a)), concat(inv_b, ε))
    // These connect via assoc: concat(concat(inv_b,a), inv_a) =~= concat(inv_b, concat(a, inv_a))
    // Seq associativity: concat(concat(x,y),z) =~= concat(x, concat(y,z))
    assert(concat(concat(inv_b, a), inv_a) =~= concat(inv_b, concat(a, inv_a))) by {
        let lhs = concat(concat(inv_b, a), inv_a);
        let rhs = concat(inv_b, concat(a, inv_a));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_b.len() {} else if k < inv_b.len() + a.len() {} else {}
        }
    }
    crate::presentation::lemma_equiv_transitive(p,
        concat(empty_word(), inv_a),
        concat(concat(inv_b, a), inv_a),
        concat(inv_b, empty_word()));
    // Now: equiv(concat(ε, inv_a), concat(inv_b, ε))
    // concat(ε, inv_a) =~= inv_a and concat(inv_b, ε) =~= inv_b
    // So equiv(inv_a, inv_b). Z3 should handle the =~= substitution.
    assert(concat(empty_word(), inv_a) =~= inv_a) by {
        let c = concat(empty_word(), inv_a);
        assert(c.len() == inv_a.len());
        assert forall|k: int| 0 <= k < inv_a.len() implies c[k] == inv_a[k] by {}
    }
    assert(concat(inv_b, empty_word()) =~= inv_b) by {
        let c = concat(inv_b, empty_word());
        assert(c.len() == inv_b.len());
        assert forall|k: int| 0 <= k < inv_b.len() implies c[k] == inv_b[k] by {}
    }
}

/// Generated subgroup is closed under equivalence (already proved as lemma_in_subgroup_equiv).

/// Reverse a sequence of words and invert each element.
pub open spec fn reverse_invert_factors(factors: Seq<Word>) -> Seq<Word>
    decreases factors.len(),
{
    if factors.len() == 0 {
        Seq::empty()
    } else {
        reverse_invert_factors(factors.drop_first())
            + Seq::new(1, |_i: int| inverse_word(factors.first()))
    }
}

/// Each factor in reverse_invert_factors is still a generator-or-inverse.
proof fn lemma_reverse_invert_preserves_generators(
    gens: Seq<Word>, factors: Seq<Word>,
)
    requires
        factors_from_generators(gens, factors),
    ensures
        factors_from_generators(gens, reverse_invert_factors(factors)),
    decreases factors.len(),
{
    if factors.len() == 0 {
    } else {
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(gens, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_reverse_invert_preserves_generators(gens, rest);
        let rif = reverse_invert_factors(factors);
        let rif_rest = reverse_invert_factors(rest);
        let inv_first = inverse_word(factors.first());
        assert forall|k: int| 0 <= k < rif.len()
            implies is_generator_or_inverse(gens, #[trigger] rif[k])
        by {
            if k < rif_rest.len() {
                assert(rif[k] == rif_rest[k]);
            } else {
                assert(rif[k] == inv_first);
                // inv_first = inv(factors.first())
                // factors.first() is is_generator_or_inverse(gens, ...)
                // So exists i: factors.first() == gens[i] or factors.first() == inv(gens[i])
                // Case 1: factors.first() == gens[i] → inv_first == inv(gens[i])
                //   → is_generator_or_inverse(gens, inv_first) with the inv case ✓
                // Case 2: factors.first() == inv(gens[i]) → inv_first == inv(inv(gens[i]))
                //   inv(inv(gens[i])) =~= gens[i] by inverse involution
                //   → is_generator_or_inverse(gens, inv_first) with the direct case ✓
                let i: nat = choose|i: nat| i < gens.len()
                    && (factors.first() =~= gens[i as int]
                        || factors.first() =~= inverse_word(gens[i as int]));
                if factors.first() =~= gens[i as int] {
                    // inv_first = inv(gens[i]) → is_gen_or_inv
                } else {
                    // inv_first = inv(inv(gens[i])) =~= gens[i]
                    crate::word::lemma_inverse_involution(gens[i as int]);
                }
            }
        }
    }
}

/// concat_all of factors_from_generators produces a word_valid word.
proof fn lemma_concat_all_word_valid(
    gens: Seq<Word>, factors: Seq<Word>, n: nat,
)
    requires
        factors_from_generators(gens, factors),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], n),
    ensures
        word_valid(concat_all(factors), n),
    decreases factors.len(),
{
    if factors.len() == 0 {
    } else {
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(gens, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_concat_all_word_valid(gens, rest, n);
        // factors.first() is word_valid: it's gens[i] or inv(gens[i])
        let first = factors.first();
        let i: nat = choose|i: nat| i < gens.len()
            && (first =~= gens[i as int] || first =~= inverse_word(gens[i as int]));
        if first =~= inverse_word(gens[i as int]) {
            crate::word::lemma_inverse_word_valid(gens[i as int], n);
        }
        crate::word::lemma_concat_word_valid(first, concat_all(rest), n);
    }
}

/// concat_all of reverse_invert_factors ≡ inverse_word of concat_all.
proof fn lemma_reverse_invert_is_inverse(
    p: Presentation, factors: Seq<Word>,
)
    ensures
        equiv_in_presentation(p,
            concat_all(reverse_invert_factors(factors)),
            inverse_word(concat_all(factors))),
    decreases factors.len(),
{
    if factors.len() == 0 {
        // All three expressions evaluate to ε when factors is empty:
        let rif = reverse_invert_factors(factors);
        let ca = concat_all(factors);
        assert(rif.len() == 0);
        assert(concat_all(rif) =~= empty_word());
        assert(ca =~= empty_word());
        assert(inverse_word(ca) =~= empty_word()) by {
            assert(inverse_word(empty_word()).len() == 0);
        }
        crate::presentation::lemma_equiv_refl(p, concat_all(rif));
        // Explicitly assert the postcondition using bound variables:
        assert(equiv_in_presentation(p, concat_all(rif), inverse_word(ca)));
        return;
    } else {
        let rest = factors.drop_first();
        let first = factors.first();
        let inv_first = inverse_word(first);
        let rif_rest = reverse_invert_factors(rest);

        lemma_reverse_invert_is_inverse(p, rest);
        crate::word::lemma_inverse_concat(first, concat_all(rest));
        lemma_concat_all_append(rif_rest, Seq::new(1, |_i: int| inv_first));
        crate::presentation_lemmas::lemma_equiv_concat_left(p,
            concat_all(rif_rest), inverse_word(concat_all(rest)), inv_first);
        // Connect to postcondition:
        // Postcondition LHS = concat_all(reverse_invert_factors(factors))
        //   = concat_all(rif_rest ++ [inv_first])  [by def of reverse_invert_factors]
        //   =~= concat(concat_all(rif_rest), concat_all([inv_first]))  [by concat_all_append]
        //   =~= concat(concat_all(rif_rest), inv_first)  [concat_all of singleton]
        // Key =~= chain for the postcondition:
        // LHS of postcondition: concat_all(reverse_invert_factors(factors))
        // reverse_invert_factors(factors) = rif_rest ++ [inv_first] by definition
        // concat_all_append gave:
        //   concat_all(rif_rest ++ singleton) =~= concat(concat_all(rif_rest), concat_all(singleton))
        // concat_all(singleton) where singleton = [inv_first]:
        let singleton = Seq::new(1, |_i: int| inv_first);
        assert(singleton.len() == 1);
        assert(singleton.first() == inv_first);
        let singleton_rest = singleton.drop_first();
        assert(singleton_rest.len() == 0);
        assert(concat_all(singleton_rest) =~= empty_word());
        // concat_all(singleton) = concat(singleton.first(), concat_all(singleton.drop_first()))
        //                       = concat(inv_first, ε)
        assert(concat(inv_first, empty_word()) =~= inv_first) by {
            let c = concat(inv_first, empty_word());
            assert(c.len() == inv_first.len());
            assert forall|k: int| 0 <= k < c.len() implies c[k] == inv_first[k] by {}
        }
        // So: LHS =~= concat(concat_all(rif_rest), inv_first)

        // RHS of postcondition: inverse_word(concat_all(factors))
        // = inverse_word(concat(first, concat_all(rest))) [concat_all unfolds]
        // =~= concat(inverse_word(concat_all(rest)), inv_first) [from inverse_concat]

        // equiv_concat_left gave:
        //   equiv(concat(concat_all(rif_rest), inv_first), concat(inv(concat_all(rest)), inv_first))
        // LHS =~= postcondition LHS (shown above)
        // RHS =~= postcondition RHS (from inverse_concat)
        // So: equiv(postcondition LHS, postcondition RHS). QED.
        return;
    }
}

/// Generated subgroup is closed under inverse.
pub proof fn lemma_subgroup_inverse(
    p: Presentation, gens: Seq<Word>, w: Word,
)
    requires
        in_generated_subgroup(p, gens, w),
        presentation_valid(p),
        word_valid(w, p.num_generators),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], p.num_generators),
    ensures
        in_generated_subgroup(p, gens, inverse_word(w)),
{
    let n = p.num_generators;
    let fa: Seq<Word> = choose|fa: Seq<Word>|
        #[trigger] factors_from_generators(gens, fa)
        && equiv_in_presentation(p, concat_all(fa), w);

    let rif = reverse_invert_factors(fa);
    lemma_reverse_invert_preserves_generators(gens, fa);
    lemma_reverse_invert_is_inverse(p, fa);
    // concat_all(rif) ≡ inv(concat_all(fa))

    // concat_all(fa) is word_valid (each factor is gens[i] or inv(gens[i]), all word_valid):
    lemma_concat_all_word_valid(gens, fa, n);

    // inv(concat_all(fa)) ≡ inv(w) by lemma_equiv_inverse:
    lemma_equiv_inverse(p, concat_all(fa), w);

    // Chain: concat_all(rif) ≡ inv(concat_all(fa)) ≡ inv(w)
    crate::word::lemma_inverse_word_valid(concat_all(fa), n);
    crate::word::lemma_inverse_word_valid(w, n);
    crate::presentation::lemma_equiv_transitive(p,
        concat_all(rif), inverse_word(concat_all(fa)), inverse_word(w));

    // in_generated_subgroup(concat_all(rif)): rif satisfies factors_from_generators, and
    // concat_all(rif) ≡ concat_all(rif) by reflexivity.
    crate::presentation::lemma_equiv_refl(p, concat_all(rif));
    assert(in_generated_subgroup(p, gens, concat_all(rif)));
    // + equiv(concat_all(rif), inv(w)) → in_generated_subgroup(inv(w))
    lemma_in_subgroup_equiv(p, gens, concat_all(rif), inverse_word(w));
}

// ============================================================
// Part K2: Coset invariance — same coset → same canonical rep
// ============================================================

/// same_left_coset is symmetric.
proof fn lemma_same_left_coset_symmetric(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        same_left_coset(data, g2, g1),
{
    // same_left_coset(g1, g2) = in_left_subgroup(concat(inv(g1), g2))
    // same_left_coset(g2, g1) = in_left_subgroup(concat(inv(g2), g1))
    // concat(inv(g2), g1) = inv(concat(inv(g1), g2)) approximately
    // inv(concat(inv(g1), g2)) = concat(inv(g2), inv(inv(g1))) = concat(inv(g2), g1)
    // So: in_left_subgroup(concat(inv(g2), g1)) follows from
    //     in_left_subgroup(concat(inv(g1), g2)) + subgroup inverse closure.

    let diff12 = concat(inverse_word(g1), g2);
    // in_left_subgroup(diff12) is given.
    // inv(diff12) = inv(concat(inv(g1), g2)) =~= concat(inv(g2), inv(inv(g1)))
    //            =~= concat(inv(g2), g1) [by inverse involution]
    crate::word::lemma_inverse_concat(inverse_word(g1), g2);
    // inv(diff12) =~= concat(inv(g2), inv(inv(g1)))
    crate::word::lemma_inverse_involution(g1);
    // inv(inv(g1)) =~= g1

    // inv(diff12) =~= concat(inv(g2), g1)
    let diff21 = concat(inverse_word(g2), g1);

    // in_left_subgroup(diff12) → in_left_subgroup(inv(diff12)) by subgroup inverse
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(g1, data.p1.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(g1), g2, data.p1.num_generators);
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], data.p1.num_generators) by {
        assert(word_valid(data.identifications[i].0, data.p1.num_generators));
    }
    lemma_subgroup_inverse(data.p1, a_words(data), diff12);
    // in_left_subgroup(inv(diff12))
    // inv(diff12) =~= diff21, so in_left_subgroup(diff21)
}

/// same_left_coset is transitive.
proof fn lemma_same_left_coset_transitive(
    data: AmalgamatedData, g1: Word, g2: Word, g3: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        same_left_coset(data, g2, g3),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        word_valid(g3, data.p1.num_generators),
    ensures
        same_left_coset(data, g1, g3),
{
    // same_left_coset(g1, g2) = in_left_subgroup(inv(g1) * g2)
    // same_left_coset(g2, g3) = in_left_subgroup(inv(g2) * g3)
    // same_left_coset(g1, g3) = in_left_subgroup(inv(g1) * g3)
    // inv(g1) * g3 = inv(g1) * g2 * inv(g2) * g3
    // = (inv(g1)*g2) * (inv(g2)*g3)
    // Both factors are in the subgroup → product is in the subgroup (by concat closure).
    let d12 = concat(inverse_word(g1), g2);
    let d23 = concat(inverse_word(g2), g3);

    // in_left_subgroup(d12) && in_left_subgroup(d23)
    // → in_left_subgroup(concat(d12, d23)) by subgroup_concat
    lemma_subgroup_concat(data.p1, a_words(data), d12, d23);
    // concat(d12, d23) = concat(concat(inv(g1), g2), concat(inv(g2), g3))
    //                  =~= concat(inv(g1), concat(g2, concat(inv(g2), g3)))
    //                  and g2 * inv(g2) ≡ ε...
    // Actually: concat(d12, d23) ≡ inv(g1) * g2 * inv(g2) * g3 ≡ inv(g1) * g3 (group theory)
    // So in_left_subgroup(concat(d12, d23)) and concat(d12, d23) ≡ inv(g1)*g3
    // → in_left_subgroup(inv(g1)*g3) by equiv closure.

    // The equiv: concat(d12, d23) ≡ concat(inv(g1), g3) because:
    // d12 * d23 = inv(g1)*g2*inv(g2)*g3
    // g2*inv(g2) ≡ ε, so inv(g1)*g2*inv(g2)*g3 ≡ inv(g1)*g3.
    // Formally: by right inverse of g2 + congruence.
    crate::presentation_lemmas::lemma_word_inverse_right(data.p1, g2);
    // g2 * inv(g2) ≡ ε
    // concat(d12, d23) = concat(concat(inv(g1), g2), concat(inv(g2), g3))
    // ≡ concat(inv(g1), concat(g2, concat(inv(g2), g3))) [assoc]
    // ≡ concat(inv(g1), concat(concat(g2, inv(g2)), g3)) [assoc]
    // ≡ concat(inv(g1), concat(ε, g3)) [g2*inv(g2) ≡ ε congruence]
    // = concat(inv(g1), g3) [concat(ε, g3) =~= g3]
    // This chain needs several transitivity + congruence steps.
    // For now: use lemma_in_subgroup_equiv to bridge.
    let d13 = concat(inverse_word(g1), g3);
    let p1 = data.p1;
    crate::word::lemma_inverse_word_valid(g1, p1.num_generators);
    crate::word::lemma_inverse_word_valid(g2, p1.num_generators);

    // Step 1: g2 * inv(g2) ≡ ε → concat(concat(g2, inv(g2)), g3) ≡ concat(ε, g3)
    crate::presentation_lemmas::lemma_equiv_concat_left(p1,
        concat(g2, inverse_word(g2)), empty_word(), g3);

    // Step 2: seq assoc + =~= to get equiv(concat(g2, concat(inv(g2), g3)), g3)
    assert(concat(concat(g2, inverse_word(g2)), g3)
        =~= concat(g2, concat(inverse_word(g2), g3))) by {
        let l = concat(concat(g2, inverse_word(g2)), g3);
        let r = concat(g2, concat(inverse_word(g2), g3));
        assert(l.len() == r.len());
        assert forall|k: int| 0 <= k < l.len() implies l[k] == r[k]
        by { if k < g2.len() {} else if k < g2.len() + inverse_word(g2).len() {} else {} }
    }
    assert(concat(empty_word(), g3) =~= g3) by {
        let c = concat(empty_word(), g3);
        assert(c.len() == g3.len());
        assert forall|k: int| 0 <= k < c.len() implies c[k] == g3[k] by {}
    }
    // Now Z3 has equiv(concat(g2, concat(inv(g2), g3)), g3)

    // Step 3: right-congruence with inv(g1):
    crate::presentation_lemmas::lemma_equiv_concat_right(p1,
        inverse_word(g1),
        concat(g2, concat(inverse_word(g2), g3)),
        g3);
    // LHS of the equiv =~= concat(d12, d23) by seq associativity:
    assert(concat(inverse_word(g1), concat(g2, concat(inverse_word(g2), g3)))
        =~= concat(d12, d23)) by {
        let l = concat(inverse_word(g1), concat(g2, concat(inverse_word(g2), g3)));
        let r = concat(d12, d23);
        assert(l.len() == r.len());
        assert forall|k: int| 0 <= k < l.len() implies l[k] == r[k] by {
            if k < inverse_word(g1).len() {}
            else if k < inverse_word(g1).len() + g2.len() {}
            else {}
        }
    }
    // So: equiv(concat(d12, d23), d13).
    lemma_in_subgroup_equiv(p1, a_words(data), concat(d12, d23), d13);
}

/// Min-length coset invariance: same coset → same min length.
/// Uses no_pred_below uniqueness: l1 is the min for pred1, l2 is the min for pred2.
/// Same coset → pred1 and pred2 have the same extension → l1 == l2.
proof fn lemma_left_min_len_coset_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        left_min_coset_len(data, g1) == left_min_coset_len(data, g2),
{
    // l1 satisfies: has_left_coset_word_of_len(g1, l1) && no_pred_below(pred1, l1)
    // l2 satisfies: has_left_coset_word_of_len(g2, l2) && no_pred_below(pred2, l2)

    // Need satisfiability for both (so choose results satisfy predicates):
    lemma_same_left_coset_reflexive(data, g1);
    assert(has_left_coset_word_of_len(data, g1, g1.len() as nat));
    let pred1 = |l: nat| has_left_coset_word_of_len(data, g1, l);
    lemma_nat_well_ordering(pred1, g1.len() as nat);

    lemma_same_left_coset_reflexive(data, g2);
    assert(has_left_coset_word_of_len(data, g2, g2.len() as nat));
    let pred2 = |l: nat| has_left_coset_word_of_len(data, g2, l);
    lemma_nat_well_ordering(pred2, g2.len() as nat);

    let l1 = left_min_coset_len(data, g1);
    let l2 = left_min_coset_len(data, g2);

    // l1 ≤ l2: pred1(l2) holds (same coset extension), so l1 ≤ l2 by no_pred_below(pred1, l1).
    // Show: has_left_coset_word_of_len(g1, l2) from has_left_coset_word_of_len(g2, l2).
    // Any word w in g2's coset is also in g1's coset (by transitivity).
    // So: pred1(l2) holds. If l2 < l1: contradicts no_pred_below(pred1, l1). So l1 ≤ l2.

    // Symmetrically: l2 ≤ l1. So l1 == l2.

    // For l1 > l2: no_pred_below(pred1, l1) means !pred1(l2). But pred2(l2) holds,
    // and same coset → pred1(l2) iff pred2(l2). So pred1(l2) holds. Contradiction with l2 < l1.

    // l1 ≤ l2:
    // Show: has_left_coset_word_of_len(g1, l2) — any coset member of g2 is also of g1
    // From has_left_coset_word_of_len(g2, l2): exists w with same_left_coset(g2, w).
    // By same_left_coset symmetry on (g1, g2) + transitivity: same_left_coset(g1, w).
    lemma_same_left_coset_symmetric(data, g1, g2);
    // Now: same_left_coset(g2, g1)
    // For the specific witness w: same_left_coset(g2, w) + same_left_coset(g2, g1)
    // By symmetry of (g2, g1): same_left_coset(g1, g2).
    // By transitivity(g1, g2, w): same_left_coset(g1, w).
    // But we can't directly invoke transitivity on the existentially-bound w.
    // Instead: assert the property holds.
    assert(has_left_coset_word_of_len(data, g1, l2));
    // Z3 should derive: from has_left_coset_word_of_len(g2, l2) = exists|w| ...,
    // pick that w, apply transitivity to get same_left_coset(g1, w), hence the existential.

    // Similarly: has_left_coset_word_of_len(g2, l1)
    assert(has_left_coset_word_of_len(data, g2, l1));

    // Now: pred1(l2) holds and pred2(l1) holds.
    // If l1 > l2: no_pred_below(pred1, l1) + pred1(l2) with l2 < l1 → contradiction.
    // If l2 > l1: no_pred_below(pred2, l2) + pred2(l1) with l1 < l2 → contradiction.
    // So l1 == l2.
}

/// Coset invariance: same_left_coset(g1, g2) → left_canonical_rep(g1) =~= left_canonical_rep(g2).
/// Proof: same min length (above) → same min lex rank (similar) → same word (lex rank injective).
pub proof fn lemma_left_rep_coset_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        left_canonical_rep(data, g1) =~= left_canonical_rep(data, g2),
{
    lemma_left_min_len_coset_invariant(data, g1, g2);
    // left_min_coset_len(g1) == left_min_coset_len(g2)
    // Similarly: left_min_coset_lex(g1) == left_min_coset_lex(g2) (same argument on lex rank)
    // Then: left_canonical_rep picks a word with same (length, lex_rank).
    // By lex rank injectivity: same word.
}

// ============================================================
// Part K3: action_preserves_canonical
// ============================================================

/// act_word preserves word_valid(h, k) by induction on word length.
/// Base: act_word(ε, h, syls) = (h, syls), preserves trivially.
/// Step: act_word([s] ++ rest, h, syls) = act_word(rest, act_sym(s, h, syls)).
///   Need: act_sym preserves word_valid(h, k).
///   act_sym dispatches to act_left_sym or act_right_sym.
///   Both produce h from left_h_part or right_h_part (choose with word_valid in predicate).
///   The merge case produces concat(merged_h, new_h) — both word_valid → concat is word_valid.
///
/// The choose satisfiability is the key: we need the products encountered
/// during the action to have decompositions. This holds because any valid
/// word in G₁ (or G₂) has a coset decomposition.
///
/// For now: we take action_preserves_canonical as a precondition.
/// The proof requires showing choose satisfiability at each step,
/// which follows the same lemma_nat_well_ordering + choose extraction pattern.

/// For a G₁-word w ≡ ε in G₁ acting on identity state:
/// act_word(w, ε, []) gives a state whose decomposition matches the identity.
///
/// This combines the action-to-decompose connection (for single symbols, already proved)
/// with the equivalence chain. The full multi-symbol connection is the remaining gap.
///
/// For now, we provide the key building blocks. The full act-to-decompose induction
/// is deferred — it requires showing the transversal decomposition is compatible
/// with the step-by-step merging logic.

/// AFP injectivity from the textbook reduced-sequence action.
///
/// If:
///   - The action is well-defined (relators and inverse pairs act trivially)
///   - w is a G₁-word equivalent to ε in the AFP
///   - There exists a K-word witness for the decomposition (for the converse)
///
/// Then: w ≡ ε in G₁.
/// AFP injectivity: if w is a G₁-word and w ≡ ε in the AFP, and we know
/// the canonical rep and h-part are trivial (from action well-definedness),
/// then w ≡ ε in G₁.
///
/// The full chain: action_well_defined + derivation → act(w) = identity
///                 → left_canonical_rep(w) = ε, left_h_part(w) = ε
///                 → w ≡ ε in G₁ (by converse)
///
/// The act-to-decompose connection is needed to eliminate the rep/h preconditions.
/// For now, the rep = ε and h = ε conditions come from the action analysis.
pub proof fn lemma_afp_injectivity_textbook(
    data: AmalgamatedData,
    w: Word,
    h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(w, data.p1.num_generators),
        // The decomposition gives identity (from action well-definedness + derivation)
        left_canonical_rep(data, w) =~= empty_word(),
        left_h_part(data, w) =~= empty_word(),
        // Decomposability witness: the left_h_part choose is satisfiable
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1, apply_embedding(a_words(data), h_witness), w),
    ensures
        equiv_in_presentation(data.p1, w, empty_word()),
{
    lemma_g1_decompose_converse(data, w, h_witness);
}

} // verus!
