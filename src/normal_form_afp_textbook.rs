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

/// Does the left A-coset of g contain a valid word of length l?
pub open spec fn has_left_coset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g, w) && w.len() == l
}

/// Minimum length of any valid word in g's left A-coset.
pub open spec fn left_min_coset_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] has_left_coset_word_of_len(data, g, l)
        && no_pred_below(|l2: nat| has_left_coset_word_of_len(data, g, l2), l)
}

/// Canonical coset representative: a word of minimum length in g's coset.
/// For length 0: only ε has length 0, so the rep IS ε when min length is 0.
/// For same coset: same min length, same choose predicate → same result (extensionality).
pub open spec fn left_canonical_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = left_min_coset_len(data, g);
    choose|rep: Word|
        word_valid(rep, data.p1.num_generators)
        && same_left_coset(data, g, rep)
        && rep.len() == l
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
/// left_canonical_rep(g) is in g's coset and word_valid.
proof fn lemma_left_rep_props(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        same_left_coset(data, g, left_canonical_rep(data, g)),
        word_valid(left_canonical_rep(data, g), data.p1.num_generators),
{
    // g is in its own coset → has_left_coset_word_of_len(g, g.len())
    lemma_same_left_coset_reflexive(data, g);
    assert(has_left_coset_word_of_len(data, g, g.len() as nat));
    // So left_min_coset_len's choose is satisfiable.
    // And left_canonical_rep's choose (word at min length in coset) is satisfiable.
    // g itself witnesses this. The result satisfies the predicate.
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
    // h_witness satisfies the choose predicate for left_h_part(g).
    // The choose returned ε. Since h_witness satisfies, the predicate IS satisfiable.
    // The choose result (ε) also satisfies: equiv(p1, embed_a(ε), target)
    // With embed_a(ε) = ε and target =~= g: equiv(p1, ε, g)
    // By symmetry: equiv(p1, g, ε)

    // equiv_symmetric needs word_valid(ε, n1) which is trivial
    assert(word_valid(empty_word(), data.p1.num_generators)) by {
        assert(empty_word().len() == 0);
    }
    // Z3 should see: left_h_part(g) = ε, the choose is satisfiable (h_witness),
    // so ε satisfies the predicate, giving equiv(embed_a(ε), target) = equiv(ε, g).
    // Then symmetry: equiv(g, ε).
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

    // left_canonical_rep(ε) is a word of length 0 in ε's coset.
    // Any word of length 0 is ε.
    let rep = left_canonical_rep(data, e);
    // rep satisfies: word_valid(rep, n1) && same_left_coset(ε, rep) && rep.len() == 0
    // (from the choose, since it IS satisfiable — ε itself works)
    lemma_same_left_coset_reflexive(data, e);
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }
    // ε satisfies the choose predicate: word_valid(ε, n1) && same_left_coset(ε, ε) && ε.len() == 0
    // So the choose is satisfiable and rep satisfies the predicate, in particular rep.len() == 0.
    // Any seq of length 0 equals ε.
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

/// Inserting a word at a position preserves the action if the word acts trivially.
///
/// If act_word(middle, h, syls) == (h, syls) for all h, syls:
///   act_word(prefix ++ middle ++ suffix, h, syls) == act_word(prefix ++ suffix, h, syls)
///
/// This follows from composition: split at the insertion point,
/// the middle acts as identity, and the rest is unchanged.
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
    // By composition: act(prefix ++ middle ++ suffix)
    //   = act(middle ++ suffix, act(prefix))
    //   = act(suffix, act(middle, act(prefix)))
    //   = act(suffix, act(prefix))  [since middle acts trivially]
    //   = act(prefix ++ suffix)
    lemma_act_word_concat(data, prefix, concat(middle, suffix), h, syllables);
    let (ph, ps) = act_word(data, prefix, h, syllables);
    lemma_act_word_concat(data, middle, suffix, ph, ps);
    // act(middle, ph, ps) == act(ε, ph, ps) = (ph, ps)
    // So act(middle ++ suffix, ph, ps) = act(suffix, act(middle, ph, ps)) = act(suffix, ph, ps)
    lemma_act_word_concat(data, prefix, suffix, h, syllables);
    // act(prefix ++ suffix) = act(suffix, ph, ps)
    // Both sides equal act(suffix, ph, ps). QED.
}

} // verus!
