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

/// The subgroup part: shortlex-canonical K-word h such that g ≡ concat(rep, embed_a(h)) in G₁.
/// Using shortlex-min ensures canonicity: equivalent g values give the same h.
pub open spec fn left_h_part(data: AmalgamatedData, g: Word) -> Word {
    let rep = left_canonical_rep(data, g);
    // g * rep⁻¹ is in the subgroup. Find the shortlex-min K-word embedding to it.
    choose|h: Word|
        word_valid(h, k_size(data))
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h),
            concat(inverse_word(rep), g))
        && (forall|h2: Word|
            word_valid(h2, k_size(data))
            && equiv_in_presentation(data.p1,
                apply_embedding(a_words(data), h2),
                concat(inverse_word(rep), g))
            ==> !shortlex_lt(h2, h))
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

/// The subgroup part for G₂: shortlex-canonical K-word.
pub open spec fn right_h_part(data: AmalgamatedData, g: Word) -> Word {
    let rep = right_canonical_rep(data, g);
    choose|h: Word|
        word_valid(h, k_size(data))
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h),
            concat(inverse_word(rep), g))
        && (forall|h2: Word|
            word_valid(h2, k_size(data))
            && equiv_in_presentation(data.p2,
                apply_embedding(b_words(data), h2),
                concat(inverse_word(rep), g))
            ==> !shortlex_lt(h2, h))
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
// Part H: Identity state properties
// ============================================================

/// The empty word is shortlex-minimal: nothing is shortlex-smaller.
/// (Already proved in shortlex.rs as lemma_empty_shortlex_minimal.)

/// left_canonical_rep of the empty word (identity element) is the empty word.
/// Because: ε is in ε's coset (reflexive), and ε is shortlex-minimal.
pub proof fn lemma_left_rep_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_canonical_rep(data, empty_word()) =~= empty_word(),
{
    let n1 = data.p1.num_generators;
    let e = empty_word();

    // ε is in its own coset
    lemma_same_left_coset_reflexive(data, e);

    // ε is word_valid
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }

    // Nothing is shortlex-smaller than ε
    // So ε satisfies the choose predicate of left_canonical_rep(data, ε)
    assert forall|rep2: Word|
        word_valid(rep2, n1) && same_left_coset(data, e, rep2)
        implies !shortlex_lt(rep2, e)
    by {
        crate::shortlex::lemma_empty_shortlex_minimal(rep2);
    }

    // ε satisfies the predicate — it IS the choose result.
    // Uniqueness: if rep also satisfies the predicate, then
    //   !shortlex_lt(rep, ε) and !shortlex_lt(ε, rep) [since ε is also in coset]
    //   By totality: rep =~= ε.
    // So choose returns ε.
    let rep = left_canonical_rep(data, e);
    // rep satisfies the predicate too (by choose specification)
    // We need rep =~= ε. By contradiction: if rep ≠ ε, then rep.len() > 0,
    // so shortlex_lt(ε, rep), contradicting "ε is not shortlex-smaller than rep".
    // But rep's predicate says "nothing in coset is smaller than rep".
    // ε IS in the coset. So !shortlex_lt(ε, rep).
    // Also our assertion: !shortlex_lt(rep, ε).
    // By totality: rep =~= ε.
    crate::shortlex::lemma_shortlex_total(e, rep);
}

/// left_h_part of the empty word is the empty K-word.
/// Because: left_canonical_rep(ε) = ε, so inv(rep) ++ ε = ε.
/// embed_a(ε) = ε ≡ ε in G₁. And ε is the shortlex-min such K-word.
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
    let rep = left_canonical_rep(data, e);
    assert(rep =~= e);

    // left_h_part(ε) = choose|h| word_valid(h, k) && equiv(embed_a(h), concat(inv(rep), ε))
    //                            && shortlex-min
    // Since rep =~= ε: inv(rep) =~= ε, concat(inv(rep), ε) =~= ε
    assert(inverse_word(rep) =~= e) by {
        assert(rep =~= e);
        assert(inverse_word(e) =~= e) by {
            assert(inverse_word(e).len() == 0);
        }
    }
    let target = concat(inverse_word(rep), e);
    assert(target =~= e) by {
        assert(inverse_word(rep) =~= e);
        assert(concat(e, e) =~= e) by { assert(concat(e, e).len() == 0); }
    }

    // embed_a(ε) = apply_embedding(a_words, ε) = ε
    assert(apply_embedding(a_words(data), e) =~= e);

    // equiv(p1, embed_a(ε), target) = equiv(p1, ε, ε) = true
    crate::presentation::lemma_equiv_refl(p1, e);
    assert(equiv_in_presentation(p1, e, target));

    // ε is word_valid for k
    assert(word_valid(e, k)) by { assert(e.len() == 0); }

    // ε satisfies the choose predicate of left_h_part
    // And ε is shortlex-min (nothing shorter)
    assert forall|h2: Word|
        word_valid(h2, k)
        && equiv_in_presentation(p1, apply_embedding(a_words(data), h2), target)
        implies !shortlex_lt(h2, e)
    by {
        crate::shortlex::lemma_empty_shortlex_minimal(h2);
    }

    // By same uniqueness argument as lemma_left_rep_identity:
    let h = left_h_part(data, e);
    crate::shortlex::lemma_shortlex_total(e, h);
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
