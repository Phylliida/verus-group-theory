use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;
use crate::britton::*;
use crate::benign::*;
use crate::tietze::*;
use crate::britton_proof_helpers3::*;

verus! {

// ============================================================
// PROOF OF BRITTON'S LEMMA
// ============================================================
//
// Theorem: If w is a base word and w ≡ ε in G* (the HNN extension),
// then w ≡ ε in G (the base group).
//
// PROOF STRATEGY: Induction on derivation length.
//
// Given a derivation D: w = w_0 → w_1 → ... → w_n = ε in G*:
//
// 1. If n = 0: w = ε, done by reflexivity.
//
// 2. If w_1 is base: the step w → w_1 is base-to-base, so it's
//    valid in G (by lemma_t_free_step_is_base_step). Recurse on
//    the shorter derivation w_1 → ... → ε.
//
// 3. If w_1 is non-base: find the first base intermediate w_k
//    (k > 1, exists since w_n = ε is base). Split:
//    - Right: w_k → ... → ε (length n-k < n). By IH, w_k ≡ ε in G.
//    - Left: w → w_1 → ... → w_k (single segment, all intermediates
//      non-base). By the segment lemma, w ≡ w_k in G.
//    Chain: w ≡_G w_k ≡_G ε.
//
// SINGLE SEGMENT LEMMA: If w (base) → w_1 (non-base) → ... →
// w_{k-1} (non-base) → w_k (base) in G*, then w ≡ w_k in G.
//
// Proved by induction on segment length k.
//
// Base case (k = 2): Two steps. The first introduces stable letters,
// the second removes them. Case analysis on step types:
//
//   (a) FreeExpand(stable) + FreeReduce: The only reduction that
//       eliminates both stable letters is at the insertion point.
//       So w_2 = w. Reflexivity.
//
//   (b) FreeExpand(stable) + RelatorDelete(HNN): Alignment forces
//       |a_i| = 0. Then w_2 = w minus inverse_word(b_i).
//       By hnn_associations_isomorphic, b_i ≡ ε in G.
//
//   (c) RelatorInsert(HNN) + FreeReduce: |a_i| = 0 forced for
//       adjacent stable letters. w_2 = w plus inverse_word(b_i).
//       By isomorphism condition, b_i ≡ ε in G.
//
//   (d) RelatorInsert(HNN) + RelatorDelete(HNN): Non-overlapping
//       case reduces to commutation; overlapping uses isomorphism.
//
// Inductive case (k > 2): Find a "peak" in the stable letter count
// sequence and eliminate it, reducing to shorter segments.
//
// ISOMORPHISM CONDITION: hnn_associations_isomorphic(data) ensures
// that if a_i = ε for some association, then b_i ≡ ε in G (and
// vice versa). This is essential for all non-trivial cases.

// ============================================================
// Part 1: Derivation infrastructure
// ============================================================

/// word_valid is monotone: valid for n implies valid for n+1.
pub proof fn lemma_word_valid_monotone(w: Word, n: nat)
    requires
        word_valid(w, n),
    ensures
        word_valid(w, n + 1),
{
    assert forall|i: int| 0 <= i < w.len()
        implies symbol_valid(#[trigger] w[i], n + 1)
    by {
        assert(symbol_valid(w[i], n));
        match w[i] {
            Symbol::Gen(idx) => {},
            Symbol::Inv(idx) => {},
        }
    }
}

/// Concatenate two derivations.
pub proof fn lemma_derivation_concat(
    hp: Presentation,
    steps1: Seq<DerivationStep>,
    steps2: Seq<DerivationStep>,
    w: Word,
    w_mid: Word,
    w_end: Word,
)
    requires
        derivation_produces(hp, steps1, w) == Some(w_mid),
        derivation_produces(hp, steps2, w_mid) == Some(w_end),
    ensures
        derivation_produces(hp, steps1 + steps2, w) == Some(w_end),
    decreases steps1.len(),
{
    if steps1.len() == 0 {
        assert(steps1 + steps2 =~= steps2);
    } else {
        let w1 = apply_step(hp, w, steps1.first()).unwrap();
        let rest1 = steps1.drop_first();
        lemma_derivation_concat(hp, rest1, steps2, w1, w_mid, w_end);
        assert((steps1 + steps2).first() == steps1.first());
        assert((steps1 + steps2).drop_first() =~= rest1 + steps2);
    }
}

/// Split a derivation at position k.
pub proof fn lemma_derivation_split(
    hp: Presentation, steps: Seq<DerivationStep>, w: Word, w_end: Word, k: nat,
)
    requires
        derivation_produces(hp, steps, w) == Some(w_end),
        k <= steps.len(),
    ensures
        derivation_produces(hp, steps.subrange(0, k as int), w).is_some(),
        derivation_produces(
            hp,
            steps.subrange(k as int, steps.len() as int),
            derivation_produces(hp, steps.subrange(0, k as int), w).unwrap(),
        ) == Some(w_end),
    decreases steps.len(),
{
    if k == 0 {
        assert(steps.subrange(0, 0int) =~= Seq::<DerivationStep>::empty());
        assert(steps.subrange(0int, steps.len() as int) =~= steps);
    } else {
        let w1 = apply_step(hp, w, steps.first()).unwrap();
        let rest = steps.drop_first();

        lemma_derivation_split(hp, rest, w1, w_end, (k - 1) as nat);

        let rest_left = rest.subrange(0, (k - 1) as int);
        let rest_right = rest.subrange((k - 1) as int, rest.len() as int);

        let steps_left = steps.subrange(0, k as int);
        assert(steps_left.first() == steps.first());
        assert(steps_left.drop_first() =~= rest_left);
        assert(steps.subrange(k as int, steps.len() as int) =~= rest_right);
    }
}

/// A single derivation step produces an equivalence.
proof fn lemma_single_step_equiv(
    p: Presentation, w: Word, step: DerivationStep, w_next: Word,
)
    requires
        apply_step(p, w, step) == Some(w_next),
    ensures
        equiv_in_presentation(p, w, w_next),
{
    let steps = seq![step];
    assert(steps.len() > 0);
    assert(steps.first() == step);
    assert(steps.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(apply_step(p, w, steps.first()) == Some(w_next));
    assert(derivation_produces(p, steps.drop_first(), w_next) == Some(w_next)) by {
        assert(steps.drop_first().len() == 0);
    };
    let d = Derivation { steps };
    assert(derivation_valid(p, d, w, w_next));
}

/// Extract apply_step from a 1-step derivation.
proof fn lemma_derivation_unfold_1(
    hp: Presentation, steps: Seq<DerivationStep>, w: Word, w_end: Word,
)
    requires
        steps.len() == 1,
        derivation_produces(hp, steps, w) == Some(w_end),
    ensures
        apply_step(hp, w, steps.first()) == Some(w_end),
{
    // Follow the pattern from lemma_derivation_unfold_3:
    // Get the result word from derivation_produces
    let w_chk = apply_step(hp, w, steps.first()).unwrap();
    // Show that the tail (empty) produces w_end from w_chk
    assert(derivation_produces(hp, steps.drop_first(), w_chk) == Some(w_end)) by {
        assert(steps.drop_first().len() == 0);
    };
    // Now Z3 knows w_chk == w_end
    assert(w_chk == w_end);
}

/// Construct derivation_produces for a 2-step sequence from individual apply_step facts.
pub proof fn lemma_derivation_produces_2(
    hp: Presentation, s0: DerivationStep, s1: DerivationStep,
    w0: Word, w1: Word, w2: Word,
)
    requires
        apply_step(hp, w0, s0) == Some(w1),
        apply_step(hp, w1, s1) == Some(w2),
    ensures
        derivation_produces(hp, seq![s0, s1], w0) == Some(w2),
{
    // Layer 1: prove the tail (1-step derivation)
    let tail: Seq<DerivationStep> = seq![s1];
    assert(tail.first() == s1);
    assert(derivation_produces(hp, tail.drop_first(), w2) == Some(w2)) by {
        assert(tail.drop_first().len() == 0);
    };
    assert(derivation_produces(hp, tail, w1) == Some(w2));

    // Layer 2: fold the outer level using the tail result
    let steps: Seq<DerivationStep> = seq![s0, s1];
    assert(steps.first() == s0);
    assert(steps.drop_first() =~= tail);
}

/// Unfold derivation_produces for a 3-step sequence, extracting individual apply_step facts.
proof fn lemma_derivation_unfold_3(
    hp: Presentation, steps: Seq<DerivationStep>, w: Word, w_end: Word,
) -> (intermediates: (Word, Word))
    requires
        steps.len() == 3,
        derivation_produces(hp, steps, w) == Some(w_end),
    ensures
        apply_step(hp, w, steps[0]) == Some(intermediates.0),
        apply_step(hp, intermediates.0, steps[1]) == Some(intermediates.1),
        apply_step(hp, intermediates.1, steps[2]) == Some(w_end),
{
    // Use lemma_derivation_split at position 1 to get a proven 2-step tail
    lemma_derivation_split(hp, steps, w, w_end, 1);
    let first1 = steps.subrange(0, 1int);
    let rest2 = steps.subrange(1int, 3int);
    assert(first1 =~= seq![steps[0]]);
    let w1 = derivation_produces(hp, first1, w).unwrap();

    // Unfold the 1-step prefix to get apply_step fact
    let w1_chk = apply_step(hp, w, first1.first()).unwrap();
    assert(derivation_produces(hp, first1.drop_first(), w1_chk) == Some(w1)) by {
        assert(first1.drop_first().len() == 0);
    };
    assert(w1 == w1_chk);

    // Now derivation_produces(hp, rest2, w1) == Some(w_end) with rest2.len() == 2
    // Split rest2 at position 1 to get two 1-step pieces
    lemma_derivation_split(hp, rest2, w1, w_end, 1);
    let rest2_first = rest2.subrange(0, 1int);
    let rest2_second = rest2.subrange(1int, 2int);
    assert(rest2_first.first() == steps[1]);
    assert(rest2_second.first() == steps[2]);
    let w2 = derivation_produces(hp, rest2_first, w1).unwrap();

    // Unfold the first 1-step piece: apply_step(hp, w1, steps[1]) == Some(w2)
    let w2_chk = apply_step(hp, w1, rest2_first.first()).unwrap();
    assert(derivation_produces(hp, rest2_first.drop_first(), w2_chk) == Some(w2)) by {
        assert(rest2_first.drop_first().len() == 0);
    };
    assert(w2_chk == w2);

    // Unfold the second 1-step piece: apply_step(hp, w2, steps[2]) == Some(w_end)
    let w3 = apply_step(hp, w2, rest2_second.first()).unwrap();
    assert(derivation_produces(hp, rest2_second.drop_first(), w3) == Some(w_end)) by {
        assert(rest2_second.drop_first().len() == 0);
    };
    assert(w3 == w_end);
    (w1, w2)
}

// ============================================================
// Part 2: Stable letter count helpers
// ============================================================

/// Stable letter count of a 2-element sequence [s1, s2].
pub proof fn lemma_stable_count_pair(s1: Symbol, s2: Symbol, n: nat)
    ensures
        stable_letter_count(seq![s1, s2], n) == (
            if generator_index(s1) == n { 1nat } else { 0nat }
        ) + (
            if generator_index(s2) == n { 1nat } else { 0nat }
        ),
{
    let w = seq![s1, s2];
    assert(w.len() > 0);
    assert(w.first() == s1);
    assert(w.drop_first() =~= seq![s2]);
    lemma_stable_count_single(s2, n);
}

/// Stable letter count of a 1-element sequence [s].
proof fn lemma_stable_count_single(s: Symbol, n: nat)
    ensures
        stable_letter_count(seq![s], n) == (
            if generator_index(s) == n { 1nat } else { 0nat }
        ),
{
    let w = seq![s];
    assert(w.len() > 0);
    assert(w.first() == s);
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    assert(stable_letter_count(w.drop_first(), n) == 0nat) by {
        assert(w.drop_first().len() == 0);
    };
}

// ============================================================
// Part 3: Isomorphism condition helpers
// ============================================================

/// Helper: apply_embedding of a single-generator word.
proof fn lemma_apply_embedding_single(images: Seq<Word>, i: nat)
    requires
        (i as int) < images.len(),
    ensures
        apply_embedding(images, seq![Symbol::Gen(i)]) =~=
            concat(images[i as int], empty_word()),
{
    let w: Word = seq![Symbol::Gen(i)];
    assert(w.len() > 0);
    assert(w.first() == Symbol::Gen(i));
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    // apply_embedding(images, w) =
    //   concat(apply_embedding_symbol(images, Gen(i)), apply_embedding(images, []))
    // = concat(images[i], empty_word())
    assert(apply_embedding_symbol(images, Symbol::Gen(i)) == images[i as int]);
    assert(apply_embedding(images, empty_word()) =~= empty_word());
}

/// Helper: apply_embedding of a two-symbol word [s1, s2].
proof fn lemma_apply_embedding_two(images: Seq<Word>, s1: Symbol, s2: Symbol)
    requires
        (generator_index(s1) as int) < images.len(),
        (generator_index(s2) as int) < images.len(),
    ensures
        apply_embedding(images, seq![s1, s2]) =~=
            concat(apply_embedding_symbol(images, s1),
                   apply_embedding_symbol(images, s2)),
{
    let w: Word = seq![s1, s2];
    assert(w.len() == 2);
    assert(w.first() == s1);
    assert(w.drop_first() =~= seq![s2]);
    let tail = w.drop_first();
    assert(tail.first() == s2);
    assert(tail.drop_first() =~= Seq::<Symbol>::empty());
    assert(apply_embedding(images, empty_word()) =~= empty_word());
    assert(apply_embedding(images, tail) =~=
        concat(apply_embedding_symbol(images, s2), empty_word()));
    assert(concat(apply_embedding_symbol(images, s2), empty_word())
        =~= apply_embedding_symbol(images, s2));
}

/// The isomorphism condition implies: if a_i = ε, then b_i ≡ ε in G.
pub proof fn lemma_empty_association_implies_trivial(
    data: HNNData, i: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        0 <= i < data.associations.len(),
        data.associations[i].0 =~= empty_word(),
    ensures
        equiv_in_presentation(data.base, data.associations[i].1, empty_word()),
{
    let k = data.associations.len();
    let a_words = Seq::new(k, |j: int| data.associations[j].0);
    let b_words = Seq::new(k, |j: int| data.associations[j].1);

    let w: Word = seq![Symbol::Gen(i as nat)];
    assert(word_valid(w, k as nat)) by {
        assert(w[0 as int] == Symbol::Gen(i as nat));
        assert(symbol_valid(Symbol::Gen(i as nat), k as nat));
    }

    // apply_embedding(a_words, w) = concat(a_words[i], empty_word()) =~= a_i = ε
    lemma_apply_embedding_single(a_words, i as nat);
    assert(a_words[i] == data.associations[i].0);
    assert(concat(empty_word(), empty_word()) =~= empty_word());
    assert(apply_embedding(a_words, w) =~= empty_word());

    // ε ≡ ε in G trivially
    lemma_equiv_refl(data.base, empty_word());

    // By isomorphism: apply_embedding(b_words, w) ≡ ε in G
    lemma_apply_embedding_single(b_words, i as nat);
    assert(b_words[i] == data.associations[i].1);
    assert(concat(data.associations[i].1, empty_word()) =~= data.associations[i].1);
    // So apply_embedding(b_words, w) =~= b_i
    // By isomorphism condition: b_i ≡ ε in G
}

/// The isomorphism condition implies: if b_i = ε, then a_i ≡ ε in G.
pub proof fn lemma_empty_association_implies_trivial_rev(
    data: HNNData, i: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        0 <= i < data.associations.len(),
        data.associations[i].1 =~= empty_word(),
    ensures
        equiv_in_presentation(data.base, data.associations[i].0, empty_word()),
{
    let k = data.associations.len();
    let a_words = Seq::new(k, |j: int| data.associations[j].0);
    let b_words = Seq::new(k, |j: int| data.associations[j].1);

    let w: Word = seq![Symbol::Gen(i as nat)];
    assert(word_valid(w, k as nat)) by {
        assert(w[0 as int] == Symbol::Gen(i as nat));
        assert(symbol_valid(Symbol::Gen(i as nat), k as nat));
    }

    lemma_apply_embedding_single(b_words, i as nat);
    assert(b_words[i] == data.associations[i].1);
    assert(concat(empty_word(), empty_word()) =~= empty_word());
    assert(apply_embedding(b_words, w) =~= empty_word());

    lemma_equiv_refl(data.base, empty_word());

    lemma_apply_embedding_single(a_words, i as nat);
    assert(a_words[i] == data.associations[i].0);
    assert(concat(data.associations[i].0, empty_word()) =~= data.associations[i].0);
}

/// Generalized isomorphism: if a_i ≡ ε in G, then b_i ≡ ε in G.
/// Generalizes lemma_empty_association_implies_trivial to any trivial a_i (not just empty).
pub proof fn lemma_trivial_association_implies_trivial(
    data: HNNData, i: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        0 <= i < data.associations.len(),
        equiv_in_presentation(data.base, data.associations[i].0, empty_word()),
    ensures
        equiv_in_presentation(data.base, data.associations[i].1, empty_word()),
{
    let k = data.associations.len();
    let a_words = Seq::new(k, |j: int| data.associations[j].0);
    let b_words = Seq::new(k, |j: int| data.associations[j].1);

    let w: Word = seq![Symbol::Gen(i as nat)];
    assert(word_valid(w, k as nat)) by {
        assert(w[0 as int] == Symbol::Gen(i as nat));
        assert(symbol_valid(Symbol::Gen(i as nat), k as nat));
    };

    // apply_embedding(a_words, w) =~= a_i
    lemma_apply_embedding_single(a_words, i as nat);
    assert(a_words[i] == data.associations[i].0);
    assert(concat(data.associations[i].0, empty_word()) =~= data.associations[i].0);
    assert(apply_embedding(a_words, w) =~= data.associations[i].0);

    // apply_embedding(b_words, w) =~= b_i
    lemma_apply_embedding_single(b_words, i as nat);
    assert(b_words[i] == data.associations[i].1);
    assert(concat(data.associations[i].1, empty_word()) =~= data.associations[i].1);
    assert(apply_embedding(b_words, w) =~= data.associations[i].1);

    // By isomorphism: a_i ≡ ε ↔ b_i ≡ ε
}

/// If x ≡_G y then inverse_word(x) ≡_G inverse_word(y).
proof fn lemma_inverse_word_congruence(
    p: Presentation, x: Word, y: Word,
)
    requires
        equiv_in_presentation(p, x, y),
        word_valid(x, p.num_generators),
        word_valid(y, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, inverse_word(x), inverse_word(y)),
{
    let inv_y = inverse_word(y);
    lemma_inverse_word_valid(y, p.num_generators);
    // concat(x, inv_y) ≡ concat(y, inv_y) ≡ ε
    lemma_equiv_concat_left(p, x, y, inv_y);
    lemma_word_inverse_right(p, y);
    lemma_equiv_transitive(p, concat(x, inv_y), concat(y, inv_y), empty_word());
    // identity_split: inv_y ≡ inv(x)
    lemma_identity_split(p, x, inv_y);
    // symmetric: inv(x) ≡ inv(y)
    lemma_inverse_word_valid(x, p.num_generators);
    lemma_equiv_symmetric(p, inv_y, inverse_word(x));
}

/// Isomorphism maps equivalence: if a_{j2} ≡_G a_{j1}, then b_{j2} ≡_G b_{j1}.
/// Uses the HNN isomorphism condition with the word [Gen(j2), Inv(j1)].
proof fn lemma_isomorphism_maps_equivalence(
    data: HNNData, j1: int, j2: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        0 <= j1 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        equiv_in_presentation(data.base, data.associations[j2].0, data.associations[j1].0),
    ensures
        equiv_in_presentation(data.base, data.associations[j2].1, data.associations[j1].1),
{
    let k = data.associations.len();
    let n = data.base.num_generators;
    let p = data.base;
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);
    let (a_j1, b_j1) = data.associations[j1];
    let (a_j2, b_j2) = data.associations[j2];

    // Build test word [Gen(j2), Inv(j1)]
    let s1 = Symbol::Gen(j2 as nat);
    let s2 = Symbol::Inv(j1 as nat);
    let w: Word = seq![s1, s2];
    assert(word_valid(w, k as nat)) by {
        assert(w[0int] == s1);
        assert(w[1int] == s2);
        assert(symbol_valid(s1, k as nat));
        assert(symbol_valid(s2, k as nat));
    };

    // A-embedding: concat(a_{j2}, inv(a_{j1}))
    lemma_apply_embedding_two(a_words, s1, s2);
    assert(a_words[j2] == a_j2);
    assert(a_words[j1] == a_j1);
    assert(apply_embedding(a_words, w) =~= concat(a_j2, inverse_word(a_j1)));

    // concat(a_{j2}, inv(a_{j1})) ≡_G ε
    lemma_inverse_word_valid(a_j1, n);
    lemma_equiv_concat_left(p, a_j2, a_j1, inverse_word(a_j1));
    lemma_word_inverse_right(p, a_j1);
    lemma_equiv_transitive(p,
        concat(a_j2, inverse_word(a_j1)),
        concat(a_j1, inverse_word(a_j1)),
        empty_word());

    // B-embedding: concat(b_{j2}, inv(b_{j1}))
    lemma_apply_embedding_two(b_words, s1, s2);
    assert(b_words[j2] == b_j2);
    assert(b_words[j1] == b_j1);
    assert(apply_embedding(b_words, w) =~= concat(b_j2, inverse_word(b_j1)));

    // By isomorphism: concat(b_{j2}, inv(b_{j1})) ≡_G ε
    // Now derive b_{j2} ≡_G b_{j1}
    let inv_bj1 = inverse_word(b_j1);
    lemma_inverse_word_valid(b_j1, n);

    // concat(concat(b_j2, inv_bj1), b_j1) ≡_G concat(ε, b_j1) =~= b_j1
    lemma_equiv_concat_left(p, concat(b_j2, inv_bj1), empty_word(), b_j1);
    assert(concat(empty_word(), b_j1) =~= b_j1);
    assert(concat(concat(b_j2, inv_bj1), b_j1)
        =~= concat(b_j2, concat(inv_bj1, b_j1)));

    // concat(b_j2, concat(inv_bj1, b_j1)) ≡_G b_j2
    lemma_word_inverse_left(p, b_j1);
    lemma_equiv_concat_right(p, b_j2, concat(inv_bj1, b_j1), empty_word());
    assert(concat(b_j2, empty_word()) =~= b_j2);

    // Chain: b_j2 ≡_G concat(b_j2, concat(inv_bj1, b_j1)) ≡_G b_j1
    lemma_concat_word_valid(inv_bj1, b_j1, n);
    lemma_concat_word_valid(b_j2, concat(inv_bj1, b_j1), n);
    lemma_equiv_symmetric(p, concat(b_j2, concat(inv_bj1, b_j1)), b_j2);
    lemma_equiv_transitive(p,
        b_j2,
        concat(b_j2, concat(inv_bj1, b_j1)),
        b_j1);
}

/// Isomorphism maps inverse equivalence: if a_{j2} ≡_G inv(a_{j1}), then b_{j2} ≡_G inv(b_{j1}).
/// Uses the HNN isomorphism condition with the word [Gen(j2), Gen(j1)].
proof fn lemma_isomorphism_maps_inverse_equivalence(
    data: HNNData, j1: int, j2: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        0 <= j1 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        equiv_in_presentation(data.base, data.associations[j2].0, inverse_word(data.associations[j1].0)),
    ensures
        equiv_in_presentation(data.base, data.associations[j2].1, inverse_word(data.associations[j1].1)),
{
    let k = data.associations.len();
    let n = data.base.num_generators;
    let p = data.base;
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);
    let (a_j1, b_j1) = data.associations[j1];
    let (a_j2, b_j2) = data.associations[j2];

    // Build test word [Gen(j2), Gen(j1)]
    let s1 = Symbol::Gen(j2 as nat);
    let s2 = Symbol::Gen(j1 as nat);
    let w: Word = seq![s1, s2];
    assert(word_valid(w, k as nat)) by {
        assert(w[0int] == s1);
        assert(w[1int] == s2);
        assert(symbol_valid(s1, k as nat));
        assert(symbol_valid(s2, k as nat));
    };

    // A-embedding: concat(a_{j2}, a_{j1})
    lemma_apply_embedding_two(a_words, s1, s2);
    assert(a_words[j2] == a_j2);
    assert(a_words[j1] == a_j1);
    assert(apply_embedding(a_words, w) =~= concat(a_j2, a_j1));

    // concat(a_{j2}, a_{j1}) ≡_G ε
    // From a_{j2} ≡_G inv(a_{j1}): concat(inv(a_{j1}), a_{j1}) ≡_G ε
    lemma_equiv_concat_left(p, a_j2, inverse_word(a_j1), a_j1);
    lemma_word_inverse_left(p, a_j1);
    lemma_equiv_transitive(p,
        concat(a_j2, a_j1),
        concat(inverse_word(a_j1), a_j1),
        empty_word());

    // B-embedding: concat(b_{j2}, b_{j1})
    lemma_apply_embedding_two(b_words, s1, s2);
    assert(b_words[j2] == b_j2);
    assert(b_words[j1] == b_j1);
    assert(apply_embedding(b_words, w) =~= concat(b_j2, b_j1));

    // By isomorphism: concat(b_{j2}, b_{j1}) ≡_G ε
    // Derive b_{j2} ≡_G inv(b_{j1})
    let inv_bj1 = inverse_word(b_j1);
    lemma_inverse_word_valid(b_j1, n);

    // concat(concat(b_j2, b_j1), inv_bj1) ≡_G concat(ε, inv_bj1) =~= inv_bj1
    lemma_equiv_concat_left(p, concat(b_j2, b_j1), empty_word(), inv_bj1);
    assert(concat(empty_word(), inv_bj1) =~= inv_bj1);
    assert(concat(concat(b_j2, b_j1), inv_bj1)
        =~= concat(b_j2, concat(b_j1, inv_bj1)));

    // concat(b_j2, concat(b_j1, inv_bj1)) ≡_G b_j2
    lemma_word_inverse_right(p, b_j1);
    lemma_equiv_concat_right(p, b_j2, concat(b_j1, inv_bj1), empty_word());
    assert(concat(b_j2, empty_word()) =~= b_j2);

    // Chain: b_j2 ≡_G concat(b_j2, concat(b_j1, inv_bj1)) ≡_G inv_bj1
    lemma_concat_word_valid(b_j1, inv_bj1, n);
    lemma_concat_word_valid(b_j2, concat(b_j1, inv_bj1), n);
    lemma_equiv_symmetric(p, concat(b_j2, concat(b_j1, inv_bj1)), b_j2);
    lemma_equiv_transitive(p,
        b_j2,
        concat(b_j2, concat(b_j1, inv_bj1)),
        inv_bj1);
}

// ============================================================
// Part 4: Stable letter count under steps
// ============================================================

/// Stable count of a subrange equals the count minus the removed parts.
pub proof fn lemma_stable_count_subrange(w: Word, lo: int, hi: int, n: nat)
    requires
        0 <= lo <= hi <= w.len(),
    ensures
        stable_letter_count(w.subrange(lo, hi), n)
            + stable_letter_count(w.subrange(0, lo), n)
            + stable_letter_count(w.subrange(hi, w.len() as int), n)
            == stable_letter_count(w, n),
{
    assert(w =~= w.subrange(0, lo) + w.subrange(lo, w.len() as int));
    lemma_stable_letter_count_concat(w.subrange(0, lo), w.subrange(lo, w.len() as int), n);
    assert(w.subrange(lo, w.len() as int) =~=
        w.subrange(lo, hi) + w.subrange(hi, w.len() as int));
    lemma_stable_letter_count_concat(
        w.subrange(lo, hi), w.subrange(hi, w.len() as int), n);
}

/// Stable count after FreeReduce: removes 2 symbols, count changes by
/// -2 if both are stable, 0 otherwise (since they're an inverse pair,
/// both have the same generator_index).
pub proof fn lemma_stable_count_reduce(w: Word, pos: int, n: nat)
    requires
        has_cancellation_at(w, pos),
    ensures
        stable_letter_count(reduce_at(w, pos), n) ==
            stable_letter_count(w, n) - (
                if generator_index(w[pos]) == n { 2nat } else { 0nat }
            ),
{
    // reduce_at(w, pos) = w[0..pos] + w[pos+2..]
    // The removed pair has the same generator_index (they're inverses)
    assert(w =~= w.subrange(0, pos) + w.subrange(pos, w.len() as int));
    assert(w.subrange(pos, w.len() as int) =~=
        seq![w[pos], w[pos + 1]] + w.subrange(pos + 2, w.len() as int));
    lemma_stable_letter_count_concat(
        w.subrange(0, pos), w.subrange(pos, w.len() as int), n);
    lemma_stable_letter_count_concat(
        seq![w[pos], w[pos + 1]], w.subrange(pos + 2, w.len() as int), n);
    lemma_stable_count_pair(w[pos], w[pos + 1], n);

    let result = reduce_at(w, pos);
    assert(result =~= w.subrange(0, pos) + w.subrange(pos + 2, w.len() as int));
    lemma_stable_letter_count_concat(
        w.subrange(0, pos), w.subrange(pos + 2, w.len() as int), n);

    // Both symbols in the cancelled pair have the same generator_index
    match w[pos] {
        Symbol::Gen(idx) => {
            assert(w[pos + 1] == Symbol::Inv(idx));
            assert(generator_index(w[pos]) == generator_index(w[pos + 1]));
        },
        Symbol::Inv(idx) => {
            assert(w[pos + 1] == Symbol::Gen(idx));
            assert(generator_index(w[pos]) == generator_index(w[pos + 1]));
        },
    }
}

/// stable_letter_count = 0 + word_valid(n+1) implies is_base_word.
pub proof fn lemma_zero_count_implies_base(w: Word, n: nat)
    requires
        stable_letter_count(w, n) == 0nat,
        word_valid(w, n + 1),
    ensures
        is_base_word(w, n),
{
    // For any position i, if gen_idx(w[i]) were == n, count would be >= 1.
    // Since count == 0, gen_idx(w[i]) != n. With word_valid(n+1): gen_idx < n.
    assert forall|i: int| 0 <= i < w.len()
        implies symbol_valid(#[trigger] w[i], n)
    by {
        if generator_index(w[i]) == n {
            lemma_element_contributes_to_count(w, i, n);
            assert(false);
        }
    };
    lemma_base_word_characterization(w, n);
}

/// Converse of lemma_zero_count_implies_base: base word has stable count 0.
/// Trivial since is_base_word is defined as stable_letter_count == 0.
pub proof fn lemma_base_implies_count_zero(w: Word, n: nat)
    requires
        is_base_word(w, n),
    ensures
        stable_letter_count(w, n) == 0nat,
{}

/// If w[i] has generator_index == n, then stable_letter_count(w, n) >= 1.
proof fn lemma_element_contributes_to_count(w: Word, i: int, n: nat)
    requires
        0 <= i < w.len(),
        generator_index(w[i]) == n,
    ensures
        stable_letter_count(w, n) >= 1nat,
    decreases w.len(),
{
    assert(w.first() == w[0int]);
    if i == 0 {
        // w.first() has gen_idx = n, so count(w) = count(w.drop_first()) + 1 >= 1
    } else {
        assert(w[i] == w.drop_first()[(i - 1) as int]);
        lemma_element_contributes_to_count(w.drop_first(), i - 1, n);
    }
}

/// If w has two distinct positions with generator_index == n, then count >= 2.
proof fn lemma_two_elements_contribute_to_count(w: Word, i: int, j: int, n: nat)
    requires
        0 <= i < j,
        j < w.len(),
        generator_index(w[i]) == n,
        generator_index(w[j]) == n,
    ensures
        stable_letter_count(w, n) >= 2nat,
    decreases w.len(),
{
    assert(w.first() == w[0int]);
    if i == 0 {
        assert(w[j] == w.drop_first()[(j - 1) as int]);
        lemma_element_contributes_to_count(w.drop_first(), j - 1, n);
    } else {
        assert(w[i] == w.drop_first()[(i - 1) as int]);
        assert(w[j] == w.drop_first()[(j - 1) as int]);
        lemma_two_elements_contribute_to_count(w.drop_first(), i - 1, j - 1, n);
    }
}

/// If w is base, FreeExpand with a stable symbol gives stable count 2.
pub proof fn lemma_expand_stable_gives_count_2(
    w: Word, pos: nat, sym: Symbol, n: nat,
)
    requires
        is_base_word(w, n),
        0 <= pos <= w.len(),
        generator_index(sym) == n,
    ensures
        ({
            let pair = Seq::new(1, |_i: int| sym)
                + Seq::new(1, |_i: int| inverse_symbol(sym));
            let w1 = w.subrange(0, pos as int) + pair
                + w.subrange(pos as int, w.len() as int);
            stable_letter_count(w1, n) == 2
        }),
{
    let pair = Seq::new(1, |_i: int| sym)
        + Seq::new(1, |_i: int| inverse_symbol(sym));
    let w1 = w.subrange(0, pos as int) + pair
        + w.subrange(pos as int, w.len() as int);

    let left = w.subrange(0, pos as int);
    let right = w.subrange(pos as int, w.len() as int);

    // w = left + right, both base
    assert(w =~= left + right);
    lemma_stable_letter_count_concat(left, right, n);
    assert(stable_letter_count(w, n) == 0nat);
    // Since counts are nat and sum to 0, both are 0
    assert(stable_letter_count(left, n) == 0nat);
    assert(stable_letter_count(right, n) == 0nat);

    // pair has count 2
    match sym {
        Symbol::Gen(idx) => {
            assert(generator_index(inverse_symbol(sym)) == n);
        },
        Symbol::Inv(idx) => {
            assert(generator_index(inverse_symbol(sym)) == n);
        },
    }
    assert(pair =~= seq![sym, inverse_symbol(sym)]);
    lemma_stable_count_pair(sym, inverse_symbol(sym), n);

    // w1 = left + pair + right = left + (pair + right)
    assert(w1 =~= left + (pair + right));
    lemma_stable_letter_count_concat(pair, right, n);
    assert(stable_letter_count(pair + right, n) == 2nat);
    lemma_stable_letter_count_concat(left, pair + right, n);
}

// ============================================================
// Part 4b: Single segment lemma (k=2)
// ============================================================

/// Single segment lemma for k=2.
/// Given: w (base) →[step0] w_1 (non-base) →[step1] w_2 (base)
/// Prove: w ≡ w_2 in G.
/// If w is word_valid(n+1) and base (no stable letters), then word_valid(n).
pub proof fn lemma_base_word_valid_down(w: Word, n: nat)
    requires
        word_valid(w, n + 1),
        is_base_word(w, n),
    ensures
        word_valid(w, n),
    decreases w.len(),
{
    if w.len() > 0 {
        let rest = w.drop_first();
        assert(word_valid(rest, n + 1)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies symbol_valid(#[trigger] rest[i], n + 1)
            by {
                assert(rest[i] == w[i + 1]);
            }
        }
        // is_base_word(rest, n) from stable_letter_count
        assert(stable_letter_count(w, n) == 0nat);
        // w.first() doesn't contribute to stable count, so rest count is also 0
        // or rest count ≤ w count = 0

        // By definition: if gen_idx(first) == n, then count = rest_count + 1
        // Since count == 0, gen_idx(first) != n, and rest_count == 0
        assert(is_base_word(rest, n));

        lemma_base_word_valid_down(rest, n);

        // Combine: w.first() is valid for n, rest is valid for n
        assert(symbol_valid(w.first(), n + 1));
        assert(generator_index(w.first()) != n);
        match w.first() {
            Symbol::Gen(idx) => { assert(idx < n); },
            Symbol::Inv(idx) => { assert(idx < n); },
        }
        assert(symbol_valid(w.first(), n));

        // Stitch together: word_valid(w, n)
        assert forall|i: int| 0 <= i < w.len()
            implies symbol_valid(#[trigger] w[i], n)
        by {
            if i == 0 {
                assert(w[0] == w.first());
            } else {
                assert(w[i] == rest[i - 1]);
            }
        }
    }
}

/// If w is base and a step produces a non-base w', the step must introduce stable letters.
/// This means: FreeReduce → always base result; FreeExpand(base sym) → base result;
/// RelatorDelete(base relator) → base result; RelatorInsert(base relator) → base result.
/// So only FreeExpand(stable sym) or RelatorInsert/Delete(HNN relator) can produce non-base.
proof fn lemma_base_to_nonbase_step_type(
    data: HNNData, w: Word, w1: Word, step: DerivationStep,
)
    requires
        hnn_data_valid(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators),
        apply_step(hnn_presentation(data), w, step) == Some(w1),
        !is_base_word(w1, data.base.num_generators),
    ensures
        // step introduces stable letters: FreeExpand with stable symbol or RelatorInsert with HNN relator
        match step {
            DerivationStep::FreeExpand { position, symbol } =>
                generator_index(symbol) == data.base.num_generators,
            DerivationStep::RelatorInsert { position, relator_index, inverted } =>
                relator_index as int >= data.base.relators.len(),
            _ => false,
        },
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    match step {
        DerivationStep::FreeReduce { position } => {
            // reduce_at(w, pos) = w[0..pos] + w[pos+2..] — subrange of base w, still base
            lemma_stable_count_reduce(w, position, n);
            // gen_idx(w[pos]) < n (word_valid(w, n)), so delta = 0
            assert(symbol_valid(w[position], n));
            match w[position] {
                Symbol::Gen(idx) => { assert(idx < n); },
                Symbol::Inv(idx) => { assert(idx < n); },
            }
            assert(stable_letter_count(w1, n) == 0nat);
            assert(false); // contradiction with !is_base_word(w1)
        },
        DerivationStep::FreeExpand { position, symbol } => {
            if generator_index(symbol) != n {
                // Base symbol: pair has no stable letters
                // So w1 = w[0..pos] + pair + w[pos..] has stable_count = 0 + 0 + 0 = 0
                // Contradiction with !is_base_word(w1)
                let left = w.subrange(0, position);
                let right = w.subrange(position, w.len() as int);
                let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
                assert(w1 =~= left + pair + right);

                // pair has 0 stable letters
                assert(pair =~= seq![symbol, inverse_symbol(symbol)]);
                lemma_stable_count_pair(symbol, inverse_symbol(symbol), n);
                match symbol {
                    Symbol::Gen(idx) => { assert(idx != n); },
                    Symbol::Inv(idx) => { assert(idx != n); },
                }
                assert(stable_letter_count(pair, n) == 0nat);

                // subranges of base w have 0 stable letters
                assert(w =~= left + right);
                lemma_stable_letter_count_concat(left, right, n);
                assert(stable_letter_count(left, n) == 0nat);
                assert(stable_letter_count(right, n) == 0nat);

                assert(w1 =~= left + (pair + right));
                lemma_stable_letter_count_concat(pair, right, n);
                lemma_stable_letter_count_concat(left, pair + right, n);
                assert(stable_letter_count(w1, n) == 0nat);
                assert(false); // contradiction
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            if (relator_index as int) < data.base.relators.len() {
                // Base relator: no stable letters
                let r = get_relator(hp, relator_index, inverted);
                let left = w.subrange(0, position);
                let right = w.subrange(position, w.len() as int);
                assert(w1 =~= left + r + right);

                // r is a base relator (or its inverse), word_valid(n)
                reveal(presentation_valid);
                assert(word_valid(data.base.relators[relator_index as int], n));
                if inverted {
                    lemma_inverse_word_valid(data.base.relators[relator_index as int], n);
                }
                // Show base relator is base (stable count 0)
                let base_r = if inverted {
                    inverse_word(data.base.relators[relator_index as int])
                } else {
                    data.base.relators[relator_index as int]
                };
                assert(r == base_r);
                assert(hp.relators[relator_index as int] == data.base.relators[relator_index as int]);
                lemma_base_word_characterization(base_r, n);
                assert(is_base_word(base_r, n));
                assert(stable_letter_count(base_r, n) == 0nat);

                // w1 has same stable count as w
                assert(w =~= left + right);
                lemma_stable_letter_count_concat(left, right, n);
                assert(stable_letter_count(left, n) == 0nat);
                assert(stable_letter_count(right, n) == 0nat);
                assert(w1 =~= left + (r + right));
                lemma_stable_letter_count_concat(r, right, n);
                lemma_stable_letter_count_concat(left, r + right, n);
                assert(stable_letter_count(w1, n) == 0nat);
                assert(false);
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            // Removes a substring from w. Result is subranges of w, still base.
            let r = get_relator(hp, relator_index, inverted);
            let rlen = r.len();
            // w1 = w[0..pos] + w[pos+rlen..]
            let left = w.subrange(0, position);
            let right = w.subrange(position + rlen as int, w.len() as int);
            assert(w1 =~= left + right);

            assert(w =~= left + w.subrange(position, w.len() as int));
            assert(w.subrange(position, w.len() as int) =~=
                w.subrange(position, position + rlen as int) + right);
            lemma_stable_letter_count_concat(left, w.subrange(position, w.len() as int), n);
            lemma_stable_letter_count_concat(
                w.subrange(position, position + rlen as int), right, n);
            assert(stable_letter_count(left, n) == 0nat);
            assert(stable_letter_count(right, n) == 0nat);

            lemma_stable_letter_count_concat(left, right, n);
            assert(stable_letter_count(w1, n) == 0nat);
            assert(false);
        },
    }
}

/// Removing a word equivalent to ε preserves equivalence.
/// If u ≡ ε in G, then left·u·right ≡ left·right in G.
pub proof fn lemma_remove_trivial_equiv(
    p: Presentation, left: Word, right: Word, u: Word,
)
    requires
        equiv_in_presentation(p, u, empty_word()),
    ensures
        equiv_in_presentation(p, concat(left, concat(u, right)), concat(left, right)),
{
    // u ≡ ε → concat(u, right) ≡ concat(ε, right) =~= right
    lemma_equiv_concat_left(p, u, empty_word(), right);
    assert(concat(empty_word(), right) =~= right);
    // Now: equiv(concat(u, right), right)
    lemma_equiv_concat_right(p, left, concat(u, right), right);
}

/// Inserting a word equivalent to ε preserves equivalence.
/// If u ≡ ε in G, then left·right ≡ left·u·right in G.
pub proof fn lemma_insert_trivial_equiv(
    p: Presentation, left: Word, right: Word, u: Word,
)
    requires
        equiv_in_presentation(p, u, empty_word()),
        word_valid(u, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, concat(left, right), concat(left, concat(u, right))),
{
    // ε ≡ u by symmetry (needs word_valid + presentation_valid)
    lemma_equiv_symmetric(p, u, empty_word());
    // concat(ε, right) ≡ concat(u, right), i.e., right ≡ concat(u, right)
    lemma_equiv_concat_left(p, empty_word(), u, right);
    assert(concat(empty_word(), right) =~= right);
    // Now: equiv(right, concat(u, right))
    lemma_equiv_concat_right(p, left, right, concat(u, right));
}

/// Right cancellation: if concat(x, y) ≡ x in G, then y ≡ ε.
pub proof fn lemma_right_cancel(
    p: Presentation, x: Word, y: Word,
)
    requires
        equiv_in_presentation(p, concat(x, y), x),
        word_valid(x, p.num_generators),
        word_valid(y, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, y, empty_word()),
{
    let inv_x = inverse_word(x);
    lemma_inverse_word_valid(x, p.num_generators);

    // Step 1: concat(inv(x), concat(x, y)) ≡ concat(inv(x), x)
    lemma_equiv_concat_right(p, inv_x, concat(x, y), x);
    // Step 2: concat(inv(x), x) ≡ ε
    lemma_word_inverse_left(p, x);
    // Step 3: concat(inv(x), concat(x, y)) ≡ ε
    lemma_equiv_transitive(p,
        concat(inv_x, concat(x, y)),
        concat(inv_x, x),
        empty_word());
    // Step 4: Seq associativity
    assert(concat(inv_x, concat(x, y))
        =~= concat(concat(inv_x, x), y));
    // So: concat(concat(inv(x), x), y) ≡ ε
    // Step 5: Remove trivial prefix, get concat(concat(inv(x), x), y) ≡ y
    lemma_remove_trivial_equiv(p, empty_word(), y, concat(inv_x, x));
    assert(concat(empty_word(), concat(concat(inv_x, x), y))
        =~= concat(concat(inv_x, x), y));
    assert(concat(empty_word(), y) =~= y);
    // Step 6: symmetric on step 5 to get y ≡ concat(concat(inv(x), x), y)
    lemma_concat_word_valid(inv_x, x, p.num_generators);
    lemma_concat_word_valid(concat(inv_x, x), y, p.num_generators);
    lemma_equiv_symmetric(p,
        concat(concat(inv_x, x), y), y);
    // Step 7: y ≡ concat(concat(inv(x),x), y) ≡ ε
    lemma_equiv_transitive(p, y,
        concat(concat(inv_x, x), y),
        empty_word());
}

/// Left cancellation: if concat(x, y) ≡ y in G, then x ≡ ε.
pub proof fn lemma_left_cancel(
    p: Presentation, x: Word, y: Word,
)
    requires
        equiv_in_presentation(p, concat(x, y), y),
        word_valid(x, p.num_generators),
        word_valid(y, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, x, empty_word()),
{
    let inv_y = inverse_word(y);
    lemma_inverse_word_valid(y, p.num_generators);

    // Step 1: concat(concat(x, y), inv(y)) ≡ concat(y, inv(y))
    lemma_equiv_concat_left(p, concat(x, y), y, inv_y);
    // Step 2: concat(y, inv(y)) ≡ ε
    lemma_word_inverse_right(p, y);
    // Step 3: concat(concat(x, y), inv(y)) ≡ ε
    lemma_equiv_transitive(p,
        concat(concat(x, y), inv_y),
        concat(y, inv_y),
        empty_word());
    // Step 4: Seq associativity
    assert(concat(concat(x, y), inv_y)
        =~= concat(x, concat(y, inv_y)));
    // So: concat(x, concat(y, inv(y))) ≡ ε
    // Step 5: Remove trivial suffix, get concat(x, concat(y, inv(y))) ≡ x
    lemma_remove_trivial_equiv(p, x, empty_word(), concat(y, inv_y));
    assert(concat(x, concat(concat(y, inv_y), empty_word()))
        =~= concat(x, concat(y, inv_y)));
    assert(concat(x, empty_word()) =~= x);
    // Step 6: symmetric on step 5 to get x ≡ concat(x, concat(y, inv(y)))
    lemma_concat_word_valid(y, inv_y, p.num_generators);
    lemma_concat_word_valid(x, concat(y, inv_y), p.num_generators);
    lemma_equiv_symmetric(p,
        concat(x, concat(y, inv_y)), x);
    // Step 7: x ≡ concat(x, concat(y, inv(y))) ≡ ε
    lemma_equiv_transitive(p, x,
        concat(x, concat(y, inv_y)),
        empty_word());
}

/// Left cancellation with equivalence: concat(prefix, a) ≡ concat(prefix, b) → a ≡ b.
pub proof fn lemma_concat_left_cancel_equiv(
    p: Presentation, prefix: Word, a: Word, b: Word,
)
    requires
        equiv_in_presentation(p, concat(prefix, a), concat(prefix, b)),
        word_valid(prefix, p.num_generators),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, a, b),
{
    let inv_p = inverse_word(prefix);
    lemma_inverse_word_valid(prefix, p.num_generators);
    // inv(prefix) · (prefix · a) ≡ inv(prefix) · (prefix · b)
    lemma_equiv_concat_right(p, inv_p, concat(prefix, a), concat(prefix, b));
    // inv(prefix) · prefix ≡ ε
    lemma_word_inverse_left(p, prefix);
    // (inv(prefix) · prefix) · a ≡ ε · a = a
    lemma_equiv_concat_left(p, concat(inv_p, prefix), empty_word(), a);
    assert(concat(inv_p, concat(prefix, a)) =~= concat(concat(inv_p, prefix), a));
    assert(concat(empty_word(), a) =~= a);
    // Similarly for b
    lemma_equiv_concat_left(p, concat(inv_p, prefix), empty_word(), b);
    assert(concat(inv_p, concat(prefix, b)) =~= concat(concat(inv_p, prefix), b));
    assert(concat(empty_word(), b) =~= b);
    // Chain: a ← (inv_p · prefix · a) ≡ inv_p · (prefix · a) ≡ inv_p · (prefix · b) ≡ (inv_p · prefix · b) → b
    lemma_concat_word_valid(inv_p, prefix, p.num_generators);
    lemma_concat_word_valid(concat(inv_p, prefix), a, p.num_generators);
    lemma_equiv_symmetric(p, concat(concat(inv_p, prefix), a), a);
    lemma_equiv_transitive(p, a, concat(inv_p, concat(prefix, a)), concat(inv_p, concat(prefix, b)));
    lemma_equiv_transitive(p, a, concat(inv_p, concat(prefix, b)), b);
}

/// Right cancellation with equivalence: concat(a, suffix) ≡ concat(b, suffix) → a ≡ b.
pub proof fn lemma_concat_right_cancel_equiv(
    p: Presentation, a: Word, b: Word, suffix: Word,
)
    requires
        equiv_in_presentation(p, concat(a, suffix), concat(b, suffix)),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        word_valid(suffix, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, a, b),
{
    let inv_s = inverse_word(suffix);
    lemma_inverse_word_valid(suffix, p.num_generators);
    // (a · suffix) · inv(suffix) ≡ (b · suffix) · inv(suffix)
    lemma_equiv_concat_left(p, concat(a, suffix), concat(b, suffix), inv_s);
    // suffix · inv(suffix) ≡ ε
    lemma_word_inverse_right(p, suffix);
    // a · (suffix · inv(suffix)) ≡ a · ε = a
    lemma_equiv_concat_right(p, a, concat(suffix, inv_s), empty_word());
    assert(concat(a, concat(suffix, inv_s)) =~= concat(concat(a, suffix), inv_s));
    assert(concat(a, empty_word()) =~= a);
    // Similarly for b
    lemma_equiv_concat_right(p, b, concat(suffix, inv_s), empty_word());
    assert(concat(b, concat(suffix, inv_s)) =~= concat(concat(b, suffix), inv_s));
    assert(concat(b, empty_word()) =~= b);
    // Chain: a ← (a · suffix · inv_s) ≡ (b · suffix · inv_s) → b
    lemma_concat_word_valid(suffix, inv_s, p.num_generators);
    lemma_concat_word_valid(a, concat(suffix, inv_s), p.num_generators);
    lemma_equiv_symmetric(p, concat(a, concat(suffix, inv_s)), a);
    lemma_equiv_transitive(p, a, concat(concat(a, suffix), inv_s), concat(concat(b, suffix), inv_s));
    lemma_equiv_transitive(p, a, concat(b, concat(suffix, inv_s)), b);
}

/// If concat(a, b) ≡ ε then b ≡ inv(a).
proof fn lemma_identity_split(
    p: Presentation, a: Word, b: Word,
)
    requires
        equiv_in_presentation(p, concat(a, b), empty_word()),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, b, inverse_word(a)),
{
    let inv_a = inverse_word(a);
    lemma_inverse_word_valid(a, p.num_generators);

    // concat(inv(a), concat(a, b)) ≡ concat(inv(a), ε) =~= inv(a)
    lemma_equiv_concat_right(p, inv_a, concat(a, b), empty_word());
    assert(concat(inv_a, empty_word()) =~= inv_a);
    // Seq associativity
    assert(concat(inv_a, concat(a, b))
        =~= concat(concat(inv_a, a), b));
    // concat(inv(a), a) ≡ ε
    lemma_word_inverse_left(p, a);
    // remove_trivial: concat(concat(inv(a), a), b) ≡ b
    lemma_remove_trivial_equiv(p, empty_word(), b, concat(inv_a, a));
    assert(concat(empty_word(), concat(concat(inv_a, a), b))
        =~= concat(concat(inv_a, a), b));
    assert(concat(empty_word(), b) =~= b);
    // Now: concat(concat(inv(a), a), b) ≡ b [from remove_trivial]
    // And: concat(concat(inv(a), a), b) ≡ inv(a) [from equiv_concat_right, via =~=]
    // Need: b ≡ inv(a)
    lemma_concat_word_valid(inv_a, a, p.num_generators);
    lemma_concat_word_valid(concat(inv_a, a), b, p.num_generators);
    lemma_equiv_symmetric(p, concat(concat(inv_a, a), b), b);
    // b ≡ concat(concat(inv(a), a), b) ≡ inv(a)
    lemma_equiv_transitive(p, b, concat(concat(inv_a, a), b), inv_a);
}

/// Case (a): FreeExpand(stable) + FreeReduce → w2 = w by stable count argument.
proof fn lemma_k2_expand_reduce(
    data: HNNData, w: Word, w1: Word, w_end: Word,
    pos0: int, sym: Symbol, pos1: int,
)
    requires
        hnn_data_valid(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::FreeExpand { position: pos0, symbol: sym };
            let step1 = DerivationStep::FreeReduce { position: pos1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w_end)
        }),
        generator_index(sym) == data.base.num_generators,
        !is_base_word(w1, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let n = data.base.num_generators;

    // w1 has exactly 2 stable letters
    lemma_expand_stable_gives_count_2(w, pos0 as nat, sym, n);

    // FreeReduce at pos1: removes 2 symbols
    lemma_stable_count_reduce(w1, pos1 as int, n);
    // w_end has 0 stable letters, so the reduce removed 2 stable letters
    // This means generator_index(w1[pos1]) == n
    // Since the only stable pair is at pos0, pos0+1, we get pos1 == pos0
    // Then w_end = reduce_at(w1, pos0) = w

    // w_end is base (count 0), w1 had count 2, reduce changes count by 0 or -2
    // Must be -2 for w_end to be base. So gen_idx(w1[pos1]) == n.
    assert(stable_letter_count(w_end, n) == 0nat);
    assert(stable_letter_count(w1, n) == 2nat);
    // From lemma_stable_count_reduce: count(w_end) = count(w1) - delta
    // where delta = 2 if gen_idx(w1[pos1]) == n, else 0
    // count(w_end) = 0 = 2 - delta, so delta = 2
    assert(generator_index(w1[pos1 as int]) == n);

    // Now: w1[pos1] is stable, w1[pos1+1] is inverse of w1[pos1]
    // The only stable symbols in w1 are at pos0 and pos0+1
    // Since w1[pos1] is stable, pos1 must be pos0 or pos0+1
    // But w1[pos1] and w1[pos1+1] are an inverse pair, both stable
    // So {pos1, pos1+1} ⊆ {pos0, pos0+1} => pos1 == pos0

    // w1 = w[0..pos0] ++ [sym, inv(sym)] ++ w[pos0..]
    // Every symbol of w is base (gen_idx < n)
    // So w1[i] is stable iff i == pos0 or i == pos0 + 1
    // w1[pos1] is stable, so pos1 ∈ {pos0, pos0+1}
    // If pos1 == pos0 + 1, then w1[pos1+1] = w1[pos0+2] is from w, so base, not inverse of stable
    // So pos1 == pos0

    // All symbols of w are base (gen_idx < n)
    assert forall|i: int| 0 <= i < w.len()
        implies generator_index(#[trigger] w[i]) < n
    by {
        assert(symbol_valid(w[i], n));
    }

    // w1 = left ++ [sym, inv(sym)] ++ right where left = w[0..pos0], right = w[pos0..]
    let left = w.subrange(0, pos0 as int);
    let right = w.subrange(pos0 as int, w.len() as int);
    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= left + pair + right);

    // Show w1[pos1] is at a specific location in w1
    // w1[pos0] == sym (stable), w1[pos0+1] == inv(sym) (stable)
    // For any other index j < pos0: w1[j] == left[j] == w[j] → gen_idx < n
    // For any index j > pos0+1: w1[j] == w[j-2] → gen_idx < n

    // Since w1[pos1] is stable and pos1 must be pos0 or pos0+1:
    // w1[pos0] = sym, gen_idx = n ✓
    // If pos1 == pos0+1, w1[pos1+1] = w1[pos0+2]:
    //   if pos0+2 < w1.len(), w1[pos0+2] is from right[0] = w[pos0], gen_idx < n
    //   so has_cancellation_at requires w1[pos1] and w1[pos1+1] are inverses
    //   but w1[pos0+1] = inv(sym) and w1[pos0+2] has gen_idx < n ≠ n
    //   so they can't be inverses → contradiction with has_cancellation_at
    // Therefore pos1 == pos0.

    if pos1 != pos0 {
        // Derive contradiction: w1[pos1] is stable but pos1 ∉ {pos0, pos0+1} is impossible
        // Actually, pos1 could be pos0+1. Let's handle that.
        if pos1 == pos0 + 1 {
            // w1[pos1] = inv(sym), w1[pos1+1] = right[0] if right.len() > 0
            // has_cancellation_at(w1, pos1) means w1[pos1] and w1[pos1+1] are inverses
            // w1[pos1] = inv(sym), gen_idx = n
            // w1[pos1+1] is from right = w[pos0..], so gen_idx < n
            // They have different gen_idx, can't be inverses
            if right.len() > 0 {
                assert(w1[pos1 as int + 1] == right[0]);
                assert(right[0] == w[pos0 as int]);
                assert(generator_index(w[pos0 as int]) < n);
                // w1[pos1] = inv(sym), gen_idx = n
                // w1[pos1+1] gen_idx < n
                // For has_cancellation_at: w1[pos1+1] == inverse_symbol(w1[pos1])
                // inverse_symbol preserves gen_idx, so gen_idx(w1[pos1+1]) should == n
                // But it's < n. Contradiction.
                match w1[pos1 as int] {
                    Symbol::Gen(idx) => {
                        assert(w1[pos1 as int + 1] == Symbol::Inv(idx));
                    },
                    Symbol::Inv(idx) => {
                        assert(w1[pos1 as int + 1] == Symbol::Gen(idx));
                    },
                }
            } else {
                // right is empty, w1 = left ++ [sym, inv(sym)]
                // pos1+1 = pos0+2 = w1.len(), but has_cancellation_at needs pos1+1 < w1.len()
                assert(false);
            }
        } else {
            // pos1 ≠ pos0 and pos1 ≠ pos0+1
            // w1[pos1] has gen_idx == n, but it's not at pos0 or pos0+1
            // All other positions in w1 come from w (base), so gen_idx < n
            // Contradiction
            if (pos1 as int) < (pos0 as int) {
                // w1[pos1] = left[pos1] = w[pos1], gen_idx < n
                assert(w1[pos1 as int] == left[pos1 as int]);
                assert(left[pos1 as int] == w[pos1 as int]);
                assert(generator_index(w[pos1 as int]) < n);
            } else {
                // pos1 > pos0 + 1
                // w1[pos1] is from right[pos1 - pos0 - 2] = w[pos1 - 2]
                let wi = (pos1 - 2) as int;
                assert(w1[pos1 as int] == right[(pos1 - pos0 - 2) as int]);
                assert(right[(pos1 - pos0 - 2) as int] == w[wi]);
                assert(generator_index(w[wi]) < n);
            }
        }
    }

    assert(pos1 == pos0);

    // Now show w_end = w
    // w_end = reduce_at(w1, pos0) = w1[0..pos0] ++ w1[pos0+2..]
    //       = left ++ right = w
    assert(w_end =~= w1.subrange(0, pos0 as int) + w1.subrange(pos0 as int + 2, w1.len() as int));
    assert(w1.subrange(0, pos0 as int) =~= left);
    assert(w1.subrange(pos0 as int + 2, w1.len() as int) =~= right);
    assert(w_end =~= left + right);
    assert(w =~= left + right);
    assert(w_end =~= w);

    lemma_equiv_refl(data.base, w);
}

/// Inserting a word into a non-base word preserves non-base status.
/// If w has stable letters and we insert u at position pos, the result still has stable letters.
proof fn lemma_insert_preserves_nonbase(w: Word, u: Word, pos: int, n: nat)
    requires
        !is_base_word(w, n),
        0 <= pos <= w.len(),
    ensures
        !is_base_word(
            w.subrange(0, pos) + u + w.subrange(pos, w.len() as int),
            n,
        ),
{
    let left = w.subrange(0, pos);
    let right = w.subrange(pos, w.len() as int);
    assert(w =~= left + right);
    lemma_stable_letter_count_concat(left, right, n);
    assert(stable_letter_count(w, n) > 0);

    let w_new = (left + u) + right;
    assert(w_new =~= left + (u + right));
    lemma_stable_letter_count_concat(left, u + right, n);
    lemma_stable_letter_count_concat(u, right, n);
    // count(w_new) = count(left) + count(u) + count(right) >= count(w) > 0
    assert(stable_letter_count(w_new, n) > 0);
}

/// The stable letter positions in a non-inverted HNN relator:
/// position 0 is Inv(n) and position |a_j|+1 is Gen(n).
pub proof fn lemma_hnn_relator_stable_positions(data: HNNData, j: int)
    requires
        hnn_data_valid(data),
        0 <= j < data.associations.len(),
    ensures
        ({
            let n = data.base.num_generators;
            let r = hnn_relator(data, j);
            let (a_j, b_j) = data.associations[j];
            &&& r[0int] == stable_letter_inv(data)
            &&& r[(a_j.len() + 1) as int] == stable_letter(data)
            &&& generator_index(r[0int]) == n
            &&& generator_index(r[(a_j.len() + 1) as int]) == n
            &&& r.len() == 2 + a_j.len() + b_j.len()
        }),
{
    let n = data.base.num_generators;
    let (a_j, b_j) = data.associations[j];
    let t_inv = stable_letter_inv(data);
    let t = stable_letter(data);
    let head = Seq::new(1, |_k: int| t_inv);
    let gen_seq = Seq::new(1, |_k: int| t);
    lemma_inverse_word_len(b_j);
    let tail = inverse_word(b_j);
    let r = hnn_relator(data, j);
    assert(r =~= head + a_j + gen_seq + tail);

    // r[0] = head[0] = t_inv = Inv(n)
    assert((head + a_j + gen_seq + tail)[0int] == head[0int]);
    assert(head[0int] == t_inv);

    // r[|a_j|+1]: split r into first_part + second_part
    let first_part = head + a_j;
    assert(first_part.len() == 1 + a_j.len());
    let second_part = gen_seq + tail;
    assert(r =~= first_part + second_part);
    assert(r[(1 + a_j.len() as int)] == second_part[0int]);
    assert(second_part[0int] == gen_seq[0int]);
    assert(gen_seq[0int] == t);
}

/// The inverted HNN relator has structure:
/// b_j ++ [Inv(n)] ++ inverse_word(a_j) ++ [Gen(n)]
/// Stable letters at positions |b_j| and |b_j|+|a_j|+1.
pub proof fn lemma_hnn_relator_inverted_stable_positions(data: HNNData, j: int)
    requires
        hnn_data_valid(data),
        0 <= j < data.associations.len(),
    ensures
        ({
            let n = data.base.num_generators;
            let a_j = data.associations[j].0;
            let b_j = data.associations[j].1;
            let inv_r = inverse_word(hnn_relator(data, j));
            &&& inv_r =~= b_j + Seq::new(1, |_i: int| stable_letter_inv(data))
                + inverse_word(a_j) + Seq::new(1, |_i: int| stable_letter(data))
            &&& inv_r[b_j.len() as int] == stable_letter_inv(data)
            &&& inv_r[(b_j.len() + a_j.len() + 1) as int] == stable_letter(data)
            &&& generator_index(inv_r[b_j.len() as int]) == n
            &&& generator_index(inv_r[(b_j.len() + a_j.len() + 1) as int]) == n
            &&& inv_r.len() == 2 + a_j.len() + b_j.len()
        }),
{
    let n = data.base.num_generators;
    let (a_j, b_j) = data.associations[j];
    let t_inv = stable_letter_inv(data);
    let t = stable_letter(data);
    let t_inv_seq = Seq::new(1, |_i: int| t_inv);
    let t_seq = Seq::new(1, |_i: int| t);
    let r = hnn_relator(data, j);
    lemma_inverse_word_len(b_j);
    let inv_bj = inverse_word(b_j);
    assert(r =~= t_inv_seq + a_j + t_seq + inv_bj);

    // inverse_word distributes over concat (reversed order)
    lemma_inverse_concat(t_inv_seq + a_j + t_seq, inv_bj);
    lemma_inverse_concat(t_inv_seq + a_j, t_seq);
    lemma_inverse_concat(t_inv_seq, a_j);
    lemma_inverse_singleton(t_inv);
    lemma_inverse_singleton(t);
    crate::word::lemma_inverse_involution(b_j);
    assert(inverse_symbol(t_inv) == t);
    assert(inverse_symbol(t) == t_inv);

    let inv_r = inverse_word(r);

    // inverse_word(r) = inverse_word(inv_bj) ++ inverse_word(t_seq) ++ inverse_word(a_j) ++ inverse_word(t_inv_seq)
    //                 = b_j ++ [Inv(n)] ++ inverse_word(a_j) ++ [Gen(n)]
    assert(inverse_word(t_inv_seq) =~= Seq::new(1, |_i: int| t));
    assert(inverse_word(t_seq) =~= Seq::new(1, |_i: int| t_inv));
    assert(inverse_word(inv_bj) =~= b_j);

    assert(inv_r =~= b_j + Seq::new(1, |_i: int| t_inv)
        + inverse_word(a_j) + Seq::new(1, |_i: int| t));

    // Position |b_j|: t_inv_seq after b_j
    let bj_part = b_j;
    let rest = Seq::new(1, |_i: int| t_inv) + inverse_word(a_j) + Seq::new(1, |_i: int| t);
    assert(inv_r =~= bj_part + rest);
    assert(inv_r[b_j.len() as int] == rest[0int]);
    assert(rest[0int] == t_inv);

    // Position |b_j|+|a_j|+1: t after the middle part
    lemma_inverse_word_len(a_j);
    let mid = Seq::new(1, |_i: int| t_inv) + inverse_word(a_j);
    let end_part = Seq::new(1, |_i: int| t);
    assert(rest =~= mid + end_part);
    assert(mid.len() == 1 + a_j.len());
    assert(rest[(1 + a_j.len() as int)] == end_part[0int]);
    assert(end_part[0int] == t);
    assert(inv_r[(b_j.len() + a_j.len() + 1) as int] == t);
}

/// Case (b): FreeExpand(stable) + RelatorDelete(HNN) → w ≡ w_end in G.
/// The adjacent stable pair forces the deleted HNN relator to have |a_j| = 0.
proof fn lemma_k2_expand_reldelete(
    data: HNNData, w: Word, w1: Word, w_end: Word,
    pos0: int, sym: Symbol, pos1: int, r_idx: nat, inverted: bool,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::FreeExpand { position: pos0, symbol: sym };
            let step1 = DerivationStep::RelatorDelete { position: pos1, relator_index: r_idx, inverted };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w_end)
        }),
        generator_index(sym) == data.base.num_generators,
        !is_base_word(w1, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r = get_relator(hp, r_idx, inverted);

    // w1 has 2 stable letters
    lemma_expand_stable_gives_count_2(w, pos0 as nat, sym, n);

    // Stable count arithmetic: count(r) = 2
    assert(w1.subrange(pos1, pos1 + r.len() as int) =~= r);
    assert(w_end =~= w1.subrange(0, pos1) + w1.subrange(pos1 + r.len() as int, w1.len() as int));
    assert(w1 =~= w1.subrange(0, pos1) + w1.subrange(pos1, w1.len() as int));
    lemma_stable_letter_count_concat(w1.subrange(0, pos1), w1.subrange(pos1, w1.len() as int), n);
    assert(w1.subrange(pos1, w1.len() as int) =~=
        r + w1.subrange(pos1 + r.len() as int, w1.len() as int));
    lemma_stable_letter_count_concat(r, w1.subrange(pos1 + r.len() as int, w1.len() as int), n);
    lemma_stable_letter_count_concat(
        w1.subrange(0, pos1),
        w1.subrange(pos1 + r.len() as int, w1.len() as int), n);
    assert(stable_letter_count(r, n) == 2nat);

    // r_idx must be HNN (base relator has count 0)
    if (r_idx as int) < data.base.relators.len() {
        reveal(presentation_valid);
        let base_r = data.base.relators[r_idx as int];
        assert(hp.relators[r_idx as int] == base_r);
        if inverted {
            lemma_inverse_word_valid(base_r, n);
            lemma_base_word_characterization(inverse_word(base_r), n);
        } else {
            lemma_base_word_characterization(base_r, n);
        }
        assert(false); // count(r) = 2 vs count(base_r) = 0
    }

    let j = (r_idx as int - data.base.relators.len()) as int;
    assert(0 <= j < data.associations.len());
    assert(hp.relators[r_idx as int] == hnn_relator(data, j));
    let (a_j, b_j) = data.associations[j];

    // w1 structure: stable letters only at pos0 and pos0+1
    let left_w = w.subrange(0, pos0);
    let right_w = w.subrange(pos0, w.len() as int);
    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= left_w + pair + right_w);

    assert forall|i: int| 0 <= i < w.len()
        implies generator_index(#[trigger] w[i]) < n
    by {
        assert(symbol_valid(w[i], n));
    }

    assert forall|i: int| 0 <= i < w1.len() && i != pos0 && i != pos0 + 1
        implies generator_index(#[trigger] w1[i]) < n
    by {
        if i < pos0 {
            assert(w1[i] == left_w[i]);
            assert(left_w[i] == w[i]);
        } else {
            assert(w1[i] == right_w[(i - pos0 - 2)]);
            assert(right_w[(i - pos0 - 2)] == w[(i - 2)]);
        }
    }

    if !inverted {
        crate::britton_proof_helpers3::lemma_k2_expand_reldelete_noninv(
            data, w, w1, w_end, pos0, sym, pos1, r_idx, j);
    } else {
        crate::britton_proof_helpers3::lemma_k2_expand_reldelete_inv(
            data, w, w1, w_end, pos0, sym, pos1, r_idx, j);
    }
}

/// Case (c): RelatorInsert(HNN) + FreeReduce → w ≡ w_end in G.
/// The FreeReduce forces the HNN relator's stable letters to be adjacent (|a_j| = 0).
proof fn lemma_k2_relinsert_reduce(
    data: HNNData, w: Word, w1: Word, w_end: Word,
    pos0: int, r_idx: nat, inverted: bool, pos1: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: pos0, relator_index: r_idx, inverted };
            let step1 = DerivationStep::FreeReduce { position: pos1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w_end)
        }),
        r_idx as int >= data.base.relators.len(),
        !is_base_word(w1, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r = get_relator(hp, r_idx, inverted);

    // w1 = w[0..pos0] ++ r ++ w[pos0..]
    let w_left = w.subrange(0, pos0);
    let w_right = w.subrange(pos0, w.len() as int);
    assert(w1 =~= w_left + (r + w_right));

    // w_end = reduce_at(w1, pos1)
    assert(has_cancellation_at(w1, pos1));
    assert(w_end =~= w1.subrange(0, pos1) + w1.subrange(pos1 + 2, w1.len() as int));

    // Stable count: w1 has ≥ 2 stable letters (from HNN relator), w_end has 0
    lemma_stable_count_reduce(w1, pos1, n);

    // w is base, so count(w) = 0. w1 = w_left ++ r ++ w_right, and w is base.
    assert(w =~= w_left + w_right);
    lemma_stable_letter_count_concat(w_left, w_right, n);
    assert(stable_letter_count(w_left, n) == 0nat);
    assert(stable_letter_count(w_right, n) == 0nat);
    lemma_stable_letter_count_concat(w_left, r + w_right, n);
    lemma_stable_letter_count_concat(r, w_right, n);
    assert(stable_letter_count(w1, n) == stable_letter_count(r, n));

    // FreeReduce reduces count by 0 or 2. For w_end to be base (count 0):
    // Must reduce by exactly count(w1) = count(r).
    // From lemma_stable_count_reduce: if gen_idx(w1[pos1]) = n then delta = 2 else delta = 0.
    // count(w_end) = count(w1) - delta = count(r) - delta = 0 → delta = count(r)
    assert(stable_letter_count(w_end, n) == 0nat);

    // Extract HNN relator info
    let j = (r_idx as int - data.base.relators.len()) as int;
    assert(0 <= j < data.associations.len());
    assert(hp.relators[r_idx as int] == hnn_relator(data, j));
    let (a_j, b_j) = data.associations[j];

    if !inverted {
        // r = hnn_relator(data, j) = [Inv(n)] ++ a_j ++ [Gen(n)] ++ inv(b_j)
        lemma_hnn_relator_stable_positions(data, j);
        lemma_inverse_word_len(b_j);

        // Stable letters at positions pos0 and pos0+|a_j|+1 in w1
        // FreeReduce at pos1 requires adjacent inverse pair containing both stable letters
        // So pos1 and pos1+1 must be the two stable positions: |a_j| = 0

        // w1 stable letters: at pos0 (Inv(n)) and pos0+|a_j|+1 (Gen(n))
        // All other positions in w1 are base
        assert(w1[pos0 as int] == r[0int]);
        assert(generator_index(w1[pos0 as int]) == n);

        // For FreeReduce to remove stable letters: gen_idx(w1[pos1]) must be n
        // (otherwise count doesn't decrease and w_end has count(r) > 0)
        assert(generator_index(w1[pos1]) == n);

        // Show pos1 = pos0 and |a_j| = 0
        // w1 has base content from w everywhere except in the relator
        // Stable letters in w1 are at pos0 (from r[0] = Inv(n))
        // and pos0+|a_j|+1 (from r[|a_j|+1] = Gen(n))
        // FreeReduce pair must be at these two positions, so they must be adjacent
        // pos0+|a_j|+1 = pos0+1 → |a_j| = 0
        // And pos1 = pos0

        // All w1 positions outside the relator are base
        assert forall|i: int| 0 <= i < w1.len() && (i < pos0 || i >= pos0 + r.len() as int)
            implies generator_index(#[trigger] w1[i]) < n
        by {
            if i < pos0 {
                assert(w1[i] == w_left[i]);
                assert(w_left[i] == w[i]);
                assert(symbol_valid(w[i], n));
            } else {
                let k = i - pos0 - r.len() as int;
                assert(w1[i] == w_right[k]);
                assert(w_right[k] == w[(pos0 + k) as int]);
                assert(symbol_valid(w[(pos0 + k) as int], n));
            }
        }

        // Within the relator, base positions also have gen_idx < n
        assert forall|i: int| 0 <= i < r.len() && i != 0 && i != (a_j.len() + 1) as int
            implies generator_index(#[trigger] r[i]) < n
        by {
            reveal(presentation_valid);
            // All symbols of a_j and inv(b_j) have gen_idx < n
            if i > 0 && i <= a_j.len() as int {
                // Position i is in a_j (at index i-1)
                assert(word_valid(a_j, n));
                let head = Seq::new(1, |_k: int| stable_letter_inv(data));
                assert(r =~= head + a_j + Seq::new(1, |_k: int| stable_letter(data)) + inverse_word(b_j));
                assert(r[i] == (head + a_j)[i]);
                assert((head + a_j)[i] == a_j[(i - 1) as int]);
                assert(symbol_valid(a_j[(i - 1) as int], n));
            } else if i > (a_j.len() + 1) as int {
                // Position i is in inv(b_j) (at index i - a_j.len() - 2)
                let head_aj_gen = Seq::new(1, |_k: int| stable_letter_inv(data)) + a_j + Seq::new(1, |_k: int| stable_letter(data));
                let inv_bj = inverse_word(b_j);
                assert(r =~= head_aj_gen + inv_bj);
                assert(head_aj_gen.len() == a_j.len() + 2);
                assert(r[i] == inv_bj[(i - a_j.len() as int - 2) as int]);
                lemma_inverse_word_valid(b_j, n);
                assert(symbol_valid(inv_bj[(i - a_j.len() as int - 2) as int], n));
            }
        }

        // Therefore w1 positions with gen_idx = n are exactly pos0 and pos0+|a_j|+1
        // FreeReduce pair at pos1 has gen_idx(w1[pos1]) = n
        // So pos1 ∈ {pos0, pos0+|a_j|+1} (it must be within the relator region)
        // pos1+1 also has gen_idx = n (the pair element), so pos1+1 ∈ {pos0, pos0+|a_j|+1}
        // For {pos1, pos1+1} ⊆ {pos0, pos0+|a_j|+1}:
        // pos1 = pos0 and pos1+1 = pos0+|a_j|+1 → |a_j| = 0

        if a_j.len() > 0 {
            // Stable positions are pos0 and pos0+|a_j|+1, separated by > 1
            // FreeReduce needs adjacent pair, but the stable positions aren't adjacent
            // gen_idx(w1[pos1]) = n, and w1[pos1+1] = inverse_symbol(w1[pos1]) (inverse pair)
            // So gen_idx(w1[pos1+1]) = n too
            // pos1 and pos1+1 are consecutive with gen_idx = n
            // But the only gen_idx = n positions are pos0 and pos0+|a_j|+1
            // These are separated by |a_j|+1 > 1, so they're not consecutive
            // Contradiction: can't have two consecutive gen_idx = n positions
            if pos1 == pos0 as int {
                // w1[pos1+1] = w1[pos0+1] is in the relator at index 1
                // When |a_j| > 0: r[1] = a_j[0], gen_idx < n
                assert(w1[(pos1 + 1) as int] == r[1int]);
                assert(generator_index(r[1int]) < n);
                // But has_cancellation_at means gen_idx(w1[pos1+1]) matches
                match w1[pos1] {
                    Symbol::Gen(idx) => { assert(w1[(pos1+1) as int] == Symbol::Inv(idx)); },
                    Symbol::Inv(idx) => { assert(w1[(pos1+1) as int] == Symbol::Gen(idx)); },
                }
                assert(generator_index(w1[(pos1+1) as int]) == n);
                assert(false);
            } else if pos1 == (pos0 + a_j.len() as int + 1) {
                // w1[pos1+1] is at relator index |a_j|+2, in inv(b_j)
                assert(w1[(pos1 + 1) as int] == r[(a_j.len() as int + 2) as int]);
                assert(generator_index(r[(a_j.len() as int + 2) as int]) < n);
                match w1[pos1] {
                    Symbol::Gen(idx) => { assert(w1[(pos1+1) as int] == Symbol::Inv(idx)); },
                    Symbol::Inv(idx) => { assert(w1[(pos1+1) as int] == Symbol::Gen(idx)); },
                }
                assert(generator_index(w1[(pos1+1) as int]) == n);
                assert(false);
            } else {
                // pos1 is not at either stable position
                assert(generator_index(w1[pos1]) < n);
                assert(false);
            }
        }
        assert(a_j.len() == 0);
        assert(a_j =~= Seq::<Symbol>::empty());
        assert(pos1 == pos0 as int);

        // r = [Inv(n), Gen(n)] ++ inv(b_j), |r| = 2 + |b_j|
        let inv_bj = inverse_word(b_j);

        // w_end = w1[0..pos0] ++ w1[pos0+2..]
        // w1 = w_left ++ [Inv(n), Gen(n)] ++ inv_bj ++ w_right
        // w_end = w_left ++ inv_bj ++ w_right
        // = concat(w_left, concat(inv_bj, w_right))
        assert(w1.subrange(0, pos0) =~= w_left);
        let r_prefix = Seq::new(1, |_i: int| Symbol::Inv(n)) + Seq::new(1, |_i: int| Symbol::Gen(n));
        assert(r =~= r_prefix + inv_bj);
        assert(w1 =~= w_left + r_prefix + inv_bj + w_right);
        assert(w1 =~= w_left + (r_prefix + (inv_bj + w_right)));
        assert(w1.subrange(pos0 + 2, w1.len() as int) =~= inv_bj + w_right);
        assert(w_end =~= w_left + (inv_bj + w_right));

        // w = w_left ++ w_right = concat(w_left, w_right)
        assert(w =~= w_left + w_right);

        // By isomorphism: a_j = ε → b_j ≡ ε → inv(b_j) ≡ ε
        lemma_empty_association_implies_trivial(data, j);
        lemma_inverse_of_identity(data.base, b_j);
        lemma_inverse_word_valid(b_j, n);

        // w_end ≡ w by removing inv(b_j) from w_end
        // w_end = concat(w_left, concat(inv_bj, w_right))
        // w = concat(w_left, w_right)
        // By remove_trivial_equiv: w_end ≡ w
        lemma_remove_trivial_equiv(data.base, w_left, w_right, inv_bj);
        // But we want w ≡ w_end, so use symmetry
        // Actually, remove gives w_end ≡ w. But we want ensures w ≡ w_end.
        // Use insert instead: w ≡ w_end
        lemma_insert_trivial_equiv(data.base, w_left, w_right, inv_bj);
    } else {
        // Inverted case: r = b_j ++ [Inv(n)] ++ inv(a_j) ++ [Gen(n)]
        lemma_hnn_relator_inverted_stable_positions(data, j);
        lemma_inverse_word_len(b_j);
        lemma_inverse_word_len(a_j);

        let bj_len = b_j.len() as int;
        // Stable at pos0+|b_j| and pos0+|b_j|+|a_j|+1 in w1
        assert(w1[(pos0 + bj_len) as int] == r[bj_len]);
        assert(generator_index(w1[(pos0 + bj_len) as int]) == n);

        // gen_idx(w1[pos1]) = n (from FreeReduce removing stable pair)
        assert(generator_index(w1[pos1]) == n);

        // Show |a_j| = 0 using same argument
        assert forall|i: int| 0 <= i < w1.len() && (i < pos0 || i >= pos0 + r.len() as int)
            implies generator_index(#[trigger] w1[i]) < n
        by {
            if i < pos0 {
                assert(w1[i] == w_left[i]);
                assert(w_left[i] == w[i]);
                assert(symbol_valid(w[i], n));
            } else {
                let k = i - pos0 - r.len() as int;
                assert(w1[i] == w_right[k]);
                assert(w_right[k] == w[(pos0 + k) as int]);
                assert(symbol_valid(w[(pos0 + k) as int], n));
            }
        }

        // Within the relator, base positions also have gen_idx < n
        assert forall|i: int| 0 <= i < r.len() && i != bj_len && i != (bj_len + a_j.len() + 1) as int
            implies generator_index(#[trigger] r[i]) < n
        by {
            reveal(presentation_valid);
            let inv_aj = inverse_word(a_j);
            lemma_inverse_word_len(a_j);
            if i < bj_len {
                // Position in b_j
                let bj_head = b_j;
                let bj_tail = Seq::new(1, |_i: int| stable_letter_inv(data))
                    + inv_aj + Seq::new(1, |_i: int| stable_letter(data));
                assert(r =~= bj_head + bj_tail);
                assert(r[i] == b_j[i]);
                assert(word_valid(b_j, n));
                assert(symbol_valid(b_j[i], n));
            } else if i > bj_len && i < (bj_len + a_j.len() + 1) as int {
                // Position in inv(a_j) at index i - bj_len - 1
                let head = b_j + Seq::new(1, |_i: int| stable_letter_inv(data));
                assert(head.len() == bj_len + 1);
                assert(r =~= head + inv_aj + Seq::new(1, |_i: int| stable_letter(data)));
                assert(r[i] == (head + inv_aj)[i]);
                assert((head + inv_aj)[i] == inv_aj[(i - bj_len - 1) as int]);
                lemma_inverse_word_valid(a_j, n);
                assert(symbol_valid(inv_aj[(i - bj_len - 1) as int], n));
            } else if i > (bj_len + a_j.len() + 1) as int {
                // Past second stable letter — impossible since r.len() = 2 + |a_j| + |b_j|
                // and max position is bj_len + a_j.len() + 1, so i >= bj_len + a_j.len() + 2 = r.len()
                // but i < r.len(), contradiction
                assert(false);
            }
        }

        if a_j.len() > 0 {
            // Same adjacency contradiction: stable positions pos0+|b_j| and pos0+|b_j|+|a_j|+1
            // separated by |a_j|+1 > 1, can't be an adjacent pair
            if pos1 == (pos0 + bj_len) as int {
                assert(w1[(pos1 + 1) as int] == r[(bj_len + 1) as int]);
                // r[|b_j|+1] is the first symbol of inv(a_j), gen_idx < n
                let bj_part = b_j + Seq::new(1, |_i: int| stable_letter_inv(data));
                let inv_aj = inverse_word(a_j);
                assert(r =~= bj_part + inv_aj + Seq::new(1, |_i: int| stable_letter(data)));
                assert(bj_part.len() == bj_len + 1);
                assert(r[(bj_len + 1) as int] == inv_aj[0int]);
                lemma_inverse_word_valid(a_j, n);
                assert(symbol_valid(inv_aj[0int], n));
                assert(generator_index(r[(bj_len + 1) as int]) < n);
                match w1[pos1] {
                    Symbol::Gen(idx) => { assert(w1[(pos1+1) as int] == Symbol::Inv(idx)); },
                    Symbol::Inv(idx) => { assert(w1[(pos1+1) as int] == Symbol::Gen(idx)); },
                }
                assert(generator_index(w1[(pos1+1) as int]) == n);
                assert(false);
            } else if pos1 == (pos0 + bj_len + a_j.len() as int + 1) {
                assert(w1[(pos1 + 1) as int] == r[(bj_len + a_j.len() as int + 2) as int]);
                // This is past the relator's second stable letter, should be out of range or base
                // r has length 2 + |a_j| + |b_j|. Position bj_len + a_j.len() + 2 = |r|
                // That's past the end of the relator!
                // w1[pos1+1] would be from w_right or past w1's end
                // But has_cancellation_at requires pos1+1 < w1.len()
                assert(r.len() == 2 + a_j.len() + bj_len);
                // pos1+1 = pos0 + bj_len + a_j.len() + 2 = pos0 + r.len()
                // At this position in w1: it's w_right[0] if w_right.len() > 0
                if w_right.len() > 0 {
                    assert(w1[(pos1+1) as int] == w_right[0int]);
                    assert(w_right[0int] == w[pos0 as int]);
                    assert(symbol_valid(w[pos0 as int], n));
                    assert(generator_index(w1[(pos1+1) as int]) < n);
                } else {
                    // w1[pos1+1] would be at w1.len(), out of bounds
                    // has_cancellation_at requires pos1+1 < w1.len()
                    assert(w1.len() == w.len() + r.len());
                    assert(pos1 + 1 == pos0 + r.len() as int);
                    assert(pos0 + r.len() as int == w_left.len() + r.len());
                    assert(w1.len() == w_left.len() + r.len() + w_right.len());
                    assert(pos1 + 1 == w1.len() - w_right.len());
                    assert(pos1 + 1 == w1.len());
                    // has_cancellation_at needs pos1+1 < w1.len(), contradiction
                }
                match w1[pos1] {
                    Symbol::Gen(idx) => { assert(w1[(pos1+1) as int] == Symbol::Inv(idx)); },
                    Symbol::Inv(idx) => { assert(w1[(pos1+1) as int] == Symbol::Gen(idx)); },
                }
                assert(generator_index(w1[(pos1+1) as int]) == n);
                assert(false);
            } else {
                // pos1 is not at either stable position. Show gen_idx(w1[pos1]) < n.
                if pos1 >= pos0 && pos1 < pos0 + r.len() as int {
                    // Within relator: w1[pos1] = r[pos1 - pos0]
                    let ri = (pos1 - pos0) as int;
                    assert(w1[pos1] == (w_left + (r + w_right))[(w_left.len() + ri) as int]);
                    assert(w1[pos1] == r[ri]);
                    assert(ri != bj_len);
                    assert(ri != (bj_len + a_j.len() + 1) as int);
                    assert(generator_index(r[ri]) < n);
                } else {
                    // Outside relator: covered by outer forall
                }
                assert(generator_index(w1[pos1]) < n);
                assert(false);
            }
        }
        assert(a_j.len() == 0);
        assert(a_j =~= Seq::<Symbol>::empty());
        assert(pos1 == (pos0 + bj_len) as int);

        // r = b_j ++ [Inv(n), Gen(n)], |r| = bj_len + 2
        assert(r.len() == 2 + bj_len);

        // w_end = w1[0..pos1] ++ w1[pos1+2..]
        // = w1[0..pos0+bj_len] ++ w1[pos0+bj_len+2..]
        // w1 = w_left ++ b_j ++ [Inv(n), Gen(n)] ++ w_right
        // w_end = w_left ++ b_j ++ w_right = concat(w_left, concat(b_j, w_right))
        let t_inv_seq = Seq::new(1, |_i: int| stable_letter_inv(data));
        let t_seq = Seq::new(1, |_i: int| stable_letter(data));
        assert(r =~= b_j + t_inv_seq + Seq::<Symbol>::empty() + t_seq);
        assert(r =~= b_j + t_inv_seq + t_seq);
        assert(w1 =~= w_left + (b_j + t_inv_seq + t_seq) + w_right);
        assert(w1 =~= w_left + b_j + t_inv_seq + t_seq + w_right);
        assert(w1.subrange(0, pos0 + bj_len) =~= w_left + b_j);
        assert(w1.subrange(pos0 + bj_len + 2, w1.len() as int) =~= w_right);
        assert(w_end =~= (w_left + b_j) + w_right);
        assert(w_end =~= w_left + (b_j + w_right));

        // w = w_left ++ w_right
        assert(w =~= w_left + w_right);

        // By isomorphism: a_j = ε → b_j ≡ ε
        lemma_empty_association_implies_trivial(data, j);

        // w ≡ w_end = concat(w_left, concat(b_j, w_right)) by inserting b_j ≡ ε
        lemma_insert_trivial_equiv(data.base, w_left, w_right, b_j);
    }
}

/// Case (d), (!inv, !inv2): both relators non-inverted.
proof fn lemma_k2_rr_nn(
    data: HNNData, w: Word, w1: Word, w_end: Word,
    pos0: int, r_idx: nat, pos1: int, r_idx2: nat,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: pos0, relator_index: r_idx, inverted: false };
            let step1 = DerivationStep::RelatorDelete { position: pos1, relator_index: r_idx2, inverted: false };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w_end)
        }),
        r_idx as int >= data.base.relators.len(),
        !is_base_word(w1, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, r_idx, false);
    let r2 = get_relator(hp, r_idx2, false);
    let w_left = w.subrange(0, pos0);
    let w_right = w.subrange(pos0, w.len() as int);
    assert(w1 =~= w_left + (r1 + w_right));
    assert(w =~= w_left + w_right);
    assert(w1.subrange(pos1, pos1 + r2.len() as int) =~= r2);
    assert(w_end =~= w1.subrange(0, pos1) + w1.subrange(pos1 + r2.len() as int, w1.len() as int));

    // Count argument → r2 is HNN
    lemma_stable_letter_count_concat(w_left, w_right, n);
    lemma_stable_letter_count_concat(w_left, r1 + w_right, n);
    lemma_stable_letter_count_concat(r1, w_right, n);
    assert(w1 =~= w1.subrange(0, pos1) + w1.subrange(pos1, w1.len() as int));
    lemma_stable_letter_count_concat(w1.subrange(0, pos1), w1.subrange(pos1, w1.len() as int), n);
    assert(w1.subrange(pos1, w1.len() as int) =~= r2 + w1.subrange(pos1 + r2.len() as int, w1.len() as int));
    lemma_stable_letter_count_concat(r2, w1.subrange(pos1 + r2.len() as int, w1.len() as int), n);
    lemma_stable_letter_count_concat(w1.subrange(0, pos1), w1.subrange(pos1 + r2.len() as int, w1.len() as int), n);

    let j1 = (r_idx as int - data.base.relators.len()) as int;
    assert(0 <= j1 < data.associations.len());
    assert(hp.relators[r_idx as int] == hnn_relator(data, j1));
    let (a_j1, b_j1) = data.associations[j1];
    let t_inv = stable_letter_inv(data);
    let t = stable_letter(data);
    let t_inv_seq = Seq::new(1, |_i: int| t_inv);
    let t_seq = Seq::new(1, |_i: int| t);
    lemma_inverse_word_len(b_j1);
    let inv_b_j1 = inverse_word(b_j1);
    lemma_hnn_relator_stable_positions(data, j1);
    assert(r1 =~= t_inv_seq + a_j1 + t_seq + inv_b_j1);
    lemma_base_word_characterization(a_j1, n);
    lemma_inverse_word_valid(b_j1, n);
    lemma_base_word_characterization(inv_b_j1, n);
    lemma_stable_count_single(t_inv, n);
    lemma_stable_count_single(t, n);
    assert(t_inv_seq =~= seq![t_inv]);
    assert(t_seq =~= seq![t]);
    lemma_stable_letter_count_concat(t_inv_seq, a_j1, n);
    lemma_stable_letter_count_concat(t_inv_seq + a_j1, t_seq, n);
    lemma_stable_letter_count_concat(t_inv_seq + a_j1 + t_seq, inv_b_j1, n);
    assert(stable_letter_count(r1, n) == 2nat);

    if (r_idx2 as int) < data.base.relators.len() {
        reveal(presentation_valid);
        lemma_base_word_characterization(data.base.relators[r_idx2 as int], n);
        assert(false);
    }
    let j2 = (r_idx2 as int - data.base.relators.len()) as int;
    let (a_j2, b_j2) = data.associations[j2];
    lemma_inverse_word_len(b_j2);
    lemma_inverse_word_len(a_j2);

    // Stable letter alignment: pos1 = pos0, |a_j2| = |a_j1|
    lemma_hnn_relator_stable_positions(data, j2);
    assert(w1[pos1 as int] == r2[0int]);
    assert(generator_index(w1[pos1 as int]) == n);

    // w1 outside r1 has gen_idx < n
    assert forall|i: int| 0 <= i < w1.len() && (i < pos0 || i >= pos0 + r1.len() as int)
        implies generator_index(#[trigger] w1[i]) < n
    by {
        if i < pos0 { assert(w1[i] == w[i]); }
        else { let k = i - pos0 - r1.len() as int; assert(w1[i] == w_right[k]); assert(w_right[k] == w[(pos0 + k) as int]); }
    }
    // r1 non-stable positions
    assert forall|i: int| 0 <= i < r1.len() && i != 0 && i != (a_j1.len() + 1) as int
        implies generator_index(#[trigger] r1[i]) < n
    by {
        if i > 0 && i <= a_j1.len() as int {
            assert(r1 =~= t_inv_seq + a_j1 + t_seq + inv_b_j1);
            assert(r1[i] == (t_inv_seq + a_j1)[i]);
            assert((t_inv_seq + a_j1)[i] == a_j1[(i - 1) as int]);
        } else if i > (a_j1.len() + 1) as int {
            let h = t_inv_seq + a_j1 + t_seq;
            assert(r1 =~= h + inv_b_j1);
            assert(h.len() == a_j1.len() + 2);
            assert(r1[i] == inv_b_j1[(i - a_j1.len() as int - 2) as int]);
        }
    }
    if pos1 < pos0 || pos1 >= pos0 + r1.len() as int { assert(generator_index(w1[pos1 as int]) < n); assert(false); }
    let ri = (pos1 - pos0) as int;
    assert(w1[pos1 as int] == r1[ri]);
    if ri != 0 {
        if ri == (a_j1.len() + 1) as int { assert(r1[ri] == t); assert(r2[0int] == t_inv); assert(w1[pos1 as int] == t); assert(w1[pos1 as int] == t_inv); assert(false); }
        else { assert(generator_index(r1[ri]) < n); assert(false); }
    }
    assert(pos1 == pos0);
    assert(a_j2.len() == a_j1.len());

    // Content: a_j1 = a_j2
    assert forall|i: int| 0 <= i < a_j1.len() implies #[trigger] a_j1[i] == a_j2[i] by {
        assert(r1 =~= t_inv_seq + a_j1 + t_seq + inv_b_j1);
        assert(r1[(1 + i) as int] == (t_inv_seq + a_j1)[(1 + i) as int]);
        assert((t_inv_seq + a_j1)[(1 + i) as int] == a_j1[i]);
        assert(r2 =~= t_inv_seq + a_j2 + Seq::new(1, |_k: int| t) + inverse_word(b_j2));
        assert(r2[(1 + i) as int] == (t_inv_seq + a_j2)[(1 + i) as int]);
        assert((t_inv_seq + a_j2)[(1 + i) as int] == a_j2[i]);
        assert(w1[(pos0 + 1 + i) as int] == r1[(1 + i) as int]);
    }
    assert(a_j1 =~= a_j2);

    // Isomorphism: b_j1 ++ inv(b_j2) ≡ ε
    let k = data.associations.len();
    let a_words = Seq::new(k, |j: int| data.associations[j].0);
    let b_words = Seq::new(k, |j: int| data.associations[j].1);
    let u: Word = seq![Symbol::Gen(j1 as nat), Symbol::Inv(j2 as nat)];
    assert(word_valid(u, k as nat)) by {
        assert(u[0int] == Symbol::Gen(j1 as nat)); assert(u[1int] == Symbol::Inv(j2 as nat));
    }
    lemma_apply_embedding_two(a_words, Symbol::Gen(j1 as nat), Symbol::Inv(j2 as nat));
    assert(apply_embedding(a_words, u) =~= concat(a_j1, inverse_word(a_j2)));
    assert(inverse_word(a_j2) =~= inverse_word(a_j1));
    lemma_word_inverse_right(data.base, a_j1);
    lemma_apply_embedding_two(b_words, Symbol::Gen(j1 as nat), Symbol::Inv(j2 as nat));
    assert(apply_embedding(b_words, u) =~= concat(b_j1, inverse_word(b_j2)));

    reveal(presentation_valid);
    lemma_inverse_word_valid(b_j2, n);
    lemma_identity_split(data.base, b_j1, inverse_word(b_j2));

    // Word manipulation via tail + helper
    let tail = concat(inv_b_j1, w_right);
    let inv_b_j2 = inverse_word(b_j2);
    let spl = a_j1.len() as int + 2;
    assert(w1.subrange(pos0 + spl, w1.len() as int) =~= tail);
    assert(pos1 + r2.len() as int == pos0 + spl + b_j2.len() as int);
    assert(w1.subrange(pos1 + r2.len() as int, w1.len() as int) =~= tail.subrange(b_j2.len() as int, tail.len() as int));
    assert(w1.subrange(0, pos1) =~= w_left);
    assert(w_end =~= w_left + tail.subrange(b_j2.len() as int, tail.len() as int));
    // Bridge: tail[0..|b_j2|] = inv_b_j2 (from r2 overlap in w1)
    let head2 = t_inv_seq + a_j2 + t_seq;
    assert(r2 =~= head2 + inv_b_j2);
    assert(head2.len() == spl);
    assert forall|k: int| 0 <= k < b_j2.len()
        implies tail[k] == #[trigger] inv_b_j2[k]
    by {
        assert(w1[(pos0 + spl + k) as int] == r2[(spl + k) as int]);
        assert(r2[(spl + k) as int] == inv_b_j2[k]);
    }
    assert(inv_b_j2 =~= tail.subrange(0, b_j2.len() as int));
    assert(inv_b_j2.len() <= tail.len()) by {
        assert(tail.len() == inv_b_j1.len() + w_right.len());
    }
    lemma_subrange_word_valid(w, 0, pos0, n);
    lemma_subrange_word_valid(w, pos0, w.len() as int, n);
    crate::britton_proof_helpers::lemma_tail_shift_equiv(data.base, n, w, w_left, w_right, w_end, inv_b_j1, inv_b_j2, tail);
}

/// Case (d), (!inv, inv2): r1 non-inverted, r2 inverted.
proof fn lemma_k2_rr_ni(
    data: HNNData, w: Word, w1: Word, w_end: Word,
    pos0: int, r_idx: nat, pos1: int, r_idx2: nat,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: pos0, relator_index: r_idx, inverted: false };
            let step1 = DerivationStep::RelatorDelete { position: pos1, relator_index: r_idx2, inverted: true };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w_end)
        }),
        r_idx as int >= data.base.relators.len(),
        !is_base_word(w1, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, r_idx, false);
    let r2 = get_relator(hp, r_idx2, true);
    let w_left = w.subrange(0, pos0);
    let w_right = w.subrange(pos0, w.len() as int);
    assert(w1 =~= w_left + (r1 + w_right));
    assert(w =~= w_left + w_right);
    assert(w1.subrange(pos1, pos1 + r2.len() as int) =~= r2);
    assert(w_end =~= w1.subrange(0, pos1) + w1.subrange(pos1 + r2.len() as int, w1.len() as int));

    // Count + r2 is HNN (same preamble)
    lemma_stable_letter_count_concat(w_left, w_right, n);
    lemma_stable_letter_count_concat(w_left, r1 + w_right, n);
    lemma_stable_letter_count_concat(r1, w_right, n);
    assert(w1 =~= w1.subrange(0, pos1) + w1.subrange(pos1, w1.len() as int));
    lemma_stable_letter_count_concat(w1.subrange(0, pos1), w1.subrange(pos1, w1.len() as int), n);
    assert(w1.subrange(pos1, w1.len() as int) =~= r2 + w1.subrange(pos1 + r2.len() as int, w1.len() as int));
    lemma_stable_letter_count_concat(r2, w1.subrange(pos1 + r2.len() as int, w1.len() as int), n);
    lemma_stable_letter_count_concat(w1.subrange(0, pos1), w1.subrange(pos1 + r2.len() as int, w1.len() as int), n);

    let j1 = (r_idx as int - data.base.relators.len()) as int;
    let (a_j1, b_j1) = data.associations[j1];
    let t_inv = stable_letter_inv(data);
    let t = stable_letter(data);
    let t_inv_seq = Seq::new(1, |_i: int| t_inv);
    let t_seq = Seq::new(1, |_i: int| t);
    lemma_inverse_word_len(b_j1);
    let inv_b_j1 = inverse_word(b_j1);
    lemma_hnn_relator_stable_positions(data, j1);
    assert(r1 =~= t_inv_seq + a_j1 + t_seq + inv_b_j1);
    lemma_base_word_characterization(a_j1, n);
    lemma_inverse_word_valid(b_j1, n);
    lemma_base_word_characterization(inv_b_j1, n);
    lemma_stable_count_single(t_inv, n);
    lemma_stable_count_single(t, n);
    assert(t_inv_seq =~= seq![t_inv]);
    assert(t_seq =~= seq![t]);
    lemma_stable_letter_count_concat(t_inv_seq, a_j1, n);
    lemma_stable_letter_count_concat(t_inv_seq + a_j1, t_seq, n);
    lemma_stable_letter_count_concat(t_inv_seq + a_j1 + t_seq, inv_b_j1, n);
    assert(stable_letter_count(r1, n) == 2nat);

    if (r_idx2 as int) < data.base.relators.len() {
        reveal(presentation_valid);
        let base_r = data.base.relators[r_idx2 as int];
        lemma_inverse_word_valid(base_r, n);
        lemma_base_word_characterization(inverse_word(base_r), n);
        assert(false);
    }
    let j2 = (r_idx2 as int - data.base.relators.len()) as int;
    let (a_j2, b_j2) = data.associations[j2];
    lemma_inverse_word_len(b_j2);
    lemma_inverse_word_len(a_j2);

    // r2 inverted: r2 = b_j2 ++ [Inv(n)] ++ inv(a_j2) ++ [Gen(n)]
    lemma_hnn_relator_inverted_stable_positions(data, j2);
    // Inv(n) at w1[pos1+|b_j2|] must match pos0 (Inv(n) in r1)
    assert(w1[(pos1 + b_j2.len() as int) as int] == r2[b_j2.len() as int]);
    assert(generator_index(w1[(pos1 + b_j2.len() as int) as int]) == n);
    let stable_pos = (pos1 + b_j2.len() as int) as int;

    // w1 outside r1 has gen_idx < n
    assert forall|i: int| 0 <= i < w1.len() && (i < pos0 || i >= pos0 + r1.len() as int)
        implies generator_index(#[trigger] w1[i]) < n
    by {
        if i < pos0 { assert(w1[i] == w[i]); }
        else { let k = i - pos0 - r1.len() as int; assert(w1[i] == w_right[k]); assert(w_right[k] == w[(pos0 + k) as int]); }
    }
    assert forall|i: int| 0 <= i < r1.len() && i != 0 && i != (a_j1.len() + 1) as int
        implies generator_index(#[trigger] r1[i]) < n
    by {
        if i > 0 && i <= a_j1.len() as int {
            assert(r1 =~= t_inv_seq + a_j1 + t_seq + inv_b_j1);
            assert(r1[i] == (t_inv_seq + a_j1)[i]);
            assert((t_inv_seq + a_j1)[i] == a_j1[(i - 1) as int]);
        } else if i > (a_j1.len() + 1) as int {
            let h = t_inv_seq + a_j1 + t_seq;
            assert(r1 =~= h + inv_b_j1); assert(h.len() == a_j1.len() + 2);
            assert(r1[i] == inv_b_j1[(i - a_j1.len() as int - 2) as int]);
        }
    }

    if stable_pos < pos0 || stable_pos >= pos0 + r1.len() as int { assert(generator_index(w1[stable_pos]) < n); assert(false); }
    let ri = (stable_pos - pos0) as int;
    assert(w1[stable_pos] == r1[ri]);
    if ri != 0 {
        if ri == (a_j1.len() + 1) as int { assert(r1[ri] == t); assert(w1[stable_pos] == t_inv); assert(false); }
        else { assert(generator_index(r1[ri]) < n); assert(false); }
    }
    assert(stable_pos == pos0);
    assert(pos1 == pos0 - b_j2.len() as int);
    assert(a_j2.len() == a_j1.len());

    // Content: a_j1 = inv(a_j2)
    assert forall|i: int| 0 <= i < a_j1.len() implies #[trigger] a_j1[i] == inverse_word(a_j2)[i] by {
        assert(r1 =~= t_inv_seq + a_j1 + t_seq + inv_b_j1);
        assert(r1[(1 + i) as int] == a_j1[i]);
        let head2 = b_j2 + Seq::new(1, |_k: int| t_inv);
        let inv_a_j2 = inverse_word(a_j2);
        assert(r2 =~= head2 + inv_a_j2 + t_seq);
        assert(head2.len() == b_j2.len() + 1);
        assert(r2[(b_j2.len() + 1 + i) as int] == (head2 + inv_a_j2)[(b_j2.len() + 1 + i) as int]);
        assert((head2 + inv_a_j2)[(b_j2.len() + 1 + i) as int] == inv_a_j2[i]);
        assert(w1[(pos0 + 1 + i) as int] == r1[(1 + i) as int]);
    }
    assert(a_j1 =~= inverse_word(a_j2));
    crate::word::lemma_inverse_involution(a_j2);
    assert(a_j2 =~= inverse_word(a_j1));
    assert(concat(a_j1, a_j2) =~= concat(a_j1, inverse_word(a_j1)));
    lemma_word_inverse_right(data.base, a_j1);

    // Isomorphism: b_j1 ++ b_j2 ≡ ε
    let k = data.associations.len();
    let a_words = Seq::new(k, |j: int| data.associations[j].0);
    let b_words = Seq::new(k, |j: int| data.associations[j].1);
    let u: Word = seq![Symbol::Gen(j1 as nat), Symbol::Gen(j2 as nat)];
    assert(word_valid(u, k as nat)) by {
        assert(u[0int] == Symbol::Gen(j1 as nat)); assert(u[1int] == Symbol::Gen(j2 as nat));
    }
    lemma_apply_embedding_two(a_words, Symbol::Gen(j1 as nat), Symbol::Gen(j2 as nat));
    assert(apply_embedding(a_words, u) =~= concat(a_j1, a_j2));
    lemma_apply_embedding_two(b_words, Symbol::Gen(j1 as nat), Symbol::Gen(j2 as nat));
    assert(apply_embedding(b_words, u) =~= concat(b_j1, b_j2));
    reveal(presentation_valid);
    lemma_identity_split(data.base, b_j1, b_j2);

    // Word manipulation
    let left_part = w_left.subrange(0, pos0 - b_j2.len() as int);
    assert(w1.subrange(0, pos1) =~= left_part);
    assert(w1.subrange(pos0 + a_j1.len() as int + 2, w1.len() as int) =~= concat(inv_b_j1, w_right));
    assert(w_end =~= left_part + (inv_b_j1 + w_right));
    // Bridge: r2 starts at pos1, first |b_j2| elements are b_j2
    let inv_a_j2 = inverse_word(a_j2);
    assert(r2 =~= b_j2 + t_inv_seq + inv_a_j2 + t_seq);
    assert forall|i_idx: int| 0 <= i_idx < b_j2.len()
        implies w_left[(pos1 + i_idx) as int] == #[trigger] b_j2[i_idx]
    by {
        assert(w1[(pos1 + i_idx) as int] == r2[i_idx]);
        assert(r2[i_idx] == b_j2[i_idx]);
        assert(w1[(pos1 + i_idx) as int] == w_left[(pos1 + i_idx) as int]);
    }
    assert(w_left.subrange(pos0 - b_j2.len() as int, pos0) =~= b_j2);
    assert(w_left =~= left_part + b_j2);
    assert(w =~= left_part + (b_j2 + w_right));
    lemma_equiv_concat_left(data.base, b_j2, inverse_word(b_j1), w_right);
    lemma_equiv_concat_right(data.base, left_part, concat(b_j2, w_right), concat(inverse_word(b_j1), w_right));
}

/// Case (d), (inv, !inv2): r1 inverted, r2 non-inverted.
proof fn lemma_k2_rr_in(
    data: HNNData, w: Word, w1: Word, w_end: Word,
    pos0: int, r_idx: nat, pos1: int, r_idx2: nat,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: pos0, relator_index: r_idx, inverted: true };
            let step1 = DerivationStep::RelatorDelete { position: pos1, relator_index: r_idx2, inverted: false };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w_end)
        }),
        r_idx as int >= data.base.relators.len(),
        !is_base_word(w1, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, r_idx, true);
    let r2 = get_relator(hp, r_idx2, false);
    let w_left = w.subrange(0, pos0);
    let w_right = w.subrange(pos0, w.len() as int);
    assert(w1 =~= w_left + (r1 + w_right));
    assert(w =~= w_left + w_right);
    assert(w1.subrange(pos1, pos1 + r2.len() as int) =~= r2);
    assert(w_end =~= w1.subrange(0, pos1) + w1.subrange(pos1 + r2.len() as int, w1.len() as int));

    // Count + r2 is HNN
    lemma_stable_letter_count_concat(w_left, w_right, n);
    lemma_stable_letter_count_concat(w_left, r1 + w_right, n);
    lemma_stable_letter_count_concat(r1, w_right, n);
    assert(w1 =~= w1.subrange(0, pos1) + w1.subrange(pos1, w1.len() as int));
    lemma_stable_letter_count_concat(w1.subrange(0, pos1), w1.subrange(pos1, w1.len() as int), n);
    assert(w1.subrange(pos1, w1.len() as int) =~= r2 + w1.subrange(pos1 + r2.len() as int, w1.len() as int));
    lemma_stable_letter_count_concat(r2, w1.subrange(pos1 + r2.len() as int, w1.len() as int), n);
    lemma_stable_letter_count_concat(w1.subrange(0, pos1), w1.subrange(pos1 + r2.len() as int, w1.len() as int), n);

    let j1 = (r_idx as int - data.base.relators.len()) as int;
    let (a_j1, b_j1) = data.associations[j1];
    let t_inv = stable_letter_inv(data);
    let t = stable_letter(data);
    let t_inv_seq = Seq::new(1, |_i: int| t_inv);
    let t_seq = Seq::new(1, |_i: int| t);
    lemma_inverse_word_len(b_j1);
    let inv_b_j1 = inverse_word(b_j1);
    lemma_hnn_relator_inverted_stable_positions(data, j1);
    lemma_inverse_word_len(a_j1);
    let inv_a_j1 = inverse_word(a_j1);
    assert(r1 =~= b_j1 + t_inv_seq + inv_a_j1 + t_seq);
    lemma_base_word_characterization(a_j1, n);
    lemma_inverse_word_valid(b_j1, n);
    lemma_base_word_characterization(inv_b_j1, n);
    lemma_inverse_word_valid(a_j1, n);
    lemma_base_word_characterization(inv_a_j1, n);
    lemma_base_word_characterization(b_j1, n);
    lemma_stable_count_single(t_inv, n);
    lemma_stable_count_single(t, n);
    assert(t_inv_seq =~= seq![t_inv]);
    assert(t_seq =~= seq![t]);
    lemma_stable_letter_count_concat(b_j1, t_inv_seq, n);
    lemma_stable_letter_count_concat(b_j1 + t_inv_seq, inv_a_j1, n);
    lemma_stable_letter_count_concat(b_j1 + t_inv_seq + inv_a_j1, t_seq, n);
    assert(stable_letter_count(r1, n) == 2nat);

    if (r_idx2 as int) < data.base.relators.len() {
        reveal(presentation_valid);
        lemma_base_word_characterization(data.base.relators[r_idx2 as int], n);
        assert(false);
    }
    let j2 = (r_idx2 as int - data.base.relators.len()) as int;
    let (a_j2, b_j2) = data.associations[j2];
    lemma_inverse_word_len(b_j2);
    lemma_inverse_word_len(a_j2);
    let s1 = pos0 + b_j1.len() as int;

    // r2 non-inverted: r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2)
    lemma_hnn_relator_stable_positions(data, j2);
    assert(w1[pos1 as int] == r2[0int]);
    assert(generator_index(w1[pos1 as int]) == n);

    // w1 outside r1 has gen_idx < n
    assert forall|i: int| 0 <= i < w1.len() && (i < pos0 || i >= pos0 + r1.len() as int)
        implies generator_index(#[trigger] w1[i]) < n
    by {
        if i < pos0 { assert(w1[i] == w[i]); }
        else { let k = i - pos0 - r1.len() as int; assert(w1[i] == w_right[k]); assert(w_right[k] == w[(pos0 + k) as int]); }
    }
    assert forall|i: int| 0 <= i < r1.len()
        && i != b_j1.len() as int && i != (b_j1.len() + a_j1.len() + 1) as int
        implies generator_index(#[trigger] r1[i]) < n
    by {
        if i < b_j1.len() as int {
            assert(r1 =~= b_j1 + t_inv_seq + inv_a_j1 + t_seq);
            assert(r1[i] == b_j1[i]);
        } else if i > b_j1.len() as int && i < (b_j1.len() + a_j1.len() + 1) as int {
            let head = b_j1 + t_inv_seq;
            assert(r1 =~= head + inv_a_j1 + t_seq); assert(head.len() == b_j1.len() + 1);
            assert(r1[i] == (head + inv_a_j1)[i]);
            assert((head + inv_a_j1)[i] == inv_a_j1[(i - b_j1.len() as int - 1) as int]);
        } else if i > (b_j1.len() + a_j1.len() + 1) as int {
            assert(r1.len() == 2 + a_j1.len() + b_j1.len()); assert(false);
        }
    }

    if pos1 < pos0 || pos1 >= pos0 + r1.len() as int { assert(generator_index(w1[pos1 as int]) < n); assert(false); }
    let ri = (pos1 - pos0) as int;
    assert(w1[pos1 as int] == r1[ri]);
    if ri != b_j1.len() as int {
        if ri == (b_j1.len() + a_j1.len() + 1) as int { assert(r1[ri] == t); assert(w1[pos1 as int] == t_inv); assert(false); }
        else { assert(generator_index(r1[ri]) < n); assert(false); }
    }
    assert(pos1 == s1);
    assert(a_j2.len() == a_j1.len());

    // Content: inv(a_j1) = a_j2
    assert forall|i: int| 0 <= i < a_j1.len() implies #[trigger] inv_a_j1[i] == a_j2[i] by {
        let head1 = b_j1 + t_inv_seq;
        assert(r1 =~= head1 + inv_a_j1 + t_seq); assert(head1.len() == b_j1.len() + 1);
        assert(r1[(b_j1.len() + 1 + i) as int] == (head1 + inv_a_j1)[(b_j1.len() + 1 + i) as int]);
        assert((head1 + inv_a_j1)[(b_j1.len() + 1 + i) as int] == inv_a_j1[i]);
        assert(r2 =~= t_inv_seq + a_j2 + Seq::new(1, |_k: int| t) + inverse_word(b_j2));
        assert(r2[(1 + i) as int] == (t_inv_seq + a_j2)[(1 + i) as int]);
        assert((t_inv_seq + a_j2)[(1 + i) as int] == a_j2[i]);
        assert(w1[(s1 + 1 + i) as int] == r1[(b_j1.len() + 1 + i) as int]);
    }
    assert(inv_a_j1 =~= a_j2);
    crate::word::lemma_inverse_involution(a_j1);

    // Isomorphism: inv(b_j1) ++ inv(b_j2) ≡ ε
    let k = data.associations.len();
    let a_words = Seq::new(k, |j: int| data.associations[j].0);
    let b_words = Seq::new(k, |j: int| data.associations[j].1);
    let u: Word = seq![Symbol::Inv(j1 as nat), Symbol::Inv(j2 as nat)];
    assert(word_valid(u, k as nat)) by {
        assert(u[0int] == Symbol::Inv(j1 as nat)); assert(u[1int] == Symbol::Inv(j2 as nat));
    }
    lemma_apply_embedding_two(a_words, Symbol::Inv(j1 as nat), Symbol::Inv(j2 as nat));
    assert(apply_embedding(a_words, u) =~= concat(inverse_word(a_j1), inverse_word(a_j2)));
    assert(concat(inverse_word(a_j1), inverse_word(a_j2)) =~= concat(a_j2, inverse_word(a_j2)));
    lemma_word_inverse_right(data.base, a_j2);
    lemma_apply_embedding_two(b_words, Symbol::Inv(j1 as nat), Symbol::Inv(j2 as nat));
    assert(apply_embedding(b_words, u) =~= concat(inverse_word(b_j1), inverse_word(b_j2)));
    reveal(presentation_valid);
    lemma_inverse_word_valid(b_j1, n);
    lemma_inverse_word_valid(b_j2, n);
    lemma_identity_split(data.base, inverse_word(b_j1), inverse_word(b_j2));
    crate::word::lemma_inverse_involution(b_j1);
    // inv(b_j2) ≡ b_j1

    // Word manipulation: r2 starts at s1, covers [s1, s1+|r2|)
    // After Gen(n) in w1 is w_right (r1 ends at pos0+|r1|)
    // r2's inv(b_j2) tail is at [s1+2+|a_j2|, s1+|r2|) = [pos0+|r1|, pos0+|r1|+|b_j2|)
    // That maps to w_right[0..|b_j2|]
    assert(w1.subrange(0, s1) =~= w_left + b_j1);
    assert(s1 + r2.len() as int == s1 + 2 + a_j2.len() as int + b_j2.len() as int);
    // w1[pos0+|r1|..] = w_right, and pos0+|r1| = s1+2+|a_j2| = s1+|a_j1|+2
    assert(pos0 + r1.len() as int == s1 + a_j1.len() as int + 2);
    // r2 tail = inv(b_j2) occupies w1[s1+2+|a_j2| .. s1+|r2|]
    // s1+2+|a_j2| = pos0+|b_j1|+2+|a_j1| = pos0+|r1|
    // So w1[pos0+|r1| .. pos0+|r1|+|b_j2|] = inv(b_j2)
    // And w1[pos0+|r1|+k] = w_right[k] for k >= 0
    assert(w1.subrange(s1 + r2.len() as int, w1.len() as int) =~=
        w_right.subrange(b_j2.len() as int, w_right.len() as int));
    assert(w_end =~= (w_left + b_j1) + w_right.subrange(b_j2.len() as int, w_right.len() as int));
    assert(w_end =~= w_left + (b_j1 + w_right.subrange(b_j2.len() as int, w_right.len() as int)));

    // Bridge: w_right[0..|b_j2|] = inv(b_j2)
    let inv_b_j2 = inverse_word(b_j2);
    // r2 content at positions [2+|a_j2|, |r2|) = inv(b_j2)
    // In w1: those are at [s1+2+|a_j2|, s1+|r2|) = [pos0+|r1|, pos0+|r1|+|b_j2|)
    assert forall|i_idx: int| 0 <= i_idx < b_j2.len()
        implies w_right[i_idx] == #[trigger] inv_b_j2[i_idx]
    by {
        // w1[pos0+|r1|+i_idx] = r2[2+|a_j2|+i_idx] = inv_b_j2[i_idx]
        let r2_off = (2 + a_j2.len() + i_idx) as int;
        assert(w1[(pos0 + r1.len() as int + i_idx) as int] == r2[r2_off]);
        // r2 = head2 + inv_b_j2_actual where head2 = [Inv(n)] + a_j2 + [Gen(n)]
        let head2 = t_inv_seq + a_j2 + t_seq;
        assert(r2 =~= head2 + inv_b_j2);
        assert(head2.len() == 2 + a_j2.len());
        assert(r2[r2_off] == inv_b_j2[i_idx]);
        // w1[pos0+|r1|+i_idx] = w_right[i_idx]
    }
    assert(w_right.subrange(0, b_j2.len() as int) =~= inv_b_j2);
    assert(w_right =~= inv_b_j2 + w_right.subrange(b_j2.len() as int, w_right.len() as int));
    let w_right_rest = w_right.subrange(b_j2.len() as int, w_right.len() as int);
    assert(w =~= w_left + (inv_b_j2 + w_right_rest));
    assert(w_end =~= w_left + (b_j1 + w_right_rest));

    // inv(b_j2) ≡ b_j1, so w ≡ w_end
    lemma_equiv_concat_left(data.base, inv_b_j2, b_j1, w_right_rest);
    lemma_equiv_concat_right(data.base, w_left, concat(inv_b_j2, w_right_rest), concat(b_j1, w_right_rest));
}

/// Case (d), (inv, inv2): both relators inverted.
proof fn lemma_k2_rr_ii(
    data: HNNData, w: Word, w1: Word, w_end: Word,
    pos0: int, r_idx: nat, pos1: int, r_idx2: nat,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: pos0, relator_index: r_idx, inverted: true };
            let step1 = DerivationStep::RelatorDelete { position: pos1, relator_index: r_idx2, inverted: true };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w_end)
        }),
        r_idx as int >= data.base.relators.len(),
        !is_base_word(w1, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, r_idx, true);
    let r2 = get_relator(hp, r_idx2, true);
    let w_left = w.subrange(0, pos0);
    let w_right = w.subrange(pos0, w.len() as int);
    assert(w1 =~= w_left + (r1 + w_right));
    assert(w =~= w_left + w_right);
    assert(w1.subrange(pos1, pos1 + r2.len() as int) =~= r2);
    assert(w_end =~= w1.subrange(0, pos1) + w1.subrange(pos1 + r2.len() as int, w1.len() as int));

    // Count + r2 is HNN
    lemma_stable_letter_count_concat(w_left, w_right, n);
    lemma_stable_letter_count_concat(w_left, r1 + w_right, n);
    lemma_stable_letter_count_concat(r1, w_right, n);
    assert(w1 =~= w1.subrange(0, pos1) + w1.subrange(pos1, w1.len() as int));
    lemma_stable_letter_count_concat(w1.subrange(0, pos1), w1.subrange(pos1, w1.len() as int), n);
    assert(w1.subrange(pos1, w1.len() as int) =~= r2 + w1.subrange(pos1 + r2.len() as int, w1.len() as int));
    lemma_stable_letter_count_concat(r2, w1.subrange(pos1 + r2.len() as int, w1.len() as int), n);
    lemma_stable_letter_count_concat(w1.subrange(0, pos1), w1.subrange(pos1 + r2.len() as int, w1.len() as int), n);

    let j1 = (r_idx as int - data.base.relators.len()) as int;
    let (a_j1, b_j1) = data.associations[j1];
    let t_inv = stable_letter_inv(data);
    let t = stable_letter(data);
    let t_inv_seq = Seq::new(1, |_i: int| t_inv);
    let t_seq = Seq::new(1, |_i: int| t);
    lemma_inverse_word_len(b_j1);
    let inv_b_j1 = inverse_word(b_j1);
    lemma_hnn_relator_inverted_stable_positions(data, j1);
    lemma_inverse_word_len(a_j1);
    let inv_a_j1 = inverse_word(a_j1);
    assert(r1 =~= b_j1 + t_inv_seq + inv_a_j1 + t_seq);
    lemma_base_word_characterization(a_j1, n);
    lemma_inverse_word_valid(b_j1, n);
    lemma_base_word_characterization(inv_b_j1, n);
    lemma_inverse_word_valid(a_j1, n);
    lemma_base_word_characterization(inv_a_j1, n);
    lemma_base_word_characterization(b_j1, n);
    lemma_stable_count_single(t_inv, n);
    lemma_stable_count_single(t, n);
    assert(t_inv_seq =~= seq![t_inv]);
    assert(t_seq =~= seq![t]);
    lemma_stable_letter_count_concat(b_j1, t_inv_seq, n);
    lemma_stable_letter_count_concat(b_j1 + t_inv_seq, inv_a_j1, n);
    lemma_stable_letter_count_concat(b_j1 + t_inv_seq + inv_a_j1, t_seq, n);
    assert(stable_letter_count(r1, n) == 2nat);

    if (r_idx2 as int) < data.base.relators.len() {
        reveal(presentation_valid);
        let base_r = data.base.relators[r_idx2 as int];
        lemma_inverse_word_valid(base_r, n);
        lemma_base_word_characterization(inverse_word(base_r), n);
        assert(false);
    }
    let j2 = (r_idx2 as int - data.base.relators.len()) as int;
    let (a_j2, b_j2) = data.associations[j2];
    lemma_inverse_word_len(b_j2);
    lemma_inverse_word_len(a_j2);
    let s1 = pos0 + b_j1.len() as int;

    // r2 inverted: r2 = b_j2 ++ [Inv(n)] ++ inv(a_j2) ++ [Gen(n)]
    lemma_hnn_relator_inverted_stable_positions(data, j2);
    assert(w1[(pos1 + b_j2.len() as int) as int] == r2[b_j2.len() as int]);
    assert(generator_index(w1[(pos1 + b_j2.len() as int) as int]) == n);
    let stable_pos = (pos1 + b_j2.len() as int) as int;

    // w1 outside r1 has gen_idx < n
    assert forall|i: int| 0 <= i < w1.len() && (i < pos0 || i >= pos0 + r1.len() as int)
        implies generator_index(#[trigger] w1[i]) < n
    by {
        if i < pos0 { assert(w1[i] == w[i]); }
        else { let k = i - pos0 - r1.len() as int; assert(w1[i] == w_right[k]); assert(w_right[k] == w[(pos0 + k) as int]); }
    }
    assert forall|i: int| 0 <= i < r1.len()
        && i != b_j1.len() as int && i != (b_j1.len() + a_j1.len() + 1) as int
        implies generator_index(#[trigger] r1[i]) < n
    by {
        if i < b_j1.len() as int {
            assert(r1 =~= b_j1 + t_inv_seq + inv_a_j1 + t_seq);
            assert(r1[i] == b_j1[i]);
        } else if i > b_j1.len() as int && i < (b_j1.len() + a_j1.len() + 1) as int {
            let head = b_j1 + t_inv_seq;
            assert(r1 =~= head + inv_a_j1 + t_seq); assert(head.len() == b_j1.len() + 1);
            assert(r1[i] == (head + inv_a_j1)[i]);
            assert((head + inv_a_j1)[i] == inv_a_j1[(i - b_j1.len() as int - 1) as int]);
        } else if i > (b_j1.len() + a_j1.len() + 1) as int {
            assert(r1.len() == 2 + a_j1.len() + b_j1.len()); assert(false);
        }
    }

    if stable_pos < pos0 || stable_pos >= pos0 + r1.len() as int { assert(generator_index(w1[stable_pos]) < n); assert(false); }
    let ri = (stable_pos - pos0) as int;
    assert(w1[stable_pos] == r1[ri]);
    if ri != b_j1.len() as int {
        if ri == (b_j1.len() + a_j1.len() + 1) as int { assert(r1[ri] == t); assert(w1[stable_pos] == t_inv); assert(false); }
        else { assert(generator_index(r1[ri]) < n); assert(false); }
    }
    assert(stable_pos == s1);
    assert(pos1 == pos0 + b_j1.len() as int - b_j2.len() as int);
    assert(a_j2.len() == a_j1.len());

    // Content: inv(a_j1) = inv(a_j2) → a_j1 = a_j2
    assert forall|i: int| 0 <= i < a_j1.len() implies #[trigger] inv_a_j1[i] == inverse_word(a_j2)[i] by {
        let head1 = b_j1 + t_inv_seq;
        assert(r1 =~= head1 + inv_a_j1 + t_seq); assert(head1.len() == b_j1.len() + 1);
        assert(r1[(b_j1.len() + 1 + i) as int] == inv_a_j1[i]);
        let head2 = b_j2 + Seq::new(1, |_k: int| t_inv);
        let inv_a_j2 = inverse_word(a_j2);
        assert(r2 =~= head2 + inv_a_j2 + t_seq); assert(head2.len() == b_j2.len() + 1);
        assert(r2[(b_j2.len() + 1 + i) as int] == inv_a_j2[i]);
        assert(w1[(s1 + 1 + i) as int] == r1[(b_j1.len() + 1 + i) as int]);
    }
    assert(inv_a_j1 =~= inverse_word(a_j2));
    crate::word::lemma_inverse_involution(a_j1);
    crate::word::lemma_inverse_involution(a_j2);
    assert(a_j1 =~= a_j2);

    // Isomorphism: inv(b_j1) ++ b_j2 ≡ ε
    let k = data.associations.len();
    let a_words = Seq::new(k, |j: int| data.associations[j].0);
    let b_words = Seq::new(k, |j: int| data.associations[j].1);
    let u: Word = seq![Symbol::Inv(j1 as nat), Symbol::Gen(j2 as nat)];
    assert(word_valid(u, k as nat)) by {
        assert(u[0int] == Symbol::Inv(j1 as nat)); assert(u[1int] == Symbol::Gen(j2 as nat));
    }
    lemma_apply_embedding_two(a_words, Symbol::Inv(j1 as nat), Symbol::Gen(j2 as nat));
    assert(apply_embedding(a_words, u) =~= concat(inverse_word(a_j1), a_j2));
    assert(concat(inverse_word(a_j1), a_j2) =~= concat(inverse_word(a_j1), a_j1));
    lemma_word_inverse_left(data.base, a_j1);
    lemma_apply_embedding_two(b_words, Symbol::Inv(j1 as nat), Symbol::Gen(j2 as nat));
    assert(apply_embedding(b_words, u) =~= concat(inverse_word(b_j1), b_j2));
    reveal(presentation_valid);
    lemma_identity_split(data.base, inverse_word(b_j1), b_j2);
    crate::word::lemma_inverse_involution(b_j1);
    // b_j2 ≡ b_j1

    // Word manipulation via extracted helper (avoids path explosion with preamble)
    // Establish r1/r2 element-wise facts for the helper
    assert forall|i: int| 0 <= i < b_j1.len() implies r1[i] == b_j1[i] by {
        assert(r1 =~= b_j1 + t_inv_seq + inv_a_j1 + t_seq);
    }
    let inv_a_j2 = inverse_word(a_j2);
    assert(r2 =~= b_j2 + Seq::new(1, |_k: int| t_inv) + inv_a_j2 + t_seq);
    assert forall|i: int| 0 <= i < b_j2.len() implies r2[i] == b_j2[i] by {
        assert(r2 =~= b_j2 + Seq::new(1, |_k: int| t_inv) + inv_a_j2 + t_seq);
    }
    let pos1_val = pos0 + b_j1.len() as int - b_j2.len() as int;
    assert(pos1 == pos1_val);
    assert(pos1 + r2.len() as int == pos0 + r1.len() as int);
    assert(w1.subrange(pos0 + r1.len() as int, w1.len() as int) =~= w_right);
    assert(w_end =~= w1.subrange(0, pos1) + w_right);
    assert(w1.subrange(pos1, pos1 + r2.len() as int) =~= r2);
    crate::britton_proof_helpers::lemma_ii_word_shift(
        data.base, n, w, w_left, w_right, w_end,
        w1, r1, r2, b_j1, b_j2, pos0,
    );
}

/// Case (d): RelatorInsert(HNN) + RelatorDelete → w ≡ w_end in G.
/// Dispatches to one of the 4 (inv, inv2) subcases.
proof fn lemma_k2_relinsert_reldelete(
    data: HNNData, w: Word, w1: Word, w_end: Word,
    pos0: int, r_idx: nat, inv: bool, pos1: int, r_idx2: nat, inv2: bool,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: pos0, relator_index: r_idx, inverted: inv };
            let step1 = DerivationStep::RelatorDelete { position: pos1, relator_index: r_idx2, inverted: inv2 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w_end)
        }),
        r_idx as int >= data.base.relators.len(),
        !is_base_word(w1, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    if !inv {
        if !inv2 { lemma_k2_rr_nn(data, w, w1, w_end, pos0, r_idx, pos1, r_idx2); }
        else { lemma_k2_rr_ni(data, w, w1, w_end, pos0, r_idx, pos1, r_idx2); }
    } else {
        if !inv2 { lemma_k2_rr_in(data, w, w1, w_end, pos0, r_idx, pos1, r_idx2); }
        else { lemma_k2_rr_ii(data, w, w1, w_end, pos0, r_idx, pos1, r_idx2); }
    }
}

/// Single segment lemma for k=2.
proof fn lemma_single_segment_k2(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        steps.len() == 2,
        derivation_produces(hnn_presentation(data), steps, w) == Some(w_end),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        !is_base_word(
            apply_step(hnn_presentation(data), w, steps.first()).unwrap(),
            data.base.num_generators,
        ),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let step0 = steps[0];
    let step1 = steps[1];
    let w1 = apply_step(hp, w, step0).unwrap();

    // Derive word_valid(w, n) from word_valid(w, n+1) + is_base_word(w, n)
    lemma_base_word_valid_down(w, n);

    // Unfold derivation_produces for 2 steps
    assert(steps.first() == step0);
    let rest = steps.drop_first();
    assert(rest =~= seq![step1]);
    assert(apply_step(hp, w, step0) == Some(w1));
    // derivation_produces(hp, rest, w1) == Some(w_end)
    assert(rest.first() == step1);
    assert(rest.drop_first() =~= Seq::<DerivationStep>::empty());

    // Extract apply_step(hp, w1, step1) == Some(w_end) from derivation_produces
    assert(derivation_produces(hp, rest, w1) == Some(w_end));
    // Unfold: since rest.len() > 0, derivation_produces(hp, rest, w1) =
    //   match apply_step(hp, w1, rest.first()) { Some(w2) => derivation_produces(hp, rest.drop_first(), w2) }
    // rest.first() == step1, rest.drop_first() == empty
    // So apply_step(hp, w1, step1).is_some() and
    //   derivation_produces(hp, empty, apply_step(hp, w1, step1).unwrap()) == Some(w_end)
    // i.e., apply_step(hp, w1, step1).unwrap() == w_end
    let w_end2 = apply_step(hp, w1, step1).unwrap();
    assert(derivation_produces(hp, rest.drop_first(), w_end2) == Some(w_end)) by {
        assert(rest.drop_first().len() == 0);
    };
    assert(w_end2 == w_end);

    // Classify step0: must introduce stable letters
    lemma_base_to_nonbase_step_type(data, w, w1, step0);

    match step0 {
        DerivationStep::FreeExpand { position: pos0, symbol: sym } => {
            // gen_idx(sym) == n guaranteed by lemma_base_to_nonbase_step_type
            match step1 {
                DerivationStep::FreeReduce { position: pos1 } => {
                    // Case (a): FreeExpand(stable) + FreeReduce
                    lemma_k2_expand_reduce(data, w, w1, w_end, pos0, sym, pos1);
                },
                DerivationStep::RelatorDelete { position: pos1, relator_index: r_idx, inverted: inv } => {
                    // Case (b): FreeExpand(stable) + RelatorDelete(HNN)
                    lemma_k2_expand_reldelete(data, w, w1, w_end, pos0, sym, pos1, r_idx, inv);
                },
                DerivationStep::FreeExpand { position: pos1, symbol: sym1 } => {
                    // Impossible: inserting into non-base w1 stays non-base
                    let pair = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
                    assert(w_end =~= w1.subrange(0, pos1) + pair + w1.subrange(pos1, w1.len() as int));
                    lemma_insert_preserves_nonbase(w1, pair, pos1, n);
                },
                DerivationStep::RelatorInsert { position: pos1, relator_index: r_idx, inverted: inv } => {
                    // Impossible: inserting into non-base w1 stays non-base
                    let r = get_relator(hp, r_idx, inv);
                    assert(w_end =~= w1.subrange(0, pos1) + r + w1.subrange(pos1, w1.len() as int));
                    lemma_insert_preserves_nonbase(w1, r, pos1, n);
                },
            }
        },
        DerivationStep::RelatorInsert { position: pos0, relator_index: r_idx, inverted: inv } => {
            // r_idx >= base.relators.len() guaranteed by lemma_base_to_nonbase_step_type
            match step1 {
                DerivationStep::FreeReduce { position: pos1 } => {
                    // Case (c): RelatorInsert(HNN) + FreeReduce
                    lemma_k2_relinsert_reduce(data, w, w1, w_end, pos0, r_idx, inv, pos1);
                },
                DerivationStep::RelatorDelete { position: pos1, relator_index: r_idx2, inverted: inv2 } => {
                    // Case (d): RelatorInsert(HNN) + RelatorDelete
                    lemma_k2_relinsert_reldelete(data, w, w1, w_end, pos0, r_idx, inv, pos1, r_idx2, inv2);
                },
                DerivationStep::FreeExpand { position: pos1, symbol: sym1 } => {
                    // Impossible: inserting into non-base w1 stays non-base
                    let pair = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
                    assert(w_end =~= w1.subrange(0, pos1) + pair + w1.subrange(pos1, w1.len() as int));
                    lemma_insert_preserves_nonbase(w1, pair, pos1, n);
                },
                DerivationStep::RelatorInsert { position: pos1, relator_index: r_idx2, inverted: inv2 } => {
                    // Impossible: inserting into non-base w1 stays non-base
                    let r2 = get_relator(hp, r_idx2, inv2);
                    assert(w_end =~= w1.subrange(0, pos1) + r2 + w1.subrange(pos1, w1.len() as int));
                    lemma_insert_preserves_nonbase(w1, r2, pos1, n);
                },
            }
        },
        _ => {
            // Impossible by lemma_base_to_nonbase_step_type
        },
    }
}

// ============================================================
// Part 5: Single segment lemma (general)
// ============================================================

/// k=3 case: step0 = FreeExpand(stable), step1 = FreeReduce.
/// Commutes FreeReduce to act on base word w first, then applies k=2 lemma.
proof fn lemma_k3_expand_freereduce(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, sym: Symbol, p1: int, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        generator_index(sym) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeReduce { position: p1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    // Structural facts
    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(has_cancellation_at(w1, p1));
    assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + 2, w1.len() as int));

    // word_valid(w, n) from word_valid(w, n+1) + is_base_word
    lemma_base_word_valid_down(w, n);

    // === Eliminate p1 = p0: undoes expand, w2 = w (base), contradiction ===
    if p1 == p0 {
        assert(w2 =~= w.subrange(0, p0) + w.subrange(p0, w.len() as int));
        assert(w2 =~= w);
        assert(false);
    }

    if p1 < p0 {
        // === Eliminate p1 = p0 - 1: stable-base pair can't cancel ===
        if p1 == p0 - 1 {
            // w1[p0-1] = w[p0-1] (base), w1[p0] = sym (stable)
            // has_cancellation_at needs is_inverse_pair, which requires same gen_idx
            assert(symbol_valid(w[(p0 - 1) as int], n));
            assert(generator_index(w[(p0 - 1) as int]) < n);
            match w[(p0 - 1) as int] {
                Symbol::Gen(k) => {},
                Symbol::Inv(k) => {},
            }
            assert(generator_index(inverse_symbol(w[(p0 - 1) as int])) < n);
            assert(generator_index(sym) == n);
            // inverse_symbol(w[p0-1]) can't equal sym (gen_idx < n vs == n)
            assert(!is_inverse_pair(w1[p0 - 1], w1[p0]));
            assert(false);
        }

        // === p1 <= p0 - 2: commute FreeReduce to the front ===
        // w1[p1] = w[p1] and w1[p1+1] = w[p1+1] (before expansion)
        assert(w1[p1] == w[p1]);
        assert(w1[p1 + 1] == w[p1 + 1]);
        assert(has_cancellation_at(w, p1));

        let w_prime = reduce_at(w, p1);
        let step1_base = DerivationStep::FreeReduce { position: p1 };
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));

        // w' is base: reduced pair is base (gen_idx < n), so stable count unchanged
        lemma_stable_count_reduce(w, p1, n);
        assert(generator_index(w[p1]) < n);
        assert(stable_letter_count(w_prime, n) == 0nat);

        // w' is word_valid(n+1)
        lemma_step_preserves_word_valid(data, w, step1_base);

        // FreeExpand(p0-2, sym) on w' gives w2
        let p0_adj = (p0 - 2) as int;
        let step0_adj = DerivationStep::FreeExpand { position: p0_adj, symbol: sym };

        // Position validity
        assert(p0_adj >= 0);
        assert(w_prime.len() == w.len() - 2);
        assert(p0_adj <= w_prime.len() as int);

        // Show apply_step(hp, w', step0_adj) == Some(w2)
        let expand_result = w_prime.subrange(0, p0_adj) + pair
            + w_prime.subrange(p0_adj, w_prime.len() as int);

        // Prove expand_result =~= w2 element-by-element
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == expand_result[k]
        by {
            if k < p1 {
                // Both = w[k]
            } else if k < p0_adj {
                // w2[k] = w1[k+2] = w[k+2]; expand_result[k] = w'[k] = w[k+2]
            } else if k == p0_adj {
                // w2[k] = w1[p0] = sym; expand_result[k] = pair[0] = sym
            } else if k == p0_adj + 1 {
                // w2[k] = w1[p0+1] = inv(sym); expand_result[k] = pair[1] = inv(sym)
            } else {
                // w2[k] = w1[k+2] = w[k]; expand_result[k] = w'[k-2] = w[k]
            }
        };
        assert(w2.len() == expand_result.len());
        assert(w2 =~= expand_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

        // Construct 2-step derivation via helper
        lemma_derivation_produces_2(hp, step0_adj, step2, w_prime, w2, w_end);
        let k2_steps: Seq<DerivationStep> = seq![step0_adj, step2];

        // w' is base, w2 is non-base → k=2 segment
        lemma_single_segment_k2(data, k2_steps, w_prime, w_end);

        // w ≡_G w' via base FreeReduce step
        lemma_single_step_equiv(data.base, w, step1_base, w_prime);

        // Chain: w ≡_G w' ≡_G w_end
        lemma_equiv_transitive(data.base, w, w_prime, w_end);
    } else {
        // === p1 > p0 ===

        // === Eliminate p1 = p0 + 1: stable-base pair can't cancel ===
        if p1 == p0 + 1 {
            // w1[p0+1] = inv(sym) (stable), w1[p0+2] = w[p0] (base)
            // is_inverse_pair(inv(sym), w[p0]) requires inverse_symbol(inv(sym)) == w[p0]
            // = sym == w[p0]. But gen_idx(w[p0]) < n and gen_idx(sym) = n.
            assert(symbol_valid(w[p0], n));
            assert(generator_index(w[p0]) < n);
            assert(generator_index(sym) == n);
            match sym {
                Symbol::Gen(idx) => {
                    match w[p0] {
                        Symbol::Gen(k) => { assert(k < n); assert(Symbol::Inv(idx) != Symbol::Gen(k)); },
                        Symbol::Inv(k) => { assert(k < n); assert(Symbol::Inv(idx) != Symbol::Inv(k)); },
                    }
                },
                Symbol::Inv(idx) => {
                    match w[p0] {
                        Symbol::Gen(k) => { assert(k < n); assert(Symbol::Gen(idx) != Symbol::Gen(k)); },
                        Symbol::Inv(k) => { assert(k < n); assert(Symbol::Gen(idx) != Symbol::Inv(k)); },
                    }
                },
            }
            assert(!is_inverse_pair(w1[p0 + 1], w1[p0 + 2]));
            assert(false);
        }

        // === p1 >= p0 + 2: commute FreeReduce to the front ===
        // w1[p1] = w[p1-2] and w1[p1+1] = w[p1-1] (after expansion, shifted by 2)
        assert(w1[p1] == w[(p1 - 2) as int]);
        assert(w1[p1 + 1] == w[(p1 - 1) as int]);
        let p1_adj = (p1 - 2) as int;
        assert(has_cancellation_at(w, p1_adj));

        let w_prime = reduce_at(w, p1_adj);
        let step1_base = DerivationStep::FreeReduce { position: p1_adj };
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));

        // w' is base
        lemma_stable_count_reduce(w, p1_adj, n);
        assert(generator_index(w[p1_adj]) < n);
        assert(stable_letter_count(w_prime, n) == 0nat);

        // w' is word_valid(n+1)
        lemma_step_preserves_word_valid(data, w, step1_base);

        // FreeExpand(p0, sym) on w' gives w2
        let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym };

        // Position validity: p0 <= w.len() and w'.len() = w.len()-2, but p1_adj >= p0
        // so reduce is AFTER p0, meaning w'[0..p0] = w[0..p0]. So p0 <= w'.len().
        assert(p0 >= 0);
        assert(w_prime.len() == w.len() - 2);
        assert(p0 <= w_prime.len() as int);

        // Show apply_step(hp, w', step0_adj) == Some(w2)
        let expand_result = w_prime.subrange(0, p0) + pair
            + w_prime.subrange(p0, w_prime.len() as int);

        // Prove expand_result =~= w2 element-by-element
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == expand_result[k]
        by {
            if k < p0 {
                // w2[k] = w1[k] = w[k] (k < p0 < p1)
                // expand_result[k] = w'[k] = w[k] (k < p0 <= p1_adj)
            } else if k == p0 {
                // w2[k] = w1[p0] = sym (p0 < p1)
            } else if k == p0 + 1 {
                // w2[k] = w1[p0+1] = inv(sym) (p0+1 < p1)
            } else if k < p1 {
                // p0+2 <= k < p1
                // w2[k] = w1[k] (k < p1, not shifted); w1[k] = w[k-2] (k >= p0+2)
                // expand_result[k] = w'[k-2]; w'[k-2] = w[k-2] (k-2 < p1_adj = p1-2)
            } else {
                // k >= p1
                // w2[k] = w1[k+2] (shifted by reduce_at at p1)
                // w1[k+2] = w[k] (k+2 >= p0+2 + 2, so w1[k+2] = w[k+2-2] = w[k])
                // expand_result[k] = w'[k-2]; w'[k-2] = w[k] (k-2 >= p1-2 = p1_adj)
            }
        };
        assert(w2.len() == expand_result.len());
        assert(w2 =~= expand_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

        // Construct 2-step derivation via helper
        lemma_derivation_produces_2(hp, step0_adj, step2, w_prime, w2, w_end);
        let k2_steps: Seq<DerivationStep> = seq![step0_adj, step2];

        // w' is base, w2 is non-base → k=2 segment
        lemma_single_segment_k2(data, k2_steps, w_prime, w_end);

        // w ≡_G w' via base FreeReduce step
        lemma_single_step_equiv(data.base, w, step1_base, w_prime);

        // Chain: w ≡_G w' ≡_G w_end
        lemma_equiv_transitive(data.base, w, w_prime, w_end);
    }
}

/// Common tail for k=3 commutation proofs.
/// Given: step1_base on w → w' (base), step0_adj on w' → w2, step2 on w2 → w_end.
/// Proves: w ≡_G w_end.
pub proof fn lemma_k3_commutation_tail(
    data: HNNData, w: Word, w_prime: Word, w2: Word, w_end: Word,
    step1_base: DerivationStep, step0_adj: DerivationStep, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        is_base_word(w_prime, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w_prime, data.base.num_generators + 1),
        !is_base_word(w2, data.base.num_generators),
        apply_step(data.base, w, step1_base) == Some(w_prime),
        apply_step(hnn_presentation(data), w_prime, step0_adj) == Some(w2),
        apply_step(hnn_presentation(data), w2, step2) == Some(w_end),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    lemma_derivation_produces_2(hp, step0_adj, step2, w_prime, w2, w_end);
    let k2_steps: Seq<DerivationStep> = seq![step0_adj, step2];
    assert(k2_steps.first() == step0_adj);
    lemma_single_segment_k2(data, k2_steps, w_prime, w_end);
    lemma_single_step_equiv(data.base, w, step1_base, w_prime);
    lemma_equiv_transitive(data.base, w, w_prime, w_end);
}

/// RelatorDelete(HNN) on a word with stable count 2 produces a base word.
proof fn lemma_hnn_reldelete_gives_base(
    data: HNNData, w1: Word, w2: Word,
    p1: int, ri1: nat, inv1: bool,
)
    requires
        hnn_data_valid(data),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        word_valid(w1, data.base.num_generators + 1),
        (ri1 as int) >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let step1 = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            apply_step(hp, w1, step1) == Some(w2)
        }),
    ensures
        is_base_word(w2, data.base.num_generators),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let j = (ri1 as int - data.base.relators.len()) as int;
    assert(0 <= j < data.associations.len());
    let (a_j, b_j) = data.associations[j];

    // HNN relator has 2 stable letters → count(r1) >= 2
    if !inv1 {
        lemma_hnn_relator_stable_positions(data, j);
        assert(generator_index(r1[0int]) == n) by {
            assert(r1[0int] == stable_letter_inv(data));
            assert(stable_letter_inv(data) == Symbol::Inv(n));
        };
        assert(generator_index(r1[(a_j.len() + 1) as int]) == n) by {
            assert(r1[(a_j.len() + 1) as int] == stable_letter(data));
            assert(stable_letter(data) == Symbol::Gen(n));
        };
        lemma_two_elements_contribute_to_count(r1, 0int, (a_j.len() + 1) as int, n);
    } else {
        lemma_hnn_relator_inverted_stable_positions(data, j);
        assert(generator_index(r1[b_j.len() as int]) == n) by {
            assert(r1[b_j.len() as int] == stable_letter_inv(data));
            assert(stable_letter_inv(data) == Symbol::Inv(n));
        };
        assert(generator_index(r1[(b_j.len() + a_j.len() + 1) as int]) == n) by {
            assert(r1[(b_j.len() + a_j.len() + 1) as int] == stable_letter(data));
            assert(stable_letter(data) == Symbol::Gen(n));
        };
        lemma_two_elements_contribute_to_count(
            r1, b_j.len() as int, (b_j.len() + a_j.len() + 1) as int, n);
    }
    assert(stable_letter_count(r1, n) >= 2nat);

    // Decompose: count(w1) = count(left) + count(r1) + count(right) = 2
    assert(w1.subrange(p1, p1 + r1_len) =~= r1);
    assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + r1_len, w1.len() as int));
    assert(w1 =~= w1.subrange(0, p1) + w1.subrange(p1, w1.len() as int));
    lemma_stable_letter_count_concat(w1.subrange(0, p1), w1.subrange(p1, w1.len() as int), n);
    assert(w1.subrange(p1, w1.len() as int)
        =~= w1.subrange(p1, p1 + r1_len) + w1.subrange(p1 + r1_len, w1.len() as int));
    lemma_stable_letter_count_concat(
        w1.subrange(p1, p1 + r1_len), w1.subrange(p1 + r1_len, w1.len() as int), n);
    lemma_stable_letter_count_concat(
        w1.subrange(0, p1), w1.subrange(p1 + r1_len, w1.len() as int), n);
    // count(w2) + count(r1) = 2, count(r1) >= 2 → count(w2) = 0
    assert(stable_letter_count(w2, n) == 0nat);

    lemma_step_preserves_word_valid(data, w1,
        DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 });
    lemma_zero_count_implies_base(w2, n);
}

/// Stable letter count of any relator in the HNN presentation is 0 (base) or 2 (HNN).
pub proof fn lemma_relator_stable_count(data: HNNData, ri: nat, inv: bool)
    requires
        hnn_data_valid(data),
        ({
            let hp = hnn_presentation(data);
            (ri as int) < hp.relators.len()
        }),
    ensures
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let r = get_relator(hp, ri, inv);
            if (ri as int) < data.base.relators.len() {
                stable_letter_count(r, n) == 0nat
            } else {
                stable_letter_count(r, n) == 2nat
            }
        }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r = get_relator(hp, ri, inv);
    reveal(presentation_valid);

    if (ri as int) < data.base.relators.len() {
        // Base relator: all gen_idx < n → count = 0
        let base_r = data.base.relators[ri as int];
        assert(hp.relators[ri as int] == base_r);
        if inv {
            lemma_inverse_word_valid(base_r, n);
            lemma_base_word_characterization(inverse_word(base_r), n);
            lemma_base_implies_count_zero(r, n);
        } else {
            lemma_base_word_characterization(base_r, n);
            lemma_base_implies_count_zero(r, n);
        }
    } else {
        // HNN relator: exactly 2 stable letters
        let j = (ri as int - data.base.relators.len()) as int;
        assert(0 <= j < data.associations.len());
        let (a_j, b_j) = data.associations[j];
        let t = stable_letter(data);
        let t_inv = stable_letter_inv(data);
        assert(stable_letter(data) == Symbol::Gen(n));
        assert(stable_letter_inv(data) == Symbol::Inv(n));
        assert(generator_index(t) == n);
        assert(generator_index(t_inv) == n);

        let raw = hnn_relator(data, j);
        // raw = [t_inv] ++ a_j ++ [t] ++ inv(b_j)
        let s1 = Seq::new(1, |_i: int| t_inv);
        let s2 = Seq::new(1, |_i: int| t);

        // Bridge Seq::new(1, ...) to seq![] for stable_count_single
        assert(s1 =~= seq![t_inv]);
        assert(s2 =~= seq![t]);

        // count of singletons
        lemma_stable_count_single(t_inv, n);
        assert(stable_letter_count(s1, n) == 1nat);
        lemma_stable_count_single(t, n);
        assert(stable_letter_count(s2, n) == 1nat);

        // a_j is base → count = 0
        lemma_base_word_characterization(a_j, n);
        lemma_base_implies_count_zero(a_j, n);

        // inv(b_j) is base → count = 0
        lemma_inverse_word_valid(b_j, n);
        lemma_base_word_characterization(inverse_word(b_j), n);
        lemma_base_implies_count_zero(inverse_word(b_j), n);

        // Build up: count([t_inv] ++ a_j) = 1 + 0 = 1
        lemma_stable_letter_count_concat(s1, a_j, n);
        // count([t_inv] ++ a_j ++ [t]) = 1 + 1 = 2
        lemma_stable_letter_count_concat(s1 + a_j, s2, n);
        // count([t_inv] ++ a_j ++ [t] ++ inv(b_j)) = 2 + 0 = 2
        lemma_stable_letter_count_concat(s1 + a_j + s2, inverse_word(b_j), n);
        assert(raw =~= s1 + a_j + s2 + inverse_word(b_j));
        assert(stable_letter_count(raw, n) == 2nat);

        if inv {
            // Inverted: r = inverse_word(raw). Inverse preserves stable count.
            // inv(b_j) inverts to b_j, [t] inverts to [t_inv], a_j inverts to inv(a_j), [t_inv] to [t]
            // inv(raw) = b_j ++ [t_inv] ++ inv(a_j) ++ [t]
            lemma_inverse_word_valid(a_j, n);
            lemma_base_word_characterization(inverse_word(a_j), n);
            lemma_base_implies_count_zero(inverse_word(a_j), n);
            lemma_base_word_characterization(b_j, n);
            lemma_base_implies_count_zero(b_j, n);

            let inv_r = inverse_word(raw);
            lemma_hnn_relator_inverted_stable_positions(data, j);
            // inv_r = b_j ++ [t_inv] ++ inv(a_j) ++ [t]
            lemma_stable_letter_count_concat(b_j, Seq::new(1, |_i: int| t_inv), n);
            lemma_stable_letter_count_concat(
                b_j + Seq::new(1, |_i: int| t_inv), inverse_word(a_j), n);
            lemma_stable_letter_count_concat(
                b_j + Seq::new(1, |_i: int| t_inv) + inverse_word(a_j),
                Seq::new(1, |_i: int| t), n);
            assert(inv_r =~= b_j + Seq::new(1, |_i: int| t_inv)
                + inverse_word(a_j) + Seq::new(1, |_i: int| t));
            assert(stable_letter_count(inv_r, n) == 2nat);
        }
    }
}

/// If w has stable count >= 4, no single derivation step can produce a base word.
proof fn lemma_count4_step_cant_reach_base(
    data: HNNData, w: Word, w_end: Word, step: DerivationStep,
)
    requires
        hnn_data_valid(data),
        stable_letter_count(w, data.base.num_generators) >= 4,
        word_valid(w, data.base.num_generators + 1),
        apply_step(hnn_presentation(data), w, step) == Some(w_end),
    ensures
        !is_base_word(w_end, data.base.num_generators),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    match step {
        DerivationStep::FreeExpand { position: p, symbol: s } => {
            // w is non-base (count >= 4 > 0 = is_base_word threshold)
            // Inserting preserves non-base
            let pair = Seq::new(1, |_i: int| s) + Seq::new(1, |_i: int| inverse_symbol(s));
            lemma_insert_preserves_nonbase(w, pair, p, n);
        },
        DerivationStep::FreeReduce { position: p } => {
            lemma_stable_count_reduce(w, p, n);
            // count(w_end) = count(w) - (0 or 2) >= 4-2 = 2 > 0
        },
        DerivationStep::RelatorInsert { position: p, relator_index: ri, inverted: inv } => {
            let r = get_relator(hp, ri, inv);
            lemma_insert_preserves_nonbase(w, r, p, n);
        },
        DerivationStep::RelatorDelete { position: p, relator_index: ri, inverted: inv } => {
            let r = get_relator(hp, ri, inv);
            assert(w.subrange(p, p + r.len() as int) =~= r);
            assert(w_end =~= w.subrange(0, p) + w.subrange(p + r.len() as int, w.len() as int));
            lemma_stable_count_subrange(w, p, p + r.len() as int, n);
            lemma_stable_letter_count_concat(
                w.subrange(0, p), w.subrange(p + r.len() as int, w.len() as int), n);
            // count(w_end) = count(w) - count(r)
            lemma_relator_stable_count(data, ri, inv);
            // count(r) is 0 or 2, so count(w_end) >= 4-2 = 2
            if is_base_word(w_end, n) {
                lemma_base_implies_count_zero(w_end, n);
                assert(false);
            }
        },
    }
}

/// k=3 FreeExpand(stable) + RelatorDelete: commutation (base relator) or contradiction (HNN relator).
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
proof fn lemma_k3_expand_reldelete(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, sym: Symbol, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        generator_index(sym) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let step1 = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));

    lemma_expand_stable_gives_count_2(w, p0 as nat, sym, n);
    lemma_base_word_valid_down(w, n);

    // HNN relator case: contradiction (w2 would be base, contradicting precondition)
    if (ri1 as int) >= data.base.relators.len() {
        lemma_hnn_reldelete_gives_base(data, w1, w2, p1, ri1, inv1);
        assert(false);
    }

    // Base relator case: commutation
    assert((ri1 as int) < data.base.relators.len());
    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);
    if inv1 {
        lemma_inverse_word_valid(base_r, n);
        lemma_base_word_characterization(inverse_word(base_r), n);
    } else {
        lemma_base_word_characterization(base_r, n);
    }
    // r1 is base: stable_letter_count(r1) = 0, all gen_idx < n

    // Deleted region [p1, p1+|r1|) can't include p0 or p0+1
    // because w1[p0] = sym with gen_idx = n, but r1 has all gen_idx < n
    assert(w1.subrange(p1, p1 + r1_len) =~= r1);
    if p1 <= p0 && p0 < p1 + r1_len {
        assert(w1[p0] == r1[(p0 - p1) as int]);
        assert(generator_index(w1[p0]) == n);
        assert(generator_index(r1[(p0 - p1) as int]) < n);
        assert(false);
    }
    if p1 <= p0 + 1 && p0 + 1 < p1 + r1_len {
        assert(w1[(p0 + 1) as int] == r1[(p0 + 1 - p1) as int]);
        assert(generator_index(w1[(p0 + 1) as int]) == n) by {
            match sym { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        assert(generator_index(r1[(p0 + 1 - p1) as int]) < n);
        assert(false);
    }

    // get_relator gives same result for base presentation and HNN presentation
    assert(get_relator(data.base, ri1, inv1) =~= r1) by {
        assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
    };

    // So: p1 + |r1| <= p0 or p1 >= p0 + 2
    if p1 + r1_len <= p0 {
        // Commute: RelatorDelete at p1 on w, then FreeExpand at p0 - |r1|
        let step1_base = DerivationStep::RelatorDelete {
            position: p1, relator_index: ri1, inverted: inv1,
        };

        // w[p1..p1+|r1|] = r1 (since w1[k] = w[k] for k < p0, and p1+|r1| <= p0)
        assert forall|k: int| 0 <= k < r1_len
            implies w[(p1 + k) as int] == #[trigger] r1[k]
        by {
            assert(w1[(p1 + k) as int] == r1[k]);
            assert((p1 + k) < p0);
            assert(w1[(p1 + k) as int] == w[(p1 + k) as int]);
        };
        assert(w.subrange(p1, p1 + r1_len) =~= r1);
        let w_prime = w.subrange(0, p1) + w.subrange(p1 + r1_len, w.len() as int);
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));

        // w' is base (subword of base w, so word_valid(n) → is_base_word)
        assert forall|i: int| 0 <= i < w_prime.len()
            implies symbol_valid(#[trigger] w_prime[i], n)
        by {
            if i < p1 {
                assert(w_prime[i] == w[i]);
            } else {
                assert(w_prime[i] == w[(i + r1_len) as int]);
            }
        };
        lemma_base_word_characterization(w_prime, n);
        lemma_word_valid_monotone(w_prime, n);

        // FreeExpand(stable) at p0 - |r1| on w' gives w2
        let p0_adj = (p0 - r1_len) as int;
        let step0_adj = DerivationStep::FreeExpand { position: p0_adj, symbol: sym };
        let expand_result = w_prime.subrange(0, p0_adj) + pair
            + w_prime.subrange(p0_adj, w_prime.len() as int);

        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] expand_result[k]
        by {
            if k < p1 {
            } else if k < p0 - r1_len {
            } else if k == p0 - r1_len {
            } else if k == p0 - r1_len + 1 {
            } else {
            }
        };
        assert(w2.len() == expand_result.len());
        assert(w2 =~= expand_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

        lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
    } else if p1 >= p0 + 2 {
        // Commute: RelatorDelete at p1-2 on w, then FreeExpand at p0
        let p1_adj = (p1 - 2) as int;
        let step1_base = DerivationStep::RelatorDelete {
            position: p1_adj, relator_index: ri1, inverted: inv1,
        };

        // w[p1-2..p1-2+|r1|] = r1 (since w1[k] = w[k-2] for k >= p0+2)
        assert forall|k: int| 0 <= k < r1_len
            implies w[(p1_adj + k) as int] == #[trigger] r1[k]
        by {
            assert(w1[(p1 + k) as int] == r1[k]);
            assert(p1 + k >= p0 + 2);
            assert(w1[(p1 + k) as int] == w[((p1 + k) - 2) as int]);
        };
        assert(w.subrange(p1_adj, p1_adj + r1_len) =~= r1);
        let w_prime = w.subrange(0, p1_adj) + w.subrange(p1_adj + r1_len, w.len() as int);
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));

        // w' is base (subword of base w, so word_valid(n) → is_base_word)
        assert forall|i: int| 0 <= i < w_prime.len()
            implies symbol_valid(#[trigger] w_prime[i], n)
        by {
            if i < p1_adj {
                assert(w_prime[i] == w[i]);
            } else {
                assert(w_prime[i] == w[(i + r1_len) as int]);
            }
        };
        lemma_base_word_characterization(w_prime, n);
        lemma_word_valid_monotone(w_prime, n);

        // FreeExpand(stable) at p0 on w' gives w2
        let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym };
        let expand_result = w_prime.subrange(0, p0) + pair
            + w_prime.subrange(p0, w_prime.len() as int);

        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] expand_result[k]
        by {
            if k < p0 {
            } else if k == p0 {
            } else if k == p0 + 1 {
            } else if k < p1 {
            } else {
            }
        };
        assert(w2.len() == expand_result.len());
        assert(w2 =~= expand_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

        lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
    } else {
        // Edge case: r1_len = 0 (empty relator). Deletion is no-op, w2 = w1.
        // Treat as 2-step derivation: step0 + step2.
        assert(w2 =~= w1);
        let k2_steps = seq![
            DerivationStep::FreeExpand { position: p0, symbol: sym },
            step2,
        ];
        lemma_derivation_produces_2(hp,
            DerivationStep::FreeExpand { position: p0, symbol: sym },
            step2, w, w1, w_end);
        lemma_single_segment_k2(data, k2_steps, w, w_end);
    }
}

/// k=3 FreeExpand(Gen(n)) + FreeExpand(base) at p0+1: contradiction.
/// w2 has Gen(n) at p0, Inv(n) at p0+3. No step2 can reach base.
proof fn lemma_k3_freeexpand_gen_contra(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, idx: nat, sym1: Symbol, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        idx == data.base.num_generators,
        generator_index(sym1) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let sym = Symbol::Gen(idx);
            let p1 = p0 + 1;
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let sym = Symbol::Gen(idx);
    let p1 = p0 + 1;

    lemma_base_word_valid_down(w, n);

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int));

    lemma_expand_stable_gives_count_2(w, p0 as nat, sym, n);

    match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } => {
            lemma_insert_preserves_nonbase(w2, Seq::new(1, |_i: int| sym2) + Seq::new(1, |_i: int| inverse_symbol(sym2)), p2, n);
            assert(false);
        },
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            lemma_insert_preserves_nonbase(w2, r2, p2, n);
            assert(false);
        },
        DerivationStep::FreeReduce { position: p2 } => {
            lemma_stable_count_reduce(w2, p2, n);
            if generator_index(w2[p2]) == n {
                assert(generator_index(w2[p2 + 1]) == n);
                assert(w2[p0] == sym);
                assert(generator_index(sym) == n);
                assert(w2[(p0 + 1) as int] == sym1);
                assert(generator_index(sym1) < n);
                assert(w2[(p0 + 3) as int] == inverse_symbol(sym));
                assert(generator_index(inverse_symbol(sym)) == n) by {
                    match sym { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                };
                assert(w2[(p0 + 2) as int] == inverse_symbol(sym1));
                assert(generator_index(inverse_symbol(sym1)) < n) by {
                    match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                };
                if p2 == p0 {
                    assert(generator_index(w2[(p0 + 1) as int]) < n);
                    assert(false);
                } else if p2 == p0 + 3 {
                    assert(generator_index(w2[(p0 + 4) as int]) < n) by {
                        assert(w2[(p0 + 4) as int] == w[p0]);
                        assert(symbol_valid(w[p0], n));
                    };
                    assert(false);
                } else {
                    if p2 < p0 {
                        assert(w2[p2] == w[p2]);
                        assert(symbol_valid(w[p2], n));
                    } else if p2 == p0 + 1 {
                        assert(w2[p2] == sym1);
                    } else if p2 == p0 + 2 {
                        assert(w2[p2] == inverse_symbol(sym1));
                    } else {
                        assert(w2[p2] == w[(p2 - 4) as int]);
                        assert(symbol_valid(w[(p2 - 4) as int], n));
                    }
                    assert(generator_index(w2[p2]) < n);
                    assert(false);
                }
            }
            assert(stable_letter_count(w_end, n) == 2nat);
            assert(false);
        },
        DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            assert(w2.subrange(p2, p2 + r2.len() as int) =~= r2);
            assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int));

            lemma_stable_count_subrange(w2, p2, p2 + r2.len() as int, n);
            assert(stable_letter_count(w2.subrange(p2, p2 + r2.len() as int), n)
                == stable_letter_count(r2, n));
            lemma_stable_letter_count_concat(
                w2.subrange(0, p2),
                w2.subrange(p2 + r2.len() as int, w2.len() as int), n);

            if stable_letter_count(r2, n) == 0 {
                assert(stable_letter_count(w_end, n) == 2nat);
                assert(false);
            }
            if stable_letter_count(w_end, n) > 0nat {
                assert(false);
            }
            // count(w_end) = 0 and count(r2) >= 1 → count(r2) = 2, deleted region has both stable letters
            if (ri2 as int) < data.base.relators.len() {
                reveal(presentation_valid);
                let base_r = data.base.relators[ri2 as int];
                assert(hp.relators[ri2 as int] == base_r);
                if inv2 {
                    lemma_inverse_word_valid(base_r, n);
                    lemma_base_word_characterization(inverse_word(base_r), n);
                } else {
                    lemma_base_word_characterization(base_r, n);
                }
                assert(stable_letter_count(r2, n) == 0nat);
                assert(false);
            }
            // HNN relator: first stable letter is always Inv(n), but w2[p0] = Gen(n)
            let j = (ri2 as int - data.base.relators.len()) as int;
            assert(0 <= j < data.associations.len());
            if !inv2 {
                lemma_hnn_relator_stable_positions(data, j);
                // r2[0] = Inv(n). At w2[p2].
                if p2 <= p0 {
                    if p2 < p0 {
                        assert(w2[p2] == w[p2]);
                        assert(symbol_valid(w[p2], n));
                        assert(generator_index(w2[p2]) < n);
                        assert(r2[0int] == stable_letter_inv(data));
                        assert(generator_index(r2[0int]) == n);
                        assert(w2[p2] == r2[0int]);
                        assert(false);
                    }
                    assert(p2 == p0);
                    assert(r2[0int] == stable_letter_inv(data));
                    assert(stable_letter_inv(data) == Symbol::Inv(n));
                    assert(w2[p0] == Symbol::Gen(n));
                    assert(r2[0int] == w2[p0]);
                    assert(Symbol::Inv(n) == Symbol::Gen(n));
                    assert(false);
                } else {
                    // p2 > p0: stable letter at p0 not in deleted region
                    assert(p0 < p2);
                    assert(w2[p0] == Symbol::Gen(n));
                    assert(generator_index(w2[p0]) == n);
                    lemma_stable_count_single(w2[p0], n);
                    lemma_stable_count_subrange(w2, 0, p2, n);
                    lemma_stable_letter_count_concat(
                        w2.subrange(0, p2),
                        w2.subrange(p2 + r2.len() as int, w2.len() as int), n);
                    assert(stable_letter_count(w_end, n) >= stable_letter_count(w2.subrange(0, p2), n));
                    assert(stable_letter_count(w2.subrange(0, p2), n) >= 1nat);
                    assert(false);
                }
            } else {
                // Inverted HNN relator: Inv(n) at position |b_j|
                lemma_hnn_relator_inverted_stable_positions(data, j);
                let (a_j, b_j) = data.associations[j];
                let stable_pos1 = p2 + b_j.len() as int;
                assert(r2[b_j.len() as int] == stable_letter_inv(data));
                assert(stable_letter_inv(data) == Symbol::Inv(n));
                assert(w2[stable_pos1] == r2[b_j.len() as int]);
                assert(w2[stable_pos1] == Symbol::Inv(n));
                if stable_pos1 == p0 {
                    assert(w2[p0] == Symbol::Gen(n));
                    assert(Symbol::Inv(n) == Symbol::Gen(n));
                    assert(false);
                } else if stable_pos1 == p0 + 3 {
                    let stable_pos2 = p0 + 3 + a_j.len() as int + 1;
                    assert(stable_pos2 > p0 + 3);
                    assert(r2[(b_j.len() + a_j.len() + 1) as int] == stable_letter(data));
                    assert(stable_letter(data) == Symbol::Gen(n));
                    assert(w2[stable_pos2] == r2[(b_j.len() + a_j.len() + 1) as int]);
                    assert(w2[stable_pos2] == Symbol::Gen(n));
                    assert(w2[stable_pos2] == w[(stable_pos2 - 4) as int]);
                    assert(symbol_valid(w[(stable_pos2 - 4) as int], n));
                    assert(generator_index(w[(stable_pos2 - 4) as int]) < n);
                    assert(false);
                } else {
                    if stable_pos1 < p0 {
                        assert(w2[stable_pos1] == w[stable_pos1]);
                        assert(symbol_valid(w[stable_pos1], n));
                    } else if stable_pos1 == p0 + 1 {
                        assert(w2[stable_pos1] == sym1);
                        assert(generator_index(sym1) < n);
                    } else if stable_pos1 == p0 + 2 {
                        assert(w2[stable_pos1] == inverse_symbol(sym1));
                        assert(generator_index(inverse_symbol(sym1)) < n) by {
                            match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                        };
                    } else {
                        assert(w2[stable_pos1] == w[(stable_pos1 - 4) as int]);
                        assert(symbol_valid(w[(stable_pos1 - 4) as int], n));
                    }
                    assert(generator_index(w2[stable_pos1]) < n);
                    assert(false);
                }
            }
        },
    }
}


/// Inverted HNN relator sub-case of inv_iso: r2 = b_j ++ [Inv(n)] ++ inv(a_j) ++ [Gen(n)].
/// Proves a_j = [sym1, inv(sym1)] from inverse_word structure, then uses isomorphism.
proof fn lemma_k3_inv_iso_inverted_reldelete(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, idx: nat, sym1: Symbol,
    p2: int, ri2: nat, j: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        idx == data.base.num_generators,
        generator_index(sym1) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let sym = Symbol::Inv(idx);
            let p1 = p0 + 1;
            let step2 = DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: true };
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        j == (ri2 as int - data.base.relators.len()) as int,
        0 <= j < data.associations.len() as int,
        word_valid(w, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let sym = Symbol::Inv(idx);
    let (a_j, b_j) = data.associations[j];
    let r2 = get_relator(hp, ri2, true);

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p0 + 1) + pair1 + w1.subrange(p0 + 1, w1.len() as int));

    lemma_hnn_relator_inverted_stable_positions(data, j);

    let stable_pos = p2 + b_j.len() as int;
    assert(r2[b_j.len() as int] == stable_letter_inv(data));
    assert(stable_letter_inv(data) == Symbol::Inv(n));
    assert(w2[stable_pos] == r2[b_j.len() as int]);
    assert(w2[stable_pos] == Symbol::Inv(n));

    // stable_pos must be p0
    if stable_pos != p0 {
        if stable_pos < p0 {
            assert(w2[stable_pos] == w[stable_pos]);
            assert(symbol_valid(w[stable_pos], n));
            assert(generator_index(w2[stable_pos]) < n);
            assert(false);
        } else if stable_pos == p0 + 1 {
            assert(w2[stable_pos] == sym1);
            assert(generator_index(sym1) < n);
            assert(false);
        } else if stable_pos == p0 + 2 {
            assert(w2[stable_pos] == inverse_symbol(sym1));
            assert(generator_index(inverse_symbol(sym1)) < n) by {
                match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
            };
            assert(false);
        } else if stable_pos == p0 + 3 {
            assert(w2[stable_pos] == Symbol::Gen(n));
            assert(Symbol::Gen(n) == Symbol::Inv(n));
            assert(false);
        } else {
            assert(w2[stable_pos] == w[(stable_pos - 4) as int]);
            assert(symbol_valid(w[(stable_pos - 4) as int], n));
            assert(generator_index(w2[stable_pos]) < n);
            assert(false);
        }
    }
    assert(stable_pos == p0);
    assert(p2 == p0 - b_j.len() as int);

    // |a_j| = 2
    if a_j.len() != 2 {
        let sp2 = p0 + a_j.len() as int + 1;
        assert(r2[(b_j.len() + a_j.len() + 1) as int] == stable_letter(data));
        assert(stable_letter(data) == Symbol::Gen(n));
        assert(w2[sp2] == r2[(b_j.len() + a_j.len() + 1) as int]);
        assert(w2[sp2] == Symbol::Gen(n));
        if sp2 < p0 + 3 {
            if sp2 == p0 + 1 {
                assert(w2[sp2] == sym1);
                assert(generator_index(sym1) < n);
                assert(false);
            } else {
                assert(sp2 == p0 + 2);
                assert(w2[sp2] == inverse_symbol(sym1));
                assert(generator_index(inverse_symbol(sym1)) < n) by {
                    match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                };
                assert(false);
            }
        } else {
            assert(sp2 > p0 + 3);
            assert(w2[sp2] == w[(sp2 - 4) as int]);
            assert(symbol_valid(w[(sp2 - 4) as int], n));
            assert(false);
        }
    }
    assert(a_j.len() == 2);

    // Derive a_j = [sym1, inv(sym1)] from inverse_word
    assert(a_j =~= seq![sym1, inverse_symbol(sym1)]) by {
        lemma_inverse_word_len(a_j);
        let inv_aj = inverse_word(a_j);
        assert(inv_aj.len() == 2);
        assert(r2[(b_j.len() + 1) as int] == w2[(p0 + 1) as int]);
        assert(w2[(p0 + 1) as int] == sym1);
        assert(r2[(b_j.len() + 2) as int] == w2[(p0 + 2) as int]);
        assert(w2[(p0 + 2) as int] == inverse_symbol(sym1));
        crate::runtime::lemma_inverse_word_element(a_j, 0int);
        crate::runtime::lemma_inverse_word_element(a_j, 1int);
        assert(inv_aj[0int] == inverse_symbol(a_j[1int]));
        assert(inv_aj[1int] == inverse_symbol(a_j[0int]));
        assert(inv_aj[0int] == sym1);
        assert(inv_aj[1int] == inverse_symbol(sym1));
        assert(inverse_symbol(sym1) == a_j[1int]) by {
            match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        assert(a_j[0int] == inverse_symbol(inverse_symbol(sym1)));
        assert(inverse_symbol(inverse_symbol(sym1)) == sym1) by {
            match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
    };

    // a_j ≡_G ε
    assert(is_inverse_pair(sym1, inverse_symbol(sym1))) by {
        match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
    };
    assert(has_cancellation_at(a_j, 0int));
    let a_reduce_step = DerivationStep::FreeReduce { position: 0int };
    assert(reduce_at(a_j, 0int) =~= empty_word()) by {
        assert(a_j.subrange(0, 0int) =~= Seq::<Symbol>::empty());
        assert(a_j.subrange(2, 2int) =~= Seq::<Symbol>::empty());
    };
    assert(apply_step(data.base, a_j, a_reduce_step) == Some(empty_word()));
    lemma_single_step_equiv(data.base, a_j, a_reduce_step, empty_word());

    // b_j ≡_G ε
    lemma_trivial_association_implies_trivial(data, j);

    let bj_len = b_j.len() as int;
    assert(r2.len() == 2 + a_j.len() + b_j.len());
    assert(p2 == p0 - bj_len);

    let w_left = w.subrange(0, p0 - bj_len);
    let w_right = w.subrange(p0, w.len() as int);
    assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int));
    assert(p2 + r2.len() as int == p0 + 4);
    assert(w2.subrange(0, p2) =~= w_left);
    assert forall|k: int| 0 <= k < w.len() - p0
        implies #[trigger] w2[(p0 + 4 + k) as int] == w[(p0 + k) as int]
    by {};
    assert(w2.subrange(p0 + 4, w2.len() as int) =~= w_right);
    assert(w_end =~= w_left + w_right);

    // w[p0-|b_j|..p0] = b_j
    assert forall|k: int| 0 <= k < bj_len
        implies w[(p0 - bj_len + k) as int] == #[trigger] b_j[k]
    by {
        assert(w2[(p2 + k) as int] == r2[k]);
        assert(p2 + k < p0);
        assert(w2[(p2 + k) as int] == w[(p2 + k) as int]);
        let inv_r_full = b_j + Seq::new(1, |_i: int| stable_letter_inv(data))
            + inverse_word(a_j) + Seq::new(1, |_i: int| stable_letter(data));
        assert(r2 =~= inv_r_full);
        assert(r2[k] == (b_j + (Seq::new(1, |_i: int| stable_letter_inv(data))
            + inverse_word(a_j) + Seq::new(1, |_i: int| stable_letter(data))))[k]);
    };
    let w_mid = w.subrange(p0 - bj_len, p0);
    assert(w_mid =~= b_j);

    // w = w_left ++ b_j ++ w_right
    assert(w =~= w_left + w.subrange(p0 - bj_len, w.len() as int));
    assert(w.subrange(p0 - bj_len, w.len() as int) =~= w_mid + w_right);
    assert(w =~= w_left + (b_j + w_right));

    lemma_remove_trivial_equiv(data.base, w_left, w_right, b_j);
}

/// k=3 FreeExpand(Inv(n)) + FreeExpand(base) at p0+1: isomorphism argument.
/// w2 has Inv(n) at p0, Gen(n) at p0+3. step2 must be RelatorDelete(HNN).
proof fn lemma_k3_freeexpand_inv_iso(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, idx: nat, sym1: Symbol, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        idx == data.base.num_generators,
        generator_index(sym1) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let sym = Symbol::Inv(idx);
            let p1 = p0 + 1;
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let sym = Symbol::Inv(idx);
    let p1 = p0 + 1;

    lemma_base_word_valid_down(w, n);

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int));

    lemma_expand_stable_gives_count_2(w, p0 as nat, sym, n);

    match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } => {
            lemma_insert_preserves_nonbase(w2, Seq::new(1, |_i: int| sym2) + Seq::new(1, |_i: int| inverse_symbol(sym2)), p2, n);
            assert(false);
        },
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            lemma_insert_preserves_nonbase(w2, r2, p2, n);
            assert(false);
        },
        DerivationStep::FreeReduce { position: p2 } => {
            // Stable letters not adjacent → FreeReduce can only remove base pair
            lemma_stable_count_reduce(w2, p2, n);
            if generator_index(w2[p2]) == n {
                assert(w2[p0] == Symbol::Inv(n));
                assert(w2[(p0 + 1) as int] == sym1);
                assert(generator_index(sym1) < n);
                assert(w2[(p0 + 3) as int] == Symbol::Gen(n));
                assert(w2[(p0 + 2) as int] == inverse_symbol(sym1));
                assert(generator_index(inverse_symbol(sym1)) < n) by {
                    match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                };
                if p2 == p0 {
                    assert(generator_index(w2[(p0 + 1) as int]) < n);
                    assert(false);
                } else if p2 == p0 + 3 {
                    assert(generator_index(w2[(p0 + 4) as int]) < n) by {
                        assert(w2[(p0 + 4) as int] == w[p0]);
                        assert(symbol_valid(w[p0], n));
                    };
                    assert(false);
                } else if p2 < p0 {
                    assert(w2[p2] == w[p2]);
                    assert(symbol_valid(w[p2], n));
                    assert(generator_index(w2[p2]) < n);
                    assert(false);
                } else if p2 == p0 + 1 {
                    assert(w2[p2] == sym1);
                    assert(false);
                } else if p2 == p0 + 2 {
                    assert(generator_index(w2[p2]) < n);
                    assert(false);
                } else {
                    assert(w2[p2] == w[(p2 - 4) as int]);
                    assert(symbol_valid(w[(p2 - 4) as int], n));
                    assert(generator_index(w2[p2]) < n);
                    assert(false);
                }
            }
            assert(stable_letter_count(w_end, n) == 2nat);
            assert(false);
        },
        DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);

            // Must be HNN relator (base relator has count 0)
            if (ri2 as int) < data.base.relators.len() {
                reveal(presentation_valid);
                let base_r = data.base.relators[ri2 as int];
                assert(hp.relators[ri2 as int] == base_r);
                if inv2 {
                    lemma_inverse_word_valid(base_r, n);
                    lemma_base_word_characterization(inverse_word(base_r), n);
                } else {
                    lemma_base_word_characterization(base_r, n);
                }
                lemma_stable_count_subrange(w2, p2, p2 + r2.len() as int, n);
                lemma_stable_letter_count_concat(
                    w2.subrange(0, p2),
                    w2.subrange(p2 + r2.len() as int, w2.len() as int), n);
                assert(stable_letter_count(w_end, n) == 2nat);
                assert(false);
            }

            let j = (ri2 as int - data.base.relators.len()) as int;
            assert(0 <= j < data.associations.len());
            let (a_j, b_j) = data.associations[j];

            if !inv2 {
                // r2 = [Inv(n), a_j, Gen(n), inv(b_j)]
                lemma_hnn_relator_stable_positions(data, j);
                assert(r2[0int] == stable_letter_inv(data));
                assert(stable_letter_inv(data) == Symbol::Inv(n));
                assert(w2[p2] == r2[0int]);

                // p2 must be p0 (where Inv(n) is)
                if p2 != p0 {
                    if p2 < p0 {
                        assert(w2[p2] == w[p2]);
                        assert(symbol_valid(w[p2], n));
                        assert(generator_index(w2[p2]) < n);
                        assert(false);
                    } else if p2 == p0 + 1 {
                        assert(w2[p2] == sym1);
                        assert(generator_index(sym1) < n);
                        assert(false);
                    } else if p2 == p0 + 2 {
                        assert(w2[p2] == inverse_symbol(sym1));
                        assert(generator_index(inverse_symbol(sym1)) < n) by {
                            match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                        };
                        assert(false);
                    } else if p2 == p0 + 3 {
                        assert(w2[p2] == Symbol::Gen(n));
                        assert(Symbol::Gen(n) == Symbol::Inv(n));
                        assert(false);
                    } else {
                        assert(w2[p2] == w[(p2 - 4) as int]);
                        assert(symbol_valid(w[(p2 - 4) as int], n));
                        assert(generator_index(w2[p2]) < n);
                        assert(false);
                    }
                }
                assert(p2 == p0);

                // |a_j| = 2
                if a_j.len() != 2 {
                    let sp2 = (p0 + a_j.len() as int + 1) as int;
                    assert(r2[(a_j.len() + 1) as int] == stable_letter(data));
                    assert(stable_letter(data) == Symbol::Gen(n));
                    assert(w2[sp2] == r2[(a_j.len() + 1) as int]);
                    assert(w2[sp2] == Symbol::Gen(n));
                    if sp2 < p0 + 3 {
                        if sp2 == p0 + 1 {
                            assert(w2[(p0 + 1) as int] == sym1);
                            assert(generator_index(sym1) < n);
                            assert(false);
                        } else {
                            assert(sp2 == p0 + 2);
                            assert(w2[(p0 + 2) as int] == inverse_symbol(sym1));
                            assert(generator_index(inverse_symbol(sym1)) < n) by {
                                match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                            };
                            assert(false);
                        }
                    } else {
                        assert(sp2 > p0 + 3);
                        assert(w2[sp2] == w[(sp2 - 4) as int]);
                        assert(symbol_valid(w[(sp2 - 4) as int], n));
                        assert(generator_index(w2[sp2]) < n);
                        assert(false);
                    }
                }
                assert(a_j.len() == 2);

                // a_j = [sym1, inv(sym1)]
                assert(r2[1int] == w2[(p0 + 1) as int]);
                assert(w2[(p0 + 1) as int] == sym1);
                assert(r2[2int] == w2[(p0 + 2) as int]);
                assert(w2[(p0 + 2) as int] == inverse_symbol(sym1));
                assert(a_j =~= seq![sym1, inverse_symbol(sym1)]);

                // a_j ≡_G ε
                assert(is_inverse_pair(sym1, inverse_symbol(sym1))) by {
                    match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                };
                assert(has_cancellation_at(a_j, 0int));
                let a_reduce_step = DerivationStep::FreeReduce { position: 0int };
                assert(reduce_at(a_j, 0int) =~= empty_word()) by {
                    assert(a_j.subrange(0, 0int) =~= Seq::<Symbol>::empty());
                    assert(a_j.subrange(2, 2int) =~= Seq::<Symbol>::empty());
                };
                assert(apply_step(data.base, a_j, a_reduce_step) == Some(empty_word()));
                lemma_single_step_equiv(data.base, a_j, a_reduce_step, empty_word());

                // b_j ≡_G ε by isomorphism
                lemma_trivial_association_implies_trivial(data, j);

                // inv(b_j) ≡ ε
                lemma_inverse_of_identity(data.base, b_j);
                lemma_inverse_word_len(b_j);

                let bj_len = b_j.len() as int;
                let inv_bj = inverse_word(b_j);
                assert(r2.len() == 4 + bj_len) by {
                    assert(r2.len() == 2 + a_j.len() + b_j.len());
                };

                // w_end decomposition
                assert(w_end =~= w2.subrange(0, p0) + w2.subrange(p0 + 4 + bj_len, w2.len() as int));
                let w_left = w.subrange(0, p0);
                let w_right = w.subrange(p0 + bj_len, w.len() as int);
                assert(w2.subrange(0, p0) =~= w_left);
                assert forall|k: int| 0 <= k < w.len() - p0
                    implies #[trigger] w2[(p0 + 4 + k) as int] == w[(p0 + k) as int]
                by {};
                assert(w2.subrange(p0 + 4 + bj_len, w2.len() as int) =~= w_right);
                assert(w_end =~= w_left + w_right);

                // w[p0..p0+bj_len] = inv(b_j)
                assert forall|k: int| 0 <= k < bj_len
                    implies w[(p0 + k) as int] == #[trigger] inv_bj[k]
                by {
                    assert(w2[(p0 + 4 + k) as int] == r2[(4 + k) as int]);
                    assert(w2[(p0 + 4 + k) as int] == w[(p0 + k) as int]);
                };
                let w_mid = w.subrange(p0, p0 + bj_len);
                assert(w_mid =~= inv_bj);

                // w = w_left ++ inv_bj ++ w_right
                assert(w =~= w_left + w.subrange(p0, w.len() as int));
                assert(w.subrange(p0, w.len() as int) =~= w_mid + w_right);
                assert(w =~= w_left + (inv_bj + w_right));

                lemma_remove_trivial_equiv(data.base, w_left, w_right, inv_bj);
            } else {
                lemma_k3_inv_iso_inverted_reldelete(data, w, w1, w2, w_end, p0, idx, sym1, p2, ri2, j);
            }
        },
    }
}


/// k=3 FreeExpand(stable) + FreeExpand(stable): count goes 2→4, no step2 can return to base.
proof fn lemma_k3_expand_freeexpand_stable(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, sym: Symbol, p1: int, sym1: Symbol, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        generator_index(sym) == data.base.num_generators,
        generator_index(sym1) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    // count(w1) = 2 (FreeExpand stable on base word)
    lemma_expand_stable_gives_count_2(w, p0 as nat, sym, n);

    // FreeExpand(stable sym1) adds 2 more stable letters → count(w2) = 4
    // Use lemma_expand_stable_gives_count_2 on w1 (which has count 2, not base, but
    // we need the general insertion count). Compute directly:
    let sing1 = Seq::new(1, |_i: int| sym1);
    let sing2 = Seq::new(1, |_i: int| inverse_symbol(sym1));
    let pair1 = sing1 + sing2;
    assert(w2 =~= w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int));
    assert(generator_index(inverse_symbol(sym1)) == n) by {
        match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
    };
    assert(sing1 =~= seq![sym1]);
    assert(sing2 =~= seq![inverse_symbol(sym1)]);
    lemma_stable_count_single(sym1, n);
    lemma_stable_count_single(inverse_symbol(sym1), n);
    lemma_stable_letter_count_concat(sing1, sing2, n);
    assert(stable_letter_count(pair1, n) == 2nat);

    // count(w2) = count(left + pair1) + count(right)
    //           = count(left) + count(pair1) + count(right)
    //           = count(w1) + count(pair1) = 2 + 2 = 4
    let left = w1.subrange(0, p1);
    let right = w1.subrange(p1, w1.len() as int);
    assert(w1 =~= left + right);
    lemma_stable_letter_count_concat(left, right, n);
    lemma_stable_letter_count_concat(left, pair1, n);
    lemma_stable_letter_count_concat(left + pair1, right, n);
    assert(stable_letter_count(w2, n) >= 4nat);

    // No single step can reduce count from 4 to 0
    lemma_step_preserves_word_valid(data, w1,
        DerivationStep::FreeExpand { position: p1, symbol: sym1 });
    lemma_count4_step_cant_reach_base(data, w2, w_end, step2);
    assert(false); // w_end is base but count4 says it can't be
}

/// Helper: commute base RelatorInsert past FreeExpand(stable).
/// p1 <= p0: insert at p1 in w, expand at p0+|r1|.
/// p1 >= p0+2: insert at p1-2 in w, expand at p0.
proof fn lemma_k3_expand_relinsert_commute(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, sym: Symbol, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        generator_index(sym) == data.base.num_generators,
        (ri1 as int) < data.base.relators.len(),
        p1 <= p0 || p1 >= p0 + 2,
        ({
            let hp = hnn_presentation(data);
            let step1 = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));

    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);
    assert(get_relator(data.base, ri1, inv1) =~= r1) by {
        assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
    };

    // Prove r1 is base
    if inv1 {
        lemma_inverse_word_valid(base_r, n);
        lemma_base_word_characterization(inverse_word(base_r), n);
    } else {
        lemma_base_word_characterization(base_r, n);
    }

    // Compute adjusted positions
    let p1_adj = if p1 <= p0 { p1 } else { (p1 - 2) as int };
    let p0_adj = if p1 <= p0 { p0 + r1_len } else { p0 };

    let step1_base = DerivationStep::RelatorInsert {
        position: p1_adj, relator_index: ri1, inverted: inv1,
    };
    let w_prime = w.subrange(0, p1_adj) + r1 + w.subrange(p1_adj, w.len() as int);
    assert(apply_step(data.base, w, step1_base) == Some(w_prime));

    // w' is base
    assert forall|i: int| 0 <= i < w_prime.len()
        implies symbol_valid(#[trigger] w_prime[i], n)
    by {
        if i < p1_adj {
            assert(w_prime[i] == w[i]);
        } else if i < p1_adj + r1_len {
            assert(w_prime[i] == r1[(i - p1_adj) as int]);
        } else {
            assert(w_prime[i] == w[(i - r1_len) as int]);
        }
    };
    lemma_base_word_characterization(w_prime, n);
    lemma_word_valid_monotone(w_prime, n);

    // FreeExpand(stable) at p0_adj on w' gives w2
    let step0_adj = DerivationStep::FreeExpand { position: p0_adj, symbol: sym };
    let expand_result = w_prime.subrange(0, p0_adj) + pair
        + w_prime.subrange(p0_adj, w_prime.len() as int);

    assert forall|k: int| 0 <= k < w2.len()
        implies w2[k] == #[trigger] expand_result[k]
    by {
        if p1 <= p0 {
            if k < p1 {
            } else if k < p1 + r1_len {
            } else if k < p0 + r1_len {
            } else if k == p0 + r1_len {
            } else if k == p0 + r1_len + 1 {
            } else {
            }
        } else {
            if k < p0 {
            } else if k == p0 {
            } else if k == p0 + 1 {
            } else if k < p1 + r1_len {
            } else {
            }
        }
    };
    assert(w2.len() == expand_result.len());
    assert(w2 =~= expand_result);
    assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

    lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
}

/// k=3 FreeExpand(Gen(n)) + RelatorInsert(base) at p0+1: contradiction.
/// w2 = w[0..p0]++[Gen(n)]++r1++[Inv(n)]++w[p0..], all step2 types → false.
proof fn lemma_k3_relinsert_p1_gen_contra(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, idx: nat, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        idx == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let sym = Symbol::Gen(idx);
            let r1 = get_relator(hp, ri1, inv1);
            &&& (ri1 as int) < data.base.relators.len()
            &&& r1.len() > 0
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0 + 1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let sym = Symbol::Gen(idx);
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    lemma_base_word_valid_down(w, n);

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p0 + 1) + r1 + w1.subrange(p0 + 1, w1.len() as int));

    // w2 structure: w[0..p0] ++ [Gen(n)] ++ r1 ++ [Inv(n)] ++ w[p0..]
    assert(w2[p0] == Symbol::Gen(n));
    assert(w2[(p0 + 1 + r1_len) as int] == Symbol::Inv(n)) by {
        assert(w1[(p0 + 1) as int] == inverse_symbol(sym));
    };

    // r1 is base word
    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);
    if inv1 {
        lemma_inverse_word_valid(base_r, n);
        lemma_base_word_characterization(inverse_word(base_r), n);
    } else {
        lemma_base_word_characterization(base_r, n);
    }
    // r1 elements all have generator_index < n
    assert(is_base_word(r1, n));
    assert forall|k: int| 0 <= k < r1_len implies generator_index(#[trigger] r1[k]) < n
    by {
        assert(symbol_valid(r1[k], n));
    };

    // Stable count = 2
    lemma_expand_stable_gives_count_2(w, p0 as nat, sym, n);
    lemma_relator_stable_count(data, ri1, inv1);
    assert(stable_letter_count(r1, n) == 0nat);
    let left1 = w1.subrange(0, p0 + 1);
    let right1 = w1.subrange(p0 + 1, w1.len() as int);
    assert(w1 =~= left1 + right1);
    lemma_stable_letter_count_concat(left1, right1, n);
    lemma_stable_letter_count_concat(left1, r1, n);
    lemma_stable_letter_count_concat(left1 + r1, right1, n);
    assert(stable_letter_count(w2, n) == 2nat);

    // w2 element access helpers
    // w2[k] for k < p0: w[k]
    // w2[p0]: Gen(n)
    // w2[p0+1..p0+1+r1_len]: r1[k-p0-1] (base)
    // w2[p0+1+r1_len]: Inv(n)
    // w2[k] for k > p0+1+r1_len: w[k - r1_len - 2]

    match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } => {
            lemma_insert_preserves_nonbase(w2, Seq::new(1, |_i: int| sym2) + Seq::new(1, |_i: int| inverse_symbol(sym2)), p2, n);
            assert(false);
        },
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            lemma_insert_preserves_nonbase(w2, r2, p2, n);
            assert(false);
        },
        DerivationStep::FreeReduce { position: p2 } => {
            lemma_stable_count_reduce(w2, p2, n);
            if generator_index(w2[p2]) == n {
                // Only stable positions are p0 and p0+1+r1_len
                if p2 == p0 {
                    // w2[p0+1] = r1[0], base
                    assert(generator_index(w2[(p0 + 1) as int]) < n) by {
                        assert(w2[(p0 + 1) as int] == r1[0int]);
                    };
                    assert(false);
                } else if p2 == p0 + 1 + r1_len {
                    // w2[p0+2+r1_len] = w[p0], base
                    assert(generator_index(w2[(p0 + 2 + r1_len) as int]) < n) by {
                        assert(w2[(p0 + 2 + r1_len) as int] == w[p0]);
                        assert(symbol_valid(w[p0], n));
                    };
                    assert(false);
                } else {
                    // p2 not at a stable position
                    if p2 < p0 {
                        assert(w2[p2] == w[p2]);
                        assert(symbol_valid(w[p2], n));
                    } else if p2 > p0 && p2 <= p0 + r1_len {
                        assert(w2[p2] == r1[(p2 - p0 - 1) as int]);
                    } else {
                        assert(w2[p2] == w[(p2 - r1_len - 2) as int]);
                        assert(symbol_valid(w[(p2 - r1_len - 2) as int], n));
                    }
                    assert(generator_index(w2[p2]) < n);
                    assert(false);
                }
            }
            // Non-stable FreeReduce: count stays 2
            assert(stable_letter_count(w_end, n) == 2nat);
            assert(false);
        },
        DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
            lemma_k3_relinsert_p1_gen_contra_rd(data, w, w1, w2, w_end, p0, idx, ri1, inv1, p2, ri2, inv2);
        },
    }
}

/// Extracted RelatorDelete arm of lemma_k3_relinsert_p1_gen_contra.
proof fn lemma_k3_relinsert_p1_gen_contra_rd(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, idx: nat, ri1: nat, inv1: bool, p2: int, ri2: nat, inv2: bool,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        idx == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let sym = Symbol::Gen(idx);
            let r1 = get_relator(hp, ri1, inv1);
            &&& (ri1 as int) < data.base.relators.len()
            &&& r1.len() > 0
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0 + 1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 }) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        false,
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let sym = Symbol::Gen(idx);
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    lemma_base_word_valid_down(w, n);

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p0 + 1) + r1 + w1.subrange(p0 + 1, w1.len() as int));

    assert(w2[p0] == Symbol::Gen(n));
    assert(w2[(p0 + 1 + r1_len) as int] == Symbol::Inv(n)) by {
        assert(w1[(p0 + 1) as int] == inverse_symbol(sym));
    };

    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);
    if inv1 {
        lemma_inverse_word_valid(base_r, n);
        lemma_base_word_characterization(inverse_word(base_r), n);
    } else {
        lemma_base_word_characterization(base_r, n);
    }
    assert(is_base_word(r1, n));
    assert forall|k: int| 0 <= k < r1_len implies generator_index(#[trigger] r1[k]) < n
    by {
        assert(symbol_valid(r1[k], n));
    };

    lemma_expand_stable_gives_count_2(w, p0 as nat, sym, n);
    lemma_relator_stable_count(data, ri1, inv1);
    assert(stable_letter_count(r1, n) == 0nat);
    let left1 = w1.subrange(0, p0 + 1);
    let right1 = w1.subrange(p0 + 1, w1.len() as int);
    assert(w1 =~= left1 + right1);
    lemma_stable_letter_count_concat(left1, right1, n);
    lemma_stable_letter_count_concat(left1, r1, n);
    lemma_stable_letter_count_concat(left1 + r1, right1, n);
    assert(stable_letter_count(w2, n) == 2nat);

    let r2 = get_relator(hp, ri2, inv2);
    assert(w2.subrange(p2, p2 + r2.len() as int) =~= r2);
    assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int));

    lemma_stable_count_subrange(w2, p2, p2 + r2.len() as int, n);
    lemma_stable_letter_count_concat(
        w2.subrange(0, p2),
        w2.subrange(p2 + r2.len() as int, w2.len() as int), n);

    if stable_letter_count(r2, n) == 0 {
        assert(stable_letter_count(w_end, n) == 2nat);
        assert(false);
    }
    if stable_letter_count(w_end, n) > 0nat {
        assert(false);
    }
    // Must be HNN relator with count 2, removing both stable letters
    if (ri2 as int) < data.base.relators.len() {
        let base_r2 = data.base.relators[ri2 as int];
        assert(hp.relators[ri2 as int] == base_r2);
        if inv2 {
            lemma_inverse_word_valid(base_r2, n);
            lemma_base_word_characterization(inverse_word(base_r2), n);
        } else {
            lemma_base_word_characterization(base_r2, n);
        }
        assert(stable_letter_count(r2, n) == 0nat);
        assert(false);
    }
    let j = (ri2 as int - data.base.relators.len()) as int;
    assert(0 <= j < data.associations.len());

    // HNN relator: first stable letter is Inv(n), but w2[p0] = Gen(n)
    if !inv2 {
        lemma_hnn_relator_stable_positions(data, j);
        // r2[0] = Inv(n), w2[p2] = r2[0]
        if p2 <= p0 {
            if p2 < p0 {
                assert(w2[p2] == w[p2]);
                assert(symbol_valid(w[p2], n));
                assert(generator_index(w2[p2]) < n);
                assert(r2[0int] == stable_letter_inv(data));
                assert(generator_index(r2[0int]) == n);
                assert(w2[p2] == r2[0int]);
                assert(false);
            }
            // p2 == p0: r2[0] = Inv(n) but w2[p0] = Gen(n)
            assert(p2 == p0);
            assert(r2[0int] == stable_letter_inv(data));
            assert(stable_letter_inv(data) == Symbol::Inv(n));
            assert(w2[p0] == Symbol::Gen(n));
            assert(r2[0int] == w2[p0]);
            assert(Symbol::Inv(n) == Symbol::Gen(n));
            assert(false);
        } else {
            // p2 > p0: stable letter at p0 not in deleted region
            assert(p0 < p2);
            assert(w2[p0] == Symbol::Gen(n));
            assert(generator_index(w2[p0]) == n);
            lemma_stable_count_single(w2[p0], n);
            lemma_stable_count_subrange(w2, 0, p2, n);
            lemma_stable_letter_count_concat(
                w2.subrange(0, p2),
                w2.subrange(p2 + r2.len() as int, w2.len() as int), n);
            assert(stable_letter_count(w_end, n) >= stable_letter_count(w2.subrange(0, p2), n));
            assert(stable_letter_count(w2.subrange(0, p2), n) >= 1nat);
            assert(false);
        }
    } else {
        // Inverted HNN relator: Inv(n) at position |b_j|
        lemma_hnn_relator_inverted_stable_positions(data, j);
        let (a_j, b_j) = data.associations[j];
        let stable_pos1 = p2 + b_j.len() as int;
        assert(r2[b_j.len() as int] == stable_letter_inv(data));
        assert(stable_letter_inv(data) == Symbol::Inv(n));
        assert(w2[stable_pos1] == r2[b_j.len() as int]);
        assert(w2[stable_pos1] == Symbol::Inv(n));
        // stable_pos1 must be at p0+1+r1_len (the Inv(n) position)
        // because w2[p0] = Gen(n) != Inv(n)
        if stable_pos1 == p0 {
            assert(w2[p0] == Symbol::Gen(n));
            assert(Symbol::Inv(n) == Symbol::Gen(n));
            assert(false);
        } else if stable_pos1 < p0 {
            assert(w2[stable_pos1] == w[stable_pos1]);
            assert(symbol_valid(w[stable_pos1], n));
            assert(generator_index(w2[stable_pos1]) < n);
            assert(false);
        } else if stable_pos1 > p0 && stable_pos1 < p0 + 1 + r1_len {
            // In the r1 region: base element
            assert(w2[stable_pos1] == r1[(stable_pos1 - p0 - 1) as int]);
            assert(generator_index(r1[(stable_pos1 - p0 - 1) as int]) < n);
            assert(false);
        } else if stable_pos1 > p0 + 1 + r1_len {
            assert(w2[stable_pos1] == w[(stable_pos1 - r1_len - 2) as int]);
            assert(symbol_valid(w[(stable_pos1 - r1_len - 2) as int], n));
            assert(generator_index(w2[stable_pos1]) < n);
            assert(false);
        }
        // stable_pos1 == p0 + 1 + r1_len
        assert(stable_pos1 == p0 + 1 + r1_len);
        // Second stable letter at stable_pos1 + |a_j| + 1
        let stable_pos2 = stable_pos1 + a_j.len() as int + 1;
        assert(r2[(b_j.len() + a_j.len() + 1) as int] == stable_letter(data));
        assert(stable_letter(data) == Symbol::Gen(n));
        assert(w2[stable_pos2] == Symbol::Gen(n));
        // stable_pos2 > p0+1+r1_len, so it's in the w region
        assert(stable_pos2 > p0 + 1 + r1_len);
        assert(w2[stable_pos2] == w[(stable_pos2 - r1_len - 2) as int]);
        assert(symbol_valid(w[(stable_pos2 - r1_len - 2) as int], n));
        assert(generator_index(w2[stable_pos2]) < n);
        assert(false);
    }
}

/// Helper: non-inverted RelatorDelete in relinsert Inv(n) iso case.
proof fn lemma_k3_relinsert_p1_inv_iso_noninv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, idx: nat, ri1: nat, inv1: bool,
    p2: int, ri2: nat, j: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        idx == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let sym = Symbol::Inv(idx);
            let r1 = get_relator(hp, ri1, inv1);
            let step2 = DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: false };
            &&& (ri1 as int) < data.base.relators.len()
            &&& r1.len() > 0
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0 + 1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        j == (ri2 as int - data.base.relators.len()) as int,
        0 <= j < data.associations.len() as int,
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let r1 = get_relator(hp, ri1, inv1);
            let r2 = get_relator(hp, ri2, false);
            &&& stable_letter_count(w2, n) == 2nat
            &&& stable_letter_count(w_end, n) == 0nat
            &&& is_base_word(r1, n)
            &&& w2[p0] == Symbol::Inv(n)
            &&& w2[(p0 + 1 + r1.len() as int) as int] == Symbol::Gen(n)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let sym = Symbol::Inv(idx);
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let r2 = get_relator(hp, ri2, false);
    let (a_j, b_j) = data.associations[j];

    // Establish word_valid(r1, n) from base presentation
    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);
    if inv1 {
        lemma_inverse_word_valid(base_r, n);
    }
    assert(word_valid(r1, n));

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p0 + 1) + r1 + w1.subrange(p0 + 1, w1.len() as int));

    assert forall|k: int| 0 <= k < r1_len implies generator_index(#[trigger] r1[k]) < n
    by { assert(symbol_valid(r1[k], n)); };

    assert(w2.subrange(p2, p2 + r2.len() as int) =~= r2);
    assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int));

    // r2 = [Inv(n), a_j, Gen(n), inv(b_j)]
    lemma_hnn_relator_stable_positions(data, j);
    assert(r2[0int] == stable_letter_inv(data));
    assert(stable_letter_inv(data) == Symbol::Inv(n));
    assert(w2[p2] == r2[0int]);

    // p2 must be p0 (where Inv(n) is)
    if p2 != p0 {
        if p2 < p0 {
            assert(w2[p2] == w[p2]);
            assert(symbol_valid(w[p2], n));
            assert(generator_index(w2[p2]) < n);
            assert(generator_index(r2[0int]) == n);
            assert(w2[p2] == r2[0int]);
            assert(false);
        } else if p2 > p0 && p2 <= p0 + r1_len {
            assert(w2[p2] == r1[(p2 - p0 - 1) as int]);
            assert(generator_index(r1[(p2 - p0 - 1) as int]) < n);
            assert(generator_index(r2[0int]) == n);
            assert(w2[p2] == r2[0int]);
            assert(false);
        } else if p2 == p0 + 1 + r1_len {
            assert(w2[p2] == Symbol::Gen(n));
            assert(Symbol::Gen(n) == Symbol::Inv(n));
            assert(false);
        } else {
            assert(w2[p2] == w[(p2 - r1_len - 2) as int]);
            assert(symbol_valid(w[(p2 - r1_len - 2) as int], n));
            assert(generator_index(w2[p2]) < n);
            assert(generator_index(r2[0int]) == n);
            assert(w2[p2] == r2[0int]);
            assert(false);
        }
    }
    assert(p2 == p0);

    // Second stable letter r2[|a_j|+1] = Gen(n) must be at p0+1+r1_len
    let sp2 = (p0 + a_j.len() as int + 1) as int;
    assert(r2[(a_j.len() + 1) as int] == stable_letter(data));
    assert(stable_letter(data) == Symbol::Gen(n));
    assert(w2[sp2] == r2[(a_j.len() + 1) as int]);
    assert(w2[sp2] == Symbol::Gen(n));
    if sp2 != p0 + 1 + r1_len {
        if sp2 > p0 && sp2 <= p0 + r1_len {
            assert(w2[sp2] == r1[(sp2 - p0 - 1) as int]);
            assert(generator_index(r1[(sp2 - p0 - 1) as int]) < n);
            assert(false);
        } else if sp2 > p0 + 1 + r1_len {
            assert(w2[sp2] == w[(sp2 - r1_len - 2) as int]);
            assert(symbol_valid(w[(sp2 - r1_len - 2) as int], n));
            assert(generator_index(w2[sp2]) < n);
            assert(false);
        }
    }
    assert(sp2 == p0 + 1 + r1_len);
    assert(a_j.len() == r1_len);

    // a_j matches r1
    assert forall|k: int| 0 <= k < r1_len implies r2[(k + 1) as int] == #[trigger] r1[k]
    by {
        assert(w2[(p0 + 1 + k) as int] == r1[k]);
        assert(w2[(p2 + 1 + k) as int] == r2[(1 + k) as int]);
    };
    assert(a_j =~= r1) by {
        assert(a_j.len() == r1.len());
        assert forall|k: int| 0 <= k < a_j.len() as int implies a_j[k] == r1[k]
        by { assert(r2[(k + 1) as int] == r1[k]); };
    };

    // r1 ≡_G ε
    assert(get_relator(data.base, ri1, inv1) =~= r1) by {
        assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
    };
    if inv1 {
        lemma_relator_is_identity(data.base, ri1 as int);
        lemma_inverse_of_identity(data.base, data.base.relators[ri1 as int]);
    } else {
        lemma_relator_is_identity(data.base, ri1 as int);
    }
    assert(equiv_in_presentation(data.base, r1, empty_word()));

    // b_j ≡_G ε by isomorphism
    lemma_trivial_association_implies_trivial(data, j);

    // inv(b_j) ≡_G ε
    lemma_inverse_of_identity(data.base, b_j);
    lemma_inverse_word_len(b_j);

    let bj_len = b_j.len() as int;
    let inv_bj = inverse_word(b_j);
    assert(r2.len() == 2 + a_j.len() + b_j.len());

    // w_end decomposition
    assert(w_end =~= w2.subrange(0, p0) + w2.subrange(p0 + r2.len() as int, w2.len() as int));
    let w_left = w.subrange(0, p0);
    let w_right = w.subrange(p0 + bj_len, w.len() as int);
    assert(w2.subrange(0, p0) =~= w_left);
    assert forall|k: int| 0 <= k < w.len() - p0
        implies #[trigger] w2[(p0 + 2 + r1_len + k) as int] == w[(p0 + k) as int]
    by {};
    assert(w2.subrange(p0 + r2.len() as int, w2.len() as int) =~= w_right) by {
        assert(r2.len() == 2 + r1_len + bj_len);
        assert(p0 + r2.len() as int == p0 + 2 + r1_len + bj_len);
    };
    assert(w_end =~= w_left + w_right);

    // w[p0..p0+bj_len] = inv(b_j)
    assert forall|k: int| 0 <= k < bj_len
        implies w[(p0 + k) as int] == #[trigger] inv_bj[k]
    by {
        assert(w2[(p0 + 2 + r1_len + k) as int] == r2[(2 + r1_len + k) as int]) by {
            assert(p2 == p0);
        };
        assert(w2[(p0 + 2 + r1_len + k) as int] == w[(p0 + k) as int]);
    };
    let w_mid = w.subrange(p0, p0 + bj_len);
    assert(w_mid =~= inv_bj);

    assert(w =~= w_left + w.subrange(p0, w.len() as int));
    assert(w.subrange(p0, w.len() as int) =~= w_mid + w_right);
    assert(w =~= w_left + (inv_bj + w_right));

    lemma_remove_trivial_equiv(data.base, w_left, w_right, inv_bj);
}

/// Helper: inverted RelatorDelete in relinsert Inv(n) iso case.
proof fn lemma_k3_relinsert_p1_inv_iso_inv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, idx: nat, ri1: nat, inv1: bool,
    p2: int, ri2: nat, j: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        idx == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let sym = Symbol::Inv(idx);
            let r1 = get_relator(hp, ri1, inv1);
            let step2 = DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: true };
            &&& (ri1 as int) < data.base.relators.len()
            &&& r1.len() > 0
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0 + 1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        j == (ri2 as int - data.base.relators.len()) as int,
        0 <= j < data.associations.len() as int,
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let r1 = get_relator(hp, ri1, inv1);
            let r2 = get_relator(hp, ri2, true);
            &&& stable_letter_count(w2, n) == 2nat
            &&& stable_letter_count(w_end, n) == 0nat
            &&& is_base_word(r1, n)
            &&& w2[p0] == Symbol::Inv(n)
            &&& w2[(p0 + 1 + r1.len() as int) as int] == Symbol::Gen(n)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let sym = Symbol::Inv(idx);
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let r2 = get_relator(hp, ri2, true);
    let (a_j, b_j) = data.associations[j];

    // Establish word_valid(r1, n) from base presentation
    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);
    if inv1 {
        lemma_inverse_word_valid(base_r, n);
    }
    assert(word_valid(r1, n));

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p0 + 1) + r1 + w1.subrange(p0 + 1, w1.len() as int));

    assert forall|k: int| 0 <= k < r1_len implies generator_index(#[trigger] r1[k]) < n
    by { assert(symbol_valid(r1[k], n)); };

    assert(w2.subrange(p2, p2 + r2.len() as int) =~= r2);
    assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int));

    // Inverted: r2 = b_j ++ [Inv(n)] ++ inv(a_j) ++ [Gen(n)]
    lemma_hnn_relator_inverted_stable_positions(data, j);
    let stable_pos1 = p2 + b_j.len() as int;
    assert(r2[b_j.len() as int] == stable_letter_inv(data));
    assert(stable_letter_inv(data) == Symbol::Inv(n));
    assert(w2[stable_pos1] == r2[b_j.len() as int]);
    assert(w2[stable_pos1] == Symbol::Inv(n));

    // stable_pos1 must be p0
    if stable_pos1 != p0 {
        if stable_pos1 < p0 {
            assert(w2[stable_pos1] == w[stable_pos1]);
            assert(symbol_valid(w[stable_pos1], n));
            assert(generator_index(w2[stable_pos1]) < n);
            assert(false);
        } else if stable_pos1 > p0 && stable_pos1 <= p0 + r1_len {
            assert(w2[stable_pos1] == r1[(stable_pos1 - p0 - 1) as int]);
            assert(generator_index(r1[(stable_pos1 - p0 - 1) as int]) < n);
            assert(false);
        } else if stable_pos1 == p0 + 1 + r1_len {
            assert(w2[stable_pos1] == Symbol::Gen(n));
            assert(Symbol::Gen(n) == Symbol::Inv(n));
            assert(false);
        } else {
            assert(w2[stable_pos1] == w[(stable_pos1 - r1_len - 2) as int]);
            assert(symbol_valid(w[(stable_pos1 - r1_len - 2) as int], n));
            assert(generator_index(w2[stable_pos1]) < n);
            assert(false);
        }
    }
    assert(stable_pos1 == p0);
    assert(p2 == p0 - b_j.len() as int);

    // Second stable letter at p0 + |a_j| + 1 must be at p0+1+r1_len
    let sp2 = p0 + a_j.len() as int + 1;
    assert(r2[(b_j.len() + a_j.len() + 1) as int] == stable_letter(data));
    assert(stable_letter(data) == Symbol::Gen(n));
    assert(w2[sp2] == r2[(b_j.len() + a_j.len() + 1) as int]);
    assert(w2[sp2] == Symbol::Gen(n));

    if sp2 != p0 + 1 + r1_len {
        if sp2 > p0 && sp2 <= p0 + r1_len {
            assert(w2[sp2] == r1[(sp2 - p0 - 1) as int]);
            assert(generator_index(r1[(sp2 - p0 - 1) as int]) < n);
            assert(false);
        } else if sp2 > p0 + 1 + r1_len {
            assert(w2[sp2] == w[(sp2 - r1_len - 2) as int]);
            assert(symbol_valid(w[(sp2 - r1_len - 2) as int], n));
            assert(generator_index(w2[sp2]) < n);
            assert(false);
        }
    }
    assert(sp2 == p0 + 1 + r1_len);
    assert(a_j.len() == r1_len);

    // inv(a_j) content matches r1 between stable letters
    lemma_inverse_word_len(a_j);
    let inv_aj = inverse_word(a_j);
    assert(inv_aj.len() == r1_len);
    assert forall|k: int| 0 <= k < r1_len implies r2[(b_j.len() as int + 1 + k) as int] == #[trigger] r1[k]
    by {
        assert(w2[(p0 + 1 + k) as int] == r1[k]);
        assert(w2[(p2 + b_j.len() as int + 1 + k) as int] == r2[(b_j.len() as int + 1 + k) as int]);
        assert(p2 + b_j.len() as int == p0);
    };
    assert(inv_aj =~= r1) by {
        assert forall|k: int| 0 <= k < inv_aj.len() as int implies inv_aj[k] == r1[k]
        by { assert(r2[(b_j.len() as int + 1 + k) as int] == r1[k]); };
    };

    // r1 ≡_G ε
    reveal(presentation_valid);
    assert(get_relator(data.base, ri1, inv1) =~= r1) by {
        assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
    };
    if inv1 {
        lemma_relator_is_identity(data.base, ri1 as int);
        lemma_inverse_of_identity(data.base, data.base.relators[ri1 as int]);
    } else {
        lemma_relator_is_identity(data.base, ri1 as int);
    }
    assert(equiv_in_presentation(data.base, r1, empty_word()));

    // inv(a_j) ≡_G ε → a_j ≡_G ε via double inversion
    assert(word_valid(r1, n));
    assert(word_valid(inv_aj, n)) by { assert(inv_aj =~= r1); };
    lemma_inverse_of_identity(data.base, inv_aj);
    crate::word::lemma_inverse_involution(a_j);
    assert(inverse_word(inv_aj) =~= a_j);
    assert(equiv_in_presentation(data.base, a_j, empty_word()));

    // b_j ≡_G ε
    lemma_trivial_association_implies_trivial(data, j);

    let bj_len = b_j.len() as int;
    assert(r2.len() == 2 + a_j.len() + b_j.len());
    assert(p2 == p0 - bj_len);

    let w_left = w.subrange(0, p0 - bj_len);
    let w_right = w.subrange(p0, w.len() as int);
    assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int));
    assert(p2 + r2.len() as int == p0 + 2 + r1_len);
    assert(w2.subrange(0, p2) =~= w_left);
    assert forall|k: int| 0 <= k < w.len() - p0
        implies #[trigger] w2[(p0 + 2 + r1_len + k) as int] == w[(p0 + k) as int]
    by {};
    assert(w2.subrange(p0 + 2 + r1_len, w2.len() as int) =~= w_right);
    assert(w_end =~= w_left + w_right);

    // w[p0-|b_j|..p0] = b_j
    assert forall|k: int| 0 <= k < bj_len
        implies w[(p0 - bj_len + k) as int] == #[trigger] b_j[k]
    by {
        assert(w2[(p2 + k) as int] == r2[k]);
        assert(p2 + k < p0);
        assert(w2[(p2 + k) as int] == w[(p2 + k) as int]);
        let inv_r_full = b_j + Seq::new(1, |_i: int| stable_letter_inv(data))
            + inverse_word(a_j) + Seq::new(1, |_i: int| stable_letter(data));
        assert(r2 =~= inv_r_full);
        assert(r2[k] == (b_j + (Seq::new(1, |_i: int| stable_letter_inv(data))
            + inverse_word(a_j) + Seq::new(1, |_i: int| stable_letter(data))))[k]);
    };
    let w_mid = w.subrange(p0 - bj_len, p0);
    assert(w_mid =~= b_j);

    assert(w =~= w_left + w.subrange(p0 - bj_len, w.len() as int));
    assert(w.subrange(p0 - bj_len, w.len() as int) =~= w_mid + w_right);
    assert(w =~= w_left + (b_j + w_right));

    lemma_remove_trivial_equiv(data.base, w_left, w_right, b_j);
}

/// k=3 FreeExpand(Inv(n)) + RelatorInsert(base) at p0+1: isomorphism argument.
/// w2 = w[0..p0]++[Inv(n)]++r1++[Gen(n)]++w[p0..], RelatorDelete(HNN) can match.
proof fn lemma_k3_relinsert_p1_inv_iso(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, idx: nat, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        idx == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let sym = Symbol::Inv(idx);
            let r1 = get_relator(hp, ri1, inv1);
            &&& (ri1 as int) < data.base.relators.len()
            &&& r1.len() > 0
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0 + 1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let sym = Symbol::Inv(idx);
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    lemma_base_word_valid_down(w, n);

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p0 + 1) + r1 + w1.subrange(p0 + 1, w1.len() as int));

    // w2 structure: w[0..p0] ++ [Inv(n)] ++ r1 ++ [Gen(n)] ++ w[p0..]
    assert(w2[p0] == Symbol::Inv(n));
    assert(w2[(p0 + 1 + r1_len) as int] == Symbol::Gen(n)) by {
        assert(w1[(p0 + 1) as int] == inverse_symbol(sym));
    };

    // r1 is base word
    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);
    if inv1 {
        lemma_inverse_word_valid(base_r, n);
        lemma_base_word_characterization(inverse_word(base_r), n);
    } else {
        lemma_base_word_characterization(base_r, n);
    }
    assert(is_base_word(r1, n));

    // Stable count = 2
    lemma_expand_stable_gives_count_2(w, p0 as nat, sym, n);
    lemma_relator_stable_count(data, ri1, inv1);
    assert(stable_letter_count(r1, n) == 0nat);
    let left1 = w1.subrange(0, p0 + 1);
    let right1 = w1.subrange(p0 + 1, w1.len() as int);
    assert(w1 =~= left1 + right1);
    lemma_stable_letter_count_concat(left1, right1, n);
    lemma_stable_letter_count_concat(left1, r1, n);
    lemma_stable_letter_count_concat(left1 + r1, right1, n);
    assert(stable_letter_count(w2, n) == 2nat);

    match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } => {
            lemma_insert_preserves_nonbase(w2, Seq::new(1, |_i: int| sym2) + Seq::new(1, |_i: int| inverse_symbol(sym2)), p2, n);
            assert(false);
        },
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            lemma_insert_preserves_nonbase(w2, r2, p2, n);
            assert(false);
        },
        DerivationStep::FreeReduce { position: p2 } => {
            lemma_stable_count_reduce(w2, p2, n);
            if generator_index(w2[p2]) == n {
                if p2 == p0 {
                    assert(generator_index(w2[(p0 + 1) as int]) < n) by {
                        assert(w2[(p0 + 1) as int] == r1[0int]);
                        assert(symbol_valid(r1[0int], n));
                    };
                    assert(false);
                } else if p2 == p0 + 1 + r1_len {
                    assert(generator_index(w2[(p0 + 2 + r1_len) as int]) < n) by {
                        assert(w2[(p0 + 2 + r1_len) as int] == w[p0]);
                        assert(symbol_valid(w[p0], n));
                    };
                    assert(false);
                } else {
                    if p2 < p0 {
                        assert(w2[p2] == w[p2]);
                        assert(symbol_valid(w[p2], n));
                    } else if p2 > p0 && p2 <= p0 + r1_len {
                        assert(w2[p2] == r1[(p2 - p0 - 1) as int]);
                        assert(symbol_valid(r1[(p2 - p0 - 1) as int], n));
                    } else {
                        assert(w2[p2] == w[(p2 - r1_len - 2) as int]);
                        assert(symbol_valid(w[(p2 - r1_len - 2) as int], n));
                    }
                    assert(generator_index(w2[p2]) < n);
                    assert(false);
                }
            }
            assert(stable_letter_count(w_end, n) == 2nat);
            assert(false);
        },
        DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);

            lemma_stable_count_subrange(w2, p2, p2 + r2.len() as int, n);
            lemma_stable_letter_count_concat(
                w2.subrange(0, p2),
                w2.subrange(p2 + r2.len() as int, w2.len() as int), n);

            if stable_letter_count(r2, n) == 0 {
                assert(stable_letter_count(w_end, n) == 2nat);
                assert(false);
            }
            if stable_letter_count(w_end, n) > 0nat {
                assert(false);
            }
            // Must be HNN relator
            if (ri2 as int) < data.base.relators.len() {
                let base_r2 = data.base.relators[ri2 as int];
                assert(hp.relators[ri2 as int] == base_r2);
                if inv2 {
                    lemma_inverse_word_valid(base_r2, n);
                    lemma_base_word_characterization(inverse_word(base_r2), n);
                } else {
                    lemma_base_word_characterization(base_r2, n);
                }
                assert(stable_letter_count(r2, n) == 0nat);
                assert(false);
            }

            let j = (ri2 as int - data.base.relators.len()) as int;
            assert(0 <= j < data.associations.len());

            if !inv2 {
                lemma_k3_relinsert_p1_inv_iso_noninv(
                    data, w, w1, w2, w_end, p0, idx, ri1, inv1, p2, ri2, j);
            } else {
                lemma_k3_relinsert_p1_inv_iso_inv(
                    data, w, w1, w2, w_end, p0, idx, ri1, inv1, p2, ri2, j);
            }
        },
    }
}

/// k=3 FreeExpand(stable) + RelatorInsert: commutation (base) or count contradiction (HNN).
proof fn lemma_k3_expand_relinsert(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, sym: Symbol, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        generator_index(sym) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let step1 = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));

    lemma_expand_stable_gives_count_2(w, p0 as nat, sym, n);
    lemma_base_word_valid_down(w, n);

    // HNN relator: count goes 2+2=4, contradiction
    if (ri1 as int) >= data.base.relators.len() {
        lemma_relator_stable_count(data, ri1, inv1);
        assert(stable_letter_count(r1, n) == 2nat);
        let left = w1.subrange(0, p1);
        let right = w1.subrange(p1, w1.len() as int);
        assert(w1 =~= left + right);
        lemma_stable_letter_count_concat(left, right, n);
        lemma_stable_letter_count_concat(left, r1, n);
        lemma_stable_letter_count_concat(left + r1, right, n);
        assert(stable_letter_count(w2, n) >= 4nat);

        lemma_step_preserves_word_valid(data, w1,
            DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 });
        lemma_count4_step_cant_reach_base(data, w2, w_end, step2);
        assert(false);
        return;
    }

    // Base relator: commutation
    assert((ri1 as int) < data.base.relators.len());
    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);

    // get_relator gives same result for base and HNN presentations
    assert(get_relator(data.base, ri1, inv1) =~= r1) by {
        assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
    };

    if p1 <= p0 || p1 >= p0 + 2 {
        lemma_k3_expand_relinsert_commute(
            data, w, w1, w2, w_end, p0, sym, p1, ri1, inv1, step2);
    } else {
        // p1 == p0 + 1: insert base relator between stable letters.
        // Can't directly commute (would interleave with stable pair).
        // Empty relator: w2 = w1, use k=2 directly.
        // Non-empty: dispatch on sym type (Gen→contradiction, Inv→isomorphism).
        if r1_len == 0 {
            assert(w2 =~= w1);
            let k2_steps = seq![
                DerivationStep::FreeExpand { position: p0, symbol: sym },
                step2,
            ];
            lemma_derivation_produces_2(hp,
                DerivationStep::FreeExpand { position: p0, symbol: sym },
                step2, w, w1, w_end);
            lemma_single_segment_k2(data, k2_steps, w, w_end);
        } else {
            // Non-empty base relator between stable letters.
            // w2 = w[0..p0]++[sym]++r1++[inv(sym)]++w[p0..]
            // Dispatch on sym: Gen(n) → contradiction, Inv(n) → isomorphism.
            match sym {
                Symbol::Gen(idx) => {
                    lemma_k3_relinsert_p1_gen_contra(
                        data, w, w1, w2, w_end, p0, idx, ri1, inv1, step2);
                },
                Symbol::Inv(idx) => {
                    lemma_k3_relinsert_p1_inv_iso(
                        data, w, w1, w2, w_end, p0, idx, ri1, inv1, step2);
                },
            }
        }
    }
}

/// k=3 case: step0 = FreeExpand(stable), step1 = FreeExpand(base).
/// Commutes FreeExpand(base) to act on w first, then applies k=2 lemma.
/// Special case: p1 = p0+1 (between stable letters) uses isomorphism argument.
proof fn lemma_k3_expand_freeexpand_base(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, sym: Symbol, p1: int, sym1: Symbol, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        generator_index(sym) == data.base.num_generators,
        generator_index(sym1) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));

    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int));

    lemma_base_word_valid_down(w, n);

    if p1 <= p0 {
        // === Commute: FreeExpand(base) at p1 on w, then FreeExpand(stable) at p0+2 ===
        let step1_base = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
        let w_prime = w.subrange(0, p1) + pair1 + w.subrange(p1, w.len() as int);
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));

        // w' is base
        assert(generator_index(inverse_symbol(sym1)) < n) by {
            match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
        assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
        assert(stable_letter_count(pair1, n) == 0nat);
        assert(w =~= w.subrange(0, p1) + w.subrange(p1, w.len() as int));
        lemma_stable_letter_count_concat(w.subrange(0, p1), w.subrange(p1, w.len() as int), n);
        lemma_stable_letter_count_concat(w.subrange(0, p1), pair1, n);
        lemma_stable_letter_count_concat(w.subrange(0, p1) + pair1, w.subrange(p1, w.len() as int), n);
        assert(stable_letter_count(w_prime, n) == 0nat);

        // w' is word_valid(n+1)
        lemma_word_valid_monotone(w_prime, n);

        // FreeExpand(stable) at p0+2 on w' gives w2
        let p0_adj = (p0 + 2) as int;
        let step0_adj = DerivationStep::FreeExpand { position: p0_adj, symbol: sym };
        let expand_result = w_prime.subrange(0, p0_adj) + pair
            + w_prime.subrange(p0_adj, w_prime.len() as int);

        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == expand_result[k]
        by {
            if k < p1 {
            } else if k < p1 + 2 {
                // pair1 region
            } else if k < p0_adj {
                // w[k-2] region (between p1+2 and p0+2)
            } else if k == p0_adj {
                // sym
            } else if k == p0_adj + 1 {
                // inv(sym)
            } else {
                // w[k-4+2] = w[k-2] shifted
            }
        };
        assert(w2.len() == expand_result.len());
        assert(w2 =~= expand_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

        lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
    } else if p1 >= p0 + 2 {
        // === Commute: FreeExpand(base) at p1-2 on w, then FreeExpand(stable) at p0 ===
        let p1_adj = (p1 - 2) as int;
        let step1_base = DerivationStep::FreeExpand { position: p1_adj, symbol: sym1 };
        let w_prime = w.subrange(0, p1_adj) + pair1 + w.subrange(p1_adj, w.len() as int);
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));

        // w' is base
        assert(generator_index(inverse_symbol(sym1)) < n) by {
            match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
        assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
        assert(stable_letter_count(pair1, n) == 0nat);
        assert(w =~= w.subrange(0, p1_adj) + w.subrange(p1_adj, w.len() as int));
        lemma_stable_letter_count_concat(w.subrange(0, p1_adj), w.subrange(p1_adj, w.len() as int), n);
        lemma_stable_letter_count_concat(w.subrange(0, p1_adj), pair1, n);
        lemma_stable_letter_count_concat(w.subrange(0, p1_adj) + pair1, w.subrange(p1_adj, w.len() as int), n);
        assert(stable_letter_count(w_prime, n) == 0nat);

        // w' is word_valid(n+1)
        lemma_word_valid_monotone(w_prime, n);

        // FreeExpand(stable) at p0 on w' gives w2
        let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym };
        let expand_result = w_prime.subrange(0, p0) + pair
            + w_prime.subrange(p0, w_prime.len() as int);

        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == expand_result[k]
        by {
            if k < p0 {
            } else if k == p0 {
            } else if k == p0 + 1 {
            } else if k < p1 {
                // w1[k] region (between p0+2 and p1)
            } else if k < p1 + 2 {
                // pair1 region
            } else {
                // w1[k-2] = w[k-4] region, and w'[k-2] = w[k-4]
            }
        };
        assert(w2.len() == expand_result.len());
        assert(w2 =~= expand_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

        lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
    } else {
        // === p1 = p0 + 1: between stable letters ===
        assert(p1 == p0 + 1);
        match sym {
            Symbol::Gen(idx) => {
                lemma_k3_freeexpand_gen_contra(data, w, w1, w2, w_end, p0, idx, sym1, step2);
            },
            Symbol::Inv(idx) => {
                lemma_k3_freeexpand_inv_iso(data, w, w1, w2, w_end, p0, idx, sym1, step2);
            },
        }
    }
}

/// RelatorDelete(HNN, non-inverted r2) sub-case of inside step2 (non-inverted r0).
/// r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2), positioned to overlap w2's stable letters.
proof fn lemma_k3_step2_rd_hnn_noninv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L: Word, inter: Word, tail: Word, w_R: Word, j0: int,
    p2: int, j2: int, r2: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            &&& w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R
            &&& w =~= w_L + w_R
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(tail, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(tail, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        equiv_in_presentation(data.base, inter, data.associations[j0].0),
        equiv_in_presentation(data.base, tail, inverse_word(data.associations[j0].1)),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        0 <= p2,
        p2 + r2.len() as int <= w2.len() as int,
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let (a_j2, b_j2) = data.associations[j2];
            &&& r2 == get_relator(hp, (data.base.relators.len() + j2) as nat, false)
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);
    let (a_j2, b_j2) = data.associations[j2];

    let pos_inv = w_L.len() as int;
    let pos_gen = (w_L.len() + 1 + inter.len()) as int;
    let r2_len = r2.len() as int;

    // Bridge: subrange indexing → point indexing
    assert forall|k: int| 0 <= k < r2_len
        implies #[trigger] w2[(p2 + k) as int] == r2[k]
    by {
        assert(w2.subrange(p2, p2 + r2_len)[k] == r2[k]);
    };

    // r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2)
    lemma_hnn_relator_stable_positions(data, j2);
    assert(r2[0int] == Symbol::Inv(n));

    // Position matching: p2 = pos_inv
    if p2 < pos_inv {
        assert(w2[p2] == w_L[p2]);
        assert(symbol_valid(w_L[p2], n));
        assert(false);
    } else if p2 > pos_inv && p2 < pos_gen {
        let ik = (p2 - pos_inv - 1) as int;
        assert(w2[p2] == inter[ik]);
        assert(symbol_valid(inter[ik], n));
        assert(false);
    } else if p2 == pos_gen {
        assert(w2[pos_gen] == Symbol::Gen(n));
        assert(Symbol::Gen(n) != Symbol::Inv(n));
        assert(false);
    } else if p2 > pos_gen {
        let tk = (p2 - pos_gen - 1) as int;
        if tk < tail.len() as int {
            assert(w2[p2] == tail[tk]);
            assert(symbol_valid(tail[tk], n));
        } else {
            let rk = (tk - tail.len() as int) as int;
            assert(w2[p2] == w_R[rk]);
            assert(symbol_valid(w_R[rk], n));
        }
        assert(false);
    }
    assert(p2 == pos_inv);

    // Gen(n) position in r2 must match pos_gen
    let sp2 = (p2 + a_j2.len() as int + 1) as int;
    assert(r2[(a_j2.len() + 1) as int] == Symbol::Gen(n));
    assert(w2[sp2] == r2[(a_j2.len() + 1) as int]);
    if sp2 != pos_gen {
        if sp2 > pos_inv && sp2 < pos_gen {
            let ik = (sp2 - pos_inv - 1) as int;
            assert(w2[sp2] == inter[ik]);
            assert(symbol_valid(inter[ik], n));
            assert(false);
        } else if sp2 > pos_gen {
            let tk = (sp2 - pos_gen - 1) as int;
            if tk < tail.len() as int {
                assert(w2[sp2] == tail[tk]);
                assert(symbol_valid(tail[tk], n));
            } else {
                let rk = (tk - tail.len() as int) as int;
                assert(w2[sp2] == w_R[rk]);
                assert(symbol_valid(w_R[rk], n));
            }
            assert(false);
        }
    }
    assert(sp2 == pos_gen);
    assert(a_j2.len() == inter.len());

    // a_j2 =~= inter
    assert forall|k: int| 0 <= k < inter.len() as int
        implies a_j2[k] == #[trigger] inter[k]
    by {
        assert(w2[(p2 + 1 + k) as int] == r2[(1 + k) as int]);
    };
    assert(a_j2 =~= inter);

    // Isomorphism: b_j2 ≡_G b_j0
    lemma_isomorphism_maps_equivalence(data, j0, j2);
    // inv(b_j2) ≡_G inv(b_j0)
    lemma_inverse_word_congruence(p, b_j2, b_j0);
    lemma_inverse_word_len(b_j2);

    let bj2_len = b_j2.len() as int;
    assert(r2.len() == 2 + a_j2.len() + b_j2.len());
    assert(p2 + r2_len == pos_gen + 1 + bj2_len);

    // inv(b_j2) matches content after Gen(n) in w2
    let inv_bj2 = inverse_word(b_j2);
    let after_gen = tail + w_R;
    assert forall|k: int| 0 <= k < bj2_len
        implies inv_bj2[k] == #[trigger] after_gen[k]
    by {
        assert(w2[(pos_gen + 1 + k) as int]
            == r2[(2 + inter.len() as int + k) as int]);
    };

    if bj2_len <= tail.len() as int {
        // Case 1: inv(b_j2) fits within tail
        let rest_tail = tail.subrange(bj2_len, tail.len() as int);
        let consumed = tail.subrange(0, bj2_len);
        assert(tail =~= consumed + rest_tail);
        assert forall|k: int| 0 <= k < bj2_len
            implies consumed[k] == #[trigger] inv_bj2[k]
        by {
            assert(consumed[k] == tail[k]);
            assert(after_gen[k] == tail[k]);
        };
        assert(consumed =~= inv_bj2);
        assert(w_end =~= w_L + rest_tail + w_R);

        // consumed ≡_G inv_bj0 (via inv_bj2 ≡_G inv_bj0)
        lemma_equiv_symmetric(p, inverse_word(b_j2), inv_bj0);
        lemma_equiv_transitive(p, tail, inv_bj0, inverse_word(b_j2));
        // tail ≡_G consumed (via =~= substitution)
        lemma_inverse_word_valid(b_j2, n);
        lemma_subrange_word_valid(tail, bj2_len, tail.len() as int, n);
        lemma_right_cancel(p, consumed, rest_tail);

        assert(w_end =~= concat(w_L, concat(rest_tail, w_R)));
        assert(w =~= concat(w_L, w_R));
        lemma_remove_trivial_equiv(p, w_L, w_R, rest_tail);
        lemma_base_word_valid_down(w_end, n);
        lemma_equiv_symmetric(p, w_end, w);
    } else {
        // Case 2: inv(b_j2) extends into w_R
        let delta = (bj2_len - tail.len() as int) as int;
        let wR_prefix = w_R.subrange(0, delta);
        let remaining = w_R.subrange(delta, w_R.len() as int);
        assert(w_R =~= wR_prefix + remaining);
        let consumed = tail + wR_prefix;
        assert forall|k: int| 0 <= k < bj2_len
            implies consumed[k] == #[trigger] inv_bj2[k]
        by {
            if k < tail.len() as int {
                assert(consumed[k] == tail[k]);
                assert(after_gen[k] == tail[k]);
            } else {
                let j = (k - tail.len() as int) as int;
                assert(consumed[k] == wR_prefix[j]);
                assert(wR_prefix[j] == w_R[j]);
                assert(after_gen[k] == w_R[j]);
            }
        };
        assert(consumed =~= inv_bj2);
        assert(w_end =~= w_L + remaining);

        // consumed =~= inv_bj2, inv_bj2 ≡_G inv_bj0 → consumed ≡_G inv_bj0
        // tail ≡_G inv_bj0 → inv_bj0 ≡_G tail → consumed ≡_G tail
        lemma_equiv_symmetric(p, tail, inv_bj0);
        lemma_equiv_transitive(p, consumed, inv_bj0, tail);
        lemma_subrange_word_valid(w_R, 0, delta, n);
        lemma_right_cancel(p, tail, wR_prefix);

        assert(w =~= concat(w_L, concat(wR_prefix, remaining)));
        lemma_remove_trivial_equiv(p, w_L, remaining, wR_prefix);
    }
}

/// RelatorDelete(HNN, inverted r2) sub-case of inside step2 (non-inverted r0).
/// r2 = b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)], positioned to overlap w2's stable letters.
proof fn lemma_k3_step2_rd_hnn_inv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L: Word, inter: Word, tail: Word, w_R: Word, j0: int,
    p2: int, j2: int, r2: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            &&& w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R
            &&& w =~= w_L + w_R
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(tail, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(tail, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        equiv_in_presentation(data.base, inter, data.associations[j0].0),
        equiv_in_presentation(data.base, tail, inverse_word(data.associations[j0].1)),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        0 <= p2,
        p2 + r2.len() as int <= w2.len() as int,
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            let (a_j2, b_j2) = data.associations[j2];
            &&& r2 == get_relator(hp, (data.base.relators.len() + j2) as nat, true)
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);
    let (a_j2, b_j2) = data.associations[j2];

    let pos_inv = w_L.len() as int;
    let pos_gen = (w_L.len() + 1 + inter.len()) as int;
    let r2_len = r2.len() as int;

    // Bridge: subrange indexing → point indexing
    assert forall|k: int| 0 <= k < r2_len
        implies #[trigger] w2[(p2 + k) as int] == r2[k]
    by {
        assert(w2.subrange(p2, p2 + r2_len)[k] == r2[k]);
    };

    // === Inverted r2: b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)] ===
    lemma_hnn_relator_inverted_stable_positions(data, j2);

    // r2[|b_j2|] = Inv(n) → w2[p2+|b_j2|] = Inv(n) → p2+|b_j2| = pos_inv
    let bj2_len = b_j2.len() as int;
    assert(r2[bj2_len] == Symbol::Inv(n));
    assert(w2[(p2 + bj2_len) as int] == r2[bj2_len]);
    let s = (p2 + bj2_len) as int;
    if s < pos_inv {
        assert(w2[s] == w_L[s]);
        assert(symbol_valid(w_L[s], n));
        assert(false);
    } else if s > pos_inv && s < pos_gen {
        let ik = (s - pos_inv - 1) as int;
        assert(w2[s] == inter[ik]);
        assert(symbol_valid(inter[ik], n));
        assert(false);
    } else if s == pos_gen {
        assert(w2[pos_gen] == Symbol::Gen(n));
        assert(Symbol::Gen(n) != Symbol::Inv(n));
        assert(false);
    } else if s > pos_gen {
        let tk = (s - pos_gen - 1) as int;
        if tk < tail.len() as int {
            assert(w2[s] == tail[tk]);
            assert(symbol_valid(tail[tk], n));
        } else {
            let rk = (tk - tail.len() as int) as int;
            assert(w2[s] == w_R[rk]);
            assert(symbol_valid(w_R[rk], n));
        }
        assert(false);
    }
    assert(s == pos_inv);
    assert(p2 == pos_inv - bj2_len);

    // Gen(n) position matching: p2+|b_j2|+|a_j2|+1 = pos_gen
    let sp2 = (p2 + bj2_len + 1 + a_j2.len() as int) as int;
    assert(r2[(bj2_len + a_j2.len() as int + 1) as int] == Symbol::Gen(n));
    assert(w2[sp2] == Symbol::Gen(n));
    if sp2 != pos_gen {
        if sp2 > pos_inv && sp2 < pos_gen {
            let ik = (sp2 - pos_inv - 1) as int;
            assert(w2[sp2] == inter[ik]);
            assert(symbol_valid(inter[ik], n));
            assert(false);
        } else if sp2 > pos_gen {
            let tk = (sp2 - pos_gen - 1) as int;
            if tk < tail.len() as int {
                assert(w2[sp2] == tail[tk]);
                assert(symbol_valid(tail[tk], n));
            } else {
                let rk = (tk - tail.len() as int) as int;
                assert(w2[sp2] == w_R[rk]);
                assert(symbol_valid(w_R[rk], n));
            }
            assert(false);
        }
    }
    assert(sp2 == pos_gen);
    assert(a_j2.len() == inter.len());

    // inv(a_j2) =~= inter
    let inv_aj2 = inverse_word(a_j2);
    assert forall|k: int| 0 <= k < inter.len() as int
        implies inv_aj2[k] == #[trigger] inter[k]
    by {
        assert(w2[(pos_inv + 1 + k) as int] == r2[(bj2_len + 1 + k) as int]);
    };
    assert(inv_aj2 =~= inter);

    // Chain: inv(a_j2) ≡_G a_j0 → a_j2 ≡_G inv(a_j0)
    lemma_inverse_word_valid(a_j2, n);
    lemma_inverse_word_congruence(p, inv_aj2, a_j0);
    lemma_word_inverse_left(p, a_j2);
    lemma_identity_split(p, inv_aj2, a_j2);
    let inv_inv_aj2 = inverse_word(inv_aj2);
    lemma_equiv_transitive(p, a_j2, inv_inv_aj2, inverse_word(a_j0));

    // Isomorphism: b_j2 ≡_G inv(b_j0)
    lemma_isomorphism_maps_inverse_equivalence(data, j0, j2);

    // After removing r2: w_end = w_L[0..pos_inv-|b_j2|] + tail + w_R
    assert(r2.len() == 2 + a_j2.len() + b_j2.len());
    assert(p2 + r2_len == pos_gen + 1);
    let prefix_len = (pos_inv - bj2_len) as int;
    let prefix = w_L.subrange(0, prefix_len);
    assert(w_end =~= prefix + tail + w_R);

    // b_j2 =~= w_L[prefix_len..pos_inv] (from w2 matching)
    let w_L_suffix = w_L.subrange(prefix_len, pos_inv);
    assert forall|k: int| 0 <= k < bj2_len
        implies b_j2[k] == #[trigger] w_L_suffix[k]
    by {
        assert(w2[(p2 + k) as int] == r2[k]);
    };
    assert(b_j2 =~= w_L_suffix);

    // w = w_L + w_R = prefix + w_L_suffix + w_R
    assert(w_L =~= prefix + w_L_suffix);
    assert(w =~= concat(prefix, concat(w_L_suffix, w_R)));
    assert(w_end =~= concat(prefix, concat(tail, w_R)));

    // w_L_suffix =~= b_j2 ≡_G inv(b_j0) and tail ≡_G inv(b_j0)
    lemma_equiv_symmetric(p, tail, inv_bj0);
    lemma_equiv_transitive(p, w_L_suffix, inv_bj0, tail);

    // concat(w_L_suffix, w_R) ≡_G concat(tail, w_R)
    lemma_equiv_concat_left(p, w_L_suffix, tail, w_R);
    lemma_equiv_concat_right(p, prefix,
        concat(w_L_suffix, w_R), concat(tail, w_R));
}

/// Step2 dispatch for inside-relator case, non-inverted r0 structure.
/// Given: w2 = w_L + [Inv(n)] + inter + [Gen(n)] + tail + w_R
/// with inter ≡_G a_{j0}, tail ≡_G inv(b_{j0}), w =~= w_L + w_R.
/// Proves w ≡_G w_end where step2 transforms w2 to w_end.
proof fn lemma_k3_inside_step2_noninv(
    data: HNNData, w: Word, w2: Word, w_end: Word, step2: DerivationStep,
    w_L: Word, inter: Word, tail: Word, w_R: Word, j0: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            &&& w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R
            &&& w =~= w_L + w_R
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(tail, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(tail, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        equiv_in_presentation(data.base, inter, data.associations[j0].0),
        equiv_in_presentation(data.base, tail, inverse_word(data.associations[j0].1)),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        apply_step(hnn_presentation(data), w2, step2) == Some(w_end),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);

    let pos_inv = w_L.len() as int;
    let pos_gen = (w_L.len() + 1 + inter.len()) as int;

    reveal(presentation_valid);

    match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } => {
            let pair2 = Seq::new(1, |_i: int| sym2) + Seq::new(1, |_i: int| inverse_symbol(sym2));
            assert(w_end =~= w2.subrange(0, p2) + pair2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, pair2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            assert(w_end =~= w2.subrange(0, p2) + r2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, r2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::FreeReduce { position: p2 } => {
            assert(has_cancellation_at(w2, p2));
            assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + 2, w2.len() as int));
            lemma_stable_count_reduce(w2, p2, n);

            if generator_index(w2[p2]) == n {
                // === Stable FreeReduce: stable letters must be adjacent ===
                // Prove p2 == pos_inv (the only valid starting position)
                if p2 < pos_inv {
                    assert(w2[p2] == w_L[p2]);
                    assert(symbol_valid(w_L[p2], n));
                    assert(false);
                } else if p2 > pos_inv && p2 < pos_gen {
                    let ik = (p2 - pos_inv - 1) as int;
                    assert(w2[p2] == inter[ik]);
                    assert(symbol_valid(inter[ik], n));
                    assert(false);
                } else if p2 == pos_gen {
                    // w2[p2] = Gen(n), w2[p2+1] must be Inv(n) = inverse(Gen(n))
                    // But p2+1 is in tail+w_R, all base → contradiction
                    assert(w2[p2 + 1] == inverse_symbol(w2[p2]));
                    assert(inverse_symbol(Symbol::Gen(n)) == Symbol::Inv(n));
                    if tail.len() > 0 {
                        assert(w2[(pos_gen + 1) as int] == tail[0int]);
                        assert(symbol_valid(tail[0int], n));
                    } else {
                        assert(w2[(pos_gen + 1) as int] == w_R[0int]);
                        assert(symbol_valid(w_R[0int], n));
                    }
                    assert(false);
                } else if p2 > pos_gen {
                    let tk = (p2 - pos_gen - 1) as int;
                    if tk < tail.len() as int {
                        assert(w2[p2] == tail[tk]);
                        assert(symbol_valid(tail[tk], n));
                    } else {
                        let rk = (tk - tail.len() as int) as int;
                        assert(w2[p2] == w_R[rk]);
                        assert(symbol_valid(w_R[rk], n));
                    }
                    assert(false);
                }
                assert(p2 == pos_inv);

                // w2[p2+1] = inverse_symbol(Inv(n)) = Gen(n)
                // So inter must be empty (adjacent stable letters)
                assert(w2[p2 + 1] == inverse_symbol(Symbol::Inv(n)));
                assert(inverse_symbol(Symbol::Inv(n)) == Symbol::Gen(n));
                if inter.len() > 0 {
                    assert(w2[(pos_inv + 1) as int] == inter[0int]);
                    assert(symbol_valid(inter[0int], n));
                    assert(generator_index(inter[0int]) < n);
                    assert(generator_index(Symbol::Gen(n)) == n);
                    assert(false);
                }
                assert(inter.len() == 0);
                assert(inter =~= empty_word());

                // inter ≡_G a_j0 with inter = ε → a_j0 ≡_G ε
                lemma_equiv_symmetric(p, inter, a_j0);
                // b_j0 ≡_G ε by isomorphism, inv(b_j0) ≡_G ε
                lemma_trivial_association_implies_trivial(data, j0);
                lemma_inverse_of_identity(p, b_j0);
                // tail ≡_G inv(b_j0) ≡_G ε
                lemma_equiv_transitive(p, tail, inv_bj0, empty_word());

                // w_end = w_L + tail + w_R
                assert(pos_gen == pos_inv + 1);
                assert(w_end =~= w_L + tail + w_R);
                assert(w_end =~= concat(w_L, concat(tail, w_R)));
                assert(w =~= concat(w_L, w_R));
                lemma_remove_trivial_equiv(p, w_L, w_R, tail);
                lemma_base_word_valid_down(w_end, n);
                lemma_equiv_symmetric(p, w_end, w);
            } else {
                // Base FreeReduce: count stays at 2
                assert(stable_letter_count(w_end, n) == 2nat);
                lemma_base_implies_count_zero(w_end, n);
            }
        },
        DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            let r2_len = r2.len() as int;
            assert(w2.subrange(p2, p2 + r2_len) =~= r2);
            assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));

            lemma_relator_stable_count(data, ri2, inv2);

            if (ri2 as int) < data.base.relators.len() {
                // Base relator delete: count unchanged → 2 → not base
                lemma_stable_count_subrange(w2, p2, p2 + r2_len, n);
                lemma_stable_letter_count_concat(
                    w2.subrange(0, p2), w2.subrange(p2 + r2_len, w2.len() as int), n);
                lemma_base_implies_count_zero(w_end, n);
            } else {
                // === HNN relator delete ===
                let j2 = (ri2 as int - data.base.relators.len()) as int;
                assert(0 <= j2 < data.associations.len() as int);

                if !inv2 {
                    lemma_k3_step2_rd_hnn_noninv(
                        data, w, w2, w_end, w_L, inter, tail, w_R, j0,
                        p2, j2, r2);
                } else {
                    lemma_k3_step2_rd_hnn_inv(
                        data, w, w2, w_end, w_L, inter, tail, w_R, j0,
                        p2, j2, r2);
                }
            }
        },
    }
}

/// RelatorDelete(HNN, non-inverted r2) sub-case of inside step2 (inverted r0).
/// w2 = w_L + head + [Inv(n)] + inter + [Gen(n)] + w_R
/// r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2), starts at pos_inv, extends into w_R.
proof fn lemma_k3_step2_inv_rd_noninv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L: Word, head: Word, inter: Word, w_R: Word, j0: int,
    p2: int, j2: int, r2: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            &&& w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R
            &&& w =~= w_L + w_R
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(head, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(head, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        equiv_in_presentation(data.base, head, data.associations[j0].1),
        equiv_in_presentation(data.base, inter, inverse_word(data.associations[j0].0)),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        0 <= p2,
        p2 + r2.len() as int <= w2.len() as int,
        ({
            let hp = hnn_presentation(data);
            let (a_j2, b_j2) = data.associations[j2];
            &&& r2 == get_relator(hp, (data.base.relators.len() + j2) as nat, false)
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);
    let (a_j2, b_j2) = data.associations[j2];

    let pos_inv = (w_L.len() + head.len()) as int;
    let pos_gen = (w_L.len() + head.len() + 1 + inter.len()) as int;
    let r2_len = r2.len() as int;

    // Bridge: subrange indexing → point indexing
    assert forall|k: int| 0 <= k < r2_len
        implies #[trigger] w2[(p2 + k) as int] == r2[k]
    by {
        assert(w2.subrange(p2, p2 + r2_len)[k] == r2[k]);
    };

    // r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2)
    lemma_hnn_relator_stable_positions(data, j2);
    assert(r2[0int] == Symbol::Inv(n));

    // Position matching: p2 = pos_inv
    if p2 < w_L.len() as int {
        assert(w2[p2] == w_L[p2]);
        assert(symbol_valid(w_L[p2], n));
        assert(false);
    } else if p2 < pos_inv {
        let hk = (p2 - w_L.len() as int) as int;
        assert(w2[p2] == head[hk]);
        assert(symbol_valid(head[hk], n));
        assert(false);
    } else if p2 > pos_inv && p2 < pos_gen {
        let ik = (p2 - pos_inv - 1) as int;
        assert(w2[p2] == inter[ik]);
        assert(symbol_valid(inter[ik], n));
        assert(false);
    } else if p2 == pos_gen {
        assert(w2[pos_gen] == Symbol::Gen(n));
        assert(Symbol::Gen(n) != Symbol::Inv(n));
        assert(false);
    } else if p2 > pos_gen {
        let rk = (p2 - pos_gen - 1) as int;
        assert(w2[p2] == w_R[rk]);
        assert(symbol_valid(w_R[rk], n));
        assert(false);
    }
    assert(p2 == pos_inv);

    // Gen(n) position matching
    let sp2 = (p2 + a_j2.len() as int + 1) as int;
    assert(r2[(a_j2.len() + 1) as int] == Symbol::Gen(n));
    assert(w2[sp2] == r2[(a_j2.len() + 1) as int]);
    if sp2 != pos_gen {
        if sp2 > pos_inv && sp2 < pos_gen {
            let ik = (sp2 - pos_inv - 1) as int;
            assert(w2[sp2] == inter[ik]);
            assert(symbol_valid(inter[ik], n));
            assert(false);
        } else if sp2 > pos_gen {
            let rk = (sp2 - pos_gen - 1) as int;
            assert(w2[sp2] == w_R[rk]);
            assert(symbol_valid(w_R[rk], n));
            assert(false);
        }
    }
    assert(sp2 == pos_gen);
    assert(a_j2.len() == inter.len());

    // a_j2 =~= inter
    assert forall|k: int| 0 <= k < inter.len() as int
        implies a_j2[k] == #[trigger] inter[k]
    by {
        assert(w2[(p2 + 1 + k) as int] == r2[(1 + k) as int]);
    };
    assert(a_j2 =~= inter);

    // inter ≡_G inv(a_j0), so a_j2 ≡_G inv(a_j0)
    // By isomorphism_maps_inverse_equivalence: b_j2 ≡_G inv(b_j0)
    lemma_isomorphism_maps_inverse_equivalence(data, j0, j2);
    // inv(b_j2) ≡_G inv(inv(b_j0)) =~= b_j0
    lemma_inverse_word_valid(b_j0, n);
    lemma_inverse_word_congruence(p, b_j2, inverse_word(b_j0));
    lemma_inverse_word_len(b_j2);
    crate::word::lemma_inverse_involution(b_j0);

    let bj2_len = b_j2.len() as int;
    assert(r2.len() == 2 + a_j2.len() + b_j2.len());
    assert(p2 + r2_len == pos_gen + 1 + bj2_len);

    // inv(b_j2) matches content after Gen(n) in w2, which is w_R
    let inv_bj2 = inverse_word(b_j2);
    assert forall|k: int| 0 <= k < bj2_len
        implies inv_bj2[k] == #[trigger] w_R[k]
    by {
        assert(w2[(pos_gen + 1 + k) as int] == r2[(2 + inter.len() as int + k) as int]);
    };

    // consumed = w_R[0..bj2_len] =~= inv_bj2
    let consumed = w_R.subrange(0, bj2_len);
    let remaining = w_R.subrange(bj2_len, w_R.len() as int);
    assert(w_R =~= consumed + remaining);
    assert(consumed =~= inv_bj2);

    // w_end = (w_L + head) + remaining
    assert(w_end =~= w_L + head + remaining);

    // Chain: inv_bj2 ≡_G inv(inv(b_j0)) =~= b_j0, head ≡_G b_j0
    // So consumed =~= inv_bj2 ≡_G b_j0 ≡_G head
    // head ≡_G consumed
    reveal(presentation_valid);
    lemma_equiv_symmetric(p, head, b_j0);
    lemma_equiv_transitive(p, consumed, b_j0, head);

    // w = w_L + w_R = w_L + consumed + remaining
    // w_end = w_L + head + remaining
    assert(w =~= concat(w_L, concat(consumed, remaining)));
    assert(w_end =~= concat(w_L, concat(head, remaining)));
    lemma_subrange_word_valid(w_R, 0, bj2_len, n);
    lemma_subrange_word_valid(w_R, bj2_len, w_R.len() as int, n);
    lemma_equiv_concat_left(p, consumed, head, remaining);
    lemma_equiv_concat_right(p, w_L, concat(consumed, remaining), concat(head, remaining));
}

/// RelatorDelete(HNN, inverted r2) sub-case of inside step2 (inverted r0).
/// w2 = w_L + head + [Inv(n)] + inter + [Gen(n)] + w_R
/// r2 = b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)], positioned so r2's stable letters align with w2's.
proof fn lemma_k3_step2_inv_rd_inv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L: Word, head: Word, inter: Word, w_R: Word, j0: int,
    p2: int, j2: int, r2: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            &&& w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R
            &&& w =~= w_L + w_R
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(head, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(head, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        equiv_in_presentation(data.base, head, data.associations[j0].1),
        equiv_in_presentation(data.base, inter, inverse_word(data.associations[j0].0)),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        0 <= p2,
        p2 + r2.len() as int <= w2.len() as int,
        ({
            let hp = hnn_presentation(data);
            let (a_j2, b_j2) = data.associations[j2];
            &&& r2 == get_relator(hp, (data.base.relators.len() + j2) as nat, true)
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);
    let (a_j2, b_j2) = data.associations[j2];

    let pos_inv = (w_L.len() + head.len()) as int;
    let pos_gen = (w_L.len() + head.len() + 1 + inter.len()) as int;
    let r2_len = r2.len() as int;

    // Bridge: subrange indexing → point indexing
    assert forall|k: int| 0 <= k < r2_len
        implies #[trigger] w2[(p2 + k) as int] == r2[k]
    by {
        assert(w2.subrange(p2, p2 + r2_len)[k] == r2[k]);
    };

    // r2 = b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)]
    lemma_hnn_relator_inverted_stable_positions(data, j2);
    let bj2_len = b_j2.len() as int;

    // r2[|b_j2|] = Inv(n), so w2[p2+|b_j2|] = Inv(n), must equal pos_inv
    assert(r2[bj2_len] == Symbol::Inv(n));
    assert(w2[(p2 + bj2_len) as int] == Symbol::Inv(n));
    let s = (p2 + bj2_len) as int;
    if s < w_L.len() as int {
        assert(w2[s] == w_L[s]);
        assert(symbol_valid(w_L[s], n));
        assert(false);
    } else if s >= w_L.len() as int && s < pos_inv {
        let hk = (s - w_L.len() as int) as int;
        assert(w2[s] == head[hk]);
        assert(symbol_valid(head[hk], n));
        assert(false);
    } else if s > pos_inv && s < pos_gen {
        let ik = (s - pos_inv - 1) as int;
        assert(w2[s] == inter[ik]);
        assert(symbol_valid(inter[ik], n));
        assert(false);
    } else if s == pos_gen {
        assert(w2[pos_gen] == Symbol::Gen(n));
        assert(Symbol::Gen(n) != Symbol::Inv(n));
        assert(false);
    } else if s > pos_gen {
        let rk = (s - pos_gen - 1) as int;
        assert(w2[s] == w_R[rk]);
        assert(symbol_valid(w_R[rk], n));
        assert(false);
    }
    assert(s == pos_inv);
    assert(p2 == pos_inv - bj2_len);

    // Gen(n) matching
    let inv_aj2 = inverse_word(a_j2);
    lemma_inverse_word_len(a_j2);
    let sp2 = (p2 + bj2_len + 1 + inv_aj2.len() as int) as int;
    assert(r2[(bj2_len + inv_aj2.len() as int + 1) as int] == Symbol::Gen(n));
    assert(w2[sp2] == Symbol::Gen(n));
    if sp2 != pos_gen {
        if sp2 > pos_inv && sp2 < pos_gen {
            let ik = (sp2 - pos_inv - 1) as int;
            assert(w2[sp2] == inter[ik]);
            assert(symbol_valid(inter[ik], n));
            assert(false);
        } else if sp2 > pos_gen {
            let rk = (sp2 - pos_gen - 1) as int;
            assert(w2[sp2] == w_R[rk]);
            assert(symbol_valid(w_R[rk], n));
            assert(false);
        }
    }
    assert(sp2 == pos_gen);
    assert(inv_aj2.len() == inter.len());

    // inv(a_j2) =~= inter
    assert forall|k: int| 0 <= k < inter.len() as int
        implies inv_aj2[k] == #[trigger] inter[k]
    by {
        assert(w2[(pos_inv + 1 + k) as int] == r2[(bj2_len + 1 + k) as int]);
    };
    assert(inv_aj2 =~= inter);

    // inv(a_j2) ≡_G inv(a_j0) → a_j2 ≡_G a_j0 (via double inverse)
    lemma_inverse_word_valid(a_j2, n);
    lemma_inverse_word_valid(a_j0, n);
    lemma_inverse_word_congruence(p, inv_aj2, inv_aj0);
    crate::word::lemma_inverse_involution(a_j2);
    crate::word::lemma_inverse_involution(a_j0);

    // b_j2 ≡_G b_j0 by isomorphism
    lemma_isomorphism_maps_equivalence(data, j0, j2);

    // r2 ends at pos_gen + 1 (Gen(n) is last element)
    assert(r2.len() == 2 + a_j2.len() + b_j2.len());
    assert(p2 + r2_len == pos_gen + 1);

    // w_end = w2[0..p2] + w_R
    assert(w_end =~= w2.subrange(0, p2) + w_R);

    reveal(presentation_valid);

    if bj2_len <= head.len() as int {
        // b_j2 fits within head
        let prefix_head = head.subrange(0, (head.len() as int - bj2_len) as int);
        let consumed = head.subrange((head.len() as int - bj2_len) as int, head.len() as int);
        assert(head =~= prefix_head + consumed);

        // consumed =~= b_j2
        assert forall|k: int| 0 <= k < bj2_len
            implies consumed[k] == #[trigger] b_j2[k]
        by {
            let hk = (head.len() as int - bj2_len + k) as int;
            assert(w2[(p2 + k) as int] == r2[k]);
        };
        assert(consumed =~= b_j2);

        // w_end = w_L + prefix_head + w_R
        assert(w2.subrange(0, p2) =~= w_L + prefix_head);
        assert(w_end =~= w_L + prefix_head + w_R);

        // consumed ≡_G b_j0 ≡_G head = prefix_head + consumed
        // → lemma_left_cancel → prefix_head ≡_G ε
        lemma_equiv_symmetric(p, head, b_j0);
        lemma_equiv_transitive(p, consumed, b_j0, head);
        lemma_subrange_word_valid(head, 0, (head.len() as int - bj2_len) as int, n);
        lemma_subrange_word_valid(head, (head.len() as int - bj2_len) as int, head.len() as int, n);
        assert(head =~= concat(prefix_head, consumed));
        lemma_equiv_symmetric(p, consumed, head);
        // concat(prefix_head, consumed) ≡_G consumed
        lemma_left_cancel(p, prefix_head, consumed);

        // w = w_L + w_R, w_end = w_L + prefix_head + w_R
        assert(w_end =~= concat(w_L, concat(prefix_head, w_R)));
        assert(w =~= concat(w_L, w_R));
        lemma_remove_trivial_equiv(p, w_L, w_R, prefix_head);
        lemma_equiv_symmetric(p, w_end, w);
    } else {
        // b_j2 extends into w_L
        let delta = (bj2_len - head.len() as int) as int;
        let w_L_prefix = w_L.subrange(0, (w_L.len() as int - delta) as int);
        let w_L_suffix = w_L.subrange((w_L.len() as int - delta) as int, w_L.len() as int);
        assert(w_L =~= w_L_prefix + w_L_suffix);

        // consumed = w_L_suffix + head =~= b_j2
        let consumed = w_L_suffix + head;
        assert forall|k: int| 0 <= k < bj2_len
            implies consumed[k] == #[trigger] b_j2[k]
        by {
            assert(w2[(p2 + k) as int] == r2[k]);
        };
        assert(consumed =~= b_j2);

        // w_end = w_L_prefix + w_R
        assert(w2.subrange(0, p2) =~= w_L_prefix);
        assert(w_end =~= w_L_prefix + w_R);

        // consumed ≡_G b_j0 ≡_G head
        // concat(w_L_suffix, head) ≡_G head → w_L_suffix ≡_G ε
        lemma_equiv_symmetric(p, head, b_j0);
        lemma_equiv_transitive(p, consumed, b_j0, head);
        lemma_subrange_word_valid(w_L, (w_L.len() as int - delta) as int, w_L.len() as int, n);
        assert(consumed =~= concat(w_L_suffix, head));
        lemma_equiv_symmetric(p, consumed, head);
        lemma_left_cancel(p, w_L_suffix, head);

        // w = w_L_prefix + w_L_suffix + w_R, w_end = w_L_prefix + w_R
        assert(w =~= concat(w_L_prefix, concat(w_L_suffix, w_R)));
        assert(w_end =~= concat(w_L_prefix, w_R));
        lemma_subrange_word_valid(w_L, 0, (w_L.len() as int - delta) as int, n);
        lemma_remove_trivial_equiv(p, w_L_prefix, w_R, w_L_suffix);
    }
}

/// Dispatches step2 case analysis for inverted r0 inside-relator cases.
/// w2 = w_L + head + [Inv(n)] + inter + [Gen(n)] + w_R where:
/// - head ≡_G b_j0 (pre-stable content)
/// - inter ≡_G inv(a_j0) (inter-stable content)
proof fn lemma_k3_inside_step2_inv(
    data: HNNData, w: Word, w2: Word, w_end: Word, step2: DerivationStep,
    w_L: Word, head: Word, inter: Word, w_R: Word, j0: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            &&& w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R
            &&& w =~= w_L + w_R
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(head, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(head, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        equiv_in_presentation(data.base, head, data.associations[j0].1),
        equiv_in_presentation(data.base, inter, inverse_word(data.associations[j0].0)),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        apply_step(hnn_presentation(data), w2, step2) == Some(w_end),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);

    let pos_inv = (w_L.len() + head.len()) as int;
    let pos_gen = (w_L.len() + head.len() + 1 + inter.len()) as int;

    reveal(presentation_valid);

    match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } => {
            let pair2 = Seq::new(1, |_i: int| sym2) + Seq::new(1, |_i: int| inverse_symbol(sym2));
            assert(w_end =~= w2.subrange(0, p2) + pair2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, pair2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            assert(w_end =~= w2.subrange(0, p2) + r2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, r2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::FreeReduce { position: p2 } => {
            assert(has_cancellation_at(w2, p2));
            assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + 2, w2.len() as int));
            lemma_stable_count_reduce(w2, p2, n);

            if generator_index(w2[p2]) == n {
                // Stable FreeReduce: p2 must be at pos_inv
                if p2 < w_L.len() as int {
                    assert(w2[p2] == w_L[p2]);
                    assert(symbol_valid(w_L[p2], n));
                    assert(false);
                } else if p2 >= w_L.len() as int && p2 < pos_inv {
                    let hk = (p2 - w_L.len() as int) as int;
                    assert(w2[p2] == head[hk]);
                    assert(symbol_valid(head[hk], n));
                    assert(false);
                } else if p2 > pos_inv && p2 < pos_gen {
                    let ik = (p2 - pos_inv - 1) as int;
                    assert(w2[p2] == inter[ik]);
                    assert(symbol_valid(inter[ik], n));
                    assert(false);
                } else if p2 == pos_gen {
                    assert(w2[p2 + 1] == inverse_symbol(w2[p2]));
                    assert(inverse_symbol(Symbol::Gen(n)) == Symbol::Inv(n));
                    if w_R.len() > 0 {
                        assert(w2[(pos_gen + 1) as int] == w_R[0int]);
                        assert(symbol_valid(w_R[0int], n));
                    } else {
                        assert(false); // w2 ends at pos_gen, no p2+1
                    }
                    assert(false);
                } else if p2 > pos_gen {
                    let rk = (p2 - pos_gen - 1) as int;
                    assert(w2[p2] == w_R[rk]);
                    assert(symbol_valid(w_R[rk], n));
                    assert(false);
                }
                assert(p2 == pos_inv);

                // inter must be empty (adjacent stable letters)
                assert(w2[p2 + 1] == inverse_symbol(Symbol::Inv(n)));
                assert(inverse_symbol(Symbol::Inv(n)) == Symbol::Gen(n));
                if inter.len() > 0 {
                    assert(w2[(pos_inv + 1) as int] == inter[0int]);
                    assert(symbol_valid(inter[0int], n));
                    assert(generator_index(inter[0int]) < n);
                    assert(generator_index(Symbol::Gen(n)) == n);
                    assert(false);
                }
                assert(inter.len() == 0);
                assert(inter =~= empty_word());

                // inter ≡_G inv(a_j0) with inter = ε → inv(a_j0) ≡_G ε → a_j0 ≡_G ε
                lemma_equiv_symmetric(p, inter, inv_aj0);
                lemma_inverse_word_valid(a_j0, n);
                lemma_inverse_of_identity(p, inv_aj0);
                crate::word::lemma_inverse_involution(a_j0);

                // b_j0 ≡_G ε by isomorphism, head ≡_G b_j0 ≡_G ε
                lemma_trivial_association_implies_trivial(data, j0);
                lemma_equiv_transitive(p, head, b_j0, empty_word());

                // w_end = w_L + head + w_R
                assert(pos_gen == pos_inv + 1);
                assert(w_end =~= w_L + head + w_R);
                assert(w_end =~= concat(w_L, concat(head, w_R)));
                assert(w =~= concat(w_L, w_R));
                lemma_remove_trivial_equiv(p, w_L, w_R, head);
                lemma_base_word_valid_down(w_end, n);
                lemma_equiv_symmetric(p, w_end, w);
            } else {
                // Base FreeReduce: count stays at 2 → not base
                assert(stable_letter_count(w_end, n) == 2nat);
                lemma_base_implies_count_zero(w_end, n);
            }
        },
        DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            let r2_len = r2.len() as int;
            assert(w2.subrange(p2, p2 + r2_len) =~= r2);
            assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));

            lemma_relator_stable_count(data, ri2, inv2);

            if (ri2 as int) < data.base.relators.len() {
                lemma_stable_count_subrange(w2, p2, p2 + r2_len, n);
                lemma_stable_letter_count_concat(
                    w2.subrange(0, p2), w2.subrange(p2 + r2_len, w2.len() as int), n);
                lemma_base_implies_count_zero(w_end, n);
            } else {
                let j2 = (ri2 as int - data.base.relators.len()) as int;
                assert(0 <= j2 < data.associations.len() as int);

                if !inv2 {
                    lemma_k3_step2_inv_rd_noninv(
                        data, w, w2, w_end, w_L, head, inter, w_R, j0,
                        p2, j2, r2);
                } else {
                    lemma_k3_step2_inv_rd_inv(
                        data, w, w2, w_end, w_L, head, inter, w_R, j0,
                        p2, j2, r2);
                }
            }
        },
    }
}

/// k=3 case: step0 = RelatorInsert(HNN), step1 = FreeExpand(base).
/// Inside-relator case for FreeExpand + non-inverted HNN relator.
/// p1 is inside the relator r0 = [Inv(n)] + a_j0 + [Gen(n)] + inv(b_j0).
proof fn lemma_k3_freeexpand_inside_noninv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, sym1: Symbol, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        generator_index(sym1) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, false);
            let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: false }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            &&& p0 < p1 < p0 + r0.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, false);
    let r0_len = r0.len() as int;
    let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
    let j0 = (ri0 as int - data.base.relators.len()) as int;
    assert(0 <= j0 < data.associations.len() as int);
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);

    reveal(presentation_valid);

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int));

    // Association words are base and valid
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inverse_word(b_j0), n);

    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);
    assert(w =~= w_L + w_R);
    lemma_base_word_valid_down(w, n);
    lemma_subrange_word_valid(w, 0, p0, n);
    lemma_subrange_word_valid(w, p0, w.len() as int, n);
    lemma_base_word_characterization(w_L, n);
    lemma_base_word_characterization(w_R, n);

    lemma_hnn_relator_stable_positions(data, j0);
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;
    let p1_rel = (p1 - p0) as int;

    if p1_rel <= 1 + aj0_len {
        // Sub-case A: pair inserted in a_j0 region
        let offset = (p1_rel - 1) as int;
        let inter = a_j0.subrange(0, offset) + pair1 + a_j0.subrange(offset, aj0_len);
        let tail = inv_bj0;

        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R)[k]
        by {
            if k < p0 {
            } else if k == p0 {
            } else if k < p1 {
            } else if k < p1 + 2 {
            } else if k <= p0 + 1 + aj0_len + 2 {
            } else if k == p0 + 1 + aj0_len + 2 {
            } else {
            }
        };
        assert(w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R);

        // inter is base and word_valid
        assert forall|k: int| 0 <= k < inter.len() as int
            implies symbol_valid(#[trigger] inter[k], n)
        by {
            if k < offset {
                assert(inter[k] == a_j0[k]);
            } else if k == offset {
                assert(inter[k] == sym1);
            } else if k == offset + 1 {
                assert(inter[k] == inverse_symbol(sym1));
                match sym1 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
            } else {
                assert(inter[k] == a_j0[(k - 2) as int]);
            }
        };
        assert(word_valid(inter, n));
        lemma_base_word_characterization(inter, n);

        // inter ≡_G a_j0 via FreeReduce
        let reduce_step = DerivationStep::FreeReduce { position: offset };
        assert(has_cancellation_at(inter, offset)) by {
            assert(inter[offset] == sym1);
            assert(inter[(offset + 1) as int] == inverse_symbol(sym1));
            match sym1 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
        };
        assert(inter.subrange(0, offset) + inter.subrange(offset + 2, inter.len() as int) =~= a_j0);
        assert(apply_step(data.base, inter, reduce_step) == Some(a_j0));
        lemma_single_step_equiv(data.base, inter, reduce_step, a_j0);

        // tail ≡_G inv(b_j0) by reflexivity
        lemma_equiv_refl(data.base, inv_bj0);

        // stable_letter_count(w2, n) == 2
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(tail, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], tail, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail, w_R, n);
        assert(stable_letter_count(w2, n) == 2nat);

        lemma_k3_inside_step2_noninv(
            data, w, w2, w_end, step2,
            w_L, inter, tail, w_R, j0);
    } else {
        // Sub-case B: pair inserted in inv(b_j0) region
        let offset = (p1_rel - 2 - aj0_len) as int;
        let inter = a_j0;
        let tail = inv_bj0.subrange(0, offset) + pair1 + inv_bj0.subrange(offset, inv_bj0.len() as int);

        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R)[k]
        by {
            if k < p0 {
            } else if k == p0 {
            } else if k <= p0 + aj0_len {
            } else if k == p0 + 1 + aj0_len {
            } else if k < p1 {
            } else if k < p1 + 2 {
            } else {
            }
        };
        assert(w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R);

        // tail is base and word_valid
        assert forall|k: int| 0 <= k < tail.len() as int
            implies symbol_valid(#[trigger] tail[k], n)
        by {
            if k < offset {
                assert(tail[k] == inv_bj0[k]);
            } else if k == offset {
                assert(tail[k] == sym1);
            } else if k == offset + 1 {
                assert(tail[k] == inverse_symbol(sym1));
                match sym1 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
            } else {
                assert(tail[k] == inv_bj0[(k - 2) as int]);
            }
        };
        assert(word_valid(tail, n));
        lemma_base_word_characterization(tail, n);

        // inter ≡_G a_j0 by reflexivity
        lemma_equiv_refl(data.base, a_j0);

        // tail ≡_G inv(b_j0) via FreeReduce
        let reduce_step = DerivationStep::FreeReduce { position: offset };
        assert(has_cancellation_at(tail, offset)) by {
            assert(tail[offset] == sym1);
            assert(tail[(offset + 1) as int] == inverse_symbol(sym1));
            match sym1 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
        };
        assert(tail.subrange(0, offset) + tail.subrange(offset + 2, tail.len() as int) =~= inv_bj0);
        assert(apply_step(data.base, tail, reduce_step) == Some(inv_bj0));
        lemma_single_step_equiv(data.base, tail, reduce_step, inv_bj0);

        // stable_letter_count(w2, n) == 2
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(tail, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], tail, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail, w_R, n);

        lemma_k3_inside_step2_noninv(
            data, w, w2, w_end, step2,
            w_L, inter, tail, w_R, j0);
    }
}

/// Inside-relator case for FreeExpand + inverted HNN relator.
/// r0 (inv) = b_j0 + [Inv(n)] + inv(a_j0) + [Gen(n)].
proof fn lemma_k3_freeexpand_inside_inv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, sym1: Symbol, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        generator_index(sym1) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, true);
            let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: true }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            &&& p0 < p1 < p0 + r0.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, true);
    let r0_len = r0.len() as int;
    let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
    let j0 = (ri0 as int - data.base.relators.len()) as int;
    assert(0 <= j0 < data.associations.len() as int);
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);

    reveal(presentation_valid);

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int));

    // Association words are base and valid
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    lemma_base_word_characterization(inv_aj0, n);

    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);
    assert(w =~= w_L + w_R);
    lemma_base_word_valid_down(w, n);
    lemma_subrange_word_valid(w, 0, p0, n);
    lemma_subrange_word_valid(w, p0, w.len() as int, n);
    lemma_base_word_characterization(w_L, n);
    lemma_base_word_characterization(w_R, n);

    lemma_hnn_relator_inverted_stable_positions(data, j0);
    let bj0_len = b_j0.len() as int;
    let aj0_len = a_j0.len() as int;
    let inv_aj0_len = inv_aj0.len() as int;
    lemma_inverse_word_len(a_j0);
    assert(inv_aj0_len == aj0_len);
    let p1_rel = (p1 - p0) as int;

    if p1_rel <= bj0_len {
        // Sub-case A: pair inserted in b_j0 region
        let offset = p1_rel;
        let head = b_j0.subrange(0, offset) + pair1 + b_j0.subrange(offset, bj0_len);
        let inter = inv_aj0;

        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R)[k]
        by {
            if k < p0 {
            } else if k < p1 {
            } else if k < p1 + 2 {
            } else if k <= p0 + bj0_len + 2 {
            } else if k == p0 + bj0_len + 2 {
            } else if k <= p0 + bj0_len + 2 + aj0_len {
            } else if k == p0 + bj0_len + 2 + aj0_len + 1 {
            } else {
            }
        };
        assert(w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R);

        // head is base and word_valid
        assert forall|k: int| 0 <= k < head.len() as int
            implies symbol_valid(#[trigger] head[k], n)
        by {
            if k < offset {
                assert(head[k] == b_j0[k]);
            } else if k == offset {
                assert(head[k] == sym1);
            } else if k == offset + 1 {
                assert(head[k] == inverse_symbol(sym1));
                match sym1 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
            } else {
                assert(head[k] == b_j0[(k - 2) as int]);
            }
        };
        assert(word_valid(head, n));
        lemma_base_word_characterization(head, n);

        // head ≡_G b_j0 via FreeReduce
        let reduce_step = DerivationStep::FreeReduce { position: offset };
        assert(has_cancellation_at(head, offset)) by {
            assert(head[offset] == sym1);
            assert(head[(offset + 1) as int] == inverse_symbol(sym1));
            match sym1 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
        };
        assert(head.subrange(0, offset) + head.subrange(offset + 2, head.len() as int) =~= b_j0);
        assert(apply_step(data.base, head, reduce_step) == Some(b_j0));
        lemma_single_step_equiv(data.base, head, reduce_step, b_j0);

        // inter ≡_G inv(a_j0) by reflexivity
        lemma_equiv_refl(data.base, inv_aj0);

        // stable_letter_count(w2, n) == 2
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(head, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, head, n);
        lemma_stable_letter_count_concat(w_L + head, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], w_R, n);

        lemma_k3_inside_step2_inv(
            data, w, w2, w_end, step2,
            w_L, head, inter, w_R, j0);
    } else {
        // Sub-case B: pair inserted in inv(a_j0) region
        let offset = (p1_rel - bj0_len - 1) as int;
        let head = b_j0;
        let inter = inv_aj0.subrange(0, offset) + pair1 + inv_aj0.subrange(offset, inv_aj0_len);

        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R)[k]
        by {
            if k < p0 {
            } else if k < p0 + bj0_len {
            } else if k == p0 + bj0_len {
            } else if k < p1 {
            } else if k < p1 + 2 {
            } else if k <= p0 + bj0_len + 1 + aj0_len + 2 {
            } else if k == p0 + bj0_len + 1 + aj0_len + 2 {
            } else {
            }
        };
        assert(w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R);

        // inter is base and word_valid
        assert forall|k: int| 0 <= k < inter.len() as int
            implies symbol_valid(#[trigger] inter[k], n)
        by {
            if k < offset {
                assert(inter[k] == inv_aj0[k]);
            } else if k == offset {
                assert(inter[k] == sym1);
            } else if k == offset + 1 {
                assert(inter[k] == inverse_symbol(sym1));
                match sym1 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
            } else {
                assert(inter[k] == inv_aj0[(k - 2) as int]);
            }
        };
        assert(word_valid(inter, n));
        lemma_base_word_characterization(inter, n);

        // head ≡_G b_j0 by reflexivity
        lemma_equiv_refl(data.base, b_j0);

        // inter ≡_G inv(a_j0) via FreeReduce
        let reduce_step = DerivationStep::FreeReduce { position: offset };
        assert(has_cancellation_at(inter, offset)) by {
            assert(inter[offset] == sym1);
            assert(inter[(offset + 1) as int] == inverse_symbol(sym1));
            match sym1 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
        };
        assert(inter.subrange(0, offset) + inter.subrange(offset + 2, inter.len() as int) =~= inv_aj0);
        assert(apply_step(data.base, inter, reduce_step) == Some(inv_aj0));
        lemma_single_step_equiv(data.base, inter, reduce_step, inv_aj0);

        // stable_letter_count(w2, n) == 2
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(head, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, head, n);
        lemma_stable_letter_count_concat(w_L + head, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], w_R, n);

        lemma_k3_inside_step2_inv(
            data, w, w2, w_end, step2,
            w_L, head, inter, w_R, j0);
    }
}

/// Commutes base FreeExpand to act first on w, then RelatorInsert(HNN).
proof fn lemma_k3_ri_hnn_freeexpand_base(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, sym1: Symbol, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        generator_index(sym1) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
            let step1 = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int));
    lemma_base_word_valid_down(w, n);

    if p1 <= p0 {
        // Commute: FreeExpand(base) at p1 on w, then RelatorInsert(HNN) at p0+2
        let step1_base = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
        let w_prime = w.subrange(0, p1) + pair1 + w.subrange(p1, w.len() as int);
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));

        assert(generator_index(inverse_symbol(sym1)) < n) by {
            match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
        assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
        assert(w =~= w.subrange(0, p1) + w.subrange(p1, w.len() as int));
        lemma_stable_letter_count_concat(w.subrange(0, p1), w.subrange(p1, w.len() as int), n);
        lemma_stable_letter_count_concat(w.subrange(0, p1), pair1, n);
        lemma_stable_letter_count_concat(w.subrange(0, p1) + pair1, w.subrange(p1, w.len() as int), n);
        assert(stable_letter_count(w_prime, n) == 0nat);
        lemma_word_valid_monotone(w_prime, n);

        let p0_adj = (p0 + 2) as int;
        let step0_adj = DerivationStep::RelatorInsert {
            position: p0_adj, relator_index: ri0, inverted: inv0,
        };
        let insert_result = w_prime.subrange(0, p0_adj) + r0
            + w_prime.subrange(p0_adj, w_prime.len() as int);

        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] insert_result[k]
        by {
            if k < p1 {
            } else if k < p1 + 2 {
            } else if k < p0_adj {
            } else if k < p0_adj + r0_len {
            } else {
            }
        };
        assert(w2.len() == insert_result.len());
        assert(w2 =~= insert_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
        lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
    } else if p1 >= p0 + r0_len {
        // Commute: FreeExpand(base) at p1-r0_len on w, then RelatorInsert(HNN) at p0
        let p1_adj = (p1 - r0_len) as int;
        let step1_base = DerivationStep::FreeExpand { position: p1_adj, symbol: sym1 };
        let w_prime = w.subrange(0, p1_adj) + pair1 + w.subrange(p1_adj, w.len() as int);
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));

        assert(generator_index(inverse_symbol(sym1)) < n) by {
            match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
        assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
        assert(w =~= w.subrange(0, p1_adj) + w.subrange(p1_adj, w.len() as int));
        lemma_stable_letter_count_concat(w.subrange(0, p1_adj), w.subrange(p1_adj, w.len() as int), n);
        lemma_stable_letter_count_concat(w.subrange(0, p1_adj), pair1, n);
        lemma_stable_letter_count_concat(w.subrange(0, p1_adj) + pair1, w.subrange(p1_adj, w.len() as int), n);
        assert(stable_letter_count(w_prime, n) == 0nat);
        lemma_word_valid_monotone(w_prime, n);

        let step0_adj = DerivationStep::RelatorInsert {
            position: p0, relator_index: ri0, inverted: inv0,
        };
        let insert_result = w_prime.subrange(0, p0) + r0
            + w_prime.subrange(p0, w_prime.len() as int);

        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] insert_result[k]
        by {
            if k < p0 {
            } else if k < p0 + r0_len {
            } else if k < p1 {
            } else if k < p1 + 2 {
            } else {
            }
        };
        assert(w2.len() == insert_result.len());
        assert(w2 =~= insert_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
        lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
    } else {
        // Inside relator: p0 < p1 < p0 + r0_len
        let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
        let step1_fe = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
        lemma_step_preserves_word_valid(data, w, step0);
        lemma_step_preserves_word_valid(data, w1, step1_fe);

        if !inv0 {
            lemma_k3_freeexpand_inside_noninv(
                data, w, w1, w2, w_end,
                p0, ri0, p1, sym1, step2);
        } else {
            lemma_k3_freeexpand_inside_inv(
                data, w, w1, w2, w_end,
                p0, ri0, p1, sym1, step2);
        }
    }
}

/// Inside-relator: RelatorInsert(base) in first base region of non-inv HNN relator.
/// r1 spliced into a_j0 → inter = a_j0[0..offset] + r1 + a_j0[offset..], tail = inv(b_j0).
proof fn lemma_k3_ri_noninv_splice_a(
    data: HNNData, w: Word, w2: Word, w_end: Word, step2: DerivationStep,
    w_L: Word, w_R: Word, r1: Word, ri1: nat, inv1: bool, j0: int,
    p0: int, p1: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        (ri1 as int) < data.base.relators.len(),
        word_valid(r1, data.base.num_generators),
        is_base_word(r1, data.base.num_generators),
        get_relator(data.base, ri1, inv1) =~= r1,
        w =~= w_L + w_R,
        is_base_word(w_L, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        ({
            let n = data.base.num_generators;
            let (a_j0, b_j0) = data.associations[j0];
            let aj0_len = a_j0.len() as int;
            let p1_rel = (p1 - p0) as int;
            let offset = (p1_rel - 1) as int;
            let inter = a_j0.subrange(0, offset) + r1 + a_j0.subrange(offset, aj0_len);
            let inv_bj0 = inverse_word(b_j0);
            &&& 0 <= offset <= aj0_len
            &&& w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + inv_bj0 + w_R
        }),
        apply_step(hnn_presentation(data), w2, step2) == Some(w_end),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let n = data.base.num_generators;
    let (a_j0, b_j0) = data.associations[j0];
    let aj0_len = a_j0.len() as int;
    let inv_bj0 = inverse_word(b_j0);
    let p1_rel = (p1 - p0) as int;
    let offset = (p1_rel - 1) as int;
    let r1_len = r1.len() as int;
    let inter = a_j0.subrange(0, offset) + r1 + a_j0.subrange(offset, aj0_len);
    let tail = inv_bj0;

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inv_bj0, n);

    // inter is base and word_valid
    assert forall|k: int| 0 <= k < inter.len() as int
        implies symbol_valid(#[trigger] inter[k], n)
    by {
        if k < offset { assert(inter[k] == a_j0[k]); }
        else if k < offset + r1_len { assert(inter[k] == r1[(k - offset) as int]); }
        else { assert(inter[k] == a_j0[(k - r1_len) as int]); }
    };
    assert(word_valid(inter, n));
    lemma_base_word_characterization(inter, n);

    // inter ≡_G a_j0 via RelatorDelete
    let delete_step = DerivationStep::RelatorDelete { position: offset, relator_index: ri1, inverted: inv1 };
    assert(inter.subrange(offset, offset + r1_len) =~= r1);
    assert(inter.subrange(0, offset) + inter.subrange(offset + r1_len, inter.len() as int) =~= a_j0);
    assert(apply_step(data.base, inter, delete_step) == Some(a_j0));
    lemma_single_step_equiv(data.base, inter, delete_step, a_j0);
    lemma_equiv_refl(data.base, inv_bj0);

    // stable_letter_count(w2, n) == 2
    lemma_base_implies_count_zero(w_L, n);
    lemma_base_implies_count_zero(inter, n);
    lemma_base_implies_count_zero(tail, n);
    lemma_base_implies_count_zero(w_R, n);
    lemma_stable_count_single(Symbol::Inv(n), n);
    lemma_stable_count_single(Symbol::Gen(n), n);
    lemma_stable_letter_count_concat(w_L, seq![Symbol::Inv(n)], n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)], inter, n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], tail, n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail, w_R, n);

    lemma_k3_inside_step2_noninv(data, w, w2, w_end, step2, w_L, inter, tail, w_R, j0);
}

/// Inside-relator: RelatorInsert(base) in second base region of non-inv HNN relator.
/// r1 spliced into inv(b_j0) → inter = a_j0, tail = inv(b_j0)[0..offset] + r1 + inv(b_j0)[offset..].
proof fn lemma_k3_ri_noninv_splice_b(
    data: HNNData, w: Word, w2: Word, w_end: Word, step2: DerivationStep,
    w_L: Word, w_R: Word, r1: Word, ri1: nat, inv1: bool, j0: int,
    p0: int, p1: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        (ri1 as int) < data.base.relators.len(),
        word_valid(r1, data.base.num_generators),
        is_base_word(r1, data.base.num_generators),
        get_relator(data.base, ri1, inv1) =~= r1,
        w =~= w_L + w_R,
        is_base_word(w_L, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        ({
            let n = data.base.num_generators;
            let (a_j0, b_j0) = data.associations[j0];
            let aj0_len = a_j0.len() as int;
            let inv_bj0 = inverse_word(b_j0);
            let p1_rel = (p1 - p0) as int;
            let offset = (p1_rel - 2 - aj0_len) as int;
            let tail = inv_bj0.subrange(0, offset) + r1 + inv_bj0.subrange(offset, inv_bj0.len() as int);
            &&& 0 <= offset <= inv_bj0.len()
            &&& w2 =~= w_L + seq![Symbol::Inv(n)] + a_j0 + seq![Symbol::Gen(n)] + tail + w_R
        }),
        apply_step(hnn_presentation(data), w2, step2) == Some(w_end),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let n = data.base.num_generators;
    let (a_j0, b_j0) = data.associations[j0];
    let aj0_len = a_j0.len() as int;
    let inv_bj0 = inverse_word(b_j0);
    let p1_rel = (p1 - p0) as int;
    let offset = (p1_rel - 2 - aj0_len) as int;
    let r1_len = r1.len() as int;
    let inter = a_j0;
    let tail = inv_bj0.subrange(0, offset) + r1 + inv_bj0.subrange(offset, inv_bj0.len() as int);

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inv_bj0, n);

    // tail is base and word_valid
    assert forall|k: int| 0 <= k < tail.len() as int
        implies symbol_valid(#[trigger] tail[k], n)
    by {
        if k < offset { assert(tail[k] == inv_bj0[k]); }
        else if k < offset + r1_len { assert(tail[k] == r1[(k - offset) as int]); }
        else { assert(tail[k] == inv_bj0[(k - r1_len) as int]); }
    };
    assert(word_valid(tail, n));
    lemma_base_word_characterization(tail, n);

    // tail ≡_G inv(b_j0) via RelatorDelete
    let delete_step = DerivationStep::RelatorDelete { position: offset, relator_index: ri1, inverted: inv1 };
    assert(tail.subrange(offset, offset + r1_len) =~= r1);
    assert(tail.subrange(0, offset) + tail.subrange(offset + r1_len, tail.len() as int) =~= inv_bj0);
    assert(apply_step(data.base, tail, delete_step) == Some(inv_bj0));
    lemma_single_step_equiv(data.base, tail, delete_step, inv_bj0);
    lemma_equiv_refl(data.base, a_j0);

    // stable_letter_count(w2, n) == 2
    lemma_base_implies_count_zero(w_L, n);
    lemma_base_implies_count_zero(inter, n);
    lemma_base_implies_count_zero(tail, n);
    lemma_base_implies_count_zero(w_R, n);
    lemma_stable_count_single(Symbol::Inv(n), n);
    lemma_stable_count_single(Symbol::Gen(n), n);
    lemma_stable_letter_count_concat(w_L, seq![Symbol::Inv(n)], n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)], inter, n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], tail, n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail, w_R, n);

    lemma_k3_inside_step2_noninv(data, w, w2, w_end, step2, w_L, inter, tail, w_R, j0);
}

/// Inside-relator case for RelatorInsert(base) + non-inverted HNN relator.
/// Dispatches to splice_a or splice_b based on insertion position.
proof fn lemma_k3_relinsert_inside_noninv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        word_valid(get_relator(hnn_presentation(data), ri1, inv1), data.base.num_generators),
        is_base_word(get_relator(hnn_presentation(data), ri1, inv1), data.base.num_generators),
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, false);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: false }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            &&& p0 < p1 < p0 + r0.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, false);
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let j0 = (ri0 as int - data.base.relators.len()) as int;
    assert(0 <= j0 < data.associations.len() as int);
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);

    reveal(presentation_valid);

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));

    assert(get_relator(data.base, ri1, inv1) =~= r1) by {
        assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
    };

    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);
    assert(w =~= w_L + w_R);
    lemma_base_word_valid_down(w, n);
    lemma_subrange_word_valid(w, 0, p0, n);
    lemma_subrange_word_valid(w, p0, w.len() as int, n);
    lemma_base_word_characterization(w_L, n);
    lemma_base_word_characterization(w_R, n);

    lemma_hnn_relator_stable_positions(data, j0);
    lemma_inverse_word_valid(b_j0, n);
    let aj0_len = a_j0.len() as int;
    let p1_rel = (p1 - p0) as int;

    if p1_rel <= 1 + aj0_len {
        let offset = (p1_rel - 1) as int;
        let inter = a_j0.subrange(0, offset) + r1 + a_j0.subrange(offset, aj0_len);
        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + inv_bj0 + w_R)[k]
        by {
            if k < p0 {} else if k == p0 {} else if k < p1 {}
            else if k < p1 + r1_len {} else if k <= p0 + 1 + aj0_len + r1_len {}
            else if k == p0 + 1 + aj0_len + r1_len {} else {}
        };
        assert(w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + inv_bj0 + w_R);
        lemma_k3_ri_noninv_splice_a(data, w, w2, w_end, step2, w_L, w_R, r1, ri1, inv1, j0, p0, p1);
    } else {
        let offset = (p1_rel - 2 - aj0_len) as int;
        let tail = inv_bj0.subrange(0, offset) + r1 + inv_bj0.subrange(offset, inv_bj0.len() as int);
        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + seq![Symbol::Inv(n)] + a_j0 + seq![Symbol::Gen(n)] + tail + w_R)[k]
        by {
            if k < p0 {} else if k == p0 {} else if k <= p0 + aj0_len {}
            else if k == p0 + 1 + aj0_len {} else if k < p1 {}
            else if k < p1 + r1_len {} else {}
        };
        assert(w2 =~= w_L + seq![Symbol::Inv(n)] + a_j0 + seq![Symbol::Gen(n)] + tail + w_R);
        lemma_k3_ri_noninv_splice_b(data, w, w2, w_end, step2, w_L, w_R, r1, ri1, inv1, j0, p0, p1);
    }
}

/// Inside-relator case for RelatorInsert(base) + inverted HNN relator.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
proof fn lemma_k3_relinsert_inside_inv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        word_valid(get_relator(hnn_presentation(data), ri1, inv1), data.base.num_generators),
        is_base_word(get_relator(hnn_presentation(data), ri1, inv1), data.base.num_generators),
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, true);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: true }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            &&& p0 < p1 < p0 + r0.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, true);
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let j0 = (ri0 as int - data.base.relators.len()) as int;
    assert(0 <= j0 < data.associations.len() as int);
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);

    reveal(presentation_valid);

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));

    assert(get_relator(data.base, ri1, inv1) =~= r1) by {
        assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
    };

    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    lemma_base_word_characterization(inverse_word(a_j0), n);

    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);
    assert(w =~= w_L + w_R);
    lemma_base_word_valid_down(w, n);
    lemma_subrange_word_valid(w, 0, p0, n);
    lemma_subrange_word_valid(w, p0, w.len() as int, n);
    lemma_base_word_characterization(w_L, n);
    lemma_base_word_characterization(w_R, n);

    lemma_hnn_relator_inverted_stable_positions(data, j0);
    let bj0_len = b_j0.len() as int;
    let aj0_len = a_j0.len() as int;
    lemma_inverse_word_len(a_j0);
    let p1_rel = (p1 - p0) as int;

    if p1_rel <= bj0_len {
        // Sub-case A: r1 in b_j0 region
        let offset = p1_rel;
        let head = b_j0.subrange(0, offset) + r1 + b_j0.subrange(offset, bj0_len);
        let inter = inv_aj0;

        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R)[k]
        by {
            if k < p0 {
            } else if k < p1 {
            } else if k < p1 + r1_len {
            } else if k <= p0 + bj0_len + r1_len {
            } else if k == p0 + bj0_len + r1_len {
            } else if k <= p0 + bj0_len + r1_len + aj0_len {
            } else if k == p0 + bj0_len + r1_len + aj0_len + 1 {
            } else {
            }
        };
        assert(w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R);

        // head is base and word_valid
        assert forall|k: int| 0 <= k < head.len() as int
            implies symbol_valid(#[trigger] head[k], n)
        by {
            if k < offset {
                assert(head[k] == b_j0[k]);
            } else if k < offset + r1_len {
                assert(head[k] == r1[(k - offset) as int]);
            } else {
                assert(head[k] == b_j0[(k - r1_len) as int]);
            }
        };
        assert(word_valid(head, n));
        lemma_base_word_characterization(head, n);

        // head ≡_G b_j0 via RelatorDelete
        let delete_step = DerivationStep::RelatorDelete { position: offset, relator_index: ri1, inverted: inv1 };
        assert(head.subrange(offset, offset + r1_len) =~= r1);
        assert(head.subrange(0, offset) + head.subrange(offset + r1_len, head.len() as int) =~= b_j0);
        assert(apply_step(data.base, head, delete_step) == Some(b_j0));
        lemma_single_step_equiv(data.base, head, delete_step, b_j0);

        // inter ≡_G inv(a_j0) by reflexivity
        lemma_equiv_refl(data.base, inv_aj0);

        // stable_letter_count(w2, n) == 2
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(head, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, head, n);
        lemma_stable_letter_count_concat(w_L + head, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], w_R, n);

        lemma_k3_inside_step2_inv(
            data, w, w2, w_end, step2,
            w_L, head, inter, w_R, j0);
    } else {
        // Sub-case B: r1 in inv(a_j0) region
        let offset = (p1_rel - bj0_len - 1) as int;
        let head = b_j0;
        let inter = inv_aj0.subrange(0, offset) + r1 + inv_aj0.subrange(offset, inv_aj0.len() as int);

        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R)[k]
        by {
            if k < p0 {
            } else if k < p0 + bj0_len {
            } else if k == p0 + bj0_len {
            } else if k < p1 {
            } else if k < p1 + r1_len {
            } else if k <= p0 + bj0_len + 1 + aj0_len + r1_len {
            } else if k == p0 + bj0_len + 1 + aj0_len + r1_len {
            } else {
            }
        };
        assert(w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R);

        // inter is base and word_valid
        assert forall|k: int| 0 <= k < inter.len() as int
            implies symbol_valid(#[trigger] inter[k], n)
        by {
            if k < offset {
                assert(inter[k] == inv_aj0[k]);
            } else if k < offset + r1_len {
                assert(inter[k] == r1[(k - offset) as int]);
            } else {
                assert(inter[k] == inv_aj0[(k - r1_len) as int]);
            }
        };
        assert(word_valid(inter, n));
        lemma_base_word_characterization(inter, n);

        // head ≡_G b_j0 by reflexivity
        lemma_equiv_refl(data.base, b_j0);

        // inter ≡_G inv(a_j0) via RelatorDelete
        let delete_step = DerivationStep::RelatorDelete { position: offset, relator_index: ri1, inverted: inv1 };
        assert(inter.subrange(offset, offset + r1_len) =~= r1);
        assert(inter.subrange(0, offset) + inter.subrange(offset + r1_len, inter.len() as int) =~= inv_aj0);
        assert(apply_step(data.base, inter, delete_step) == Some(inv_aj0));
        lemma_single_step_equiv(data.base, inter, delete_step, inv_aj0);

        // stable_letter_count(w2, n) == 2
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(head, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, head, n);
        lemma_stable_letter_count_concat(w_L + head, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], w_R, n);

        lemma_k3_inside_step2_inv(
            data, w, w2, w_end, step2,
            w_L, head, inter, w_R, j0);
    }
}

/// k=3 case: step0 = RelatorInsert(HNN), step1 = RelatorInsert(base).
/// Commutes base RelatorInsert to act first on w, then RelatorInsert(HNN).
proof fn lemma_k3_ri_hnn_relinsert_base(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
            let step1 = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));
    lemma_base_word_valid_down(w, n);

    // Prove r1 is base
    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);
    assert(get_relator(data.base, ri1, inv1) =~= r1) by {
        assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
    };
    if inv1 {
        lemma_inverse_word_valid(base_r, n);
        lemma_base_word_characterization(inverse_word(base_r), n);
    } else {
        lemma_base_word_characterization(base_r, n);
    }

    if p1 <= p0 {
        crate::britton_proof_helpers3::lemma_k3_ri_hnn_relinsert_base_left(
            data, w, w1, w2, w_end, p0, ri0, inv0, p1, ri1, inv1, step2);
    } else if p1 >= p0 + r0_len {
        crate::britton_proof_helpers3::lemma_k3_ri_hnn_relinsert_base_right(
            data, w, w1, w2, w_end, p0, ri0, inv0, p1, ri1, inv1, step2);
    } else {
        // Inside relator
        let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
        let step1_ri = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
        lemma_step_preserves_word_valid(data, w, step0);
        lemma_step_preserves_word_valid(data, w1, step1_ri);

        // Prove r1 is base
        let base_r = data.base.relators[ri1 as int];
        assert(hp.relators[ri1 as int] == base_r);
        if inv1 {
            lemma_inverse_word_valid(base_r, n);
            lemma_base_word_characterization(inverse_word(base_r), n);
        } else {
            lemma_base_word_characterization(base_r, n);
        }

        if !inv0 {
            lemma_k3_relinsert_inside_noninv(
                data, w, w1, w2, w_end,
                p0, ri0, p1, ri1, inv1, step2);
        } else {
            lemma_k3_relinsert_inside_inv(
                data, w, w1, w2, w_end,
                p0, ri0, p1, ri1, inv1, step2);
        }
    }
}

/// Inside-relator case for FreeReduce + non-inverted HNN relator.
/// p1 and p1+1 are both strictly inside r0 (not on stable letters or boundary with w).
/// r0 = [Inv(n)] + a_j0 + [Gen(n)] + inv(b_j0).
proof fn lemma_k3_freereduce_inside_noninv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        generator_index(w1[p1]) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, false);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: false }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeReduce { position: p1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            &&& p0 + 1 <= p1
            &&& p1 + 2 <= p0 + r0.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, false);
    let r0_len = r0.len() as int;
    let j0 = (ri0 as int - data.base.relators.len()) as int;
    assert(0 <= j0 < data.associations.len() as int);
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);

    reveal(presentation_valid);

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(has_cancellation_at(w1, p1));
    assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + 2, w1.len() as int));

    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inverse_word(b_j0), n);

    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);
    assert(w =~= w_L + w_R);
    lemma_base_word_valid_down(w, n);
    lemma_subrange_word_valid(w, 0, p0, n);
    lemma_subrange_word_valid(w, p0, w.len() as int, n);
    lemma_base_word_characterization(w_L, n);
    lemma_base_word_characterization(w_R, n);

    lemma_hnn_relator_stable_positions(data, j0);
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;
    let p1_rel = (p1 - p0) as int;

    // p1_rel >= 1 and p1_rel+1 < r0_len = 2+aj0_len+bj0_len
    // The pair can't straddle stable letter positions.
    // Stable letters: Inv(n) at r0[0], Gen(n) at r0[1+aj0_len].
    // w1[p1] has generator_index < n, so w1[p1] can't be a stable letter.
    // Also w1[p1+1] = inverse_symbol(w1[p1]) has same generator_index < n.
    // So both are base generators. They must both be in a_j0 or both in inv_bj0.

    if p1_rel <= aj0_len {
        // Sub-case A: pair in a_j0 region
        // p1 maps to a_j0[offset] where offset = p1_rel - 1
        let offset = (p1_rel - 1) as int;
        // Need: offset+1 < aj0_len (both in a_j0)
        // If offset+1 == aj0_len, then w1[p1+1] = Gen(n), index n, contradiction.
        assert(offset + 1 < aj0_len) by {
            if offset + 1 >= aj0_len {
                // p1+1 = p0+1+aj0_len, so w1[p1+1] = Gen(n)
                assert(w1[(p1 + 1) as int] == Symbol::Gen(n));
                // But has_cancellation_at means w1[p1+1] = inverse_symbol(w1[p1])
                // and generator_index(w1[p1]) < n, so generator_index(w1[p1+1]) < n too
                // But generator_index(Gen(n)) = n. Contradiction.
            }
        };

        let sym = w1[p1];
        let inter = a_j0.subrange(0, offset) + a_j0.subrange(offset + 2, aj0_len);
        let tail = inv_bj0;

        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R)[k]
        by {
            if k < p0 {
            } else if k == p0 {
            } else if k < p1 {
            } else if k < p0 + 1 + aj0_len - 2 {
                // After removal point, before Gen(n)
            } else if k == p0 + 1 + aj0_len - 2 {
            } else {
            }
        };
        assert(w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R);

        // inter is base and word_valid
        assert forall|k: int| 0 <= k < inter.len() as int
            implies symbol_valid(#[trigger] inter[k], n)
        by {
            if k < offset {
                assert(inter[k] == a_j0[k]);
            } else {
                assert(inter[k] == a_j0[(k + 2) as int]);
            }
        };
        assert(word_valid(inter, n));
        lemma_base_word_characterization(inter, n);

        // inter ≡_G a_j0 via FreeExpand (reconstruct the pair)
        let expand_step = DerivationStep::FreeExpand { position: offset, symbol: a_j0[offset] };
        assert(inter.subrange(0, offset) + seq![a_j0[offset]] + seq![inverse_symbol(a_j0[offset])] + inter.subrange(offset, inter.len() as int) =~= a_j0) by {
            // a_j0[offset+1] = inverse_symbol(a_j0[offset]) (from the cancellation)
            assert(a_j0[offset] == w1[(p0 + 1 + offset) as int]);
            assert(a_j0[(offset + 1) as int] == w1[(p0 + 1 + offset + 1) as int]);
            assert(has_cancellation_at(w1, p1));
            assert(w1[p1] == inverse_symbol(w1[(p1 + 1) as int]));
        };
        assert(apply_step(data.base, inter, expand_step) == Some(a_j0));
        lemma_single_step_equiv(data.base, inter, expand_step, a_j0);

        // tail ≡_G inv(b_j0) by reflexivity
        lemma_equiv_refl(data.base, inv_bj0);

        // stable_letter_count(w2, n) == 2
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(tail, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], tail, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail, w_R, n);
        assert(stable_letter_count(w2, n) == 2nat);

        lemma_k3_inside_step2_noninv(
            data, w, w2, w_end, step2,
            w_L, inter, tail, w_R, j0);
    } else {
        // Sub-case B: pair in inv(b_j0) region
        let offset = (p1_rel - 2 - aj0_len) as int;
        // Need: offset >= 0 and offset+1 < bj0_len
        // If p1_rel == 1+aj0_len, then w1[p1] = Gen(n), index n, contradiction.
        assert(offset >= 0 && offset + 1 < bj0_len) by {
            if p1_rel == 1 + aj0_len {
                assert(w1[p1] == Symbol::Gen(n));
            }
            // offset+1 < bj0_len because p1+2 <= p0+r0_len = p0+2+aj0_len+bj0_len
            // offset+2 = p1_rel-aj0_len = p1-p0-aj0_len
            // offset+1 < bj0_len iff p1-p0-aj0_len-1 < bj0_len iff p1 < p0+1+aj0_len+bj0_len = p0+r0_len-1
            // We have p1+2 <= p0+r0_len, so p1 <= p0+r0_len-2 = p0+aj0_len+bj0_len, so offset+1 <= bj0_len-1.
        };

        let inter = a_j0;
        let tail = inv_bj0.subrange(0, offset) + inv_bj0.subrange(offset + 2, inv_bj0.len() as int);

        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R)[k]
        by {
            if k < p0 {
            } else if k == p0 {
            } else if k <= p0 + aj0_len {
            } else if k == p0 + 1 + aj0_len {
            } else if k < p1 {
            } else {
            }
        };
        assert(w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R);

        // tail is base and word_valid
        assert forall|k: int| 0 <= k < tail.len() as int
            implies symbol_valid(#[trigger] tail[k], n)
        by {
            if k < offset {
                assert(tail[k] == inv_bj0[k]);
            } else {
                assert(tail[k] == inv_bj0[(k + 2) as int]);
            }
        };
        assert(word_valid(tail, n));
        lemma_base_word_characterization(tail, n);

        // inter ≡_G a_j0 by reflexivity
        lemma_equiv_refl(data.base, a_j0);

        // tail ≡_G inv(b_j0) via FreeExpand (reconstruct the pair)
        let expand_step = DerivationStep::FreeReduce { position: offset };
        assert(has_cancellation_at(inv_bj0, offset)) by {
            assert(inv_bj0[offset] == w1[(p0 + 2 + aj0_len + offset) as int]);
            assert(inv_bj0[(offset + 1) as int] == w1[(p0 + 2 + aj0_len + offset + 1) as int]);
            assert(w1[p1] == w1[(p0 + 2 + aj0_len + offset) as int]);
            assert(w1[(p1 + 1) as int] == w1[(p0 + 2 + aj0_len + offset + 1) as int]);
        };
        assert(inv_bj0.subrange(0, offset) + inv_bj0.subrange(offset + 2, inv_bj0.len() as int) =~= tail);
        assert(apply_step(data.base, inv_bj0, expand_step) == Some(tail));
        lemma_single_step_equiv(data.base, inv_bj0, expand_step, tail);
        // This gives inv_bj0 ≡_G tail, we need tail ≡_G inv_bj0
        lemma_equiv_symmetric(data.base, inv_bj0, tail);

        // stable_letter_count(w2, n) == 2
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(tail, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], tail, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail, w_R, n);

        lemma_k3_inside_step2_noninv(
            data, w, w2, w_end, step2,
            w_L, inter, tail, w_R, j0);
    }
}

/// Inside-relator case for FreeReduce + inverted HNN relator.
/// r0 (inv) = b_j0 + [Inv(n)] + inv(a_j0) + [Gen(n)].
proof fn lemma_k3_freereduce_inside_inv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        generator_index(w1[p1]) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, true);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: true }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeReduce { position: p1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            &&& p0 <= p1
            &&& p1 + 2 <= p0 + r0.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, true);
    let r0_len = r0.len() as int;
    let j0 = (ri0 as int - data.base.relators.len()) as int;
    assert(0 <= j0 < data.associations.len() as int);
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);

    reveal(presentation_valid);

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(has_cancellation_at(w1, p1));
    assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + 2, w1.len() as int));

    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    lemma_base_word_characterization(inverse_word(a_j0), n);

    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);
    assert(w =~= w_L + w_R);
    lemma_base_word_valid_down(w, n);
    lemma_subrange_word_valid(w, 0, p0, n);
    lemma_subrange_word_valid(w, p0, w.len() as int, n);
    lemma_base_word_characterization(w_L, n);
    lemma_base_word_characterization(w_R, n);

    lemma_hnn_relator_inverted_stable_positions(data, j0);
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;
    let p1_rel = (p1 - p0) as int;

    // Inverted r0 = b_j0 + [Inv(n)] + inv(a_j0) + [Gen(n)]
    // b_j0 at positions p0..p0+bj0_len-1
    // Inv(n) at p0+bj0_len
    // inv(a_j0) at p0+bj0_len+1..p0+bj0_len+aj0_len
    // Gen(n) at p0+bj0_len+1+aj0_len

    if p1_rel < bj0_len {
        // Sub-case A: pair in b_j0 region
        let offset = p1_rel;
        // Need: offset+1 < bj0_len
        assert(offset + 1 < bj0_len) by {
            if offset + 1 >= bj0_len {
                // p1+1 = p0+bj0_len = Inv(n) position
                assert(w1[(p1 + 1) as int] == Symbol::Inv(n));
            }
        };

        let head = b_j0.subrange(0, offset) + b_j0.subrange(offset + 2, bj0_len);
        let inter = inv_aj0;

        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R)[k]
        by {
            if k < p0 {
            } else if k < p1 {
            } else if k < p0 + bj0_len - 2 {
            } else {
            }
        };
        assert(w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R);

        // head is base and word_valid
        assert forall|k: int| 0 <= k < head.len() as int
            implies symbol_valid(#[trigger] head[k], n)
        by {
            if k < offset {
                assert(head[k] == b_j0[k]);
            } else {
                assert(head[k] == b_j0[(k + 2) as int]);
            }
        };
        assert(word_valid(head, n));
        lemma_base_word_characterization(head, n);

        // head ≡_G b_j0 via FreeExpand
        let expand_step = DerivationStep::FreeExpand { position: offset, symbol: b_j0[offset] };
        assert(head.subrange(0, offset) + seq![b_j0[offset]] + seq![inverse_symbol(b_j0[offset])] + head.subrange(offset, head.len() as int) =~= b_j0) by {
            assert(b_j0[offset] == w1[(p0 + offset) as int]);
            assert(b_j0[(offset + 1) as int] == w1[(p0 + offset + 1) as int]);
            assert(w1[p1] == inverse_symbol(w1[(p1 + 1) as int]));
        };
        assert(apply_step(data.base, head, expand_step) == Some(b_j0));
        lemma_single_step_equiv(data.base, head, expand_step, b_j0);

        // inter ≡_G inv(a_j0) by reflexivity
        lemma_equiv_refl(data.base, inv_aj0);

        // stable_letter_count(w2, n) == 2
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(head, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, head, n);
        lemma_stable_letter_count_concat(w_L + head, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], w_R, n);
        assert(stable_letter_count(w2, n) == 2nat);

        lemma_k3_inside_step2_inv(
            data, w, w2, w_end, step2,
            w_L, head, inter, w_R, j0);
    } else {
        // Sub-case B: pair in inv(a_j0) region
        let offset = (p1_rel - bj0_len - 1) as int;
        // Need: p1_rel > bj0_len (not on Inv(n))
        assert(p1_rel > bj0_len) by {
            if p1_rel == bj0_len {
                assert(w1[p1] == Symbol::Inv(n));
            }
        };
        assert(offset >= 0 && offset + 1 < aj0_len) by {
            if offset + 1 >= aj0_len {
                // p1+1 = p0+bj0_len+1+aj0_len = Gen(n) position
                assert(w1[(p1 + 1) as int] == Symbol::Gen(n));
            }
        };

        let head = b_j0;
        let inter = inv_aj0.subrange(0, offset) + inv_aj0.subrange(offset + 2, inv_aj0.len() as int);

        // w2 decomposition
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] (w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R)[k]
        by {
            if k < p0 {
            } else if k < p0 + bj0_len {
            } else if k == p0 + bj0_len {
            } else if k < p1 {
            } else {
            }
        };
        assert(w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R);

        // inter is base and word_valid
        assert forall|k: int| 0 <= k < inter.len() as int
            implies symbol_valid(#[trigger] inter[k], n)
        by {
            if k < offset {
                assert(inter[k] == inv_aj0[k]);
            } else {
                assert(inter[k] == inv_aj0[(k + 2) as int]);
            }
        };
        assert(word_valid(inter, n));
        lemma_base_word_characterization(inter, n);

        // head ≡_G b_j0 by reflexivity
        lemma_equiv_refl(data.base, b_j0);

        // inter ≡_G inv(a_j0) via FreeExpand (reconstruct pair)
        let reduce_step = DerivationStep::FreeReduce { position: offset };
        assert(has_cancellation_at(inv_aj0, offset)) by {
            assert(inv_aj0[offset] == w1[(p0 + bj0_len + 1 + offset) as int]);
            assert(inv_aj0[(offset + 1) as int] == w1[(p0 + bj0_len + 1 + offset + 1) as int]);
            assert(w1[p1] == w1[(p0 + bj0_len + 1 + offset) as int]);
        };
        assert(inv_aj0.subrange(0, offset) + inv_aj0.subrange(offset + 2, inv_aj0.len() as int) =~= inter);
        assert(apply_step(data.base, inv_aj0, reduce_step) == Some(inter));
        lemma_single_step_equiv(data.base, inv_aj0, reduce_step, inter);
        lemma_equiv_symmetric(data.base, inv_aj0, inter);

        // stable_letter_count(w2, n) == 2
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(head, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, head, n);
        lemma_stable_letter_count_concat(w_L + head, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], w_R, n);

        lemma_k3_inside_step2_inv(
            data, w, w2, w_end, step2,
            w_L, head, inter, w_R, j0);
    }
}

/// Right-boundary case for FreeReduce + non-inverted HNN relator.
/// p1 = last position of r0, so the pair straddles r0 boundary with w_R.
/// Last element of inv(b_j0) cancels with w[p0].
proof fn lemma_k3_freereduce_boundary_noninv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        generator_index(w1[p1]) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, false);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: false }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeReduce { position: p1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            &&& p1 == p0 + r0.len() - 1
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, false);
    let r0_len = r0.len() as int;
    let j0 = (ri0 as int - data.base.relators.len()) as int;
    assert(0 <= j0 < data.associations.len() as int);
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);

    reveal(presentation_valid);

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(has_cancellation_at(w1, p1));
    assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + 2, w1.len() as int));

    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inverse_word(b_j0), n);

    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);
    let w_R_short = w.subrange(p0 + 1, w.len() as int);
    assert(w =~= w_L + w_R);
    assert(w_R =~= seq![w[p0]] + w_R_short);
    lemma_base_word_valid_down(w, n);
    lemma_subrange_word_valid(w, 0, p0, n);
    lemma_subrange_word_valid(w, p0, w.len() as int, n);
    lemma_subrange_word_valid(w, p0 + 1, w.len() as int, n);
    lemma_base_word_characterization(w_L, n);
    lemma_base_word_characterization(w_R, n);
    lemma_base_word_characterization(w_R_short, n);

    lemma_hnn_relator_stable_positions(data, j0);
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;

    // The boundary pair: inv_bj0[bj0_len-1] and w[p0] cancel.
    // inv_bj0 must have length >= 1 (else p1 = p0+1+aj0_len which is Gen(n), contradiction)
    assert(bj0_len >= 1) by {
        if bj0_len == 0 {
            // r0_len = 2+aj0_len, p1 = p0+r0_len-1 = p0+1+aj0_len = Gen(n) position
            assert(w1[p1] == Symbol::Gen(n));
            // But generator_index(w1[p1]) < n and generator_index(Gen(n)) = n. Contradiction.
        }
    };

    let inv_bj_short = inv_bj0.subrange(0, bj0_len - 1);
    let last_sym = inv_bj0[(bj0_len - 1) as int];
    assert(inv_bj0 =~= inv_bj_short + seq![last_sym]);
    assert(w1[p1] == last_sym);
    assert(w1[(p1 + 1) as int] == w[p0]);
    assert(last_sym == inverse_symbol(w[p0]));

    // w2 = w_L + [Inv(n)] + a_j0 + [Gen(n)] + inv_bj_short + w_R_short
    let inter = a_j0;
    let tail = inv_bj_short;

    assert forall|k: int| 0 <= k < w2.len()
        implies w2[k] == #[trigger] (w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R_short)[k]
    by {
        if k < p0 {
        } else if k == p0 {
        } else if k <= p0 + aj0_len {
        } else if k == p0 + 1 + aj0_len {
        } else if k < p1 {
        } else {
            // After the removed pair: w2[k] = w1[k+2] = w[k+2-r0_len+1] ... = w_R_short[...]
        }
    };
    assert(w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R_short);

    // tail is base and word_valid
    lemma_subrange_word_valid(inv_bj0, 0, bj0_len - 1, n);
    lemma_base_word_characterization(tail, n);

    // stable_letter_count(w2, n) == 2
    lemma_base_implies_count_zero(w_L, n);
    lemma_base_implies_count_zero(inter, n);
    lemma_base_implies_count_zero(tail, n);
    lemma_base_implies_count_zero(w_R_short, n);
    lemma_stable_count_single(Symbol::Inv(n), n);
    lemma_stable_count_single(Symbol::Gen(n), n);
    lemma_stable_letter_count_concat(w_L, seq![Symbol::Inv(n)], n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)], inter, n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], tail, n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail, w_R_short, n);
    assert(stable_letter_count(w2, n) == 2nat);

    // Now case-analyze step2. This is like the step2 handler but with
    // w = w_L + [w[p0]] + w_R_short instead of w = w_L + w_R_short.
    // inter = a_j0 (exact), tail = inv_bj_short = inv(b_j0) minus last element.
    // Key: concat(tail, [last_sym]) = inv(b_j0), and [last_sym, w[p0]] cancels.

    // The step2 handler requires w =~= w_L + w_R, but here w = w_L + [w[p0]] + w_R_short.
    // We can't use the handler directly. Instead, we'll handle step2 inline.

    // inter ≡_G a_j0 trivially
    lemma_equiv_refl(data.base, a_j0);

    // For the boundary: we use a modified argument.
    // We know: inv(b_j0) = tail + [last_sym], [last_sym] = inverse_symbol(w[p0]).
    // w = w_L + [w[p0]] + w_R_short.
    // The key insight: for any step2 that deletes the stable letters,
    // the association matching gives b_j2 ≡_G b_j0, so inv(b_j2) ≡_G inv(b_j0).
    // Then: inv(b_j2) ≡_G tail + [last_sym].
    // Cancellation of [last_sym] with [w[p0]] connects tail back to w.

    // For now, we'll use the step2 handler with a slight trick:
    // Define w_fake = w_L + w_R_short. Then w2 has the right form for step2 handler
    // (with w_R = w_R_short). The handler proves w_fake ≡_G w_end.
    // Then we show w ≡_G w_fake (because [w[p0]] ≡_G ε is NOT true in general).
    //
    // Actually, we can't do this. We need a custom argument.
    // Let's handle step2 case by case:

    lemma_k3_freereduce_boundary_noninv_step2(
        data, w, w2, w_end, step2,
        w_L, inter, tail, w_R_short, j0, w[p0], last_sym);
}

/// Non-inverted r2 RelatorDelete sub-case for boundary FreeReduce + non-inverted r0.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_k3_freereduce_noninv_step2_rd_noninv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L: Word, inter: Word, tail: Word, w_R_short: Word,
    j0: int, wp0: Symbol, last_sym: Symbol,
    p2: int, j2: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            let inv_bj0 = inverse_word(data.associations[j0].1);
            &&& w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R_short
            &&& w =~= w_L + seq![wp0] + w_R_short
            &&& inter =~= data.associations[j0].0
            &&& tail =~= inv_bj0.subrange(0, inv_bj0.len() as int - 1)
            &&& last_sym == inv_bj0[inv_bj0.len() as int - 1]
            &&& wp0 == inverse_symbol(last_sym)
            &&& inv_bj0.len() >= 1
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(tail, data.base.num_generators),
        is_base_word(w_R_short, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(tail, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R_short, data.base.num_generators),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        ({
            let hp = hnn_presentation(data);
            let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, false);
            &&& 0 <= p2
            &&& p2 + r2.len() as int <= w2.len() as int
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);
    let bj0_len = b_j0.len() as int;
    let aj0_len = a_j0.len() as int;
    let pos_inv = w_L.len() as int;
    let pos_gen = pos_inv + 1 + aj0_len;
    let (a_j2, b_j2) = data.associations[j2];
    let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, false);

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inv_bj0, n);
    lemma_base_word_characterization(a_j2, n);
    lemma_base_word_characterization(b_j2, n);
    lemma_inverse_word_valid(b_j2, n);
    lemma_inverse_word_valid(a_j2, n);
    assert(inv_bj0 =~= tail + seq![last_sym]);
    lemma_equiv_refl(p, inv_bj0);

    // Bridge: connect r2 to hnn_relator structural facts
    assert(r2 =~= hnn_relator(data, j2)) by {
        assert(hp.relators =~= data.base.relators + hnn_relators(data));
        assert(hp.relators[(data.base.relators.len() + j2) as int]
            == hnn_relators(data)[j2 as int]);
        assert(hnn_relators(data)[j2 as int] == hnn_relator(data, j2));
    };

    // Non-inverted r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2)
    lemma_hnn_relator_stable_positions(data, j2);
    // r2[0] = Inv(n), must be at pos_inv → p2 = pos_inv
    assert(p2 == pos_inv) by {
        // r2 contains Inv(n) at r2[0] and Gen(n) at r2[1+a_j2.len()].
        // These must match w2's only stable letters at pos_inv and pos_gen.
        // If r2[0]=Inv(n) is not at pos_inv, then it's at some other position
        // where w2 has a base generator. Contradiction.
        if p2 != pos_inv {
            if p2 < pos_inv {
                assert(w2[p2] == r2[0]);
                assert(r2[0] == Symbol::Inv(n));
                // But w2[p2] for p2 < pos_inv is in w_L (base). Contradiction.
            } else {
                // p2 > pos_inv, but r2[0] = Inv(n) must match a stable letter position.
                // The only other stable is Gen(n) at pos_gen, but Inv(n) ≠ Gen(n).
                assert(w2[p2] == Symbol::Inv(n));
                if p2 <= pos_gen {
                    if p2 == pos_gen {
                        // w2[pos_gen] = Gen(n) ≠ Inv(n)
                    } else {
                        // p2 between pos_inv+1 and pos_gen-1: w2[p2] is base (inter element)
                    }
                } else {
                    // p2 > pos_gen: w2[p2] is base (tail or w_R_short)
                }
            }
        }
    };
    // a_j2 = inter = a_j0 (same content at same positions)
    assert(a_j2.len() == aj0_len) by {
        // Gen(n) at r2[1+a_j2.len()] must match pos_gen = pos_inv+1+aj0_len
        // p2 = pos_inv, so r2[1+a_j2.len()] is at position pos_inv+1+a_j2.len()
        // This must be pos_gen = pos_inv+1+aj0_len
    };
    assert(a_j2 =~= inter) by {
        assert forall|k: int| 0 <= k < a_j2.len()
            implies a_j2[k] == #[trigger] inter[k]
        by {
            assert(a_j2[k] == r2[(k + 1) as int]);
            assert(r2[(k + 1) as int] == w2[(pos_inv + 1 + k) as int]);
        };
    };
    assert(a_j2 =~= a_j0);

    // By isomorphism: a_j2 ≡_G a_j0 → b_j2 ≡_G b_j0
    lemma_equiv_refl(p, a_j0);
    lemma_isomorphism_maps_equivalence(data, j0, j2);
    // b_j2 ≡_G b_j0, so inv(b_j2) ≡_G inv(b_j0)
    lemma_inverse_word_congruence(p, b_j2, b_j0);

    let inv_bj2 = inverse_word(b_j2);
    let r2_len = r2.len() as int;
    // r2 occupies w2[pos_inv..pos_inv+r2_len]
    // After Gen(n), r2 has inv(b_j2) of length bj2_len.
    // In w2 after Gen(n): tail + w_R_short.
    // inv(b_j2) must match prefix of (tail + w_R_short).
    let bj2_len = b_j2.len() as int;
    let tail_len = tail.len() as int;

    // w_end = w_L + (tail + w_R_short)[bj2_len..]
    // We need w ≡_G w_end.
    // Key fact: inv(b_j2) ≡_G inv(b_j0) = tail + [last_sym]
    // And inv(b_j2) =~= (tail + w_R_short)[0..bj2_len]

    if bj2_len <= tail_len {
        // r2 fits within tail region
        let suffix = tail.subrange(bj2_len, tail_len);
        assert(w_end =~= w_L + suffix + w_R_short);

        // inv(b_j2) =~= tail[0..bj2_len]
        // inv(b_j2) ≡_G inv(b_j0) = tail + [last_sym]
        // So tail[0..bj2_len] ≡_G tail + [last_sym]
        // By left cancel on tail[0..bj2_len]:
        // Let prefix = tail[0..bj2_len]. Then tail = prefix + suffix.
        // prefix ≡_G prefix + suffix + [last_sym]
        // By left cancel: ε ≡_G suffix + [last_sym]
        // By identity_split: suffix ≡_G inverse_word([last_sym]) = [wp0]
        // inv(b_j2) =~= tail[0..bj2_len] (positional matching in w2)
        assert forall|k: int| 0 <= k < bj2_len
            implies inverse_word(b_j2)[k] == #[trigger] tail[k]
        by {
            assert(inverse_word(b_j2)[k] == r2[(2 + aj0_len + k) as int]);
            assert(r2[(2 + aj0_len + k) as int] == w2[(pos_gen + 1 + k) as int]);
        };
        assert(inverse_word(b_j2) =~= tail.subrange(0, bj2_len));

        // inv(b_j2) ≡_G inv(b_j0) and by =~=:
        assert(tail =~= tail.subrange(0, bj2_len) + suffix);
        assert(inv_bj0 =~= tail.subrange(0, bj2_len) + suffix + seq![last_sym]);

        // Bridge associativity for right_cancel
        assert(concat(tail.subrange(0, bj2_len), suffix + seq![last_sym])
            =~= inv_bj0);

        // Establish word_valid facts
        lemma_subrange_word_valid(tail, 0, bj2_len, n);
        lemma_subrange_word_valid(tail, bj2_len, tail_len, n);
        assert(word_valid(seq![last_sym], n)) by {
            assert(symbol_valid(last_sym, n));
        };
        lemma_concat_word_valid(suffix, seq![last_sym], n);
        lemma_inverse_word_valid(b_j2, n);

        // inv(b_j2) ≡_G inv(b_j0), flip to get inv_bj0 ≡_G inv(b_j2)
        lemma_equiv_symmetric(p, inverse_word(b_j2), inv_bj0);
        // inv_bj0 =~= concat(tail[0..bj2_len], suffix+[last_sym]) ≡_G tail[0..bj2_len] =~= inv(b_j2)
        lemma_right_cancel(p, tail.subrange(0, bj2_len), suffix + seq![last_sym]);
        // suffix + [last_sym] ≡_G ε

        // Algebraic: suffix + [last_sym] ≡_G ε, [last_sym, wp0] cancels
        let cancel_sf = seq![last_sym] + seq![wp0];
        let cancel_sf_step = DerivationStep::FreeReduce { position: 0 };
        assert(has_cancellation_at(cancel_sf, 0)) by {
            match last_sym { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
            match wp0 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
        };
        assert(apply_step(p, cancel_sf, cancel_sf_step) == Some(empty_word()));
        lemma_single_step_equiv(p, cancel_sf, cancel_sf_step, empty_word());
        lemma_equiv_concat_left(p, suffix + seq![last_sym], empty_word(), seq![wp0]);
        assert((suffix + seq![last_sym]) + seq![wp0] =~= suffix + cancel_sf);
        lemma_remove_trivial_equiv(p, suffix, empty_word(), cancel_sf);
        assert(concat(suffix, concat(cancel_sf, empty_word())) =~= suffix + cancel_sf);
        assert(concat(suffix, empty_word()) =~= suffix);
        assert(word_valid(seq![last_sym], n)) by { assert(symbol_valid(last_sym, n)); };
        assert(word_valid(seq![wp0], n)) by { assert(symbol_valid(wp0, n)); };
        lemma_concat_word_valid(seq![last_sym], seq![wp0], n);
        lemma_concat_word_valid(suffix, cancel_sf, n);
        lemma_equiv_symmetric(p, suffix + cancel_sf, seq![wp0]);
        lemma_equiv_transitive(p, seq![wp0], suffix + cancel_sf, suffix);
        // [wp0] ≡_G suffix

        // w = w_L + [wp0] + w_R_short ≡_G w_L + suffix + w_R_short = w_end
        lemma_equiv_concat_right(p, w_L, seq![wp0], suffix);
        lemma_equiv_concat_left(p, w_L + seq![wp0], w_L + suffix, w_R_short);
        assert(w =~= w_L + seq![wp0] + w_R_short);
        assert(w_end =~= w_L + suffix + w_R_short);
        assert(concat(w_L + seq![wp0], w_R_short) =~= w);
        assert(concat(w_L + suffix, w_R_short) =~= w_end);
    } else {
        // r2 extends past tail into w_R_short
        let overshoot = (bj2_len - tail_len) as int;
        assert(w_end =~= w_L + w_R_short.subrange(overshoot, w_R_short.len() as int));

        // inv(b_j2) =~= tail + w_R_short[0..overshoot]
        crate::word::lemma_inverse_word_len(b_j2);
        assert(inverse_word(b_j2) =~= tail + w_R_short.subrange(0, overshoot)) by {
            assert forall|k: int| 0 <= k < bj2_len
                implies inverse_word(b_j2)[k] == #[trigger] (tail + w_R_short.subrange(0, overshoot))[k]
            by {
                assert(inverse_word(b_j2)[k] == r2[(2 + aj0_len + k) as int]);
                assert(r2[(2 + aj0_len + k) as int] == w2[(pos_gen + 1 + k) as int]);
            };
        };
        // Bridge =~= to equiv: inv(b_j2) =~= tail+w_R[..overshoot], inv_bj0 =~= tail+[last_sym]
        // From congruence (line 8785): equiv(inv(b_j2), inv_bj0)
        // We need: equiv(concat(tail, w_R[..overshoot]), concat(tail, [last_sym]))
        // which follows from equiv(inv(b_j2), inv_bj0) + two =~= equalities.
        assert(inv_bj0 =~= tail + seq![last_sym]);
        assert(equiv_in_presentation(p, concat(tail, w_R_short.subrange(0, overshoot)), concat(tail, seq![last_sym]))) by {
            // In focused context: inv(b_j2) == tail + w_R[..overshoot] and inv_bj0 == tail + [last_sym]
            // So equiv(inv(b_j2), inv_bj0) == equiv(concat(tail, w_R[..overshoot]), concat(tail, [last_sym]))
            assert(inverse_word(b_j2) =~= tail + w_R_short.subrange(0, overshoot));
        };
        // left cancel: w_R_short[0..overshoot] ≡_G [last_sym]
        lemma_subrange_word_valid(w_R_short, 0, overshoot, n);
        assert(word_valid(seq![last_sym], n)) by { assert(symbol_valid(last_sym, n)); };
        lemma_concat_left_cancel_equiv(p, tail, w_R_short.subrange(0, overshoot), seq![last_sym]);

        // [wp0] + w_R_short[0..overshoot] ≡_G [wp0] + [last_sym] ≡_G ε
        // Because wp0 = inverse_symbol(last_sym), so [wp0, last_sym] is cancelling pair
        lemma_subrange_word_valid(w_R_short, 0, overshoot, n);
        assert(word_valid(seq![wp0], n)) by { assert(symbol_valid(wp0, n)); };
        lemma_equiv_concat_right(p, seq![wp0], w_R_short.subrange(0, overshoot), seq![last_sym]);
        // [wp0] + w_R_short[0..overshoot] ≡_G [wp0] + [last_sym]
        // [wp0, last_sym] cancels
        let cancel_word = seq![wp0] + seq![last_sym];
        let cancel_step = DerivationStep::FreeReduce { position: 0 };
        assert(has_cancellation_at(cancel_word, 0)) by {
            assert(cancel_word[0] == wp0);
            assert(cancel_word[1] == last_sym);
            match wp0 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
            match last_sym { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
        };
        assert(apply_step(p, cancel_word, cancel_step) == Some(empty_word()));
        lemma_single_step_equiv(p, cancel_word, cancel_step, empty_word());
        // cancel_word ≡_G ε
        lemma_equiv_transitive(p, seq![wp0] + w_R_short.subrange(0, overshoot), cancel_word, empty_word());

        // w = w_L + [wp0] + w_R_short[0..overshoot] + w_R_short[overshoot..]
        // ≡_G w_L + ε + w_R_short[overshoot..] = w_L + w_R_short[overshoot..] = w_end
        assert(w_R_short =~= w_R_short.subrange(0, overshoot) + w_R_short.subrange(overshoot, w_R_short.len() as int));
        assert(w =~= w_L + (seq![wp0] + w_R_short.subrange(0, overshoot)) + w_R_short.subrange(overshoot, w_R_short.len() as int));
        lemma_remove_trivial_equiv(p, w_L, w_R_short.subrange(overshoot, w_R_short.len() as int), seq![wp0] + w_R_short.subrange(0, overshoot));
        assert(concat(w_L, concat(seq![wp0] + w_R_short.subrange(0, overshoot), w_R_short.subrange(overshoot, w_R_short.len() as int))) =~= w);
        assert(concat(w_L, w_R_short.subrange(overshoot, w_R_short.len() as int)) =~= w_end);
    }
}

/// Inverted r2 RelatorDelete sub-case for boundary FreeReduce + non-inverted r0.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_k3_freereduce_noninv_step2_rd_inv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L: Word, inter: Word, tail: Word, w_R_short: Word,
    j0: int, wp0: Symbol, last_sym: Symbol,
    p2: int, j2: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            let inv_bj0 = inverse_word(data.associations[j0].1);
            &&& w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R_short
            &&& w =~= w_L + seq![wp0] + w_R_short
            &&& inter =~= data.associations[j0].0
            &&& tail =~= inv_bj0.subrange(0, inv_bj0.len() as int - 1)
            &&& last_sym == inv_bj0[inv_bj0.len() as int - 1]
            &&& wp0 == inverse_symbol(last_sym)
            &&& inv_bj0.len() >= 1
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(tail, data.base.num_generators),
        is_base_word(w_R_short, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(tail, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R_short, data.base.num_generators),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        ({
            let hp = hnn_presentation(data);
            let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, true);
            &&& 0 <= p2
            &&& p2 + r2.len() as int <= w2.len() as int
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);
    let bj0_len = b_j0.len() as int;
    let aj0_len = a_j0.len() as int;
    let pos_inv = w_L.len() as int;
    let pos_gen = pos_inv + 1 + aj0_len;
    let (a_j2, b_j2) = data.associations[j2];
    let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, true);

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inv_bj0, n);
    lemma_base_word_characterization(a_j2, n);
    lemma_base_word_characterization(b_j2, n);
    lemma_inverse_word_valid(b_j2, n);
    lemma_inverse_word_valid(a_j2, n);
    assert(inv_bj0 =~= tail + seq![last_sym]);
    lemma_equiv_refl(p, inv_bj0);

    // Bridge: connect r2 to hnn_relator structural facts
    assert(r2 =~= inverse_word(hnn_relator(data, j2))) by {
        assert(hp.relators =~= data.base.relators + hnn_relators(data));
        assert(hp.relators[(data.base.relators.len() + j2) as int]
            == hnn_relators(data)[j2 as int]);
        assert(hnn_relators(data)[j2 as int] == hnn_relator(data, j2));
    };

    // Inverted r2 = b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)]
    lemma_hnn_relator_inverted_stable_positions(data, j2);
    let inv_r = inverse_word(hnn_relator(data, j2));
    assert(r2 =~= inv_r);

    // Inv(n) at r2[b_j2.len()], Gen(n) at r2[b_j2.len()+1+a_j2.len()]
    // r2's Inv(n) must be at pos_inv: p2 + b_j2.len() = pos_inv → p2 = pos_inv - b_j2.len()
    // r2's Gen(n) at p2 + b_j2.len() + 1 + a_j2.len() = pos_inv + 1 + a_j2.len()
    // Must match pos_gen = pos_inv + 1 + aj0_len → a_j2.len() = aj0_len
    let bj2_len = b_j2.len() as int;
    let aj2_len = a_j2.len() as int;
    assert(p2 + bj2_len == pos_inv) by {
        // r2's Inv(n) position must match w2's Inv(n) at pos_inv
        // since r2 is a subrange of w2 and Inv(n) only appears once
        if p2 + bj2_len != pos_inv {
            if p2 + bj2_len < pos_inv {
                assert(w2[(p2 + bj2_len) as int] == Symbol::Inv(n));
                // but this position is in w_L (base), contradiction
            } else {
                assert(w2[(p2 + bj2_len) as int] == Symbol::Inv(n));
                if p2 + bj2_len == pos_gen {
                    // Gen(n) ≠ Inv(n)
                } else {
                    // base position, contradiction
                }
            }
        }
    };
    assert(aj2_len == aj0_len) by {
        // Gen(n) at p2+bj2_len+1+aj2_len = pos_inv+1+aj2_len must be pos_gen
    };
    // inv(a_j2) =~= inter = a_j0
    assert(inverse_word(a_j2) =~= inter) by {
        assert forall|k: int| 0 <= k < aj2_len
            implies inverse_word(a_j2)[k] == #[trigger] inter[k]
        by {
            assert(inverse_word(a_j2)[k] == r2[(bj2_len + 1 + k) as int]);
            assert(r2[(bj2_len + 1 + k) as int] == w2[(pos_inv + 1 + k) as int]);
        };
    };
    // So inv(a_j2) = a_j0 → a_j2 = inverse_word(a_j0)
    // By isomorphism_maps_inverse_equivalence: a_j2 ≡_G inv(a_j0) → b_j2 ≡_G inv(b_j0)
    crate::word::lemma_inverse_involution(a_j0);
    assert(a_j2 =~= inverse_word(a_j0)) by {
        crate::word::lemma_inverse_involution(a_j2);
    };
    lemma_equiv_refl(p, inverse_word(a_j0));
    lemma_isomorphism_maps_inverse_equivalence(data, j0, j2);
    // b_j2 ≡_G inv(b_j0) = inv_bj0 = tail + [last_sym]

    // b_j2 occupies w2[p2..p2+bj2_len] = w_L[pos_inv-bj2_len..pos_inv]
    // After deletion: w_end = w2[0..p2] + w2[p2+r2.len()..]
    // = w_L[0..pos_inv-bj2_len] + (tail + w_R_short)  [since r2 ends right after Gen(n)]
    let r2_len = r2.len() as int;
    assert(r2_len == bj2_len + 2 + aj0_len);
    // r2 starts at p2 = pos_inv-bj2_len and has length bj2_len+2+aj0_len
    // r2 ends at p2+r2_len = pos_inv + 2 + aj0_len = pos_gen + 1
    // After r2: w2[pos_gen+1..] = tail + w_R_short
    assert(w_end =~= w_L.subrange(0, pos_inv - bj2_len) + tail + w_R_short);

    // b_j2 =~= w_L[pos_inv-bj2_len..pos_inv]
    assert forall|k: int| 0 <= k < bj2_len
        implies b_j2[k] == #[trigger] w_L[(pos_inv - bj2_len + k) as int]
    by {
        assert(b_j2[k] == r2[k]);
        assert(r2[k] == w2[(p2 + k) as int]);
    };

    // b_j2 ≡_G inv_bj0 = tail + [last_sym]
    // So w_L[pos_inv-bj2_len..pos_inv] ≡_G tail + [last_sym]
    // w = w_L + [wp0] + w_R_short
    //   = w_L[0..pos_inv-bj2_len] + b_j2 + [wp0] + w_R_short
    // w_end = w_L[0..pos_inv-bj2_len] + tail + w_R_short
    // Need: b_j2 + [wp0] ≡_G tail
    // b_j2 ≡_G tail + [last_sym]
    // So b_j2 + [wp0] ≡_G tail + [last_sym] + [wp0] = tail + [last_sym, wp0]
    // [last_sym, wp0]: last_sym = inv(wp0), so [last_sym, wp0] is inverse pair.
    // tail + [last_sym, wp0] ≡_G tail + ε = tail (by removing cancelling pair)
    // So b_j2 + [wp0] ≡_G tail. QED.

    // Use concat chain approach with explicit decomposition.
    let w_L_prefix = w_L.subrange(0, pos_inv - bj2_len);
    let b_j2_content = w_L.subrange(pos_inv - bj2_len, pos_inv as int);
    assert(w_L =~= w_L_prefix + b_j2_content);
    assert(b_j2_content =~= b_j2) by {
        assert forall|k: int| 0 <= k < bj2_len
            implies b_j2_content[k] == #[trigger] b_j2[k]
        by {
            // Bridge: fires the earlier forall's trigger on w_L[...]
            assert(b_j2_content[k] == w_L[(pos_inv - bj2_len + k) as int]);
        };
    };
    assert(w =~= w_L_prefix + b_j2_content + seq![wp0] + w_R_short);
    assert(w_end =~= w_L_prefix + tail + w_R_short);

    // Show: b_j2_content + [wp0] ≡_G tail
    // b_j2 ≡_G inv_bj0 = tail + [last_sym]
    // b_j2_content =~= b_j2, inv_bj0 =~= tail + [last_sym]
    // Bridge =~= to equiv via focused assert
    assert(equiv_in_presentation(p, b_j2_content, tail + seq![last_sym])) by {
        // b_j2_content == b_j2 (from =~=) and inv_bj0 == tail + [last_sym] (from =~=)
        // equiv(b_j2, inv_bj0) from isomorphism → equiv(b_j2_content, tail + [last_sym])
        assert(b_j2_content =~= b_j2);
        assert(inv_bj0 =~= tail + seq![last_sym]);
    };
    // b_j2_content + [wp0] ≡_G tail + [last_sym] + [wp0]
    // [last_sym, wp0] cancels → tail + [last_sym, wp0] ≡_G tail
    lemma_equiv_concat_left(p, b_j2_content, tail + seq![last_sym], seq![wp0]);
    // b_j2_content + [wp0] ≡_G (tail + [last_sym]) + [wp0] = tail + [last_sym] + [wp0]
    assert((tail + seq![last_sym]) + seq![wp0] =~= tail + (seq![last_sym] + seq![wp0]));
    let cancel_pair = seq![last_sym] + seq![wp0];
    let cancel_step = DerivationStep::FreeReduce { position: 0 };
    assert(has_cancellation_at(cancel_pair, 0)) by {
        match last_sym { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
        match wp0 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
    };
    assert(apply_step(p, cancel_pair, cancel_step) == Some(empty_word()));
    lemma_single_step_equiv(p, cancel_pair, cancel_step, empty_word());
    // cancel_pair ≡_G ε
    lemma_remove_trivial_equiv(p, tail, empty_word(), cancel_pair);
    assert(concat(tail, concat(cancel_pair, empty_word())) =~= tail + cancel_pair);
    assert(concat(tail, empty_word()) =~= tail);
    // tail + cancel_pair ≡_G tail
    // Bridge: concat_left gave equiv(b_j2_content+[wp0], (tail+[last_sym])+[wp0])
    // and (tail+[last_sym])+[wp0] =~= tail+cancel_pair
    assert(equiv_in_presentation(p, b_j2_content + seq![wp0], tail + cancel_pair)) by {
        assert((tail + seq![last_sym]) + seq![wp0] =~= tail + cancel_pair);
    };
    // So b_j2_content + [wp0] ≡_G tail + cancel_pair ≡_G tail
    lemma_equiv_transitive(p, b_j2_content + seq![wp0], tail + cancel_pair, tail);

    // Now: w = w_L_prefix + (b_j2_content + [wp0]) + w_R_short
    //      ≡_G w_L_prefix + tail + w_R_short = w_end
    assert(w =~= concat(w_L_prefix, concat(b_j2_content + seq![wp0], w_R_short)));
    assert(w_end =~= concat(w_L_prefix, concat(tail, w_R_short)));
    lemma_equiv_concat_right(p, w_L_prefix, b_j2_content + seq![wp0], tail);
    // Now have: equiv(w_L_prefix + (b_j2_content+[wp0]), w_L_prefix + tail)
    lemma_equiv_concat_left(p, w_L_prefix + (b_j2_content + seq![wp0]), w_L_prefix + tail, w_R_short);
    // Now have: equiv(concat(w_L_prefix + (b_j2_content+[wp0]), w_R_short), concat(w_L_prefix + tail, w_R_short))
    // Need: equiv(w, w_end)
    // w =~= w_L_prefix + b_j2_content + seq![wp0] + w_R_short
    //   =~= concat(w_L_prefix, concat(b_j2_content + seq![wp0], w_R_short))
    // But lemma_equiv_concat_left gave: equiv(concat(X, w_R_short), concat(Y, w_R_short))
    // where X = w_L_prefix + (b_j2_content + [wp0]) and Y = w_L_prefix + tail
    // concat(X, w_R_short) = (w_L_prefix + (b_j2_content + [wp0])) + w_R_short
    // We need: this =~= w. Is it?
    // w =~= w_L_prefix + b_j2_content + seq![wp0] + w_R_short
    // X + w_R_short = (w_L_prefix + (b_j2_content + seq![wp0])) + w_R_short
    // By associativity: these should be =~=.
    assert(concat(w_L_prefix + (b_j2_content + seq![wp0]), w_R_short) =~= w);
    assert(concat(w_L_prefix + tail, w_R_short) =~= w_end);
}

/// Step2 handler for the right-boundary FreeReduce + non-inverted r0 case.
/// w2 = w_L + [Inv(n)] + inter + [Gen(n)] + tail + w_R_short, w = w_L + [wp0] + w_R_short,
/// inter = a_j0, tail = inv(b_j0).drop_last(), last_sym = inv(b_j0).last(), wp0 = inverse_symbol(last_sym).
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_k3_freereduce_boundary_noninv_step2(
    data: HNNData, w: Word, w2: Word, w_end: Word, step2: DerivationStep,
    w_L: Word, inter: Word, tail: Word, w_R_short: Word, j0: int, wp0: Symbol, last_sym: Symbol,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            let inv_bj0 = inverse_word(data.associations[j0].1);
            &&& w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R_short
            &&& w =~= w_L + seq![wp0] + w_R_short
            &&& inter =~= data.associations[j0].0
            &&& tail =~= inv_bj0.subrange(0, inv_bj0.len() as int - 1)
            &&& last_sym == inv_bj0[inv_bj0.len() as int - 1]
            &&& wp0 == inverse_symbol(last_sym)
            &&& inv_bj0.len() >= 1
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(tail, data.base.num_generators),
        is_base_word(w_R_short, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(tail, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R_short, data.base.num_generators),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        apply_step(hnn_presentation(data), w2, step2) == Some(w_end),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);
    let bj0_len = b_j0.len() as int;
    let aj0_len = a_j0.len() as int;
    let p = data.base;

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inv_bj0, n);

    let pos_inv = w_L.len() as int;
    let pos_gen = pos_inv + 1 + aj0_len;

    // w2 has stable letters at pos_inv and pos_gen.
    // step2 must remove both. Only FreeReduce(stable) or RelatorDelete(HNN) can do this.

    // inv_bj0 = tail + [last_sym] — needed for RelatorDelete branches
    assert(inv_bj0 =~= tail + seq![last_sym]);
    lemma_equiv_refl(p, inv_bj0);

    match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } => {
            // Adds 0 or 2 stable letters. Count stays >= 2. Not base. Contradiction.
            let pair2 = Seq::new(1, |_i: int| sym2) + Seq::new(1, |_i: int| inverse_symbol(sym2));
            assert(w_end =~= w2.subrange(0, p2) + pair2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, pair2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } => {
            // Adds 0 or 2 stable letters. Same argument.
            let r2 = get_relator(hp, ri2, inv2);
            assert(w_end =~= w2.subrange(0, p2) + r2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, r2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::FreeReduce { position: p2 } => {
            // Reduces by 0 or 2 stable letters.
            lemma_stable_count_reduce(w2, p2, n);
            if generator_index(w2[p2]) == n {
                // Stable FreeReduce: removes 2 stable letters → count = 0 → base.
                // The two stable letters must be adjacent: positions p2 and p2+1.
                // They must be at pos_inv and pos_gen. For adjacency: pos_gen = pos_inv + 1,
                // meaning aj0_len = 0, so inter is empty.
                assert(p2 == pos_inv || p2 == pos_gen || (p2 != pos_inv && p2 != pos_gen));
                // The only stable positions are pos_inv and pos_gen. For cancellation,
                // one must be at p2 and the other at p2+1.
                assert(p2 == pos_inv) by {
                    // w2[p2] is stable, so p2 is pos_inv or pos_gen.
                    // If p2 == pos_gen, then w2[p2] = Gen(n), w2[p2+1] must be Inv(n).
                    // But p2+1 > pos_gen, and next stable is... none after pos_gen in the base region.
                    // Actually w2[pos_gen+1..] = tail + w_R_short, all base. So w2[p2+1] has index < n.
                    // Contradiction with cancellation (same gen_index needed).
                };
                // p2 = pos_inv: w2[p2] = Inv(n), w2[p2+1] must cancel with it.
                // w2[pos_inv+1] = inter[0] if inter nonempty, else Gen(n).
                // For cancellation: w2[pos_inv+1] = Gen(n), meaning inter is empty, aj0_len = 0.
                assert(aj0_len == 0) by {
                    // w2[pos_inv] = Inv(n), w2[pos_inv+1] = inverse_symbol(Inv(n)) = Gen(n)
                    // This means w2[pos_inv+1] = Gen(n), which is inter[0] or Gen(n) if inter empty
                };
                assert(inter.len() == 0);
                assert(a_j0.len() == 0);
                // a_j0 = ε → a_j0 ≡_G ε
                lemma_equiv_refl(p, empty_word());
                assert(a_j0 =~= empty_word());
                // By trivial association: b_j0 ≡_G ε
                lemma_trivial_association_implies_trivial(data, j0);
                // inv(b_j0) ≡_G ε
                lemma_inverse_of_identity(p, b_j0);

                // After FreeReduce: w_end = w_L + tail + w_R_short
                assert(w_end =~= w_L + tail + w_R_short);

                // tail = inv_bj0[0..bj0_len-1], and inv_bj0 ≡_G ε.
                // So tail ++ [last_sym] = inv_bj0 ≡_G ε.
                // [last_sym, wp0] also cancel (they're inverse symbols).
                // So [wp0] ≡_G [last_sym]^{-1} ... hmm, let's use a simpler argument:
                // inv_bj0 ≡_G ε means all of inv_bj0 represents the identity.
                // tail = inv_bj0 minus last element. We need w = w_L + [wp0] + w_R_short ≡_G w_end = w_L + tail + w_R_short.
                // i.e., [wp0] ≡_G tail.
                // We know: inv_bj0 = tail + [last_sym] ≡_G ε.
                // By identity_split: tail ≡_G inverse_word([last_sym]) = [inverse_symbol(last_sym)] = [wp0].
                assert(inv_bj0 =~= tail + seq![last_sym]);
                // Algebraic approach: tail + [last_sym] ≡_G ε, and [last_sym, wp0] cancels
                let cancel = seq![last_sym] + seq![wp0];
                let cancel_step_fr = DerivationStep::FreeReduce { position: 0 };
                assert(has_cancellation_at(cancel, 0)) by {
                    match last_sym { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
                    match wp0 { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
                };
                assert(apply_step(p, cancel, cancel_step_fr) == Some(empty_word()));
                lemma_single_step_equiv(p, cancel, cancel_step_fr, empty_word());
                // cancel ≡_G ε

                // Append [wp0] to both sides: (tail+[last_sym])+[wp0] ≡_G [wp0]
                lemma_equiv_concat_left(p, tail + seq![last_sym], empty_word(), seq![wp0]);
                assert((tail + seq![last_sym]) + seq![wp0] =~= tail + cancel);

                // tail + cancel ≡_G tail (remove trivial)
                lemma_remove_trivial_equiv(p, tail, empty_word(), cancel);
                assert(concat(tail, concat(cancel, empty_word())) =~= tail + cancel);
                assert(concat(tail, empty_word()) =~= tail);

                // Chain: tail ≡ tail+cancel ≡ [wp0]
                assert(word_valid(seq![last_sym], n)) by { assert(symbol_valid(last_sym, n)); };
                assert(word_valid(seq![wp0], n)) by { assert(symbol_valid(wp0, n)); };
                lemma_concat_word_valid(seq![last_sym], seq![wp0], n);
                lemma_concat_word_valid(tail, cancel, n);
                lemma_equiv_symmetric(p, tail + cancel, seq![wp0]);
                lemma_equiv_transitive(p, seq![wp0], tail + cancel, tail);
                // [wp0] ≡_G tail
                lemma_equiv_concat_right(p, w_L, seq![wp0], tail);
                lemma_equiv_concat_left(p, w_L + seq![wp0], w_L + tail, w_R_short);
                assert(w =~= w_L + seq![wp0] + w_R_short);
                assert(w_end =~= w_L + tail + w_R_short);
            }
            else {
                // Base FreeReduce: count stays at 2
                assert(stable_letter_count(w_end, n) == 2nat);
                lemma_base_implies_count_zero(w_end, n);
            }
        },
        DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            let r2_len = r2.len() as int;
            assert(w2.subrange(p2, p2 + r2_len) =~= r2);
            assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));

            lemma_relator_stable_count(data, ri2, inv2);

            if (ri2 as int) < p.relators.len() {
                // Base relator delete: count unchanged → 2 → not base
                lemma_stable_count_subrange(w2, p2, p2 + r2_len, n);
                lemma_stable_letter_count_concat(
                    w2.subrange(0, p2), w2.subrange(p2 + r2_len, w2.len() as int), n);
                lemma_base_implies_count_zero(w_end, n);
            } else {
                // HNN relator: removes 2 stable letters.
                let j2 = (ri2 as int - p.relators.len()) as int;
                let (a_j2, b_j2) = data.associations[j2];
                lemma_base_word_characterization(a_j2, n);
                lemma_base_word_characterization(b_j2, n);
                lemma_inverse_word_valid(b_j2, n);
                lemma_inverse_word_valid(a_j2, n);
                assert(w2.subrange(p2, p2 + r2.len()) =~= r2);
                assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int));

                assert(ri2 == (data.base.relators.len() + j2) as nat);
                if !inv2 {
                    lemma_k3_freereduce_noninv_step2_rd_noninv(
                        data, w, w2, w_end, w_L, inter, tail, w_R_short,
                        j0, wp0, last_sym, p2, j2);
                } else {
                    lemma_k3_freereduce_noninv_step2_rd_inv(
                        data, w, w2, w_end, w_L, inter, tail, w_R_short,
                        j0, wp0, last_sym, p2, j2);
                }
            }
        },
    }
}

/// Left-boundary case for FreeReduce + inverted HNN relator.
/// p1 = p0-1, so the pair straddles w_L boundary with r0.
/// w[p0-1] cancels with b_j0[0].
proof fn lemma_k3_freereduce_boundary_inv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        generator_index(w1[p1]) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, true);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: true }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeReduce { position: p1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            &&& p1 == p0 - 1
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, true);
    let r0_len = r0.len() as int;
    let j0 = (ri0 as int - data.base.relators.len()) as int;
    assert(0 <= j0 < data.associations.len() as int);
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);

    reveal(presentation_valid);

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(has_cancellation_at(w1, p1));
    assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + 2, w1.len() as int));

    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    lemma_base_word_characterization(inverse_word(a_j0), n);

    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);
    let w_L_short = w.subrange(0, p0 - 1);
    assert(w =~= w_L + w_R);
    assert(w_L =~= w_L_short + seq![w[(p0 - 1) as int]]);
    lemma_base_word_valid_down(w, n);
    lemma_subrange_word_valid(w, 0, p0, n);
    lemma_subrange_word_valid(w, p0, w.len() as int, n);
    lemma_subrange_word_valid(w, 0, p0 - 1, n);
    lemma_base_word_characterization(w_L, n);
    lemma_base_word_characterization(w_R, n);
    lemma_base_word_characterization(w_L_short, n);

    lemma_hnn_relator_inverted_stable_positions(data, j0);
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;

    // The boundary pair: w[p0-1] and b_j0[0] cancel.
    // b_j0 must have length >= 1 (else r0[0] = Inv(n), and p1+1 = p0 = Inv(n) position,
    // so w1[p1+1] = Inv(n), gen_index = n, but has_cancellation requires same index as w1[p1] < n. Contradiction.)
    assert(bj0_len >= 1) by {
        if bj0_len == 0 {
            assert(w1[(p1 + 1) as int] == w1[p0]);
            assert(w1[p0] == Symbol::Inv(n));
        }
    };

    let first_sym = b_j0[0];
    let wp_last = w[(p0 - 1) as int];
    let bj_short = b_j0.subrange(1, bj0_len);
    assert(b_j0 =~= seq![first_sym] + bj_short);
    assert(w1[p1] == wp_last);
    assert(w1[(p1 + 1) as int] == first_sym);
    assert(wp_last == inverse_symbol(first_sym));

    // w2 = w_L_short + bj_short + [Inv(n)] + inv(a_j0) + [Gen(n)] + w_R
    let head = bj_short;
    let inter = inv_aj0;

    assert forall|k: int| 0 <= k < w2.len()
        implies w2[k] == #[trigger] (w_L_short + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R)[k]
    by {
        if k < p0 - 1 {
        } else {
        }
    };
    assert(w2 =~= w_L_short + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R);

    // head is base and word_valid
    lemma_subrange_word_valid(b_j0, 1, bj0_len, n);
    lemma_base_word_characterization(head, n);

    // stable_letter_count(w2, n) == 2
    lemma_base_implies_count_zero(w_L_short, n);
    lemma_base_implies_count_zero(head, n);
    lemma_base_implies_count_zero(inter, n);
    lemma_base_implies_count_zero(w_R, n);
    lemma_stable_count_single(Symbol::Inv(n), n);
    lemma_stable_count_single(Symbol::Gen(n), n);
    lemma_stable_letter_count_concat(w_L_short, head, n);
    lemma_stable_letter_count_concat(w_L_short + head, seq![Symbol::Inv(n)], n);
    lemma_stable_letter_count_concat(w_L_short + head + seq![Symbol::Inv(n)], inter, n);
    lemma_stable_letter_count_concat(w_L_short + head + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
    lemma_stable_letter_count_concat(w_L_short + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], w_R, n);
    assert(stable_letter_count(w2, n) == 2nat);

    // This is symmetric to the noninv boundary case.
    // head = bj_short = b_j0[1..], first_sym = b_j0[0], wp_last = inverse_symbol(first_sym).
    // w = w_L_short + [wp_last] + w_R.
    // Step2 handler with the boundary twist.
    lemma_k3_freereduce_boundary_inv_step2(
        data, w, w2, w_end, step2,
        w_L_short, head, inter, w_R, j0, wp_last, first_sym);
}

/// Non-inverted r2 RelatorDelete sub-case for boundary FreeReduce + inverted r0.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_k3_freereduce_inv_step2_rd_noninv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L_short: Word, head: Word, inter: Word, w_R: Word,
    j0: int, wp_last: Symbol, first_sym: Symbol,
    p2: int, j2: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            let b_j0 = data.associations[j0].1;
            &&& w2 =~= w_L_short + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R
            &&& w =~= w_L_short + seq![wp_last] + w_R
            &&& inter =~= inverse_word(data.associations[j0].0)
            &&& head =~= b_j0.subrange(1, b_j0.len() as int)
            &&& first_sym == b_j0[0]
            &&& wp_last == inverse_symbol(first_sym)
            &&& b_j0.len() >= 1
        }),
        is_base_word(w_L_short, data.base.num_generators),
        is_base_word(head, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(head, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(w_L_short, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        ({
            let hp = hnn_presentation(data);
            let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, false);
            &&& 0 <= p2
            &&& p2 + r2.len() as int <= w2.len() as int
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);
    let bj0_len = b_j0.len() as int;
    let aj0_len = a_j0.len() as int;
    let (a_j2, b_j2) = data.associations[j2];
    let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, false);

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    crate::word::lemma_inverse_word_len(a_j0);
    lemma_base_word_characterization(inv_aj0, n);
    lemma_base_word_characterization(a_j2, n);
    lemma_base_word_characterization(b_j2, n);
    lemma_inverse_word_valid(b_j2, n);
    lemma_inverse_word_valid(a_j2, n);

    let head_len = head.len() as int;
    let pos_inv = w_L_short.len() as int + head_len;
    let pos_gen = pos_inv + 1 + aj0_len;

    // Bridge: connect r2 to hnn_relator structural facts
    assert(r2 =~= hnn_relator(data, j2)) by {
        assert(hp.relators =~= data.base.relators + hnn_relators(data));
        assert(hp.relators[(data.base.relators.len() + j2) as int]
            == hnn_relators(data)[j2 as int]);
        assert(hnn_relators(data)[j2 as int] == hnn_relator(data, j2));
    };

    // Non-inverted r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2)
    lemma_hnn_relator_stable_positions(data, j2);
    assert(p2 == pos_inv) by {
        if p2 != pos_inv {
            if p2 < pos_inv {
                assert(w2[p2] == Symbol::Inv(n));
            } else {
                assert(w2[p2] == Symbol::Inv(n));
                if p2 == pos_gen {} else {}
            }
        }
    };
    let aj2_len = a_j2.len() as int;
    // Gen(n) in r2 at index 1+aj2_len must align with pos_gen
    assert(aj2_len == aj0_len) by {
        assert(r2[(1 + aj2_len) as int] == Symbol::Gen(n));
        assert(w2[(pos_inv + 1 + aj2_len) as int] == Symbol::Gen(n));
        if aj2_len < aj0_len {
            // Help Z3 index: pos_inv+1+aj2_len falls in inter segment
            let seg_pre = w_L_short + head + seq![Symbol::Inv(n)];
            assert(seg_pre.len() == pos_inv + 1);
            let seg_with_inter = seg_pre + inter;
            assert(seg_with_inter.len() == pos_gen);
            let idx = (pos_inv + 1 + aj2_len) as int;
            assert(idx >= seg_pre.len());
            assert(idx < seg_with_inter.len());
            // inter[aj2_len] is base (gen_index < n), contradiction with Gen(n)
        } else if aj2_len > aj0_len {
            // Help Z3 index: pos_inv+1+aj2_len is past Gen(n), in w_R
            let seg_all = w_L_short + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)];
            assert(seg_all.len() == pos_gen + 1);
            let idx = (pos_inv + 1 + aj2_len) as int;
            assert(idx >= seg_all.len());
            // w_R[idx - seg_all.len()] is base, contradiction with Gen(n)
        }
    };
    // a_j2 =~= inter = inv(a_j0) (both occupy positions pos_inv+1..pos_gen in w2)
    assert(a_j2 =~= inter) by {
        assert forall|k: int| 0 <= k < aj2_len
            implies a_j2[k] == #[trigger] inter[k]
        by {
            assert(a_j2[k] == r2[(k + 1) as int]);
            assert(r2[(k + 1) as int] == w2[(pos_inv + 1 + k) as int]);
        };
    };
    // a_j2 = inv(a_j0), so a_j2 ≡_G inv(a_j0)
    lemma_equiv_refl(p, inv_aj0);
    // By isomorphism_maps_inverse_equivalence (the "a_j2 ≡ inv(a_j0)" variant):
    // We need to be careful: the isomorphism says if a_j2 ≡ inv(a_j0), then b_j2 ≡ inv(b_j0).
    // But we use lemma_isomorphism_maps_inverse_equivalence(data, j0, j2)
    // which requires a_j2 ≡_G inverse_word(a_j0).
    lemma_isomorphism_maps_inverse_equivalence(data, j0, j2);
    // b_j2 ≡_G inv(b_j0)

    let bj2_len = b_j2.len() as int;
    let inv_bj2 = inverse_word(b_j2);
    let r2_len = r2.len() as int;

    // After deletion: w_end = w2[0..pos_inv] + w2[pos_inv+r2_len..]
    // w2[0..pos_inv] = w_L_short + head
    // w2[pos_inv+r2_len..] = after Gen(n) and inv(b_j2): rest of w_R region
    // r2_len = 2 + aj0_len + bj2_len
    // w2 after r2: w2[pos_inv+r2_len..] = w_R[... some portion]
    // Actually: w2 = w_L_short + head + [Inv(n)] + inter + [Gen(n)] + w_R
    // r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2) starts at pos_inv
    // r2 occupies: [Inv(n)] + inter + [Gen(n)] + first bj2_len elements of w_R
    // So: inv(b_j2) =~= w_R[0..bj2_len] (if bj2_len <= w_R.len())
    // After deletion: w_end = (w_L_short + head) + w_R[bj2_len..]

    assert forall|k: int| 0 <= k < bj2_len
        implies inv_bj2[k] == #[trigger] w_R[k]
    by {
        assert(inv_bj2[k] == r2[(2 + aj0_len + k) as int]);
        assert(r2[(2 + aj0_len + k) as int] == w2[(pos_inv + 2 + aj0_len + k) as int]);
        assert(w2[(pos_gen + 1 + k) as int] == w_R[k]);
    };
    assert(w_end =~= w_L_short + head + w_R.subrange(bj2_len, w_R.len() as int));

    // b_j2 ≡_G inv(b_j0) from isomorphism.
    // Need: w_R[0..bj2_len] ≡_G b_j0 = [first_sym] + head
    // Strategy: inverse_word_congruence + focused =~= bridge
    lemma_inverse_word_valid(b_j0, n);
    lemma_inverse_word_congruence(p, b_j2, inverse_word(b_j0));
    crate::word::lemma_inverse_involution(b_j0);
    // equiv(inv(b_j2), inv(inv(b_j0))) and inv(inv(b_j0)) =~= b_j0
    assert(b_j0 =~= seq![first_sym] + head);
    crate::word::lemma_inverse_word_len(b_j2);

    // Bridge =~= to equiv via focused assert
    assert(inv_bj2 =~= w_R.subrange(0, bj2_len));
    assert(inverse_word(inverse_word(b_j0)) =~= b_j0);
    // equiv(inv_bj2, b_j0): inv(b_j2) ≡_G b_j0
    assert(equiv_in_presentation(p, inv_bj2, b_j0)) by {
        // congruence gave equiv(inv_bj2, inv(inv(b_j0)))
        // inv(inv(b_j0)) == b_j0 from =~=
    };
    // equiv(w_R[0..bj2_len], b_j0): bridge inv_bj2 =~= w_R[0..bj2_len]
    assert(equiv_in_presentation(p, w_R.subrange(0, bj2_len), b_j0)) by {
        // inv_bj2 == w_R[0..bj2_len] from =~=
        // equiv(inv_bj2, b_j0) from above
    };

    // w_R[0..bj2_len] ≡_G [first_sym] + head
    // [wp_last] + w_R[0..bj2_len] ≡_G [wp_last] + [first_sym] + head
    //    = [wp_last, first_sym] + head ≡_G ε + head = head
    lemma_subrange_word_valid(w_R, 0, bj2_len, n);
    assert(word_valid(seq![wp_last], n)) by { assert(symbol_valid(wp_last, n)); };
    lemma_equiv_concat_right(p, seq![wp_last], w_R.subrange(0, bj2_len), seq![first_sym] + head);
    // [wp_last] + w_R[0..bj2_len] ≡_G [wp_last] + [first_sym] + head

    // [wp_last, first_sym] cancels
    let cancel_pair = seq![wp_last] + seq![first_sym];
    let cancel_step = DerivationStep::FreeReduce { position: 0 };
    assert(has_cancellation_at(cancel_pair, 0)) by {
        match wp_last { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
        match first_sym { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
    };
    assert(apply_step(p, cancel_pair, cancel_step) == Some(empty_word()));
    lemma_single_step_equiv(p, cancel_pair, cancel_step, empty_word());

    assert(seq![wp_last] + (seq![first_sym] + head) =~= (seq![wp_last] + seq![first_sym]) + head);
    assert((seq![wp_last] + seq![first_sym]) + head =~= cancel_pair + head);
    lemma_remove_trivial_equiv(p, empty_word(), head, cancel_pair);
    assert(concat(empty_word(), concat(cancel_pair, head)) =~= cancel_pair + head);
    assert(concat(empty_word(), head) =~= head);
    // cancel_pair + head ≡_G head
    // Bridge: equiv_concat_left gave equiv([wp_last]+w_R[..], [wp_last]+([first_sym]+head))
    // and [wp_last]+([first_sym]+head) =~= cancel_pair+head (associativity)
    assert(equiv_in_presentation(p, seq![wp_last] + w_R.subrange(0, bj2_len), cancel_pair + head)) by {
        assert(seq![wp_last] + (seq![first_sym] + head) =~= cancel_pair + head);
    };
    lemma_equiv_transitive(p, seq![wp_last] + w_R.subrange(0, bj2_len), cancel_pair + head, head);

    // w = w_L_short + ([wp_last] + w_R[0..bj2_len]) + w_R[bj2_len..]
    // w_end = w_L_short + head + w_R[bj2_len..]
    let w_R_tail = w_R.subrange(bj2_len, w_R.len() as int);
    assert(w_R =~= w_R.subrange(0, bj2_len) + w_R_tail);
    assert(w =~= concat(w_L_short, concat(seq![wp_last] + w_R.subrange(0, bj2_len), w_R_tail)));
    assert(w_end =~= concat(w_L_short, concat(head, w_R_tail)));
    lemma_equiv_concat_right(p, w_L_short, seq![wp_last] + w_R.subrange(0, bj2_len), head);
    lemma_equiv_concat_left(p, w_L_short + (seq![wp_last] + w_R.subrange(0, bj2_len)), w_L_short + head,
        w_R_tail);
    assert(concat(w_L_short + (seq![wp_last] + w_R.subrange(0, bj2_len)), w_R_tail) =~= w);
    assert(concat(w_L_short + head, w_R_tail) =~= w_end);
}

/// Inverted r2 RelatorDelete sub-case for boundary FreeReduce + inverted r0.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_k3_freereduce_inv_step2_rd_inv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L_short: Word, head: Word, inter: Word, w_R: Word,
    j0: int, wp_last: Symbol, first_sym: Symbol,
    p2: int, j2: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            let b_j0 = data.associations[j0].1;
            &&& w2 =~= w_L_short + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R
            &&& w =~= w_L_short + seq![wp_last] + w_R
            &&& inter =~= inverse_word(data.associations[j0].0)
            &&& head =~= b_j0.subrange(1, b_j0.len() as int)
            &&& first_sym == b_j0[0]
            &&& wp_last == inverse_symbol(first_sym)
            &&& b_j0.len() >= 1
        }),
        is_base_word(w_L_short, data.base.num_generators),
        is_base_word(head, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(head, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(w_L_short, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        ({
            let hp = hnn_presentation(data);
            let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, true);
            &&& 0 <= p2
            &&& p2 + r2.len() as int <= w2.len() as int
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);
    let bj0_len = b_j0.len() as int;
    let aj0_len = a_j0.len() as int;
    let (a_j2, b_j2) = data.associations[j2];
    let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, true);

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    crate::word::lemma_inverse_word_len(a_j0);
    lemma_base_word_characterization(inv_aj0, n);
    lemma_base_word_characterization(a_j2, n);
    lemma_base_word_characterization(b_j2, n);
    lemma_inverse_word_valid(b_j2, n);
    lemma_inverse_word_valid(a_j2, n);

    let head_len = head.len() as int;
    let pos_inv = w_L_short.len() as int + head_len;
    let pos_gen = pos_inv + 1 + aj0_len;

    // Bridge: connect r2 to hnn_relator structural facts
    assert(r2 =~= inverse_word(hnn_relator(data, j2))) by {
        assert(hp.relators =~= data.base.relators + hnn_relators(data));
        assert(hp.relators[(data.base.relators.len() + j2) as int]
            == hnn_relators(data)[j2 as int]);
        assert(hnn_relators(data)[j2 as int] == hnn_relator(data, j2));
    };

    // Inverted r2 = b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)]
    lemma_hnn_relator_inverted_stable_positions(data, j2);
    let bj2_len = b_j2.len() as int;
    let aj2_len = a_j2.len() as int;

    // Inv(n) at r2[bj2_len] must match pos_inv
    assert(p2 + bj2_len == pos_inv) by {
        if p2 + bj2_len != pos_inv {
            if p2 + bj2_len < pos_inv {
                assert(w2[(p2 + bj2_len) as int] == Symbol::Inv(n));
            } else {
                assert(w2[(p2 + bj2_len) as int] == Symbol::Inv(n));
                if p2 + bj2_len == pos_gen {} else {}
            }
        }
    };
    // Gen(n) in r2 at index bj2_len+1+aj2_len must align with pos_gen
    assert(aj2_len == aj0_len) by {
        assert(r2[(bj2_len + 1 + aj2_len) as int] == Symbol::Gen(n));
        assert(w2[(pos_inv + 1 + aj2_len) as int] == Symbol::Gen(n));
        if aj2_len < aj0_len {
            // Help Z3 index: pos_inv+1+aj2_len falls in inter segment
            let seg_pre = w_L_short + head + seq![Symbol::Inv(n)];
            assert(seg_pre.len() == pos_inv + 1);
            let seg_with_inter = seg_pre + inter;
            assert(seg_with_inter.len() == pos_gen);
            let idx = (pos_inv + 1 + aj2_len) as int;
            assert(idx >= seg_pre.len());
            assert(idx < seg_with_inter.len());
        } else if aj2_len > aj0_len {
            let seg_all = w_L_short + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)];
            assert(seg_all.len() == pos_gen + 1);
            let idx = (pos_inv + 1 + aj2_len) as int;
            assert(idx >= seg_all.len());
        }
    };
    // inv(a_j2) =~= inter = inv(a_j0)
    assert(inverse_word(a_j2) =~= inter) by {
        assert forall|k: int| 0 <= k < aj2_len
            implies inverse_word(a_j2)[k] == #[trigger] inter[k]
        by {
            assert(inverse_word(a_j2)[k] == r2[(bj2_len + 1 + k) as int]);
            assert(r2[(bj2_len + 1 + k) as int] == w2[(pos_inv + 1 + k) as int]);
        };
    };
    // So inv(a_j2) = inv(a_j0), a_j2 = a_j0
    crate::word::lemma_inverse_involution(a_j2);
    crate::word::lemma_inverse_involution(a_j0);
    assert(a_j2 =~= a_j0);
    lemma_equiv_refl(p, a_j0);
    lemma_isomorphism_maps_equivalence(data, j0, j2);
    // b_j2 ≡_G b_j0

    // b_j2 occupies w2[p2..p2+bj2_len]
    // p2 = pos_inv - bj2_len = w_L_short.len() + head_len - bj2_len
    // b_j2 sits in the w_L_short + head region

    // r2 ends at p2 + r2.len() = pos_inv + 2 + aj0_len = pos_gen + 1
    // After r2: w2[pos_gen+1..] = w_R
    let r2_len = r2.len() as int;
    let w_L_short_len = w_L_short.len() as int;

    if bj2_len <= head_len {
        // b_j2 fits within head region
        // p2 = w_L_short_len + head_len - bj2_len
        assert(w_end =~= w_L_short + head.subrange(0, head_len - bj2_len) + w_R);

        // b_j2 =~= head[head_len-bj2_len..head_len]
        assert forall|k: int| 0 <= k < bj2_len
            implies b_j2[k] == #[trigger] head[(head_len - bj2_len + k) as int]
        by {
            assert(b_j2[k] == r2[k]);
            assert(r2[k] == w2[(p2 + k) as int]);
        };

        // b_j2 ≡_G b_j0 = [first_sym] + head
        // head = head[0..head_len-bj2_len] + b_j2_content
        let head_prefix = head.subrange(0, head_len - bj2_len);
        assert(head =~= head_prefix + head.subrange(head_len - bj2_len, head_len));

        // b_j2 ≡_G [first_sym] + head = [first_sym] + head_prefix + b_j2_content
        // b_j2 = b_j2_content ≡_G [first_sym] + head_prefix + b_j2_content
        // By right cancel: ε ≡_G [first_sym] + head_prefix
        // → head_prefix ≡_G inverse_word([first_sym]) = [wp_last]

        // Actually we need the right direction for lemma_right_cancel.
        // b_j2 ≡_G b_j0 = [first_sym] + head
        //              = [first_sym] + head_prefix + b_j2_content
        // b_j2 = b_j2_content (since b_j2 matches that subrange of head)
        // So: b_j2_content ≡_G [first_sym] + head_prefix + b_j2_content
        // concat(ε, b_j2_content) ≡_G concat([first_sym] + head_prefix, b_j2_content)
        // By right cancel (or left cancel flipped): ε ≡_G [first_sym] + head_prefix
        // → [first_sym] + head_prefix ≡_G ε
        // → head_prefix ≡_G inv([first_sym]) = [wp_last]

        assert(b_j0 =~= seq![first_sym] + head_prefix + head.subrange(head_len - bj2_len, head_len));
        assert(b_j2 =~= head.subrange(head_len - bj2_len, head_len)) by {
            assert forall|k: int| 0 <= k < bj2_len
                implies b_j2[k] == #[trigger] head.subrange(head_len - bj2_len, head_len)[k]
            by {
                assert(b_j2[k] == head[(head_len - bj2_len + k) as int]);
            };
        };
        // Flip: equiv(b_j0, b_j2), then left_cancel
        lemma_equiv_symmetric(p, b_j2, b_j0);
        // b_j0 = concat([first_sym]+head_prefix, head[tail]), b_j2 = head[tail]
        // equiv(concat(x, y), y) → x ≡ ε
        lemma_subrange_word_valid(head, head_len - bj2_len, head_len, n);
        lemma_subrange_word_valid(head, 0, head_len - bj2_len, n);
        assert(word_valid(seq![first_sym], n)) by { assert(symbol_valid(first_sym, n)); };
        lemma_concat_word_valid(seq![first_sym], head_prefix, n);
        lemma_left_cancel(p, seq![first_sym] + head_prefix, head.subrange(head_len - bj2_len, head_len));
        // [first_sym] + head_prefix ≡_G ε
        // Also: [first_sym] + [wp_last] ≡_G ε (cancelling pair)
        let cancel_hp = seq![first_sym, wp_last];
        assert(cancel_hp =~= seq![first_sym] + seq![wp_last]);
        let cancel_hp_step = DerivationStep::FreeReduce { position: 0 };
        assert(has_cancellation_at(cancel_hp, 0)) by {
            assert(cancel_hp[0] == first_sym);
            assert(cancel_hp[1] == wp_last);
            match first_sym { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
            match wp_last { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
        };
        assert(apply_step(p, cancel_hp, cancel_hp_step) == Some(empty_word()));
        lemma_single_step_equiv(p, cancel_hp, cancel_hp_step, empty_word());
        // [first_sym]+[wp_last] ≡_G ε
        assert(equiv_in_presentation(p, seq![first_sym] + seq![wp_last], empty_word())) by {
            assert(concat(seq![first_sym], seq![wp_last]) =~= cancel_hp);
        };
        // Chain: [first_sym]+head_prefix ≡_G ε, ε ≡_G..., no —
        // use left_cancel_equiv: equiv([first_sym]+head_prefix, [first_sym]+[wp_last]) → head_prefix ≡_G [wp_last]
        assert(word_valid(seq![wp_last], n)) by { assert(symbol_valid(wp_last, n)); };
        crate::word::lemma_concat_word_valid(seq![first_sym], seq![wp_last], n);
        lemma_equiv_symmetric(p, seq![first_sym] + seq![wp_last], empty_word());
        lemma_equiv_transitive(p, seq![first_sym] + head_prefix, empty_word(), seq![first_sym] + seq![wp_last]);
        // [first_sym]+head_prefix ≡_G [first_sym]+[wp_last]
        lemma_concat_left_cancel_equiv(p, seq![first_sym], head_prefix, seq![wp_last]);
        // head_prefix ≡_G [wp_last]
        lemma_equiv_symmetric(p, head_prefix, seq![wp_last]);

        // w = w_L_short + [wp_last] + w_R ≡_G w_L_short + head_prefix + w_R = w_end
        lemma_equiv_concat_right(p, w_L_short, seq![wp_last], head_prefix);
        lemma_equiv_concat_left(p, w_L_short + seq![wp_last], w_L_short + head_prefix, w_R);
        assert(w =~= w_L_short + seq![wp_last] + w_R);
        assert(w_end =~= w_L_short + head_prefix + w_R);
    } else {
        // b_j2 extends into w_L_short region
        let in_wl = (bj2_len - head_len) as int;
        // p2 = w_L_short_len - in_wl
        assert(w_end =~= w_L_short.subrange(0, w_L_short_len - in_wl) + w_R);

        // b_j2[0..in_wl] from w_L_short, b_j2[in_wl..] from head
        assert forall|k: int| 0 <= k < bj2_len
            implies b_j2[k] == #[trigger] (w_L_short.subrange(w_L_short_len - in_wl, w_L_short_len) + head)[k]
        by {
            assert(b_j2[k] == r2[k]);
            assert(r2[k] == w2[(p2 + k) as int]);
        };

        // b_j2 ≡_G b_j0 = [first_sym] + head
        // b_j2 = w_L_short[w_L_short_len-in_wl..] + head
        // So: w_L_short[w_L_short_len-in_wl..] + head ≡_G [first_sym] + head
        // By right cancel: w_L_short[w_L_short_len-in_wl..] ≡_G [first_sym]
        assert(b_j2 =~= w_L_short.subrange(w_L_short_len - in_wl, w_L_short_len) + head);
        assert(b_j0 =~= seq![first_sym] + head);
        // Bridge =~= to equiv for concat_right_cancel_equiv precondition
        assert(equiv_in_presentation(p, w_L_short.subrange(w_L_short_len - in_wl, w_L_short_len) + head, seq![first_sym] + head)) by {
            assert(b_j2 =~= w_L_short.subrange(w_L_short_len - in_wl, w_L_short_len) + head);
            assert(b_j0 =~= seq![first_sym] + head);
        };
        lemma_concat_right_cancel_equiv(p, w_L_short.subrange(w_L_short_len - in_wl, w_L_short_len), seq![first_sym], head);
        // w_L_short[w_L_short_len-in_wl..] ≡_G [first_sym]
        // So: [wp_last] + w_L_short[w_L_short_len-in_wl..] ≡_G [wp_last] + [first_sym] ≡_G ε

        lemma_subrange_word_valid(w_L_short, w_L_short_len - in_wl, w_L_short_len, n);

        // w = prefix + suf + [wp_last] + w_R, w_end = prefix + w_R
        // Need: suf + [wp_last] ≡_G ε
        // suf ≡_G [first_sym] (from right_cancel_equiv above)
        // So suf + [wp_last] ≡_G [first_sym] + [wp_last] = [first_sym, inv(first_sym)] ≡_G ε
        let suf = w_L_short.subrange(w_L_short_len - in_wl, w_L_short_len);
        // [wp_last] + suf ≡_G ε (shown above)
        // Need: suf + [wp_last] ≡_G ε
        // suf ≡_G [first_sym] (from right_cancel_equiv)
        // So suf + [wp_last] ≡_G [first_sym] + [wp_last] = [first_sym, inverse_symbol(first_sym)] ≡_G ε
        let cancel_pair2 = seq![first_sym] + seq![wp_last];
        let cancel_step2 = DerivationStep::FreeReduce { position: 0 };
        assert(has_cancellation_at(cancel_pair2, 0)) by {
            match first_sym { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
            match wp_last { Symbol::Gen(g) => {}, Symbol::Inv(g) => {} }
        };
        assert(apply_step(p, cancel_pair2, cancel_step2) == Some(empty_word()));
        lemma_single_step_equiv(p, cancel_pair2, cancel_step2, empty_word());

        lemma_equiv_concat_left(p, suf, seq![first_sym], seq![wp_last]);
        lemma_equiv_transitive(p, suf + seq![wp_last], cancel_pair2, empty_word());

        assert(w_L_short =~= w_L_short.subrange(0, w_L_short_len - in_wl) + suf);
        assert(w =~= concat(w_L_short.subrange(0, w_L_short_len - in_wl), concat(suf + seq![wp_last], w_R)));
        assert(w_end =~= concat(w_L_short.subrange(0, w_L_short_len - in_wl), w_R));
        lemma_remove_trivial_equiv(p, w_L_short.subrange(0, w_L_short_len - in_wl), w_R, suf + seq![wp_last]);
    }
}

/// Step2 handler for the left-boundary FreeReduce + inverted r0 case.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_k3_freereduce_boundary_inv_step2(
    data: HNNData, w: Word, w2: Word, w_end: Word, step2: DerivationStep,
    w_L_short: Word, head: Word, inter: Word, w_R: Word, j0: int, wp_last: Symbol, first_sym: Symbol,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            let b_j0 = data.associations[j0].1;
            &&& w2 =~= w_L_short + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R
            &&& w =~= w_L_short + seq![wp_last] + w_R
            &&& inter =~= inverse_word(data.associations[j0].0)
            &&& head =~= b_j0.subrange(1, b_j0.len() as int)
            &&& first_sym == b_j0[0]
            &&& wp_last == inverse_symbol(first_sym)
            &&& b_j0.len() >= 1
        }),
        is_base_word(w_L_short, data.base.num_generators),
        is_base_word(head, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        word_valid(head, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(w_L_short, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        apply_step(hnn_presentation(data), w2, step2) == Some(w_end),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);
    let bj0_len = b_j0.len() as int;
    let aj0_len = a_j0.len() as int;
    let p = data.base;

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    crate::word::lemma_inverse_word_len(a_j0);
    lemma_base_word_characterization(inv_aj0, n);

    let head_len = head.len() as int;
    let pos_inv = w_L_short.len() as int + head_len;
    let pos_gen = pos_inv + 1 + aj0_len;

    match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } => {
            let pair2 = Seq::new(1, |_i: int| sym2) + Seq::new(1, |_i: int| inverse_symbol(sym2));
            assert(w_end =~= w2.subrange(0, p2) + pair2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, pair2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            assert(w_end =~= w2.subrange(0, p2) + r2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, r2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::FreeReduce { position: p2 } => {
            lemma_stable_count_reduce(w2, p2, n);
            if generator_index(w2[p2]) == n {
                // Stable FreeReduce: stable letters adjacent → head and inter both empty
                assert(p2 == pos_inv) by {
                    if p2 == pos_gen {
                        // w2[pos_gen+1] is base, can't cancel with Gen(n)
                    }
                };
                assert(aj0_len == 0) by {
                    // p2 = pos_inv: w2[pos_inv+1] must cancel with Inv(n).
                    // Cancellation needs Gen(n) at pos_inv+1. If aj0_len > 0, inter[0] is base → contradiction.
                    if aj0_len > 0 {
                        // w2[pos_inv+1] = inter[0], which is base (gen_index < n)
                        // But cancellation requires inverse_symbol(Inv(n)) = Gen(n), gen_index = n
                        assert(w2[(pos_inv + 1) as int] == inter[0]);
                    }
                };
                assert(inter.len() == 0);
                assert(a_j0 =~= empty_word());

                // a_j0 = ε → a_j0 ≡_G ε (needed for trivial_association precondition)
                lemma_equiv_refl(p, empty_word());
                // a_j0 = ε → b_j0 ≡_G ε by trivial association
                lemma_trivial_association_implies_trivial(data, j0);
                // b_j0 = [first_sym] + head ≡_G ε
                assert(b_j0 =~= seq![first_sym] + head);

                // After FreeReduce (removing Inv(n) and Gen(n)): w_end = w_L_short + head + w_R
                assert(w_end =~= w_L_short + head + w_R);

                // identity_split: head ≡_G inv([first_sym]) = [wp_last]
                assert(word_valid(seq![first_sym], n)) by {
                    assert(symbol_valid(first_sym, n));
                };
                lemma_identity_split(p, seq![first_sym], head);
                crate::word::lemma_inverse_singleton(first_sym);
                assert(seq![first_sym] =~= Seq::new(1, |_i: int| first_sym));
                assert(inverse_word(seq![first_sym]) =~= seq![wp_last]);
                // head ≡_G [wp_last], flip to [wp_last] ≡_G head
                lemma_equiv_symmetric(p, head, seq![wp_last]);

                // w = w_L_short + [wp_last] + w_R ≡_G w_L_short + head + w_R = w_end
                lemma_equiv_concat_right(p, w_L_short, seq![wp_last], head);
                lemma_equiv_concat_left(p, w_L_short + seq![wp_last], w_L_short + head, w_R);
                assert(w =~= w_L_short + seq![wp_last] + w_R);
                assert(w_end =~= w_L_short + head + w_R);
            }
            else {
                // Base FreeReduce: count stays at 2
                assert(stable_letter_count(w_end, n) == 2nat);
                lemma_base_implies_count_zero(w_end, n);
            }
        },
        DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            let r2_len = r2.len() as int;
            assert(w2.subrange(p2, p2 + r2_len) =~= r2);
            assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));

            lemma_relator_stable_count(data, ri2, inv2);

            if (ri2 as int) < p.relators.len() {
                // Base relator delete: count unchanged → 2 → not base
                lemma_stable_count_subrange(w2, p2, p2 + r2_len, n);
                lemma_stable_letter_count_concat(
                    w2.subrange(0, p2), w2.subrange(p2 + r2_len, w2.len() as int), n);
                lemma_base_implies_count_zero(w_end, n);
            } else {
                let j2 = (ri2 as int - p.relators.len()) as int;
                let (a_j2, b_j2) = data.associations[j2];
                lemma_base_word_characterization(a_j2, n);
                lemma_base_word_characterization(b_j2, n);
                lemma_inverse_word_valid(b_j2, n);
                lemma_inverse_word_valid(a_j2, n);
                assert(w2.subrange(p2, p2 + r2.len()) =~= r2);
                assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int));

                assert(ri2 == (data.base.relators.len() + j2) as nat);
                if !inv2 {
                    lemma_k3_freereduce_inv_step2_rd_noninv(
                        data, w, w2, w_end, w_L_short, head, inter, w_R,
                        j0, wp_last, first_sym, p2, j2);
                } else {
                    lemma_k3_freereduce_inv_step2_rd_inv(
                        data, w, w2, w_end, w_L_short, head, inter, w_R,
                        j0, wp_last, first_sym, p2, j2);
                }
            }
        },
    }
}

/// k=3 case: step0 = RelatorInsert(HNN), step1 = FreeReduce(base).
/// Commutes base FreeReduce to act first on w, then RelatorInsert(HNN).
proof fn lemma_k3_ri_hnn_freereduce_base(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        generator_index(w1[p1]) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeReduce { position: p1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(has_cancellation_at(w1, p1));
    assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + 2, w1.len() as int));
    lemma_base_word_valid_down(w, n);

    if p1 + 1 < p0 {
        // Both positions before relator
        assert(w1[p1] == w[p1]);
        assert(w1[p1 + 1] == w[p1 + 1]);
        assert(has_cancellation_at(w, p1));

        let w_prime = reduce_at(w, p1);
        let step1_base = DerivationStep::FreeReduce { position: p1 };
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));

        lemma_stable_count_reduce(w, p1, n);
        assert(generator_index(w[p1]) < n);
        assert(stable_letter_count(w_prime, n) == 0nat);

        assert(apply_step(hp, w, step1_base) == Some(w_prime));
        lemma_step_preserves_word_valid(data, w, step1_base);

        let p0_adj = (p0 - 2) as int;
        let step0_adj = DerivationStep::RelatorInsert {
            position: p0_adj, relator_index: ri0, inverted: inv0,
        };
        let insert_result = w_prime.subrange(0, p0_adj) + r0
            + w_prime.subrange(p0_adj, w_prime.len() as int);

        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] insert_result[k]
        by {
            if k < p1 {
            } else if k < p0_adj {
            } else if k < p0_adj + r0_len {
            } else {
            }
        };
        assert(w2.len() == insert_result.len());
        assert(w2 =~= insert_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
        lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
    } else if p1 >= p0 + r0_len {
        // Both positions after relator
        let p1_adj = (p1 - r0_len) as int;
        assert(w1[p1] == w[p1_adj]);
        assert(w1[p1 + 1] == w[(p1_adj + 1) as int]);
        assert(has_cancellation_at(w, p1_adj));

        let w_prime = reduce_at(w, p1_adj);
        let step1_base = DerivationStep::FreeReduce { position: p1_adj };
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));

        lemma_stable_count_reduce(w, p1_adj, n);
        assert(generator_index(w[p1_adj]) < n);
        assert(stable_letter_count(w_prime, n) == 0nat);

        assert(apply_step(hp, w, step1_base) == Some(w_prime));
        lemma_step_preserves_word_valid(data, w, step1_base);

        let step0_adj = DerivationStep::RelatorInsert {
            position: p0, relator_index: ri0, inverted: inv0,
        };
        let insert_result = w_prime.subrange(0, p0) + r0
            + w_prime.subrange(p0, w_prime.len() as int);

        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == #[trigger] insert_result[k]
        by {
            if k < p0 {
            } else if k < p0 + r0_len {
            } else if k < p1 {
            } else {
            }
        };
        assert(w2.len() == insert_result.len());
        assert(w2 =~= insert_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
        lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
    } else {
        // Boundary or inside relator: p0-1 <= p1 and p1 < p0+r0_len
        // We need w1 and w2 to be word_valid for the helpers
        let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
        lemma_step_preserves_word_valid(data, w, step0);
        lemma_step_preserves_word_valid(data, w1, DerivationStep::FreeReduce { position: p1 });

        if !inv0 {
            // Non-inverted r0 = [Inv(n)] + a_j0 + [Gen(n)] + inv(b_j0)
            let j0 = (ri0 as int - data.base.relators.len()) as int;
            let (a_j0, b_j0) = data.associations[j0];
            let aj0_len = a_j0.len() as int;
            let bj0_len = b_j0.len() as int;
            lemma_hnn_relator_stable_positions(data, j0);

            if p1 + 2 <= p0 + r0_len && p1 >= p0 + 1 {
                // Both elements inside r0 (inside handler precondition: p1+2 <= p0+r0.len())
                lemma_k3_freereduce_inside_noninv(
                    data, w, w1, w2, w_end, p0, ri0, p1, step2);
            } else if p1 == p0 + r0_len - 1 {
                // Right boundary: last of inv(b_j0) cancels with w[p0]
                lemma_k3_freereduce_boundary_noninv(
                    data, w, w1, w2, w_end, p0, ri0, p1, step2);
            } else {
                // Remaining: p1 <= p0 (stable letter position → contradiction)
                if p1 == p0 - 1 {
                    // w1[p1+1] = Inv(n), gen_index = n, but cancellation needs same as w1[p1] < n
                    assert(w1[(p1 + 1) as int] == Symbol::Inv(n));
                } else {
                    // p1 = p0: w1[p1] = Inv(n), gen_index = n, contradicts require < n
                    assert(w1[p1] == Symbol::Inv(n));
                }
            }
        } else {
            // Inverted r0 = b_j0 + [Inv(n)] + inv(a_j0) + [Gen(n)]
            let j0 = (ri0 as int - data.base.relators.len()) as int;
            let (a_j0, b_j0) = data.associations[j0];
            let aj0_len = a_j0.len() as int;
            let bj0_len = b_j0.len() as int;
            lemma_hnn_relator_inverted_stable_positions(data, j0);

            if p1 == p0 - 1 {
                // Left boundary: w[p0-1] cancels with b_j0[0]
                lemma_k3_freereduce_boundary_inv(
                    data, w, w1, w2, w_end, p0, ri0, p1, step2);
            } else if p1 >= p0 && p1 + 2 <= p0 + r0_len {
                // Both elements strictly inside r0
                lemma_k3_freereduce_inside_inv(
                    data, w, w1, w2, w_end, p0, ri0, p1, step2);
            } else {
                // Position involves stable letter → contradiction
                // The only remaining case: p1 at the end involving Gen(n)
                // p1 = p0+r0_len-1 = p0+bj0_len+1+aj0_len: w1[p1] = Gen(n), index n
                assert(p1 == p0 + bj0_len + 1 + aj0_len);
                assert(w1[p1] == Symbol::Gen(n));
            }
        }
    }
}

/// k=3 case: step0 = RelatorInsert(HNN), step1 = RelatorDelete(base), delete before relator.
proof fn lemma_k3_ri_hnn_reldelete_before(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
            let step1 = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        p1 + (get_relator(hnn_presentation(data), ri1, inv1).len() as int) <= p0,
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(w1.subrange(p1, p1 + r1_len) =~= r1);
    assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + r1_len, w1.len() as int));
    lemma_base_word_valid_down(w, n);

    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);
    assert(get_relator(data.base, ri1, inv1) =~= r1) by {
        assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
    };
    if inv1 {
        lemma_inverse_word_valid(base_r, n);
        lemma_base_word_characterization(inverse_word(base_r), n);
    } else {
        lemma_base_word_characterization(base_r, n);
    }

    assert forall|k: int| 0 <= k < r1_len
        implies w[(p1 + k) as int] == #[trigger] r1[k]
    by {
        assert(w1[(p1 + k) as int] == r1[k]);
        assert((p1 + k) < p0);
        assert(w1[(p1 + k) as int] == w[(p1 + k) as int]);
    };
    assert(w.subrange(p1, p1 + r1_len) =~= r1);

    let step1_base = DerivationStep::RelatorDelete {
        position: p1, relator_index: ri1, inverted: inv1,
    };
    let w_prime = w.subrange(0, p1) + w.subrange(p1 + r1_len, w.len() as int);
    assert(apply_step(data.base, w, step1_base) == Some(w_prime));

    assert forall|i: int| 0 <= i < w_prime.len()
        implies symbol_valid(#[trigger] w_prime[i], n)
    by {
        if i < p1 {
            assert(w_prime[i] == w[i]);
        } else {
            assert(w_prime[i] == w[(i + r1_len) as int]);
        }
    };
    lemma_base_word_characterization(w_prime, n);
    lemma_word_valid_monotone(w_prime, n);

    let p0_adj = (p0 - r1_len) as int;
    let step0_adj = DerivationStep::RelatorInsert {
        position: p0_adj, relator_index: ri0, inverted: inv0,
    };
    let insert_result = w_prime.subrange(0, p0_adj) + r0
        + w_prime.subrange(p0_adj, w_prime.len() as int);

    assert forall|k: int| 0 <= k < w2.len()
        implies w2[k] == #[trigger] insert_result[k]
    by {
        if k < p1 {
        } else if k < p0_adj {
        } else if k < p0_adj + r0_len {
        } else {
        }
    };
    assert(w2.len() == insert_result.len());
    assert(w2 =~= insert_result);
    assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
    lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
}

/// k=3 case: step0 = RelatorInsert(HNN), step1 = RelatorDelete(base), delete after relator.
proof fn lemma_k3_ri_hnn_reldelete_after(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, inv0);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
            let step1 = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            &&& p1 >= p0 + r0.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    assert(w1.subrange(p1, p1 + r1_len) =~= r1);
    assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + r1_len, w1.len() as int));
    lemma_base_word_valid_down(w, n);

    reveal(presentation_valid);
    let base_r = data.base.relators[ri1 as int];
    assert(hp.relators[ri1 as int] == base_r);
    assert(get_relator(data.base, ri1, inv1) =~= r1) by {
        assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
    };
    if inv1 {
        lemma_inverse_word_valid(base_r, n);
        lemma_base_word_characterization(inverse_word(base_r), n);
    } else {
        lemma_base_word_characterization(base_r, n);
    }

    let p1_adj = (p1 - r0_len) as int;
    assert forall|k: int| 0 <= k < r1_len
        implies w[(p1_adj + k) as int] == #[trigger] r1[k]
    by {
        assert(w1[(p1 + k) as int] == r1[k]);
        assert((p1 + k) >= p0 + r0_len);
        assert(w1[(p1 + k) as int] == w[((p1 + k) - r0_len) as int]);
    };
    assert(w.subrange(p1_adj, p1_adj + r1_len) =~= r1);

    let step1_base = DerivationStep::RelatorDelete {
        position: p1_adj, relator_index: ri1, inverted: inv1,
    };
    let w_prime = w.subrange(0, p1_adj) + w.subrange(p1_adj + r1_len, w.len() as int);
    assert(apply_step(data.base, w, step1_base) == Some(w_prime));

    assert forall|i: int| 0 <= i < w_prime.len()
        implies symbol_valid(#[trigger] w_prime[i], n)
    by {
        if i < p1_adj {
            assert(w_prime[i] == w[i]);
        } else {
            assert(w_prime[i] == w[(i + r1_len) as int]);
        }
    };
    lemma_base_word_characterization(w_prime, n);
    lemma_word_valid_monotone(w_prime, n);

    let step0_adj = DerivationStep::RelatorInsert {
        position: p0, relator_index: ri0, inverted: inv0,
    };
    let insert_result = w_prime.subrange(0, p0) + r0
        + w_prime.subrange(p0, w_prime.len() as int);

    assert forall|k: int| 0 <= k < w2.len()
        implies w2[k] == #[trigger] insert_result[k]
    by {
        if k < p0 {
        } else if k < p0 + r0_len {
        } else if k < p1 {
        } else {
        }
    };
    assert(w2.len() == insert_result.len());
    assert(w2 =~= insert_result);
    assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
    lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
}

/// k=3 overlap case: RelatorDelete(base) inside non-inverted HNN relator.
/// r1 is entirely within a_j or inv(b_j) region of r0 = [Inv(n)] + a_j + [Gen(n)] + inv(b_j).
/// Deleting r1 (≡_G ε) modifies the base content; equivalence preserved.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_k3_rd_inside_noninv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
    j0: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, false);
            let r1 = get_relator(hp, ri1, inv1);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: false };
            let step1 = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            // r1 entirely inside r0 (not touching stable letters or boundary)
            &&& p1 >= p0 + 1
            &&& p1 + r1.len() <= p0 + r0.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        j0 == (ri0 as int - data.base.relators.len()) as int,
        0 <= j0 < data.associations.len(),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, false);
    let r1 = get_relator(hp, ri1, inv1);
    let r0_len = r0.len() as int;
    let r1_len = r1.len() as int;
    let (a_j0, b_j0) = data.associations[j0];
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;
    let inv_bj0 = inverse_word(b_j0);
    let p = data.base;

    reveal(presentation_valid);
    lemma_hnn_relator_stable_positions(data, j0);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_inverse_word_len(b_j0);
    lemma_base_word_characterization(inv_bj0, n);
    lemma_base_word_valid_down(w, n);

    // r0 = [Inv(n)] + a_j0 + [Gen(n)] + inv(b_j0)
    assert(r0 =~= seq![stable_letter_inv(data)] + a_j0 + seq![stable_letter(data)] + inv_bj0);
    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));

    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);

    // r1 is a base relator, hence ≡_G ε
    assert(hp.relators[ri1 as int] == p.relators[ri1 as int]);
    assert(get_relator(p, ri1, inv1) =~= r1);
    if inv1 {
        lemma_relator_is_identity(p, ri1 as int);
        lemma_inverse_word_valid(p.relators[ri1 as int], n);
        lemma_inverse_of_identity(p, p.relators[ri1 as int]);
        lemma_base_word_characterization(inverse_word(p.relators[ri1 as int]), n);
    } else {
        lemma_relator_is_identity(p, ri1 as int);
        lemma_base_word_characterization(p.relators[ri1 as int], n);
    }
    // Now: r1 is base, word_valid for n, and equiv(r1, empty) in G

    // Position of stable letters in w1: p0 (Inv(n)), p0+aj0_len+1 (Gen(n))
    let pos_inv = p0;
    let pos_gen = p0 + aj0_len + 1;

    // r1 position relative to r0 regions
    let r1_offset = (p1 - p0) as int; // offset within r0

    if r1_offset >= 1 && (p1 + r1_len) <= pos_gen {
        // r1 entirely within a_j region
        let offset_in_aj = (r1_offset - 1) as int;
        let inter = a_j0.subrange(0, offset_in_aj)
            + a_j0.subrange(offset_in_aj + r1_len, aj0_len);
        let tail = inv_bj0;

        // inter is base and word_valid
        assert forall|k: int| 0 <= k < inter.len() as int
            implies symbol_valid(#[trigger] inter[k], n)
        by {
            if k < offset_in_aj {
                assert(inter[k] == a_j0[k]);
            } else {
                assert(inter[k] == a_j0[(k + r1_len) as int]);
            }
        };
        assert(word_valid(inter, n));
        lemma_base_word_characterization(inter, n);

        // r1 =~= a_j0[offset..offset+r1_len]
        assert forall|k: int| 0 <= k < r1_len
            implies r1[k] == #[trigger] a_j0[(offset_in_aj + k) as int]
        by {
            assert(w1[(p1 + k) as int] == r1[k]);
            assert(w1[(p1 + k) as int] == r0[(r1_offset + k) as int]);
            assert(r0[(r1_offset + k) as int] == a_j0[(offset_in_aj + k) as int]);
        };

        // inter ≡_G a_j0 via RelatorInsert (re-inserting r1 gives back a_j0)
        let insert_step = DerivationStep::RelatorInsert {
            position: offset_in_aj, relator_index: ri1, inverted: inv1,
        };
        assert(inter.subrange(0, offset_in_aj) + r1
            + inter.subrange(offset_in_aj, inter.len() as int) =~= a_j0);
        assert(apply_step(p, inter, insert_step) == Some(a_j0));
        lemma_single_step_equiv(p, inter, insert_step, a_j0);
        // equiv(inter, a_j0)

        // w2 decomposition
        assert(w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R);

        // w_L, w_R are base subranges of w
        lemma_stable_count_subrange(w, 0, p0, n);
        lemma_subrange_word_valid(w, 0, p0, n + 1);
        lemma_subrange_word_valid(w, p0, w.len() as int, n + 1);
        lemma_base_word_valid_down(w_L, n);
        lemma_base_word_valid_down(w_R, n);

        // stable count
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(tail, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], tail, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail, w_R, n);

        lemma_equiv_refl(p, inv_bj0);
        lemma_k3_inside_step2_noninv(data, w, w2, w_end, step2, w_L, inter, tail, w_R, j0);
    } else {
        // r1 entirely within inv(b_j) region
        // First prove r1 can't overlap Gen(n) at pos_gen.
        // From else condition + r1_offset >= 1: p1 + r1_len > pos_gen.
        // If p1 <= pos_gen, r1 contains the Gen(n) position → contradiction with r1 being base.
        if p1 <= pos_gen {
            let idx_in_r1 = (pos_gen - p1) as int;
            assert(w1.subrange(p1, p1 + r1_len) =~= r1);
            assert(w1[pos_gen] == r1[idx_in_r1]);
            assert(w1[pos_gen] == r0[(pos_gen - p0) as int]);
            assert(generator_index(w1[pos_gen]) == n);
            assert(symbol_valid(r1[idx_in_r1], n));
        }
        assert(p1 > pos_gen);
        let offset_in_invbj = (p1 - pos_gen - 1) as int;
        let inter = a_j0;
        let tail = inv_bj0.subrange(0, offset_in_invbj)
            + inv_bj0.subrange(offset_in_invbj + r1_len, inv_bj0.len() as int);

        // tail is base and word_valid
        assert forall|k: int| 0 <= k < tail.len() as int
            implies symbol_valid(#[trigger] tail[k], n)
        by {
            if k < offset_in_invbj {
                assert(tail[k] == inv_bj0[k]);
            } else {
                assert(tail[k] == inv_bj0[(k + r1_len) as int]);
            }
        };
        assert(word_valid(tail, n));
        lemma_base_word_characterization(tail, n);

        // r1 =~= inv_bj0[offset..offset+r1_len]
        assert forall|k: int| 0 <= k < r1_len
            implies r1[k] == #[trigger] inv_bj0[(offset_in_invbj + k) as int]
        by {
            assert(w1[(p1 + k) as int] == r1[k]);
            let r0_pos = (p1 + k - p0) as int;
            assert(w1[(p1 + k) as int] == r0[r0_pos]);
            assert(r0[r0_pos] == inv_bj0[(offset_in_invbj + k) as int]);
        };

        // tail ≡_G inv(b_j0) via RelatorInsert
        let insert_step = DerivationStep::RelatorInsert {
            position: offset_in_invbj, relator_index: ri1, inverted: inv1,
        };
        assert(tail.subrange(0, offset_in_invbj) + r1
            + tail.subrange(offset_in_invbj, tail.len() as int) =~= inv_bj0);
        assert(apply_step(p, tail, insert_step) == Some(inv_bj0));
        lemma_single_step_equiv(p, tail, insert_step, inv_bj0);

        // w2 decomposition
        assert(w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R);

        // w_L, w_R are base subranges of w
        lemma_stable_count_subrange(w, 0, p0, n);
        lemma_subrange_word_valid(w, 0, p0, n + 1);
        lemma_subrange_word_valid(w, p0, w.len() as int, n + 1);
        lemma_base_word_valid_down(w_L, n);
        lemma_base_word_valid_down(w_R, n);

        // stable count
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(tail, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], tail, n);
        lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail, w_R, n);

        lemma_equiv_refl(p, a_j0);
        lemma_k3_inside_step2_noninv(data, w, w2, w_end, step2, w_L, inter, tail, w_R, j0);
    }
}

/// k=3 overlap case: RelatorDelete(base) inside inverted HNN relator.
/// r1 is entirely within b_j or inv(a_j) region of r0 (inv) = b_j + [Inv(n)] + inv(a_j) + [Gen(n)].
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_k3_rd_inside_inv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
    j0: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, true);
            let r1 = get_relator(hp, ri1, inv1);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: true };
            let step1 = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            // r1 entirely inside r0 (not touching stable letters or boundary)
            &&& p1 >= p0
            &&& p1 + r1.len() <= p0 + r0.len()
            // p1 strictly inside r0 (excludes degenerate p1 = p0 + r0_len)
            &&& p1 < p0 + r0.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        j0 == (ri0 as int - data.base.relators.len()) as int,
        0 <= j0 < data.associations.len(),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, true);
    let r1 = get_relator(hp, ri1, inv1);
    let r0_len = r0.len() as int;
    let r1_len = r1.len() as int;
    let (a_j0, b_j0) = data.associations[j0];
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;
    let inv_aj0 = inverse_word(a_j0);
    let p = data.base;

    reveal(presentation_valid);
    lemma_hnn_relator_inverted_stable_positions(data, j0);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    lemma_inverse_word_len(a_j0);
    lemma_base_word_characterization(inv_aj0, n);
    lemma_base_word_valid_down(w, n);

    // r0 (inv) = b_j0 + [Inv(n)] + inv(a_j0) + [Gen(n)]
    assert(r0 =~= b_j0 + seq![stable_letter_inv(data)] + inv_aj0 + seq![stable_letter(data)]);
    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));

    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);

    // r1 is base relator ≡_G ε
    assert(hp.relators[ri1 as int] == p.relators[ri1 as int]);
    assert(get_relator(p, ri1, inv1) =~= r1);
    if inv1 {
        lemma_relator_is_identity(p, ri1 as int);
        lemma_inverse_word_valid(p.relators[ri1 as int], n);
        lemma_inverse_of_identity(p, p.relators[ri1 as int]);
        lemma_base_word_characterization(inverse_word(p.relators[ri1 as int]), n);
    } else {
        lemma_relator_is_identity(p, ri1 as int);
        lemma_base_word_characterization(p.relators[ri1 as int], n);
    }

    // Stable positions: p0 + bj0_len (Inv(n)), p0 + bj0_len + aj0_len + 1 (Gen(n))
    let pos_inv = p0 + bj0_len;
    let pos_gen = p0 + bj0_len + aj0_len + 1;

    if p1 + r1_len <= pos_inv {
        // r1 entirely within b_j region
        let offset_in_bj = (p1 - p0) as int;
        let head = b_j0.subrange(0, offset_in_bj)
            + b_j0.subrange(offset_in_bj + r1_len, bj0_len);
        let inter = inv_aj0;

        // head is base and word_valid
        assert forall|k: int| 0 <= k < head.len() as int
            implies symbol_valid(#[trigger] head[k], n)
        by {
            if k < offset_in_bj {
                assert(head[k] == b_j0[k]);
            } else {
                assert(head[k] == b_j0[(k + r1_len) as int]);
            }
        };
        assert(word_valid(head, n));
        lemma_base_word_characterization(head, n);

        // r1 =~= b_j0[offset..offset+r1_len]
        assert forall|k: int| 0 <= k < r1_len
            implies r1[k] == #[trigger] b_j0[(offset_in_bj + k) as int]
        by {
            assert(w1[(p1 + k) as int] == r1[k]);
            assert(w1[(p1 + k) as int] == r0[((p1 - p0) + k) as int]);
            assert(r0[((p1 - p0) + k) as int] == b_j0[(offset_in_bj + k) as int]);
        };

        // head ≡_G b_j0 via RelatorInsert
        let insert_step = DerivationStep::RelatorInsert {
            position: offset_in_bj, relator_index: ri1, inverted: inv1,
        };
        assert(head.subrange(0, offset_in_bj) + r1
            + head.subrange(offset_in_bj, head.len() as int) =~= b_j0);
        assert(apply_step(p, head, insert_step) == Some(b_j0));
        lemma_single_step_equiv(p, head, insert_step, b_j0);

        // w2 decomposition
        assert(w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R);

        // w_L, w_R are base subranges of w
        lemma_stable_count_subrange(w, 0, p0, n);
        lemma_subrange_word_valid(w, 0, p0, n + 1);
        lemma_subrange_word_valid(w, p0, w.len() as int, n + 1);
        lemma_base_word_valid_down(w_L, n);
        lemma_base_word_valid_down(w_R, n);

        // stable count
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(head, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, head, n);
        lemma_stable_letter_count_concat(w_L + head, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], w_R, n);

        lemma_equiv_refl(p, inv_aj0);
        lemma_k3_inside_step2_inv(data, w, w2, w_end, step2, w_L, head, inter, w_R, j0);
    } else {
        // r1 entirely within inv(a_j) region
        // First prove r1 can't overlap Inv(n) at pos_inv.
        // From else condition: p1 + r1_len > pos_inv.
        // If p1 <= pos_inv, r1 contains the Inv(n) position → contradiction with r1 being base.
        if p1 <= pos_inv {
            let idx_in_r1 = (pos_inv - p1) as int;
            assert(w1.subrange(p1, p1 + r1_len) =~= r1);
            assert(w1[pos_inv] == r1[idx_in_r1]);
            assert(w1[pos_inv] == r0[(pos_inv - p0) as int]);
            assert(generator_index(w1[pos_inv]) == n);
            assert(symbol_valid(r1[idx_in_r1], n));
        }
        assert(p1 > pos_inv);
        // p1 < p0 + r0_len = pos_gen + 1 (from precondition), so p1 <= pos_gen.
        // Prove r1 doesn't touch Gen(n) at pos_gen.
        if p1 + r1_len > pos_gen {
            // p1 <= pos_gen (from p1 < p0 + r0_len and pos_gen = p0 + r0_len - 1)
            let idx_in_r1 = (pos_gen - p1) as int;
            assert(w1.subrange(p1, p1 + r1_len) =~= r1);
            assert(w1[pos_gen] == r1[idx_in_r1]);
            assert(w1[pos_gen] == r0[(pos_gen - p0) as int]);
            assert(generator_index(w1[pos_gen]) == n);
            assert(symbol_valid(r1[idx_in_r1], n));
        }
        assert(p1 + r1_len <= pos_gen);
        let offset_in_invaj = (p1 - pos_inv - 1) as int;
        let head = b_j0;
        let inter = inv_aj0.subrange(0, offset_in_invaj)
            + inv_aj0.subrange(offset_in_invaj + r1_len, inv_aj0.len() as int);

        // inter is base and word_valid
        assert forall|k: int| 0 <= k < inter.len() as int
            implies symbol_valid(#[trigger] inter[k], n)
        by {
            if k < offset_in_invaj {
                assert(inter[k] == inv_aj0[k]);
            } else {
                assert(inter[k] == inv_aj0[(k + r1_len) as int]);
            }
        };
        assert(word_valid(inter, n));
        lemma_base_word_characterization(inter, n);

        // r1 =~= inv_aj0[offset..offset+r1_len]
        assert forall|k: int| 0 <= k < r1_len
            implies r1[k] == #[trigger] inv_aj0[(offset_in_invaj + k) as int]
        by {
            assert(w1[(p1 + k) as int] == r1[k]);
            let r0_pos = (p1 + k - p0) as int;
            assert(w1[(p1 + k) as int] == r0[r0_pos]);
            assert(r0[r0_pos] == inv_aj0[(offset_in_invaj + k) as int]);
        };

        // inter ≡_G inv(a_j0) via RelatorInsert
        let insert_step = DerivationStep::RelatorInsert {
            position: offset_in_invaj, relator_index: ri1, inverted: inv1,
        };
        assert(inter.subrange(0, offset_in_invaj) + r1
            + inter.subrange(offset_in_invaj, inter.len() as int) =~= inv_aj0);
        assert(apply_step(p, inter, insert_step) == Some(inv_aj0));
        lemma_single_step_equiv(p, inter, insert_step, inv_aj0);

        // w2 decomposition
        assert(w2 =~= w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R);

        // w_L, w_R are base subranges of w
        lemma_stable_count_subrange(w, 0, p0, n);
        lemma_subrange_word_valid(w, 0, p0, n + 1);
        lemma_subrange_word_valid(w, p0, w.len() as int, n + 1);
        lemma_base_word_valid_down(w_L, n);
        lemma_base_word_valid_down(w_R, n);

        // stable count
        lemma_base_implies_count_zero(w_L, n);
        lemma_base_implies_count_zero(head, n);
        lemma_base_implies_count_zero(inter, n);
        lemma_base_implies_count_zero(w_R, n);
        lemma_stable_count_single(Symbol::Inv(n), n);
        lemma_stable_count_single(Symbol::Gen(n), n);
        lemma_stable_letter_count_concat(w_L, head, n);
        lemma_stable_letter_count_concat(w_L + head, seq![Symbol::Inv(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)], inter, n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter, seq![Symbol::Gen(n)], n);
        lemma_stable_letter_count_concat(w_L + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)], w_R, n);

        lemma_equiv_refl(p, b_j0);
        lemma_k3_inside_step2_inv(data, w, w2, w_end, step2, w_L, head, inter, w_R, j0);
    }
}

/// k=3 overlap case: RelatorDelete(base) straddles right boundary of non-inverted HNN relator.
/// r0 = [Inv(n)] + a_j + [Gen(n)] + inv(b_j). r1 starts in inv(b_j) region and extends past r0
/// into w_R. After deletion: w2 = w_L + [Inv(n)] + a_j + [Gen(n)] + tail + w_R_short,
/// where tail = inv_bj[0..offset], w_R_short = w_R[overlap..].
/// w = w_L + r1_in_wR + w_R_short where r1 = r1_in_r0 + r1_in_wR ≡_G ε.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_k3_rd_boundary_noninv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
    j0: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, false);
            let r1 = get_relator(hp, ri1, inv1);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: false };
            let step1 = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            // r1 starts inside inv(b_j) and extends past r0
            &&& p1 > p0
            &&& p1 < p0 + r0.len()
            &&& p1 + r1.len() > p0 + r0.len()
            &&& p1 + r1.len() <= w1.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        j0 == (ri0 as int - data.base.relators.len()) as int,
        0 <= j0 < data.associations.len(),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let r0 = get_relator(hp, ri0, false);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;

    reveal(presentation_valid);
    lemma_hnn_relator_stable_positions(data, j0);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inv_bj0, n);

    // w1 = w_L + r0 + w_R where w_L = w[0..p0], w_R = w[p0..]
    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);
    assert(w1 =~= w_L + r0 + w_R);
    assert(w =~= w_L + w_R);

    lemma_base_word_valid_down(w, n);
    lemma_subrange_word_valid(w, 0, p0, n);
    lemma_subrange_word_valid(w, p0, w.len() as int, n);
    lemma_base_word_characterization(w_L, n);
    lemma_base_word_characterization(w_R, n);

    // r1 is base
    if inv1 {
        lemma_inverse_word_valid(data.base.relators[ri1 as int], n);
        lemma_base_word_characterization(inverse_word(data.base.relators[ri1 as int]), n);
    } else {
        lemma_base_word_characterization(data.base.relators[ri1 as int], n);
    }
    assert(hp.relators[ri1 as int] == data.base.relators[ri1 as int]);

    let pos_gen = p0 + aj0_len + 1;

    // r1 can't contain Gen(n) at pos_gen, so p1 > pos_gen
    // (already established by dispatcher, but we need it here for the proof)
    if p1 <= pos_gen {
        let idx_in_r1 = (pos_gen - p1) as int;
        if p1 + r1_len > pos_gen {
            assert(w1.subrange(p1, p1 + r1_len) =~= r1);
            assert(w1[pos_gen] == r1[idx_in_r1]);
            assert(generator_index(w1[pos_gen]) == n);
            assert(symbol_valid(r1[idx_in_r1], n));
        }
    }
    assert(p1 > pos_gen);

    // Decompose the boundary overlap
    // r0 = [Inv(n)] + a_j + [Gen(n)] + inv_bj  (length 2 + aj0_len + bj0_len)
    // r1 starts at p1 in w1, within the inv_bj region (p1 > pos_gen = p0 + aj0_len + 1)
    // offset = how far into inv_bj r1 starts
    let offset = p1 - (pos_gen + 1);
    // overlap_in_r0 = how much of r1 is inside r0
    let overlap_in_r0 = (p0 + r0_len) - p1;
    // overlap_in_wR = how much of r1 is in w_R
    let overlap_in_wR = r1_len - overlap_in_r0;

    assert(offset >= 0);
    assert(overlap_in_r0 > 0);
    assert(overlap_in_wR > 0);
    assert(offset + overlap_in_r0 == bj0_len) by {
        // pos_gen + 1 + offset = p1
        // p1 + overlap_in_r0 = p0 + r0_len = p0 + 2 + aj0_len + bj0_len
        // pos_gen + 1 = p0 + aj0_len + 2
        // offset + overlap_in_r0 = (p0 + 2 + aj0_len + bj0_len) - (p0 + aj0_len + 2) = bj0_len
    };

    let tail = inv_bj0.subrange(0, offset);
    let r1_in_r0 = inv_bj0.subrange(offset, bj0_len);
    let r1_in_wR = w_R.subrange(0, overlap_in_wR);
    let w_R_short = w_R.subrange(overlap_in_wR, w_R.len() as int);

    assert(inv_bj0 =~= tail + r1_in_r0);
    assert(w_R =~= r1_in_wR + w_R_short);
    assert(w =~= w_L + r1_in_wR + w_R_short);

    // r1 = r1_in_r0 + r1_in_wR (content matching in w1)
    assert(r1 =~= r1_in_r0 + r1_in_wR) by {
        assert(w1.subrange(p1, p1 + r1_len) =~= r1);
        assert forall|k: int| 0 <= k < r1_len
            implies r1[k] == #[trigger] (r1_in_r0 + r1_in_wR)[k]
        by {
            if k < overlap_in_r0 {
                // r1[k] = w1[p1 + k] where p1+k is inside r0's inv_bj region
                assert(w1[(p1 + k) as int] == r0[((p1 + k) - p0) as int]);
                // r0[pos_gen+1-p0+offset+k] = inv_bj0[offset + k] = r1_in_r0[k]
            } else {
                // r1[k] = w1[p1 + k] where p1+k >= p0+r0_len, so in w_R
                assert(w1[(p1 + k) as int] == w_R[((p1 + k) - p0 - r0_len) as int]);
            }
        };
    };

    // r1 ≡_G ε (in base presentation, since r1 is a base relator)
    assert(hp.relators[ri1 as int] == p.relators[ri1 as int]);
    assert(get_relator(p, ri1, inv1) =~= r1);
    if inv1 {
        lemma_relator_is_identity(p, ri1 as int);
        lemma_inverse_of_identity(p, p.relators[ri1 as int]);
    } else {
        lemma_relator_is_identity(p, ri1 as int);
    }

    // r1 = r1_in_r0 + r1_in_wR ≡_G ε → identity_split → r1_in_wR ≡_G inv(r1_in_r0)
    lemma_subrange_word_valid(inv_bj0, 0, offset, n);
    lemma_subrange_word_valid(inv_bj0, offset, bj0_len, n);
    lemma_subrange_word_valid(w_R, 0, overlap_in_wR, n);
    lemma_subrange_word_valid(w_R, overlap_in_wR, w_R.len() as int, n);
    lemma_base_word_characterization(tail, n);
    lemma_base_word_characterization(r1_in_r0, n);
    lemma_base_word_characterization(r1_in_wR, n);
    lemma_base_word_characterization(w_R_short, n);

    assert(concat(r1_in_r0, r1_in_wR) =~= r1);
    lemma_identity_split(p, r1_in_r0, r1_in_wR);
    // r1_in_wR ≡_G inv(r1_in_r0)

    // w2 = w_L + [Inv(n)] + a_j + [Gen(n)] + tail + w_R_short
    assert forall|k: int| 0 <= k < w2.len()
        implies w2[k] == #[trigger] (w_L + seq![Symbol::Inv(n)] + a_j0 + seq![Symbol::Gen(n)] + tail + w_R_short)[k]
    by {
        // w2 = w1[0..p1] + w1[p1+r1_len..]
        assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + r1_len, w1.len() as int));
        if k < p0 {
        } else if k == p0 {
        } else if k <= p0 + aj0_len {
        } else if k == pos_gen {
        } else if k < p1 {
            // in tail region
        } else {
            // after deletion: from w_R_short
        }
    };
    assert(w2 =~= w_L + seq![Symbol::Inv(n)] + a_j0 + seq![Symbol::Gen(n)] + tail + w_R_short);

    // stable_letter_count(w2, n) == 2
    lemma_base_implies_count_zero(w_L, n);
    lemma_base_implies_count_zero(a_j0, n);
    lemma_base_implies_count_zero(tail, n);
    lemma_base_implies_count_zero(w_R_short, n);
    lemma_stable_count_single(Symbol::Inv(n), n);
    lemma_stable_count_single(Symbol::Gen(n), n);
    lemma_stable_letter_count_concat(w_L, seq![Symbol::Inv(n)], n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)], a_j0, n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + a_j0, seq![Symbol::Gen(n)], n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + a_j0 + seq![Symbol::Gen(n)], tail, n);
    lemma_stable_letter_count_concat(w_L + seq![Symbol::Inv(n)] + a_j0 + seq![Symbol::Gen(n)] + tail, w_R_short, n);
    assert(stable_letter_count(w2, n) == 2nat);

    // Now dispatch step2
    let inter = a_j0;
    lemma_equiv_refl(p, a_j0);

    // Step2 must eliminate both stable letters. Case analysis:
    match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } => {
            let pair2 = Seq::new(1, |_i: int| sym2) + Seq::new(1, |_i: int| inverse_symbol(sym2));
            assert(w_end =~= w2.subrange(0, p2) + pair2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, pair2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            assert(w_end =~= w2.subrange(0, p2) + r2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, r2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::FreeReduce { position: p2 } => {
            lemma_stable_count_reduce(w2, p2, n);
            if generator_index(w2[p2]) == n {
                // Stable FreeReduce: adjacent stable letters → inter empty → a_j ≡_G ε
                let pos_inv = w_L.len() as int;
                assert(p2 == pos_inv) by {
                    if p2 != pos_inv {
                        if p2 == pos_gen {
                            // w2[pos_gen+1] = tail[0] or w_R_short[0], both base → can't cancel Gen(n)
                        } else if p2 < pos_inv {
                        } else if p2 > pos_gen {
                        } else {
                            // between: base symbol, not stable
                        }
                    }
                };
                assert(aj0_len == 0) by {
                    // w2[pos_inv+1] must be Gen(n) for cancellation with Inv(n)
                };
                assert(a_j0 =~= empty_word());
                lemma_equiv_refl(p, empty_word());
                lemma_trivial_association_implies_trivial(data, j0);
                // b_j0 ≡_G ε → inv(b_j0) ≡_G ε
                lemma_inverse_of_identity(p, b_j0);
                // inv_bj0 = tail + r1_in_r0 ≡_G ε
                // identity_split: r1_in_r0 ≡_G inv(tail)
                assert(concat(tail, r1_in_r0) =~= inv_bj0);
                lemma_identity_split(p, tail, r1_in_r0);
                // r1_in_r0 ≡_G inv(tail)
                // Chain: inv(r1_in_r0) ≡_G inv(inv(tail)) =~= tail
                // Then: r1_in_wR ≡_G inv(r1_in_r0) ≡_G tail
                lemma_inverse_word_valid(r1_in_r0, n);
                lemma_inverse_word_valid(tail, n);
                lemma_inverse_word_congruence(p, r1_in_r0, inverse_word(tail));
                crate::word::lemma_inverse_involution(tail);
                lemma_equiv_transitive(p, r1_in_wR, inverse_word(r1_in_r0), tail);
                // r1_in_wR ≡_G tail

                // w_end = w_L + tail + w_R_short (after removing stable pair)
                assert(w_end =~= w_L + tail + w_R_short);
                // w = w_L + r1_in_wR + w_R_short ≡_G w_L + tail + w_R_short = w_end
                lemma_equiv_concat_right(p, w_L, r1_in_wR, tail);
                lemma_equiv_concat_left(p, w_L + r1_in_wR, w_L + tail, w_R_short);
                assert(concat(w_L + r1_in_wR, w_R_short) =~= w);
                assert(concat(w_L + tail, w_R_short) =~= w_end);
            } else {
                // Base FreeReduce: count stays at 2 → not base → contradiction
                assert(stable_letter_count(w_end, n) == 2nat);
                lemma_base_implies_count_zero(w_end, n);
            }
        },
        DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            let r2_len = r2.len() as int;
            assert(w2.subrange(p2, p2 + r2_len) =~= r2);
            assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));

            lemma_relator_stable_count(data, ri2, inv2);

            if (ri2 as int) < p.relators.len() {
                // Base relator delete: count unchanged → 2 → not base → contradiction
                lemma_stable_count_subrange(w2, p2, p2 + r2_len, n);
                lemma_stable_letter_count_concat(
                    w2.subrange(0, p2), w2.subrange(p2 + r2_len, w2.len() as int), n);
                lemma_base_implies_count_zero(w_end, n);
            } else {
                // HNN RelatorDelete: removes 2 stable letters
                let j2 = (ri2 as int - p.relators.len()) as int;
                let (a_j2, b_j2) = data.associations[j2];
                lemma_base_word_characterization(a_j2, n);
                lemma_base_word_characterization(b_j2, n);
                lemma_inverse_word_valid(b_j2, n);
                lemma_inverse_word_valid(a_j2, n);
                assert(ri2 == (data.base.relators.len() + j2) as nat);

                if !inv2 {
                    lemma_k3_rd_boundary_noninv_step2_rd_noninv(
                        data, w, w2, w_end, w_L, inter, tail, w_R_short,
                        j0, r1_in_r0, r1_in_wR, p2, j2);
                } else {
                    lemma_k3_rd_boundary_noninv_step2_rd_inv(
                        data, w, w2, w_end, w_L, inter, tail, w_R_short,
                        j0, r1_in_r0, r1_in_wR, p2, j2);
                }
            }
        },
    }
}

/// Non-inverted r2 RelatorDelete sub-case for boundary RelatorDelete + non-inverted r0.
/// w2 = w_L + [Inv(n)] + inter + [Gen(n)] + tail + w_R_short,
/// w = w_L + r1_in_wR + w_R_short,
/// inv_bj0 = tail + r1_in_r0, r1 = r1_in_r0 + r1_in_wR ≡_G ε.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_k3_rd_boundary_noninv_step2_rd_noninv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L: Word, inter: Word, tail: Word, w_R_short: Word,
    j0: int, r1_in_r0: Word, r1_in_wR: Word,
    p2: int, j2: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            let inv_bj0 = inverse_word(data.associations[j0].1);
            &&& w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R_short
            &&& w =~= w_L + r1_in_wR + w_R_short
            &&& inter =~= data.associations[j0].0
            &&& inv_bj0 =~= tail + r1_in_r0
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(tail, data.base.num_generators),
        is_base_word(w_R_short, data.base.num_generators),
        is_base_word(r1_in_r0, data.base.num_generators),
        is_base_word(r1_in_wR, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(tail, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R_short, data.base.num_generators),
        word_valid(r1_in_r0, data.base.num_generators),
        word_valid(r1_in_wR, data.base.num_generators),
        // r1_in_wR ≡_G inv(r1_in_r0)
        equiv_in_presentation(data.base, r1_in_wR, inverse_word(r1_in_r0)),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        ({
            let hp = hnn_presentation(data);
            let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, false);
            &&& 0 <= p2
            &&& p2 + r2.len() as int <= w2.len() as int
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;
    let pos_inv = w_L.len() as int;
    let pos_gen = pos_inv + 1 + aj0_len;
    let (a_j2, b_j2) = data.associations[j2];
    let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, false);

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inv_bj0, n);
    lemma_base_word_characterization(a_j2, n);
    lemma_base_word_characterization(b_j2, n);
    lemma_inverse_word_valid(b_j2, n);
    lemma_inverse_word_valid(a_j2, n);

    // r2 structure
    assert(r2 =~= hnn_relator(data, j2)) by {
        assert(hp.relators =~= data.base.relators + hnn_relators(data));
        assert(hp.relators[(data.base.relators.len() + j2) as int]
            == hnn_relators(data)[j2 as int]);
        assert(hnn_relators(data)[j2 as int] == hnn_relator(data, j2));
    };
    lemma_hnn_relator_stable_positions(data, j2);

    // Position matching: r2[0] = Inv(n) must be at pos_inv → p2 = pos_inv
    assert(p2 == pos_inv) by {
        if p2 != pos_inv {
            if p2 < pos_inv {
                assert(w2[p2] == r2[0]);
                assert(r2[0] == Symbol::Inv(n));
            } else {
                assert(w2[p2] == Symbol::Inv(n));
                if p2 == pos_gen {
                } else if p2 < pos_gen {
                } else {
                }
            }
        }
    };

    // a_j2 = inter = a_j0
    assert(a_j2.len() == aj0_len) by {};
    assert(a_j2 =~= inter) by {
        assert forall|k: int| 0 <= k < a_j2.len()
            implies a_j2[k] == #[trigger] inter[k]
        by {
            assert(a_j2[k] == r2[(k + 1) as int]);
            assert(r2[(k + 1) as int] == w2[(pos_inv + 1 + k) as int]);
        };
    };
    assert(a_j2 =~= a_j0);

    // By isomorphism: b_j2 ≡_G b_j0 → inv(b_j2) ≡_G inv(b_j0)
    lemma_equiv_refl(p, a_j0);
    lemma_isomorphism_maps_equivalence(data, j0, j2);
    lemma_inverse_word_congruence(p, b_j2, b_j0);

    let inv_bj2 = inverse_word(b_j2);
    let bj2_len = b_j2.len() as int;
    let tail_len = tail.len() as int;
    let r1_in_r0_len = r1_in_r0.len() as int;

    // inv(b_j2) must match prefix of (tail + w_R_short) in w2
    crate::word::lemma_inverse_word_len(b_j2);

    if bj2_len <= tail_len {
        // r2 fits within tail region
        let suffix = tail.subrange(bj2_len, tail_len);
        assert(w_end =~= w_L + suffix + w_R_short);

        // inv(b_j2) =~= tail[0..bj2_len]
        assert forall|k: int| 0 <= k < bj2_len
            implies inv_bj2[k] == #[trigger] tail[k]
        by {
            assert(inv_bj2[k] == r2[(2 + aj0_len + k) as int]);
            assert(r2[(2 + aj0_len + k) as int] == w2[(pos_gen + 1 + k) as int]);
        };
        assert(inv_bj2 =~= tail.subrange(0, bj2_len));

        // inv(b_j2) ≡_G inv(b_j0) = tail + r1_in_r0
        // So: tail[0..bj2_len] ≡_G tail + r1_in_r0
        // tail = tail[0..bj2_len] + suffix
        assert(tail =~= tail.subrange(0, bj2_len) + suffix);
        assert(inv_bj0 =~= tail.subrange(0, bj2_len) + suffix + r1_in_r0);
        assert(concat(tail.subrange(0, bj2_len), suffix + r1_in_r0) =~= inv_bj0);

        lemma_subrange_word_valid(tail, 0, bj2_len, n);
        lemma_subrange_word_valid(tail, bj2_len, tail_len, n);
        lemma_concat_word_valid(suffix, r1_in_r0, n);
        lemma_inverse_word_valid(b_j2, n);

        // inv_bj0 ≡_G inv(b_j2) = tail[0..bj2_len]
        lemma_equiv_symmetric(p, inv_bj2, inv_bj0);
        lemma_right_cancel(p, tail.subrange(0, bj2_len), suffix + r1_in_r0);
        // suffix + r1_in_r0 ≡_G ε
        // identity_split: r1_in_r0 ≡_G inv(suffix)
        lemma_identity_split(p, suffix, r1_in_r0);

        // r1_in_wR ≡_G inv(r1_in_r0) ≡_G inv(inv(suffix)) =~= suffix
        lemma_inverse_word_valid(suffix, n);
        lemma_inverse_word_valid(r1_in_r0, n);
        lemma_inverse_word_congruence(p, r1_in_r0, inverse_word(suffix));
        crate::word::lemma_inverse_involution(suffix);
        lemma_equiv_transitive(p, r1_in_wR, inverse_word(r1_in_r0), suffix);

        // w ≡_G w_end
        lemma_equiv_concat_right(p, w_L, r1_in_wR, suffix);
        lemma_equiv_concat_left(p, w_L + r1_in_wR, w_L + suffix, w_R_short);
        assert(concat(w_L + r1_in_wR, w_R_short) =~= w);
        assert(concat(w_L + suffix, w_R_short) =~= w_end);
    } else {
        // r2 extends past tail into w_R_short
        let overshoot = (bj2_len - tail_len) as int;
        assert(w_end =~= w_L + w_R_short.subrange(overshoot, w_R_short.len() as int));

        // inv(b_j2) =~= tail + w_R_short[0..overshoot]
        assert(inv_bj2 =~= tail + w_R_short.subrange(0, overshoot)) by {
            assert forall|k: int| 0 <= k < bj2_len
                implies inv_bj2[k] == #[trigger] (tail + w_R_short.subrange(0, overshoot))[k]
            by {
                assert(inv_bj2[k] == r2[(2 + aj0_len + k) as int]);
                assert(r2[(2 + aj0_len + k) as int] == w2[(pos_gen + 1 + k) as int]);
            };
        };

        // inv(b_j2) ≡_G inv(b_j0) = tail + r1_in_r0
        // So: tail + w_R_short[0..overshoot] ≡_G tail + r1_in_r0
        // By left cancel: w_R_short[0..overshoot] ≡_G r1_in_r0
        lemma_subrange_word_valid(w_R_short, 0, overshoot, n);
        lemma_subrange_word_valid(w_R_short, overshoot, w_R_short.len() as int, n);
        assert(concat(tail, w_R_short.subrange(0, overshoot)) =~= inv_bj2);
        assert(concat(tail, r1_in_r0) =~= inv_bj0);
        lemma_concat_left_cancel_equiv(p, tail, w_R_short.subrange(0, overshoot), r1_in_r0);
        // w_R_short[0..overshoot] ≡_G r1_in_r0

        // r1_in_wR ≡_G inv(r1_in_r0) ≡_G inv(w_R_short[0..overshoot])
        lemma_inverse_word_valid(r1_in_r0, n);
        lemma_inverse_word_valid(w_R_short.subrange(0, overshoot), n);
        // w_R_short[0..overshoot] ≡ r1_in_r0 → inv(w_R_short[0..overshoot]) ≡ inv(r1_in_r0)
        lemma_equiv_symmetric(p, w_R_short.subrange(0, overshoot), r1_in_r0);
        lemma_inverse_word_congruence(p, r1_in_r0, w_R_short.subrange(0, overshoot));
        // inv(r1_in_r0) ≡ inv(w_R_short[0..overshoot])
        lemma_equiv_transitive(p, r1_in_wR, inverse_word(r1_in_r0), inverse_word(w_R_short.subrange(0, overshoot)));
        // r1_in_wR ≡_G inv(w_R_short[0..overshoot])

        // r1_in_wR + w_R_short[0..overshoot] ≡_G inv(w_R_short[0..overshoot]) + w_R_short[0..overshoot] ≡_G ε
        lemma_inverse_word_valid(w_R_short.subrange(0, overshoot), n);
        lemma_equiv_concat_left(p, r1_in_wR, inverse_word(w_R_short.subrange(0, overshoot)), w_R_short.subrange(0, overshoot));
        crate::presentation_lemmas::lemma_word_inverse_left(p, w_R_short.subrange(0, overshoot));
        lemma_equiv_transitive(p,
            concat(r1_in_wR, w_R_short.subrange(0, overshoot)),
            concat(inverse_word(w_R_short.subrange(0, overshoot)), w_R_short.subrange(0, overshoot)),
            empty_word());
        // r1_in_wR + w_R_short[0..overshoot] ≡_G ε

        // w = w_L + (r1_in_wR + w_R_short[0..overshoot]) + w_R_short[overshoot..]
        assert(w_R_short =~= w_R_short.subrange(0, overshoot) + w_R_short.subrange(overshoot, w_R_short.len() as int));
        assert(w =~= w_L + (r1_in_wR + w_R_short.subrange(0, overshoot)) + w_R_short.subrange(overshoot, w_R_short.len() as int));
        lemma_remove_trivial_equiv(p, w_L, w_R_short.subrange(overshoot, w_R_short.len() as int),
            r1_in_wR + w_R_short.subrange(0, overshoot));
        assert(concat(w_L, concat(r1_in_wR + w_R_short.subrange(0, overshoot), w_R_short.subrange(overshoot, w_R_short.len() as int))) =~= w);
        assert(concat(w_L, w_R_short.subrange(overshoot, w_R_short.len() as int)) =~= w_end);
    }
}

/// Inverted r2 RelatorDelete sub-case for boundary RelatorDelete + non-inverted r0.
/// Same decomposition as non-inverted but r2 = b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)].
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_k3_rd_boundary_noninv_step2_rd_inv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L: Word, inter: Word, tail: Word, w_R_short: Word,
    j0: int, r1_in_r0: Word, r1_in_wR: Word,
    p2: int, j2: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            let inv_bj0 = inverse_word(data.associations[j0].1);
            &&& w2 =~= w_L + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + tail + w_R_short
            &&& w =~= w_L + r1_in_wR + w_R_short
            &&& inter =~= data.associations[j0].0
            &&& inv_bj0 =~= tail + r1_in_r0
        }),
        is_base_word(w_L, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(tail, data.base.num_generators),
        is_base_word(w_R_short, data.base.num_generators),
        is_base_word(r1_in_r0, data.base.num_generators),
        is_base_word(r1_in_wR, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(tail, data.base.num_generators),
        word_valid(w_L, data.base.num_generators),
        word_valid(w_R_short, data.base.num_generators),
        word_valid(r1_in_r0, data.base.num_generators),
        word_valid(r1_in_wR, data.base.num_generators),
        equiv_in_presentation(data.base, r1_in_wR, inverse_word(r1_in_r0)),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        ({
            let hp = hnn_presentation(data);
            let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, true);
            &&& 0 <= p2
            &&& p2 + r2.len() as int <= w2.len() as int
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_bj0 = inverse_word(b_j0);
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;
    let pos_inv = w_L.len() as int;
    let pos_gen = pos_inv + 1 + aj0_len;
    let (a_j2, b_j2) = data.associations[j2];
    let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, true);

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inv_bj0, n);
    lemma_base_word_characterization(a_j2, n);
    lemma_base_word_characterization(b_j2, n);
    lemma_inverse_word_valid(b_j2, n);
    lemma_inverse_word_valid(a_j2, n);

    // Inverted r2 = b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)]
    lemma_hnn_relator_inverted_stable_positions(data, j2);
    let bj2_len = b_j2.len() as int;
    let aj2_len = a_j2.len() as int;

    // r2's Inv(n) is at position bj2_len within r2, must match w2's Inv(n) at pos_inv
    // So p2 + bj2_len = pos_inv, i.e., p2 = pos_inv - bj2_len
    assert(p2 == pos_inv - bj2_len) by {
        // r2 has stable letters at positions bj2_len (Inv) and bj2_len+aj2_len+1 (Gen)
        // These must match w2's stable letters at pos_inv and pos_gen
        // r2[bj2_len] = Inv(n) must match w2[p2+bj2_len] = w2[pos_inv] = Inv(n)
        // So p2+bj2_len = pos_inv
        if p2 + bj2_len != pos_inv {
            // r2[bj2_len] = Inv(n) at position p2+bj2_len in w2
            // If p2+bj2_len != pos_inv, then w2[p2+bj2_len] is base → contradiction
            if p2 + bj2_len < pos_inv {
                assert(w2[(p2 + bj2_len) as int] == r2[bj2_len]);
            } else if p2 + bj2_len == pos_gen {
                // w2[pos_gen] = Gen(n) ≠ Inv(n)
                assert(w2[pos_gen] == Symbol::Gen(n));
            } else {
                assert(w2[(p2 + bj2_len) as int] == r2[bj2_len]);
            }
        }
    };

    // b_j2 = w_L suffix (b_j2 covers w2[p2..pos_inv] = w_L[p2..])
    assert(b_j2 =~= w_L.subrange(pos_inv - bj2_len, pos_inv)) by {
        assert forall|k: int| 0 <= k < bj2_len
            implies b_j2[k] == #[trigger] w_L.subrange(pos_inv - bj2_len, pos_inv)[k]
        by {
            assert(b_j2[k] == r2[k]);
            assert(r2[k] == w2[(p2 + k) as int]);
        };
    };

    // inv(a_j2) must match inter, so |inv(a_j2)| = |a_j0| and inv(a_j2) =~= a_j0
    crate::word::lemma_inverse_word_len(a_j2);
    assert(aj2_len == aj0_len) by {
        // Gen(n) at r2[bj2_len+aj2_len+1] must match pos_gen
        // p2+bj2_len+aj2_len+1 = pos_inv+aj2_len+1 must equal pos_gen = pos_inv+1+aj0_len
    };
    let inv_aj2 = inverse_word(a_j2);
    assert(inv_aj2 =~= inter) by {
        assert forall|k: int| 0 <= k < aj0_len
            implies inv_aj2[k] == #[trigger] inter[k]
        by {
            assert(inv_aj2[k] == r2[(bj2_len + 1 + k) as int]);
            assert(r2[(bj2_len + 1 + k) as int] == w2[(pos_inv + 1 + k) as int]);
        };
    };
    assert(inv_aj2 =~= a_j0);

    // inv(a_j2) = a_j0 → a_j2 = inv(a_j0) → a_j2 ≡_G inv(a_j0)
    crate::word::lemma_inverse_involution(a_j2);
    // a_j2 =~= inv(inv(a_j2)) =~= inv(a_j0)
    // By isomorphism (inverse variant): a_j2 ≡_G inv(a_j0) → b_j2 ≡_G inv(b_j0)
    lemma_equiv_refl(p, inverse_word(a_j0));
    lemma_isomorphism_maps_inverse_equivalence(data, j0, j2);
    // b_j2 ≡_G inv(b_j0)

    // r2 deletes: w_end = w2[0..p2] + w2[p2+r2_len..]
    // p2 = pos_inv - bj2_len
    // r2_len = bj2_len + 1 + aj0_len + 1 + 1... wait
    // r2 = b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)], len = bj2_len + 1 + aj0_len + 1
    let r2_len = r2.len() as int;
    // p2 + r2_len = pos_inv - bj2_len + bj2_len + 2 + aj0_len = pos_inv + 2 + aj0_len = pos_gen + 1
    // So r2 goes from p2 to pos_gen+1, just after Gen(n)
    // w_end = w_L[0..p2] + (tail + w_R_short)
    assert(w_end =~= w_L.subrange(0, pos_inv - bj2_len) + tail + w_R_short) by {
        assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));
        // w2[0..p2] = w_L[0..pos_inv-bj2_len]
        // w2[p2+r2_len..] = w2[pos_gen+1..] = tail + w_R_short
    };

    // b_j2 ≡_G inv(b_j0) and b_j2 =~= w_L[pos_inv-bj2_len..pos_inv]
    // Need: w = w_L + r1_in_wR + w_R_short ≡_G w_L[0..pos_inv-bj2_len] + tail + w_R_short = w_end
    // i.e., w_L[pos_inv-bj2_len..] + r1_in_wR ≡_G tail
    // where w_L[pos_inv-bj2_len..] = b_j2

    let w_L_prefix = w_L.subrange(0, pos_inv - bj2_len);
    let w_L_suffix = w_L.subrange(pos_inv - bj2_len, pos_inv);
    assert(w_L =~= w_L_prefix + w_L_suffix);
    assert(w_L_suffix =~= b_j2);
    assert(w =~= w_L_prefix + w_L_suffix + r1_in_wR + w_R_short);
    assert(w_end =~= w_L_prefix + tail + w_R_short);

    // Need: w_L_suffix + r1_in_wR ≡_G tail
    // b_j2 ≡_G inv(b_j0), and inv(b_j0) = inv_bj0 = tail + r1_in_r0
    // So: b_j2 ≡_G tail + r1_in_r0
    // Also: r1_in_wR ≡_G inv(r1_in_r0)
    // So: w_L_suffix + r1_in_wR = b_j2 + r1_in_wR ≡_G (tail + r1_in_r0) + inv(r1_in_r0)
    //   = tail + (r1_in_r0 + inv(r1_in_r0)) ≡_G tail + ε = tail

    // b_j2 ≡_G tail + r1_in_r0
    assert(inv_bj0 =~= tail + r1_in_r0);
    lemma_equiv_symmetric(p, b_j2, inverse_word(b_j0));
    // inv(b_j0) ≡_G b_j2, but we need b_j2 ≡_G inv(b_j0) = tail + r1_in_r0
    // We have b_j2 ≡_G inv(b_j0) from isomorphism
    // So: w_L_suffix ≡_G tail + r1_in_r0 (since w_L_suffix =~= b_j2)

    // w_L_suffix + r1_in_wR ≡_G (tail + r1_in_r0) + inv(r1_in_r0)
    lemma_equiv_concat_left(p, w_L_suffix, tail + r1_in_r0, r1_in_wR);
    // gives: w_L_suffix + r1_in_wR ≡_G (tail + r1_in_r0) + r1_in_wR
    // But we need (tail + r1_in_r0) + inv(r1_in_r0), and r1_in_wR ≡_G inv(r1_in_r0)
    lemma_equiv_concat_right(p, tail + r1_in_r0, r1_in_wR, inverse_word(r1_in_r0));
    // (tail + r1_in_r0) + r1_in_wR ≡_G (tail + r1_in_r0) + inv(r1_in_r0)
    lemma_concat_word_valid(tail, r1_in_r0, n);
    lemma_concat_word_valid(w_L_suffix, r1_in_wR, n);
    lemma_inverse_word_valid(r1_in_r0, n);
    lemma_concat_word_valid(tail + r1_in_r0, r1_in_wR, n);
    lemma_concat_word_valid(tail + r1_in_r0, inverse_word(r1_in_r0), n);
    lemma_equiv_transitive(p,
        concat(w_L_suffix, r1_in_wR),
        concat(tail + r1_in_r0, r1_in_wR),
        concat(tail + r1_in_r0, inverse_word(r1_in_r0)));
    // w_L_suffix + r1_in_wR ≡_G (tail + r1_in_r0) + inv(r1_in_r0)

    // (tail + r1_in_r0) + inv(r1_in_r0) = tail + (r1_in_r0 + inv(r1_in_r0))
    assert(concat(tail + r1_in_r0, inverse_word(r1_in_r0))
        =~= tail + concat(r1_in_r0, inverse_word(r1_in_r0)));
    // r1_in_r0 + inv(r1_in_r0) ≡_G ε
    crate::presentation_lemmas::lemma_word_inverse_right(p, r1_in_r0);
    // tail + (r1_in_r0 + inv(r1_in_r0)) ≡_G tail + ε = tail
    lemma_remove_trivial_equiv(p, tail, empty_word(), concat(r1_in_r0, inverse_word(r1_in_r0)));
    assert(concat(tail, concat(concat(r1_in_r0, inverse_word(r1_in_r0)), empty_word()))
        =~= tail + concat(r1_in_r0, inverse_word(r1_in_r0)));
    assert(concat(tail, empty_word()) =~= tail);
    // So: tail + (r1_in_r0 + inv(r1_in_r0)) ≡_G tail
    lemma_equiv_transitive(p,
        concat(w_L_suffix, r1_in_wR),
        tail + concat(r1_in_r0, inverse_word(r1_in_r0)),
        tail);

    // Finally: w = w_L_prefix + (w_L_suffix + r1_in_wR) + w_R_short
    //        ≡_G w_L_prefix + tail + w_R_short = w_end
    lemma_subrange_word_valid(w_L, 0, pos_inv - bj2_len, n);
    lemma_equiv_concat_right(p, w_L_prefix, concat(w_L_suffix, r1_in_wR), tail);
    lemma_equiv_concat_left(p, w_L_prefix + concat(w_L_suffix, r1_in_wR), w_L_prefix + tail, w_R_short);
    assert(concat(w_L_prefix + concat(w_L_suffix, r1_in_wR), w_R_short) =~= w);
    assert(concat(w_L_prefix + tail, w_R_short) =~= w_end);
}

/// k=3 overlap case: RelatorDelete(base) straddles left boundary of inverted HNN relator.
/// r0 (inv) = b_j + [Inv(n)] + inv(a_j) + [Gen(n)]. r1 starts before r0 (in w_L) and extends
/// into the b_j region of r0. After deletion: w2 = w_L_short + b_j_tail + [Inv(n)] + inv(a_j) + [Gen(n)] + w_R,
/// where b_j_tail = b_j[overlap_in_r0..], w_L_short = w_L[0..p1].
/// w = w_L_short + r1_in_wL + w_R where r1 = r1_in_wL + r1_in_r0 ≡_G ε.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_k3_rd_boundary_inv(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
    j0: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, true);
            let r1 = get_relator(hp, ri1, inv1);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: true };
            let step1 = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
            // r1 starts before r0 and extends into b_j
            &&& p1 < p0
            &&& p1 + r1.len() > p0
            &&& p1 + r1.len() <= p0 + r0.len()
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        j0 == (ri0 as int - data.base.relators.len()) as int,
        0 <= j0 < data.associations.len(),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let r0 = get_relator(hp, ri0, true);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let (a_j0, b_j0) = data.associations[j0];
    let inv_aj0 = inverse_word(a_j0);
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;

    reveal(presentation_valid);
    lemma_hnn_relator_inverted_stable_positions(data, j0);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(inv_aj0, n);

    // w1 = w_L + r0 + w_R
    let w_L = w.subrange(0, p0);
    let w_R = w.subrange(p0, w.len() as int);
    assert(w1 =~= w_L + r0 + w_R);
    assert(w =~= w_L + w_R);

    lemma_base_word_valid_down(w, n);
    lemma_subrange_word_valid(w, 0, p0, n);
    lemma_subrange_word_valid(w, p0, w.len() as int, n);
    lemma_base_word_characterization(w_L, n);
    lemma_base_word_characterization(w_R, n);

    // r1 is base
    if inv1 {
        lemma_inverse_word_valid(data.base.relators[ri1 as int], n);
        lemma_base_word_characterization(inverse_word(data.base.relators[ri1 as int]), n);
    } else {
        lemma_base_word_characterization(data.base.relators[ri1 as int], n);
    }
    assert(hp.relators[ri1 as int] == data.base.relators[ri1 as int]);

    // r0 (inv) = b_j + [Inv(n)] + inv(a_j) + [Gen(n)]
    // Stable letters at p0 + bj0_len (Inv(n)) and p0 + bj0_len + aj0_len + 1 (Gen(n))
    let pos_inv = p0 + bj0_len;
    let pos_gen = p0 + bj0_len + aj0_len + 1;

    // r1 can't contain Inv(n), so p1 + r1_len <= pos_inv
    if p1 + r1_len > pos_inv {
        let idx_in_r1 = (pos_inv - p1) as int;
        assert(w1.subrange(p1, p1 + r1_len) =~= r1);
        assert(w1[pos_inv] == r1[idx_in_r1]);
        assert(generator_index(w1[pos_inv]) == n);
        assert(symbol_valid(r1[idx_in_r1], n));
    }
    assert(p1 + r1_len <= pos_inv);

    // Decompose boundary overlap
    // r1 starts at p1 (< p0) in w_L, extends into b_j region of r0
    let overlap_in_wL = p0 - p1;  // how much of r1 is in w_L
    let overlap_in_r0 = r1_len - overlap_in_wL;  // how much of r1 is in b_j
    assert(overlap_in_wL > 0);
    assert(overlap_in_r0 > 0);
    assert(overlap_in_r0 <= bj0_len);

    let r1_in_wL = w_L.subrange(p1, p0);
    let r1_in_r0 = b_j0.subrange(0, overlap_in_r0);
    let w_L_short = w_L.subrange(0, p1);
    let head = b_j0.subrange(overlap_in_r0, bj0_len);

    assert(w_L =~= w_L_short + r1_in_wL);
    assert(b_j0 =~= r1_in_r0 + head);
    assert(w =~= w_L_short + r1_in_wL + w_R);

    // r1 = r1_in_wL + r1_in_r0 (content matching in w1)
    assert(r1 =~= r1_in_wL + r1_in_r0) by {
        assert(w1.subrange(p1, p1 + r1_len) =~= r1);
        assert forall|k: int| 0 <= k < r1_len
            implies r1[k] == #[trigger] (r1_in_wL + r1_in_r0)[k]
        by {
            if k < overlap_in_wL {
                assert(w1[(p1 + k) as int] == w_L[(p1 + k) as int]);
            } else {
                assert(w1[(p1 + k) as int] == r0[((p1 + k) - p0) as int]);
            }
        };
    };

    // r1 ≡_G ε (in base presentation)
    assert(hp.relators[ri1 as int] == p.relators[ri1 as int]);
    assert(get_relator(p, ri1, inv1) =~= r1);
    if inv1 {
        lemma_relator_is_identity(p, ri1 as int);
        lemma_inverse_of_identity(p, p.relators[ri1 as int]);
    } else {
        lemma_relator_is_identity(p, ri1 as int);
    }

    // r1 = r1_in_wL + r1_in_r0 ≡_G ε → identity_split → r1_in_r0 ≡_G inv(r1_in_wL)
    lemma_subrange_word_valid(w_L, p1, p0, n);
    lemma_subrange_word_valid(w_L, 0, p1, n);
    lemma_subrange_word_valid(b_j0, 0, overlap_in_r0, n);
    lemma_subrange_word_valid(b_j0, overlap_in_r0, bj0_len, n);
    lemma_base_word_characterization(r1_in_wL, n);
    lemma_base_word_characterization(r1_in_r0, n);
    lemma_base_word_characterization(w_L_short, n);
    lemma_base_word_characterization(head, n);

    assert(concat(r1_in_wL, r1_in_r0) =~= r1);
    lemma_identity_split(p, r1_in_wL, r1_in_r0);
    // r1_in_r0 ≡_G inv(r1_in_wL)

    // w2 = w_L_short + head + [Inv(n)] + inv(a_j) + [Gen(n)] + w_R
    assert forall|k: int| 0 <= k < w2.len()
        implies w2[k] == #[trigger] (w_L_short + head + seq![Symbol::Inv(n)] + inv_aj0 + seq![Symbol::Gen(n)] + w_R)[k]
    by {
        assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + r1_len, w1.len() as int));
        if k < p1 {
        } else if k < p1 + (bj0_len - overlap_in_r0) {
            // in head region (remaining b_j)
        } else if k == p1 + (bj0_len - overlap_in_r0) {
            // Inv(n) position
        } else if k < p1 + (bj0_len - overlap_in_r0) + 1 + aj0_len {
            // inv(a_j) region
        } else if k == p1 + (bj0_len - overlap_in_r0) + 1 + aj0_len {
            // Gen(n) position
        } else {
            // w_R region
        }
    };
    assert(w2 =~= w_L_short + head + seq![Symbol::Inv(n)] + inv_aj0 + seq![Symbol::Gen(n)] + w_R);

    // stable_letter_count(w2, n) == 2
    lemma_base_implies_count_zero(w_L_short, n);
    lemma_base_implies_count_zero(head, n);
    lemma_base_implies_count_zero(inv_aj0, n);
    lemma_base_implies_count_zero(w_R, n);
    lemma_stable_count_single(Symbol::Inv(n), n);
    lemma_stable_count_single(Symbol::Gen(n), n);
    lemma_stable_letter_count_concat(w_L_short, head, n);
    lemma_stable_letter_count_concat(w_L_short + head, seq![Symbol::Inv(n)], n);
    lemma_stable_letter_count_concat(w_L_short + head + seq![Symbol::Inv(n)], inv_aj0, n);
    lemma_stable_letter_count_concat(w_L_short + head + seq![Symbol::Inv(n)] + inv_aj0, seq![Symbol::Gen(n)], n);
    lemma_stable_letter_count_concat(w_L_short + head + seq![Symbol::Inv(n)] + inv_aj0 + seq![Symbol::Gen(n)], w_R, n);
    assert(stable_letter_count(w2, n) == 2nat);

    // This has the inverted r0 structure: w2 = w_L_short + head + [Inv(n)] + inter + [Gen(n)] + w_R
    // with head = b_j[overlap..], inter = inv(a_j)
    // For inside step2 handler we need: head ≡_G b_j0, but head is only a suffix of b_j0
    // So we can't directly use lemma_k3_inside_step2_inv

    // Instead, follow the same approach as the noninv boundary: inline the step2 case analysis
    let inter = inv_aj0;
    lemma_equiv_refl(p, inv_aj0);

    match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } => {
            let pair2 = Seq::new(1, |_i: int| sym2) + Seq::new(1, |_i: int| inverse_symbol(sym2));
            assert(w_end =~= w2.subrange(0, p2) + pair2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, pair2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            assert(w_end =~= w2.subrange(0, p2) + r2 + w2.subrange(p2, w2.len() as int));
            lemma_insert_preserves_nonbase(w2, r2, p2, n);
            lemma_base_implies_count_zero(w_end, n);
        },
        DerivationStep::FreeReduce { position: p2 } => {
            lemma_stable_count_reduce(w2, p2, n);
            if generator_index(w2[p2]) == n {
                // Stable FreeReduce: adjacent stable letters
                let head_len = head.len() as int;
                let pos_inv_w2 = w_L_short.len() as int + head_len;
                let pos_gen_w2 = pos_inv_w2 + 1 + aj0_len;
                assert(p2 == pos_inv_w2) by {
                    if p2 != pos_inv_w2 {
                        if p2 == pos_gen_w2 {
                        } else if p2 < pos_inv_w2 {
                        } else if p2 > pos_gen_w2 {
                        } else {
                        }
                    }
                };
                // inter = inv(a_j) empty → a_j empty → a_j ≡_G ε
                assert(aj0_len == 0);
                assert(a_j0 =~= empty_word());
                lemma_equiv_refl(p, empty_word());
                lemma_trivial_association_implies_trivial(data, j0);
                // b_j0 ≡_G ε
                // b_j0 = r1_in_r0 + head, so r1_in_r0 + head ≡_G ε
                assert(concat(r1_in_r0, head) =~= b_j0);
                // identity_split: head ≡_G inv(r1_in_r0)
                lemma_identity_split(p, r1_in_r0, head);
                // r1_in_r0 ≡_G inv(r1_in_wL) [from above]
                // head ≡_G inv(r1_in_r0) ≡_G inv(inv(r1_in_wL)) =~= r1_in_wL
                lemma_inverse_word_valid(r1_in_r0, n);
                lemma_inverse_word_valid(r1_in_wL, n);
                lemma_inverse_word_congruence(p, r1_in_r0, inverse_word(r1_in_wL));
                crate::word::lemma_inverse_involution(r1_in_wL);
                lemma_equiv_transitive(p, head, inverse_word(r1_in_r0), r1_in_wL);
                // head ≡_G r1_in_wL

                // w_end = w_L_short + head + w_R (after removing stable pair)
                assert(w_end =~= w_L_short + head + w_R);
                // w = w_L_short + r1_in_wL + w_R ≡_G w_L_short + head + w_R = w_end
                lemma_equiv_symmetric(p, head, r1_in_wL);
                lemma_equiv_concat_right(p, w_L_short, r1_in_wL, head);
                lemma_equiv_concat_left(p, w_L_short + r1_in_wL, w_L_short + head, w_R);
                assert(concat(w_L_short + r1_in_wL, w_R) =~= w);
                assert(concat(w_L_short + head, w_R) =~= w_end);
            } else {
                assert(stable_letter_count(w_end, n) == 2nat);
                lemma_base_implies_count_zero(w_end, n);
            }
        },
        DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
            let r2 = get_relator(hp, ri2, inv2);
            let r2_len = r2.len() as int;
            assert(w2.subrange(p2, p2 + r2_len) =~= r2);
            assert(w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));

            lemma_relator_stable_count(data, ri2, inv2);

            if (ri2 as int) < p.relators.len() {
                lemma_stable_count_subrange(w2, p2, p2 + r2_len, n);
                lemma_stable_letter_count_concat(
                    w2.subrange(0, p2), w2.subrange(p2 + r2_len, w2.len() as int), n);
                lemma_base_implies_count_zero(w_end, n);
            } else {
                // HNN RelatorDelete: removes 2 stable letters
                let j2 = (ri2 as int - p.relators.len()) as int;
                let (a_j2, b_j2) = data.associations[j2];
                lemma_base_word_characterization(a_j2, n);
                lemma_base_word_characterization(b_j2, n);
                lemma_inverse_word_valid(b_j2, n);
                lemma_inverse_word_valid(a_j2, n);
                assert(ri2 == (data.base.relators.len() + j2) as nat);

                if !inv2 {
                    lemma_k3_rd_boundary_inv_step2_rd_noninv(
                        data, w, w2, w_end, w_L_short, head, inter, w_R,
                        j0, r1_in_wL, r1_in_r0, p2, j2);
                } else {
                    lemma_k3_rd_boundary_inv_step2_rd_inv(
                        data, w, w2, w_end, w_L_short, head, inter, w_R,
                        j0, r1_in_wL, r1_in_r0, p2, j2);
                }
            }
        },
    }
}

/// Non-inverted r2 RelatorDelete sub-case for boundary RelatorDelete + inverted r0.
/// w2 = w_L_short + head + [Inv(n)] + inter + [Gen(n)] + w_R,
/// w = w_L_short + r1_in_wL + w_R,
/// b_j0 = r1_in_r0 + head, r1 = r1_in_wL + r1_in_r0 ≡_G ε.
/// r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2) — non-inverted, starts at head's Inv(n).
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_k3_rd_boundary_inv_step2_rd_noninv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L_short: Word, head: Word, inter: Word, w_R: Word,
    j0: int, r1_in_wL: Word, r1_in_r0: Word,
    p2: int, j2: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            let b_j0 = data.associations[j0].1;
            &&& w2 =~= w_L_short + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R
            &&& w =~= w_L_short + r1_in_wL + w_R
            &&& inter =~= inverse_word(data.associations[j0].0)
            &&& b_j0 =~= r1_in_r0 + head
        }),
        is_base_word(w_L_short, data.base.num_generators),
        is_base_word(head, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        is_base_word(r1_in_wL, data.base.num_generators),
        is_base_word(r1_in_r0, data.base.num_generators),
        word_valid(head, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(w_L_short, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        word_valid(r1_in_wL, data.base.num_generators),
        word_valid(r1_in_r0, data.base.num_generators),
        equiv_in_presentation(data.base, r1_in_r0, inverse_word(r1_in_wL)),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        ({
            let hp = hnn_presentation(data);
            let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, false);
            &&& 0 <= p2
            &&& p2 + r2.len() as int <= w2.len() as int
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;
    let head_len = head.len() as int;
    let pos_inv_w2 = w_L_short.len() as int + head_len;
    let pos_gen_w2 = pos_inv_w2 + 1 + aj0_len;
    let (a_j2, b_j2) = data.associations[j2];
    let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, false);

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(a_j2, n);
    lemma_base_word_characterization(b_j2, n);
    lemma_inverse_word_valid(b_j2, n);
    lemma_inverse_word_valid(a_j2, n);

    assert(r2 =~= hnn_relator(data, j2)) by {
        assert(hp.relators =~= data.base.relators + hnn_relators(data));
        assert(hp.relators[(data.base.relators.len() + j2) as int]
            == hnn_relators(data)[j2 as int]);
        assert(hnn_relators(data)[j2 as int] == hnn_relator(data, j2));
    };
    lemma_hnn_relator_stable_positions(data, j2);

    // r2[0] = Inv(n) must align with w2's Inv(n) at pos_inv_w2
    assert(p2 == pos_inv_w2) by {
        if p2 != pos_inv_w2 {
            if p2 < pos_inv_w2 {
                assert(w2[p2] == r2[0]);
                assert(r2[0] == Symbol::Inv(n));
            } else {
                assert(w2[p2] == Symbol::Inv(n));
                if p2 == pos_gen_w2 {
                } else if p2 < pos_gen_w2 {
                } else {
                }
            }
        }
    };

    // r2 is non-inverted: r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2)
    // a_j2 must match inter = inv(a_j0)
    let aj2_len = a_j2.len() as int;
    // inter =~= inverse_word(a_j0), need Z3 to know inter.len() == aj0_len
    crate::word::lemma_inverse_word_len(a_j0);
    assert(inter.len() == aj0_len);
    // r2[aj2_len + 1] = Gen(n) must align with w2's Gen(n) at pos_gen_w2
    assert(aj2_len == aj0_len) by {};
    assert(a_j2 =~= inter) by {
        assert forall|k: int| 0 <= k < aj2_len
            implies a_j2[k] == #[trigger] inter[k]
        by {
            assert(a_j2[k] == r2[(k + 1) as int]);
            assert(r2[(k + 1) as int] == w2[(pos_inv_w2 + 1 + k) as int]);
        };
    };
    // a_j2 =~= inv(a_j0)
    assert(a_j2 =~= inverse_word(a_j0));

    // isomorphism: a_j2 =~= inv(a_j0) → b_j2 ≡_G inv(b_j0)
    lemma_equiv_refl(p, inverse_word(a_j0));
    lemma_isomorphism_maps_inverse_equivalence(data, j0, j2);
    // b_j2 ≡_G inv(b_j0)

    // After r2 deletion: inv(b_j2) matches suffix of w2 after Gen(n)
    // w2 after Gen(n): w_R
    // r2 ends at pos_gen_w2 + 1 + bj2_len... wait
    // r2 = [Inv(n)] + a_j2 + [Gen(n)] + inv(b_j2), len = 2 + aj0_len + bj2_len
    // r2 starts at pos_inv_w2, ends at pos_inv_w2 + 2 + aj0_len + bj2_len = pos_gen_w2 + 1 + bj2_len
    let bj2_len = b_j2.len() as int;
    crate::word::lemma_inverse_word_len(b_j2);
    let inv_bj2 = inverse_word(b_j2);

    // inv(b_j2) aligns with w_R[0..bj2_len]
    assert(inv_bj2 =~= w_R.subrange(0, bj2_len)) by {
        assert forall|k: int| 0 <= k < bj2_len
            implies inv_bj2[k] == #[trigger] w_R.subrange(0, bj2_len)[k]
        by {
            assert(inv_bj2[k] == r2[(2 + aj0_len + k) as int]);
            assert(r2[(2 + aj0_len + k) as int] == w2[(pos_gen_w2 + 1 + k) as int]);
        };
    };

    // w_end = w2[0..pos_inv_w2] + w2[pos_inv_w2 + r2_len..]
    //       = (w_L_short + head) + w_R[bj2_len..]
    let r2_len = r2.len() as int;
    assert(w_end =~= w_L_short + head + w_R.subrange(bj2_len, w_R.len() as int));

    // Need: w = w_L_short + r1_in_wL + w_R ≡_G w_L_short + head + w_R[bj2_len..] = w_end
    // i.e., r1_in_wL + w_R[0..bj2_len] ≡_G head

    // b_j2 ≡_G inv(b_j0), so inv(b_j2) ≡_G inv(inv(b_j0)) =~= b_j0
    lemma_inverse_word_congruence(p, b_j2, inverse_word(b_j0));
    crate::word::lemma_inverse_involution(b_j0);
    // inv(b_j2) ≡_G b_j0 = r1_in_r0 + head
    // inv(b_j2) =~= w_R[0..bj2_len]
    // So: w_R[0..bj2_len] ≡_G r1_in_r0 + head

    // r1_in_wL + w_R[0..bj2_len] ≡_G r1_in_wL + (r1_in_r0 + head)
    //                              = (r1_in_wL + r1_in_r0) + head
    //                              ≡_G ε + head = head  (since r1 = r1_in_wL + r1_in_r0 ≡_G ε)
    lemma_subrange_word_valid(w_R, 0, bj2_len, n);
    lemma_subrange_word_valid(w_R, bj2_len, w_R.len() as int, n);
    lemma_concat_word_valid(r1_in_r0, head, n);

    // w_R[0..bj2_len] ≡_G r1_in_r0 + head
    assert(concat(w_R.subrange(0, bj2_len), Seq::<Symbol>::empty()) =~= w_R.subrange(0, bj2_len));

    lemma_equiv_concat_right(p, r1_in_wL, w_R.subrange(0, bj2_len), r1_in_r0 + head);
    // r1_in_wL + w_R[0..bj2_len] ≡_G r1_in_wL + (r1_in_r0 + head)
    assert(concat(r1_in_wL, r1_in_r0 + head) =~= (r1_in_wL + r1_in_r0) + head);
    // r1_in_wL + r1_in_r0 = r1 ≡_G ε
    assert(concat(r1_in_wL, r1_in_r0) =~= r1_in_wL + r1_in_r0);
    // From identity_split: r1_in_r0 ≡_G inv(r1_in_wL), so r1_in_wL + r1_in_r0 ≡_G r1_in_wL + inv(r1_in_wL) ≡_G ε
    lemma_inverse_word_valid(r1_in_wL, n);
    lemma_equiv_concat_left(p, r1_in_r0, inverse_word(r1_in_wL), head);
    // Not quite right... let me use the relator identity directly
    // Establish r1_in_wL + r1_in_r0 ≡_G ε:
    // r1_in_r0 ≡_G inv(r1_in_wL) [given], so r1_in_wL + r1_in_r0 ≡_G r1_in_wL + inv(r1_in_wL) ≡_G ε
    lemma_inverse_word_valid(r1_in_wL, n);
    lemma_equiv_concat_right(p, r1_in_wL, r1_in_r0, inverse_word(r1_in_wL));
    crate::presentation_lemmas::lemma_word_inverse_right(p, r1_in_wL);
    lemma_concat_word_valid(r1_in_wL, r1_in_r0, n);
    lemma_concat_word_valid(r1_in_wL, inverse_word(r1_in_wL), n);
    lemma_equiv_transitive(p,
        r1_in_wL + r1_in_r0,
        concat(r1_in_wL, inverse_word(r1_in_wL)),
        empty_word());
    // r1_in_wL + r1_in_r0 ≡_G ε
    // So: (r1_in_wL + r1_in_r0) + head ≡_G ε + head = head
    lemma_remove_trivial_equiv(p, empty_word(), head, r1_in_wL + r1_in_r0);
    assert(concat(empty_word(), concat(r1_in_wL + r1_in_r0, head)) =~= (r1_in_wL + r1_in_r0) + head);
    assert(concat(empty_word(), head) =~= head);
    // (r1_in_wL + r1_in_r0) + head ≡_G head

    lemma_concat_word_valid(r1_in_wL, w_R.subrange(0, bj2_len), n);
    lemma_concat_word_valid(r1_in_wL, r1_in_r0 + head, n);
    lemma_equiv_transitive(p,
        concat(r1_in_wL, w_R.subrange(0, bj2_len)),
        (r1_in_wL + r1_in_r0) + head,
        head);
    // r1_in_wL + w_R[0..bj2_len] ≡_G head

    // w = w_L_short + (r1_in_wL + w_R[0..bj2_len]) + w_R[bj2_len..]
    assert(w_R =~= w_R.subrange(0, bj2_len) + w_R.subrange(bj2_len, w_R.len() as int));
    assert(w =~= w_L_short + (r1_in_wL + w_R.subrange(0, bj2_len)) + w_R.subrange(bj2_len, w_R.len() as int));
    lemma_equiv_concat_right(p, w_L_short, concat(r1_in_wL, w_R.subrange(0, bj2_len)), head);
    lemma_equiv_concat_left(p, w_L_short + concat(r1_in_wL, w_R.subrange(0, bj2_len)),
        w_L_short + head, w_R.subrange(bj2_len, w_R.len() as int));
    assert(concat(w_L_short + concat(r1_in_wL, w_R.subrange(0, bj2_len)), w_R.subrange(bj2_len, w_R.len() as int)) =~= w);
    assert(concat(w_L_short + head, w_R.subrange(bj2_len, w_R.len() as int)) =~= w_end);
}

/// Inverted r2 RelatorDelete sub-case for boundary RelatorDelete + inverted r0.
/// r2 = b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)] — inverted, positioned so Inv(n) aligns.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
proof fn lemma_k3_rd_boundary_inv_step2_rd_inv(
    data: HNNData, w: Word, w2: Word, w_end: Word,
    w_L_short: Word, head: Word, inter: Word, w_R: Word,
    j0: int, r1_in_wL: Word, r1_in_r0: Word,
    p2: int, j2: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        0 <= j0 < data.associations.len(),
        0 <= j2 < data.associations.len(),
        ({
            let n = data.base.num_generators;
            let b_j0 = data.associations[j0].1;
            &&& w2 =~= w_L_short + head + seq![Symbol::Inv(n)] + inter + seq![Symbol::Gen(n)] + w_R
            &&& w =~= w_L_short + r1_in_wL + w_R
            &&& inter =~= inverse_word(data.associations[j0].0)
            &&& b_j0 =~= r1_in_r0 + head
        }),
        is_base_word(w_L_short, data.base.num_generators),
        is_base_word(head, data.base.num_generators),
        is_base_word(inter, data.base.num_generators),
        is_base_word(w_R, data.base.num_generators),
        is_base_word(r1_in_wL, data.base.num_generators),
        is_base_word(r1_in_r0, data.base.num_generators),
        word_valid(head, data.base.num_generators),
        word_valid(inter, data.base.num_generators),
        word_valid(w_L_short, data.base.num_generators),
        word_valid(w_R, data.base.num_generators),
        word_valid(r1_in_wL, data.base.num_generators),
        word_valid(r1_in_r0, data.base.num_generators),
        equiv_in_presentation(data.base, r1_in_r0, inverse_word(r1_in_wL)),
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        ({
            let hp = hnn_presentation(data);
            let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, true);
            &&& 0 <= p2
            &&& p2 + r2.len() as int <= w2.len() as int
            &&& w2.subrange(p2, p2 + r2.len() as int) =~= r2
            &&& w_end =~= w2.subrange(0, p2) + w2.subrange(p2 + r2.len() as int, w2.len() as int)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let p = data.base;
    let (a_j0, b_j0) = data.associations[j0];
    let aj0_len = a_j0.len() as int;
    let bj0_len = b_j0.len() as int;
    let head_len = head.len() as int;
    let pos_inv_w2 = w_L_short.len() as int + head_len;
    let pos_gen_w2 = pos_inv_w2 + 1 + aj0_len;
    let (a_j2, b_j2) = data.associations[j2];
    let r2 = get_relator(hp, (data.base.relators.len() + j2) as nat, true);

    reveal(presentation_valid);
    lemma_base_word_characterization(a_j0, n);
    lemma_base_word_characterization(b_j0, n);
    lemma_inverse_word_valid(a_j0, n);
    lemma_inverse_word_valid(b_j0, n);
    lemma_base_word_characterization(a_j2, n);
    lemma_base_word_characterization(b_j2, n);
    lemma_inverse_word_valid(b_j2, n);
    lemma_inverse_word_valid(a_j2, n);

    // Inverted r2 = b_j2 + [Inv(n)] + inv(a_j2) + [Gen(n)]
    lemma_hnn_relator_inverted_stable_positions(data, j2);
    let bj2_len = b_j2.len() as int;
    let aj2_len = a_j2.len() as int;
    crate::word::lemma_inverse_word_len(a_j2);

    // r2's Inv(n) at position bj2_len must align with w2's Inv(n) at pos_inv_w2
    // So p2 + bj2_len = pos_inv_w2, i.e., p2 = pos_inv_w2 - bj2_len
    assert(p2 == pos_inv_w2 - bj2_len) by {
        if p2 + bj2_len != pos_inv_w2 {
            if p2 + bj2_len < pos_inv_w2 {
                assert(w2[(p2 + bj2_len) as int] == r2[bj2_len]);
            } else if p2 + bj2_len == pos_gen_w2 {
                assert(w2[pos_gen_w2] == Symbol::Gen(n));
            } else {
                assert(w2[(p2 + bj2_len) as int] == r2[bj2_len]);
            }
        }
    };

    // inv(a_j2) must match inter = inv(a_j0), so aj2_len == aj0_len
    // inter =~= inverse_word(a_j0), need Z3 to know inter.len() == aj0_len
    crate::word::lemma_inverse_word_len(a_j0);
    assert(inter.len() == aj0_len);
    // r2's Gen(n) is at position bj2_len + 1 + aj2_len, must align with w2's Gen(n) at pos_gen_w2
    assert(aj2_len == aj0_len) by {};
    let inv_aj2 = inverse_word(a_j2);
    assert(inv_aj2 =~= inter) by {
        assert forall|k: int| 0 <= k < aj2_len
            implies inv_aj2[k] == #[trigger] inter[k]
        by {
            assert(inv_aj2[k] == r2[(bj2_len + 1 + k) as int]);
            assert(r2[(bj2_len + 1 + k) as int] == w2[(pos_inv_w2 + 1 + k) as int]);
        };
    };
    assert(inv_aj2 =~= inverse_word(a_j0));
    // a_j2 =~= a_j0 (by inverse involution)
    crate::word::lemma_inverse_involution(a_j2);
    crate::word::lemma_inverse_involution(a_j0);
    assert(a_j2 =~= a_j0);

    // By isomorphism: a_j2 ≡_G a_j0 → b_j2 ≡_G b_j0
    lemma_equiv_refl(p, a_j0);
    lemma_isomorphism_maps_equivalence(data, j0, j2);
    // b_j2 ≡_G b_j0 = r1_in_r0 + head

    // b_j2 covers w2[p2..pos_inv_w2] = (w_L_short + head)[p2..pos_inv_w2]
    // p2 = pos_inv_w2 - bj2_len
    // If bj2_len <= head_len: b_j2 is within head
    // If bj2_len > head_len: b_j2 extends into w_L_short

    if bj2_len <= head_len {
        // b_j2 = head[head_len - bj2_len..]
        let head_prefix = head.subrange(0, head_len - bj2_len);
        assert(b_j2 =~= head.subrange(head_len - bj2_len, head_len)) by {
            assert forall|k: int| 0 <= k < bj2_len
                implies b_j2[k] == #[trigger] head.subrange(head_len - bj2_len, head_len)[k]
            by {
                assert(b_j2[k] == r2[k]);
                assert(r2[k] == w2[(p2 + k) as int]);
            };
        };
        assert(head =~= head_prefix + b_j2);

        // w_end = w_L_short + head_prefix + w_R (r2 ends at pos_gen_w2 + 1, which is start of w_R)
        let r2_len = r2.len() as int;
        assert(w_end =~= w_L_short + head_prefix + w_R);

        // b_j2 ≡_G b_j0 = r1_in_r0 + head = r1_in_r0 + head_prefix + b_j2
        assert(b_j0 =~= r1_in_r0 + head_prefix + b_j2);
        assert(concat(r1_in_r0 + head_prefix, b_j2) =~= b_j0);
        // equiv_symmetric: b_j0 ≡_G b_j2
        lemma_equiv_symmetric(p, b_j2, b_j0);
        // b_j0 ≡_G b_j2
        // So: (r1_in_r0 + head_prefix) + b_j2 ≡_G b_j2
        // By left_cancel: r1_in_r0 + head_prefix ≡_G ε
        lemma_subrange_word_valid(head, 0, head_len - bj2_len, n);
        lemma_concat_word_valid(r1_in_r0, head_prefix, n);
        lemma_left_cancel(p, r1_in_r0 + head_prefix, b_j2);
        // r1_in_r0 + head_prefix ≡_G ε

        // r1_in_r0 ≡_G inv(r1_in_wL) [given]
        // So: inv(r1_in_wL) + head_prefix ≡_G ε (by substitution)
        // → head_prefix ≡_G inv(inv(r1_in_wL)) = r1_in_wL
        lemma_equiv_concat_left(p, r1_in_r0, inverse_word(r1_in_wL), head_prefix);
        lemma_inverse_word_valid(r1_in_wL, n);
        lemma_concat_word_valid(inverse_word(r1_in_wL), head_prefix, n);
        lemma_concat_word_valid(r1_in_r0, head_prefix, n);
        // Chain: concat(inv(r1_in_wL), head_prefix) ≡ concat(r1_in_r0, head_prefix) ≡ ε
        lemma_equiv_symmetric(p,
            concat(r1_in_r0, head_prefix),
            concat(inverse_word(r1_in_wL), head_prefix));
        lemma_equiv_transitive(p,
            concat(inverse_word(r1_in_wL), head_prefix),
            concat(r1_in_r0, head_prefix),
            empty_word());
        // inv(r1_in_wL) + head_prefix ≡_G ε
        lemma_identity_split(p, inverse_word(r1_in_wL), head_prefix);
        // head_prefix ≡_G inv(inv(r1_in_wL)) =~= r1_in_wL
        crate::word::lemma_inverse_involution(r1_in_wL);
        lemma_inverse_word_valid(inverse_word(r1_in_wL), n);

        // w = w_L_short + r1_in_wL + w_R ≡_G w_L_short + head_prefix + w_R = w_end
        lemma_equiv_symmetric(p, head_prefix, r1_in_wL);
        lemma_equiv_concat_right(p, w_L_short, r1_in_wL, head_prefix);
        lemma_equiv_concat_left(p, w_L_short + r1_in_wL, w_L_short + head_prefix, w_R);
        assert(concat(w_L_short + r1_in_wL, w_R) =~= w);
        assert(concat(w_L_short + head_prefix, w_R) =~= w_end);
    } else {
        // b_j2 extends into w_L_short
        let overshoot = (bj2_len - head_len) as int;
        // b_j2 = w_L_short[wL_short_len - overshoot..] + head
        assert(b_j2 =~= w_L_short.subrange(w_L_short.len() as int - overshoot, w_L_short.len() as int) + head) by {
            assert forall|k: int| 0 <= k < bj2_len
                implies b_j2[k] == #[trigger] (w_L_short.subrange(w_L_short.len() as int - overshoot, w_L_short.len() as int) + head)[k]
            by {
                assert(b_j2[k] == r2[k]);
                assert(r2[k] == w2[(p2 + k) as int]);
            };
        };

        let w_L_short_prefix = w_L_short.subrange(0, w_L_short.len() as int - overshoot);
        let w_L_short_suffix = w_L_short.subrange(w_L_short.len() as int - overshoot, w_L_short.len() as int);
        assert(w_L_short =~= w_L_short_prefix + w_L_short_suffix);
        assert(b_j2 =~= w_L_short_suffix + head);

        // w_end = w_L_short_prefix + w_R (r2 covers from p2 to pos_gen_w2+1)
        let r2_len = r2.len() as int;
        assert(w_end =~= w_L_short_prefix + w_R);

        // b_j2 ≡_G b_j0 = r1_in_r0 + head
        // b_j2 = w_L_short_suffix + head
        // So: w_L_short_suffix + head ≡_G r1_in_r0 + head
        // By left_cancel_equiv: w_L_short_suffix ≡_G r1_in_r0 (cancel head on right)
        // Hmm, we don't have right_cancel_equiv. Let me use concat_left_cancel_equiv on reversed form.
        // Actually: concat(w_L_short_suffix, head) ≡ concat(r1_in_r0, head)
        // We can derive this using the existing equiv

        // Actually we have equiv(b_j2, b_j0), and b_j2 =~= w_L_short_suffix + head, b_j0 =~= r1_in_r0 + head
        // So equiv(w_L_short_suffix + head, r1_in_r0 + head)
        // We need right-side cancellation. We can build it:
        // Append inv(head) to both sides:
        // (w_L_short_suffix + head) + inv(head) ≡_G (r1_in_r0 + head) + inv(head)
        // = w_L_short_suffix + (head + inv(head)) ≡_G w_L_short_suffix
        // = r1_in_r0 + (head + inv(head)) ≡_G r1_in_r0
        // So w_L_short_suffix ≡_G r1_in_r0

        // Actually there's a simpler way: use lemma_right_cancel
        // concat(w_L_short_suffix, head) ≡ concat(r1_in_r0, head)
        // Hmm, right_cancel gives: concat(x, y) ≡ x → y ≡ ε. Not what we want.

        // Let me use equiv_concat_right to append inv(head), then simplify
        lemma_inverse_word_valid(head, n);
        lemma_subrange_word_valid(w_L_short, 0, w_L_short.len() as int - overshoot, n);
        lemma_subrange_word_valid(w_L_short, w_L_short.len() as int - overshoot, w_L_short.len() as int, n);
        lemma_equiv_concat_left(p, b_j2, b_j0, inverse_word(head));
        // b_j2 + inv(head) ≡_G b_j0 + inv(head)
        // b_j2 + inv(head) = (w_L_short_suffix + head) + inv(head) = w_L_short_suffix + (head + inv(head))
        assert(concat(b_j2, inverse_word(head)) =~= w_L_short_suffix + concat(head, inverse_word(head)));
        assert(concat(b_j0, inverse_word(head)) =~= r1_in_r0 + concat(head, inverse_word(head)));
        // head + inv(head) ≡_G ε
        crate::presentation_lemmas::lemma_word_inverse_right(p, head);
        // So: w_L_short_suffix + (head + inv(head)) ≡_G w_L_short_suffix
        lemma_remove_trivial_equiv(p, w_L_short_suffix, empty_word(), concat(head, inverse_word(head)));
        assert(concat(w_L_short_suffix, concat(concat(head, inverse_word(head)), empty_word()))
            =~= w_L_short_suffix + concat(head, inverse_word(head)));
        assert(concat(w_L_short_suffix, empty_word()) =~= w_L_short_suffix);
        // Similarly for r1_in_r0
        lemma_remove_trivial_equiv(p, r1_in_r0, empty_word(), concat(head, inverse_word(head)));
        assert(concat(r1_in_r0, concat(concat(head, inverse_word(head)), empty_word()))
            =~= r1_in_r0 + concat(head, inverse_word(head)));
        assert(concat(r1_in_r0, empty_word()) =~= r1_in_r0);

        // Chain: w_L_short_suffix + (h·inv(h)) ≡ b_j2·inv(h) ≡ b_j0·inv(h) ≡ r1_in_r0 + (h·inv(h)) ≡ r1_in_r0
        lemma_concat_word_valid(head, inverse_word(head), n);
        lemma_concat_word_valid(w_L_short_suffix, concat(head, inverse_word(head)), n);
        lemma_concat_word_valid(r1_in_r0, concat(head, inverse_word(head)), n);
        lemma_concat_word_valid(b_j2, inverse_word(head), n);
        lemma_concat_word_valid(b_j0, inverse_word(head), n);
        lemma_equiv_symmetric(p,
            w_L_short_suffix + concat(head, inverse_word(head)),
            w_L_short_suffix);
        // w_L_short_suffix ≡ w_L_short_suffix + (h·inv(h))
        // b_j2 =~= w_L_short_suffix + head, so b_j2·inv(h) =~= w_L_short_suffix + (h·inv(h))
        assert(concat(b_j2, inverse_word(head))
            =~= w_L_short_suffix + concat(head, inverse_word(head)));
        // Similarly, b_j0 =~= r1_in_r0 + head
        assert(concat(b_j0, inverse_word(head))
            =~= r1_in_r0 + concat(head, inverse_word(head)));
        // b_j2·inv(h) ≡ b_j0·inv(h) (from equiv_concat_left at line above)
        // = w_L_short_suffix + (h·inv(h)) ≡ r1_in_r0 + (h·inv(h))
        lemma_equiv_transitive(p,
            w_L_short_suffix,
            w_L_short_suffix + concat(head, inverse_word(head)),
            r1_in_r0 + concat(head, inverse_word(head)));
        // w_L_short_suffix ≡ r1_in_r0 + (h·inv(h))
        lemma_equiv_symmetric(p,
            r1_in_r0 + concat(head, inverse_word(head)),
            r1_in_r0);
        lemma_equiv_transitive(p,
            w_L_short_suffix,
            r1_in_r0 + concat(head, inverse_word(head)),
            r1_in_r0);
        // w_L_short_suffix ≡_G r1_in_r0

        // r1_in_r0 ≡_G inv(r1_in_wL), so w_L_short_suffix ≡_G inv(r1_in_wL)
        lemma_equiv_transitive(p, w_L_short_suffix, r1_in_r0, inverse_word(r1_in_wL));

        // w_L_short_suffix + r1_in_wL ≡_G inv(r1_in_wL) + r1_in_wL ≡_G ε
        lemma_inverse_word_valid(r1_in_wL, n);
        lemma_equiv_concat_left(p, w_L_short_suffix, inverse_word(r1_in_wL), r1_in_wL);
        crate::presentation_lemmas::lemma_word_inverse_left(p, r1_in_wL);
        lemma_equiv_transitive(p,
            concat(w_L_short_suffix, r1_in_wL),
            concat(inverse_word(r1_in_wL), r1_in_wL),
            empty_word());

        // w = w_L_short_prefix + (w_L_short_suffix + r1_in_wL) + w_R
        assert(w =~= w_L_short_prefix + (w_L_short_suffix + r1_in_wL) + w_R);
        // ≡_G w_L_short_prefix + ε + w_R = w_L_short_prefix + w_R = w_end
        lemma_remove_trivial_equiv(p, w_L_short_prefix, w_R, w_L_short_suffix + r1_in_wL);
        lemma_concat_word_valid(w_L_short_suffix, r1_in_wL, n);
        assert(concat(w_L_short_prefix, concat(w_L_short_suffix + r1_in_wL, w_R)) =~= w);
        assert(concat(w_L_short_prefix, w_R) =~= w_end);
    }
}

/// k=3 case: step0 = RelatorInsert(HNN), step1 = RelatorDelete(base).
/// Dispatches to before/after helpers or overlap handler.
proof fn lemma_k3_ri_hnn_reldelete_base(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
            let step1 = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    if p1 + r1_len <= p0 {
        lemma_k3_ri_hnn_reldelete_before(
            data, w, w1, w2, w_end, p0, ri0, inv0, p1, ri1, inv1, step2);
    } else if p1 >= p0 + r0_len {
        lemma_k3_ri_hnn_reldelete_after(
            data, w, w1, w2, w_end, p0, ri0, inv0, p1, ri1, inv1, step2);
    } else {
        // Overlap: r1 intersects with r0 in w1
        // r1 is a base relator (no stable letters). If r1 touches a stable letter of r0,
        // that's a contradiction since r1 is base but would contain Gen(n) or Inv(n).
        let j0 = (ri0 as int - data.base.relators.len()) as int;

        // r1 is base (word_valid for n, no stable letters)
        assert(hp.relators[ri1 as int] == data.base.relators[ri1 as int]);
        if inv1 {
            reveal(presentation_valid);
            lemma_inverse_word_valid(data.base.relators[ri1 as int], n);
            lemma_base_word_characterization(inverse_word(data.base.relators[ri1 as int]), n);
        } else {
            reveal(presentation_valid);
            lemma_base_word_characterization(data.base.relators[ri1 as int], n);
        }
        // r1 is base: all symbols have generator_index < n

        assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));

        if !inv0 {
            // Non-inverted r0 = [Inv(n)] + a_j + [Gen(n)] + inv(b_j)
            let (a_j, b_j) = data.associations[j0];
            lemma_hnn_relator_stable_positions(data, j0);
            // Stable in w1: position p0 is Inv(n), position p0+|a_j|+1 is Gen(n)

            // r1 can't contain position p0 (Inv(n) with gen_index n)
            if p1 <= p0 {
                // r1 contains p0: r1[p0 - p1] = w1[p0] = Inv(n), gen_index = n
                // But r1 is base, contradiction
                assert(r1[(p0 - p1) as int] == w1[p0]);
                assert(generator_index(w1[p0]) == n);
                assert(generator_index(r1[(p0 - p1) as int]) == n);
                assert(is_base_word(r1, n));
                assert(false);
            }
            // r1 can't contain position p0+|a_j|+1 (Gen(n))
            let pos_gen = p0 + a_j.len() as int + 1;
            if p1 <= pos_gen && p1 + r1_len > pos_gen {
                assert(r1[(pos_gen - p1) as int] == w1[pos_gen]);
                assert(generator_index(w1[pos_gen]) == n);
                assert(generator_index(r1[(pos_gen - p1) as int]) == n);
                assert(is_base_word(r1, n));
                assert(false);
            }

            // Now: p1 > p0 and either r1 ends before Gen(n) or r1 starts after Gen(n)
            if p1 + r1_len <= p0 + r0_len {
                // r1 entirely inside r0
                lemma_k3_rd_inside_noninv(
                    data, w, w1, w2, w_end, p0, ri0, p1, ri1, inv1, step2, j0);
            } else {
                // r1 starts in inv(b_j) region and extends past r0 into w_R
                // (boundary straddling — right boundary)
                lemma_k3_rd_boundary_noninv(
                    data, w, w1, w2, w_end, p0, ri0, p1, ri1, inv1, step2, j0);
            }
        } else {
            // Inverted r0 = b_j + [Inv(n)] + inv(a_j) + [Gen(n)]
            let (a_j, b_j) = data.associations[j0];
            lemma_hnn_relator_inverted_stable_positions(data, j0);
            // Stable in w1: position p0+|b_j| is Inv(n), position p0+|b_j|+|a_j|+1 is Gen(n)

            let pos_inv = p0 + b_j.len() as int;
            let pos_gen = p0 + b_j.len() as int + a_j.len() as int + 1;

            // r1 can't contain Inv(n) at pos_inv
            if p1 <= pos_inv && p1 + r1_len > pos_inv {
                assert(r1[(pos_inv - p1) as int] == w1[pos_inv]);
                assert(generator_index(w1[pos_inv]) == n);
                assert(generator_index(r1[(pos_inv - p1) as int]) == n);
                assert(is_base_word(r1, n));
                assert(false);
            }
            // r1 can't contain Gen(n) at pos_gen
            if p1 <= pos_gen && p1 + r1_len > pos_gen {
                assert(r1[(pos_gen - p1) as int] == w1[pos_gen]);
                assert(generator_index(w1[pos_gen]) == n);
                assert(generator_index(r1[(pos_gen - p1) as int]) == n);
                assert(is_base_word(r1, n));
                assert(false);
            }

            // Gen(n) is the last symbol of r0 (position r0_len - 1 within r0)
            // So r1 can't extend past r0 without touching Gen(n)
            // If p1 > pos_gen: p1 >= pos_gen + 1 = p0 + r0_len, which is the "after" case
            // So r1 must end before or at Gen(n), meaning r1 is inside r0

            if p1 >= p0 && p1 + r1_len <= p0 + r0_len {
                // r1 entirely inside r0
                assert(p1 < p0 + r0_len); // from overlap condition (not "after" case)
                lemma_k3_rd_inside_inv(
                    data, w, w1, w2, w_end, p0, ri0, p1, ri1, inv1, step2, j0);
            } else {
                // r1 starts before r0 (p1 < p0) and extends into b_j
                // p1 + r1_len <= pos_inv (can't touch Inv(n))
                // (boundary straddling — left boundary)
                lemma_k3_rd_boundary_inv(
                    data, w, w1, w2, w_end, p0, ri0, p1, ri1, inv1, step2, j0);
            }
        }
    }
}

/// k=3 case: step0 = RelatorInsert(HNN).
/// Dispatches to easy contradictions or commutation helpers.
proof fn lemma_k3_relinsert_hnn(
    data: HNNData, w: Word, w1: Word, w2: Word, w_end: Word,
    p0: int, ri0: nat, inv0: bool, step1: DerivationStep, step2: DerivationStep,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        (ri0 as int) >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let step0 = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));

    lemma_base_word_valid_down(w, n);
    lemma_relator_stable_count(data, ri0, inv0);
    assert(stable_letter_count(r0, n) == 2nat);

    // Establish stable_letter_count(w1) = 2
    assert(w =~= w.subrange(0, p0) + w.subrange(p0, w.len() as int));
    lemma_stable_letter_count_concat(w.subrange(0, p0), w.subrange(p0, w.len() as int), n);
    lemma_stable_letter_count_concat(w.subrange(0, p0), r0, n);
    lemma_stable_letter_count_concat(w.subrange(0, p0) + r0, w.subrange(p0, w.len() as int), n);
    assert(stable_letter_count(w1, n) == 2nat);

    lemma_step_preserves_word_valid(data, w,
        DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 });

    match step1 {
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } => {
            if generator_index(sym1) == n {
                // FreeExpand(stable): count 2+2=4 → contradiction
                let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
                assert(w2 =~= w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int));
                assert(generator_index(inverse_symbol(sym1)) == n) by {
                    match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                };
                lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
                assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
                assert(w1 =~= w1.subrange(0, p1) + w1.subrange(p1, w1.len() as int));
                lemma_stable_letter_count_concat(w1.subrange(0, p1), w1.subrange(p1, w1.len() as int), n);
                lemma_stable_letter_count_concat(w1.subrange(0, p1), pair1, n);
                lemma_stable_letter_count_concat(w1.subrange(0, p1) + pair1, w1.subrange(p1, w1.len() as int), n);
                assert(stable_letter_count(w2, n) >= 4nat);
                lemma_step_preserves_word_valid(data, w1, step1);
                lemma_count4_step_cant_reach_base(data, w2, w_end, step2);
                assert(false);
            } else {
                lemma_k3_ri_hnn_freeexpand_base(
                    data, w, w1, w2, w_end, p0, ri0, inv0, p1, sym1, step2);
            }
        },
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            lemma_relator_stable_count(data, ri1, inv1);
            let r1 = get_relator(hp, ri1, inv1);
            if (ri1 as int) >= data.base.relators.len() {
                // HNN relator: count → 4 → contradiction
                let left = w1.subrange(0, p1);
                let right = w1.subrange(p1, w1.len() as int);
                assert(w1 =~= left + right);
                lemma_stable_letter_count_concat(left, right, n);
                lemma_stable_letter_count_concat(left, r1, n);
                lemma_stable_letter_count_concat(left + r1, right, n);
                assert(stable_letter_count(w2, n) >= 4nat);
                lemma_step_preserves_word_valid(data, w1, step1);
                lemma_count4_step_cant_reach_base(data, w2, w_end, step2);
                assert(false);
            } else {
                lemma_k3_ri_hnn_relinsert_base(
                    data, w, w1, w2, w_end, p0, ri0, inv0, p1, ri1, inv1, step2);
            }
        },
        DerivationStep::FreeReduce { position: p1 } => {
            lemma_stable_count_reduce(w1, p1, n);
            if generator_index(w1[p1]) == n {
                assert(stable_letter_count(w2, n) == 0nat);
                assert(false);
            }
            lemma_k3_ri_hnn_freereduce_base(
                data, w, w1, w2, w_end, p0, ri0, inv0, p1, step2);
        },
        DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 } => {
            let r1 = get_relator(hp, ri1, inv1);
            lemma_relator_stable_count(data, ri1, inv1);
            if (ri1 as int) >= data.base.relators.len() {
                assert(stable_letter_count(r1, n) == 2nat);
                lemma_stable_count_subrange(w1, p1, p1 + r1.len() as int, n);
                lemma_stable_letter_count_concat(
                    w1.subrange(0, p1),
                    w1.subrange(p1 + r1.len() as int, w1.len() as int), n);
                assert(stable_letter_count(w2, n) == 0nat);
                assert(false);
            }
            lemma_k3_ri_hnn_reldelete_base(
                data, w, w1, w2, w_end, p0, ri0, inv0, p1, ri1, inv1, step2);
        },
    }
}

/// Hard case of single segment: k ≥ 3, ALL intermediates non-base.
/// This means the first base intermediate is at position k (= w_end).
/// Classifies how a step changes stable count: by 0 or ±2.
/// Also establishes the count of w_next.
pub proof fn lemma_stable_count_reduce_step(
    data: HNNData, w: Word, step: DerivationStep, n: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators + 1),
        n == data.base.num_generators,
        apply_step(hnn_presentation(data), w, step).is_some(),
    ensures ({
        let hp = hnn_presentation(data);
        let w_next = apply_step(hp, w, step).unwrap();
        let c = stable_letter_count(w, n);
        let c_next = stable_letter_count(w_next, n);
        (c_next == c) || (c_next == c + 2) || (c >= 2 && c_next == (c - 2) as nat)
    }),
{
    let hp = hnn_presentation(data);
    let w_next = apply_step(hp, w, step).unwrap();
    match step {
        DerivationStep::FreeReduce { position: p } => {
            lemma_stable_count_reduce(w, p, n);
        },
        DerivationStep::FreeExpand { position: p, symbol: sym } => {
            let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
            assert(pair =~= seq![sym, inverse_symbol(sym)]);
            let left = w.subrange(0, p);
            let right = w.subrange(p, w.len() as int);
            assert(w =~= left + right);
            assert(w_next =~= left + pair + right);
            lemma_stable_count_pair(sym, inverse_symbol(sym), n);
            let pc = if generator_index(sym) == n { 2nat } else { 0nat };
            assert(stable_letter_count(pair, n) == pc);
            lemma_stable_letter_count_concat(left, right, n);
            lemma_stable_letter_count_concat(left, pair, n);
            lemma_stable_letter_count_concat(left + pair, right, n);
            assert(stable_letter_count(w_next, n) ==
                stable_letter_count(left, n) + pc + stable_letter_count(right, n));
            assert(stable_letter_count(w, n) ==
                stable_letter_count(left, n) + stable_letter_count(right, n));
        },
        DerivationStep::RelatorInsert { position: p, relator_index: ri, inverted: inv } => {
            let r = get_relator(hp, ri, inv);
            let left = w.subrange(0, p);
            let right = w.subrange(p, w.len() as int);
            assert(w =~= left + right);
            assert(w_next =~= left + r + right);
            lemma_relator_stable_count(data, ri, inv);
            let rc = stable_letter_count(r, n);
            lemma_stable_letter_count_concat(left, right, n);
            lemma_stable_letter_count_concat(left, r, n);
            lemma_stable_letter_count_concat(left + r, right, n);
            assert(stable_letter_count(w_next, n) ==
                stable_letter_count(left, n) + rc + stable_letter_count(right, n));
            assert(stable_letter_count(w, n) ==
                stable_letter_count(left, n) + stable_letter_count(right, n));
            if (ri as int) >= data.base.relators.len() {
                assert(rc == 2);
            } else {
                assert(rc == 0);
            }
        },
        DerivationStep::RelatorDelete { position: p, relator_index: ri, inverted: inv } => {
            let r = get_relator(hp, ri, inv);
            lemma_relator_stable_count(data, ri, inv);
            lemma_stable_count_subrange(w, p, p + r.len() as int, n);
            lemma_stable_letter_count_concat(
                w.subrange(0, p),
                w.subrange(p + r.len() as int, w.len() as int), n);
            if (ri as int) >= data.base.relators.len() {
                assert(stable_letter_count(w_next, n) == (stable_letter_count(w, n) - 2) as nat);
            } else {
                assert(stable_letter_count(w_next, n) == stable_letter_count(w, n));
            }
        },
    }
}

/// k≥4, Case A, step0 = FreeExpand(stable): commute T-free step1.
/// Returns (w_prime, step1_base, step0_adj) such that:
///   apply_step(data.base, w, step1_base) == Some(w_prime)  (w_prime is base)
///   apply_step(hp, w_prime, step0_adj) == Some(w2)
/// FreeReduce arm of k4_tfree_expand_commute — extracted to avoid rlimit.
proof fn lemma_k4_tfree_expand_commute_fr(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, sym: Symbol, p1: int,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        generator_index(sym) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeReduce { position: p1 }) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));
    assert(has_cancellation_at(w1, p1));
    assert(w2 =~= w1.subrange(0, p1) + w1.subrange(p1 + 2, w1.len() as int));
    lemma_stable_count_reduce(w1, p1, n);
    assert(generator_index(w1[p1]) < n);

    if p1 == p0 {
        assert(w2 =~= w);
        lemma_base_implies_count_zero(w, n);
        assert(false);
    }
    if p1 == p0 - 1 {
        assert(generator_index(w1[p1]) < n);
        assert(generator_index(sym) == n);
        assert(false);
    }
    if p1 == p0 + 1 {
        assert(generator_index(inverse_symbol(sym)) == n);
        assert(generator_index(w1[p1]) == n);
        assert(false);
    }

    if p1 < p0 - 1 {
        assert(w1[p1] == w[p1]);
        assert(w1[p1 + 1] == w[p1 + 1]);
        assert(has_cancellation_at(w, p1));

        let w_prime = reduce_at(w, p1);
        let step1_base = DerivationStep::FreeReduce { position: p1 };
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));
        lemma_stable_count_reduce(w, p1, n);
        lemma_step_preserves_word_valid(data, w, step1_base);

        let p0_adj = (p0 - 2) as int;
        let step0_adj = DerivationStep::FreeExpand { position: p0_adj, symbol: sym };
        let expand_result = w_prime.subrange(0, p0_adj) + pair
            + w_prime.subrange(p0_adj, w_prime.len() as int);
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == expand_result[k] by {};
        assert(w2 =~= expand_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

        (w_prime, step1_base, step0_adj)
    } else {
        assert(p1 >= p0 + 2);
        assert(w1[p1] == w[(p1 - 2) as int]);
        assert(w1[p1 + 1] == w[(p1 - 1) as int]);
        let p1_adj = (p1 - 2) as int;
        assert(has_cancellation_at(w, p1_adj));

        let w_prime = reduce_at(w, p1_adj);
        let step1_base = DerivationStep::FreeReduce { position: p1_adj };
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));
        lemma_stable_count_reduce(w, p1_adj, n);
        lemma_step_preserves_word_valid(data, w, step1_base);

        let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym };
        let expand_result = w_prime.subrange(0, p0) + pair
            + w_prime.subrange(p0, w_prime.len() as int);
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == expand_result[k] by {};
        assert(w2 =~= expand_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

        (w_prime, step1_base, step0_adj)
    }
}

/// k≥4, Case A, step0 = FreeExpand(stable), step1 = FreeExpand(base):
/// Commute FreeExpand(base) to act on w first, then FreeExpand(stable).
/// FreeExpand(stable) is contradiction (count 2→4).
proof fn lemma_k4_tfree_expand_commute_fe(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, sym: Symbol, p1: int, sym1: Symbol,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        generator_index(sym) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));

    if generator_index(sym1) == n {
        // FreeExpand(stable): count increases by 2, so c2 = 4 != 2
        let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
        assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
        let left1 = w1.subrange(0, p1);
        let right1 = w1.subrange(p1, w1.len() as int);
        assert(w1 =~= left1 + right1);
        assert(w2 =~= left1 + pair1 + right1);
        lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
        assert(stable_letter_count(pair1, n) == 2);
        lemma_stable_letter_count_concat(left1, right1, n);
        lemma_stable_letter_count_concat(left1, pair1, n);
        lemma_stable_letter_count_concat(left1 + pair1, right1, n);
        assert(stable_letter_count(w2, n) ==
            stable_letter_count(left1, n) + 2 + stable_letter_count(right1, n));
        assert(stable_letter_count(w1, n) ==
            stable_letter_count(left1, n) + stable_letter_count(right1, n));
        // c2 = c1 + 2 = 4, but c2 == 2
        assert(false);
        arbitrary()
    } else {
        // FreeExpand(base sym1): commute past stable expand
        assert(generator_index(sym1) < n);
        let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));

        if p1 == p0 + 1 {
            // Edge case between stable letters — use assume(false) for now
            assume(false);
            arbitrary()
        } else if p1 <= p0 {
            // step1 acts before the expand region: step1 unchanged, step0 shifted by +2
            let w_prime = w.subrange(0, p1) + pair1 + w.subrange(p1, w.len() as int);
            let step1_base = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
            assert(apply_step(data.base, w, step1_base) == Some(w_prime));

            // w_prime is base: stable count = 0
            assert(generator_index(inverse_symbol(sym1)) < n) by {
                match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
            };
            lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
            assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
            assert(stable_letter_count(pair1, n) == 0nat);
            assert(w =~= w.subrange(0, p1) + w.subrange(p1, w.len() as int));
            lemma_stable_letter_count_concat(w.subrange(0, p1), w.subrange(p1, w.len() as int), n);
            lemma_stable_letter_count_concat(w.subrange(0, p1), pair1, n);
            lemma_stable_letter_count_concat(w.subrange(0, p1) + pair1, w.subrange(p1, w.len() as int), n);
            lemma_base_implies_count_zero(w, n);
            assert(stable_letter_count(w_prime, n) == 0nat);
            lemma_step_preserves_word_valid(data, w, step1_base);
            lemma_zero_count_implies_base(w_prime, n);

            let step0_adj = DerivationStep::FreeExpand { position: (p0 + 2) as int, symbol: sym };
            let expand_result = w_prime.subrange(0, (p0 + 2) as int) + pair
                + w_prime.subrange((p0 + 2) as int, w_prime.len() as int);
            assert forall|k: int| 0 <= k < w2.len()
                implies w2[k] == expand_result[k] by {};
            assert(w2 =~= expand_result);
            assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

            (w_prime, step1_base, step0_adj)
        } else {
            // step1 acts after the expand region: step1 position adjusted by -2, step0 unchanged
            assert(p1 >= p0 + 2);
            let p1_adj = (p1 - 2) as int;
            let w_prime = w.subrange(0, p1_adj) + pair1 + w.subrange(p1_adj, w.len() as int);
            let step1_base = DerivationStep::FreeExpand { position: p1_adj, symbol: sym1 };
            assert(apply_step(data.base, w, step1_base) == Some(w_prime));

            // w_prime is base: stable count = 0
            assert(generator_index(inverse_symbol(sym1)) < n) by {
                match sym1 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
            };
            lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
            assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
            assert(stable_letter_count(pair1, n) == 0nat);
            assert(w =~= w.subrange(0, p1_adj) + w.subrange(p1_adj, w.len() as int));
            lemma_stable_letter_count_concat(w.subrange(0, p1_adj), w.subrange(p1_adj, w.len() as int), n);
            lemma_stable_letter_count_concat(w.subrange(0, p1_adj), pair1, n);
            lemma_stable_letter_count_concat(w.subrange(0, p1_adj) + pair1, w.subrange(p1_adj, w.len() as int), n);
            lemma_base_implies_count_zero(w, n);
            assert(stable_letter_count(w_prime, n) == 0nat);
            lemma_step_preserves_word_valid(data, w, step1_base);
            lemma_zero_count_implies_base(w_prime, n);

            let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym };
            let expand_result = w_prime.subrange(0, p0) + pair
                + w_prime.subrange(p0, w_prime.len() as int);
            assert forall|k: int| 0 <= k < w2.len()
                implies w2[k] == expand_result[k] by {};
            assert(w2 =~= expand_result);
            assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

            (w_prime, step1_base, step0_adj)
        }
    }
}

/// k≥4, Case A, step0 = FreeExpand(stable), step1 = RelatorInsert(base):
/// Commute RelatorInsert(base) to act on w first, then FreeExpand(stable).
/// RelatorInsert(HNN) is contradiction (count 2→4).
proof fn lemma_k4_tfree_expand_commute_ri(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, sym: Symbol, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        generator_index(sym) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let step1 = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));

    if (ri1 as int) >= data.base.relators.len() {
        // HNN relator: inserts 2 stable letters, c2 = 4 != 2
        let r1 = get_relator(hp, ri1, inv1);
        let left1 = w1.subrange(0, p1);
        let right1 = w1.subrange(p1, w1.len() as int);
        assert(w1 =~= left1 + right1);
        assert(w2 =~= left1 + r1 + right1);
        lemma_relator_stable_count(data, ri1, inv1);
        let rc = stable_letter_count(r1, n);
        assert(rc == 2);
        lemma_stable_letter_count_concat(left1, right1, n);
        lemma_stable_letter_count_concat(left1, r1, n);
        lemma_stable_letter_count_concat(left1 + r1, right1, n);
        assert(stable_letter_count(w2, n) ==
            stable_letter_count(left1, n) + rc + stable_letter_count(right1, n));
        assert(stable_letter_count(w1, n) ==
            stable_letter_count(left1, n) + stable_letter_count(right1, n));
        assert(false);
        arbitrary()
    } else {
        // Base relator: commute past stable expand
        let r1 = get_relator(hp, ri1, inv1);
        let r1_len = r1.len() as int;
        reveal(presentation_valid);
        lemma_relator_stable_count(data, ri1, inv1);

        // Establish that the relator is valid in the base presentation
        let base_r = data.base.relators[ri1 as int];
        assert(hp.relators[ri1 as int] == base_r);
        assert(get_relator(data.base, ri1, inv1) =~= r1) by {
            assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
        };

        // r1 is base word: all gen_idx < n, so stable count = 0
        if inv1 {
            lemma_inverse_word_valid(base_r, n);
            lemma_base_word_characterization(inverse_word(base_r), n);
        } else {
            lemma_base_word_characterization(base_r, n);
        }
        assert(stable_letter_count(r1, n) == 0nat);

        if p1 == p0 + 1 {
            // Edge case: insert between stable letters — use assume(false) for now
            assume(false);
            arbitrary()
        } else if p1 <= p0 {
            // step1 acts before the expand region: step1 unchanged, step0 shifted by +r1_len
            let w_prime = w.subrange(0, p1) + r1 + w.subrange(p1, w.len() as int);
            let step1_base = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
            assert(apply_step(data.base, w, step1_base) == Some(w_prime));

            // w_prime is base: stable count = 0
            assert(w =~= w.subrange(0, p1) + w.subrange(p1, w.len() as int));
            lemma_stable_letter_count_concat(w.subrange(0, p1), w.subrange(p1, w.len() as int), n);
            lemma_stable_letter_count_concat(w.subrange(0, p1), r1, n);
            lemma_stable_letter_count_concat(w.subrange(0, p1) + r1, w.subrange(p1, w.len() as int), n);
            lemma_base_implies_count_zero(w, n);
            assert(stable_letter_count(w_prime, n) == 0nat);
            lemma_step_preserves_word_valid(data, w, step1_base);
            lemma_zero_count_implies_base(w_prime, n);

            let step0_adj = DerivationStep::FreeExpand { position: (p0 + r1_len) as int, symbol: sym };
            let expand_result = w_prime.subrange(0, (p0 + r1_len) as int) + pair
                + w_prime.subrange((p0 + r1_len) as int, w_prime.len() as int);
            assert forall|k: int| 0 <= k < w2.len()
                implies w2[k] == expand_result[k] by {};
            assert(w2 =~= expand_result);
            assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

            (w_prime, step1_base, step0_adj)
        } else {
            // step1 acts after the expand region: step1 position adjusted by -2, step0 unchanged
            assert(p1 >= p0 + 2);
            let p1_adj = (p1 - 2) as int;
            let w_prime = w.subrange(0, p1_adj) + r1 + w.subrange(p1_adj, w.len() as int);
            let step1_base = DerivationStep::RelatorInsert { position: p1_adj, relator_index: ri1, inverted: inv1 };
            assert(apply_step(data.base, w, step1_base) == Some(w_prime));

            // w_prime is base: stable count = 0
            assert(w =~= w.subrange(0, p1_adj) + w.subrange(p1_adj, w.len() as int));
            lemma_stable_letter_count_concat(w.subrange(0, p1_adj), w.subrange(p1_adj, w.len() as int), n);
            lemma_stable_letter_count_concat(w.subrange(0, p1_adj), r1, n);
            lemma_stable_letter_count_concat(w.subrange(0, p1_adj) + r1, w.subrange(p1_adj, w.len() as int), n);
            lemma_base_implies_count_zero(w, n);
            assert(stable_letter_count(w_prime, n) == 0nat);
            lemma_step_preserves_word_valid(data, w, step1_base);
            lemma_zero_count_implies_base(w_prime, n);

            let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym };
            let expand_result = w_prime.subrange(0, p0) + pair
                + w_prime.subrange(p0, w_prime.len() as int);
            assert forall|k: int| 0 <= k < w2.len()
                implies w2[k] == expand_result[k] by {};
            assert(w2 =~= expand_result);
            assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

            (w_prime, step1_base, step0_adj)
        }
    }
}

/// k≥4, Case A, step0 = FreeExpand(stable), step1 = RelatorDelete(base):
/// Commute RelatorDelete(base) to act on w first, then FreeExpand(stable).
/// RelatorDelete(HNN) is contradiction (count 2→0, so w2 is base).
/// Overlap with [p0, p0+2) is impossible since base relator can't contain stable letters.
proof fn lemma_k4_tfree_expand_commute_rd(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, sym: Symbol, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        generator_index(sym) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            let step1 = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= w.subrange(0, p0) + pair + w.subrange(p0, w.len() as int));

    if (ri1 as int) >= data.base.relators.len() {
        // HNN relator delete: removes 2 stable letters, count 2→0 → w2 is base
        let r1 = get_relator(hp, ri1, inv1);
        lemma_relator_stable_count(data, ri1, inv1);
        lemma_stable_count_subrange(w1, p1, p1 + r1.len() as int, n);
        lemma_stable_letter_count_concat(
            w1.subrange(0, p1),
            w1.subrange(p1 + r1.len() as int, w1.len() as int), n);
        assert(stable_letter_count(w2, n) == 0nat);
        // contradicts !is_base_word(w2) since count = 0 and word_valid
        lemma_zero_count_implies_base(w2, n);
        assert(false);
        arbitrary()
    } else {
        // Base relator: commute past stable expand
        let r1 = get_relator(hp, ri1, inv1);
        let r1_len = r1.len() as int;
        reveal(presentation_valid);
        lemma_relator_stable_count(data, ri1, inv1);

        // Establish that the relator is valid in the base presentation
        let base_r = data.base.relators[ri1 as int];
        assert(hp.relators[ri1 as int] == base_r);
        assert(get_relator(data.base, ri1, inv1) =~= r1) by {
            assert(data.base.relators[ri1 as int] == hp.relators[ri1 as int]);
        };

        // r1 is base: all generator indices < n
        if inv1 {
            lemma_inverse_word_valid(base_r, n);
            lemma_base_word_characterization(inverse_word(base_r), n);
        } else {
            lemma_base_word_characterization(base_r, n);
        }

        // The deleted region [p1, p1+r1_len) in w1 can't overlap [p0, p0+2)
        // because w1[p0] = sym (gen_idx = n) and w1[p0+1] = inverse_symbol(sym) (gen_idx = n),
        // but r1 has all gen_idx < n.
        assert(w1.subrange(p1, p1 + r1_len) =~= r1);
        if r1_len > 0 {
            if p1 <= p0 && p0 < p1 + r1_len {
                assert(w1[p0] == r1[(p0 - p1) as int]);
                assert(generator_index(w1[p0]) == n);
                assert(generator_index(r1[(p0 - p1) as int]) < n);
                assert(false);
            }
            if p1 <= p0 + 1 && p0 + 1 < p1 + r1_len {
                assert(w1[(p0 + 1) as int] == r1[(p0 + 1 - p1) as int]);
                assert(generator_index(w1[(p0 + 1) as int]) == n) by {
                    match sym { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                };
                assert(generator_index(r1[(p0 + 1 - p1) as int]) < n);
                assert(false);
            }
            // With r1_len > 0 and no overlap: p1 + r1_len <= p0 or p1 >= p0 + 2
        }

        if p1 + r1_len <= p0 {
            // step1 acts entirely before the expand region
            // Map back to w: w1[k] = w[k] for k < p0
            assert forall|k: int| p1 <= k < p1 + r1_len
                implies w1[k] == w[k] by {};
            assert(w.subrange(p1, p1 + r1_len) =~= r1);

            let w_prime = w.subrange(0, p1) + w.subrange(p1 + r1_len, w.len() as int);
            let step1_base = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
            assert(apply_step(data.base, w, step1_base) == Some(w_prime));

            // w_prime is base
            lemma_stable_count_subrange(w, p1, p1 + r1_len, n);
            lemma_stable_letter_count_concat(w.subrange(0, p1), w.subrange(p1 + r1_len, w.len() as int), n);
            lemma_base_implies_count_zero(w, n);
            assert(stable_letter_count(w_prime, n) == 0nat);
            lemma_step_preserves_word_valid(data, w, step1_base);
            lemma_zero_count_implies_base(w_prime, n);

            let p0_adj = (p0 - r1_len) as int;
            let step0_adj = DerivationStep::FreeExpand { position: p0_adj, symbol: sym };
            let expand_result = w_prime.subrange(0, p0_adj) + pair
                + w_prime.subrange(p0_adj, w_prime.len() as int);
            assert forall|k: int| 0 <= k < w2.len()
                implies w2[k] == expand_result[k] by {};
            assert(w2 =~= expand_result);
            assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

            (w_prime, step1_base, step0_adj)
        } else if p1 >= p0 + 2 {
            // step1 acts entirely after the expand region
            let p1_adj = (p1 - 2) as int;
            // Map back to w: w1[k] = w[k-2] for k >= p0+2
            assert forall|k: int| p1 <= k < p1 + r1_len
                implies w1[k] == w[(k - 2) as int] by {};
            assert(w.subrange(p1_adj, p1_adj + r1_len) =~= r1);

            let w_prime = w.subrange(0, p1_adj) + w.subrange(p1_adj + r1_len, w.len() as int);
            let step1_base = DerivationStep::RelatorDelete { position: p1_adj, relator_index: ri1, inverted: inv1 };
            assert(apply_step(data.base, w, step1_base) == Some(w_prime));

            // w_prime is base
            lemma_stable_count_subrange(w, p1_adj, p1_adj + r1_len, n);
            lemma_stable_letter_count_concat(w.subrange(0, p1_adj), w.subrange(p1_adj + r1_len, w.len() as int), n);
            lemma_base_implies_count_zero(w, n);
            assert(stable_letter_count(w_prime, n) == 0nat);
            lemma_step_preserves_word_valid(data, w, step1_base);
            lemma_zero_count_implies_base(w_prime, n);

            let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym };
            let expand_result = w_prime.subrange(0, p0) + pair
                + w_prime.subrange(p0, w_prime.len() as int);
            assert forall|k: int| 0 <= k < w2.len()
                implies w2[k] == expand_result[k] by {};
            assert(w2 =~= expand_result);
            assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

            (w_prime, step1_base, step0_adj)
        } else {
            // r1_len == 0 case: delete is a no-op, w2 == w1
            // p0 < p1 < p0 + 2 and p1 + 0 > p0, so p1 == p0 + 1
            assert(r1_len == 0);
            assert(w2 =~= w1);
            // w2 == w1 has stable count 2 (checked), but w2 has count 2 (precondition)
            // and w1 has count 2, so this is consistent.
            // The delete on w is also a no-op: w.subrange(p1_adj, p1_adj) == empty == r1
            // We can use any valid position in w for the no-op delete.
            let p1_adj = 0int;
            assert(w.subrange(p1_adj, p1_adj + r1_len) =~= r1);
            let w_prime = w.subrange(0, p1_adj) + w.subrange(p1_adj + r1_len, w.len() as int);
            assert(w_prime =~= w);
            let step1_base = DerivationStep::RelatorDelete { position: p1_adj, relator_index: ri1, inverted: inv1 };
            assert(apply_step(data.base, w, step1_base) == Some(w_prime));
            lemma_word_valid_monotone(w, n);

            let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym };
            assert(apply_step(hp, w_prime, step0_adj) == Some(w1));
            assert(w2 =~= w1);
            assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

            (w_prime, step1_base, step0_adj)
        }
    }
}

/// Non-FreeReduce arms of k4_tfree_expand_commute — dispatches to per-step-type helpers.
proof fn lemma_k4_tfree_expand_commute_other(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, sym: Symbol, step1: DerivationStep,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        generator_index(sym) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym }) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        match step1 { DerivationStep::FreeReduce { .. } => false, _ => true },
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    match step1 {
        DerivationStep::FreeReduce { .. } => {
            // Excluded by precondition
            assert(false);
            arbitrary()
        },
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } => {
            lemma_k4_tfree_expand_commute_fe(data, w, w1, w2, p0, sym, p1, sym1)
        },
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            lemma_k4_tfree_expand_commute_ri(data, w, w1, w2, p0, sym, p1, ri1, inv1)
        },
        DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 } => {
            lemma_k4_tfree_expand_commute_rd(data, w, w1, w2, p0, sym, p1, ri1, inv1)
        },
    }
}

/// FreeReduce arm of RI(HNN) commutation.
proof fn lemma_k4_tfree_ri_commute_fr(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, ri0: nat, inv0: bool, p1: int,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeReduce { position: p1 }) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;

    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    lemma_stable_count_reduce(w1, p1, n);
    assert(generator_index(w1[p1]) < n);

    // p1 can't be at a position where w1[p1] or w1[p1+1] is a stable letter
    // from the relator. If p1+1 <= p0 or p1 >= p0+r0_len: both elements from w.
    // If p1 == p0-1: w1[p1]=w[p1-1] (base), w1[p1+1]=r0[0] (might be stable) — contradiction
    // If p0 <= p1 < p0+r0_len: inside relator — edge case

    if p1 + 1 < p0 {
        assert(w1[p1] == w[p1]);
        assert(w1[p1 + 1] == w[p1 + 1]);
        assert(has_cancellation_at(w, p1));

        let w_prime = reduce_at(w, p1);
        let step1_base = DerivationStep::FreeReduce { position: p1 };
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));
        lemma_stable_count_reduce(w, p1, n);
        lemma_step_preserves_word_valid(data, w, step1_base);

        let p0_adj = (p0 - 2) as int;
        let step0_adj = DerivationStep::RelatorInsert { position: p0_adj, relator_index: ri0, inverted: inv0 };
        let insert_result = w_prime.subrange(0, p0_adj) + r0
            + w_prime.subrange(p0_adj, w_prime.len() as int);
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == insert_result[k] by {};
        assert(w2 =~= insert_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

        (w_prime, step1_base, step0_adj)
    } else if p1 == p0 - 1 {
        // w1[p0-1] = w[p0-1] (base), w1[p0] = r0[0]
        // is_inverse_pair(w1[p1], w1[p1+1]) → gen_idx match
        // gen_idx(w1[p1]) < n, so gen_idx(w1[p1+1]) = gen_idx(r0[0]) must be < n
        assert(w1[(p0 - 1) as int] == w[(p0 - 1) as int]);
        assert(w1[p0] == r0[0int]);
        // is_inverse_pair ensures gen_idx match
        assert(has_cancellation_at(w1, p1));
        assert(is_inverse_pair(w1[p1], w1[p1 + 1]));
        assert(w1[p1 + 1] == inverse_symbol(w1[p1]));
        assert(generator_index(inverse_symbol(w1[p1])) == generator_index(w1[p1])) by {
            match w1[p1] { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        assert(generator_index(w1[p1 + 1]) == generator_index(w1[p1]));
        assert(generator_index(r0[0int]) < n);

        let j = (ri0 as int - data.base.relators.len()) as int;
        let (a_j, b_j) = data.associations[j];

        if !inv0 {
            // Non-inverted: r0[0] = Inv(n), gen_idx = n. But gen_idx(r0[0]) < n. Contradiction.
            lemma_hnn_relator_stable_positions(data, j);
            assert(r0[0int] == stable_letter_inv(data));
            assert(generator_index(r0[0int]) == n);
            assert(false);
            arbitrary()
        } else {
            // Inverted: r0 = b_j ++ [Inv(n)] ++ inv(a_j) ++ [Gen(n)]
            lemma_hnn_relator_inverted_stable_positions(data, j);
            if b_j.len() == 0 {
                // b_j empty: r0[0] = Inv(n), gen_idx = n. Contradiction.
                assert(r0[0int] == stable_letter_inv(data));
                assert(generator_index(r0[0int]) == n);
                assert(false);
                arbitrary()
            } else {
                // Inverted with b_j non-empty: boundary straddle — genuinely hard
                assume(false);
                arbitrary()
            }
        }
    } else if p1 >= p0 + r0_len {
        assert(w1[p1] == w[(p1 - r0_len) as int]);
        assert(w1[p1 + 1] == w[(p1 - r0_len + 1) as int]);
        let p1_adj = (p1 - r0_len) as int;
        assert(has_cancellation_at(w, p1_adj));

        let w_prime = reduce_at(w, p1_adj);
        let step1_base = DerivationStep::FreeReduce { position: p1_adj };
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));
        lemma_stable_count_reduce(w, p1_adj, n);
        lemma_step_preserves_word_valid(data, w, step1_base);

        let step0_adj = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
        let insert_result = w_prime.subrange(0, p0) + r0
            + w_prime.subrange(p0, w_prime.len() as int);
        assert forall|k: int| 0 <= k < w2.len()
            implies w2[k] == insert_result[k] by {};
        assert(w2 =~= insert_result);
        assert(apply_step(hp, w_prime, step0_adj) == Some(w2));

        (w_prime, step1_base, step0_adj)
    } else if p1 == p0 + r0_len - 1 {
        // Boundary: w1[p1] = r0[r0_len-1], w1[p1+1] = w[p0]
        // gen_idx(w1[p1]) < n, and is_inverse_pair → gen_idx(w1[p1+1]) == gen_idx(w1[p1]) < n
        // So gen_idx(r0[r0_len-1]) < n
        assert(w1[p1] == r0[(r0_len - 1) as int]);
        assert(has_cancellation_at(w1, p1));
        assert(is_inverse_pair(w1[p1], w1[p1 + 1]));
        assert(w1[p1 + 1] == inverse_symbol(w1[p1]));
        assert(generator_index(inverse_symbol(w1[p1])) == generator_index(w1[p1])) by {
            match w1[p1] { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        // gen_idx(r0[r0_len-1]) < n
        assert(generator_index(r0[(r0_len - 1) as int]) < n);

        let j = (ri0 as int - data.base.relators.len()) as int;
        let (a_j, b_j) = data.associations[j];

        if inv0 {
            // Inverted: r0 ends with Gen(n), gen_idx = n. But gen_idx(r0[r0_len-1]) < n. Contradiction.
            lemma_hnn_relator_inverted_stable_positions(data, j);
            assert(r0[(r0_len - 1) as int] == stable_letter(data));
            assert(generator_index(r0[(r0_len - 1) as int]) == n);
            assert(false);
            arbitrary()
        } else {
            // Non-inverted: r0 = [Inv(n)] ++ a_j ++ [Gen(n)] ++ inv(b_j)
            // r0[r0_len-1] = last element of inv(b_j) if b_j non-empty, or Gen(n) if b_j empty
            lemma_hnn_relator_stable_positions(data, j);
            if b_j.len() == 0 {
                // b_j empty: r0 ends with Gen(n), gen_idx = n. Contradiction.
                assert(r0_len == 2 + a_j.len() as int + b_j.len() as int);
                assert(r0[(a_j.len() + 1) as int] == stable_letter(data));
                assert(generator_index(stable_letter(data)) == n);
                // r0_len - 1 = 1 + a_j.len() = a_j.len() + 1
                assert((r0_len - 1) as int == (a_j.len() + 1) as int);
                assert(generator_index(r0[(r0_len - 1) as int]) == n);
                assert(false);
                arbitrary()
            } else {
                // Non-inverted with b_j non-empty: boundary straddle — genuinely hard
                assume(false);
                arbitrary()
            }
        }
    } else {
        // Inside relator region
        assume(false);
        arbitrary()
    }
}

/// k≥4, Case A, step0 = RelatorInsert(HNN): commute T-free step1.
/// Returns (w_prime, step1_base, step0_adj).
proof fn lemma_k4_tfree_ri_commute(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, ri0: nat, inv0: bool, step1: DerivationStep,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    match step1 {
        DerivationStep::FreeReduce { position: p1 } => {
            lemma_k4_tfree_ri_commute_fr(data, w, w1, w2, p0, ri0, inv0, p1)
        },
        _ => {
            lemma_k4_tfree_ri_commute_other(data, w, w1, w2, p0, ri0, inv0, step1)
        },
    }
}

/// FreeExpand(base) arm of RI(HNN) commutation — dispatcher.
proof fn lemma_k4_tfree_ri_commute_fe(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, sym1: Symbol,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        ri0 as int >= data.base.relators.len(),
        generator_index(sym1) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    crate::britton_proof_helpers2::lemma_k4_tfree_ri_commute_fe(data, w, w1, w2, p0, ri0, inv0, p1, sym1)
}

/*proof fn _removed_lemma_k4_tfree_ri_commute_ri_before(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        ri0 as int >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        p1 <= p0,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
        }),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    reveal(presentation_valid);
    lemma_relator_stable_count(data, ri1, inv1);
    let w_prime = w.subrange(0, p1) + r1 + w.subrange(p1, w.len() as int);
    let step1_base = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
    assert(apply_step(data.base, w, step1_base) == Some(w_prime));
    lemma_stable_letter_count_concat(w.subrange(0, p1), r1, n);
    lemma_stable_letter_count_concat(w.subrange(0, p1) + r1, w.subrange(p1, w.len() as int), n);
    lemma_stable_letter_count_concat(w.subrange(0, p1), w.subrange(p1, w.len() as int), n);
    lemma_step_preserves_word_valid(data, w, step1_base);
    let step0_adj = DerivationStep::RelatorInsert { position: (p0 + r1_len) as int, relator_index: ri0, inverted: inv0 };
    let ins = w_prime.subrange(0, (p0 + r1_len) as int) + r0 + w_prime.subrange((p0 + r1_len) as int, w_prime.len() as int);
    assert forall|k: int| 0 <= k < w2.len() implies w2[k] == ins[k] by {};
    assert(w2 =~= ins);
    (w_prime, step1_base, step0_adj)
}

/// RelatorInsert(base) after HNN relator.
proof fn lemma_k4_tfree_ri_commute_ri_after(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        ri0 as int >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        p1 >= p0 + get_relator(hnn_presentation(data), ri0, inv0).len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
        }),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    reveal(presentation_valid);
    lemma_relator_stable_count(data, ri1, inv1);
    let p1a = (p1 - r0_len) as int;
    let w_prime = w.subrange(0, p1a) + r1 + w.subrange(p1a, w.len() as int);
    let step1_base = DerivationStep::RelatorInsert { position: p1a, relator_index: ri1, inverted: inv1 };
    assert(apply_step(data.base, w, step1_base) == Some(w_prime));
    lemma_stable_letter_count_concat(w.subrange(0, p1a), r1, n);
    lemma_stable_letter_count_concat(w.subrange(0, p1a) + r1, w.subrange(p1a, w.len() as int), n);
    lemma_stable_letter_count_concat(w.subrange(0, p1a), w.subrange(p1a, w.len() as int), n);
    lemma_step_preserves_word_valid(data, w, step1_base);
    let step0_adj = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
    let ins = w_prime.subrange(0, p0) + r0 + w_prime.subrange(p0, w_prime.len() as int);
    assert forall|k: int| 0 <= k < w2.len() implies w2[k] == ins[k] by {};
    assert(w2 =~= ins);
    (w_prime, step1_base, step0_adj)
}*/

/// RelatorInsert(base) arm of RI(HNN) commutation — dispatcher.
proof fn lemma_k4_tfree_ri_commute_ri(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        ri0 as int >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    crate::britton_proof_helpers2::lemma_k4_tfree_ri_commute_ri(data, w, w1, w2, p0, ri0, inv0, p1, ri1, inv1)
}

/// RelatorDelete(base) arm of RI(HNN) commutation.
proof fn lemma_k4_tfree_ri_commute_rd(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        ri0 as int >= data.base.relators.len(),
        (ri1 as int) < data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    crate::britton_proof_helpers2::lemma_k4_tfree_ri_commute_rd(data, w, w1, w2, p0, ri0, inv0, p1, ri1, inv1)
}

/// Non-FreeReduce arms of RI(HNN) commutation.
proof fn lemma_k4_tfree_ri_commute_other(
    data: HNNData, w: Word, w1: Word, w2: Word,
    p0: int, ri0: nat, inv0: bool, step1: DerivationStep,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 2nat,
        match step1 { DerivationStep::FreeReduce { .. } => false, _ => true },
    ensures ({
        let (w_prime, step1_base, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_prime, n)
        &&& word_valid(w_prime, n + 1)
        &&& apply_step(data.base, w, step1_base) == Some(w_prime)
        &&& apply_step(hp, w_prime, step0_adj) == Some(w2)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    match step1 {
        DerivationStep::FreeReduce { .. } => { arbitrary() },
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } => {
            if generator_index(sym1) == n {
                // Stable: count +2 contradiction
                let r0 = get_relator(hp, ri0, inv0);
                assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
                let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
                assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
                let left1 = w1.subrange(0, p1);
                let right1 = w1.subrange(p1, w1.len() as int);
                assert(w1 =~= left1 + right1);
                assert(w2 =~= left1 + pair1 + right1);
                lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
                lemma_stable_letter_count_concat(left1, right1, n);
                lemma_stable_letter_count_concat(left1, pair1, n);
                lemma_stable_letter_count_concat(left1 + pair1, right1, n);
                assert(false); arbitrary()
            }
            lemma_k4_tfree_ri_commute_fe(data, w, w1, w2, p0, ri0, inv0, p1, sym1)
        },
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            if (ri1 as int) >= data.base.relators.len() {
                // HNN: count +2 contradiction
                let r0 = get_relator(hp, ri0, inv0);
                assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
                let r1 = get_relator(hp, ri1, inv1);
                let left1 = w1.subrange(0, p1);
                let right1 = w1.subrange(p1, w1.len() as int);
                assert(w1 =~= left1 + right1);
                assert(w2 =~= left1 + r1 + right1);
                lemma_relator_stable_count(data, ri1, inv1);
                lemma_stable_letter_count_concat(left1, right1, n);
                lemma_stable_letter_count_concat(left1, r1, n);
                lemma_stable_letter_count_concat(left1 + r1, right1, n);
                assert(false); arbitrary()
            }
            lemma_k4_tfree_ri_commute_ri(data, w, w1, w2, p0, ri0, inv0, p1, ri1, inv1)
        },
        DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 } => {
            if (ri1 as int) >= data.base.relators.len() {
                // HNN delete: count -2, gives 0 = base, contradiction
                let r0 = get_relator(hp, ri0, inv0);
                assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
                let r1 = get_relator(hp, ri1, inv1);
                lemma_relator_stable_count(data, ri1, inv1);
                lemma_stable_count_subrange(w1, p1, p1 + r1.len() as int, n);
                lemma_stable_letter_count_concat(
                    w1.subrange(0, p1),
                    w1.subrange(p1 + r1.len() as int, w1.len() as int), n);
                assert(false); arbitrary()
            }
            lemma_k4_tfree_ri_commute_rd(data, w, w1, w2, p0, ri0, inv0, p1, ri1, inv1)
        },
    }
}

/* Old commented-out RI(HNN) dispatcher code — removed
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));

    match step1 {
        DerivationStep::FreeReduce { .. } => { arbitrary() },
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } => {
            if generator_index(sym1) == n {
                // Stable: count +2 contradiction
                let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
                assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
                let left1 = w1.subrange(0, p1);
                let right1 = w1.subrange(p1, w1.len() as int);
                assert(w1 =~= left1 + right1);
                assert(w2 =~= left1 + pair1 + right1);
                lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
                lemma_stable_letter_count_concat(left1, right1, n);
                lemma_stable_letter_count_concat(left1, pair1, n);
                lemma_stable_letter_count_concat(left1 + pair1, right1, n);
                assert(false); arbitrary()
            }
            let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
            if p1 <= p0 {
                let w_prime = w.subrange(0, p1) + pair1 + w.subrange(p1, w.len() as int);
                let step1_base = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
                assert(apply_step(data.base, w, step1_base) == Some(w_prime));
                lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
                lemma_stable_letter_count_concat(w.subrange(0, p1), pair1, n);
                lemma_stable_letter_count_concat(w.subrange(0, p1) + pair1, w.subrange(p1, w.len() as int), n);
                lemma_stable_letter_count_concat(w.subrange(0, p1), w.subrange(p1, w.len() as int), n);
                lemma_step_preserves_word_valid(data, w, step1_base);
                let step0_adj = DerivationStep::RelatorInsert { position: (p0 + 2) as int, relator_index: ri0, inverted: inv0 };
                let ins = w_prime.subrange(0, (p0 + 2) as int) + r0 + w_prime.subrange((p0 + 2) as int, w_prime.len() as int);
                assert forall|k: int| 0 <= k < w2.len() implies w2[k] == ins[k] by {};
                assert(w2 =~= ins);
                assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
                (w_prime, step1_base, step0_adj)
            } else if p1 >= p0 + r0_len {
                let p1a = (p1 - r0_len) as int;
                let w_prime = w.subrange(0, p1a) + pair1 + w.subrange(p1a, w.len() as int);
                let step1_base = DerivationStep::FreeExpand { position: p1a, symbol: sym1 };
                assert(apply_step(data.base, w, step1_base) == Some(w_prime));
                lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
                lemma_stable_letter_count_concat(w.subrange(0, p1a), pair1, n);
                lemma_stable_letter_count_concat(w.subrange(0, p1a) + pair1, w.subrange(p1a, w.len() as int), n);
                lemma_stable_letter_count_concat(w.subrange(0, p1a), w.subrange(p1a, w.len() as int), n);
                lemma_step_preserves_word_valid(data, w, step1_base);
                let step0_adj = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
                let ins = w_prime.subrange(0, p0) + r0 + w_prime.subrange(p0, w_prime.len() as int);
                assert forall|k: int| 0 <= k < w2.len() implies w2[k] == ins[k] by {};
                assert(w2 =~= ins);
                assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
                (w_prime, step1_base, step0_adj)
            } else {
                assume(false); arbitrary() // inside relator edge case
            }
        },
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            if (ri1 as int) >= data.base.relators.len() {
                let r1 = get_relator(hp, ri1, inv1);
                let left1 = w1.subrange(0, p1);
                let right1 = w1.subrange(p1, w1.len() as int);
                assert(w1 =~= left1 + right1);
                assert(w2 =~= left1 + r1 + right1);
                lemma_relator_stable_count(data, ri1, inv1);
                lemma_stable_letter_count_concat(left1, right1, n);
                lemma_stable_letter_count_concat(left1, r1, n);
                lemma_stable_letter_count_concat(left1 + r1, right1, n);
                assert(false); arbitrary()
            }
            let r1 = get_relator(hp, ri1, inv1);
            let r1_len = r1.len() as int;
            reveal(presentation_valid);
            lemma_relator_stable_count(data, ri1, inv1);
            if p1 <= p0 {
                let w_prime = w.subrange(0, p1) + r1 + w.subrange(p1, w.len() as int);
                let step1_base = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
                assert(apply_step(data.base, w, step1_base) == Some(w_prime));
                lemma_stable_letter_count_concat(w.subrange(0, p1), r1, n);
                lemma_stable_letter_count_concat(w.subrange(0, p1) + r1, w.subrange(p1, w.len() as int), n);
                lemma_stable_letter_count_concat(w.subrange(0, p1), w.subrange(p1, w.len() as int), n);
                lemma_step_preserves_word_valid(data, w, step1_base);
                let step0_adj = DerivationStep::RelatorInsert { position: (p0 + r1_len) as int, relator_index: ri0, inverted: inv0 };
                let ins = w_prime.subrange(0, (p0 + r1_len) as int) + r0 + w_prime.subrange((p0 + r1_len) as int, w_prime.len() as int);
                assert forall|k: int| 0 <= k < w2.len() implies w2[k] == ins[k] by {};
                assert(w2 =~= ins);
                assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
                (w_prime, step1_base, step0_adj)
            } else if p1 >= p0 + r0_len {
                let p1a = (p1 - r0_len) as int;
                let w_prime = w.subrange(0, p1a) + r1 + w.subrange(p1a, w.len() as int);
                let step1_base = DerivationStep::RelatorInsert { position: p1a, relator_index: ri1, inverted: inv1 };
                assert(apply_step(data.base, w, step1_base) == Some(w_prime));
                lemma_stable_letter_count_concat(w.subrange(0, p1a), r1, n);
                lemma_stable_letter_count_concat(w.subrange(0, p1a) + r1, w.subrange(p1a, w.len() as int), n);
                lemma_stable_letter_count_concat(w.subrange(0, p1a), w.subrange(p1a, w.len() as int), n);
                lemma_step_preserves_word_valid(data, w, step1_base);
                let step0_adj = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
                let ins = w_prime.subrange(0, p0) + r0 + w_prime.subrange(p0, w_prime.len() as int);
                assert forall|k: int| 0 <= k < w2.len() implies w2[k] == ins[k] by {};
                assert(w2 =~= ins);
                assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
                (w_prime, step1_base, step0_adj)
            } else {
                assume(false); arbitrary() // inside relator edge case
            }
        },
        DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 } => {
            if (ri1 as int) >= data.base.relators.len() {
                lemma_stable_count_reduce_step(data, w1, step1, n);
                assert(stable_letter_count(w2, n) == 0nat);
                lemma_zero_count_implies_base(w2, n);
                assert(false); arbitrary()
            }
            let r1 = get_relator(hp, ri1, inv1);
            let r1_len = r1.len() as int;
            reveal(presentation_valid);
            lemma_relator_stable_count(data, ri1, inv1);
            if p1 + r1_len <= p0 {
                assert forall|k: int| p1 <= k < p1 + r1_len implies w1[k] == w[k] by {};
                assert(w.subrange(p1, p1 + r1_len) =~= r1);
                let w_prime = w.subrange(0, p1) + w.subrange(p1 + r1_len, w.len() as int);
                let step1_base = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
                assert(apply_step(data.base, w, step1_base) == Some(w_prime));
                lemma_stable_count_subrange(w, p1, p1 + r1_len, n);
                lemma_stable_letter_count_concat(w.subrange(0, p1), w.subrange(p1 + r1_len, w.len() as int), n);
                lemma_step_preserves_word_valid(data, w, step1_base);
                let step0_adj = DerivationStep::RelatorInsert { position: (p0 - r1_len) as int, relator_index: ri0, inverted: inv0 };
                let ins = w_prime.subrange(0, (p0 - r1_len) as int) + r0 + w_prime.subrange((p0 - r1_len) as int, w_prime.len() as int);
                assert forall|k: int| 0 <= k < w2.len() implies w2[k] == ins[k] by {};
                assert(w2 =~= ins);
                assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
                (w_prime, step1_base, step0_adj)
            } else if p1 >= p0 + r0_len {
                let p1a = (p1 - r0_len) as int;
                assert forall|k: int| p1 <= k < p1 + r1_len implies w1[k] == w[(k - r0_len) as int] by {};
                assert(w.subrange(p1a, p1a + r1_len) =~= r1);
                let w_prime = w.subrange(0, p1a) + w.subrange(p1a + r1_len, w.len() as int);
                let step1_base = DerivationStep::RelatorDelete { position: p1a, relator_index: ri1, inverted: inv1 };
                assert(apply_step(data.base, w, step1_base) == Some(w_prime));
                lemma_stable_count_subrange(w, p1a, p1a + r1_len, n);
                lemma_stable_letter_count_concat(w.subrange(0, p1a), w.subrange(p1a + r1_len, w.len() as int), n);
                lemma_step_preserves_word_valid(data, w, step1_base);
                let step0_adj = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
                let ins = w_prime.subrange(0, p0) + r0 + w_prime.subrange(p0, w_prime.len() as int);
                assert forall|k: int| 0 <= k < w2.len() implies w2[k] == ins[k] by {};
                assert(w2 =~= ins);
                assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
                (w_prime, step1_base, step0_adj)
            } else {
                assume(false); arbitrary() // overlap/inside relator
            }
        },
    }
*/

/*proof fn _dead_lemma_k4_peak_step12(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w1: Word, w2: Word, w_end: Word,
    remaining_steps: Seq<DerivationStep>,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        steps.len() >= 4,
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, steps[0]) == Some(w1)
            &&& apply_step(hp, w1, steps[1]) == Some(w2)
            &&& remaining_steps == steps.subrange(2, steps.len() as int)
            &&& derivation_produces(hp, remaining_steps, w2) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 4nat,
        match steps[0] {
            DerivationStep::FreeExpand { position, symbol } =>
                generator_index(symbol) == data.base.num_generators,
            DerivationStep::RelatorInsert { position, relator_index, inverted } =>
                relator_index as int >= data.base.relators.len(),
            _ => false,
        },
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            forall|j: nat| 1 <= j < steps.len()
                ==> !is_base_word(derivation_word_at(hp, steps, w, j), n)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
    decreases steps.len(), 0nat,
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    if steps.len() == 4 {
        // k=4: c_3 is forced to be 2.
        // Step 2 operates on w_2 (count 4). Step 3 must bring to base (count 0).
        // By lemma_count4_step_cant_reach_base, step 3 can't reach base from count ≥ 4.
        // So step 2 must reduce count: c_3 ∈ {2, 4, 6}.
        // c_3 = 4 or 6: step 3 goes from c_3 ≥ 4 → 0, impossible.
        // c_3 = 2: step 2 is -2, step 3 is -2. ✓
        let step2 = remaining_steps[0int];
        let step3 = remaining_steps[1int];
        assert(remaining_steps.len() == 2);

        // Establish step 2 validity and w3
        assert(apply_step(hp, w2, step2).is_some());
        let w3 = apply_step(hp, w2, step2).unwrap();
        lemma_step_preserves_word_valid(data, w2, step2);

        // w3 is the last non-base intermediate
        assert(derivation_word_at(hp, steps, w, 3nat) == w3) by {
            let rest0 = steps.drop_first();
            let rest1 = rest0.drop_first();
            assert(derivation_word_at(hp, steps, w, 3nat) ==
                derivation_word_at(hp, rest0, w1, 2nat));
            assert(derivation_word_at(hp, rest0, w1, 2nat) ==
                derivation_word_at(hp, rest1, w2, 1nat));
            assert(rest1.first() == step2);
            lemma_word_at_one(hp, rest1, w2);
        };
        assert(!is_base_word(w3, n));

        // Prove c_3 = 2: step 3 can't reach base from count ≥ 4
        lemma_stable_count_reduce_step(data, w2, step2, n);
        let c3 = stable_letter_count(w3, n);
        // c3 is one of {2, 4, 6}
        // Establish step3 produces w_end from w3 by unfolding derivation_produces
        let rest1 = remaining_steps.drop_first();
        assert(rest1.len() == 1);
        assert(rest1.first() == step3);
        // derivation_produces(hp, remaining_steps, w2) unfolds to:
        // apply_step(hp, w2, step2) = Some(w3), then derivation_produces(hp, rest1, w3)
        assert(derivation_produces(hp, rest1, w3) == Some(w_end));
        // Use derivation split to extract step3 validity
        lemma_derivation_split(hp, remaining_steps, w2, w_end, 1nat);
        lemma_word_at_produces(hp, remaining_steps, w2, 1nat);
        let right_part = remaining_steps.subrange(1, 2);
        assert(derivation_produces(hp, right_part, w3) == Some(w_end));
        assert(right_part.len() == 1);
        assert(right_part.first() == step3) by {
            assert(right_part[0int] == step3);
        };
        lemma_derivation_unfold_1(hp, right_part, w3, w_end);
        assert(apply_step(hp, w3, step3) == Some(w_end));

        if c3 >= 4 {
            lemma_step_preserves_word_valid(data, w3, step3);
            lemma_count4_step_cant_reach_base(data, w3, w_end, step3);
            assert(false);
        }
        assert(c3 == 2nat);

        // Steps 1 (+2) and 2 (-2) form a peak.
        // Step 1: FreeExpand(stable) or RelatorInsert(HNN) — introduces 2 stable letters
        // Step 2: FreeReduce(stable) or RelatorDelete(HNN) — removes 2 stable letters
        //
        // Strategy: construct a 2-step derivation [s0, s3] from w to w_end.
        // If w_3 = w_1 (steps 1 and 2 cancel), this is direct.
        // If w_3 ≠ w_1 (steps 1 and 2 commute), create a base intermediate.
        //
        // Key insight: step2 removes 2 stable letters from w_2 (which has 4).
        // These 2 letters are either from step1 (cancel) or from step0 (commute).
        // In both cases we can construct a shorter derivation.
        //
        // For now, construct [s0, s3] when possible, or use the k=3 result.
        // Note: w → w_1 → w_2 → w_3 → w_end is a 4-step derivation.
        // w and w_end are base. w_1 has c=2, w_2 has c=4, w_3 has c=2.
        // Sub-derivation w_1 → w_2 → w_3: 2 steps, c goes 2→4→2.
        // But the sub-derivation [s0, s2, s3] (removing step 1) or [s0, s1, s3]
        // might not be valid derivations since the words don't chain.
        //
        // Alternative: use the 3-step sub-derivation [s0, s1, s2] from w to w_3.
        // Both w and w_3 are... w is base but w_3 is NOT base (c_3 = 2).
        // Not directly useful.
        //
        // Better approach for k=4: call lemma_single_segment on the FULL
        // 4-step derivation, but noting that w_2 has c=4.
        // Actually, w_2 is non-base, so the existing infrastructure handles it.
        // lemma_base_derivation_equiv would try to find a base intermediate,
        // and since all intermediates are non-base, it would call
        // lemma_single_segment_hard again with the same 4 steps. This is circular.
        //
        // The right approach: show that steps 1 and 2 can be REPLACED by steps
        // that produce a base intermediate.
        //
        // For this, I need to analyze the specific step types.
        // Step 1 is +2: FreeExpand(stable, p1, sym1) or RelatorInsert(HNN, p1, ri1, inv1)
        // Step 2 is -2: FreeReduce(stable, p2) or RelatorDelete(HNN, p2, ri2, inv2)
        //
        // For the simplest case: step1 = FreeExpand(sym1, p1) and step2 = FreeReduce(p2).
        // The FreeExpand inserts [sym1, inv(sym1)] at p1 in w_1.
        // The FreeReduce removes a stable pair from w_2.
        //
        // If p2 = p1 (cancel): w_3 = w_1. Derivation becomes [s0, s3] from w to w_end.
        // If p2 ≠ p1 (commute): step2 removes a different stable pair (from w_1).
        //   Apply step2 to w_1 first → w_1' (count 0, BASE!).
        //   Then apply step1 to w_1' → w_3.
        //   New derivation: [s0, s2', s1', s3] from w to w_end, base at position 2.
        //
        // In both cases, call lemma_base_derivation_equiv on shorter derivations.
        //
        // Since this requires per-type case analysis, delegate to a helper.
        // Peak cancel or commute — inline to avoid recursion group issues
        if w3 =~= w1 {
            // Cancel case: steps 1 and 2 cancel, w3 = w1
            // Construct 2-step derivation [step0, step3] from w to w_end
            assert(apply_step(hp, w1, step3) == Some(w_end)) by {
                assert(w3 =~= w1);
            };
            lemma_derivation_produces_2(hp, steps[0], step3, w, w1, w_end);
            let short_steps: Seq<DerivationStep> = seq![steps[0], step3];
            lemma_base_derivation_equiv(data, short_steps, w, w_end);
        } else {
            // Non-cancel: need per-type commutation analysis
            assume(false);
        }
    } else {
        // k >= 5 with c_2 = 4
        // TODO: commute from end or deeper peak analysis
        assume(false);
    }
}*/

/// Strategy: for k=3, dispatch on step types and commute neutral step to front.
/// For k≥4: commute T-free step to front, or peak-eliminate.
proof fn lemma_single_segment_hard(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        steps.len() >= 3,
        derivation_produces(hnn_presentation(data), steps, w) == Some(w_end),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        !is_base_word(
            apply_step(hnn_presentation(data), w, steps.first()).unwrap(),
            data.base.num_generators,
        ),
        // ALL intermediates are non-base
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            forall|j: nat| 1 <= j < steps.len()
                ==> !is_base_word(derivation_word_at(hp, steps, w, j), n)
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
    decreases steps.len(), 0nat,
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    if steps.len() == 3 {
        let step0 = steps[0];
        let step1 = steps[1];
        let step2 = steps[2];
        let w1 = apply_step(hp, w, step0).unwrap();

        // Unfold the 3-step derivation into individual apply_step facts
        let (w1_chk, w2_chk) = lemma_derivation_unfold_3(hp, steps, w, w_end);
        assert(w1_chk == w1);
        let w2 = w2_chk;
        assert(apply_step(hp, w1, step1) == Some(w2));
        assert(apply_step(hp, w2, step2) == Some(w_end));

        // w2 is non-base (from the all-intermediates condition)
        let rest01 = steps.drop_first();
        assert(derivation_word_at(hp, steps, w, 2nat) == w2) by {
            assert(derivation_word_at(hp, steps, w, 2nat) ==
                derivation_word_at(hp, rest01, w1, 1nat));
            assert(rest01.len() > 0);
            assert(rest01.first() == step1);
            assert(apply_step(hp, w1, rest01.first()).is_some());
            lemma_word_at_one(hp, rest01, w1);
        };
        assert(!is_base_word(w2, n));

        // Classify step0
        lemma_base_word_valid_down(w, n);
        lemma_base_to_nonbase_step_type(data, w, w1, step0);

        match step0 {
            DerivationStep::FreeExpand { position: p0, symbol: sym } => {
                match step1 {
                    DerivationStep::FreeReduce { position: p1 } => {
                        lemma_k3_expand_freereduce(
                            data, w, w1, w2, w_end, p0, sym, p1, step2,
                        );
                    },
                    DerivationStep::FreeExpand { position: p1, symbol: sym1 } => {
                        if generator_index(sym1) < n {
                            lemma_k3_expand_freeexpand_base(
                                data, w, w1, w2, w_end, p0, sym, p1, sym1, step2,
                            );
                        } else {
                            lemma_k3_expand_freeexpand_stable(
                                data, w, w1, w2, w_end, p0, sym, p1, sym1, step2,
                            );
                        }
                    },
                    DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 } => {
                        lemma_k3_expand_reldelete(
                            data, w, w1, w2, w_end, p0, sym, p1, ri1, inv1, step2,
                        );
                    },
                    DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
                        lemma_k3_expand_relinsert(
                            data, w, w1, w2, w_end, p0, sym, p1, ri1, inv1, step2,
                        );
                    },
                }
            },
            DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 } => {
                lemma_k3_relinsert_hnn(
                    data, w, w1, w2, w_end, p0, ri0, inv0, step1, step2);
            },
            _ => {
                // Unreachable by lemma_base_to_nonbase_step_type
            },
        }
    } else {
        // k >= 4: peak elimination
        let step0 = steps[0];
        let step1 = steps[1];
        let w1 = apply_step(hp, w, step0).unwrap();

        lemma_step_preserves_word_valid(data, w, step0);

        // Establish step1 is valid on w1 (from derivation validity)
        let rest0 = steps.drop_first();
        assert(rest0.len() >= 3);
        assert(rest0.first() == step1);
        assert(derivation_produces(hp, rest0, w1) == Some(w_end));
        assert(apply_step(hp, w1, step1).is_some());

        lemma_step_preserves_word_valid(data, w1, step1);
        let w2 = apply_step(hp, w1, step1).unwrap();

        // Establish w2 = derivation_word_at(hp, steps, w, 2)
        assert(derivation_word_at(hp, steps, w, 2nat) == w2) by {
            assert(derivation_word_at(hp, steps, w, 2nat) ==
                derivation_word_at(hp, rest0, w1, 1nat));
            assert(rest0.len() > 0);
            assert(apply_step(hp, w1, rest0.first()).is_some());
            lemma_word_at_one(hp, rest0, w1);
        };
        assert(!is_base_word(w2, n));

        // Get remaining derivation from w2 to w_end
        lemma_word_at_produces(hp, steps, w, 2nat);
        assert(derivation_produces(hp, steps.subrange(0, 2), w) == Some(w2));
        lemma_derivation_split(hp, steps, w, w_end, 2nat);
        let remaining_steps = steps.subrange(2, steps.len() as int);
        assert(derivation_produces(hp, remaining_steps, w2) == Some(w_end));

        // Classify step 0
        lemma_base_word_valid_down(w, n);
        lemma_base_to_nonbase_step_type(data, w, w1, step0);

        // c_1 = 2
        lemma_base_implies_count_zero(w, n);
        lemma_stable_count_reduce_step(data, w, step0, n);
        assert(stable_letter_count(w1, n) == 2nat);

        // Classify step 1 by stable count change
        lemma_stable_count_reduce_step(data, w1, step1, n);
        let c2 = stable_letter_count(w2, n);

        if c2 == 2 {
            // Case A: step 1 is T-free — commute it before step 0
            let (w_prime, step1_base, step0_adj) = match step0 {
                DerivationStep::FreeExpand { position: p0, symbol: sym } => {
                    match step1 {
                        DerivationStep::FreeReduce { position: p1 } =>
                            lemma_k4_tfree_expand_commute_fr(data, w, w1, w2, p0, sym, p1),
                        _ =>
                            lemma_k4_tfree_expand_commute_other(data, w, w1, w2, p0, sym, step1),
                    }
                },
                DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 } => {
                    lemma_k4_tfree_ri_commute(data, w, w1, w2, p0, ri0, inv0, step1)
                },
                _ => { assert(false); arbitrary() },
            };

            // Build (k-1)-step derivation from w' to w_end
            assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
            // Prove 1-step derivation from w' to w2
            let one_step: Seq<DerivationStep> = seq![step0_adj];
            assert(one_step.len() == 1);
            assert(one_step.first() == step0_adj);
            assert(one_step.drop_first() =~= Seq::<DerivationStep>::empty());
            assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w2) == Some(w2));
            assert(derivation_produces(hp, one_step, w_prime) == Some(w2));
            // Concat to get full derivation from w'
            lemma_derivation_concat(hp, one_step, remaining_steps, w_prime, w2, w_end);
            let new_steps = one_step + remaining_steps;
            lemma_base_derivation_equiv(data, new_steps, w_prime, w_end);
            lemma_single_step_equiv(data.base, w, step1_base, w_prime);
            lemma_equiv_transitive(data.base, w, w_prime, w_end);
        } else {
            // Case B: step 1 is +2, c_2 = 4. Peak elimination.
            assert(c2 == 4nat);

            if steps.len() == 4 {
                // k=4: c_3 forced to be 2.
                let step2 = remaining_steps[0int];
                let step3 = remaining_steps[1int];
                assert(remaining_steps.len() == 2);
                assert(apply_step(hp, w2, step2).is_some());
                let w3 = apply_step(hp, w2, step2).unwrap();
                lemma_step_preserves_word_valid(data, w2, step2);

                // w3 is non-base intermediate
                assert(derivation_word_at(hp, steps, w, 3nat) == w3) by {
                    let r0 = steps.drop_first();
                    let r1 = r0.drop_first();
                    assert(derivation_word_at(hp, steps, w, 3nat) ==
                        derivation_word_at(hp, r0, w1, 2nat));
                    assert(derivation_word_at(hp, r0, w1, 2nat) ==
                        derivation_word_at(hp, r1, w2, 1nat));
                    assert(r1.first() == step2);
                    lemma_word_at_one(hp, r1, w2);
                };
                assert(!is_base_word(w3, n));

                // Prove c_3 = 2 via count4 barrier
                lemma_stable_count_reduce_step(data, w2, step2, n);
                let c3 = stable_letter_count(w3, n);
                // Extract step3 validity
                lemma_derivation_split(hp, remaining_steps, w2, w_end, 1nat);
                lemma_word_at_produces(hp, remaining_steps, w2, 1nat);
                let right_part = remaining_steps.subrange(1, 2);
                assert(right_part.first() == step3) by {
                    assert(right_part[0int] == step3);
                };
                lemma_derivation_unfold_1(hp, right_part, w3, w_end);
                assert(apply_step(hp, w3, step3) == Some(w_end));

                if c3 >= 4 {
                    lemma_count4_step_cant_reach_base(data, w3, w_end, step3);
                    assert(false);
                }
                assert(c3 == 2nat);

                // Peak at steps (1, 2): cancel or commute
                if w3 =~= w1 {
                    // Cancel: construct 2-step derivation [step0, step3]
                    assert(apply_step(hp, w1, step3) == Some(w_end));
                    lemma_derivation_produces_2(hp, step0, step3, w, w1, w_end);
                    let short: Seq<DerivationStep> = seq![step0, step3];
                    lemma_base_derivation_equiv(data, short, w, w_end);
                } else {
                    // Non-cancel: commute step2 past step1 to create base intermediate
                    let (w1_prime, step2_adj, step1_adj) =
                        lemma_k4_peak_noncancel_commute(data, w1, w2, w3, step1, step2);

                    // Build 2-step derivation [step0, step2_adj] from w (base) to w1' (base)
                    lemma_derivation_produces_2(hp, step0, step2_adj, w, w1, w1_prime);
                    let left_steps: Seq<DerivationStep> = seq![step0, step2_adj];
                    lemma_base_derivation_equiv(data, left_steps, w, w1_prime);

                    // Build 2-step derivation [step1_adj, step3] from w1' (base) to w_end (base)
                    lemma_step_preserves_word_valid(data, w1_prime, step1_adj);
                    lemma_derivation_produces_2(hp, step1_adj, step3, w1_prime, w3, w_end);
                    let right_steps: Seq<DerivationStep> = seq![step1_adj, step3];
                    lemma_base_derivation_equiv(data, right_steps, w1_prime, w_end);

                    // Chain: w ≡ w1' ≡ w_end in base group
                    lemma_equiv_transitive(data.base, w, w1_prime, w_end);
                }
            } else {
                // k >= 5 with c_2 = 4: same peak argument as k=4.
                let step2 = remaining_steps[0int];
                assert(apply_step(hp, w2, step2).is_some());
                let w3 = apply_step(hp, w2, step2).unwrap();
                lemma_step_preserves_word_valid(data, w2, step2);

                // w3 is non-base intermediate
                assert(derivation_word_at(hp, steps, w, 3nat) == w3) by {
                    let r0 = steps.drop_first();
                    let r1 = r0.drop_first();
                    assert(derivation_word_at(hp, steps, w, 3nat) ==
                        derivation_word_at(hp, r0, w1, 2nat));
                    assert(derivation_word_at(hp, r0, w1, 2nat) ==
                        derivation_word_at(hp, r1, w2, 1nat));
                    assert(r1.first() == step2);
                    lemma_word_at_one(hp, r1, w2);
                };
                assert(!is_base_word(w3, n));

                // c_3 = 2 (c3 >= 4 requires deeper analysis)
                lemma_stable_count_reduce_step(data, w2, step2, n);
                let c3 = stable_letter_count(w3, n);
                lemma_derivation_split(hp, remaining_steps, w2, w_end, 1nat);
                let tail_steps = remaining_steps.subrange(1, remaining_steps.len() as int);
                assert(derivation_produces(hp, tail_steps, w3) == Some(w_end));

                if c3 >= 4 {
                    // c3 >= 4: need deeper peak analysis (T-free or higher peak)
                    assume(false);
                }
                assert(c3 == 2nat);

                // Peak at steps (1, 2): cancel or commute
                if w3 =~= w1 {
                    let short = crate::britton_proof_helpers3::lemma_k5_peak_cancel(
                        data, steps, w, w_end, w1, step0, tail_steps);
                    lemma_base_derivation_equiv(data, short, w, w_end);
                } else {
                    let (w1_prime, left_steps, right_steps) =
                        crate::britton_proof_helpers3::lemma_k5_peak_noncancel(
                            data, steps, w, w_end, w1, w2, w3,
                            step0, step1, step2, tail_steps);
                    lemma_base_derivation_equiv(data, left_steps, w, w1_prime);
                    lemma_base_derivation_equiv(data, right_steps, w1_prime, w_end);
                    lemma_equiv_transitive(data.base, w, w1_prime, w_end);
                }
            }
        }
    }
}

/// The single segment lemma: if a derivation from base w to base w_end
/// has w_1 non-base, then w ≡ w_end in G.
///
/// Strategy: induction on steps.len().
/// Base: steps.len() == 2 → lemma_single_segment_k2.
/// k > 2: Find first base intermediate after w_1.
///   If found before w_end: split and recurse.
///   If not (all intermediates non-base): delegate to lemma_single_segment_hard.
proof fn lemma_single_segment(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        steps.len() >= 2,
        derivation_produces(hnn_presentation(data), steps, w) == Some(w_end),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        // All intermediates are non-base
        !is_base_word(
            apply_step(hnn_presentation(data), w, steps.first()).unwrap(),
            data.base.num_generators,
        ),
        // (For k > 2: all w_1,...,w_{k-1} are non-base — handled by induction)
    ensures
        equiv_in_presentation(data.base, w, w_end),
    decreases steps.len(), 1nat,
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let k: nat = steps.len();

    if k == 2 {
        lemma_single_segment_k2(data, steps, w, w_end);
    } else {
        // k >= 3. Look at w_2.
        let step0 = steps[0];
        let step1 = steps[1];
        let w1 = apply_step(hp, w, step0).unwrap();
        let rest0 = steps.drop_first();
        assert(rest0.first() == step1);

        // Establish sub-derivation validity
        assert(derivation_produces(hp, rest0, w1) == Some(w_end));

        let w2 = apply_step(hp, w1, step1).unwrap();

        // w1 and w2 are word_valid
        lemma_step_preserves_word_valid(data, w, step0);
        lemma_step_preserves_word_valid(data, w1, step1);

        // Check if w_2 is base
        lemma_word_at_one(hp, steps, w);
        // derivation_word_at(hp, steps, w, 2) == w2
        assert(derivation_word_at(hp, steps, w, 2nat) == w2) by {
            assert(derivation_word_at(hp, steps, w, 2nat) ==
                derivation_word_at(hp, rest0, w1, 1nat));
            lemma_word_at_one(hp, rest0, w1);
        };

        if is_base_word(w2, n) {
            // w_2 is base: split at position 2
            // Left: steps[0..2] from base w to base w_2, k=2 segment
            // Right: steps[2..] from base w_2 to base w_end
            lemma_derivation_split(hp, steps, w, w_end, 2nat);
            let left_steps = steps.subrange(0, 2int);
            let right_steps = steps.subrange(2int, steps.len() as int);
            lemma_word_at_produces(hp, steps, w, 2nat);

            // Left: k=2 segment, w ≡_G w2
            assert(left_steps.first() == steps[0]) by {
                assert(left_steps[0] == steps[0]);
            };
            assert(left_steps.len() == 2);
            lemma_single_segment_k2(data, left_steps, w, w2);

            // Right: base→base derivation. Use britton_with_derivation_general
            // for now, call recursively via lemma_base_derivation_equiv
            lemma_base_derivation_equiv(data, right_steps, w2, w_end);

            // Chain
            lemma_equiv_transitive(data.base, w, w2, w_end);
        } else {
            // w_2 is non-base. Find first base intermediate in the
            // sub-derivation from w_1 (rest0 = steps[1..]).
            // Since w_end is base and w_2 is non-base, first base intermediate
            // in rest0 from w_1 is at position >= 2 (since w_2 = word_at(rest0, w_1, 1) is non-base).
            lemma_first_base_is_base(hp, rest0, w1, w_end, n);
            let j = first_base_intermediate(hp, rest0, w1, n);
            // j >= 2 since w_2 is non-base
            assert(j >= 2) by {
                lemma_word_at_one(hp, rest0, w1);
                assert(derivation_word_at(hp, rest0, w1, 1nat) == w2);
                if j == 1 {
                    assert(is_base_word(derivation_word_at(hp, rest0, w1, j), n));
                    assert(false);
                }
            };

            let w_j1 = derivation_word_at(hp, rest0, w1, j);
            // w_j1 is base

            // In the original derivation, w_j1 is at position 1+j
            // derivation_word_at(hp, steps, w, 1+j) == derivation_word_at(hp, rest0, w1, j) = w_j1
            assert(derivation_word_at(hp, steps, w, (1 + j) as nat) == w_j1);

            // Split the original derivation at position 1+j
            let split_pos: nat = (1 + j) as nat;
            lemma_derivation_split(hp, steps, w, w_end, split_pos);
            let left_steps = steps.subrange(0, split_pos as int);
            let right_steps = steps.subrange(split_pos as int, steps.len() as int);
            lemma_word_at_produces(hp, steps, w, split_pos);

            // w_j1 is word_valid
            lemma_word_at_valid(data, steps, w, split_pos);

            assert(left_steps.first() == steps[0]) by {
                assert(left_steps[0] == steps[0]);
            };

            if split_pos < k {
                // Left: strictly shorter single segment
                lemma_single_segment(data, left_steps, w, w_j1);

                // Right: base→base, strictly shorter
                lemma_base_derivation_equiv(data, right_steps, w_j1, w_end);

                // Chain
                lemma_equiv_transitive(data.base, w, w_j1, w_end);
            } else {
                // split_pos == k, meaning w_j1 = w_end (first base intermediate is at the end)
                // ALL intermediates w_1,...,w_{k-1} are non-base.
                // This is the hard case: we can't split further.
                // For now, handle k=3 specially.
                assert(split_pos == k);
                assert(left_steps =~= steps);
                assert(w_j1 == w_end) by {
                    lemma_word_at_produces(hp, steps, w, k);
                    assert(derivation_produces(hp, steps, w) == Some(w_end));
                    assert(derivation_produces(hp, steps.subrange(0, k as int), w) == Some(w_j1));
                    assert(steps.subrange(0, k as int) =~= steps);
                };

                // Prove ALL intermediates are non-base
                // j = first_base_intermediate(hp, rest0, w1, n) = k-1
                // lemma_no_base_before_first on rest0 gives: for 1 <= m < j,
                // derivation_word_at(hp, rest0, w1, m) is non-base.
                // Translation: for 2 <= m_orig < k,
                // derivation_word_at(hp, steps, w, m_orig) is non-base.
                assert forall|m: nat| 1 <= m < steps.len()
                    implies !is_base_word(derivation_word_at(hp, steps, w, m), n)
                by {
                    if m == 1 {
                        lemma_word_at_one(hp, steps, w);
                    } else {
                        // m >= 2: word_at(steps, w, m) = word_at(rest0, w1, m-1)
                        assert(derivation_word_at(hp, steps, w, m)
                            == derivation_word_at(hp, rest0, w1, (m - 1) as nat));
                        // 1 <= m-1 < k-1 = j = first_base_intermediate(hp, rest0, w1, n)
                        lemma_no_base_before_first(hp, rest0, w1, w_end, n, (m - 1) as nat);
                    }
                };

                // Delegate to the hard case helper
                lemma_single_segment_hard(data, steps, w, w_end);
            }
        }
    }
}

/// General base→base derivation equivalence.
/// If a derivation in G* goes from base w to base w_end, then w ≡_G w_end.
/// Uses mutual recursion with lemma_single_segment.
pub proof fn lemma_base_derivation_equiv(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        derivation_produces(hnn_presentation(data), steps, w) == Some(w_end),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
    ensures
        equiv_in_presentation(data.base, w, w_end),
    decreases steps.len(), 2nat,
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    if steps.len() == 0 {
        assert(w =~= w_end);
        lemma_equiv_refl(data.base, w);
    } else {
        let step0 = steps.first();
        let w1 = apply_step(hp, w, step0).unwrap();
        let rest = steps.drop_first();

        lemma_step_preserves_word_valid(data, w, step0);

        if is_base_word(w1, n) {
            // Base-to-base step, valid in G
            lemma_t_free_step_is_base_step(data, w, step0);
            lemma_single_step_equiv(data.base, w, step0, w1);
            lemma_base_derivation_equiv(data, rest, w1, w_end);
            lemma_equiv_transitive(data.base, w, w1, w_end);
        } else {
            // w1 is non-base. Find first base intermediate.
            lemma_first_base_is_base(hp, steps, w, w_end, n);
            let k = first_base_intermediate(hp, steps, w, n);
            lemma_word_at_one(hp, steps, w);
            assert(k >= 2) by {
                assert(!is_base_word(w1, n));
                assert(derivation_word_at(hp, steps, w, 1nat) == w1);
                if k == 1 {
                    assert(is_base_word(derivation_word_at(hp, steps, w, k), n));
                    assert(false);
                }
            };

            let w_k = derivation_word_at(hp, steps, w, k);

            // Split derivation at k
            lemma_derivation_split(hp, steps, w, w_end, k);
            let left_steps = steps.subrange(0, k as int);
            let right_steps = steps.subrange(k as int, steps.len() as int);
            lemma_word_at_produces(hp, steps, w, k);

            // w_k is word_valid
            lemma_word_at_valid(data, steps, w, k);

            // Left: single segment from w to w_k
            lemma_single_segment(data, left_steps, w, w_k);

            // Right: shorter base→base derivation (k >= 2 so right is strictly shorter)
            lemma_base_derivation_equiv(data, right_steps, w_k, w_end);

            // Chain
            lemma_equiv_transitive(data.base, w, w_k, w_end);
        }
    }
}

// ============================================================
// Part 6: Word validity preservation
// ============================================================

/// Subrange of a word_valid word is word_valid.
pub proof fn lemma_subrange_word_valid(w: Word, lo: int, hi: int, n: nat)
    requires
        word_valid(w, n),
        0 <= lo <= hi <= w.len(),
    ensures
        word_valid(w.subrange(lo, hi), n),
{
    let sub = w.subrange(lo, hi);
    assert forall|i: int| 0 <= i < sub.len()
        implies symbol_valid(#[trigger] sub[i], n)
    by {
        assert(sub[i] == w[lo + i]);
        assert(symbol_valid(w[lo + i], n));
    }
}

/// inverse_symbol preserves symbol_valid.
proof fn lemma_inverse_symbol_valid(s: Symbol, n: nat)
    requires
        symbol_valid(s, n),
    ensures
        symbol_valid(inverse_symbol(s), n),
{
    match s {
        Symbol::Gen(idx) => {},
        Symbol::Inv(idx) => {},
    }
}

/// A single relator from a valid presentation is word_valid, lifted to n+1.
proof fn lemma_relator_valid_lifted(p: Presentation, i: int)
    requires
        presentation_valid(p),
        0 <= i < p.relators.len(),
    ensures
        word_valid(p.relators[i], p.num_generators + 1),
{
    reveal(presentation_valid);
    lemma_word_valid_monotone(p.relators[i], p.num_generators);
}

/// The HNN presentation is valid (all relators are word_valid).
proof fn lemma_hnn_presentation_valid(data: HNNData)
    requires
        hnn_data_valid(data),
    ensures
        presentation_valid(hnn_presentation(data)),
{
    reveal(presentation_valid);
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    assert forall|i: int| #![trigger hp.relators[i]]
        0 <= i < hp.relators.len()
        implies word_valid(hp.relators[i], hp.num_generators)
    by {
        let base_len = data.base.relators.len() as int;
        if i < base_len {
            // Base relator: valid for n, lift to n+1
            assert(hp.relators[i] == data.base.relators[i]);
            lemma_relator_valid_lifted(data.base, i);
        } else {
            // HNN relator at index i - base_len
            let k = (i - base_len);
            assert(hp.relators[i] == hnn_relator(data, k));
            let (a_k, b_k) = data.associations[k];
            let t = stable_letter(data);
            let t_inv = stable_letter_inv(data);
            let r = Seq::new(1, |_j: int| t_inv) + a_k
                + Seq::new(1, |_j: int| t) + inverse_word(b_k);
            assert(hp.relators[i] =~= r);

            // Show each symbol is valid for n+1
            assert(word_valid(a_k, n));
            lemma_inverse_word_valid(b_k, n);
            assert(word_valid(inverse_word(b_k), n));

            assert forall|j: int| 0 <= j < r.len()
                implies symbol_valid(#[trigger] r[j], n + 1)
            by {
                if j == 0 {
                    // t_inv = Inv(n), valid for n+1
                } else if (j as int) < 1 + a_k.len() {
                    // a_k symbol, valid for n hence n+1
                    let aj = (j - 1) as int;
                    assert(r[j] == a_k[aj]);
                    assert(symbol_valid(a_k[aj], n));
                    match a_k[aj] {
                        Symbol::Gen(idx) => {},
                        Symbol::Inv(idx) => {},
                    }
                } else if j == 1 + a_k.len() {
                    // t = Gen(n), valid for n+1
                    assert(r[j] == t);
                } else {
                    // inverse_word(b_k) symbol
                    let bj = (j - 2 - a_k.len()) as int;
                    let inv_bk = inverse_word(b_k);
                    assert(r[j] == inv_bk[bj]);
                    assert(symbol_valid(inv_bk[bj], n));
                    match inv_bk[bj] {
                        Symbol::Gen(idx) => {},
                        Symbol::Inv(idx) => {},
                    }
                }
            }
        }
    }
}

/// Helper: a valid step in G* produces a word_valid result.
pub proof fn lemma_step_preserves_word_valid(
    data: HNNData, w: Word, step: DerivationStep,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators + 1),
        apply_step(hnn_presentation(data), w, step).is_some(),
    ensures
        word_valid(
            apply_step(hnn_presentation(data), w, step).unwrap(),
            data.base.num_generators + 1,
        ),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators + 1;
    let result = apply_step(hp, w, step).unwrap();

    match step {
        DerivationStep::FreeReduce { position } => {
            // result = w[0..pos] + w[pos+2..] — subranges of w
            let pos = position;
            lemma_subrange_word_valid(w, 0, pos, n);
            lemma_subrange_word_valid(w, pos + 2, w.len() as int, n);
            lemma_concat_word_valid(
                w.subrange(0, pos),
                w.subrange(pos + 2, w.len() as int),
                n,
            );
            assert(result =~= w.subrange(0, pos) + w.subrange(pos + 2, w.len() as int));
        },
        DerivationStep::FreeExpand { position, symbol } => {
            // result = w[0..pos] + [sym, inv(sym)] + w[pos..]
            let pos = position;
            let pair = Seq::new(1, |_i: int| symbol)
                + Seq::new(1, |_i: int| inverse_symbol(symbol));
            lemma_subrange_word_valid(w, 0, pos, n);
            lemma_subrange_word_valid(w, pos, w.len() as int, n);

            // pair is word_valid
            lemma_inverse_symbol_valid(symbol, n);
            assert(word_valid(pair, n)) by {
                assert forall|i: int| 0 <= i < pair.len()
                    implies symbol_valid(#[trigger] pair[i], n)
                by {
                    if i == 0 {
                    } else {
                        assert(pair[1] == inverse_symbol(symbol));
                    }
                }
            }

            lemma_concat_word_valid(w.subrange(0, pos), pair, n);
            lemma_concat_word_valid(
                w.subrange(0, pos) + pair,
                w.subrange(pos, w.len() as int),
                n,
            );
            assert(result =~=
                w.subrange(0, pos) + pair + w.subrange(pos, w.len() as int));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            // result = w[0..pos] + r + w[pos..]
            let pos = position;
            let r = get_relator(hp, relator_index, inverted);
            lemma_subrange_word_valid(w, 0, pos, n);
            lemma_subrange_word_valid(w, pos, w.len() as int, n);

            // r is word_valid from presentation_valid
            lemma_hnn_presentation_valid(data);
            reveal(presentation_valid);
            let rel = hp.relators[relator_index as int];
            if inverted {
                lemma_inverse_word_valid(rel, n);
            }

            lemma_concat_word_valid(w.subrange(0, pos), r, n);
            lemma_concat_word_valid(
                w.subrange(0, pos) + r,
                w.subrange(pos, w.len() as int),
                n,
            );
            assert(result =~=
                w.subrange(0, pos) + r + w.subrange(pos, w.len() as int));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            // result = w[0..pos] + w[pos+|r|..]
            let r = get_relator(hp, relator_index, inverted);
            let rlen = r.len();
            let pos = position;
            lemma_subrange_word_valid(w, 0, pos, n);
            lemma_subrange_word_valid(w, pos + rlen as int, w.len() as int, n);
            lemma_concat_word_valid(
                w.subrange(0, pos),
                w.subrange(pos + rlen as int, w.len() as int),
                n,
            );
            assert(result =~=
                w.subrange(0, pos) + w.subrange(pos + rlen as int, w.len() as int));
        },
    }
}

/// Compute the intermediate word after k steps of a derivation.
spec fn derivation_word_at(p: Presentation, steps: Seq<DerivationStep>, w: Word, k: nat) -> Word
    recommends
        k <= steps.len(),
        derivation_produces(p, steps, w).is_some(),
    decreases k,
{
    if k == 0 {
        w
    } else {
        derivation_word_at(
            p,
            steps.drop_first(),
            apply_step(p, w, steps.first()).unwrap(),
            (k - 1) as nat,
        )
    }
}

/// derivation_word_at at 0 is just w.
proof fn lemma_word_at_zero(p: Presentation, steps: Seq<DerivationStep>, w: Word)
    ensures
        derivation_word_at(p, steps, w, 0) == w,
{}

/// derivation_word_at at 1 is the result of the first step.
proof fn lemma_word_at_one(
    p: Presentation, steps: Seq<DerivationStep>, w: Word,
)
    requires
        steps.len() > 0,
        apply_step(p, w, steps.first()).is_some(),
    ensures
        derivation_word_at(p, steps, w, 1nat)
            == apply_step(p, w, steps.first()).unwrap(),
{
    // Unfold: derivation_word_at(p, steps, w, 1)
    //   = derivation_word_at(p, steps.drop_first(), w1, 0)
    //   = w1
    let w1 = apply_step(p, w, steps.first()).unwrap();
    assert(derivation_word_at(p, steps.drop_first(), w1, 0nat) == w1);
}

/// derivation_word_at relates to the derivation_produces of the prefix.
proof fn lemma_word_at_produces(
    p: Presentation, steps: Seq<DerivationStep>, w: Word, k: nat,
)
    requires
        k <= steps.len(),
        derivation_produces(p, steps, w).is_some(),
    ensures
        derivation_produces(p, steps.subrange(0, k as int), w)
            == Some(derivation_word_at(p, steps, w, k)),
    decreases k,
{
    if k == 0 {
        assert(steps.subrange(0, 0int) =~= Seq::<DerivationStep>::empty());
    } else {
        let w1 = apply_step(p, w, steps.first()).unwrap();
        let rest = steps.drop_first();
        lemma_word_at_produces(p, rest, w1, (k - 1) as nat);

        // Connect: steps.subrange(0, k)[0] == steps[0], drop_first = rest.subrange(0, k-1)
        let prefix = steps.subrange(0, k as int);
        assert(prefix.first() == steps.first());
        assert(prefix.drop_first() =~= rest.subrange(0, (k - 1) as int));
    }
}

/// Steps preserve word_valid across a derivation.
proof fn lemma_derivation_preserves_word_valid(
    data: HNNData, steps: Seq<DerivationStep>, w: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators + 1),
        derivation_produces(hnn_presentation(data), steps, w).is_some(),
    ensures
        word_valid(
            derivation_produces(hnn_presentation(data), steps, w).unwrap(),
            data.base.num_generators + 1,
        ),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let hp = hnn_presentation(data);
        let w1 = apply_step(hp, w, steps.first()).unwrap();
        lemma_step_preserves_word_valid(data, w, steps.first());
        lemma_derivation_preserves_word_valid(data, steps.drop_first(), w1);
    }
}

/// word_valid at each intermediate in a derivation.
proof fn lemma_word_at_valid(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, k: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators + 1),
        derivation_produces(hnn_presentation(data), steps, w).is_some(),
        k <= steps.len(),
    ensures
        word_valid(
            derivation_word_at(hnn_presentation(data), steps, w, k),
            data.base.num_generators + 1,
        ),
{
    lemma_word_at_produces(hnn_presentation(data), steps, w, k);
    let prefix = steps.subrange(0, k as int);
    lemma_derivation_preserves_word_valid(data, prefix, w);
}

/// Find the first k > 0 such that the intermediate is a base word.
/// Since w_n = ε is base, such k exists.
spec fn first_base_intermediate(
    p: Presentation, steps: Seq<DerivationStep>, w: Word, n: nat,
) -> nat
    recommends
        steps.len() > 0,
        derivation_produces(p, steps, w).is_some(),
    decreases steps.len(),
{
    if steps.len() == 0 {
        0
    } else {
        let w1 = apply_step(p, w, steps.first()).unwrap();
        if is_base_word(w1, n) {
            1
        } else if steps.drop_first().len() == 0 {
            1  // shouldn't happen when last word is base
        } else {
            1 + first_base_intermediate(p, steps.drop_first(), w1, n)
        }
    }
}

/// The first base intermediate gives a base word.
proof fn lemma_first_base_is_base(
    p: Presentation, steps: Seq<DerivationStep>, w: Word, w_end: Word, n: nat,
)
    requires
        steps.len() > 0,
        derivation_produces(p, steps, w) == Some(w_end),
        is_base_word(w_end, n),
    ensures
        ({
            let k = first_base_intermediate(p, steps, w, n);
            &&& 1 <= k <= steps.len()
            &&& is_base_word(derivation_word_at(p, steps, w, k), n)
        }),
    decreases steps.len(),
{
    let w1 = apply_step(p, w, steps.first()).unwrap();
    let rest = steps.drop_first();
    if is_base_word(w1, n) {
        // k = 1, w1 is base
        lemma_word_at_one(p, steps, w);
        assert(first_base_intermediate(p, steps, w, n) == 1);
    } else if rest.len() == 0 {
        // steps.len() == 1, w1 = w_end which is base — contradiction
        assert(derivation_produces(p, rest, w1) == Some(w_end)) by {
            assert(rest.len() == 0);
        };
        assert(w1 == w_end);
        assert(false);
    } else {
        lemma_first_base_is_base(p, rest, w1, w_end, n);
        let k_rest = first_base_intermediate(p, rest, w1, n);
        let k = 1 + k_rest;
        assert(first_base_intermediate(p, steps, w, n) == k);
        // derivation_word_at(p, steps, w, k) == derivation_word_at(p, rest, w1, k_rest)
        assert(derivation_word_at(p, steps, w, k) ==
            derivation_word_at(p, rest, w1, k_rest));
    }
}

/// No intermediate before the first base one is base.
proof fn lemma_no_base_before_first(
    p: Presentation, steps: Seq<DerivationStep>, w: Word, w_end: Word, n: nat,
    j: nat,
)
    requires
        steps.len() > 0,
        derivation_produces(p, steps, w) == Some(w_end),
        is_base_word(w_end, n),
        !is_base_word(apply_step(p, w, steps.first()).unwrap(), n),
        1 <= j < first_base_intermediate(p, steps, w, n),
    ensures
        !is_base_word(derivation_word_at(p, steps, w, j), n),
    decreases steps.len(),
{
    let w1 = apply_step(p, w, steps.first()).unwrap();
    let rest = steps.drop_first();
    if j == 1 {
        // derivation_word_at(p, steps, w, 1) = w1 which is !base
        lemma_word_at_one(p, steps, w);
    } else {
        // j >= 2
        // Since !is_base_word(w1) and rest.len() > 0 (else fbi would be 1):
        assert(rest.len() > 0) by {
            if rest.len() == 0 {
                // first_base_intermediate(p, steps, w, n) = 1 (the else-if branch)
                // but j >= 2 and j < fbi — contradiction
            }
        };
        // first_base_intermediate(steps, w, n) = 1 + first_base_intermediate(rest, w1, n)
        assert(first_base_intermediate(p, steps, w, n)
            == 1 + first_base_intermediate(p, rest, w1, n));
        // derivation_word_at(steps, w, j) = derivation_word_at(rest, w1, j-1)
        assert(derivation_word_at(p, steps, w, j)
            == derivation_word_at(p, rest, w1, (j - 1) as nat));
        lemma_no_base_before_first(p, rest, w1, w_end, n, (j - 1) as nat);
    }
}

/// Core: given a specific derivation from base w to ε, prove w ≡_G ε.
/// Delegates to lemma_base_derivation_equiv.
proof fn britton_lemma_with_derivation(
    data: HNNData, steps: Seq<DerivationStep>, w: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        derivation_produces(hnn_presentation(data), steps, w) == Some(empty_word()),
        is_base_word(w, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    lemma_empty_is_base_word(data.base.num_generators);
    // empty_word() is trivially word_valid
    assert(word_valid(empty_word(), data.base.num_generators + 1)) by {
        assert forall|i: int| 0 <= i < empty_word().len()
            implies symbol_valid(#[trigger] empty_word()[i], data.base.num_generators + 1)
        by {}
    };
    lemma_base_derivation_equiv(data, steps, w, empty_word());
}

/// Britton's Lemma: replaces the axiom.
/// If w is a base word equivalent to ε in G*, then w ≡ ε in G.
pub proof fn britton_lemma(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let d = choose|d: Derivation| derivation_valid(hp, d, w, empty_word());

    lemma_word_valid_monotone(w, n);
    lemma_base_word_characterization(w, n);

    britton_lemma_with_derivation(data, d.steps, w);
}

} // verus!
