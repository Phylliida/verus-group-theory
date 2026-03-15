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

// ============================================================
// Part 2: Stable letter count helpers
// ============================================================

/// Stable letter count of a 2-element sequence [s1, s2].
proof fn lemma_stable_count_pair(s1: Symbol, s2: Symbol, n: nat)
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

// ============================================================
// Part 4: Stable letter count under steps
// ============================================================

/// Stable count of a subrange equals the count minus the removed parts.
proof fn lemma_stable_count_subrange(w: Word, lo: int, hi: int, n: nat)
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
proof fn lemma_stable_count_reduce(w: Word, pos: int, n: nat)
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

/// If w is base, FreeExpand with a stable symbol gives stable count 2.
proof fn lemma_expand_stable_gives_count_2(
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
proof fn lemma_base_word_valid_down(w: Word, n: nat)
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
proof fn lemma_remove_trivial_equiv(
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
proof fn lemma_insert_trivial_equiv(
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
proof fn lemma_hnn_relator_stable_positions(data: HNNData, j: int)
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
proof fn lemma_hnn_relator_inverted_stable_positions(data: HNNData, j: int)
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
        // r = hnn_relator(data, j) = [Inv(n)] ++ a_j ++ [Gen(n)] ++ inv(b_j)
        lemma_hnn_relator_stable_positions(data, j);
        let t_inv = stable_letter_inv(data);
        assert(r[0int] == t_inv);
        assert(generator_index(r[0int]) == n);

        // r[0] = w1[pos1], and gen_idx(w1[pos1]) = n → pos1 ∈ {pos0, pos0+1}
        assert(w1[pos1] == r[0int]);
        assert(generator_index(w1[pos1]) == n);

        // Show pos1 = pos0 (pos1 = pos0+1 leads to contradiction)
        if pos1 != pos0 as int {
            assert(pos1 == pos0 + 1);
            // r[|a_j|+1] is at w1[pos1+|a_j|+1] = w1[pos0+|a_j|+2]
            // Must be in {pos0, pos0+1}. But pos0+|a_j|+2 >= pos0+2 > pos0+1.
            let second_pos = pos1 + a_j.len() as int + 1;
            assert(second_pos == pos0 + a_j.len() as int + 2);
            assert(second_pos > pos0 + 1);
            assert(second_pos != pos0);
            assert(second_pos != pos0 + 1);
            // But r[|a_j|+1] has gen_idx = n, so w1[second_pos] has gen_idx = n
            // This contradicts the forall (gen_idx < n for positions ≠ pos0, pos0+1)
            assert(generator_index(w1[second_pos]) == n);
            assert(generator_index(w1[second_pos]) < n);
            assert(false);
        }
        assert(pos1 == pos0 as int);

        // |a_j| = 0 (from second stable letter at pos0+|a_j|+1 must be pos0+1)
        if a_j.len() > 0 {
            let second_pos = pos1 + a_j.len() as int + 1;
            assert(second_pos == pos0 + a_j.len() as int + 1);
            assert(second_pos > pos0 + 1);
            assert(second_pos != pos0);
            assert(second_pos != pos0 + 1);
            assert(generator_index(r[(a_j.len() + 1) as int]) == n);
            assert(w1[second_pos] == r[(a_j.len() + 1) as int]);
            assert(generator_index(w1[second_pos]) == n);
            assert(generator_index(w1[second_pos]) < n);
            assert(false);
        }
        assert(a_j.len() == 0);
        assert(a_j =~= Seq::<Symbol>::empty());

        // sym = Inv(n): w1[pos0] = sym = r[0] = Inv(n)
        assert(sym == t_inv);
        assert(t_inv == Symbol::Inv(n));

        // Compute w_end = w with inv(b_j) removed at pos0
        lemma_inverse_word_len(b_j);
        let inv_bj = inverse_word(b_j);
        let bj_len = b_j.len() as int;

        // r = [Inv(n), Gen(n)] ++ inv_bj (since |a_j| = 0)
        let r_prefix = Seq::new(1, |_i: int| Symbol::Inv(n)) + Seq::new(1, |_i: int| Symbol::Gen(n));
        assert(r =~= r_prefix + inv_bj);
        assert(r.len() == 2 + bj_len);

        // w_end = w1[0..pos0] ++ w1[pos0+2+bj_len..]
        // = w[0..pos0] ++ w[pos0+bj_len..]
        let w_left = w.subrange(0, pos0);
        let w_right = w.subrange(pos0 + bj_len, w.len() as int);
        assert(w_end =~= w1.subrange(0, pos0) + w1.subrange(pos0 + 2 + bj_len, w1.len() as int));
        assert(w1.subrange(0, pos0) =~= w_left);

        // w1[pos0+2+k] = w[pos0+k] for k >= 0
        assert forall|k: int| 0 <= k < w.len() - pos0
            implies #[trigger] w1[(pos0 + 2 + k) as int] == w[(pos0 + k) as int]
        by {
            assert(w1[(pos0 + 2 + k) as int] == right_w[k]);
            assert(right_w[k] == w[(pos0 + k) as int]);
        }
        assert(w1.subrange(pos0 + 2 + bj_len, w1.len() as int) =~= w_right);
        assert(w_end =~= w_left + w_right);

        // w[pos0..pos0+bj_len] = inv_bj (from relator matching in w1)
        assert forall|k: int| 0 <= k < bj_len
            implies w[(pos0 + k) as int] == #[trigger] inv_bj[k]
        by {
            assert(r[(2 + k) as int] == (r_prefix + inv_bj)[(2 + k) as int]);
            assert((r_prefix + inv_bj)[(2 + k) as int] == inv_bj[k]);
            assert(w1[(pos0 + 2 + k) as int] == r[(2 + k) as int]);
            assert(w1[(pos0 + 2 + k) as int] == w[(pos0 + k) as int]);
        }
        let w_mid = w.subrange(pos0, pos0 + bj_len);
        assert(w_mid =~= inv_bj);

        // w = w_left ++ inv_bj ++ w_right
        assert(w =~= w_left + w.subrange(pos0, w.len() as int));
        assert(w.subrange(pos0, w.len() as int) =~= w_mid + w_right);
        assert(w =~= w_left + (inv_bj + w_right));

        // By isomorphism: a_j = ε → b_j ≡ ε → inv(b_j) ≡ ε
        lemma_empty_association_implies_trivial(data, j);
        lemma_inverse_of_identity(data.base, b_j);
        lemma_inverse_word_valid(b_j, n);

        // w ≡ w_end by removing inv(b_j) from w
        lemma_remove_trivial_equiv(data.base, w_left, w_right, inv_bj);
    } else {
        // Inverted case: r = b_j ++ [Inv(n)] ++ inv(a_j) ++ [Gen(n)]
        lemma_hnn_relator_inverted_stable_positions(data, j);
        let t_inv = stable_letter_inv(data);
        assert(r[b_j.len() as int] == t_inv);
        assert(generator_index(r[b_j.len() as int]) == n);

        // r[|b_j|] = w1[pos1+|b_j|], gen_idx = n → pos1+|b_j| ∈ {pos0, pos0+1}
        assert(w1[(pos1 + b_j.len() as int)] == r[b_j.len() as int]);
        assert(generator_index(w1[(pos1 + b_j.len() as int)]) == n);

        if pos1 + b_j.len() as int != pos0 {
            assert(pos1 + b_j.len() as int == pos0 + 1);
            let second_pos = pos1 + b_j.len() as int + a_j.len() as int + 1;
            assert(second_pos == pos0 + a_j.len() as int + 2);
            assert(second_pos > pos0 + 1);
            assert(generator_index(r[(b_j.len() + a_j.len() + 1) as int]) == n);
            assert(w1[second_pos] == r[(b_j.len() + a_j.len() + 1) as int]);
            assert(generator_index(w1[second_pos]) == n);
            assert(generator_index(w1[second_pos]) < n);
            assert(false);
        }
        assert(pos1 + b_j.len() as int == pos0);

        // |a_j| = 0
        if a_j.len() > 0 {
            let second_pos = pos1 + b_j.len() as int + a_j.len() as int + 1;
            assert(second_pos == pos0 + a_j.len() as int + 1);
            assert(second_pos > pos0 + 1);
            assert(generator_index(r[(b_j.len() + a_j.len() + 1) as int]) == n);
            assert(w1[second_pos] == r[(b_j.len() + a_j.len() + 1) as int]);
            assert(generator_index(w1[second_pos]) == n);
            assert(generator_index(w1[second_pos]) < n);
            assert(false);
        }
        assert(a_j.len() == 0);
        assert(a_j =~= Seq::<Symbol>::empty());

        // pos1 = pos0 - |b_j|
        let bj_len = b_j.len() as int;
        assert(pos1 == pos0 - bj_len);

        // r = b_j ++ [Inv(n), Gen(n)] (since |a_j| = 0)
        // r.len() = bj_len + 2
        assert(r.len() == 2 + bj_len);

        // w_end = w1[0..pos1] ++ w1[pos1+bj_len+2..]
        // = w1[0..pos0-bj_len] ++ w1[pos0+2..]
        // = w[0..pos0-bj_len] ++ w[pos0..]
        let w_left = w.subrange(0, pos0 - bj_len);
        let w_right = w.subrange(pos0, w.len() as int);
        assert(w_end =~= w1.subrange(0, pos1) + w1.subrange(pos1 + r.len() as int, w1.len() as int));
        assert(pos1 + r.len() as int == pos0 + 2);
        assert(w1.subrange(0, pos1) =~= w_left);

        assert forall|k: int| 0 <= k < w.len() - pos0
            implies #[trigger] w1[(pos0 + 2 + k) as int] == w[(pos0 + k) as int]
        by {
            assert(w1[(pos0 + 2 + k) as int] == right_w[k]);
            assert(right_w[k] == w[(pos0 + k) as int]);
        }
        assert(w1.subrange(pos0 + 2, w1.len() as int) =~= w_right);
        assert(w_end =~= w_left + w_right);

        // w[pos0-bj_len..pos0] = b_j (from relator matching)
        assert forall|k: int| 0 <= k < bj_len
            implies w[(pos0 - bj_len + k) as int] == #[trigger] b_j[k]
        by {
            // r[k] = b_j[k] (first bj_len symbols of inverted relator)
            // r[k] = w1[pos1+k] = w1[pos0-bj_len+k]
            // Since pos0-bj_len+k < pos0: w1[pos0-bj_len+k] = w[pos0-bj_len+k]
            assert(w1[(pos1 + k) as int] == r[k]);
            assert(pos1 + k < pos0);
            assert(w1[(pos1 + k) as int] == left_w[(pos1 + k) as int]);
            assert(left_w[(pos1 + k) as int] == w[(pos1 + k) as int]);
            // Now show r[k] = b_j[k]
            let inv_r_full = b_j + Seq::new(1, |_i: int| stable_letter_inv(data))
                + inverse_word(a_j) + Seq::new(1, |_i: int| stable_letter(data));
            assert(r =~= inv_r_full);
            assert(r[k] == (b_j + (Seq::new(1, |_i: int| stable_letter_inv(data))
                + inverse_word(a_j) + Seq::new(1, |_i: int| stable_letter(data))))[k]);
            assert((b_j + (Seq::new(1, |_i: int| stable_letter_inv(data))
                + inverse_word(a_j) + Seq::new(1, |_i: int| stable_letter(data))))[k] == b_j[k]);
        }
        let w_mid = w.subrange(pos0 - bj_len, pos0);
        assert(w_mid =~= b_j);

        // w = w_left ++ b_j ++ w_right
        assert(w =~= w_left + w.subrange(pos0 - bj_len, w.len() as int));
        assert(w.subrange(pos0 - bj_len, w.len() as int) =~= w_mid + w_right);
        assert(w =~= w_left + (b_j + w_right));

        // By isomorphism: a_j = ε → b_j ≡ ε
        lemma_empty_association_implies_trivial(data, j);

        // w ≡ w_end by removing b_j from w
        lemma_remove_trivial_equiv(data.base, w_left, w_right, b_j);
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
                    // Case (d): RelatorInsert(HNN) + RelatorDelete — complex, deferred
                    assume(false);
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

/// The single segment lemma: if a derivation from base w to base w_end
/// has all non-base intermediates, then w ≡ w_end in G.
///
/// Strategy: induction on steps.len().
/// Base: steps.len() == 2 → lemma_single_segment_k2.
/// Step: Find a peak (stable count up then down), eliminate it.
///   - Peak elimination either:
///     (a) removes 2 steps (w_{i+1} = w_{i-1}), giving shorter segment, or
///     (b) introduces a base intermediate, splitting into two shorter segments.
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
    decreases steps.len(),
{
    if steps.len() == 2 {
        lemma_single_segment_k2(data, steps, w, w_end);
    } else {
        assume(false); // TODO: peak finding + elimination + recursion
        // 1. Find a peak at position i (1 ≤ i < steps.len())
        // 2. Eliminate the peak (case analysis on step types)
        // 3. Result: shorter derivation from w to w_end, possibly
        //    with a new base intermediate at position i
        // 4. If new base intermediate: split into two single segments
        // 5. Recurse on each (both shorter)
    }
}

// ============================================================
// Part 6: Word validity preservation
// ============================================================

/// Subrange of a word_valid word is word_valid.
proof fn lemma_subrange_word_valid(w: Word, lo: int, hi: int, n: nat)
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
proof fn lemma_step_preserves_word_valid(
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
/// Induction on derivation length.
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
    decreases steps.len(),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    if steps.len() == 0 {
        // w = ε
        assert(w =~= empty_word());
        lemma_equiv_refl(data.base, w);
    } else {
        let step0 = steps.first();
        let w1 = apply_step(hp, w, step0).unwrap();
        let rest = steps.drop_first();

        // w1 is word_valid for n+1
        lemma_step_preserves_word_valid(data, w, step0);

        if is_base_word(w1, n) {
            // Case 2: w1 is base. Step is base-to-base → valid in G.
            lemma_t_free_step_is_base_step(data, w, step0);
            lemma_single_step_equiv(data.base, w, step0, w1);

            // Recurse on shorter derivation
            britton_lemma_with_derivation(data, rest, w1);

            // Chain: w ≡_G w1 ≡_G ε
            lemma_equiv_transitive(data.base, w, w1, empty_word());
        } else {
            // Case 3: w1 is non-base. Find first base intermediate.
            lemma_empty_is_base_word(n);
            lemma_first_base_is_base(hp, steps, w, empty_word(), n);
            let k = first_base_intermediate(hp, steps, w, n);
            // k >= 2 since w1 is not base
            // k >= 2 since w1 is not base
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
            lemma_derivation_split(hp, steps, w, empty_word(), k);
            let left_steps = steps.subrange(0, k as int);
            let right_steps = steps.subrange(k as int, steps.len() as int);
            lemma_word_at_produces(hp, steps, w, k);
            // left_steps derives w → w_k, right_steps derives w_k → ε

            // w_k is word_valid
            lemma_word_at_valid(data, steps, w, k);

            // Right: w_k ≡_G ε by IH (right_steps.len() < steps.len())
            britton_lemma_with_derivation(data, right_steps, w_k);

            // Left: w ≡_G w_k by single segment lemma
            // Need: all intermediates w_1,...,w_{k-1} are non-base
            // w1 = derivation_word_at(hp, steps, w, 1) is !base (known)
            // For 1 < j < k: lemma_no_base_before_first
            lemma_single_segment(data, left_steps, w, w_k);

            // Chain: w ≡_G w_k ≡_G ε
            lemma_equiv_transitive(data.base, w, w_k, empty_word());
        }
    }
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
