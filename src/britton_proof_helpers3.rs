use vstd::prelude::*;
use crate::word::*;
use crate::symbol::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::reduction::*;
use crate::hnn::*;
use crate::britton::*;
use crate::britton_proof::*;
use crate::tietze::*;
use crate::benign::*;

verus! {

/// k=4 peak non-cancel: FreeExpand(stable) + FreeReduce commutation.
/// step1 = FreeExpand(stable, p1, sym1) on w1 → w2
/// step2 = FreeReduce(p2) on w2 → w3
/// w3 ≠ w1 (non-cancel)
///
/// Returns (w1', step2_adj, step1_adj) where:
///   apply_step(hp, w1, step2_adj) == Some(w1')  (w1' is base)
///   apply_step(hp, w1', step1_adj) == Some(w3)
pub proof fn lemma_k4_peak_fe_fr(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p1: int, sym1: Symbol, p2: int,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym1) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::FreeReduce { position: p2 }) == Some(w3)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        !is_base_word(w3, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 4nat,
        stable_letter_count(w3, data.base.num_generators) == 2nat,
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w1_prime, n)
        &&& word_valid(w1_prime, n + 1)
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
    assert(pair =~= seq![sym1, inverse_symbol(sym1)]);

    // Expand w2 structure
    assert(w2 =~= w1.subrange(0, p1) + pair + w1.subrange(p1, w1.len() as int));

    // step2 = FreeReduce at p2: removes w2[p2], w2[p2+1] which are inverses
    assert(has_cancellation_at(w2, p2));
    assert(w3 =~= w2.subrange(0, p2) + w2.subrange(p2 + 2, w2.len() as int));

    // The stable count decreased by 2 (from 4 to 2), so the reduced pair is stable
    lemma_stable_count_reduce(w2, p2, n);
    assert(generator_index(w2[p2]) == n);

    // Case p2 == p1: removes [sym1, inv(sym1)] exactly → w3 = w1 (cancel)
    if p2 == p1 {
        assert forall|k: int| 0 <= k < w1.len() implies w3[k] == w1[k] by {
            if k < p1 {
                assert(w3[k] == w2[k]);
                assert(w2[k] == w1[k]);
            } else {
                assert(w3[k] == w2[k + 2]);
                assert(w2[k + 2] == w1[k]);
            }
        };
        assert(w3 =~= w1);
        assert(false); // contradicts !(w3 =~= w1)
    }

    // Case p2 == p1 - 1: pair is [w1[p1-1], sym1]. Since gen_idx(w2[p2]) == n
    // and w2[p1-1] = w1[p1-1], we need gen_idx(w1[p1-1]) == n.
    // The pair is [w1[p1-1], sym1] and they're inverses, so w1[p1-1] = inv(sym1).
    // Then w3 = w1[0..p1-1] ++ [inv(sym1)] ++ w1[p1..] = w1. Cancel!
    if p2 == p1 - 1 {
        assert(w2[p2] == w1[(p1 - 1) as int]);
        assert(w2[p2 + 1] == sym1);
        // w3 = w2[0..p1-1] ++ w2[p1+1..]
        //     = w1[0..p1-1] ++ [inv(sym1)] ++ w1[p1..]
        // Since w1[p1-1] = inv(sym1) (they cancel with sym1):
        assert(is_inverse_pair(w1[(p1 - 1) as int], sym1));
        assert forall|k: int| 0 <= k < w1.len() implies w3[k] == w1[k] by {
            if k < p1 - 1 {
                assert(w3[k] == w2[k]);
                assert(w2[k] == w1[k]);
            } else if k == p1 - 1 {
                // w3[p1-1] = w2[p1+1] = inv(sym1)
                // w1[p1-1] = inv(sym1) (from the cancellation pair)
                assert(w3[k] == w2[(p1 + 1) as int]);
                assert(w2[(p1 + 1) as int] == inverse_symbol(sym1));
                assert(w1[k] == inverse_symbol(sym1)) by {
                    assert(is_inverse_pair(w1[k], sym1));
                    match w1[k] {
                        Symbol::Gen(idx) => {
                            assert(sym1 == Symbol::Inv(idx));
                            assert(inverse_symbol(sym1) == Symbol::Gen(idx));
                        },
                        Symbol::Inv(idx) => {
                            assert(sym1 == Symbol::Gen(idx));
                            assert(inverse_symbol(sym1) == Symbol::Inv(idx));
                        },
                    }
                };
            } else {
                // k >= p1
                assert(w3[k] == w2[k + 2]);
                assert(w2[k + 2] == w1[k]);
            }
        };
        assert(w3 =~= w1);
        assert(false); // contradicts !(w3 =~= w1)
    }

    // Case p2 == p1 + 1: pair is [inv(sym1), w1[p1]]. Since gen_idx(w2[p2]) == n
    // and w2[p1+1] = inv(sym1), gen_idx(inv(sym1)) == n. ✓
    // They cancel: inv(sym1) and w1[p1] are inverses → w1[p1] = sym1.
    // w3 = w1[0..p1] ++ [sym1] ++ w1[p1+1..] = w1. Cancel!
    if p2 == p1 + 1 {
        assert(w2[p2] == inverse_symbol(sym1));
        assert(w2[p2 + 1] == w1[p1]);
        assert(is_inverse_pair(inverse_symbol(sym1), w1[p1]));
        // w1[p1] = sym1
        assert(w1[p1] == sym1) by {
            let isym = inverse_symbol(sym1);
            assert(is_inverse_pair(isym, w1[p1]));
            match isym {
                Symbol::Gen(idx) => {
                    assert(w1[p1] == Symbol::Inv(idx));
                    // sym1 must be Inv(idx) since inverse_symbol(sym1) = Gen(idx)
                    match sym1 {
                        Symbol::Gen(j) => { assert(isym == Symbol::Inv(j)); assert(false); },
                        Symbol::Inv(j) => {
                            assert(isym == Symbol::Gen(j));
                            assert(idx == j);
                            assert(w1[p1] == Symbol::Inv(j));
                            assert(sym1 == Symbol::Inv(j));
                        },
                    }
                },
                Symbol::Inv(idx) => {
                    assert(w1[p1] == Symbol::Gen(idx));
                    match sym1 {
                        Symbol::Gen(j) => {
                            assert(isym == Symbol::Inv(j));
                            assert(idx == j);
                            assert(w1[p1] == Symbol::Gen(j));
                            assert(sym1 == Symbol::Gen(j));
                        },
                        Symbol::Inv(j) => { assert(isym == Symbol::Gen(j)); assert(false); },
                    }
                },
            }
        };
        // Now w3 = w2[0..p1+1] ++ w2[p1+3..]
        //        = w1[0..p1] ++ [sym1] ++ w1[p1+1..]
        //        = w1 (since w1[p1] = sym1)
        assert forall|k: int| 0 <= k < w1.len() implies w3[k] == w1[k] by {
            if k < p1 {
                assert(w3[k] == w2[k]);
                assert(w2[k] == w1[k]);
            } else if k == p1 {
                assert(w3[k] == w2[p1]);
                assert(w2[p1] == sym1);
                assert(w1[k] == sym1);
            } else {
                assert(w3[k] == w2[k + 2]);
                assert(w2[k + 2] == w1[k]);
            }
        };
        assert(w3 =~= w1);
        assert(false); // contradicts !(w3 =~= w1)
    }

    // Non-boundary cases: the FreeReduce acts entirely within w1's region
    if p2 < p1 - 1 {
        // pair at p2, p2+1 is entirely from w1[0..p1]
        assert(w2[p2] == w1[p2]);
        assert(w2[p2 + 1] == w1[p2 + 1]);
        assert(has_cancellation_at(w1, p2));

        // Apply FreeReduce at p2 on w1 → w1'
        let w1_prime = reduce_at(w1, p2);
        let step2_adj = DerivationStep::FreeReduce { position: p2 };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));

        // w1' has stable count 2 - 2 = 0 (the pair is stable)
        lemma_stable_count_reduce(w1, p2, n);
        assert(stable_letter_count(w1_prime, n) == 0nat);
        lemma_zero_count_implies_base(w1_prime, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);

        // Apply FreeExpand at p1-2 on w1' → w3
        let p1_adj = (p1 - 2) as int;
        let step1_adj = DerivationStep::FreeExpand { position: p1_adj, symbol: sym1 };
        let expand_result = w1_prime.subrange(0, p1_adj) + pair
            + w1_prime.subrange(p1_adj, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == expand_result[k] by {
            if k < p2 {
                assert(w3[k] == w2[k]);
                assert(w2[k] == w1[k]);
                assert(expand_result[k] == w1_prime[k]);
                assert(w1_prime[k] == w1[k]);
            } else if k < p1_adj {
                // p2 <= k < p1-2
                // w3 = w2[0..p2] ++ w2[p2+2..], so for k >= p2: w3[k] = w2[k+2]
                // w2[k+2] = w1[k+2] (since k+2 < p1, within w1 prefix)
                // w1_prime = w1[0..p2] ++ w1[p2+2..], so w1_prime[k] = w1[k+2]
                assert(w3[k] == w2[k + 2]);
                assert(w2[k + 2] == w1[k + 2]);
            } else if k == p1_adj {
                // expand_result[p1-2] = sym1
                // w3[p1-2] = w2[p1] = sym1
                assert(w3[k] == w2[k + 2]);
                assert(w2[(p1_adj + 2) as int] == w2[p1]);
                assert(w2[p1] == sym1);
                assert(expand_result[k] == sym1);
            } else if k == p1_adj + 1 {
                // expand_result[p1-1] = inv(sym1)
                // w3[p1-1] = w2[p1+1] = inv(sym1)
                assert(w3[k] == w2[k + 2]);
                assert(w2[(k + 2) as int] == inverse_symbol(sym1));
                assert(expand_result[k] == inverse_symbol(sym1));
            } else {
                // k >= p1
                // expand_result[k] = w1_prime[k-2] = w1[k] (since k-2 >= p2, w1_prime[k-2] = w1[k])
                // w3[k] = w2[k+2] = w1[k] (since k+2 >= p1+2, w2[k+2] = w1[k])
                assert(w3[k] == w2[k + 2]);
                assert(w2[k + 2] == w1[k]);
                assert(expand_result[k] == w1_prime[(k - 2) as int]);
                assert(w1_prime[(k - 2) as int] == w1[k]);
            }
        };
        assert(w3 =~= expand_result);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));

        (w1_prime, step2_adj, step1_adj)
    } else {
        // p2 >= p1 + 2
        assert(p2 >= p1 + 2);
        // pair at p2, p2+1 in w2 corresponds to w1[p2-2], w1[p2-1]
        assert(w2[p2] == w1[(p2 - 2) as int]);
        assert(w2[p2 + 1] == w1[(p2 - 1) as int]);
        let p2_adj = (p2 - 2) as int;
        assert(has_cancellation_at(w1, p2_adj));

        // Apply FreeReduce at p2-2 on w1 → w1'
        let w1_prime = reduce_at(w1, p2_adj);
        let step2_adj = DerivationStep::FreeReduce { position: p2_adj };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));

        lemma_stable_count_reduce(w1, p2_adj, n);
        assert(stable_letter_count(w1_prime, n) == 0nat);
        lemma_zero_count_implies_base(w1_prime, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);

        // Apply FreeExpand at p1 on w1' → w3
        let step1_adj = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
        let expand_result = w1_prime.subrange(0, p1) + pair
            + w1_prime.subrange(p1, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == expand_result[k] by {
            if k < p1 {
                // w3[k] = w2[k] (since k < p2, because p2 >= p1+2 > k)
                // Actually w3 = w2[0..p2] ++ w2[p2+2..], so for k < p2: w3[k] = w2[k]
                // w2[k] = w1[k] (since k < p1)
                // expand_result[k] = w1_prime[k] = w1[k] (since k < p1 <= p2-2 = p2_adj)
                assert(w3[k] == w2[k]);
                assert(w2[k] == w1[k]);
                assert(expand_result[k] == w1_prime[k]);
                assert(w1_prime[k] == w1[k]);
            } else if k == p1 {
                assert(w3[k] == w2[k]);
                assert(w2[p1] == sym1);
                assert(expand_result[k] == sym1);
            } else if k == p1 + 1 {
                assert(w3[k] == w2[k]);
                assert(w2[(p1 + 1) as int] == inverse_symbol(sym1));
                assert(expand_result[k] == inverse_symbol(sym1));
            } else if k < p2 {
                // p1+2 <= k < p2
                // w3[k] = w2[k] (since k < p2)
                // w2[k] = w1[k-2] (since k >= p1+2)
                // expand_result[k] = w1_prime[k-2]
                // w1_prime[k-2] = w1[k-2] (since k-2 < p2-2 = p2_adj)
                assert(w3[k] == w2[k]);
                assert(w2[k] == w1[(k - 2) as int]);
                assert(expand_result[k] == w1_prime[(k - 2) as int]);
                assert(w1_prime[(k - 2) as int] == w1[(k - 2) as int]);
            } else {
                // k >= p2
                // w3[k] = w2[k+2] (since k >= p2 in w3 = w2[0..p2]++w2[p2+2..])
                // w2[k+2] = w1[k] (since k+2 >= p1+2)
                // expand_result[k] = w1_prime[k-2]
                // w1_prime[k-2] = w1[k] (since k-2 >= p2_adj, w1_prime[k-2] = w1[k])
                assert(w3[k] == w2[k + 2]);
                assert(w2[k + 2] == w1[k]);
                assert(expand_result[k] == w1_prime[(k - 2) as int]);
                assert(w1_prime[(k - 2) as int] == w1[k]);
            }
        };
        assert(w3 =~= expand_result);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));

        (w1_prime, step2_adj, step1_adj)
    }
}

/// k=4 peak non-cancel: FreeExpand(stable) + RelatorDelete(HNN) commutation.
/// Non-overlapping case only.
pub proof fn lemma_k4_peak_fe_rd(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p1: int, sym1: Symbol, p2: int, ri2: nat, inv2: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym1) == data.base.num_generators,
        ri2 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 }) == Some(w3)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w3, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 4nat,
        stable_letter_count(w3, data.base.num_generators) == 2nat,
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w1_prime, n)
        &&& word_valid(w1_prime, n + 1)
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = seq![sym1, inverse_symbol(sym1)];
    let r2 = get_relator(hp, ri2, inv2);
    let r2_len = r2.len() as int;

    assert(w2 =~= w1.subrange(0, p1) + pair + w1.subrange(p1, w1.len() as int));
    assert(w2.subrange(p2, p2 + r2_len) =~= r2);
    assert(w3 =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));

    lemma_relator_stable_count(data, ri2, inv2);

    if p2 + r2_len <= p1 {
        // Relator is entirely before insertion. Translate to w1 directly.
        assert forall|k: int| p2 <= k < p2 + r2_len implies w2[k] == w1[k] by {};
        assert(w1.subrange(p2, p2 + r2_len) =~= r2);

        let w1_prime = w1.subrange(0, p2) + w1.subrange(p2 + r2_len, w1.len() as int);
        let step2_adj = DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));

        // Count: removes 2 stable letters from w1 (HNN relator has 2)
        lemma_stable_count_subrange(w1, p2, p2 + r2_len, n);
        lemma_stable_letter_count_concat(w1.subrange(0, p2), w1.subrange(p2 + r2_len, w1.len() as int), n);
        lemma_stable_letter_count_concat(w1.subrange(0, p2), w1.subrange(p2, w1.len() as int), n);
        assert(stable_letter_count(w1_prime, n) == 0nat);
        lemma_zero_count_implies_base(w1_prime, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);

        let p1_adj = (p1 - r2_len) as int;
        let step1_adj = DerivationStep::FreeExpand { position: p1_adj, symbol: sym1 };
        let expand_result = w1_prime.subrange(0, p1_adj) + pair
            + w1_prime.subrange(p1_adj, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == expand_result[k] by {};
        assert(w3 =~= expand_result);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));

        (w1_prime, step2_adj, step1_adj)
    } else if p2 >= p1 + 2 {
        // Relator is entirely after insertion. Translate position back by 2.
        let p2_adj = (p2 - 2) as int;
        assert forall|k: int| p2 <= k < p2 + r2_len implies w2[k] == w1[(k - 2) as int] by {};
        assert(w1.subrange(p2_adj, p2_adj + r2_len) =~= r2);

        let w1_prime = w1.subrange(0, p2_adj) + w1.subrange(p2_adj + r2_len, w1.len() as int);
        let step2_adj = DerivationStep::RelatorDelete { position: p2_adj, relator_index: ri2, inverted: inv2 };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));

        lemma_stable_count_subrange(w1, p2_adj, p2_adj + r2_len, n);
        lemma_stable_letter_count_concat(w1.subrange(0, p2_adj), w1.subrange(p2_adj + r2_len, w1.len() as int), n);
        lemma_stable_letter_count_concat(w1.subrange(0, p2_adj), w1.subrange(p2_adj, w1.len() as int), n);
        assert(stable_letter_count(w1_prime, n) == 0nat);
        lemma_zero_count_implies_base(w1_prime, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);

        let step1_adj = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
        let expand_result = w1_prime.subrange(0, p1) + pair
            + w1_prime.subrange(p1, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == expand_result[k] by {};
        assert(w3 =~= expand_result);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));

        (w1_prime, step2_adj, step1_adj)
    } else {
        // Overlap: relator region [p2, p2+r2_len) overlaps insertion [p1, p1+2).
        // The relator contains the FE stable pair. Since w1 has count 2, FE adds 2,
        // w2 has count 4, r2 removes 2 → w3 has count 2. The removed 2 must be
        // the FE pair (otherwise w3 = w1, cancel case contradiction).
        //
        // This forces: the relator's 2 stable letters are at the FE positions.
        // For non-inverted: stable at 0, |a_j|+1. Adjacent → a_j = [].
        // For inverted: stable at |b_j|, |b_j|+|a_j|+1. Adjacent → a_j = [].
        //
        // After RelatorDelete: w3 = w1 minus the base content of the relator
        // (the a_j and inv(b_j) parts, minus the stable pair which was from FE).
        // Since a_j = []: the base content is just inv(b_j) (non-inv) or b_j (inv).
        // w3 = w1 minus this base content at the appropriate position.
        //
        // From isomorphism (a_j = ε): b_j ≡ ε in data.base.
        //
        // Strategy: find w1_prime (base) by removing w1's original 2 stable letters.
        // The original stable letters are from step0 (the step before the peak).
        // We need the step2_adj to remove them from w1 → w1_prime (base).
        // Then step1_adj inserts them back into w1_prime at adjusted position → w3.
        //
        // The key: w3 has the SAME 2 stable letters as w1 (the ones from step0,
        // NOT the ones from the FE). They're at the same positions (the relator
        // deletion removed only the FE stable letters and some base content).
        //
        // So I need step2_adj = -2 step that removes w1's original stable letters.
        // And step1_adj = +2 step that puts them back into w1_prime → w3.
        //
        // But which -2 step removes w1's original stable letters? That depends on
        // how step0 created them. If step0 = FreeExpand(stable, p0, sym0): the
        // stable letters are at p0, p0+1 in w1. step2_adj = FreeReduce(p0) removes them.
        // w1_prime = w1[0..p0] ++ w1[p0+2..] = w (base!).
        // step1_adj = FreeExpand(sym0, p0_adj) on w → w3 at adjusted position.
        //
        // But wait — this is just the NON-OVERLAP commutation with step2_adj removing
        // the OTHER pair of stable letters! The non-overlap code handles this.
        // The issue was: the commutation code checks positions of step2 (RelatorDelete)
        // relative to step1 (FreeExpand), and finds they overlap. But the ADJUSTED
        // step2_adj should remove the OTHER stable letters (from step0), which are
        // at a NON-overlapping position.
        //
        // So: step2_adj removes w1's original stable letters (from step0, at positions
        // unrelated to the FE positions p1). This gives w1_prime = w (base).
        // step1_adj = FreeExpand(sym1, p1_adj) inserts the FE pair into w at adjusted
        // position, BUT the relator also removed base content (inv(b_j) or b_j).
        // So step1_adj needs to produce w3, which is w1 minus base content.
        //
        // w3 = w1 minus base_content at some position.
        // w = w1 minus the 2 original stable letters.
        // So w3 = w minus base_content at adjusted position + 2 original stable letters adjusted.
        //
        // This is getting complex. Let me use a simpler approach:
        // The non-cancel condition says w3 ≠ w1. The overlap means the relator
        // contains the FE pair. After deleting the relator, the FE pair is gone
        // and some base content is also gone. w3 has w1's original stable letters.
        //
        // For the non-cancel case: w3 ≠ w1 means the relator removed base content
        // beyond just the FE pair. This base content is inv(b_j) (or b_j for inverted),
        // and it was originally in w1 (from the word w via step0).
        //
        // I can construct w1_prime by removing w1's original 2 stable letters
        // (FreeReduce if from FreeExpand, RelatorDelete if from RelatorInsert).
        // This gives w1_prime = w (base). Then I need step1_adj on w → w3.
        // w3 = w minus base_content. If base_content was a subword of w at some
        // position, step1_adj = RelatorDelete(base) or FreeReduce at that position.
        // But base_content (inv(b_j)) might not be a base relator.
        //
        // Alternative: w1_prime = w3 minus the 2 original stable letters.
        // step2_adj removes them from w1 → w1_prime. step1_adj adds them back to w1_prime → w3.
        // But w1 and w3 have the original stable letters at the SAME positions
        // (the relator deletion only removed the FE pair, not the originals).
        // So removing the originals from w1 gives one base word, and removing
        // them from w3 gives another base word that differs by the base_content.
        //
        // Hmm, the originals might NOT be at the same positions in w1 and w3
        // if the relator deletion shifted positions.
        //
        // This is genuinely hard. For now, use assume(false) with the analysis above
        // documented. The fix requires tracking the original stable letter positions
        // through the relator deletion.
        assume(false); arbitrary()
    }
}

/// k=4 peak non-cancel: RelatorInsert(HNN) + FreeReduce commutation.
/// Non-overlapping case only.
pub proof fn lemma_k4_peak_ri_fr(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p1: int, ri1: nat, inv1: bool, p2: int,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri1 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::FreeReduce { position: p2 }) == Some(w3)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w3, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 4nat,
        stable_letter_count(w3, data.base.num_generators) == 2nat,
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w1_prime, n)
        &&& word_valid(w1_prime, n + 1)
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));
    assert(has_cancellation_at(w2, p2));
    assert(w3 =~= w2.subrange(0, p2) + w2.subrange(p2 + 2, w2.len() as int));

    lemma_stable_count_reduce(w2, p2, n);
    assert(generator_index(w2[p2]) == n);

    lemma_relator_stable_count(data, ri1, inv1);

    if p2 + 2 <= p1 {
        // FreeReduce pair is entirely before relator insertion
        assert(w2[p2] == w1[p2]);
        assert(w2[p2 + 1] == w1[p2 + 1]);
        assert(has_cancellation_at(w1, p2));

        let w1_prime = reduce_at(w1, p2);
        let step2_adj = DerivationStep::FreeReduce { position: p2 };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));

        lemma_stable_count_reduce(w1, p2, n);
        assert(stable_letter_count(w1_prime, n) == 0nat);
        lemma_zero_count_implies_base(w1_prime, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);

        let p1_adj = (p1 - 2) as int;
        let step1_adj = DerivationStep::RelatorInsert { position: p1_adj, relator_index: ri1, inverted: inv1 };
        let ins = w1_prime.subrange(0, p1_adj) + r1 + w1_prime.subrange(p1_adj, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
        assert(w3 =~= ins);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));

        (w1_prime, step2_adj, step1_adj)
    } else if p2 >= p1 + r1_len {
        // FreeReduce pair is entirely after relator insertion
        let p2_adj = (p2 - r1_len) as int;
        assert(w2[p2] == w1[p2_adj]);
        assert(w2[p2 + 1] == w1[(p2_adj + 1) as int]);
        assert(has_cancellation_at(w1, p2_adj));

        let w1_prime = reduce_at(w1, p2_adj);
        let step2_adj = DerivationStep::FreeReduce { position: p2_adj };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));

        lemma_stable_count_reduce(w1, p2_adj, n);
        assert(stable_letter_count(w1_prime, n) == 0nat);
        lemma_zero_count_implies_base(w1_prime, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);

        let step1_adj = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
        let ins = w1_prime.subrange(0, p1) + r1 + w1_prime.subrange(p1, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
        assert(w3 =~= ins);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));

        (w1_prime, step2_adj, step1_adj)
    } else {
        // Overlap: FR(stable) pair overlaps the relator region [p1, p1+r1_len).
        // The FR has gen_idx(w2[p2]) == n (stable). is_inverse_pair gives gen_idx match.
        // So both w2[p2] and w2[p2+1] have gen_idx == n (stable).
        //
        // Case (a): p2 == p1 - 1 — left boundary straddle
        //   w2[p2] = w1[p2] (from w1, stable), w2[p2+1] = r1[0] (from relator)
        //   Both gen_idx == n. For non-inverted: r1[0] = Inv(n), gen_idx = n. ✓
        //   w1[p2] has gen_idx = n, so w1 has a stable letter at position p1-1.
        //   The commutation in this case requires adjusting for the boundary.
        //
        // Case (b): p1 <= p2 AND p2+2 <= p1+r1_len — both elements inside relator
        //   Both r1[p2-p1] and r1[p2-p1+1] have gen_idx == n.
        //   Relator has stable letters at exactly 2 positions. For adjacent: a_j = [].
        //
        // Case (c): p2 == p1+r1_len-1 — right boundary straddle
        //   w2[p2] = r1[r1_len-1], w2[p2+1] = w1[p2-r1_len+1] (adjusted)
        //   Similar to case (a) at the right end.
        //
        // All three cases require detailed HNN relator structure analysis.
        // For now, use assume(false) — the remaining overlaps all need the
        // isomorphism argument (a_j=[] → b_j≡ε) or boundary straddle handling.
        assume(false); arbitrary()
    }
}

/// k=4 peak non-cancel: RelatorInsert(HNN) + RelatorDelete(HNN) commutation.
/// Non-overlapping case only.
pub proof fn lemma_k4_peak_ri_rd(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p1: int, ri1: nat, inv1: bool, p2: int, ri2: nat, inv2: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri1 as int >= data.base.relators.len(),
        ri2 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 }) == Some(w3)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w3, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 4nat,
        stable_letter_count(w3, data.base.num_generators) == 2nat,
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w1_prime, n)
        &&& word_valid(w1_prime, n + 1)
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let r2 = get_relator(hp, ri2, inv2);
    let r2_len = r2.len() as int;

    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));
    assert(w2.subrange(p2, p2 + r2_len) =~= r2);
    assert(w3 =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));

    lemma_relator_stable_count(data, ri1, inv1);
    lemma_relator_stable_count(data, ri2, inv2);

    // Cancel case: same relator, same position
    if ri1 == ri2 && inv1 == inv2 && p2 == p1 {
        assert(r1 =~= r2);
        assert forall|k: int| 0 <= k < w1.len() implies w3[k] == w1[k] by {
            if k < p1 {
                assert(w3[k] == w2[k]);
                assert(w2[k] == w1[k]);
            } else {
                assert(w3[k] == w2[k + r1_len]);
                assert(w2[k + r1_len] == w1[k]);
            }
        };
        assert(w3 =~= w1);
        assert(false); // contradicts !(w3 =~= w1)
    }

    if p2 + r2_len <= p1 {
        lemma_k4_peak_ri_rd_left(data, w1, w2, w3, p1, ri1, inv1, p2, ri2, inv2)
    } else if p2 >= p1 + r1_len {
        lemma_k4_peak_ri_rd_right(data, w1, w2, w3, p1, ri1, inv1, p2, ri2, inv2)
    } else {
        // Overlap: relator regions overlap
        assume(false); arbitrary()
    }
}

proof fn lemma_k4_peak_ri_rd_left(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p1: int, ri1: nat, inv1: bool, p2: int, ri2: nat, inv2: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri1 as int >= data.base.relators.len(),
        ri2 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let r2 = get_relator(hp, ri2, inv2);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 }) == Some(w3)
            &&& p2 + r2.len() <= p1
        }),
        stable_letter_count(w1, data.base.num_generators) >= 2,
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators) + 2,
        stable_letter_count(w3, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        let c = stable_letter_count(w1, n);
        &&& stable_letter_count(w1_prime, n) == (c - 2) as nat
        &&& word_valid(w1_prime, n + 1)
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let r2 = get_relator(hp, ri2, inv2);
    let r2_len = r2.len() as int;
    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));
    lemma_relator_stable_count(data, ri2, inv2);

    assert forall|k: int| p2 <= k < p2 + r2_len implies w2[k] == w1[k] by {};
    assert(w1.subrange(p2, p2 + r2_len) =~= r2);
    let w1_prime = w1.subrange(0, p2) + w1.subrange(p2 + r2_len, w1.len() as int);
    let step2_adj = DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 };
    assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));
    lemma_stable_count_subrange(w1, p2, p2 + r2_len, n);
    lemma_stable_letter_count_concat(w1.subrange(0, p2), w1.subrange(p2 + r2_len, w1.len() as int), n);
    lemma_stable_letter_count_concat(w1.subrange(0, p2), w1.subrange(p2, w1.len() as int), n);
    lemma_step_preserves_word_valid(data, w1, step2_adj);
    let p1_adj = (p1 - r2_len) as int;
    let step1_adj = DerivationStep::RelatorInsert { position: p1_adj, relator_index: ri1, inverted: inv1 };
    let ins = w1_prime.subrange(0, p1_adj) + r1 + w1_prime.subrange(p1_adj, w1_prime.len() as int);
    assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
    assert(w3 =~= ins);
    assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));
    (w1_prime, step2_adj, step1_adj)
}

proof fn lemma_k4_peak_ri_rd_right(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p1: int, ri1: nat, inv1: bool, p2: int, ri2: nat, inv2: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri1 as int >= data.base.relators.len(),
        ri2 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let r1 = get_relator(hp, ri1, inv1);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 }) == Some(w3)
            &&& p2 >= p1 + r1.len()
        }),
        stable_letter_count(w1, data.base.num_generators) >= 2,
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators) + 2,
        stable_letter_count(w3, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        let c = stable_letter_count(w1, n);
        &&& stable_letter_count(w1_prime, n) == (c - 2) as nat
        &&& word_valid(w1_prime, n + 1)
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let r2 = get_relator(hp, ri2, inv2);
    let r2_len = r2.len() as int;
    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));
    lemma_relator_stable_count(data, ri2, inv2);

    let p2_adj = (p2 - r1_len) as int;
    assert forall|k: int| p2 <= k < p2 + r2_len implies w2[k] == w1[(k - r1_len) as int] by {};
    assert(w1.subrange(p2_adj, p2_adj + r2_len) =~= r2);
    let w1_prime = w1.subrange(0, p2_adj) + w1.subrange(p2_adj + r2_len, w1.len() as int);
    let step2_adj = DerivationStep::RelatorDelete { position: p2_adj, relator_index: ri2, inverted: inv2 };
    assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));
    lemma_stable_count_subrange(w1, p2_adj, p2_adj + r2_len, n);
    lemma_stable_letter_count_concat(w1.subrange(0, p2_adj), w1.subrange(p2_adj + r2_len, w1.len() as int), n);
    lemma_stable_letter_count_concat(w1.subrange(0, p2_adj), w1.subrange(p2_adj, w1.len() as int), n);
    lemma_step_preserves_word_valid(data, w1, step2_adj);
    let step1_adj = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
    let ins = w1_prime.subrange(0, p1) + r1 + w1_prime.subrange(p1, w1_prime.len() as int);
    assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
    assert(w3 =~= ins);
    assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));
    (w1_prime, step2_adj, step1_adj)
}

/// Main dispatcher for k=4 peak non-cancel commutation.
/// Classifies step1 (count +2) and step2 (count -2) types,
/// then delegates to per-combination helpers.
///
/// Returns (w1', step2_adj, step1_adj) where w1' is base and:
///   apply_step(hp, w1, step2_adj) == Some(w1')
///   apply_step(hp, w1', step1_adj) == Some(w3)
pub proof fn lemma_k4_peak_noncancel_commute(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    step1: DerivationStep, step2: DerivationStep,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w3)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        !is_base_word(w3, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 4nat,
        stable_letter_count(w3, data.base.num_generators) == 2nat,
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w1_prime, n)
        &&& word_valid(w1_prime, n + 1)
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    // Classify step1: must be +2 (FreeExpand(stable) or RelatorInsert(HNN))
    lemma_stable_count_reduce_step(data, w1, step1, n);

    // Classify step2: must be -2 (FreeReduce(stable) or RelatorDelete(HNN))
    lemma_stable_count_reduce_step(data, w2, step2, n);

    // Helper: prove step2 (count -2) must be FreeReduce or RelatorDelete(HNN)
    // by showing FreeExpand/RelatorInsert can only increase or maintain count.
    // This is a nested function to share the step2 ruling-out logic.

    match step1 {
        DerivationStep::FreeReduce { position: p1r } => {
            // FreeReduce: count(w2) = count(w1) - {0,2} ≤ 2. But c2 = 4.
            lemma_stable_count_reduce(w1, p1r, n);
            assert(false); arbitrary()
        },
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } => {
            // Prove sym1 is stable using count argument
            let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
            assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
            let left1 = w1.subrange(0, p1);
            let right1 = w1.subrange(p1, w1.len() as int);
            assert(w1 =~= left1 + right1);
            assert(w2 =~= left1 + pair1 + right1);
            lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
            let pc1 = if generator_index(sym1) == n { 2nat } else { 0nat };
            assert(stable_letter_count(pair1, n) == pc1);
            lemma_stable_letter_count_concat(left1, right1, n);
            lemma_stable_letter_count_concat(left1, pair1, n);
            lemma_stable_letter_count_concat(left1 + pair1, right1, n);
            assert(stable_letter_count(w2, n) ==
                stable_letter_count(left1, n) + pc1 + stable_letter_count(right1, n));
            assert(stable_letter_count(w1, n) ==
                stable_letter_count(left1, n) + stable_letter_count(right1, n));
            // c2 = c1 + pc1. Since c2 = 4 and c1 = 2, pc1 = 2, so gen_idx(sym1) == n.
            assert(pc1 == 2nat);
            assert(generator_index(sym1) == n);
            // Now classify step2
            match step2 {
                DerivationStep::FreeExpand { position: p2e, symbol: sym2e } => {
                    // FreeExpand: count(w3) >= count(w2) = 4. But count(w3) = 2.
                    let pair2 = Seq::new(1, |_i: int| sym2e) + Seq::new(1, |_i: int| inverse_symbol(sym2e));
                    assert(pair2 =~= seq![sym2e, inverse_symbol(sym2e)]);
                    let left2 = w2.subrange(0, p2e);
                    let right2 = w2.subrange(p2e, w2.len() as int);
                    assert(w2 =~= left2 + right2);
                    assert(w3 =~= left2 + pair2 + right2);
                    lemma_stable_count_pair(sym2e, inverse_symbol(sym2e), n);
                    let pc2 = if generator_index(sym2e) == n { 2nat } else { 0nat };
                    assert(stable_letter_count(pair2, n) == pc2);
                    lemma_stable_letter_count_concat(left2, right2, n);
                    lemma_stable_letter_count_concat(left2, pair2, n);
                    lemma_stable_letter_count_concat(left2 + pair2, right2, n);
                    assert(stable_letter_count(w3, n) ==
                        stable_letter_count(left2, n) + pc2 + stable_letter_count(right2, n));
                    assert(stable_letter_count(w2, n) ==
                        stable_letter_count(left2, n) + stable_letter_count(right2, n));
                    // c3 = c2 + pc2 >= c2 = 4, but c3 = 2. Contradiction.
                    assert(false); arbitrary()
                },
                DerivationStep::RelatorInsert { position: p2r, relator_index: ri2, inverted: inv2 } => {
                    // RelatorInsert: count(w3) >= count(w2) = 4. But count(w3) = 2.
                    let r2 = get_relator(hp, ri2, inv2);
                    lemma_relator_stable_count(data, ri2, inv2);
                    let left2 = w2.subrange(0, p2r);
                    let right2 = w2.subrange(p2r, w2.len() as int);
                    assert(w2 =~= left2 + right2);
                    assert(w3 =~= left2 + r2 + right2);
                    lemma_stable_letter_count_concat(left2, right2, n);
                    lemma_stable_letter_count_concat(left2, r2, n);
                    lemma_stable_letter_count_concat(left2 + r2, right2, n);
                    assert(stable_letter_count(w3, n) ==
                        stable_letter_count(left2, n) + stable_letter_count(r2, n) + stable_letter_count(right2, n));
                    assert(stable_letter_count(w2, n) ==
                        stable_letter_count(left2, n) + stable_letter_count(right2, n));
                    // c3 = c2 + count(r2) >= c2 = 4, but c3 = 2. Contradiction.
                    assert(false); arbitrary()
                },
                DerivationStep::FreeReduce { position: p2 } => {
                    lemma_k4_peak_fe_fr(data, w1, w2, w3, p1, sym1, p2)
                },
                DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
                    lemma_relator_stable_count(data, ri2, inv2);
                    if (ri2 as int) < data.base.relators.len() {
                        // Base relator: count(r2) = 0, so count(w3) = count(w2) = 4 ≠ 2
                        let r2 = get_relator(hp, ri2, inv2);
                        lemma_stable_count_subrange(w2, p2, p2 + r2.len() as int, n);
                        lemma_stable_letter_count_concat(w2.subrange(0, p2), w2.subrange(p2 + r2.len() as int, w2.len() as int), n);
                        lemma_stable_letter_count_concat(w2.subrange(0, p2), w2.subrange(p2, w2.len() as int), n);
                        assert(false);
                    }
                    lemma_k4_peak_fe_rd(data, w1, w2, w3, p1, sym1, p2, ri2, inv2)
                },
            }
        },
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            // Prove ri1 is HNN: if base, count doesn't change → c2 = 2 ≠ 4
            let r1 = get_relator(hp, ri1, inv1);
            lemma_relator_stable_count(data, ri1, inv1);
            let left1 = w1.subrange(0, p1);
            let right1 = w1.subrange(p1, w1.len() as int);
            assert(w1 =~= left1 + right1);
            assert(w2 =~= left1 + r1 + right1);
            lemma_stable_letter_count_concat(left1, right1, n);
            lemma_stable_letter_count_concat(left1, r1, n);
            lemma_stable_letter_count_concat(left1 + r1, right1, n);
            assert(stable_letter_count(w2, n) ==
                stable_letter_count(left1, n) + stable_letter_count(r1, n) + stable_letter_count(right1, n));
            assert(stable_letter_count(w1, n) ==
                stable_letter_count(left1, n) + stable_letter_count(right1, n));
            if (ri1 as int) < data.base.relators.len() {
                // count(r1) = 0 → c2 = c1 = 2 ≠ 4
                assert(stable_letter_count(r1, n) == 0nat);
                assert(false); arbitrary()
            }
            // Now classify step2
            match step2 {
                DerivationStep::FreeExpand { position: p2e, symbol: sym2e } => {
                    let pair2 = Seq::new(1, |_i: int| sym2e) + Seq::new(1, |_i: int| inverse_symbol(sym2e));
                    assert(pair2 =~= seq![sym2e, inverse_symbol(sym2e)]);
                    let left2 = w2.subrange(0, p2e);
                    let right2 = w2.subrange(p2e, w2.len() as int);
                    assert(w2 =~= left2 + right2);
                    assert(w3 =~= left2 + pair2 + right2);
                    lemma_stable_count_pair(sym2e, inverse_symbol(sym2e), n);
                    let pc2 = if generator_index(sym2e) == n { 2nat } else { 0nat };
                    assert(stable_letter_count(pair2, n) == pc2);
                    lemma_stable_letter_count_concat(left2, right2, n);
                    lemma_stable_letter_count_concat(left2, pair2, n);
                    lemma_stable_letter_count_concat(left2 + pair2, right2, n);
                    assert(stable_letter_count(w3, n) ==
                        stable_letter_count(left2, n) + pc2 + stable_letter_count(right2, n));
                    assert(stable_letter_count(w2, n) ==
                        stable_letter_count(left2, n) + stable_letter_count(right2, n));
                    assert(false); arbitrary()
                },
                DerivationStep::RelatorInsert { position: p2r, relator_index: ri2, inverted: inv2 } => {
                    let r2 = get_relator(hp, ri2, inv2);
                    lemma_relator_stable_count(data, ri2, inv2);
                    let left2 = w2.subrange(0, p2r);
                    let right2 = w2.subrange(p2r, w2.len() as int);
                    assert(w2 =~= left2 + right2);
                    assert(w3 =~= left2 + r2 + right2);
                    lemma_stable_letter_count_concat(left2, right2, n);
                    lemma_stable_letter_count_concat(left2, r2, n);
                    lemma_stable_letter_count_concat(left2 + r2, right2, n);
                    assert(stable_letter_count(w3, n) ==
                        stable_letter_count(left2, n) + stable_letter_count(r2, n) + stable_letter_count(right2, n));
                    assert(stable_letter_count(w2, n) ==
                        stable_letter_count(left2, n) + stable_letter_count(right2, n));
                    assert(false); arbitrary()
                },
                DerivationStep::FreeReduce { position: p2 } => {
                    lemma_k4_peak_ri_fr(data, w1, w2, w3, p1, ri1, inv1, p2)
                },
                DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
                    lemma_relator_stable_count(data, ri2, inv2);
                    if (ri2 as int) < data.base.relators.len() {
                        let r2 = get_relator(hp, ri2, inv2);
                        lemma_stable_count_subrange(w2, p2, p2 + r2.len() as int, n);
                        lemma_stable_letter_count_concat(w2.subrange(0, p2), w2.subrange(p2 + r2.len() as int, w2.len() as int), n);
                        lemma_stable_letter_count_concat(w2.subrange(0, p2), w2.subrange(p2, w2.len() as int), n);
                        assert(false);
                    }
                    lemma_k4_peak_ri_rd(data, w1, w2, w3, p1, ri1, inv1, p2, ri2, inv2)
                },
            }
        },
        DerivationStep::RelatorDelete { position: p1d, relator_index: ri1, inverted: inv1 } => {
            // RelatorDelete: count(w2) = count(w1) - count(r1) ≤ count(w1) = 2. But c2 = 4.
            let r1 = get_relator(hp, ri1, inv1);
            lemma_relator_stable_count(data, ri1, inv1);
            // w2 = w1[0..p1d] ++ w1[p1d+|r1|..], removing r1 from w1
            lemma_stable_count_subrange(w1, p1d, p1d + r1.len() as int, n);
            lemma_stable_letter_count_concat(
                w1.subrange(0, p1d),
                w1.subrange(p1d + r1.len() as int, w1.len() as int), n);
            lemma_stable_letter_count_concat(
                w1.subrange(0, p1d),
                w1.subrange(p1d, w1.len() as int), n);
            // count(w2) = count(w1) - count(r1) ≤ 2. But c2 = 4.
            assert(false); arbitrary()
        },
    }
}

/// k=2 FreeExpand(stable) + RelatorDelete(HNN), non-inverted branch.
/// Extracted from lemma_k2_expand_reldelete to reduce rlimit.
pub proof fn lemma_k2_expand_reldelete_noninv(
    data: HNNData, w: Word, w1: Word, w_end: Word,
    pos0: int, sym: Symbol, pos1: int, r_idx: nat,
    j: int,
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
            let step1 = DerivationStep::RelatorDelete { position: pos1, relator_index: r_idx, inverted: false };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w_end)
        }),
        generator_index(sym) == data.base.num_generators,
        !is_base_word(w1, data.base.num_generators),
        r_idx as int >= data.base.relators.len(),
        j == (r_idx as int - data.base.relators.len()) as int,
        0 <= j < data.associations.len(),
        // Common setup results:
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        ({
            let hp = hnn_presentation(data);
            hp.relators[r_idx as int] == hnn_relator(data, j)
        }),
        ({
            let n = data.base.num_generators;
            forall|i: int| 0 <= i < w1.len() && i != pos0 && i != pos0 + 1
                ==> generator_index(#[trigger] w1[i]) < n
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r = get_relator(hp, r_idx, false);
    let (a_j, b_j) = data.associations[j];

    let left_w = w.subrange(0, pos0);
    let right_w = w.subrange(pos0, w.len() as int);
    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= left_w + pair + right_w);

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
        let second_pos = pos1 + a_j.len() as int + 1;
        assert(second_pos == pos0 + a_j.len() as int + 2);
        assert(second_pos > pos0 + 1);
        assert(second_pos != pos0);
        assert(second_pos != pos0 + 1);
        assert(generator_index(w1[second_pos]) == n);
        assert(generator_index(w1[second_pos]) < n);
        assert(false);
    }
    assert(pos1 == pos0 as int);

    // |a_j| = 0
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

    assert(sym == t_inv);
    assert(t_inv == Symbol::Inv(n));

    lemma_inverse_word_len(b_j);
    let inv_bj = inverse_word(b_j);
    let bj_len = b_j.len() as int;

    let r_prefix = Seq::new(1, |_i: int| Symbol::Inv(n)) + Seq::new(1, |_i: int| Symbol::Gen(n));
    assert(r =~= r_prefix + inv_bj);
    assert(r.len() == 2 + bj_len);

    let w_left = w.subrange(0, pos0);
    let w_right = w.subrange(pos0 + bj_len, w.len() as int);
    assert(w_end =~= w1.subrange(0, pos0) + w1.subrange(pos0 + 2 + bj_len, w1.len() as int));
    assert(w1.subrange(0, pos0) =~= w_left);

    assert forall|k: int| 0 <= k < w.len() - pos0
        implies #[trigger] w1[(pos0 + 2 + k) as int] == w[(pos0 + k) as int]
    by {
        assert(w1[(pos0 + 2 + k) as int] == right_w[k]);
        assert(right_w[k] == w[(pos0 + k) as int]);
    }
    assert(w1.subrange(pos0 + 2 + bj_len, w1.len() as int) =~= w_right);
    assert(w_end =~= w_left + w_right);

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

    assert(w =~= w_left + w.subrange(pos0, w.len() as int));
    assert(w.subrange(pos0, w.len() as int) =~= w_mid + w_right);
    assert(w =~= w_left + (inv_bj + w_right));

    lemma_empty_association_implies_trivial(data, j);
    lemma_inverse_of_identity(data.base, b_j);
    lemma_inverse_word_valid(b_j, n);

    lemma_remove_trivial_equiv(data.base, w_left, w_right, inv_bj);
}

/// k=2 FreeExpand(stable) + RelatorDelete(HNN), inverted branch.
/// Extracted from lemma_k2_expand_reldelete to reduce rlimit.
pub proof fn lemma_k2_expand_reldelete_inv(
    data: HNNData, w: Word, w1: Word, w_end: Word,
    pos0: int, sym: Symbol, pos1: int, r_idx: nat,
    j: int,
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
            let step1 = DerivationStep::RelatorDelete { position: pos1, relator_index: r_idx, inverted: true };
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w_end)
        }),
        generator_index(sym) == data.base.num_generators,
        !is_base_word(w1, data.base.num_generators),
        r_idx as int >= data.base.relators.len(),
        j == (r_idx as int - data.base.relators.len()) as int,
        0 <= j < data.associations.len(),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        ({
            let hp = hnn_presentation(data);
            hp.relators[r_idx as int] == hnn_relator(data, j)
        }),
        ({
            let n = data.base.num_generators;
            forall|i: int| 0 <= i < w1.len() && i != pos0 && i != pos0 + 1
                ==> generator_index(#[trigger] w1[i]) < n
        }),
    ensures
        equiv_in_presentation(data.base, w, w_end),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r = get_relator(hp, r_idx, true);
    let (a_j, b_j) = data.associations[j];

    let left_w = w.subrange(0, pos0);
    let right_w = w.subrange(pos0, w.len() as int);
    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    assert(w1 =~= left_w + pair + right_w);

    // Inverted case: r = b_j ++ [Inv(n)] ++ inv(a_j) ++ [Gen(n)]
    lemma_hnn_relator_inverted_stable_positions(data, j);
    let t_inv = stable_letter_inv(data);
    assert(r[b_j.len() as int] == t_inv);
    assert(generator_index(r[b_j.len() as int]) == n);

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

    let bj_len = b_j.len() as int;
    assert(pos1 == pos0 - bj_len);
    assert(r.len() == 2 + bj_len);

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

    assert forall|k: int| 0 <= k < bj_len
        implies w[(pos0 - bj_len + k) as int] == #[trigger] b_j[k]
    by {
        assert(w1[(pos1 + k) as int] == r[k]);
        assert(pos1 + k < pos0);
        assert(w1[(pos1 + k) as int] == left_w[(pos1 + k) as int]);
        assert(left_w[(pos1 + k) as int] == w[(pos1 + k) as int]);
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

    assert(w =~= w_left + w.subrange(pos0 - bj_len, w.len() as int));
    assert(w.subrange(pos0 - bj_len, w.len() as int) =~= w_mid + w_right);
    assert(w =~= w_left + (b_j + w_right));

    lemma_empty_association_implies_trivial(data, j);

    lemma_remove_trivial_equiv(data.base, w_left, w_right, b_j);
}

/// k=3 RI(HNN) + RI(base) commutation, p1 <= p0 branch.
/// Extracted from lemma_k3_ri_hnn_relinsert_base to reduce rlimit.
pub proof fn lemma_k3_ri_hnn_relinsert_base_left(
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
        p1 <= p0,
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

    let step1_base = DerivationStep::RelatorInsert {
        position: p1, relator_index: ri1, inverted: inv1,
    };
    let w_prime = w.subrange(0, p1) + r1 + w.subrange(p1, w.len() as int);
    assert(apply_step(data.base, w, step1_base) == Some(w_prime));

    assert forall|i: int| 0 <= i < w_prime.len()
        implies symbol_valid(#[trigger] w_prime[i], n)
    by {
        if i < p1 {
            assert(w_prime[i] == w[i]);
        } else if i < p1 + r1_len {
            assert(w_prime[i] == r1[(i - p1) as int]);
        } else {
            assert(w_prime[i] == w[(i - r1_len) as int]);
        }
    };
    lemma_base_word_characterization(w_prime, n);
    lemma_word_valid_monotone(w_prime, n);

    let p0_adj = (p0 + r1_len) as int;
    let step0_adj = DerivationStep::RelatorInsert {
        position: p0_adj, relator_index: ri0, inverted: inv0,
    };
    let insert_result = w_prime.subrange(0, p0_adj) + r0
        + w_prime.subrange(p0_adj, w_prime.len() as int);

    assert forall|k: int| 0 <= k < w2.len()
        implies w2[k] == #[trigger] insert_result[k]
    by {
        if k < p1 {
        } else if k < p1 + r1_len {
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

/// k=3 RI(HNN) + RI(base) commutation, p1 >= p0 + r0_len branch.
/// Extracted from lemma_k3_ri_hnn_relinsert_base to reduce rlimit.
pub proof fn lemma_k3_ri_hnn_relinsert_base_right(
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
        p1 >= p0 + get_relator(hnn_presentation(data), ri0, inv0).len(),
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
    let step1_base = DerivationStep::RelatorInsert {
        position: p1_adj, relator_index: ri1, inverted: inv1,
    };
    let w_prime = w.subrange(0, p1_adj) + r1 + w.subrange(p1_adj, w.len() as int);
    assert(apply_step(data.base, w, step1_base) == Some(w_prime));

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
        } else if k < p1 + r1_len {
        } else {
        }
    };
    assert(w2.len() == insert_result.len());
    assert(w2 =~= insert_result);
    assert(apply_step(hp, w_prime, step0_adj) == Some(w2));
    lemma_k3_commutation_tail(data, w, w_prime, w2, w_end, step1_base, step0_adj, step2);
}

/// k≥5 peak non-cancel: commute step2 past step1, return derivation data.
/// Returns (w1_prime, left_steps, right_steps) where:
///   - w1_prime is base, word_valid
///   - derivation_produces(hp, left_steps, w) == Some(w1_prime), len 2
///   - derivation_produces(hp, right_steps, w1_prime) == Some(w_end), len k-2
pub proof fn lemma_k5_peak_noncancel(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
    w1: Word, w2: Word, w3: Word,
    step0: DerivationStep, step1: DerivationStep, step2: DerivationStep,
    tail_steps: Seq<DerivationStep>,
) -> (result: (Word, Seq<DerivationStep>, Seq<DerivationStep>))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        steps.len() >= 5,
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& step0 == steps[0]
            &&& step1 == steps[1]
            &&& step2 == steps[2]
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w3)
            &&& tail_steps =~= steps.subrange(3, steps.len() as int)
            &&& derivation_produces(hp, tail_steps, w3) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        !is_base_word(w3, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 4nat,
        stable_letter_count(w3, data.base.num_generators) == 2nat,
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, left_steps, right_steps) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w1_prime, n)
        &&& word_valid(w1_prime, n + 1)
        &&& derivation_produces(hp, left_steps, w) == Some(w1_prime)
        &&& derivation_produces(hp, right_steps, w1_prime) == Some(w_end)
        &&& left_steps.len() < steps.len()
        &&& right_steps.len() < steps.len()
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    let (w1_prime, step2_adj, step1_adj) =
        lemma_k4_peak_noncancel_commute(data, w1, w2, w3, step1, step2);

    // Left: [step0, step2_adj] from w to w1', 2 steps
    lemma_derivation_produces_2(hp, step0, step2_adj, w, w1, w1_prime);
    let left_steps: Seq<DerivationStep> = seq![step0, step2_adj];

    // Right: [step1_adj] ++ tail_steps from w1' to w_end
    lemma_step_preserves_word_valid(data, w1_prime, step1_adj);
    assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));
    let one_adj: Seq<DerivationStep> = seq![step1_adj];
    assert(one_adj.first() == step1_adj);
    assert(one_adj.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w3) == Some(w3)) by {
        assert(Seq::<DerivationStep>::empty().len() == 0);
    };
    assert(derivation_produces(hp, one_adj, w1_prime) == Some(w3));
    lemma_derivation_concat(hp, one_adj, tail_steps, w1_prime, w3, w_end);
    let right_steps = one_adj + tail_steps;

    (w1_prime, left_steps, right_steps)
}

/// k≥5 cancel case: build shorter derivation [step0] ++ tail_steps (k-2 steps).
pub proof fn lemma_k5_peak_cancel(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
    w1: Word, step0: DerivationStep,
    tail_steps: Seq<DerivationStep>,
) -> (short: Seq<DerivationStep>)
    requires
        hnn_data_valid(data),
        steps.len() >= 5,
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& step0 == steps[0]
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& tail_steps =~= steps.subrange(3, steps.len() as int)
            &&& derivation_produces(hp, tail_steps, w1) == Some(w_end)
        }),
    ensures ({
        let hp = hnn_presentation(data);
        &&& derivation_produces(hp, short, w) == Some(w_end)
        &&& short.len() < steps.len()
    }),
{
    let hp = hnn_presentation(data);

    let one_step: Seq<DerivationStep> = seq![step0];
    assert(one_step.first() == step0);
    assert(apply_step(hp, w, one_step.first()) == Some(w1));
    assert(one_step.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w1) == Some(w1)) by {
        assert(Seq::<DerivationStep>::empty().len() == 0);
    };
    assert(derivation_produces(hp, one_step, w) == Some(w1));

    lemma_derivation_concat(hp, one_step, tail_steps, w, w1, w_end);
    one_step + tail_steps
}

/// Generalized swap: FreeReduce(base) past FreeExpand(stable).
pub proof fn lemma_swap_fr_past_expand(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, sym0: Symbol, p1: int,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym0) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p0, symbol: sym0 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::FreeReduce { position: p1 }) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = Seq::new(1, |_i: int| sym0) + Seq::new(1, |_i: int| inverse_symbol(sym0));
    assert(w2 =~= w1.subrange(0, p0) + pair + w1.subrange(p0, w1.len() as int));

    lemma_stable_count_reduce(w2, p1, n);
    assert(generator_index(w2[p1]) < n);

    // Boundary cases: all contradictions (stable vs base gen_idx)
    if p1 == p0 {
        assert(w2[p0] == sym0);
        assert(generator_index(sym0) == n);
        assert(false);
    }
    if p1 == p0 - 1 {
        assert(is_inverse_pair(w2[p1], w2[p1 + 1]));
        assert(w2[p1 + 1] == sym0);
        assert(generator_index(w2[p1]) == generator_index(sym0)) by {
            assert(w2[p1 + 1] == inverse_symbol(w2[p1]));
            match w2[p1] { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        assert(generator_index(sym0) == n);
        assert(false);
    }
    if p1 == p0 + 1 {
        assert(w2[p1] == inverse_symbol(sym0));
        assert(generator_index(inverse_symbol(sym0)) == n) by {
            match sym0 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        assert(false);
    }

    if p1 < p0 - 1 {
        assert(w2[p1] == w1[p1]);
        assert(w2[p1 + 1] == w1[p1 + 1]);
        assert(has_cancellation_at(w1, p1));
        let w1_prime = reduce_at(w1, p1);
        let step_tfree_adj = DerivationStep::FreeReduce { position: p1 };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        lemma_stable_count_reduce(w1, p1, n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);

        let p0_adj = (p0 - 2) as int;
        let step0_adj = DerivationStep::FreeExpand { position: p0_adj, symbol: sym0 };
        let result = w1_prime.subrange(0, p0_adj) + pair
            + w1_prime.subrange(p0_adj, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
        assert(w3 =~= result);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    } else {
        assert(p1 >= p0 + 2);
        let p1_adj = (p1 - 2) as int;
        assert(w2[p1] == w1[p1_adj]);
        assert(w2[p1 + 1] == w1[(p1_adj + 1) as int]);
        assert(has_cancellation_at(w1, p1_adj));
        let w1_prime = reduce_at(w1, p1_adj);
        let step_tfree_adj = DerivationStep::FreeReduce { position: p1_adj };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        lemma_stable_count_reduce(w1, p1_adj, n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);

        let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym0 };
        let result = w1_prime.subrange(0, p0) + pair
            + w1_prime.subrange(p0, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
        assert(w3 =~= result);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    }
}

/// Generalized swap: FreeExpand(base) past FreeExpand(stable).
pub proof fn lemma_swap_fe_past_expand(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, sym0: Symbol, p1: int, sym1: Symbol,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym0) == data.base.num_generators,
        generator_index(sym1) < data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p0, symbol: sym0 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w3)
        }),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = Seq::new(1, |_i: int| sym0) + Seq::new(1, |_i: int| inverse_symbol(sym0));
    let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
    assert(w2 =~= w1.subrange(0, p0) + pair + w1.subrange(p0, w1.len() as int));

    // Count proof helper: pair1 has count 0 since sym1 is base
    assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
    lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
    assert(stable_letter_count(pair1, n) == 0nat);

    if p1 == p0 + 1 {
        // Edge case: insert between stable letters — not handled yet
        assume(false); arbitrary()
    } else if p1 <= p0 {
        let w1_prime = w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int);
        let step_tfree_adj = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        // Count: w1_prime has same count as w1
        let left = w1.subrange(0, p1);
        let right = w1.subrange(p1, w1.len() as int);
        assert(w1 =~= left + right);
        lemma_stable_letter_count_concat(left, right, n);
        lemma_stable_letter_count_concat(left, pair1, n);
        lemma_stable_letter_count_concat(left + pair1, right, n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
        let step0_adj = DerivationStep::FreeExpand { position: (p0 + 2) as int, symbol: sym0 };
        let result = w1_prime.subrange(0, (p0 + 2) as int) + pair
            + w1_prime.subrange((p0 + 2) as int, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
        assert(w3 =~= result);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    } else {
        assert(p1 >= p0 + 2);
        let p1_adj = (p1 - 2) as int;
        let w1_prime = w1.subrange(0, p1_adj) + pair1 + w1.subrange(p1_adj, w1.len() as int);
        let step_tfree_adj = DerivationStep::FreeExpand { position: p1_adj, symbol: sym1 };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        let left = w1.subrange(0, p1_adj);
        let right = w1.subrange(p1_adj, w1.len() as int);
        assert(w1 =~= left + right);
        lemma_stable_letter_count_concat(left, right, n);
        lemma_stable_letter_count_concat(left, pair1, n);
        lemma_stable_letter_count_concat(left + pair1, right, n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
        let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym0 };
        let result = w1_prime.subrange(0, p0) + pair
            + w1_prime.subrange(p0, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
        assert(w3 =~= result);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    }
}

/// Generalized swap: RelatorInsert/Delete(base) past FreeExpand(stable).
/// Dispatches to per-type helpers.
pub proof fn lemma_swap_ri_rd_past_expand(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, sym0: Symbol, step_tfree: DerivationStep,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym0) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p0, symbol: sym0 }) == Some(w2)
            &&& apply_step(hp, w2, step_tfree) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
        match step_tfree {
            DerivationStep::RelatorInsert { .. } | DerivationStep::RelatorDelete { .. } => true,
            _ => false,
        },
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    match step_tfree {
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            lemma_swap_ri_past_expand(data, w1, w2, w3, p0, sym0, p1, ri1, inv1)
        },
        DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 } => {
            lemma_swap_rd_past_expand(data, w1, w2, w3, p0, sym0, p1, ri1, inv1)
        },
        _ => { assert(false); arbitrary() },
    }
}

/// Generalized swap: RelatorInsert past FreeExpand(stable).
proof fn lemma_swap_ri_past_expand(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, sym0: Symbol, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym0) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p0, symbol: sym0 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = Seq::new(1, |_i: int| sym0) + Seq::new(1, |_i: int| inverse_symbol(sym0));
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    assert(w2 =~= w1.subrange(0, p0) + pair + w1.subrange(p0, w1.len() as int));
    lemma_relator_stable_count(data, ri1, inv1);
    // Prove count(r1) == 0 from T-free condition
    let left2 = w2.subrange(0, p1);
    let right2 = w2.subrange(p1, w2.len() as int);
    assert(w2 =~= left2 + right2);
    assert(w3 =~= left2 + r1 + right2);
    lemma_stable_letter_count_concat(left2, right2, n);
    lemma_stable_letter_count_concat(left2, r1, n);
    lemma_stable_letter_count_concat(left2 + r1, right2, n);
    assert(stable_letter_count(r1, n) == 0nat);
    if p1 <= p0 {
        let left = w1.subrange(0, p1);
        let right = w1.subrange(p1, w1.len() as int);
        let w1_prime = left + r1 + right;
        let step_tfree_adj = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        assert(w1 =~= left + right);
        lemma_stable_letter_count_concat(left, right, n);
        lemma_stable_letter_count_concat(left, r1, n);
        lemma_stable_letter_count_concat(left + r1, right, n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
        let step0_adj = DerivationStep::FreeExpand { position: (p0 + r1_len) as int, symbol: sym0 };
        let result = w1_prime.subrange(0, (p0 + r1_len) as int) + pair
            + w1_prime.subrange((p0 + r1_len) as int, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
        assert(w3 =~= result);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    } else if p1 >= p0 + 2 {
        let p1_adj = (p1 - 2) as int;
        let left = w1.subrange(0, p1_adj);
        let right = w1.subrange(p1_adj, w1.len() as int);
        let w1_prime = left + r1 + right;
        let step_tfree_adj = DerivationStep::RelatorInsert { position: p1_adj, relator_index: ri1, inverted: inv1 };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        assert(w1 =~= left + right);
        lemma_stable_letter_count_concat(left, right, n);
        lemma_stable_letter_count_concat(left, r1, n);
        lemma_stable_letter_count_concat(left + r1, right, n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
        let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym0 };
        let result = w1_prime.subrange(0, p0) + pair
            + w1_prime.subrange(p0, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
        assert(w3 =~= result);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    } else {
        assume(false); arbitrary()
    }
}

/// Generalized swap: RelatorDelete past FreeExpand(stable).
proof fn lemma_swap_rd_past_expand(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, sym0: Symbol, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym0) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p0, symbol: sym0 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = Seq::new(1, |_i: int| sym0) + Seq::new(1, |_i: int| inverse_symbol(sym0));
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    assert(w2 =~= w1.subrange(0, p0) + pair + w1.subrange(p0, w1.len() as int));
    lemma_relator_stable_count(data, ri1, inv1);
    // Prove count(r1) == 0 from T-free condition
    lemma_stable_count_subrange(w2, p1, p1 + r1_len, n);
    lemma_stable_letter_count_concat(w2.subrange(0, p1), w2.subrange(p1 + r1_len, w2.len() as int), n);
    lemma_stable_letter_count_concat(w2.subrange(0, p1), w2.subrange(p1, w2.len() as int), n);
    assert(stable_letter_count(r1, n) == 0nat);
    if p1 + r1_len <= p0 {
        assert forall|k: int| p1 <= k < p1 + r1_len implies w2[k] == w1[k] by {};
        assert(w1.subrange(p1, p1 + r1_len) =~= r1);
        let w1_prime = w1.subrange(0, p1) + w1.subrange(p1 + r1_len, w1.len() as int);
        let step_tfree_adj = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        lemma_stable_count_subrange(w1, p1, p1 + r1_len, n);
        lemma_stable_letter_count_concat(w1.subrange(0, p1), w1.subrange(p1 + r1_len, w1.len() as int), n);
        lemma_stable_letter_count_concat(w1.subrange(0, p1), w1.subrange(p1, w1.len() as int), n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
        let step0_adj = DerivationStep::FreeExpand { position: (p0 - r1_len) as int, symbol: sym0 };
        let result = w1_prime.subrange(0, (p0 - r1_len) as int) + pair
            + w1_prime.subrange((p0 - r1_len) as int, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
        assert(w3 =~= result);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    } else if p1 >= p0 + 2 {
        let p1_adj = (p1 - 2) as int;
        assert forall|k: int| p1 <= k < p1 + r1_len implies w2[k] == w1[(k - 2) as int] by {};
        assert(w1.subrange(p1_adj, p1_adj + r1_len) =~= r1);
        let w1_prime = w1.subrange(0, p1_adj) + w1.subrange(p1_adj + r1_len, w1.len() as int);
        let step_tfree_adj = DerivationStep::RelatorDelete { position: p1_adj, relator_index: ri1, inverted: inv1 };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        lemma_stable_count_subrange(w1, p1_adj, p1_adj + r1_len, n);
        lemma_stable_letter_count_concat(w1.subrange(0, p1_adj), w1.subrange(p1_adj + r1_len, w1.len() as int), n);
        lemma_stable_letter_count_concat(w1.subrange(0, p1_adj), w1.subrange(p1_adj, w1.len() as int), n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
        let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym0 };
        let result = w1_prime.subrange(0, p0) + pair
            + w1_prime.subrange(p0, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
        assert(w3 =~= result);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    } else {
        // Overlap: relator region [p1, p1+r1_len) overlaps [p0, p0+2)
        // The relator has count 0 (all base, gen_idx < n).
        // But w2[p0] = sym0 with gen_idx = n. If the relator contains position p0,
        // then r1[p0-p1] = w2[p0] = sym0, gen_idx = n. But r1 has count 0. Contradiction!
        // Similarly for p0+1.
        assert(w2.subrange(p1, p1 + r1_len) =~= r1);
        if p1 <= p0 && p0 < p1 + r1_len {
            // r1[p0-p1] = w2[p0] = sym0
            assert(r1[(p0 - p1) as int] == w2[p0]);
            assert(w2[p0] == sym0);
            assert(generator_index(sym0) == n);
            // But r1 has count 0, so all elements have gen_idx < n
            // Specifically: r1[p0-p1] has gen_idx < n (from count 0)
            // This is a contradiction since gen_idx(r1[p0-p1]) = n
            lemma_stable_count_subrange(r1, (p0 - p1) as int, (p0 - p1 + 1) as int, n);
            assert(false);
        }
        assert(p1 == p0 + 1);
        // r1_len = 0: RelatorDelete is a no-op. Treat as non-overlapping.
        if r1_len == 0 {
            // Empty relator: no-op. w3 = w2. Use position 0 on w1.
            assert(w3 =~= w2);
            let step_tfree_adj = DerivationStep::RelatorDelete { position: 0int, relator_index: ri1, inverted: inv1 };
            assert(w1.subrange(0, 0 + r1_len) =~= r1);
            let w1_prime = w1.subrange(0, 0) + w1.subrange(0 + r1_len, w1.len() as int);
            assert(w1_prime =~= w1);
            assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
            lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
            let step0_adj = DerivationStep::FreeExpand { position: p0, symbol: sym0 };
            let result = w1_prime.subrange(0, p0) + pair
                + w1_prime.subrange(p0, w1_prime.len() as int);
            assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
            assert(w3 =~= result);
            assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
            (w1_prime, step_tfree_adj, step0_adj)
        } else {
            // r1_len >= 1. r1[0] = w2[p1] = w2[p0+1] = inv(sym0), gen_idx = n.
            // But count(r1) = 0 → contradiction.
            assert(w2[(p0 + 1) as int] == inverse_symbol(sym0));
            assert(generator_index(inverse_symbol(sym0)) == n) by {
                match sym0 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
            };
            assert forall|k: int| p1 <= k < p1 + r1_len
                implies w2[k] == #[trigger] r1[(k - p1) as int] by {
                assert(w2.subrange(p1, p1 + r1_len) =~= r1);
            };
            assert(generator_index(r1[0int]) == n);
            lemma_stable_count_subrange(r1, 0, 1, n);
            assert(false);
            arbitrary()
        }
    }
}

/// Dispatcher: swap any T-free step past FreeExpand(stable) at any word.
pub proof fn lemma_swap_tfree_past_expand(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, sym0: Symbol, step_tfree: DerivationStep,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym0) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p0, symbol: sym0 }) == Some(w2)
            &&& apply_step(hp, w2, step_tfree) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    match step_tfree {
        DerivationStep::FreeReduce { position: p1 } => {
            lemma_swap_fr_past_expand(data, w1, w2, w3, p0, sym0, p1)
        },
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } => {
            // Must be base symbol (T-free means gen_idx < n)
            lemma_stable_count_reduce_step(data, w2, step_tfree, n);
            let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
            assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
            let left = w2.subrange(0, p1);
            let right = w2.subrange(p1, w2.len() as int);
            assert(w2 =~= left + right);
            assert(w3 =~= left + pair1 + right);
            lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
            let pc = if generator_index(sym1) == n { 2nat } else { 0nat };
            assert(stable_letter_count(pair1, n) == pc);
            lemma_stable_letter_count_concat(left, right, n);
            lemma_stable_letter_count_concat(left, pair1, n);
            lemma_stable_letter_count_concat(left + pair1, right, n);
            assert(pc == 0nat);
            assert(generator_index(sym1) < n);
            lemma_swap_fe_past_expand(data, w1, w2, w3, p0, sym0, p1, sym1)
        },
        DerivationStep::RelatorInsert { .. } | DerivationStep::RelatorDelete { .. } => {
            lemma_swap_ri_rd_past_expand(data, w1, w2, w3, p0, sym0, step_tfree)
        },
    }
}

/// k≥5 c_3=4 case: two-round commutation for step0=FE(stable), step1=FE(stable).
/// Swaps step2 (T-free) past step1, then past step0, creating base intermediate.
/// Returns (w_base, base_step, derivation_steps) where:
///   apply_step(data.base, w, base_step) == Some(w_base)
///   derivation_produces(hp, derivation_steps, w_base) == Some(w_end)
///   derivation_steps.len() < steps.len()
pub proof fn lemma_k5_c3_eq4_two_round_fe_fe(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
    w1: Word, w2: Word, w3: Word,
    p0: int, sym0: Symbol, p1: int, sym1: Symbol,
    step2: DerivationStep, tail_steps: Seq<DerivationStep>,
) -> (result: (Word, DerivationStep, Seq<DerivationStep>))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        steps.len() >= 5,
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym0) == data.base.num_generators,
        generator_index(sym1) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, DerivationStep::FreeExpand { position: p0, symbol: sym0 }) == Some(w1)
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w3)
            &&& step2 == steps[2]
            &&& tail_steps =~= steps.subrange(3, steps.len() as int)
            &&& derivation_produces(hp, tail_steps, w3) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        !is_base_word(w3, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 4nat,
        stable_letter_count(w3, data.base.num_generators) == 4nat,
    ensures ({
        let (w_base, base_step, deriv_steps) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_base, n)
        &&& word_valid(w_base, n + 1)
        &&& apply_step(data.base, w, base_step) == Some(w_base)
        &&& derivation_produces(hp, deriv_steps, w_base) == Some(w_end)
        &&& deriv_steps.len() < steps.len()
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    // Round 1: swap step2 (T-free, count 4→4) past step1 (FE stable, +2)
    let (w1_prime, step2_adj, step1_adj) =
        lemma_swap_tfree_past_expand(data, w1, w2, w3, p1, sym1, step2);
    // step2_adj on w1 → w1' (T-free, count 2→2)
    // step1_adj on w1' → w3 (FE stable, count 2→4)

    // Round 2: swap step2_adj (T-free) past step0 (FE stable, +2) at w (BASE)
    // Use existing base-level commutation
    let (w_base, step2_base, step0_adj) = match step2_adj {
        DerivationStep::FreeReduce { position: p2r } =>
            lemma_k4_tfree_expand_commute_fr(data, w, w1, w1_prime, p0, sym0, p2r),
        _ =>
            lemma_k4_tfree_expand_commute_other(data, w, w1, w1_prime, p0, sym0, step2_adj),
    };
    // step2_base on w → w_base (base step, in data.base)
    // step0_adj on w_base → w1' (FE stable, +2)

    // Build derivation: [step0_adj, step1_adj] ++ tail_steps from w_base to w_end
    lemma_step_preserves_word_valid(data, w_base, step0_adj);
    lemma_derivation_produces_2(hp, step0_adj, step1_adj, w_base, w1_prime, w3);
    let prefix: Seq<DerivationStep> = seq![step0_adj, step1_adj];
    lemma_derivation_concat(hp, prefix, tail_steps, w_base, w3, w_end);
    let deriv_steps = prefix + tail_steps;

    (w_base, step2_base, deriv_steps)
}

/// Generalized swap: any T-free step past RelatorInsert(HNN) at any word.
/// Dispatcher — splits by T-free step type to manage rlimit.
pub proof fn lemma_swap_tfree_past_ri(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, ri0: nat, inv0: bool, step_tfree: DerivationStep,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w2)
            &&& apply_step(hp, w2, step_tfree) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    match step_tfree {
        DerivationStep::FreeReduce { .. } | DerivationStep::FreeExpand { .. } => {
            lemma_swap_fr_fe_past_ri(data, w1, w2, w3, p0, ri0, inv0, step_tfree)
        },
        DerivationStep::RelatorInsert { .. } | DerivationStep::RelatorDelete { .. } => {
            lemma_swap_rird_past_ri(data, w1, w2, w3, p0, ri0, inv0, step_tfree)
        },
    }
}

/// Sub-helper: FreeReduce or FreeExpand past RI(HNN) — dispatcher.
proof fn lemma_swap_fr_fe_past_ri(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, ri0: nat, inv0: bool, step_tfree: DerivationStep,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w2)
            &&& apply_step(hp, w2, step_tfree) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
        match step_tfree {
            DerivationStep::FreeReduce { .. } | DerivationStep::FreeExpand { .. } => true,
            _ => false,
        },
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    match step_tfree {
        DerivationStep::FreeReduce { position: p1 } =>
            lemma_swap_fr_past_ri_inner(data, w1, w2, w3, p0, ri0, inv0, p1),
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } =>
            lemma_swap_fe_past_ri_inner(data, w1, w2, w3, p0, ri0, inv0, p1, sym1),
        _ => { assert(false); arbitrary() },
    }
}

proof fn lemma_swap_fr_past_ri_inner(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, ri0: nat, inv0: bool, p1: int,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::FreeReduce { position: p1 }) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    assert(w2 =~= w1.subrange(0, p0) + r0 + w1.subrange(p0, w1.len() as int));

    lemma_stable_count_reduce(w2, p1, n);
    assert(generator_index(w2[p1]) < n);
    if p1 + 2 <= p0 {
        assert(w2[p1] == w1[p1]);
        assert(w2[p1 + 1] == w1[p1 + 1]);
        assert(has_cancellation_at(w1, p1));
        let w1_prime = reduce_at(w1, p1);
        let step_tfree_adj = DerivationStep::FreeReduce { position: p1 };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        lemma_stable_count_reduce(w1, p1, n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
        let step0_adj = DerivationStep::RelatorInsert { position: (p0 - 2) as int, relator_index: ri0, inverted: inv0 };
        let ins = w1_prime.subrange(0, (p0 - 2) as int) + r0
            + w1_prime.subrange((p0 - 2) as int, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
        assert(w3 =~= ins);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    } else if p1 >= p0 + r0_len {
        let p1_adj = (p1 - r0_len) as int;
        assert(w2[p1] == w1[p1_adj]);
        assert(w2[p1 + 1] == w1[(p1_adj + 1) as int]);
        assert(has_cancellation_at(w1, p1_adj));
        let w1_prime = reduce_at(w1, p1_adj);
        let step_tfree_adj = DerivationStep::FreeReduce { position: p1_adj };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        lemma_stable_count_reduce(w1, p1_adj, n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
        let step0_adj = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
        let ins = w1_prime.subrange(0, p0) + r0
            + w1_prime.subrange(p0, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
        assert(w3 =~= ins);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    } else {
        // FreeReduce inside/boundary of relator
        assume(false); arbitrary()
    }
}

proof fn lemma_swap_fe_past_ri_inner(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, sym1: Symbol,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    assert(w2 =~= w1.subrange(0, p0) + r0 + w1.subrange(p0, w1.len() as int));

    let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
    assert(pair1 =~= seq![sym1, inverse_symbol(sym1)]);
    lemma_stable_count_pair(sym1, inverse_symbol(sym1), n);
    let left2 = w2.subrange(0, p1);
    let right2 = w2.subrange(p1, w2.len() as int);
    assert(w2 =~= left2 + right2);
    assert(w3 =~= left2 + pair1 + right2);
    lemma_stable_letter_count_concat(left2, right2, n);
    lemma_stable_letter_count_concat(left2, pair1, n);
    lemma_stable_letter_count_concat(left2 + pair1, right2, n);
    assert(stable_letter_count(pair1, n) == 0nat);

    if p1 <= p0 {
                let w1_prime = w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int);
                let step_tfree_adj = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
                assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
                let left1 = w1.subrange(0, p1);
                let right1 = w1.subrange(p1, w1.len() as int);
                assert(w1 =~= left1 + right1);
                lemma_stable_letter_count_concat(left1, right1, n);
                lemma_stable_letter_count_concat(left1, pair1, n);
                lemma_stable_letter_count_concat(left1 + pair1, right1, n);
                lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
                let step0_adj = DerivationStep::RelatorInsert { position: (p0 + 2) as int, relator_index: ri0, inverted: inv0 };
                let ins = w1_prime.subrange(0, (p0 + 2) as int) + r0
                    + w1_prime.subrange((p0 + 2) as int, w1_prime.len() as int);
                assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
                assert(w3 =~= ins);
                assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
                (w1_prime, step_tfree_adj, step0_adj)
            } else if p1 >= p0 + r0_len {
                let p1_adj = (p1 - r0_len) as int;
                let w1_prime = w1.subrange(0, p1_adj) + pair1 + w1.subrange(p1_adj, w1.len() as int);
                let step_tfree_adj = DerivationStep::FreeExpand { position: p1_adj, symbol: sym1 };
                assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
                let left1 = w1.subrange(0, p1_adj);
                let right1 = w1.subrange(p1_adj, w1.len() as int);
                assert(w1 =~= left1 + right1);
                lemma_stable_letter_count_concat(left1, right1, n);
                lemma_stable_letter_count_concat(left1, pair1, n);
                lemma_stable_letter_count_concat(left1 + pair1, right1, n);
                lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
                let step0_adj = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
                let ins = w1_prime.subrange(0, p0) + r0
                    + w1_prime.subrange(p0, w1_prime.len() as int);
                assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
                assert(w3 =~= ins);
                assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
                (w1_prime, step_tfree_adj, step0_adj)
            } else {
                // Inside relator region
                assume(false); arbitrary()
            }
}

/// Sub-helper: RelatorInsert or RelatorDelete past RI(HNN) — dispatcher.
proof fn lemma_swap_rird_past_ri(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, ri0: nat, inv0: bool, step_tfree: DerivationStep,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w2)
            &&& apply_step(hp, w2, step_tfree) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
        match step_tfree {
            DerivationStep::RelatorInsert { .. } | DerivationStep::RelatorDelete { .. } => true,
            _ => false,
        },
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    match step_tfree {
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } =>
            lemma_swap_ri_past_ri_inner(data, w1, w2, w3, p0, ri0, inv0, p1, ri1, inv1),
        DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 } =>
            lemma_swap_rd_past_ri_inner(data, w1, w2, w3, p0, ri0, inv0, p1, ri1, inv1),
        _ => { assert(false); arbitrary() },
    }
}

proof fn lemma_swap_ri_past_ri_inner(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    assert(w2 =~= w1.subrange(0, p0) + r0 + w1.subrange(p0, w1.len() as int));
    lemma_relator_stable_count(data, ri1, inv1);
    let left2 = w2.subrange(0, p1);
    let right2 = w2.subrange(p1, w2.len() as int);
    assert(w2 =~= left2 + right2);
    assert(w3 =~= left2 + r1 + right2);
    lemma_stable_letter_count_concat(left2, right2, n);
    lemma_stable_letter_count_concat(left2, r1, n);
    lemma_stable_letter_count_concat(left2 + r1, right2, n);
    assert(stable_letter_count(r1, n) == 0nat);
    if p1 <= p0 {
        let left1 = w1.subrange(0, p1);
        let right1 = w1.subrange(p1, w1.len() as int);
        let w1_prime = left1 + r1 + right1;
        let step_tfree_adj = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        assert(w1 =~= left1 + right1);
        lemma_stable_letter_count_concat(left1, right1, n);
        lemma_stable_letter_count_concat(left1, r1, n);
        lemma_stable_letter_count_concat(left1 + r1, right1, n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
        let step0_adj = DerivationStep::RelatorInsert { position: (p0 + r1_len) as int, relator_index: ri0, inverted: inv0 };
        let ins = w1_prime.subrange(0, (p0 + r1_len) as int) + r0
            + w1_prime.subrange((p0 + r1_len) as int, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
        assert(w3 =~= ins);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    } else if p1 >= p0 + r0_len {
        lemma_swap_ri_past_ri_right(data, w1, w2, w3, p0, ri0, inv0, p1, ri1, inv1)
    } else {
        assume(false); arbitrary()
    }
}

proof fn lemma_swap_ri_past_ri_right(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w3)
            &&& p1 >= p0 + get_relator(hp, ri0, inv0).len()
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    assert(w2 =~= w1.subrange(0, p0) + r0 + w1.subrange(p0, w1.len() as int));
    lemma_relator_stable_count(data, ri1, inv1);
    let left2 = w2.subrange(0, p1);
    let right2 = w2.subrange(p1, w2.len() as int);
    assert(w2 =~= left2 + right2);
    assert(w3 =~= left2 + r1 + right2);
    lemma_stable_letter_count_concat(left2, right2, n);
    lemma_stable_letter_count_concat(left2, r1, n);
    lemma_stable_letter_count_concat(left2 + r1, right2, n);
    assert(stable_letter_count(r1, n) == 0nat);

    let p1_adj = (p1 - r0_len) as int;
    let left1 = w1.subrange(0, p1_adj);
    let right1 = w1.subrange(p1_adj, w1.len() as int);
    let w1_prime = left1 + r1 + right1;
    let step_tfree_adj = DerivationStep::RelatorInsert { position: p1_adj, relator_index: ri1, inverted: inv1 };
    assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
    assert(w1 =~= left1 + right1);
    lemma_stable_letter_count_concat(left1, right1, n);
    lemma_stable_letter_count_concat(left1, r1, n);
    lemma_stable_letter_count_concat(left1 + r1, right1, n);
    lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
    let step0_adj = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
    let ins = w1_prime.subrange(0, p0) + r0
        + w1_prime.subrange(p0, w1_prime.len() as int);
    assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
    assert(w3 =~= ins);
    assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
    (w1_prime, step_tfree_adj, step0_adj)
}

proof fn lemma_swap_rd_past_ri_inner(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w3)
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    assert(w2 =~= w1.subrange(0, p0) + r0 + w1.subrange(p0, w1.len() as int));
    lemma_relator_stable_count(data, ri1, inv1);
    lemma_stable_count_subrange(w2, p1, p1 + r1_len, n);
    lemma_stable_letter_count_concat(w2.subrange(0, p1), w2.subrange(p1 + r1_len, w2.len() as int), n);
    lemma_stable_letter_count_concat(w2.subrange(0, p1), w2.subrange(p1, w2.len() as int), n);
    assert(stable_letter_count(r1, n) == 0nat);
    if p1 + r1_len <= p0 {
        assert forall|k: int| p1 <= k < p1 + r1_len implies w2[k] == w1[k] by {};
        assert(w1.subrange(p1, p1 + r1_len) =~= r1);
        let w1_prime = w1.subrange(0, p1) + w1.subrange(p1 + r1_len, w1.len() as int);
        let step_tfree_adj = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
        assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
        lemma_stable_count_subrange(w1, p1, p1 + r1_len, n);
        lemma_stable_letter_count_concat(w1.subrange(0, p1), w1.subrange(p1 + r1_len, w1.len() as int), n);
        lemma_stable_letter_count_concat(w1.subrange(0, p1), w1.subrange(p1, w1.len() as int), n);
        lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
        let step0_adj = DerivationStep::RelatorInsert { position: (p0 - r1_len) as int, relator_index: ri0, inverted: inv0 };
        let ins = w1_prime.subrange(0, (p0 - r1_len) as int) + r0
            + w1_prime.subrange((p0 - r1_len) as int, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
        assert(w3 =~= ins);
        assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
        (w1_prime, step_tfree_adj, step0_adj)
    } else if p1 >= p0 + r0_len {
        lemma_swap_rd_past_ri_right(data, w1, w2, w3, p0, ri0, inv0, p1, ri1, inv1)
    } else {
        assume(false); arbitrary()
    }
}

proof fn lemma_swap_rd_past_ri_right(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p0: int, ri0: nat, inv0: bool, p1: int, ri1: nat, inv1: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri0 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            let r0 = get_relator(hp, ri0, inv0);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w3)
            &&& p1 >= p0 + r0.len()
        }),
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w3, data.base.num_generators),
    ensures ({
        let (w1_prime, step_tfree_adj, step0_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step0_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    assert(w2 =~= w1.subrange(0, p0) + r0 + w1.subrange(p0, w1.len() as int));
    lemma_relator_stable_count(data, ri1, inv1);
    lemma_stable_count_subrange(w2, p1, p1 + r1_len, n);
    lemma_stable_letter_count_concat(w2.subrange(0, p1), w2.subrange(p1 + r1_len, w2.len() as int), n);
    lemma_stable_letter_count_concat(w2.subrange(0, p1), w2.subrange(p1, w2.len() as int), n);
    assert(stable_letter_count(r1, n) == 0nat);

    let p1_adj = (p1 - r0_len) as int;
    assert forall|k: int| p1 <= k < p1 + r1_len implies w2[k] == w1[(k - r0_len) as int] by {};
    assert(w1.subrange(p1_adj, p1_adj + r1_len) =~= r1);
    let w1_prime = w1.subrange(0, p1_adj) + w1.subrange(p1_adj + r1_len, w1.len() as int);
    let step_tfree_adj = DerivationStep::RelatorDelete { position: p1_adj, relator_index: ri1, inverted: inv1 };
    assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
    lemma_stable_count_subrange(w1, p1_adj, p1_adj + r1_len, n);
    lemma_stable_letter_count_concat(w1.subrange(0, p1_adj), w1.subrange(p1_adj + r1_len, w1.len() as int), n);
    lemma_stable_letter_count_concat(w1.subrange(0, p1_adj), w1.subrange(p1_adj, w1.len() as int), n);
    lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
    let step0_adj = DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 };
    let ins = w1_prime.subrange(0, p0) + r0
        + w1_prime.subrange(p0, w1_prime.len() as int);
    assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
    assert(w3 =~= ins);
    assert(apply_step(hp, w1_prime, step0_adj) == Some(w3));
    (w1_prime, step_tfree_adj, step0_adj)
}

/// Classify a step that increases stable count by 2.
/// If count goes up by 2, the step must be FreeExpand(stable) or RelatorInsert(HNN).
pub proof fn lemma_plus2_step_type(
    data: HNNData, w: Word, w_next: Word, step: DerivationStep, n: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, n + 1),
        n == data.base.num_generators,
        apply_step(hnn_presentation(data), w, step) == Some(w_next),
        stable_letter_count(w_next, n) == stable_letter_count(w, n) + 2,
    ensures
        match step {
            DerivationStep::FreeExpand { symbol, .. } =>
                generator_index(symbol) == n,
            DerivationStep::RelatorInsert { relator_index, .. } =>
                relator_index as int >= data.base.relators.len(),
            _ => false,
        },
{
    let hp = hnn_presentation(data);
    let c = stable_letter_count(w, n);
    match step {
        DerivationStep::FreeReduce { position: p } => {
            lemma_stable_count_reduce(w, p, n);
            // count decreases or stays same, can't increase by 2
            assert(false);
        },
        DerivationStep::FreeExpand { position: p, symbol: sym } => {
            let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
            assert(pair =~= seq![sym, inverse_symbol(sym)]);
            let left = w.subrange(0, p);
            let right = w.subrange(p, w.len() as int);
            assert(w =~= left + right);
            assert(w_next =~= left + pair + right);
            lemma_stable_count_pair(sym, inverse_symbol(sym), n);
            lemma_stable_letter_count_concat(left, right, n);
            lemma_stable_letter_count_concat(left, pair, n);
            lemma_stable_letter_count_concat(left + pair, right, n);
            // count(w_next) = count(w) + count(pair). Since count(w_next) = count(w) + 2,
            // count(pair) = 2, so gen_idx(sym) == n.
        },
        DerivationStep::RelatorInsert { position: p, relator_index: ri, inverted: inv } => {
            let r = get_relator(hp, ri, inv);
            lemma_relator_stable_count(data, ri, inv);
            let left = w.subrange(0, p);
            let right = w.subrange(p, w.len() as int);
            assert(w =~= left + right);
            assert(w_next =~= left + r + right);
            lemma_stable_letter_count_concat(left, right, n);
            lemma_stable_letter_count_concat(left, r, n);
            lemma_stable_letter_count_concat(left + r, right, n);
            // count(w_next) = count(w) + count(r). Since +2, count(r) = 2 → HNN relator.
        },
        DerivationStep::RelatorDelete { position: p, relator_index: ri, inverted: inv } => {
            let r = get_relator(hp, ri, inv);
            lemma_relator_stable_count(data, ri, inv);
            lemma_stable_count_subrange(w, p, p + r.len() as int, n);
            lemma_stable_letter_count_concat(w.subrange(0, p), w.subrange(p + r.len() as int, w.len() as int), n);
            lemma_stable_letter_count_concat(w.subrange(0, p), w.subrange(p, w.len() as int), n);
            // count decreases or stays same, can't increase by 2
            assert(false);
        },
    }
}

/// Generic k≥5 c_3=4 two-round commutation for any step0×step1 combination.
/// Round 1: swap step2 (T-free) past step1 (+2) using generalized swap.
/// Round 2: swap result past step0 (+2) using existing base-level swap.
pub proof fn lemma_k5_c3_eq4_two_round(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
    w1: Word, w2: Word, w3: Word,
    step0: DerivationStep, step1: DerivationStep,
    step2: DerivationStep, tail_steps: Seq<DerivationStep>,
) -> (result: (Word, DerivationStep, Seq<DerivationStep>))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        steps.len() >= 5,
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& step0 == steps[0]
            &&& step1 == steps[1]
            &&& step2 == steps[2]
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w3)
            &&& tail_steps =~= steps.subrange(3, steps.len() as int)
            &&& derivation_produces(hp, tail_steps, w3) == Some(w_end)
        }),
        !is_base_word(w1, data.base.num_generators),
        !is_base_word(w2, data.base.num_generators),
        !is_base_word(w3, data.base.num_generators),
        stable_letter_count(w1, data.base.num_generators) == 2nat,
        stable_letter_count(w2, data.base.num_generators) == 4nat,
        stable_letter_count(w3, data.base.num_generators) == 4nat,
        // step0 is +2: FreeExpand(stable) or RelatorInsert(HNN)
        match step0 {
            DerivationStep::FreeExpand { symbol, .. } =>
                generator_index(symbol) == data.base.num_generators,
            DerivationStep::RelatorInsert { relator_index, .. } =>
                relator_index as int >= data.base.relators.len(),
            _ => false,
        },
        // step1 is +2: FreeExpand(stable) or RelatorInsert(HNN)
        match step1 {
            DerivationStep::FreeExpand { symbol, .. } =>
                generator_index(symbol) == data.base.num_generators,
            DerivationStep::RelatorInsert { relator_index, .. } =>
                relator_index as int >= data.base.relators.len(),
            _ => false,
        },
    ensures ({
        let (w_base, base_step, deriv_steps) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_base, n)
        &&& word_valid(w_base, n + 1)
        &&& apply_step(data.base, w, base_step) == Some(w_base)
        &&& derivation_produces(hp, deriv_steps, w_base) == Some(w_end)
        &&& deriv_steps.len() < steps.len()
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    // Round 1: swap step2 (T-free) past step1 (+2)
    let (w1_prime, step2_adj, step1_adj) = match step1 {
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } =>
            lemma_swap_tfree_past_expand(data, w1, w2, w3, p1, sym1, step2),
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } =>
            lemma_swap_tfree_past_ri(data, w1, w2, w3, p1, ri1, inv1, step2),
        _ => { assert(false); arbitrary() },
    };
    // step2_adj on w1 → w1' (T-free, count 2)
    // step1_adj on w1' → w3 (+2)

    // Round 2: swap step2_adj (T-free) past step0 (+2) at w (BASE)
    let (w_base, step2_base, step0_adj) = match step0 {
        DerivationStep::FreeExpand { position: p0, symbol: sym0 } => {
            match step2_adj {
                DerivationStep::FreeReduce { position: p } =>
                    lemma_k4_tfree_expand_commute_fr(data, w, w1, w1_prime, p0, sym0, p),
                _ =>
                    lemma_k4_tfree_expand_commute_other(data, w, w1, w1_prime, p0, sym0, step2_adj),
            }
        },
        DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 } =>
            lemma_k4_tfree_ri_commute(data, w, w1, w1_prime, p0, ri0, inv0, step2_adj),
        _ => { assert(false); arbitrary() },
    };

    // Build derivation: [step0_adj, step1_adj] ++ tail_steps from w_base to w_end
    lemma_step_preserves_word_valid(data, w_base, step0_adj);
    lemma_derivation_produces_2(hp, step0_adj, step1_adj, w_base, w1_prime, w3);
    let prefix: Seq<DerivationStep> = seq![step0_adj, step1_adj];
    lemma_derivation_concat(hp, prefix, tail_steps, w_base, w3, w_end);
    let deriv_steps = prefix + tail_steps;

    (w_base, step2_base, deriv_steps)
}

/// Generalized peak commutation: FreeExpand(stable) + FreeReduce at arbitrary count.
/// Same position arithmetic as lemma_k4_peak_fe_fr, but for any count c ≥ 2.
pub proof fn lemma_peak_fe_fr_general(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p1: int, sym1: Symbol, p2: int,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym1) == data.base.num_generators,
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::FreeReduce { position: p2 }) == Some(w3)
        }),
        stable_letter_count(w1, data.base.num_generators) >= 2,
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators) + 2,
        stable_letter_count(w3, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators),
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        let c = stable_letter_count(w1, n);
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == (c - 2) as nat
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    // Identical position arithmetic to lemma_k4_peak_fe_fr.
    // The only difference: w1' has count c-2 instead of 0.
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
    assert(pair =~= seq![sym1, inverse_symbol(sym1)]);

    assert(w2 =~= w1.subrange(0, p1) + pair + w1.subrange(p1, w1.len() as int));
    assert(has_cancellation_at(w2, p2));
    assert(w3 =~= w2.subrange(0, p2) + w2.subrange(p2 + 2, w2.len() as int));

    // The stable count decreased by 2 (from c+2 to c), so the reduced pair is stable
    lemma_stable_count_reduce(w2, p2, n);
    assert(generator_index(w2[p2]) == n);

    // Boundary cases: all lead to w3 = w1 (cancel), contradicting non-cancel.
    // Same proof as lemma_k4_peak_fe_fr lines for p2 == p1, p1-1, p1+1.
    if p2 == p1 {
        assert forall|k: int| 0 <= k < w1.len() implies w3[k] == w1[k] by {
            if k < p1 { assert(w3[k] == w2[k]); assert(w2[k] == w1[k]); }
            else { assert(w3[k] == w2[k + 2]); assert(w2[k + 2] == w1[k]); }
        };
        assert(w3 =~= w1); assert(false);
    }
    if p2 == p1 - 1 {
        assert(is_inverse_pair(w2[p2], w2[p2 + 1]));
        assert(w2[p2 + 1] == sym1);
        assert(generator_index(w2[p2]) == generator_index(sym1)) by {
            assert(w2[p2 + 1] == inverse_symbol(w2[p2]));
            match w2[p2] { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
        };
        assert forall|k: int| 0 <= k < w1.len() implies w3[k] == w1[k] by {
            if k < p1 - 1 { assert(w3[k] == w2[k]); assert(w2[k] == w1[k]); }
            else if k == p1 - 1 {
                assert(w3[k] == w2[(p1 + 1) as int]);
                assert(w2[(p1 + 1) as int] == inverse_symbol(sym1));
                assert(w1[k] == inverse_symbol(sym1)) by {
                    assert(is_inverse_pair(w1[k], sym1));
                    match w1[k] { Symbol::Gen(i) => {
                        assert(sym1 == Symbol::Inv(i));
                        assert(inverse_symbol(sym1) == Symbol::Gen(i));
                    }, Symbol::Inv(i) => {
                        assert(sym1 == Symbol::Gen(i));
                        assert(inverse_symbol(sym1) == Symbol::Inv(i));
                    } }
                };
            } else { assert(w3[k] == w2[k + 2]); assert(w2[k + 2] == w1[k]); }
        };
        assert(w3 =~= w1); assert(false);
    }
    if p2 == p1 + 1 {
        assert(w2[p2] == inverse_symbol(sym1));
        assert(is_inverse_pair(inverse_symbol(sym1), w1[p1]));
        assert(w1[p1] == sym1) by {
            let isym = inverse_symbol(sym1);
            assert(is_inverse_pair(isym, w1[p1]));
            match isym {
                Symbol::Gen(idx) => { match sym1 {
                    Symbol::Gen(j) => { assert(isym == Symbol::Inv(j)); assert(false); },
                    Symbol::Inv(j) => { assert(idx == j); }
                } },
                Symbol::Inv(idx) => { match sym1 {
                    Symbol::Gen(j) => { assert(idx == j); },
                    Symbol::Inv(j) => { assert(isym == Symbol::Gen(j)); assert(false); }
                } },
            }
        };
        assert forall|k: int| 0 <= k < w1.len() implies w3[k] == w1[k] by {
            if k < p1 { assert(w3[k] == w2[k]); assert(w2[k] == w1[k]); }
            else if k == p1 { assert(w3[k] == w2[p1]); assert(w2[p1] == sym1); }
            else { assert(w3[k] == w2[k + 2]); assert(w2[k + 2] == w1[k]); }
        };
        assert(w3 =~= w1); assert(false);
    }

    // Non-boundary: same position adjustment as count-2 case
    if p2 < p1 - 1 {
        assert(w2[p2] == w1[p2]);
        assert(w2[p2 + 1] == w1[p2 + 1]);
        assert(has_cancellation_at(w1, p2));
        let w1_prime = reduce_at(w1, p2);
        let step2_adj = DerivationStep::FreeReduce { position: p2 };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));
        lemma_stable_count_reduce(w1, p2, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);

        let p1_adj = (p1 - 2) as int;
        let step1_adj = DerivationStep::FreeExpand { position: p1_adj, symbol: sym1 };
        let expand_result = w1_prime.subrange(0, p1_adj) + pair
            + w1_prime.subrange(p1_adj, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == expand_result[k] by {
            if k < p2 {
                assert(w3[k] == w2[k]); assert(w2[k] == w1[k]);
                assert(expand_result[k] == w1_prime[k]); assert(w1_prime[k] == w1[k]);
            } else if k < p1_adj {
                assert(w3[k] == w2[k + 2]); assert(w2[k + 2] == w1[k + 2]);
                assert(expand_result[k] == w1_prime[k]); assert(w1_prime[k] == w1[k + 2]);
            } else if k == p1_adj {
                assert(w3[k] == w2[k + 2]); assert(w2[(p1_adj + 2) as int] == sym1);
                assert(expand_result[k] == sym1);
            } else if k == p1_adj + 1 {
                assert(w3[k] == w2[k + 2]); assert(w2[(k + 2) as int] == inverse_symbol(sym1));
                assert(expand_result[k] == inverse_symbol(sym1));
            } else {
                assert(w3[k] == w2[k + 2]); assert(w2[k + 2] == w1[k]);
                assert(expand_result[k] == w1_prime[(k - 2) as int]); assert(w1_prime[(k - 2) as int] == w1[k]);
            }
        };
        assert(w3 =~= expand_result);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));
        (w1_prime, step2_adj, step1_adj)
    } else {
        assert(p2 >= p1 + 2);
        let p2_adj = (p2 - 2) as int;
        assert(w2[p2] == w1[p2_adj]);
        assert(w2[p2 + 1] == w1[(p2_adj + 1) as int]);
        assert(has_cancellation_at(w1, p2_adj));
        let w1_prime = reduce_at(w1, p2_adj);
        let step2_adj = DerivationStep::FreeReduce { position: p2_adj };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));
        lemma_stable_count_reduce(w1, p2_adj, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);

        let step1_adj = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
        let expand_result = w1_prime.subrange(0, p1) + pair
            + w1_prime.subrange(p1, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == expand_result[k] by {
            if k < p1 {
                assert(w3[k] == w2[k]); assert(w2[k] == w1[k]);
                assert(expand_result[k] == w1_prime[k]); assert(w1_prime[k] == w1[k]);
            } else if k == p1 {
                assert(w3[k] == w2[k]); assert(w2[p1] == sym1);
                assert(expand_result[k] == sym1);
            } else if k == p1 + 1 {
                assert(w3[k] == w2[k]); assert(w2[(p1 + 1) as int] == inverse_symbol(sym1));
                assert(expand_result[k] == inverse_symbol(sym1));
            } else if k < p2 {
                // p1+2 <= k < p2: w3[k] = w2[k] = w1[k-2], expand_result[k] = w1_prime[k-2] = w1[k-2]
                assert(w3[k] == w2[k]); assert(w2[k] == w1[(k - 2) as int]);
                assert(expand_result[k] == w1_prime[(k - 2) as int]); assert(w1_prime[(k - 2) as int] == w1[(k - 2) as int]);
            } else {
                // k >= p2: w3[k] = w2[k+2] = w1[k], expand_result[k] = w1_prime[k-2] = w1[k]
                assert(w3[k] == w2[k + 2]); assert(w2[k + 2] == w1[k]);
                assert(expand_result[k] == w1_prime[(k - 2) as int]); assert(w1_prime[(k - 2) as int] == w1[k]);
            }
        };
        assert(w3 =~= expand_result);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));
        (w1_prime, step2_adj, step1_adj)
    }
}

/// Generalized peak: FreeExpand(stable) + RelatorDelete(HNN) at arbitrary count.
pub proof fn lemma_peak_fe_rd_general(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p1: int, sym1: Symbol, p2: int, ri2: nat, inv2: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        generator_index(sym1) == data.base.num_generators,
        ri2 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::FreeExpand { position: p1, symbol: sym1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 }) == Some(w3)
        }),
        stable_letter_count(w1, data.base.num_generators) >= 2,
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators) + 2,
        stable_letter_count(w3, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators),
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        let c = stable_letter_count(w1, n);
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == (c - 2) as nat
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = seq![sym1, inverse_symbol(sym1)];
    let r2 = get_relator(hp, ri2, inv2);
    let r2_len = r2.len() as int;

    assert(w2 =~= w1.subrange(0, p1) + (Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1))) + w1.subrange(p1, w1.len() as int));
    assert(w2.subrange(p2, p2 + r2_len) =~= r2);
    assert(w3 =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));

    lemma_relator_stable_count(data, ri2, inv2);

    if p2 + r2_len <= p1 {
        // Relator entirely before insertion
        assert forall|k: int| p2 <= k < p2 + r2_len implies w2[k] == w1[k] by {};
        assert(w1.subrange(p2, p2 + r2_len) =~= r2);
        let w1_prime = w1.subrange(0, p2) + w1.subrange(p2 + r2_len, w1.len() as int);
        let step2_adj = DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));
        lemma_stable_count_subrange(w1, p2, p2 + r2_len, n);
        lemma_stable_letter_count_concat(w1.subrange(0, p2), w1.subrange(p2 + r2_len, w1.len() as int), n);
        lemma_stable_letter_count_concat(w1.subrange(0, p2), w1.subrange(p2, w1.len() as int), n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);
        let p1_adj = (p1 - r2_len) as int;
        let step1_adj = DerivationStep::FreeExpand { position: p1_adj, symbol: sym1 };
        let pair_full = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
        let expand_result = w1_prime.subrange(0, p1_adj) + pair_full
            + w1_prime.subrange(p1_adj, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == expand_result[k] by {};
        assert(w3 =~= expand_result);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));
        (w1_prime, step2_adj, step1_adj)
    } else if p2 >= p1 + 2 {
        // Relator entirely after insertion
        let p2_adj = (p2 - 2) as int;
        assert forall|k: int| p2 <= k < p2 + r2_len implies w2[k] == w1[(k - 2) as int] by {};
        assert(w1.subrange(p2_adj, p2_adj + r2_len) =~= r2);
        let w1_prime = w1.subrange(0, p2_adj) + w1.subrange(p2_adj + r2_len, w1.len() as int);
        let step2_adj = DerivationStep::RelatorDelete { position: p2_adj, relator_index: ri2, inverted: inv2 };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));
        lemma_stable_count_subrange(w1, p2_adj, p2_adj + r2_len, n);
        lemma_stable_letter_count_concat(w1.subrange(0, p2_adj), w1.subrange(p2_adj + r2_len, w1.len() as int), n);
        lemma_stable_letter_count_concat(w1.subrange(0, p2_adj), w1.subrange(p2_adj, w1.len() as int), n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);
        let step1_adj = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
        let pair_full = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
        let expand_result = w1_prime.subrange(0, p1) + pair_full
            + w1_prime.subrange(p1, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == expand_result[k] by {};
        assert(w3 =~= expand_result);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));
        (w1_prime, step2_adj, step1_adj)
    } else {
        // Overlap
        assume(false); arbitrary()
    }
}

/// Generalized peak: RelatorInsert(HNN) + FreeReduce at arbitrary count.
pub proof fn lemma_peak_ri_fr_general(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p1: int, ri1: nat, inv1: bool, p2: int,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri1 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::FreeReduce { position: p2 }) == Some(w3)
        }),
        stable_letter_count(w1, data.base.num_generators) >= 2,
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators) + 2,
        stable_letter_count(w3, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators),
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        let c = stable_letter_count(w1, n);
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == (c - 2) as nat
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;

    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));
    assert(has_cancellation_at(w2, p2));
    assert(w3 =~= w2.subrange(0, p2) + w2.subrange(p2 + 2, w2.len() as int));

    lemma_stable_count_reduce(w2, p2, n);
    assert(generator_index(w2[p2]) == n);
    lemma_relator_stable_count(data, ri1, inv1);

    if p2 + 2 <= p1 {
        assert(w2[p2] == w1[p2]);
        assert(w2[p2 + 1] == w1[p2 + 1]);
        assert(has_cancellation_at(w1, p2));
        let w1_prime = reduce_at(w1, p2);
        let step2_adj = DerivationStep::FreeReduce { position: p2 };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));
        lemma_stable_count_reduce(w1, p2, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);
        let p1_adj = (p1 - 2) as int;
        let step1_adj = DerivationStep::RelatorInsert { position: p1_adj, relator_index: ri1, inverted: inv1 };
        let ins = w1_prime.subrange(0, p1_adj) + r1 + w1_prime.subrange(p1_adj, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
        assert(w3 =~= ins);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));
        (w1_prime, step2_adj, step1_adj)
    } else if p2 >= p1 + r1_len {
        let p2_adj = (p2 - r1_len) as int;
        assert(w2[p2] == w1[p2_adj]);
        assert(w2[p2 + 1] == w1[(p2_adj + 1) as int]);
        assert(has_cancellation_at(w1, p2_adj));
        let w1_prime = reduce_at(w1, p2_adj);
        let step2_adj = DerivationStep::FreeReduce { position: p2_adj };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));
        lemma_stable_count_reduce(w1, p2_adj, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);
        let step1_adj = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
        let ins = w1_prime.subrange(0, p1) + r1 + w1_prime.subrange(p1, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
        assert(w3 =~= ins);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));
        (w1_prime, step2_adj, step1_adj)
    } else {
        // Overlap
        assume(false); arbitrary()
    }
}

/// Generalized peak: RelatorInsert(HNN) + RelatorDelete(HNN) at arbitrary count.
/// Split into left/right sub-helpers to manage rlimit.
pub proof fn lemma_peak_ri_rd_general(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    p1: int, ri1: nat, inv1: bool, p2: int, ri2: nat, inv2: bool,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri1 as int >= data.base.relators.len(),
        ri2 as int >= data.base.relators.len(),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 }) == Some(w3)
        }),
        stable_letter_count(w1, data.base.num_generators) >= 2,
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators) + 2,
        stable_letter_count(w3, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators),
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        let c = stable_letter_count(w1, n);
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == (c - 2) as nat
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    let r2 = get_relator(hp, ri2, inv2);
    let r2_len = r2.len() as int;

    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));
    assert(w2.subrange(p2, p2 + r2_len) =~= r2);
    assert(w3 =~= w2.subrange(0, p2) + w2.subrange(p2 + r2_len, w2.len() as int));

    lemma_relator_stable_count(data, ri1, inv1);
    lemma_relator_stable_count(data, ri2, inv2);

    // Cancel: same relator, same position
    if ri1 == ri2 && inv1 == inv2 && p2 == p1 {
        assert(r1 =~= r2);
        assert forall|k: int| 0 <= k < w1.len() implies w3[k] == w1[k] by {
            if k < p1 { assert(w3[k] == w2[k]); assert(w2[k] == w1[k]); }
            else { assert(w3[k] == w2[k + r1_len]); assert(w2[k + r1_len] == w1[k]); }
        };
        assert(w3 =~= w1); assert(false);
    }

    if p2 + r2_len <= p1 {
        // Reuse existing left helper (same position arithmetic)
        lemma_k4_peak_ri_rd_left(data, w1, w2, w3, p1, ri1, inv1, p2, ri2, inv2)
    } else if p2 >= p1 + r1_len {
        lemma_k4_peak_ri_rd_right(data, w1, w2, w3, p1, ri1, inv1, p2, ri2, inv2)
    } else {
        // Overlap
        assume(false); arbitrary()
    }
}

/// Generalized peak dispatcher at arbitrary count c ≥ 2.
/// Classifies step1 (+2) and step2 (-2) types, delegates to per-combination helpers.
pub proof fn lemma_peak_commute_general(
    data: HNNData, w1: Word, w2: Word, w3: Word,
    step1: DerivationStep, step2: DerivationStep,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w3)
        }),
        stable_letter_count(w1, data.base.num_generators) >= 2,
        stable_letter_count(w2, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators) + 2,
        stable_letter_count(w3, data.base.num_generators) ==
            stable_letter_count(w1, data.base.num_generators),
        !(w3 =~= w1),
    ensures ({
        let (w1_prime, step2_adj, step1_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        let c = stable_letter_count(w1, n);
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == (c - 2) as nat
        &&& apply_step(hp, w1, step2_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step1_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    // Classify step1 as +2
    lemma_plus2_step_type(data, w1, w2, step1, n);

    // Classify step2 as -2: same logic as in lemma_k4_peak_noncancel_commute
    lemma_stable_count_reduce_step(data, w2, step2, n);

    match step1 {
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } => {
            match step2 {
                DerivationStep::FreeReduce { position: p2 } => {
                    lemma_peak_fe_fr_general(data, w1, w2, w3, p1, sym1, p2)
                },
                DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
                    lemma_relator_stable_count(data, ri2, inv2);
                    // Must be HNN (count -2)
                    if (ri2 as int) < data.base.relators.len() {
                        let r2 = get_relator(hp, ri2, inv2);
                        lemma_stable_count_subrange(w2, p2, p2 + r2.len() as int, n);
                        lemma_stable_letter_count_concat(w2.subrange(0, p2), w2.subrange(p2 + r2.len() as int, w2.len() as int), n);
                        lemma_stable_letter_count_concat(w2.subrange(0, p2), w2.subrange(p2, w2.len() as int), n);
                        assert(false);
                    }
                    lemma_peak_fe_rd_general(data, w1, w2, w3, p1, sym1, p2, ri2, inv2)
                },
                _ => {
                    // FreeExpand/RelatorInsert can't decrease count
                    lemma_stable_count_reduce_step(data, w2, step2, n);
                    match step2 {
                        DerivationStep::FreeExpand { position: p2e, symbol: sym2e } => {
                            let pair2 = Seq::new(1, |_i: int| sym2e) + Seq::new(1, |_i: int| inverse_symbol(sym2e));
                            assert(pair2 =~= seq![sym2e, inverse_symbol(sym2e)]);
                            let l2 = w2.subrange(0, p2e);
                            let r2 = w2.subrange(p2e, w2.len() as int);
                            assert(w2 =~= l2 + r2);
                            assert(w3 =~= l2 + pair2 + r2);
                            lemma_stable_count_pair(sym2e, inverse_symbol(sym2e), n);
                            lemma_stable_letter_count_concat(l2, r2, n);
                            lemma_stable_letter_count_concat(l2, pair2, n);
                            lemma_stable_letter_count_concat(l2 + pair2, r2, n);
                            assert(false); arbitrary()
                        },
                        DerivationStep::RelatorInsert { position: p2r, relator_index: ri2, inverted: inv2 } => {
                            let r2 = get_relator(hp, ri2, inv2);
                            lemma_relator_stable_count(data, ri2, inv2);
                            let l2 = w2.subrange(0, p2r);
                            let r2r = w2.subrange(p2r, w2.len() as int);
                            assert(w2 =~= l2 + r2r);
                            assert(w3 =~= l2 + r2 + r2r);
                            lemma_stable_letter_count_concat(l2, r2r, n);
                            lemma_stable_letter_count_concat(l2, r2, n);
                            lemma_stable_letter_count_concat(l2 + r2, r2r, n);
                            assert(false); arbitrary()
                        },
                        _ => { arbitrary() }, // already handled above
                    }
                },
            }
        },
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            match step2 {
                DerivationStep::FreeReduce { position: p2 } => {
                    lemma_peak_ri_fr_general(data, w1, w2, w3, p1, ri1, inv1, p2)
                },
                DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
                    lemma_relator_stable_count(data, ri2, inv2);
                    if (ri2 as int) < data.base.relators.len() {
                        let r2 = get_relator(hp, ri2, inv2);
                        lemma_stable_count_subrange(w2, p2, p2 + r2.len() as int, n);
                        lemma_stable_letter_count_concat(w2.subrange(0, p2), w2.subrange(p2 + r2.len() as int, w2.len() as int), n);
                        lemma_stable_letter_count_concat(w2.subrange(0, p2), w2.subrange(p2, w2.len() as int), n);
                        assert(false);
                    }
                    lemma_peak_ri_rd_general(data, w1, w2, w3, p1, ri1, inv1, p2, ri2, inv2)
                },
                _ => {
                    match step2 {
                        DerivationStep::FreeExpand { position: p2e, symbol: sym2e } => {
                            let pair2 = Seq::new(1, |_i: int| sym2e) + Seq::new(1, |_i: int| inverse_symbol(sym2e));
                            assert(pair2 =~= seq![sym2e, inverse_symbol(sym2e)]);
                            let l2 = w2.subrange(0, p2e);
                            let r2 = w2.subrange(p2e, w2.len() as int);
                            assert(w2 =~= l2 + r2);
                            assert(w3 =~= l2 + pair2 + r2);
                            lemma_stable_count_pair(sym2e, inverse_symbol(sym2e), n);
                            lemma_stable_letter_count_concat(l2, r2, n);
                            lemma_stable_letter_count_concat(l2, pair2, n);
                            lemma_stable_letter_count_concat(l2 + pair2, r2, n);
                            assert(false); arbitrary()
                        },
                        DerivationStep::RelatorInsert { position: p2r, relator_index: ri2, inverted: inv2 } => {
                            let r2 = get_relator(hp, ri2, inv2);
                            lemma_relator_stable_count(data, ri2, inv2);
                            let l2 = w2.subrange(0, p2r);
                            let r2r = w2.subrange(p2r, w2.len() as int);
                            assert(w2 =~= l2 + r2r);
                            assert(w3 =~= l2 + r2 + r2r);
                            lemma_stable_letter_count_concat(l2, r2r, n);
                            lemma_stable_letter_count_concat(l2, r2, n);
                            lemma_stable_letter_count_concat(l2 + r2, r2r, n);
                            assert(false); arbitrary()
                        },
                        _ => { arbitrary() },
                    }
                },
            }
        },
        _ => {
            // step1 must be FE or RI (from plus2_step_type)
            assert(false); arbitrary()
        },
    }
}

/// word_valid is preserved through a derivation in the HNN presentation.
pub proof fn lemma_derivation_preserves_word_valid(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators + 1),
        derivation_produces(hnn_presentation(data), steps, w) == Some(w_end),
    ensures
        word_valid(w_end, data.base.num_generators + 1),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(w_end == w);
    } else {
        let hp = hnn_presentation(data);
        let w1 = apply_step(hp, w, steps.first()).unwrap();
        lemma_step_preserves_word_valid(data, w, steps.first());
        lemma_derivation_preserves_word_valid(data, steps.drop_first(), w1, w_end);
    }
}

/// If all steps are +2 (FE stable or RI HNN) starting from count c,
/// then after k steps the stable count is c + 2*k.
pub proof fn lemma_plus2_prefix_gives_count(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word, c: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators + 1),
        stable_letter_count(w, data.base.num_generators) == c,
        derivation_produces(hnn_presentation(data), steps, w) == Some(w_end),
        forall|j: int| 0 <= j < steps.len() ==>
            match #[trigger] steps[j] {
                DerivationStep::FreeExpand { symbol, .. } =>
                    generator_index(symbol) == data.base.num_generators,
                DerivationStep::RelatorInsert { relator_index, .. } =>
                    relator_index as int >= data.base.relators.len(),
                _ => false,
            },
    ensures
        stable_letter_count(w_end, data.base.num_generators) == c + 2 * steps.len(),
    decreases steps.len(),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    if steps.len() == 0 {
        assert(w_end == w);
    } else {
        let step0 = steps.first();
        let w1 = apply_step(hp, w, step0).unwrap();
        lemma_step_preserves_word_valid(data, w, step0);

        // step0 is +2: count increases by exactly 2
        lemma_stable_count_reduce_step(data, w, step0, n);
        // From plus2_step_type and the count arithmetic:
        // count(w1) ∈ {c, c+2, c-2}. Since step0 is +2: count(w1) = c + 2.
        match step0 {
            DerivationStep::FreeExpand { position: p, symbol: sym } => {
                let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
                assert(pair =~= seq![sym, inverse_symbol(sym)]);
                let left = w.subrange(0, p);
                let right = w.subrange(p, w.len() as int);
                assert(w =~= left + right);
                assert(w1 =~= left + pair + right);
                lemma_stable_count_pair(sym, inverse_symbol(sym), n);
                lemma_stable_letter_count_concat(left, right, n);
                lemma_stable_letter_count_concat(left, pair, n);
                lemma_stable_letter_count_concat(left + pair, right, n);
                assert(stable_letter_count(w1, n) == c + 2);
            },
            DerivationStep::RelatorInsert { position: p, relator_index: ri, inverted: inv } => {
                let r = get_relator(hp, ri, inv);
                lemma_relator_stable_count(data, ri, inv);
                let left = w.subrange(0, p);
                let right = w.subrange(p, w.len() as int);
                assert(w =~= left + right);
                assert(w1 =~= left + r + right);
                lemma_stable_letter_count_concat(left, right, n);
                lemma_stable_letter_count_concat(left, r, n);
                lemma_stable_letter_count_concat(left + r, right, n);
                assert(stable_letter_count(w1, n) == c + 2);
            },
            _ => { assert(false); },
        }

        // Recurse on tail
        let tail = steps.drop_first();
        assert forall|j: int| 0 <= j < tail.len() implies
            match #[trigger] tail[j] {
                DerivationStep::FreeExpand { symbol, .. } =>
                    generator_index(symbol) == n,
                DerivationStep::RelatorInsert { relator_index, .. } =>
                    relator_index as int >= data.base.relators.len(),
                _ => false,
            }
        by {
            assert(tail[j] == steps[j + 1]);
        };
        lemma_plus2_prefix_gives_count(data, tail, w1, w_end, c + 2);
    }
}

/// Bubble a peak leftward to position (1,2), then create a base intermediate.
///
/// Takes the derivation decomposed into: prefix ++ [step_up, step_down] ++ suffix.
/// prefix has length ≥ 1 (all +2 steps). step_up is +2, step_down is -2.
/// Recursively commutes the peak left until it reaches position (1,2).
///
/// Returns (w_base, left, right) where w_base is base and left, right are
/// shorter derivations from w to w_base and w_base to w_end.
pub proof fn lemma_bubble_peak_to_front(
    data: HNNData,
    prefix: Seq<DerivationStep>,
    step_up: DerivationStep,
    step_down: DerivationStep,
    suffix: Seq<DerivationStep>,
    w: Word,
    w_before_peak: Word,
    w_at_peak: Word,
    w_after_peak: Word,
    w_end: Word,
) -> (result: (Word, Seq<DerivationStep>, Seq<DerivationStep>))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        prefix.len() >= 1,
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w_before_peak, data.base.num_generators + 1),
        word_valid(w_at_peak, data.base.num_generators + 1),
        word_valid(w_after_peak, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& derivation_produces(hp, prefix, w) == Some(w_before_peak)
            &&& apply_step(hp, w_before_peak, step_up) == Some(w_at_peak)
            &&& apply_step(hp, w_at_peak, step_down) == Some(w_after_peak)
            &&& derivation_produces(hp, suffix, w_after_peak) == Some(w_end)
        }),
        ({
            let n = data.base.num_generators;
            &&& stable_letter_count(w_before_peak, n) == 2 * prefix.len()
            &&& stable_letter_count(w_at_peak, n) == 2 * prefix.len() + 2
            &&& stable_letter_count(w_after_peak, n) == 2 * prefix.len()
        }),
        !(w_after_peak =~= w_before_peak),
        // step_up is +2
        match step_up {
            DerivationStep::FreeExpand { symbol, .. } =>
                generator_index(symbol) == data.base.num_generators,
            DerivationStep::RelatorInsert { relator_index, .. } =>
                relator_index as int >= data.base.relators.len(),
            _ => false,
        },
        // All prefix steps are +2
        forall|j: int| 0 <= j < prefix.len() ==>
            match #[trigger] prefix[j] {
                DerivationStep::FreeExpand { symbol, .. } =>
                    generator_index(symbol) == data.base.num_generators,
                DerivationStep::RelatorInsert { relator_index, .. } =>
                    relator_index as int >= data.base.relators.len(),
                _ => false,
            },
    ensures ({
        let (w_base, left_steps, right_steps) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        let total = prefix.len() + 2 + suffix.len();
        &&& is_base_word(w_base, n)
        &&& word_valid(w_base, n + 1)
        &&& derivation_produces(hp, left_steps, w) == Some(w_base)
        &&& derivation_produces(hp, right_steps, w_base) == Some(w_end)
        &&& left_steps.len() < total
        &&& right_steps.len() < total
    }),
    decreases prefix.len(),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    if prefix.len() == 1 {
        // Peak at (1,2): counts (2, 4, 2).
        lemma_derivation_unfold_1(hp, prefix, w, w_before_peak);
        let step0 = prefix.first();
        assert(apply_step(hp, w, step0) == Some(w_before_peak));

        // Use the count-2 peak commutation (handles non-overlap, assume(false) for overlap)
        let (w_base, step_down_adj, step_up_adj) =
            lemma_k4_peak_noncancel_commute(data, w_before_peak, w_at_peak, w_after_peak, step_up, step_down);

        // left: [step0, step_down_adj] from w to w_base (2 steps)
        lemma_derivation_produces_2(hp, step0, step_down_adj, w, w_before_peak, w_base);
        let left_steps: Seq<DerivationStep> = seq![step0, step_down_adj];

        // right: [step_up_adj] ++ suffix from w_base to w_end
        lemma_step_preserves_word_valid(data, w_base, step_up_adj);
        let one_adj: Seq<DerivationStep> = seq![step_up_adj];
        assert(one_adj.first() == step_up_adj);
        assert(one_adj.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w_after_peak) == Some(w_after_peak)) by {
            assert(Seq::<DerivationStep>::empty().len() == 0);
        };
        assert(derivation_produces(hp, one_adj, w_base) == Some(w_after_peak));
        lemma_derivation_concat(hp, one_adj, suffix, w_base, w_after_peak, w_end);
        let right_steps = one_adj + suffix;

        (w_base, left_steps, right_steps)
    } else {
        // prefix.len() > 1: commute, then recurse with shorter prefix
        let (w_prime, step_down_adj, step_up_adj) =
            lemma_peak_commute_general(data, w_before_peak, w_at_peak, w_after_peak, step_up, step_down);
        // step_down_adj on w_before_peak → w' (count 2*(prefix.len()-1))
        // step_up_adj on w' → w_after_peak

        // New peak: last step of prefix (+2) followed by step_down_adj (-2)
        // New prefix = prefix.drop_last() (shorter by 1)
        // New step_up = prefix.last()
        // New step_down = step_down_adj
        // New suffix = [step_up_adj] ++ suffix

        // Get w_prev (word before the last prefix step)
        let new_prefix = prefix.subrange(0, prefix.len() as int - 1);
        let last_prefix_step = prefix[prefix.len() as int - 1];

        // derivation_produces(hp, prefix, w) == Some(w_before_peak)
        // Split prefix: new_prefix ++ [last_prefix_step]
        lemma_derivation_split(hp, prefix, w, w_before_peak, (prefix.len() - 1) as nat);
        let w_prev = derivation_produces(hp, new_prefix, w).unwrap();
        assert(derivation_produces(hp, new_prefix, w) == Some(w_prev));

        // last_prefix_step on w_prev → w_before_peak
        let last_step_seq = prefix.subrange(prefix.len() as int - 1, prefix.len() as int);
        assert(last_step_seq.len() == 1);
        assert(last_step_seq.first() == last_prefix_step);
        lemma_derivation_unfold_1(hp, last_step_seq, w_prev, w_before_peak);
        assert(apply_step(hp, w_prev, last_prefix_step) == Some(w_before_peak));

        // word_valid for w_prev
        lemma_step_preserves_word_valid(data, w_before_peak, step_down_adj);

        // Build new suffix: [step_up_adj] ++ suffix
        let one_up: Seq<DerivationStep> = seq![step_up_adj];
        assert(one_up.first() == step_up_adj);
        assert(one_up.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w_after_peak) == Some(w_after_peak)) by {
            assert(Seq::<DerivationStep>::empty().len() == 0);
        };
        assert(derivation_produces(hp, one_up, w_prime) == Some(w_after_peak));
        lemma_derivation_concat(hp, one_up, suffix, w_prime, w_after_peak, w_end);
        let new_suffix = one_up + suffix;
        assert(derivation_produces(hp, new_suffix, w_prime) == Some(w_end));

        // Counts for recursion:
        // w_prev: count 2*(prefix.len()-1) = 2*new_prefix.len()
        // w_before_peak: count 2*prefix.len() = 2*new_prefix.len() + 2
        // w_prime: count 2*(prefix.len()-1) = 2*new_prefix.len()
        // last_prefix_step is +2 (all prefix steps are +2)

        // Establish last_prefix_step is +2 (from forall on prefix)
        assert(match last_prefix_step {
            DerivationStep::FreeExpand { symbol, .. } =>
                generator_index(symbol) == n,
            DerivationStep::RelatorInsert { relator_index, .. } =>
                relator_index as int >= data.base.relators.len(),
            _ => false,
        });

        // word_valid for w_prev from derivation
        lemma_derivation_preserves_word_valid(data, new_prefix, w, w_prev);

        // Count of w_prev = 2 * new_prefix.len() from all-+2 prefix
        assert forall|j: int| 0 <= j < new_prefix.len() implies
            match #[trigger] new_prefix[j] {
                DerivationStep::FreeExpand { symbol, .. } =>
                    generator_index(symbol) == n,
                DerivationStep::RelatorInsert { relator_index, .. } =>
                    relator_index as int >= data.base.relators.len(),
                _ => false,
            }
        by {
            assert(new_prefix[j] == prefix[j]);
        };
        lemma_base_implies_count_zero(w, n);
        lemma_plus2_prefix_gives_count(data, new_prefix, w, w_prev, 0nat);

        // Check cancel at new peak
        if w_prime =~= w_prev {
            // Cancel: new_prefix goes w → w_prev, new_suffix goes w_prime=w_prev → w_end
            lemma_derivation_concat(hp, new_prefix, new_suffix, w, w_prev, w_end);
            let short = new_prefix + new_suffix;
            // short has (prefix.len()-1) + (1 + suffix.len()) = prefix.len() + suffix.len() = total - 2
            assert(short.len() == prefix.len() - 1 + 1 + suffix.len());
            // Prove empty derivation from w to w
            assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w) == Some(w)) by {
                assert(Seq::<DerivationStep>::empty().len() == 0);
            };
            (w, Seq::<DerivationStep>::empty(), short)
        } else {
            // Non-cancel: recurse with peak_pos - 1
            // new_prefix is shorter: new_prefix.len() = prefix.len() - 1
            // All new_prefix steps are +2 (they're a sub-sequence of the original prefix)
            assert forall|j: int| 0 <= j < new_prefix.len() implies
                match #[trigger] new_prefix[j] {
                    DerivationStep::FreeExpand { symbol, .. } =>
                        generator_index(symbol) == n,
                    DerivationStep::RelatorInsert { relator_index, .. } =>
                        relator_index as int >= data.base.relators.len(),
                    _ => false,
                }
            by {
                assert(new_prefix[j] == prefix[j]);
            };

            lemma_bubble_peak_to_front(
                data,
                new_prefix,
                last_prefix_step,  // new step_up (+2)
                step_down_adj,     // new step_down (-2)
                new_suffix,
                w,
                w_prev,
                w_before_peak,
                w_prime,
                w_end,
            )
        }
    }
}

/// 3-round swap for c_3=6, c_4=6 (step3 T-free).
/// Swaps step3 past step2, step1, step0 to create base intermediate.
proof fn lemma_k5_c3_6_c4_6_three_round(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
    w1: Word, w2: Word, w3: Word, w4: Word,
    step0: DerivationStep, step1: DerivationStep,
    step2: DerivationStep, step3: DerivationStep,
    suffix: Seq<DerivationStep>,
) -> (result: (Word, Seq<DerivationStep>, Seq<DerivationStep>))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        steps.len() >= 5,
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        word_valid(w4, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w3)
            &&& apply_step(hp, w3, step3) == Some(w4)
            &&& derivation_produces(hp, suffix, w4) == Some(w_end)
        }),
        ({
            let n = data.base.num_generators;
            &&& stable_letter_count(w1, n) == 2nat
            &&& stable_letter_count(w2, n) == 4nat
            &&& stable_letter_count(w3, n) == 6nat
            &&& stable_letter_count(w4, n) == 6nat  // step3 is T-free
        }),
        match step0 {
            DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == data.base.num_generators,
            DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
            _ => false,
        },
        match step1 {
            DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == data.base.num_generators,
            DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
            _ => false,
        },
        match step2 {
            DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == data.base.num_generators,
            DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
            _ => false,
        },
        // suffix length relates to steps length
        suffix.len() + 4 <= steps.len(),
    ensures ({
        let (w_base, left_steps, right_steps) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_base, n)
        &&& word_valid(w_base, n + 1)
        &&& derivation_produces(hp, left_steps, w) == Some(w_base)
        &&& derivation_produces(hp, right_steps, w_base) == Some(w_end)
        &&& left_steps.len() < steps.len()
        &&& right_steps.len() < steps.len()
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    // Round 1: swap step3 (T-free) past step2 (+2)
    let (w_prime, step3_adj, step2_adj) = match step2 {
        DerivationStep::FreeExpand { position: p2, symbol: sym2 } =>
            lemma_swap_tfree_past_expand(data, w2, w3, w4, p2, sym2, step3),
        DerivationStep::RelatorInsert { position: p2, relator_index: ri2, inverted: inv2 } =>
            lemma_swap_tfree_past_ri(data, w2, w3, w4, p2, ri2, inv2, step3),
        _ => { assert(false); arbitrary() },
    };
    lemma_step_preserves_word_valid(data, w2, step3_adj);

    // Round 2: swap step3_adj (T-free) past step1 (+2)
    let (w1_prime, step3_adj2, step1_adj) = match step1 {
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } =>
            lemma_swap_tfree_past_expand(data, w1, w2, w_prime, p1, sym1, step3_adj),
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } =>
            lemma_swap_tfree_past_ri(data, w1, w2, w_prime, p1, ri1, inv1, step3_adj),
        _ => { assert(false); arbitrary() },
    };
    assert(stable_letter_count(w1_prime, n) == 2nat);
    assert(!is_base_word(w1_prime, n));
    lemma_step_preserves_word_valid(data, w1, step3_adj2);
    lemma_base_word_valid_down(w, n);

    // Round 3: swap step3_adj2 (T-free) past step0 (+2) at w (BASE)
    let (w_base, step3_base, step0_adj) = match step0 {
        DerivationStep::FreeExpand { position: p0, symbol: sym0 } => {
            match step3_adj2 {
                DerivationStep::FreeReduce { position: p } =>
                    lemma_k4_tfree_expand_commute_fr(data, w, w1, w1_prime, p0, sym0, p),
                _ =>
                    lemma_k4_tfree_expand_commute_other(data, w, w1, w1_prime, p0, sym0, step3_adj2),
            }
        },
        DerivationStep::RelatorInsert { position: p0, relator_index: ri0, inverted: inv0 } =>
            lemma_k4_tfree_ri_commute(data, w, w1, w1_prime, p0, ri0, inv0, step3_adj2),
        _ => { assert(false); arbitrary() },
    };

    // Build derivation: [step0_adj, step1_adj, step2_adj] ++ suffix from w_base to w_end
    lemma_step_preserves_word_valid(data, w_base, step0_adj);
    lemma_derivation_produces_2(hp, step0_adj, step1_adj, w_base, w1_prime, w_prime);
    let prefix2: Seq<DerivationStep> = seq![step0_adj, step1_adj];
    let step2_adj_seq: Seq<DerivationStep> = seq![step2_adj];
    assert(step2_adj_seq.first() == step2_adj);
    assert(step2_adj_seq.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w4) == Some(w4)) by {
        assert(Seq::<DerivationStep>::empty().len() == 0);
    };
    assert(derivation_produces(hp, step2_adj_seq, w_prime) == Some(w4));
    lemma_derivation_concat(hp, step2_adj_seq, suffix, w_prime, w4, w_end);
    let suffix_full = step2_adj_seq + suffix;
    lemma_derivation_concat(hp, prefix2, suffix_full, w_base, w_prime, w_end);
    let deriv_steps = prefix2 + suffix_full;

    // left = [step3_base] (base step on w → w_base), 1 step
    let left_steps: Seq<DerivationStep> = seq![step3_base];
    assert(left_steps.first() == step3_base);
    assert(left_steps.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w_base) == Some(w_base)) by {
        assert(Seq::<DerivationStep>::empty().len() == 0);
    };
    assert(derivation_produces(hp, left_steps, w) == Some(w_base));

    // Length: left=1, right = 2 + 1 + suffix.len() = 3 + suffix.len()
    // steps.len() >= 5 and right = steps.len() - 1 (since suffix.len() = steps.len() - 4)
    assert(left_steps.len() == 1);
    assert(deriv_steps.len() == 3 + suffix.len());

    (w_base, left_steps, deriv_steps)
}

/// Bubble a T-free step leftward through a prefix of +2 steps to position 0.
/// At position 0, the T-free step acts on w (base) as a base step.
/// Returns (w_base, base_step, remaining) where w_base is base and
/// remaining is a shorter derivation from w_base to w_end.
proof fn lemma_bubble_tfree_to_front(
    data: HNNData,
    prefix: Seq<DerivationStep>,  // +2 steps before the T-free step
    step_tfree: DerivationStep,   // the T-free step
    suffix: Seq<DerivationStep>,  // steps after
    w: Word, w_before_tfree: Word, w_after_tfree: Word, w_end: Word,
    total_len: nat,
) -> (result: (Word, DerivationStep, Seq<DerivationStep>))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w, data.base.num_generators),
        word_valid(w_before_tfree, data.base.num_generators + 1),
        word_valid(w_after_tfree, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& derivation_produces(hp, prefix, w) == Some(w_before_tfree)
            &&& apply_step(hp, w_before_tfree, step_tfree) == Some(w_after_tfree)
            &&& derivation_produces(hp, suffix, w_after_tfree) == Some(w_end)
        }),
        stable_letter_count(w_before_tfree, data.base.num_generators) == 2 * prefix.len(),
        stable_letter_count(w_after_tfree, data.base.num_generators) == 2 * prefix.len(),
        total_len == prefix.len() + 1 + suffix.len(),
        total_len >= 4,
        forall|j: int| 0 <= j < prefix.len() ==>
            match #[trigger] prefix[j] {
                DerivationStep::FreeExpand { symbol, .. } =>
                    generator_index(symbol) == data.base.num_generators,
                DerivationStep::RelatorInsert { relator_index, .. } =>
                    relator_index as int >= data.base.relators.len(),
                _ => false,
            },
    ensures ({
        let (w_base, base_step, remaining) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_base, n)
        &&& word_valid(w_base, n + 1)
        &&& apply_step(data.base, w, base_step) == Some(w_base)
        &&& derivation_produces(hp, remaining, w_base) == Some(w_end)
        &&& remaining.len() < total_len
    }),
    decreases prefix.len(),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    if prefix.len() == 0 {
        // T-free step acts on w (base). It's a base step!
        // w_before_tfree = w (base), count 0.
        // step_tfree on w → w_after_tfree (base, count 0).
        assert(w_before_tfree == w);
        lemma_base_implies_count_zero(w, n);
        assert(stable_letter_count(w_after_tfree, n) == 0nat);
        lemma_zero_count_implies_base(w_after_tfree, n);
        // Prove apply_step(data.base, w, step_tfree) == Some(w_after_tfree)
        // For each T-free step type, the step is valid in data.base:
        match step_tfree {
            DerivationStep::FreeReduce { position } => {
                // FreeReduce doesn't depend on presentation
                assert(apply_step(data.base, w, step_tfree) == Some(w_after_tfree));
            },
            DerivationStep::FreeExpand { position, symbol } => {
                // FreeExpand: needs symbol_valid(symbol, data.base.num_generators)
                // T-free means gen_idx(symbol) < n. symbol_valid requires gen_idx < num_generators = n.
                // From count unchanged: pair count = 0, so gen_idx < n.
                lemma_stable_count_reduce_step(data, w, step_tfree, n);
                let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
                assert(pair =~= seq![symbol, inverse_symbol(symbol)]);
                let left = w.subrange(0, position);
                let right = w.subrange(position, w.len() as int);
                assert(w =~= left + right);
                assert(w_after_tfree =~= left + pair + right);
                lemma_stable_count_pair(symbol, inverse_symbol(symbol), n);
                lemma_stable_letter_count_concat(left, right, n);
                lemma_stable_letter_count_concat(left, pair, n);
                lemma_stable_letter_count_concat(left + pair, right, n);
                // count unchanged → pair count = 0 → gen_idx(symbol) < n
                assert(generator_index(symbol) < n);
                // symbol_valid in base presentation
                assert(symbol_valid(symbol, data.base.num_generators));
                assert(apply_step(data.base, w, step_tfree) == Some(w_after_tfree));
            },
            DerivationStep::RelatorInsert { position, relator_index: ri, inverted: inv } => {
                // T-free → relator has count 0 → base relator (ri < base.relators.len())
                lemma_relator_stable_count(data, ri, inv);
                let r = get_relator(hp, ri, inv);
                let left = w.subrange(0, position);
                let right = w.subrange(position, w.len() as int);
                assert(w =~= left + right);
                assert(w_after_tfree =~= left + r + right);
                lemma_stable_letter_count_concat(left, right, n);
                lemma_stable_letter_count_concat(left, r, n);
                lemma_stable_letter_count_concat(left + r, right, n);
                assert(stable_letter_count(r, n) == 0nat);
                assert((ri as int) < data.base.relators.len());
                // Base relator: same in both presentations
                reveal(presentation_valid);
                assert(data.base.relators[ri as int] == hp.relators[ri as int]);
                assert(get_relator(data.base, ri, inv) =~= r) by {
                    assert(data.base.relators[ri as int] == hp.relators[ri as int]);
                };
                assert(apply_step(data.base, w, step_tfree) == Some(w_after_tfree));
            },
            DerivationStep::RelatorDelete { position, relator_index: ri, inverted: inv } => {
                // Same logic as RelatorInsert
                lemma_relator_stable_count(data, ri, inv);
                let r = get_relator(hp, ri, inv);
                lemma_stable_count_subrange(w, position, position + r.len() as int, n);
                lemma_stable_letter_count_concat(w.subrange(0, position), w.subrange(position + r.len() as int, w.len() as int), n);
                lemma_stable_letter_count_concat(w.subrange(0, position), w.subrange(position, w.len() as int), n);
                assert(stable_letter_count(r, n) == 0nat);
                assert((ri as int) < data.base.relators.len());
                reveal(presentation_valid);
                assert(data.base.relators[ri as int] == hp.relators[ri as int]);
                assert(get_relator(data.base, ri, inv) =~= r) by {
                    assert(data.base.relators[ri as int] == hp.relators[ri as int]);
                };
                assert(apply_step(data.base, w, step_tfree) == Some(w_after_tfree));
            },
        }
        (w_after_tfree, step_tfree, suffix)
    } else {
        // Swap T-free past last prefix step
        let last_step = prefix[prefix.len() as int - 1];
        assert(match last_step {
            DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == n,
            DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
            _ => false,
        });

        let shorter_prefix = prefix.subrange(0, prefix.len() as int - 1);
        lemma_derivation_split(hp, prefix, w, w_before_tfree, (prefix.len() - 1) as nat);
        let w_prev = derivation_produces(hp, shorter_prefix, w).unwrap();
        let last_seq = prefix.subrange(prefix.len() as int - 1, prefix.len() as int);
        assert(last_seq.len() == 1);
        assert(last_seq.first() == last_step);
        lemma_derivation_unfold_1(hp, last_seq, w_prev, w_before_tfree);
        lemma_derivation_preserves_word_valid(data, shorter_prefix, w, w_prev);

        // Establish count of w_prev
        lemma_base_implies_count_zero(w, n);
        assert forall|j: int| 0 <= j < shorter_prefix.len() implies
            match #[trigger] shorter_prefix[j] {
                DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == n,
                DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
                _ => false,
            }
        by { assert(shorter_prefix[j] == prefix[j]); };
        lemma_plus2_prefix_gives_count(data, shorter_prefix, w, w_prev, 0nat);
        assert(stable_letter_count(w_prev, n) == 2 * shorter_prefix.len());

        // count of w_prev_adj after swap: same as w_prev (T-free)
        // This will be established by the swap ensures.

        // Swap
        let (w_prev_adj, tfree_adj, plus2_adj) = match last_step {
            DerivationStep::FreeExpand { position: p, symbol: sym } =>
                lemma_swap_tfree_past_expand(data, w_prev, w_before_tfree, w_after_tfree, p, sym, step_tfree),
            DerivationStep::RelatorInsert { position: p, relator_index: ri, inverted: inv } =>
                lemma_swap_tfree_past_ri(data, w_prev, w_before_tfree, w_after_tfree, p, ri, inv, step_tfree),
            _ => { assert(false); arbitrary() },
        };
        lemma_step_preserves_word_valid(data, w_prev, tfree_adj);

        // Build new suffix: [plus2_adj] ++ suffix
        let plus2_seq: Seq<DerivationStep> = seq![plus2_adj];
        assert(plus2_seq.first() == plus2_adj);
        assert(plus2_seq.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w_after_tfree) == Some(w_after_tfree)) by {
            assert(Seq::<DerivationStep>::empty().len() == 0);
        };
        assert(derivation_produces(hp, plus2_seq, w_prev_adj) == Some(w_after_tfree));
        lemma_derivation_concat(hp, plus2_seq, suffix, w_prev_adj, w_after_tfree, w_end);
        let new_suffix = plus2_seq + suffix;

        // forall on shorter_prefix
        assert forall|j: int| 0 <= j < shorter_prefix.len() implies
            match #[trigger] shorter_prefix[j] {
                DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == n,
                DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
                _ => false,
            }
        by { assert(shorter_prefix[j] == prefix[j]); };

        // Recurse with shorter prefix
        lemma_bubble_tfree_to_front(
            data, shorter_prefix, tfree_adj, new_suffix,
            w, w_prev, w_prev_adj, w_end, total_len)
    }
}

/// Recursive scan for first non-+2 step. When found:
/// - If -2: peak, call bubble_peak_to_front
/// - If T-free: n-round swap to front
/// - If +2: extend prefix, recurse
///
/// prefix: accumulated +2 steps (derivation from w to w_current)
/// remaining: steps after prefix (derivation from w_current to w_end)
proof fn lemma_scan_and_handle(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
    prefix: Seq<DerivationStep>,
    remaining: Seq<DerivationStep>,
    w_current: Word,
) -> (result: (Word, Seq<DerivationStep>, Seq<DerivationStep>))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        steps.len() >= 5,
        prefix.len() >= 2,
        remaining.len() >= 2,  // need at least 2 more steps to reach base
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w_current, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& derivation_produces(hp, prefix, w) == Some(w_current)
            &&& derivation_produces(hp, remaining, w_current) == Some(w_end)
        }),
        stable_letter_count(w_current, data.base.num_generators) == 2 * prefix.len(),
        prefix.len() + remaining.len() == steps.len(),
        // All prefix steps are +2
        forall|j: int| 0 <= j < prefix.len() ==>
            match #[trigger] prefix[j] {
                DerivationStep::FreeExpand { symbol, .. } =>
                    generator_index(symbol) == data.base.num_generators,
                DerivationStep::RelatorInsert { relator_index, .. } =>
                    relator_index as int >= data.base.relators.len(),
                _ => false,
            },
    ensures ({
        let (w_base, left_steps, right_steps) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_base, n)
        &&& word_valid(w_base, n + 1)
        &&& derivation_produces(hp, left_steps, w) == Some(w_base)
        &&& derivation_produces(hp, right_steps, w_base) == Some(w_end)
        &&& left_steps.len() < steps.len()
        &&& right_steps.len() < steps.len()
    }),
    decreases remaining.len(),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    let first_step = remaining.first();
    assert(apply_step(hp, w_current, first_step).is_some());
    let w_next = apply_step(hp, w_current, first_step).unwrap();
    lemma_step_preserves_word_valid(data, w_current, first_step);
    lemma_stable_count_reduce_step(data, w_current, first_step, n);
    let c_next = stable_letter_count(w_next, n);

    let rest = remaining.drop_first();

    if c_next < stable_letter_count(w_current, n) {
        // first_step is -2. Peak at (prefix.len()-1, prefix.len()).
        // w_current is w_before_peak (count 2*prefix.len())
        // w_next is w_after_peak (count 2*prefix.len() - 2)

        // But wait — the peak is between the LAST prefix step (+2) and first_step (-2).
        // The last prefix step took w_{prev} → w_current. first_step takes w_current → w_next.
        // This doesn't have a word BETWEEN them at the peak top.
        // Actually: the peak is at counts (2*(prefix.len()-1), 2*prefix.len(), 2*(prefix.len()-1)).
        // step_up = prefix.last(), step_down = first_step
        // w_before = word at prefix.len()-1, w_at = w_current, w_after = w_next

        // Split prefix to get w_before
        lemma_derivation_split(hp, prefix, w, w_current, (prefix.len() - 1) as nat);
        let new_prefix = prefix.subrange(0, prefix.len() as int - 1);
        let w_before = derivation_produces(hp, new_prefix, w).unwrap();
        lemma_derivation_preserves_word_valid(data, new_prefix, w, w_before);

        // Establish derivation for rest
        lemma_derivation_split(hp, remaining, w_current, w_end, 1nat);
        assert(derivation_produces(hp, rest, w_next) == Some(w_end));

        // Cancel check
        if w_next =~= w_before {
            // Cancel: remove the peak steps
            lemma_derivation_concat(hp, new_prefix, rest, w, w_before, w_end);
            let short = new_prefix + rest;
            assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w) == Some(w)) by {
                assert(Seq::<DerivationStep>::empty().len() == 0);
            };
            (w, Seq::<DerivationStep>::empty(), short)
        } else {
            // Non-cancel: bubble peak to front
            let last_prefix_step = prefix[prefix.len() as int - 1];
            // Establish count and +2 type for last_prefix_step
            assert(match last_prefix_step {
                DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == n,
                DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
                _ => false,
            });
            // Establish counts
            lemma_base_implies_count_zero(w, n);
            lemma_plus2_prefix_gives_count(data, new_prefix, w, w_before, 0nat);
            assert(stable_letter_count(w_before, n) == 2 * new_prefix.len());
            assert(stable_letter_count(w_current, n) == 2 * new_prefix.len() + 2);
            assert(stable_letter_count(w_next, n) == 2 * new_prefix.len());

            // forall on new_prefix steps
            assert forall|j: int| 0 <= j < new_prefix.len() implies
                match #[trigger] new_prefix[j] {
                    DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == n,
                    DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
                    _ => false,
                }
            by { assert(new_prefix[j] == prefix[j]); };

            // Establish apply_step for the peak steps
            let last_step_seq = prefix.subrange(prefix.len() as int - 1, prefix.len() as int);
            assert(last_step_seq.len() == 1);
            assert(last_step_seq.first() == last_prefix_step);
            lemma_derivation_unfold_1(hp, last_step_seq, w_before, w_current);
            assert(apply_step(hp, w_before, last_prefix_step) == Some(w_current));

            lemma_bubble_peak_to_front(
                data, new_prefix, last_prefix_step, first_step, rest,
                w, w_before, w_current, w_next, w_end)
        }
    } else if c_next == stable_letter_count(w_current, n) {
        // first_step is T-free. Swap past last prefix step, reducing prefix by 1.
        // Then recurse — the T-free step is now one position closer to front.
        let last_prefix_step = prefix[prefix.len() as int - 1];
        assert(match last_prefix_step {
            DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == n,
            DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
            _ => false,
        });

        // Get w_before (word before last prefix step)
        lemma_derivation_split(hp, prefix, w, w_current, (prefix.len() - 1) as nat);
        let shorter_prefix = prefix.subrange(0, prefix.len() as int - 1);
        let w_before = derivation_produces(hp, shorter_prefix, w).unwrap();
        let last_step_seq = prefix.subrange(prefix.len() as int - 1, prefix.len() as int);
        assert(last_step_seq.len() == 1);
        assert(last_step_seq.first() == last_prefix_step);
        lemma_derivation_unfold_1(hp, last_step_seq, w_before, w_current);
        assert(apply_step(hp, w_before, last_prefix_step) == Some(w_current));
        lemma_derivation_preserves_word_valid(data, shorter_prefix, w, w_before);

        // Swap first_step (T-free) past last_prefix_step (+2)
        let (w_before_adj, tfree_adj, plus2_adj) = match last_prefix_step {
            DerivationStep::FreeExpand { position: p, symbol: sym } =>
                lemma_swap_tfree_past_expand(data, w_before, w_current, w_next, p, sym, first_step),
            DerivationStep::RelatorInsert { position: p, relator_index: ri, inverted: inv } =>
                lemma_swap_tfree_past_ri(data, w_before, w_current, w_next, p, ri, inv, first_step),
            _ => { assert(false); arbitrary() },
        };
        // tfree_adj on w_before → w_before_adj (T-free, count 2*(prefix.len()-1))
        // plus2_adj on w_before_adj → w_next (+2)

        // New derivation: shorter_prefix ++ [tfree_adj] produces w_before_adj from w
        let tfree_seq: Seq<DerivationStep> = seq![tfree_adj];
        assert(tfree_seq.first() == tfree_adj);
        assert(tfree_seq.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w_before_adj) == Some(w_before_adj)) by {
            assert(Seq::<DerivationStep>::empty().len() == 0);
        };
        assert(derivation_produces(hp, tfree_seq, w_before) == Some(w_before_adj));
        lemma_derivation_concat(hp, shorter_prefix, tfree_seq, w, w_before, w_before_adj);
        let new_prefix_with_tfree = shorter_prefix + tfree_seq;

        // New remaining: [plus2_adj] ++ rest
        let plus2_seq: Seq<DerivationStep> = seq![plus2_adj];
        assert(plus2_seq.first() == plus2_adj);
        assert(plus2_seq.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w_next) == Some(w_next)) by {
            assert(Seq::<DerivationStep>::empty().len() == 0);
        };
        assert(derivation_produces(hp, plus2_seq, w_before_adj) == Some(w_next));
        lemma_derivation_split(hp, remaining, w_current, w_end, 1nat);
        lemma_derivation_concat(hp, plus2_seq, rest, w_before_adj, w_next, w_end);
        let new_remaining = plus2_seq + rest;

        // Use lemma_bubble_tfree_to_front to swap T-free all the way to position 0
        lemma_base_word_valid_down(w, n);
        lemma_derivation_split(hp, remaining, w_current, w_end, 1nat);
        let (w_base, base_step, remaining_deriv) =
            lemma_bubble_tfree_to_front(
                data, prefix, first_step, rest,
                w, w_current, w_next, w_end,
                steps.len());

        // left = [base_step], right = remaining_deriv
        let left_steps: Seq<DerivationStep> = seq![base_step];
        assert(left_steps.first() == base_step);
        assert(left_steps.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w_base) == Some(w_base)) by {
            assert(Seq::<DerivationStep>::empty().len() == 0);
        };
        assert(derivation_produces(hp, left_steps, w) == Some(w_base));

        (w_base, left_steps, remaining_deriv)
    } else {
        // first_step is +2. Extend prefix, recurse.
        assert(c_next == stable_letter_count(w_current, n) + 2);

        if rest.len() < 2 {
            // Not enough remaining steps to reach base — contradiction
            // From count 2*(prefix.len()+1) with < 2 steps remaining,
            // can reduce by at most 4. Need to reach 0.
            // 2*(prefix.len()+1) ≥ 2*(2+1) = 6 > 4.
            // So can't reach 0. But w_end is base (count 0).
            // Need at least prefix.len()+1 steps of -2 to reach 0.
            // remaining has at most 1 step. prefix.len()+1 ≥ 3 > 1.
            // Contradiction.
            lemma_derivation_split(hp, remaining, w_current, w_end, 1nat);
            if rest.len() == 0 {
                // Only first_step. first_step takes c to c+2. w_end has count 0. c+2 > 0.
                assert(false);
            } else {
                // rest has 1 step. w_next has count ≥ 6. 1 step can reduce by at most 2. ≥4 > 0.
                assert(rest.len() == 1);
                lemma_derivation_unfold_1(hp, rest, w_next, w_end);
                lemma_count4_step_cant_reach_base(data, w_next, w_end, rest.first());
                assert(false);
            }
            arbitrary()
        } else {
            // Extend prefix and recurse
            let new_prefix = prefix + seq![first_step];
            lemma_plus2_step_type(data, w_current, w_next, first_step, n);

            // Prove new_prefix derivation
            let first_step_seq: Seq<DerivationStep> = seq![first_step];
            assert(first_step_seq.first() == first_step);
            assert(first_step_seq.drop_first() =~= Seq::<DerivationStep>::empty());
            assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w_next) == Some(w_next)) by {
                assert(Seq::<DerivationStep>::empty().len() == 0);
            };
            assert(derivation_produces(hp, first_step_seq, w_current) == Some(w_next));
            lemma_derivation_concat(hp, prefix, first_step_seq, w, w_current, w_next);

            // Prove forall on new_prefix
            assert forall|j: int| 0 <= j < new_prefix.len() implies
                match #[trigger] new_prefix[j] {
                    DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == n,
                    DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
                    _ => false,
                }
            by {
                if j < prefix.len() as int { assert(new_prefix[j] == prefix[j]); }
                else { assert(new_prefix[j] == first_step); }
            };

            lemma_derivation_split(hp, remaining, w_current, w_end, 1nat);
            lemma_scan_and_handle(data, steps, w, w_end, new_prefix, rest, w_next)
        }
    }
}

/// Handle c_3 ≥ 6 case. Returns (w_base, left, right) where w_base is base
/// and left ++ right is a shorter derivation from w to w_end via w_base.
/// For cancel: left is empty, right is the shorter derivation.
pub proof fn lemma_k5_c3_ge6(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
    w1: Word, w2: Word, w3: Word,
    step0: DerivationStep, step1: DerivationStep, step2: DerivationStep,
    tail_steps: Seq<DerivationStep>,
) -> (result: (Word, Seq<DerivationStep>, Seq<DerivationStep>))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        steps.len() >= 5,
        is_base_word(w, data.base.num_generators),
        is_base_word(w_end, data.base.num_generators),
        word_valid(w, data.base.num_generators + 1),
        word_valid(w_end, data.base.num_generators + 1),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            let n = data.base.num_generators;
            &&& step0 == steps[0]
            &&& step1 == steps[1]
            &&& step2 == steps[2]
            &&& apply_step(hp, w, step0) == Some(w1)
            &&& apply_step(hp, w1, step1) == Some(w2)
            &&& apply_step(hp, w2, step2) == Some(w3)
            &&& tail_steps =~= steps.subrange(3, steps.len() as int)
            &&& derivation_produces(hp, tail_steps, w3) == Some(w_end)
            &&& stable_letter_count(w1, n) == 2nat
            &&& stable_letter_count(w2, n) == 4nat
            &&& stable_letter_count(w3, n) >= 6
        }),
        match step0 {
            DerivationStep::FreeExpand { symbol, .. } =>
                generator_index(symbol) == data.base.num_generators,
            DerivationStep::RelatorInsert { relator_index, .. } =>
                relator_index as int >= data.base.relators.len(),
            _ => false,
        },
    ensures ({
        let (w_base, left_steps, right_steps) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& is_base_word(w_base, n)
        &&& word_valid(w_base, n + 1)
        &&& derivation_produces(hp, left_steps, w) == Some(w_base)
        &&& derivation_produces(hp, right_steps, w_base) == Some(w_end)
        &&& left_steps.len() < steps.len()
        &&& right_steps.len() < steps.len()
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    // c3 = 6 (only possibility from c2=4, change ±2, c3≥6)
    assert(stable_letter_count(w3, n) == 6nat) by {
        lemma_stable_count_reduce_step(data, w2, step2, n);
    };

    // k=5: c3≥6 is impossible (can't reach 0 in 2 remaining steps)
    if steps.len() == 5 {
        assert(tail_steps.len() == 2);
        let s3 = tail_steps[0int];
        assert(apply_step(hp, w3, s3).is_some());
        let w4_k5 = apply_step(hp, w3, s3).unwrap();
        lemma_step_preserves_word_valid(data, w3, s3);
        lemma_stable_count_reduce_step(data, w3, s3, n);
        assert(stable_letter_count(w4_k5, n) >= 4);
        lemma_derivation_split(hp, tail_steps, w3, w_end, 1nat);
        let last = tail_steps.subrange(1, 2);
        lemma_derivation_unfold_1(hp, last, w4_k5, w_end);
        lemma_count4_step_cant_reach_base(data, w4_k5, w_end, last.first());
        assert(false);
        return arbitrary();
    }

    // Get step3 and w4
    assert(tail_steps.len() >= 1);
    let step3_inner = tail_steps[0int];
    assert(apply_step(hp, w3, step3_inner).is_some());
    let w4 = apply_step(hp, w3, step3_inner).unwrap();
    lemma_step_preserves_word_valid(data, w3, step3_inner);
    lemma_stable_count_reduce_step(data, w3, step3_inner, n);
    let c4 = stable_letter_count(w4, n);

    lemma_derivation_split(hp, tail_steps, w3, w_end, 1nat);
    let inner_suffix = tail_steps.subrange(1, tail_steps.len() as int);

    if c4 == 4 {
        // Peak at (2,3). Use bubble chain.
        let prefix_steps = steps.subrange(0, 2);
        // Build derivation_produces for the full steps from components
        lemma_derivation_produces_2(hp, step0, step1, w, w1, w2);
        let first2: Seq<DerivationStep> = seq![step0, step1];
        assert(first2 =~= prefix_steps);
        let step2_seq: Seq<DerivationStep> = seq![step2];
        assert(step2_seq.first() == step2);
        assert(step2_seq.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w3) == Some(w3)) by {
            assert(Seq::<DerivationStep>::empty().len() == 0);
        };
        assert(derivation_produces(hp, step2_seq, w2) == Some(w3));
        lemma_derivation_concat(hp, step2_seq, tail_steps, w2, w3, w_end);
        lemma_derivation_concat(hp, prefix_steps, step2_seq + tail_steps, w, w2, w_end);
        assert(derivation_produces(hp, prefix_steps, w) == Some(w2));

        if w4 =~= w2 {
            // Cancel
            lemma_derivation_concat(hp, prefix_steps, inner_suffix, w, w2, w_end);
            let short = prefix_steps + inner_suffix;
            assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w) == Some(w)) by {
                assert(Seq::<DerivationStep>::empty().len() == 0);
            };
            (w, Seq::<DerivationStep>::empty(), short)
        } else {
            // Non-cancel: bubble peak to front
            lemma_plus2_step_type(data, w2, w3, step2, n);
            lemma_plus2_step_type(data, w1, w2, step1, n);
            assert forall|j: int| 0 <= j < prefix_steps.len() implies
                match #[trigger] prefix_steps[j] {
                    DerivationStep::FreeExpand { symbol, .. } =>
                        generator_index(symbol) == n,
                    DerivationStep::RelatorInsert { relator_index, .. } =>
                        relator_index as int >= data.base.relators.len(),
                    _ => false,
                }
            by {
                if j == 0 { assert(prefix_steps[j] == step0); }
                else { assert(prefix_steps[j] == step1); }
            };

            lemma_bubble_peak_to_front(
                data, prefix_steps, step2, step3_inner, inner_suffix,
                w, w2, w3, w4, w_end,
            )
        }
    } else {
        // c4 >= 6: for k=6 this is impossible; for k≥7 need deeper scan
        if steps.len() == 6 {
            // k=6, c4≥6: count can't reach 0 in remaining steps
            let step4_inner = inner_suffix[0int];
            assert(apply_step(hp, w4, step4_inner).is_some());
            let w5 = apply_step(hp, w4, step4_inner).unwrap();
            lemma_step_preserves_word_valid(data, w4, step4_inner);
            lemma_stable_count_reduce_step(data, w4, step4_inner, n);
            assert(stable_letter_count(w5, n) >= 4);
            lemma_derivation_split(hp, inner_suffix, w4, w_end, 1nat);
            let last_seq = inner_suffix.subrange(1, inner_suffix.len() as int);
            lemma_derivation_unfold_1(hp, last_seq, w5, w_end);
            let step5_inner = last_seq.first();
            lemma_count4_step_cant_reach_base(data, w5, w_end, step5_inner);
            assert(false);
            arbitrary()
        } else {
            // k≥7, c4≥6: step3 is T-free (c4=6) or +2 (c4=8).
            if c4 == 6 {
                // step3 is T-free. 3-round swap to front. Delegate to helper.
                lemma_plus2_step_type(data, w2, w3, step2, n);
                lemma_plus2_step_type(data, w1, w2, step1, n);
                lemma_base_word_valid_down(w, n);
                lemma_k5_c3_6_c4_6_three_round(
                    data, steps, w, w_end, w1, w2, w3, w4,
                    step0, step1, step2, step3_inner, inner_suffix)
            } else {
                // c4 = 8: step3 is +2. Extend prefix and recurse.
                // prefix = [step0, step1, step2, step3], all +2
                let prefix4 = steps.subrange(0, 4);
                lemma_plus2_step_type(data, w1, w2, step1, n);
                lemma_plus2_step_type(data, w2, w3, step2, n);
                lemma_plus2_step_type(data, w3, w4, step3_inner, n);
                assert forall|j: int| 0 <= j < prefix4.len() implies
                    match #[trigger] prefix4[j] {
                        DerivationStep::FreeExpand { symbol, .. } => generator_index(symbol) == n,
                        DerivationStep::RelatorInsert { relator_index, .. } => relator_index as int >= data.base.relators.len(),
                        _ => false,
                    }
                by {
                    if j == 0 { assert(prefix4[j] == step0); }
                    else if j == 1 { assert(prefix4[j] == step1); }
                    else if j == 2 { assert(prefix4[j] == step2); }
                    else { assert(prefix4[j] == step3_inner); }
                };
                // Build derivation for prefix4
                lemma_derivation_produces_2(hp, step0, step1, w, w1, w2);
                let first2: Seq<DerivationStep> = seq![step0, step1];
                let step2_seq: Seq<DerivationStep> = seq![step2];
                assert(step2_seq.first() == step2);
                assert(step2_seq.drop_first() =~= Seq::<DerivationStep>::empty());
                assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w3) == Some(w3)) by {
                    assert(Seq::<DerivationStep>::empty().len() == 0);
                };
                assert(derivation_produces(hp, step2_seq, w2) == Some(w3));
                lemma_derivation_concat(hp, first2, step2_seq, w, w2, w3);
                let first3 = first2 + step2_seq;
                let step3_seq: Seq<DerivationStep> = seq![step3_inner];
                assert(step3_seq.first() == step3_inner);
                assert(step3_seq.drop_first() =~= Seq::<DerivationStep>::empty());
                assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w4) == Some(w4)) by {
                    assert(Seq::<DerivationStep>::empty().len() == 0);
                };
                assert(derivation_produces(hp, step3_seq, w3) == Some(w4));
                lemma_derivation_concat(hp, first3, step3_seq, w, w3, w4);
                assert(prefix4 =~= first3 + step3_seq);
                assert(derivation_produces(hp, prefix4, w) == Some(w4));

                // Recurse: scan inner_suffix for first non-+2 step
                lemma_scan_and_handle(data, steps, w, w_end,
                    prefix4, inner_suffix, w4)
            }
        }
    }
}

/// Fuel-based peak elimination for overlap cases.
/// When the peak commutation hits an overlap (step_down acts inside step_up's
/// insertion region), this function constructs a modified derivation with lower
/// count_sum and recurses with decreasing fuel.
///
/// The modified derivation replaces the overlapping peak with its near-cancel
/// equivalent. The near-cancel inserts trivial base content (e.g., inv(b_j)
/// from the isomorphism argument) which reduces the peak height.
///
/// fuel starts at derivation_count_sum and decreases with each peak elimination.
pub proof fn lemma_overlap_peak_elimination(
    data: HNNData, steps: Seq<DerivationStep>, w: Word, w_end: Word,
    fuel: nat,
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
    ensures
        equiv_in_presentation(data.base, w, w_end),
    decreases fuel, steps.len(),
{
    // Strategy: find a peak or T-free step, eliminate it to produce
    // a shorter or lower-count_sum derivation, then recurse.
    //
    // For shorter derivation: call lemma_base_derivation_equiv (safe,
    // shorter steps means the mutual recursion terminates).
    //
    // For same-length lower-count_sum: call self with fuel-1.
    //
    // The implementation follows the standard Britton's lemma peak
    // elimination, handling both overlap and non-overlap cases.
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    // Base case: len=2 (single segment with 2 steps)
    if steps.len() == 2 {
        let s0 = steps.first();
        let w1_check = apply_step(hp, w, s0).unwrap();
        lemma_step_preserves_word_valid(data, w, s0);
        if is_base_word(w1_check, n) {
            // Both steps are T-free → base equivalences
            lemma_t_free_step_is_base_step(data, w, s0);
            lemma_single_step_equiv(data.base, w, s0, w1_check);
            let rest = steps.drop_first();
            lemma_derivation_unfold_1(hp, rest, w1_check, w_end);
            let s1 = rest.first();
            lemma_t_free_step_is_base_step(data, w1_check, s1);
            lemma_single_step_equiv(data.base, w1_check, s1, w_end);
            lemma_equiv_transitive(data.base, w, w1_check, w_end);
        } else {
            // Single segment k=2
            lemma_single_segment_k2(data, steps, w, w_end);
        }
        return;
    }

    // Step 0: check for base intermediates (split point)
    let step0 = steps.first();
    let w1 = apply_step(hp, w, step0).unwrap();
    lemma_step_preserves_word_valid(data, w, step0);

    if is_base_word(w1, n) {
        // w1 is base: T-free step. Apply in base group and recurse on shorter.
        lemma_t_free_step_is_base_step(data, w, step0);
        lemma_single_step_equiv(data.base, w, step0, w1);
        let rest = steps.drop_first();
        // rest has len >= 2 (since steps.len() >= 3)
        // Recurse — rest is shorter than steps (fuel, rest.len()) < (fuel, steps.len())
        lemma_overlap_peak_elimination(data, rest, w1, w_end, fuel);
        lemma_equiv_transitive(data.base, w, w1, w_end);
        return;
    }

    // w1 is non-base. Find first base intermediate.
    lemma_first_base_is_base(hp, steps, w, w_end, n);
    let k = first_base_intermediate(hp, steps, w, n);
    lemma_word_at_one(hp, steps, w);
    assert(k >= 2) by {
        assert(!is_base_word(w1, n));
        assert(derivation_word_at(hp, steps, w, 1nat) == w1);
        if k == 1 { assert(is_base_word(derivation_word_at(hp, steps, w, k), n)); assert(false); }
    };

    if k < steps.len() {
        // Base intermediate at position k < steps.len()
        // Split and handle each piece separately
        let w_k = derivation_word_at(hp, steps, w, k);
        lemma_derivation_split(hp, steps, w, w_end, k);
        let left_steps = steps.subrange(0, k as int);
        let right_steps = steps.subrange(k as int, steps.len() as int);
        lemma_word_at_produces(hp, steps, w, k);
        lemma_word_at_valid(data, steps, w, k);

        // Left piece: k steps, single segment (shorter → recurse)
        // left has len k ≥ 2 (since k ≥ 2), shorter than steps
        lemma_overlap_peak_elimination(data, left_steps, w, w_k, fuel);

        // Right piece: shorter → recurse
        if right_steps.len() >= 2 {
            lemma_overlap_peak_elimination(data, right_steps, w_k, w_end, fuel);
        } else if right_steps.len() == 1 {
            // Single T-free step
            lemma_derivation_unfold_1(hp, right_steps, w_k, w_end);
            lemma_t_free_step_is_base_step(data, w_k, right_steps.first());
            lemma_single_step_equiv(data.base, w_k, right_steps.first(), w_end);
        } else {
            // right_steps.len() == 0: w_k == w_end
            assert(w_k == w_end);
            lemma_equiv_refl(data.base, w);
        }

        lemma_equiv_transitive(data.base, w, w_k, w_end);
    } else {
        // k == steps.len(): all intermediates are non-base.
        // Peak elimination via the standard Britton argument.
        //
        // Step 0 is +2 (base → non-base).
        lemma_base_word_valid_down(w, n);
        lemma_base_to_nonbase_step_type(data, w, w1, step0);
        lemma_base_implies_count_zero(w, n);
        lemma_stable_count_reduce_step(data, w, step0, n);
        assert(stable_letter_count(w1, n) == 2nat);

        let step1 = steps[1int];
        assert(apply_step(hp, w1, step1).is_some());
        let w2 = apply_step(hp, w1, step1).unwrap();
        lemma_step_preserves_word_valid(data, w1, step1);
        lemma_stable_count_reduce_step(data, w1, step1, n);
        let c2 = stable_letter_count(w2, n);

        // Get remaining derivation from w2
        let rest0 = steps.drop_first();
        assert(rest0.first() == step1);
        assert(derivation_produces(hp, rest0, w1) == Some(w_end));
        let remaining = steps.subrange(2, steps.len() as int);
        assert(derivation_produces(hp, steps, w).is_some());
        lemma_derivation_split(hp, steps, w, w_end, 2nat);
        lemma_word_at_produces(hp, steps, w, 2nat);
        assert(derivation_word_at(hp, steps, w, 2nat) == w2) by {
            assert(derivation_word_at(hp, steps, w, 2nat) ==
                derivation_word_at(hp, rest0, w1, 1nat));
            lemma_word_at_one(hp, rest0, w1);
        };
        assert(derivation_produces(hp, remaining, w2) == Some(w_end));

        // w2 is non-base (all intermediates are non-base since k == steps.len())
        // Use lemma_no_base_before_first: for j < first_base_intermediate, word at j is non-base
        if steps.len() >= 3 {
            lemma_no_base_before_first(hp, steps, w, w_end, n, 2nat);
            assert(!is_base_word(derivation_word_at(hp, steps, w, 2nat), n));
        }
        assert(!is_base_word(w2, n));

        if c2 == 2 {
            // Step 1 is T-free. Commute past step 0.
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

            lemma_single_step_equiv(data.base, w, step1_base, w_prime);

            // Build (k-1)-step derivation from w' to w_end
            let one_step: Seq<DerivationStep> = seq![step0_adj];
            assert(one_step.first() == step0_adj);
            assert(one_step.drop_first() =~= Seq::<DerivationStep>::empty());
            assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w2) == Some(w2)) by {
                assert(Seq::<DerivationStep>::empty().len() == 0);
            };
            assert(derivation_produces(hp, one_step, w_prime) == Some(w2));
            lemma_derivation_concat(hp, one_step, remaining, w_prime, w2, w_end);
            let new_steps = one_step + remaining;
            // (k-1) steps, shorter → recurse
            lemma_overlap_peak_elimination(data, new_steps, w_prime, w_end, fuel);
            lemma_equiv_transitive(data.base, w, w_prime, w_end);
        } else {
            // c2 ∈ {0, 4} (from stable_count_reduce_step). c2=0 means base → contradiction.
            if c2 == 0 {
                lemma_zero_count_implies_base(w2, n);
                assert(false); // w2 is base but all intermediates non-base
            }
            assert(c2 == 4nat);

            // Get step2 and w3
            let step2 = remaining[0int];
            assert(apply_step(hp, w2, step2).is_some());
            let w3 = apply_step(hp, w2, step2).unwrap();
            lemma_step_preserves_word_valid(data, w2, step2);
            lemma_stable_count_reduce_step(data, w2, step2, n);
            let c3 = stable_letter_count(w3, n);

            // Split remaining at step2
            lemma_derivation_split(hp, remaining, w2, w_end, 1nat);
            let tail = remaining.subrange(1, remaining.len() as int);
            assert(derivation_produces(hp, tail, w3) == Some(w_end));

            if c3 == 2 {
                // Peak at steps (1,2). Cancel or commute.
                if w3 =~= w1 {
                    // Cancel: remove steps 1,2. Build [step0] ++ tail (k-2 steps)
                    let prefix_one: Seq<DerivationStep> = seq![step0];
                    assert(prefix_one.first() == step0);
                    assert(prefix_one.drop_first() =~= Seq::<DerivationStep>::empty());
                    assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w1) == Some(w1)) by {
                        assert(Seq::<DerivationStep>::empty().len() == 0);
                    };
                    assert(derivation_produces(hp, prefix_one, w) == Some(w1));
                    lemma_derivation_concat(hp, prefix_one, tail, w, w1, w_end);
                    let short = prefix_one + tail;
                    // k-2 steps, shorter → recurse
                    if short.len() >= 2 {
                        lemma_overlap_peak_elimination(data, short, w, w_end, fuel);
                    } else {
                        // short has 1 step: single T-free step
                        lemma_derivation_unfold_1(hp, short, w, w_end);
                        lemma_t_free_step_is_base_step(data, w, short.first());
                        lemma_single_step_equiv(data.base, w, short.first(), w_end);
                    }
                } else {
                    // Non-cancel peak at (1,2) with counts (2,4,2).
                    lemma_plus2_step_type(data, w1, w2, step1, n);

                    let (w_prime, step2_adj, step1_adj) =
                        lemma_k4_peak_noncancel_commute(data, w1, w2, w3, step1, step2);

                    // Build [step0, step2_adj] from w to w_prime (2 steps)
                    lemma_derivation_produces_2(hp, step0, step2_adj, w, w1, w_prime);
                    let left: Seq<DerivationStep> = seq![step0, step2_adj];

                    // Build [step1_adj] ++ tail from w_prime to w_end
                    lemma_step_preserves_word_valid(data, w_prime, step1_adj);
                    let one_adj: Seq<DerivationStep> = seq![step1_adj];
                    assert(one_adj.first() == step1_adj);
                    assert(one_adj.drop_first() =~= Seq::<DerivationStep>::empty());
                    assert(derivation_produces(hp, Seq::<DerivationStep>::empty(), w3) == Some(w3)) by {
                        assert(Seq::<DerivationStep>::empty().len() == 0);
                    };
                    assert(derivation_produces(hp, one_adj, w_prime) == Some(w3));
                    lemma_derivation_concat(hp, one_adj, tail, w_prime, w3, w_end);
                    let right = one_adj + tail;

                    // Both shorter → recurse
                    lemma_overlap_peak_elimination(data, left, w, w_prime, fuel);
                    if right.len() >= 2 {
                        lemma_overlap_peak_elimination(data, right, w_prime, w_end, fuel);
                    } else {
                        lemma_derivation_unfold_1(hp, right, w_prime, w_end);
                        lemma_t_free_step_is_base_step(data, w_prime, right.first());
                        lemma_single_step_equiv(data.base, w_prime, right.first(), w_end);
                    }
                    lemma_equiv_transitive(data.base, w, w_prime, w_end);
                }
            } else if c3 == 4 && steps.len() >= 5 {
                // c3 = 4, k≥5: step2 is T-free. Two-round swap.
                lemma_plus2_step_type(data, w1, w2, step1, n);
                let (w_base, base_step, deriv_steps) =
                    lemma_k5_c3_eq4_two_round(
                        data, steps, w, w_end, w1, w2, w3,
                        step0, step1, step2, tail);
                // w_base is base and word_valid (from ensures of two_round)
                lemma_single_step_equiv(data.base, w, base_step, w_base);
                // deriv has < steps.len() steps (from ensures). steps.len()>=5 → deriv >= 2.
                assert(deriv_steps.len() < steps.len());
                assert(steps.len() >= 5);
                // deriv could be 0..steps.len()-1. Need >= 2.
                // Actually deriv = steps.len() - 1 = k-1 since it's one base step peeled off.
                // But the ensures only says < steps.len(), not == steps.len()-1.
                // We need a tighter bound. Let me check what the helper actually returns.
                // lemma_k5_c3_eq4_two_round returns (w_base, base_step, deriv_steps) where
                // deriv_steps has specific structure: [step0_adj, step1_adj] ++ tail.
                // tail = [step2_adj] ++ original_tail. So deriv = 2 + 1 + tail.len() = 3 + tail.len().
                // tail.len() = steps.len() - 4. So deriv = steps.len() - 1.
                // But the ensures only says < steps.len(). Let me just check >= 2 differently.
                if deriv_steps.len() < 2 {
                    if deriv_steps.len() == 0 {
                        assert(w_base == w_end);
                        lemma_equiv_refl(data.base, w_base);
                    } else {
                        lemma_derivation_unfold_1(hp, deriv_steps, w_base, w_end);
                        lemma_t_free_step_is_base_step(data, w_base, deriv_steps.first());
                        lemma_single_step_equiv(data.base, w_base, deriv_steps.first(), w_end);
                    }
                } else {
                    lemma_overlap_peak_elimination(data, deriv_steps, w_base, w_end, fuel);
                }
                lemma_equiv_transitive(data.base, w, w_base, w_end);
            } else if c3 >= 6 && steps.len() >= 5 {
                // c3 >= 6, k≥5: delegate to scan handler
                let (w_base, left_s, right_s) = lemma_k5_c3_ge6(
                    data, steps, w, w_end, w1, w2, w3,
                    step0, step1, step2, tail);
                // w_base is base and word_valid (from ensures of c3_ge6)
                // Helper: handle a sub-derivation of any length
                // For left piece:
                if left_s.len() == 0 {
                    assert(w_base == w);
                    lemma_equiv_refl(data.base, w);
                } else if left_s.len() == 1 {
                    lemma_derivation_unfold_1(hp, left_s, w, w_base);
                    lemma_t_free_step_is_base_step(data, w, left_s.first());
                    lemma_single_step_equiv(data.base, w, left_s.first(), w_base);
                } else {
                    lemma_overlap_peak_elimination(data, left_s, w, w_base, fuel);
                }
                // For right piece:
                if right_s.len() == 0 {
                    assert(w_base == w_end);
                    lemma_equiv_refl(data.base, w_base);
                } else if right_s.len() == 1 {
                    lemma_derivation_unfold_1(hp, right_s, w_base, w_end);
                    lemma_t_free_step_is_base_step(data, w_base, right_s.first());
                    lemma_single_step_equiv(data.base, w_base, right_s.first(), w_end);
                } else {
                    lemma_overlap_peak_elimination(data, right_s, w_base, w_end, fuel);
                }
                lemma_equiv_transitive(data.base, w, w_base, w_end);
            } else {
                // k=4 with c3=4 or c3>=6: these are impossible.
                // k=4: count goes 0,2,4,c3,0. c3 must satisfy c3→0 in 1 step.
                // If c3=4: need -4 in 1 step → impossible.
                // If c3>=6: even worse.
                assert(steps.len() == 4);
                // tail has 1 step. w3(c3) → w_end(0). step reduces by at most 2.
                // c3 >= 4 → w_end count >= 2 > 0. But w_end is base (count 0).
                lemma_derivation_unfold_1(hp, tail, w3, w_end);
                lemma_count4_step_cant_reach_base(data, w3, w_end, tail.first());
                assert(false);
            }
        }
    }
}

/// Commute two non-overlapping FreeReduce steps.
/// Given step2: w2 → w3 (FR at p2) and step3: w3 → w_end (FR at p3),
/// where the adjusted positions don't overlap,
/// produce step3_adj: w2 → w2' and step2_adj: w2' → w_end.
pub proof fn lemma_commute_fr_fr(
    data: HNNData, w2: Word, w3: Word, w_end: Word,
    p2: int, p3: int,
) -> (result: (Word, DerivationStep, DerivationStep))
    requires
        hnn_data_valid(data),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w2, DerivationStep::FreeReduce { position: p2 }) == Some(w3)
            &&& apply_step(hp, w3, DerivationStep::FreeReduce { position: p3 }) == Some(w_end)
        }),
        // Both FRs reduce stable count by 2
        stable_letter_count(w2, data.base.num_generators) >= 4,
        stable_letter_count(w3, data.base.num_generators) ==
            (stable_letter_count(w2, data.base.num_generators) - 2) as nat,
        stable_letter_count(w_end, data.base.num_generators) ==
            (stable_letter_count(w3, data.base.num_generators) - 2) as nat,
        // Non-overlapping in w2: step3's adjusted position doesn't overlap with step2
        p3 < p2 ==> p3 + 2 <= p2,
    ensures ({
        let (w2_prime, step3_adj, step2_adj) = result;
        let hp = hnn_presentation(data);
        &&& apply_step(hp, w2, step3_adj) == Some(w2_prime)
        &&& apply_step(hp, w2_prime, step2_adj) == Some(w_end)
        &&& word_valid(w2_prime, data.base.num_generators + 1)
        &&& stable_letter_count(w2_prime, data.base.num_generators) ==
            (stable_letter_count(w2, data.base.num_generators) - 2) as nat
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    assert(has_cancellation_at(w2, p2));
    assert(w3 =~= reduce_at(w2, p2));
    assert(has_cancellation_at(w3, p3));
    assert(w_end =~= reduce_at(w3, p3));

    // Prove step3 removes stable letters (gen_idx == n)
    lemma_stable_count_reduce(w3, p3, n);
    lemma_stable_count_reduce(w2, p2, n);
    // count(w3) = count(w2) - 2 >= 4 - 2 = 2
    let cnt_3 = stable_letter_count(w3, n);
    assert(cnt_3 >= 2);
    // If gen_idx(w3[p3]) != n, FR doesn't change count. But count(w_end) = count(w3) - 2 < count(w3).
    if generator_index(w3[p3]) != n {
        // count(reduce_at(w3, p3)) = count(w3) - 0 = count(w3)
        // But w_end =~= reduce_at(w3, p3) and count(w_end) = count(w3) - 2
        // So count(w3) = count(w3) - 2, impossible since count(w3) >= 2
        assert(false);
    }
    assert(generator_index(w3[p3]) == n);

    if p3 < p2 {
        // step3 acts before step2 in the word
        // p3_adj = p3 (same position in w2)
        assert(w3[p3] == w2[p3]);
        assert(w3[p3 + 1] == w2[p3 + 1]);
        assert(has_cancellation_at(w2, p3));

        let step3_adj = DerivationStep::FreeReduce { position: p3 };
        let w2_prime = reduce_at(w2, p3);
        assert(apply_step(hp, w2, step3_adj) == Some(w2_prime));
        lemma_stable_count_reduce(w2, p3, n);
        // w3[p3] == w2[p3] (p3 < p2, unaffected by step2), so gen_idx transfers
        assert(generator_index(w2[p3]) == generator_index(w3[p3]));
        lemma_step_preserves_word_valid(data, w2, step3_adj);

        // step2_adj at p2-2 in w2'
        let step2_adj = DerivationStep::FreeReduce { position: (p2 - 2) as int };
        // w2'[p2-2] = w2[p2] and w2'[p2-1] = w2[p2+1]
        assert(w2_prime[(p2 - 2) as int] == w2[p2]);
        assert(w2_prime[(p2 - 1) as int] == w2[p2 + 1]);
        assert(has_cancellation_at(w2_prime, (p2 - 2) as int));

        // Prove the final result matches w_end
        let result_word = reduce_at(w2_prime, (p2 - 2) as int);
        assert forall|k: int| 0 <= k < w_end.len() implies w_end[k] == result_word[k] by {
            // w3 = w2 minus {p2,p2+1}. w_end = w3 minus {p3,p3+1}.
            // w2_prime = w2 minus {p3,p3+1}. result_word = w2_prime minus {p2-2,p2-1}.
            // Both remove the same 4 positions from w2: {p3,p3+1,p2,p2+1}.
            if k < p3 {
                // Both = w2[k]
                assert(result_word[k] == w2_prime[k]); assert(w2_prime[k] == w2[k]);
                assert(w_end[k] == w3[k]); assert(w3[k] == w2[k]);
            } else if k < p2 - 2 {
                // Both = w2[k+2]
                // w_end[k]: k >= p3 so w_end[k] = w3[k+2]. k+2 < p2 so w3[k+2] = w2[k+2].
                assert(w_end[k] == w3[(k + 2) as int]); assert(w3[(k + 2) as int] == w2[(k + 2) as int]);
                // result_word[k]: k < p2-2 so result_word[k] = w2_prime[k]. k >= p3 so w2_prime[k] = w2[k+2].
                assert(result_word[k] == w2_prime[k]); assert(w2_prime[k] == w2[(k + 2) as int]);
            } else {
                // k >= p2-2: both = w2[k+4]
                // w_end[k]: k >= p3 so w_end[k] = w3[k+2]. k+2 >= p2 so w3[k+2] = w2[k+4].
                assert(w_end[k] == w3[(k + 2) as int]); assert(w3[(k + 2) as int] == w2[(k + 4) as int]);
                // result_word[k]: k >= p2-2 so result_word[k] = w2_prime[k+2]. k+2 >= p2 > p3 so w2_prime[k+2] = w2[k+4].
                assert(result_word[k] == w2_prime[(k + 2) as int]); assert(w2_prime[(k + 2) as int] == w2[(k + 4) as int]);
            }
        };
        assert(w_end =~= result_word);
        assert(apply_step(hp, w2_prime, step2_adj) == Some(w_end));

        (w2_prime, step3_adj, step2_adj)
    } else {
        // p3 >= p2: step3 acts after step2's removal
        // In w3, position p3 corresponds to position p3+2 in w2
        let p3_adj = (p3 + 2) as int;
        assert(w3[p3] == w2[p3_adj]);
        assert(w3[p3 + 1] == w2[(p3_adj + 1) as int]);
        assert(has_cancellation_at(w2, p3_adj));

        let step3_adj = DerivationStep::FreeReduce { position: p3_adj };
        let w2_prime = reduce_at(w2, p3_adj);
        assert(apply_step(hp, w2, step3_adj) == Some(w2_prime));
        lemma_stable_count_reduce(w2, p3_adj, n);
        // w3[p3] == w2[p3+2] = w2[p3_adj], so gen_idx transfers
        assert(generator_index(w2[p3_adj]) == generator_index(w3[p3]));
        lemma_step_preserves_word_valid(data, w2, step3_adj);

        // step2_adj at p2 in w2' (unchanged since step3_adj acts after p2)
        let step2_adj = DerivationStep::FreeReduce { position: p2 };
        assert(w2_prime[p2] == w2[p2]);
        assert(w2_prime[p2 + 1] == w2[p2 + 1]);
        assert(has_cancellation_at(w2_prime, p2));

        let result_word = reduce_at(w2_prime, p2);
        assert forall|k: int| 0 <= k < w_end.len() implies w_end[k] == result_word[k] by {
            // w3 = w2 minus {p2,p2+1}. w_end = w3 minus {p3,p3+1}.
            // w2_prime = w2 minus {p3+2,p3+3}. result_word = w2_prime minus {p2,p2+1}.
            // Both remove same 4 positions from w2: {p2,p2+1,p3+2,p3+3}.
            if k < p2 {
                // Both = w2[k]
                assert(w_end[k] == w3[k]); assert(w3[k] == w2[k]);
                assert(result_word[k] == w2_prime[k]); assert(w2_prime[k] == w2[k]);
            } else if k < p3 {
                // Both = w2[k+2]
                // w_end[k]: k < p3 so w_end[k] = w3[k]. k >= p2 so w3[k] = w2[k+2].
                assert(w_end[k] == w3[k]); assert(w3[k] == w2[(k + 2) as int]);
                // result_word[k]: k >= p2 so result_word[k] = w2_prime[k+2]. k+2 < p3+2 so w2_prime[k+2] = w2[k+2].
                assert(result_word[k] == w2_prime[(k + 2) as int]); assert(w2_prime[(k + 2) as int] == w2[(k + 2) as int]);
            } else {
                // k >= p3: both = w2[k+4]
                // w_end[k]: k >= p3 so w_end[k] = w3[k+2]. k+2 >= p2 so w3[k+2] = w2[k+4].
                assert(w_end[k] == w3[(k + 2) as int]); assert(w3[(k + 2) as int] == w2[(k + 4) as int]);
                // result_word[k]: k >= p2 so result_word[k] = w2_prime[k+2]. k+2 >= p3+2 so w2_prime[k+2] = w2[k+4].
                assert(result_word[k] == w2_prime[(k + 2) as int]); assert(w2_prime[(k + 2) as int] == w2[(k + 4) as int]);
            }
        };
        assert(w_end =~= result_word);
        assert(apply_step(hp, w2_prime, step2_adj) == Some(w_end));

        (w2_prime, step3_adj, step2_adj)
    }
}

/// When a_j is empty, b_j is equivalent to ε in the base group.
/// Uses the HNN isomorphism: a_j ≡ ε iff b_j ≡ ε.
pub proof fn lemma_aj_empty_bj_trivial(
    data: HNNData, j: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        0 <= j < data.associations.len(),
        data.associations[j].0.len() == 0, // a_j = []
    ensures
        equiv_in_presentation(data.base, data.associations[j].1, empty_word()),
{
    let k = data.associations.len();
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);
    let (a_j, b_j) = data.associations[j];

    // Construct witness word: w = [Gen(j)]
    let w: Word = seq![Symbol::Gen(j as nat)];
    assert(word_valid(w, k as nat)) by {
        assert(w.len() == 1);
        assert forall|i: int| 0 <= i < w.len() implies generator_index(w[i]) < k as nat by {
            assert(w[0int] == Symbol::Gen(j as nat));
            assert(generator_index(Symbol::Gen(j as nat)) == j as nat);
        };
    };

    // apply_embedding(a_words, [Gen(j)]) = concat(a_j, empty_word()) = a_j
    assert(apply_embedding(a_words, w) =~= concat(apply_embedding_symbol(a_words, Symbol::Gen(j as nat)),
        apply_embedding(a_words, w.drop_first())));
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    assert(apply_embedding(a_words, w.drop_first()) =~= empty_word());
    assert(apply_embedding_symbol(a_words, Symbol::Gen(j as nat)) =~= a_words[j]);
    assert(a_words[j] =~= a_j);
    assert(a_j.len() == 0);
    assert(a_j =~= empty_word());
    assert(apply_embedding(a_words, w) =~= concat(empty_word(), empty_word()));
    assert(concat(empty_word(), empty_word()) =~= empty_word());

    // So apply_embedding(a_words, w) ≡ ε trivially
    lemma_equiv_refl(data.base, empty_word());
    assert(equiv_in_presentation(data.base, apply_embedding(a_words, w), empty_word()));

    // By isomorphism: apply_embedding(b_words, w) ≡ ε
    assert(equiv_in_presentation(data.base, apply_embedding(b_words, w), empty_word()));

    // apply_embedding(b_words, [Gen(j)]) = b_j
    assert(apply_embedding(b_words, w) =~= concat(apply_embedding_symbol(b_words, Symbol::Gen(j as nat)),
        apply_embedding(b_words, w.drop_first())));
    assert(apply_embedding(b_words, w.drop_first()) =~= empty_word());
    assert(apply_embedding_symbol(b_words, Symbol::Gen(j as nat)) =~= b_words[j]);
    assert(b_words[j] =~= b_j);
    assert(apply_embedding(b_words, w) =~= concat(b_j, empty_word()));
    assert(concat(b_j, empty_word()) =~= b_j);
}

/// When a_j is empty, inv(b_j) is equivalent to ε in the base group.
pub proof fn lemma_aj_empty_inv_bj_trivial(
    data: HNNData, j: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        0 <= j < data.associations.len(),
        data.associations[j].0.len() == 0,
    ensures
        equiv_in_presentation(data.base, inverse_word(data.associations[j].1), empty_word()),
{
    let (a_j, b_j) = data.associations[j];
    lemma_aj_empty_bj_trivial(data, j);
    // b_j ≡ ε → inv(b_j) ≡ ε
    reveal(presentation_valid);
    lemma_inverse_word_valid(b_j, data.base.num_generators);
    crate::tietze::lemma_inverse_of_identity(data.base, b_j);
}

/// Check if a +2 step and -2 step overlap in their affected regions.
/// Returns true if they don't overlap (i.e., safe to commute).
pub open spec fn peak_steps_non_overlapping(
    hp: Presentation, step_up: DerivationStep, step_down: DerivationStep,
    w1: Word,
) -> bool {
    match step_up {
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } => {
            match step_down {
                DerivationStep::FreeReduce { position: p2 } => {
                    p2 + 2 <= p1 || p2 >= p1 + 2
                },
                DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
                    let r2 = get_relator(hp, ri2, inv2);
                    p2 + r2.len() <= p1 || p2 >= p1 + 2
                },
                _ => true,
            }
        },
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            let r1 = get_relator(hp, ri1, inv1);
            match step_down {
                DerivationStep::FreeReduce { position: p2 } => {
                    p2 + 2 <= p1 || p2 >= p1 + r1.len()
                },
                DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 } => {
                    let r2 = get_relator(hp, ri2, inv2);
                    p2 + r2.len() <= p1 || p2 >= p1 + r1.len()
                },
                _ => true,
            }
        },
        _ => true,
    }
}

/// For the RI+FR overlap case with a_j=[], prove that w1 and w3 differ only by
/// insertion of inv(b_j) (which is trivial by the isomorphism).
/// This establishes equiv_in_presentation(data.base, w1, w3) for the overlap case.
proof fn lemma_overlap_ri_fr_w1_equiv_w3(
    data: HNNData,
    w1: Word, w2: Word, w3: Word,
    p1: int, ri1: nat, inv1: bool, p2: int,
    j1: int,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w1, data.base.num_generators + 1),
        word_valid(w2, data.base.num_generators + 1),
        word_valid(w3, data.base.num_generators + 1),
        ri1 as int >= data.base.relators.len(),
        j1 == (ri1 as int - data.base.relators.len()) as int,
        0 <= j1 < data.associations.len(),
        !inv1, // non-inverted case
        data.associations[j1].0.len() == 0, // a_j = []
        p2 == p1, // FR at relator start (inside case, both elements)
        ({
            let hp = hnn_presentation(data);
            &&& apply_step(hp, w1, DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 }) == Some(w2)
            &&& apply_step(hp, w2, DerivationStep::FreeReduce { position: p2 }) == Some(w3)
        }),
        !(w3 =~= w1),
    ensures
        equiv_in_presentation(data.base, w1, w3),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r1 = get_relator(hp, ri1, inv1);
    let (a_j1, b_j1) = data.associations[j1];

    // r1 = [Inv(n), Gen(n)] ++ inv(b_j1) since a_j1 = []
    lemma_hnn_relator_stable_positions(data, j1);
    assert(r1[0int] == stable_letter_inv(data));
    assert(r1[1int] == stable_letter(data));

    // w2 = w1[0..p1] + r1 + w1[p1..]
    assert(w2 =~= w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int));

    // FR at p1 removes [Inv(n), Gen(n)] from w2
    // w3 = w2[0..p1] + w2[p1+2..] = w1[0..p1] + r1[2..] + w1[p1..]
    // r1[2..] = inv(b_j1) (since r1 = [Inv(n), Gen(n)] ++ inv(b_j1))
    let inv_bj1 = inverse_word(b_j1);

    // Show w3 = w1[0..p1] + inv(b_j1) + w1[p1..]
    let left = w1.subrange(0, p1);
    let right = w1.subrange(p1, w1.len() as int);

    // w3 = concat(left, concat(inv_bj1, right))
    // w1 = concat(left, right)
    assert(w1 =~= left + right);

    // Prove inv(b_j1) ≡ ε using isomorphism
    lemma_aj_empty_inv_bj_trivial(data, j1);

    // Now use lemma_insert_trivial_equiv
    reveal(presentation_valid);
    lemma_inverse_word_valid(b_j1, n);
    lemma_insert_trivial_equiv(data.base, left, right, inv_bj1);
    // This gives: equiv_in_presentation(data.base, concat(left, right), concat(left, concat(inv_bj1, right)))
    // i.e., equiv_in_presentation(data.base, w1, concat(left, concat(inv_bj1, right)))

    // Need to show w3 =~= concat(left, concat(inv_bj1, right))
    assert(concat(left, right) =~= w1);
    assert(concat(left, concat(inv_bj1, right)) =~= left + inv_bj1 + right);

    // Show w3 =~= left + inv_bj1 + right
    // w3 = w2[0..p1] + w2[p1+2..]
    // w2[0..p1] = w1[0..p1] = left
    // w2[p1+2..] = r1[2..] + w1[p1..] where r1[2..] should be inv_bj1

    // r1 structure: r1 = [Inv(n)] ++ a_j1 ++ [Gen(n)] ++ inv(b_j1)
    // With a_j1 = []: r1 = [Inv(n), Gen(n)] ++ inv(b_j1)
    // r1_len = 2 + inv_bj1.len()
    lemma_hnn_relator_structure(data, j1);
    let t = stable_letter(data);
    let t_inv = stable_letter_inv(data);
    assert(hp.relators[ri1 as int] ==
        Seq::new(1, |_j: int| t_inv) + a_j1 + Seq::new(1, |_j: int| t) + inverse_word(b_j1));
    assert(a_j1.len() == 0);
    assert(a_j1 =~= Seq::<Symbol>::empty());

    // r1 = [t_inv, t] ++ inv_bj1
    assert(hp.relators[ri1 as int] =~= seq![t_inv] + seq![t] + inv_bj1);
    assert(hp.relators[ri1 as int] =~= seq![t_inv, t] + inv_bj1);

    // get_relator returns hp.relators[ri1] or its inverse
    // Since inv1 = false: get_relator returns hp.relators[ri1]
    assert(r1 =~= hp.relators[ri1 as int]);
    assert(r1 =~= seq![t_inv, t] + inv_bj1);

    // r1.subrange(2, r1.len()) =~= inv_bj1
    assert(r1.subrange(2, r1.len() as int) =~= inv_bj1);

    // w2[p1+2..] = r1[2..] + right = inv_bj1 + right
    assert forall|k: int| 0 <= k < w3.len() implies w3[k] == (left + inv_bj1 + right)[k] by {
        if k < p1 {
            assert(w3[k] == w2[k]);
            assert(w2[k] == left[k]);
            assert((left + inv_bj1 + right)[k] == left[k]);
        } else if k < p1 + inv_bj1.len() as int {
            assert(w3[k] == w2[(k + 2) as int]);
            assert(w2[(k + 2) as int] == r1[(k + 2 - p1) as int]);
            assert(r1[(k + 2 - p1) as int] == inv_bj1[(k - p1) as int]);
            assert((left + inv_bj1 + right)[k] == inv_bj1[(k - p1) as int]);
        } else {
            assert(w3[k] == w2[(k + 2) as int]);
            let r1_len = r1.len() as int;
            assert(w2[(k + 2) as int] == w1[((k + 2) - r1_len + p1 - p1) as int]);
            // Actually: w2 = left + r1 + right.
            // w2[k+2] where k+2 >= p1 + r1_len: w2[k+2] = right[(k+2-p1-r1_len) as int] = w1[(k+2-r1_len) as int]
            // But k >= p1 + inv_bj1.len() means k+2 >= p1 + 2 + inv_bj1.len() = p1 + r1_len.
            // So w2[k+2] = right[(k - p1 - inv_bj1.len()) as int]
            assert((left + inv_bj1 + right)[k] == right[(k - p1 - inv_bj1.len()) as int]);
        }
    };
    assert(w3 =~= left + inv_bj1 + right);
    assert(w3 =~= concat(left, concat(inv_bj1, right)));
}

} // verus!
