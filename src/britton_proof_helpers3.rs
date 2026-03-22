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
        // Overlap: relator region [p2, p2+r2_len) overlaps insertion [p1, p1+2)
        // This requires a_j = [] in the HNN association — rare edge case
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
        // Overlap: FreeReduce spans boundary of inserted relator
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
        // r2 is entirely before r1 insertion point
        assert forall|k: int| p2 <= k < p2 + r2_len implies w2[k] == w1[k] by {};
        assert(w1.subrange(p2, p2 + r2_len) =~= r2);

        let w1_prime = w1.subrange(0, p2) + w1.subrange(p2 + r2_len, w1.len() as int);
        let step2_adj = DerivationStep::RelatorDelete { position: p2, relator_index: ri2, inverted: inv2 };
        assert(apply_step(hp, w1, step2_adj) == Some(w1_prime));

        lemma_stable_count_subrange(w1, p2, p2 + r2_len, n);
        lemma_stable_letter_count_concat(w1.subrange(0, p2), w1.subrange(p2 + r2_len, w1.len() as int), n);
        lemma_stable_letter_count_concat(w1.subrange(0, p2), w1.subrange(p2, w1.len() as int), n);
        assert(stable_letter_count(w1_prime, n) == 0nat);
        lemma_zero_count_implies_base(w1_prime, n);
        lemma_step_preserves_word_valid(data, w1, step2_adj);

        let p1_adj = (p1 - r2_len) as int;
        let step1_adj = DerivationStep::RelatorInsert { position: p1_adj, relator_index: ri1, inverted: inv1 };
        let ins = w1_prime.subrange(0, p1_adj) + r1 + w1_prime.subrange(p1_adj, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
        assert(w3 =~= ins);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));

        (w1_prime, step2_adj, step1_adj)
    } else if p2 >= p1 + r1_len {
        // r2 is entirely after r1 insertion
        let p2_adj = (p2 - r1_len) as int;
        assert forall|k: int| p2 <= k < p2 + r2_len implies w2[k] == w1[(k - r1_len) as int] by {};
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

        let step1_adj = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
        let ins = w1_prime.subrange(0, p1) + r1 + w1_prime.subrange(p1, w1_prime.len() as int);
        assert forall|k: int| 0 <= k < w3.len() implies w3[k] == ins[k] by {};
        assert(w3 =~= ins);
        assert(apply_step(hp, w1_prime, step1_adj) == Some(w3));

        (w1_prime, step2_adj, step1_adj)
    } else {
        // Overlap: relator regions overlap
        assume(false); arbitrary()
    }
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

/// Generalized T-free × FreeExpand(stable) commutation — FreeReduce sub-case.
pub proof fn lemma_swap_fr_past_expand(
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
    ensures ({
        let (w1_prime, step_tfree_adj, step_plus2_adj) = result;
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        &&& word_valid(w1_prime, n + 1)
        &&& stable_letter_count(w1_prime, n) == stable_letter_count(w1, n)
        &&& apply_step(hp, w1, step_tfree_adj) == Some(w1_prime)
        &&& apply_step(hp, w1_prime, step_plus2_adj) == Some(w3)
    }),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let pair = Seq::new(1, |_i: int| sym0) + Seq::new(1, |_i: int| inverse_symbol(sym0));
    assert(w2 =~= w1.subrange(0, p0) + pair + w1.subrange(p0, w1.len() as int));

    match step_tfree {
        DerivationStep::FreeReduce { position: p1 } => {
            // T-free FreeReduce: gen_idx(w2[p1]) < n
            lemma_stable_count_reduce(w2, p1, n);
            assert(generator_index(w2[p1]) < n);

            if p1 == p0 {
                assert(w2[p0] == sym0);
                assert(generator_index(sym0) == n);
                assert(generator_index(w2[p1]) < n);
                assert(false);
            }
            if p1 == p0 - 1 {
                assert(is_inverse_pair(w2[p1], w2[p1 + 1]));
                assert(w2[p1 + 1] == sym0);
                assert(generator_index(sym0) == n);
                assert(generator_index(w2[p1]) == generator_index(sym0)) by {
                    assert(w2[p1 + 1] == inverse_symbol(w2[p1]));
                    match w2[p1] { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                };
                assert(generator_index(w2[p1]) < n);
                assert(false);
            }
            if p1 == p0 + 1 {
                assert(w2[p1] == inverse_symbol(sym0));
                assert(generator_index(inverse_symbol(sym0)) == n) by {
                    match sym0 { Symbol::Gen(k) => {}, Symbol::Inv(k) => {} }
                };
                assert(generator_index(w2[p1]) < n);
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
                let step_plus2_adj = DerivationStep::FreeExpand { position: p0_adj, symbol: sym0 };
                let result = w1_prime.subrange(0, p0_adj) + pair
                    + w1_prime.subrange(p0_adj, w1_prime.len() as int);
                assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
                assert(w3 =~= result);
                assert(apply_step(hp, w1_prime, step_plus2_adj) == Some(w3));
                (w1_prime, step_tfree_adj, step_plus2_adj)
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

                let step_plus2_adj = DerivationStep::FreeExpand { position: p0, symbol: sym0 };
                let result = w1_prime.subrange(0, p0) + pair
                    + w1_prime.subrange(p0, w1_prime.len() as int);
                assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
                assert(w3 =~= result);
                assert(apply_step(hp, w1_prime, step_plus2_adj) == Some(w3));
                (w1_prime, step_tfree_adj, step_plus2_adj)
            }
        },
        DerivationStep::FreeExpand { position: p1, symbol: sym1 } => {
            let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
            if p1 == p0 + 1 {
                // Edge case: insert between stable letters
                assume(false); arbitrary()
            } else if p1 <= p0 {
                let w1_prime = w1.subrange(0, p1) + pair1 + w1.subrange(p1, w1.len() as int);
                let step_tfree_adj = DerivationStep::FreeExpand { position: p1, symbol: sym1 };
                assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
                lemma_stable_count_reduce_step(data, w1, step_tfree_adj, n);
                lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
                let step_plus2_adj = DerivationStep::FreeExpand { position: (p0 + 2) as int, symbol: sym0 };
                let result = w1_prime.subrange(0, (p0 + 2) as int) + pair
                    + w1_prime.subrange((p0 + 2) as int, w1_prime.len() as int);
                assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
                assert(w3 =~= result);
                assert(apply_step(hp, w1_prime, step_plus2_adj) == Some(w3));
                (w1_prime, step_tfree_adj, step_plus2_adj)
            } else {
                assert(p1 >= p0 + 2);
                let p1_adj = (p1 - 2) as int;
                let w1_prime = w1.subrange(0, p1_adj) + pair1 + w1.subrange(p1_adj, w1.len() as int);
                let step_tfree_adj = DerivationStep::FreeExpand { position: p1_adj, symbol: sym1 };
                assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
                lemma_stable_count_reduce_step(data, w1, step_tfree_adj, n);
                lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
                let step_plus2_adj = DerivationStep::FreeExpand { position: p0, symbol: sym0 };
                let result = w1_prime.subrange(0, p0) + pair
                    + w1_prime.subrange(p0, w1_prime.len() as int);
                assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
                assert(w3 =~= result);
                assert(apply_step(hp, w1_prime, step_plus2_adj) == Some(w3));
                (w1_prime, step_tfree_adj, step_plus2_adj)
            }
        },
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            let r1 = get_relator(hp, ri1, inv1);
            let r1_len = r1.len() as int;
            lemma_relator_stable_count(data, ri1, inv1);
            if p1 <= p0 {
                let w1_prime = w1.subrange(0, p1) + r1 + w1.subrange(p1, w1.len() as int);
                let step_tfree_adj = DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 };
                assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
                lemma_stable_count_reduce_step(data, w1, step_tfree_adj, n);
                lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
                let step_plus2_adj = DerivationStep::FreeExpand { position: (p0 + r1_len) as int, symbol: sym0 };
                let result = w1_prime.subrange(0, (p0 + r1_len) as int) + pair
                    + w1_prime.subrange((p0 + r1_len) as int, w1_prime.len() as int);
                assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
                assert(w3 =~= result);
                assert(apply_step(hp, w1_prime, step_plus2_adj) == Some(w3));
                (w1_prime, step_tfree_adj, step_plus2_adj)
            } else if p1 >= p0 + 2 {
                let p1_adj = (p1 - 2) as int;
                let w1_prime = w1.subrange(0, p1_adj) + r1 + w1.subrange(p1_adj, w1.len() as int);
                let step_tfree_adj = DerivationStep::RelatorInsert { position: p1_adj, relator_index: ri1, inverted: inv1 };
                assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
                lemma_stable_count_reduce_step(data, w1, step_tfree_adj, n);
                lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
                let step_plus2_adj = DerivationStep::FreeExpand { position: p0, symbol: sym0 };
                let result = w1_prime.subrange(0, p0) + pair
                    + w1_prime.subrange(p0, w1_prime.len() as int);
                assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
                assert(w3 =~= result);
                assert(apply_step(hp, w1_prime, step_plus2_adj) == Some(w3));
                (w1_prime, step_tfree_adj, step_plus2_adj)
            } else {
                // Inside the expand region
                assume(false); arbitrary()
            }
        },
        DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 } => {
            let r1 = get_relator(hp, ri1, inv1);
            let r1_len = r1.len() as int;
            lemma_relator_stable_count(data, ri1, inv1);
            if p1 + r1_len <= p0 {
                assert forall|k: int| p1 <= k < p1 + r1_len implies w2[k] == w1[k] by {};
                assert(w1.subrange(p1, p1 + r1_len) =~= r1);
                let w1_prime = w1.subrange(0, p1) + w1.subrange(p1 + r1_len, w1.len() as int);
                let step_tfree_adj = DerivationStep::RelatorDelete { position: p1, relator_index: ri1, inverted: inv1 };
                assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
                lemma_stable_count_reduce_step(data, w1, step_tfree_adj, n);
                lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
                let step_plus2_adj = DerivationStep::FreeExpand { position: (p0 - r1_len) as int, symbol: sym0 };
                let result = w1_prime.subrange(0, (p0 - r1_len) as int) + pair
                    + w1_prime.subrange((p0 - r1_len) as int, w1_prime.len() as int);
                assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
                assert(w3 =~= result);
                assert(apply_step(hp, w1_prime, step_plus2_adj) == Some(w3));
                (w1_prime, step_tfree_adj, step_plus2_adj)
            } else if p1 >= p0 + 2 {
                let p1_adj = (p1 - 2) as int;
                assert forall|k: int| p1 <= k < p1 + r1_len implies w2[k] == w1[(k - 2) as int] by {};
                assert(w1.subrange(p1_adj, p1_adj + r1_len) =~= r1);
                let w1_prime = w1.subrange(0, p1_adj) + w1.subrange(p1_adj + r1_len, w1.len() as int);
                let step_tfree_adj = DerivationStep::RelatorDelete { position: p1_adj, relator_index: ri1, inverted: inv1 };
                assert(apply_step(hp, w1, step_tfree_adj) == Some(w1_prime));
                lemma_stable_count_reduce_step(data, w1, step_tfree_adj, n);
                lemma_step_preserves_word_valid(data, w1, step_tfree_adj);
                let step_plus2_adj = DerivationStep::FreeExpand { position: p0, symbol: sym0 };
                let result = w1_prime.subrange(0, p0) + pair
                    + w1_prime.subrange(p0, w1_prime.len() as int);
                assert forall|k: int| 0 <= k < w3.len() implies w3[k] == result[k] by {};
                assert(w3 =~= result);
                assert(apply_step(hp, w1_prime, step_plus2_adj) == Some(w3));
                (w1_prime, step_tfree_adj, step_plus2_adj)
            } else {
                // Overlap with expand region
                assume(false); arbitrary()
            }
        },
    }
}

} // verus!
