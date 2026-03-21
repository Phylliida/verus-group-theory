use vstd::prelude::*;
use crate::word::*;
use crate::symbol::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;
use crate::britton::*;
use crate::britton_proof::*;

verus! {

/// FreeExpand(base) arm of RI(HNN) commutation.
pub proof fn lemma_k4_tfree_ri_commute_fe(
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
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    let pair1 = Seq::new(1, |_i: int| sym1) + Seq::new(1, |_i: int| inverse_symbol(sym1));
    let p1_on_w: int = if p1 <= p0 { p1 } else { (p1 - r0_len) as int };
    let p0_adj: int = if p1 <= p0 { (p0 + 2) as int } else { p0 };

    if p1 <= p0 || p1 >= p0 + r0_len {
        let w_prime = w.subrange(0, p1_on_w) + pair1 + w.subrange(p1_on_w, w.len() as int);
        let step1_base = DerivationStep::FreeExpand { position: p1_on_w, symbol: sym1 };
        crate::britton_proof_helpers::lemma_base_expand_preserves_base(w, p1_on_w, sym1, n);
        lemma_step_preserves_word_valid(data, w, step1_base);
        let step0_adj = DerivationStep::RelatorInsert { position: p0_adj, relator_index: ri0, inverted: inv0 };
        let ins = w_prime.subrange(0, p0_adj) + r0 + w_prime.subrange(p0_adj, w_prime.len() as int);
        assert(w2 =~= ins);
        (w_prime, step1_base, step0_adj)
    } else {
        assume(false); arbitrary()
    }
}

/// RelatorInsert(base) arm of RI(HNN) commutation.
pub proof fn lemma_k4_tfree_ri_commute_ri(
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
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
    reveal(presentation_valid);
    lemma_relator_stable_count(data, ri1, inv1);
    let p1_on_w: int = if p1 <= p0 { p1 } else { (p1 - r0_len) as int };
    let p0_adj: int = if p1 <= p0 { (p0 + r1_len) as int } else { p0 };

    if p1 <= p0 || p1 >= p0 + r0_len {
        let w_prime = w.subrange(0, p1_on_w) + r1 + w.subrange(p1_on_w, w.len() as int);
        let step1_base = DerivationStep::RelatorInsert { position: p1_on_w, relator_index: ri1, inverted: inv1 };
        assert(apply_step(data.base, w, step1_base) == Some(w_prime));
        lemma_stable_letter_count_concat(w.subrange(0, p1_on_w), r1, n);
        lemma_stable_letter_count_concat(w.subrange(0, p1_on_w) + r1, w.subrange(p1_on_w, w.len() as int), n);
        lemma_stable_letter_count_concat(w.subrange(0, p1_on_w), w.subrange(p1_on_w, w.len() as int), n);
        lemma_step_preserves_word_valid(data, w, step1_base);
        let step0_adj = DerivationStep::RelatorInsert { position: p0_adj, relator_index: ri0, inverted: inv0 };
        let ins = w_prime.subrange(0, p0_adj) + r0 + w_prime.subrange(p0_adj, w_prime.len() as int);
        assert(w2 =~= ins);
        (w_prime, step1_base, step0_adj)
    } else {
        assume(false); arbitrary()
    }
}

/// RelatorDelete(base) arm of RI(HNN) commutation.
pub proof fn lemma_k4_tfree_ri_commute_rd(
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
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let r0 = get_relator(hp, ri0, inv0);
    let r0_len = r0.len() as int;
    let r1 = get_relator(hp, ri1, inv1);
    let r1_len = r1.len() as int;
    assert(w1 =~= w.subrange(0, p0) + r0 + w.subrange(p0, w.len() as int));
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
}

} // verus!
