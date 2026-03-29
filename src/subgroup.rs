use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::isomorphism::*;
use crate::homomorphism::*;

verus! {

//  ============================================================
//  Subgroup and Normal Subgroup Predicates
//  ============================================================

///  A set of words forms a subgroup of the group presented by `p`.
pub open spec fn is_subgroup_set(p: Presentation, in_set: spec_fn(Word) -> bool) -> bool {
    //  Contains identity
    &&& in_set(empty_word())
    //  Closed under concatenation (group multiplication)
    &&& (forall|w1: Word, w2: Word| in_set(w1) && in_set(w2) ==> in_set(concat(w1, w2)))
    //  Closed under inverse
    &&& (forall|w: Word| in_set(w) ==> in_set(inverse_word(w)))
    //  Well-defined: closed under equivalence
    &&& (forall|w1: Word, w2: Word| in_set(w1) && equiv_in_presentation(p, w1, w2)
        ==> in_set(w2))
}

///  A normal subgroup: a subgroup closed under conjugation by word_valid elements.
///  Restricting g to word_valid is mathematically natural — in a presented group,
///  only word_valid words represent group elements.
pub open spec fn is_normal_subgroup_set(p: Presentation, in_set: spec_fn(Word) -> bool) -> bool {
    &&& is_subgroup_set(p, in_set)
    &&& (forall|w: Word, g: Word| in_set(w) && word_valid(g, p.num_generators)
        ==> in_set(concat(concat(g, w), inverse_word(g))))
}

//  ============================================================
//  Helpers
//  ============================================================

///  concat preserves word_valid.
proof fn lemma_concat_word_valid(w1: Word, w2: Word, n: nat)
    requires word_valid(w1, n), word_valid(w2, n),
    ensures word_valid(concat(w1, w2), n),
{
    assert forall|k: int| 0 <= k < concat(w1, w2).len()
        implies symbol_valid(concat(w1, w2)[k], n)
    by {
        if k < w1.len() { assert(concat(w1, w2)[k] == w1[k]); }
        else { assert(concat(w1, w2)[k] == w2[k - w1.len()]); }
    }
}

///  A derivation preserves word_valid (induction on steps).
proof fn lemma_derivation_preserves_word_valid(
    p: Presentation, steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(p, steps, w1) == Some(w2),
        word_valid(w1, p.num_generators),
        presentation_valid(p),
    ensures
        word_valid(w2, p.num_generators),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let next = apply_step(p, w1, steps.first()).unwrap();
        lemma_step_preserves_word_valid_pres(p, w1, steps.first(), next);
        lemma_derivation_preserves_word_valid(p, steps.drop_first(), next, w2);
    }
}

///  equiv_in_presentation preserves word_valid.
pub proof fn lemma_equiv_preserves_word_valid(p: Presentation, w1: Word, w2: Word)
    requires
        equiv_in_presentation(p, w1, w2),
        word_valid(w1, p.num_generators),
        presentation_valid(p),
    ensures
        word_valid(w2, p.num_generators),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    lemma_derivation_preserves_word_valid(p, d.steps, w1, w2);
}

//  ============================================================
//  Lemmas
//  ============================================================

///  The trivial subgroup: word_valid words equivalent to ε.
pub proof fn lemma_trivial_subgroup(p: Presentation)
    requires
        presentation_valid(p),
    ensures
        is_subgroup_set(p,
            |w: Word| word_valid(w, p.num_generators)
                && equiv_in_presentation(p, w, empty_word())),
{
    let n = p.num_generators;
    let in_set = |w: Word| word_valid(w, n)
        && equiv_in_presentation(p, w, empty_word());

    //  Identity: word_valid(ε) ∧ ε ≡ ε
    lemma_equiv_refl(p, empty_word());

    //  Concat
    assert forall|w1: Word, w2: Word| in_set(w1) && in_set(w2)
        implies in_set(concat(w1, w2)) by {
        lemma_concat_word_valid(w1, w2, n);
        lemma_equiv_concat(p, w1, empty_word(), w2, empty_word());
        assert(concat(empty_word(), empty_word()) =~= empty_word());
        lemma_equiv_refl(p, empty_word());
        lemma_equiv_transitive(p,
            concat(w1, w2),
            concat(empty_word(), empty_word()),
            empty_word(),
        );
    }

    //  Inverse
    assert forall|w: Word| in_set(w) implies in_set(inverse_word(w)) by {
        crate::word::lemma_inverse_word_valid(w, n);
        //  Get ε ≡ w from symmetry (needs word_valid(w) ✓)
        lemma_equiv_symmetric(p, w, empty_word());
        //  concat(ε, inv(w)) ≡ concat(w, inv(w))
        lemma_equiv_concat_left(p, empty_word(), w, inverse_word(w));
        assert(concat(empty_word(), inverse_word(w)) =~= inverse_word(w));
        //  concat(w, inv(w)) ≡ ε
        lemma_word_inverse_right(p, w);
        //  inv(w) ≡ concat(w, inv(w)) ≡ ε
        lemma_equiv_transitive(p,
            inverse_word(w),
            concat(w, inverse_word(w)),
            empty_word(),
        );
    }

    //  Equiv closure
    assert forall|w1: Word, w2: Word| in_set(w1) && equiv_in_presentation(p, w1, w2)
        implies in_set(w2) by {
        //  word_valid(w2) from derivation preservation
        lemma_equiv_preserves_word_valid(p, w1, w2);
        //  equiv(w2, w1) from symmetry (needs word_valid(w1) ✓)
        lemma_equiv_symmetric(p, w1, w2);
        //  equiv(w2, ε) from transitivity
        lemma_equiv_transitive(p, w2, w1, empty_word());
    }
}

///  The whole group is a subgroup.
pub proof fn lemma_whole_group_subgroup(p: Presentation)
    ensures
        is_subgroup_set(p, |_w: Word| true),
{
}

///  The kernel of a valid homomorphism is a normal subgroup.
pub proof fn lemma_kernel_is_normal_subgroup(h: HomomorphismData)
    requires
        is_valid_homomorphism(h),
        presentation_valid(h.source),
        presentation_valid(h.target),
    ensures
        is_normal_subgroup_set(h.source,
            |w: Word| word_valid(w, h.source.num_generators) && in_kernel(h, w)),
{
    let p = h.source;
    let n = p.num_generators;
    let in_set = |w: Word| word_valid(w, n) && in_kernel(h, w);

    //  Identity
    lemma_kernel_contains_identity(h);

    //  Concat
    assert forall|w1: Word, w2: Word| in_set(w1) && in_set(w2)
        implies in_set(concat(w1, w2)) by {
        lemma_concat_word_valid(w1, w2, n);
        lemma_kernel_closed_under_concat(h, w1, w2);
    }

    //  Inverse
    assert forall|w: Word| in_set(w) implies in_set(inverse_word(w)) by {
        crate::word::lemma_inverse_word_valid(w, n);
        lemma_kernel_closed_under_inverse(h, w);
    }

    //  Equiv closure
    assert forall|w1: Word, w2: Word| in_set(w1) && equiv_in_presentation(p, w1, w2)
        implies in_set(w2) by {
        lemma_equiv_preserves_word_valid(p, w1, w2);
        lemma_kernel_closed_under_equiv(h, w1, w2);
    }

    //  Normal: conjugation by word_valid elements
    assert forall|w: Word, g: Word| in_set(w) && word_valid(g, n)
        implies in_set(concat(concat(g, w), inverse_word(g))) by {
        //  word_valid(g·w·g⁻¹)
        crate::word::lemma_inverse_word_valid(g, n);
        lemma_concat_word_valid(g, w, n);
        lemma_concat_word_valid(concat(g, w), inverse_word(g), n);

        //  in_kernel: hom(g·w·g⁻¹) ≡ ε
        let hg = apply_hom(h, g);
        let hw = apply_hom(h, w);
        let inv_g = inverse_word(g);
        let gw = concat(g, w);

        //  Step 1: apply_hom(gw·inv_g) =~= concat(apply_hom(gw), apply_hom(inv_g))
        lemma_hom_respects_concat(h, gw, inv_g);
        //  Step 2: apply_hom(gw) =~= concat(hg, hw)
        lemma_hom_respects_concat(h, g, w);
        //  Step 3: apply_hom(inv_g) =~= inverse_word(hg)
        lemma_hom_respects_inverse(h, g);

        //  So: apply_hom(gw·inv_g) =~= concat(concat(hg, hw), inverse_word(hg))
        assert(apply_hom(h, concat(gw, inv_g))
            =~= concat(concat(hg, hw), inverse_word(hg)));

        //  hw ≡ ε (in_kernel), so concat(hg, hw) ≡ concat(hg, ε) =~= hg
        lemma_equiv_concat_right(h.target, hg, hw, empty_word());
        assert(concat(hg, empty_word()) =~= hg);
        lemma_equiv_refl(h.target, hg);
        lemma_equiv_transitive(h.target,
            concat(hg, hw), concat(hg, empty_word()), hg);

        //  concat(concat(hg, hw), inv(hg)) ≡ concat(hg, inv(hg))
        lemma_equiv_concat_left(h.target,
            concat(hg, hw), hg, inverse_word(hg));

        //  concat(hg, inv(hg)) ≡ ε
        lemma_word_inverse_right(h.target, hg);

        //  Chain: concat(concat(hg, hw), inv(hg)) ≡ concat(hg, inv(hg)) ≡ ε
        lemma_equiv_transitive(h.target,
            concat(concat(hg, hw), inverse_word(hg)),
            concat(hg, inverse_word(hg)),
            empty_word(),
        );
    }
}

///  Every normal subgroup is a subgroup.
pub proof fn lemma_normal_subgroup_is_subgroup(p: Presentation, in_set: spec_fn(Word) -> bool)
    requires
        is_normal_subgroup_set(p, in_set),
    ensures
        is_subgroup_set(p, in_set),
{
}

} //  verus!
