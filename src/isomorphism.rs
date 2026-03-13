use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::homomorphism::*;

verus! {

/// A word is in the kernel of h if its image is equivalent to ε.
pub open spec fn in_kernel(h: HomomorphismData, w: Word) -> bool {
    equiv_in_presentation(h.target, apply_hom(h, w), empty_word())
}

// --- Lemmas ---

/// The identity word is in the kernel.
pub proof fn lemma_kernel_contains_identity(h: HomomorphismData)
    ensures
        in_kernel(h, empty_word()),
{
    lemma_hom_empty(h);
    assert(apply_hom(h, empty_word()) =~= empty_word());
    lemma_equiv_refl(h.target, empty_word());
}

/// Kernel is closed under equivalence in the source presentation.
pub proof fn lemma_kernel_closed_under_equiv(h: HomomorphismData, w1: Word, w2: Word)
    requires
        is_valid_homomorphism(h),
        equiv_in_presentation(h.source, w1, w2),
        in_kernel(h, w1),
    ensures
        in_kernel(h, w2),
{
    // hom(w1) ≡ hom(w2) in target (hom preserves equiv)
    lemma_hom_preserves_equiv(h, w1, w2);
    // hom(w1) ≡ ε (w1 in kernel)
    // So hom(w2) ≡ hom(w1) ≡ ε
    lemma_equiv_symmetric(h.target, apply_hom(h, w1), apply_hom(h, w2));
    lemma_equiv_transitive(h.target, apply_hom(h, w2), apply_hom(h, w1), empty_word());
}

/// Kernel is closed under concatenation.
pub proof fn lemma_kernel_closed_under_concat(h: HomomorphismData, w1: Word, w2: Word)
    requires
        in_kernel(h, w1),
        in_kernel(h, w2),
    ensures
        in_kernel(h, concat(w1, w2)),
{
    // hom(w1·w2) =~= hom(w1)·hom(w2)
    lemma_hom_respects_concat(h, w1, w2);
    // hom(w1) ≡ ε, hom(w2) ≡ ε
    // So hom(w1)·hom(w2) ≡ ε·ε = ε
    lemma_equiv_concat(h.target,
        apply_hom(h, w1), empty_word(),
        apply_hom(h, w2), empty_word(),
    );
    assert(concat(empty_word(), empty_word()) =~= empty_word());
    lemma_equiv_refl(h.target, empty_word());
    lemma_equiv_transitive(h.target,
        concat(apply_hom(h, w1), apply_hom(h, w2)),
        concat(empty_word(), empty_word()),
        empty_word(),
    );
    // apply_hom(concat) =~= concat(apply_hom, apply_hom)
    // So in_kernel(concat)
}

/// Kernel is closed under word inverse.
pub proof fn lemma_kernel_closed_under_inverse(h: HomomorphismData, w: Word)
    requires
        in_kernel(h, w),
    ensures
        in_kernel(h, inverse_word(w)),
{
    // hom(w⁻¹) =~= hom(w)⁻¹
    lemma_hom_respects_inverse(h, w);
    // hom(w) ≡ ε, so hom(w)⁻¹ ≡ ε⁻¹ = ε
    // Need: equiv(hom(w)⁻¹, ε)

    // ε⁻¹ = ε
    lemma_inverse_empty();

    // hom(w) ≡ ε → hom(w)⁻¹ ≡ ε⁻¹ = ε
    // Use: hom(w)⁻¹ · hom(w) ≡ ε (left inverse)
    lemma_word_inverse_left(h.target, apply_hom(h, w));
    // inverse_word(hom(w)) · hom(w) ≡ ε

    // hom(w) ≡ ε, so inverse_word(hom(w)) · hom(w) ≡ inverse_word(hom(w)) · ε = inverse_word(hom(w))
    lemma_equiv_concat_right(h.target,
        inverse_word(apply_hom(h, w)),
        apply_hom(h, w),
        empty_word(),
    );
    assert(concat(inverse_word(apply_hom(h, w)), empty_word()) =~= inverse_word(apply_hom(h, w)));
    lemma_equiv_refl(h.target, inverse_word(apply_hom(h, w)));

    // inverse_word(hom(w)) ≡ concat(inverse_word(hom(w)), hom(w)) ≡ ε
    lemma_equiv_symmetric(h.target,
        concat(inverse_word(apply_hom(h, w)), apply_hom(h, w)),
        concat(inverse_word(apply_hom(h, w)), empty_word()),
    );
    lemma_equiv_transitive(h.target,
        inverse_word(apply_hom(h, w)),
        concat(inverse_word(apply_hom(h, w)), apply_hom(h, w)),
        empty_word(),
    );

    // apply_hom(inverse_word(w)) =~= inverse_word(apply_hom(w))
    // So in_kernel(inverse_word(w))
}

/// **First isomorphism theorem (kernel direction)**:
/// If hom(w1) ≡ hom(w2) in target, then w1·w2⁻¹ is in the kernel.
pub proof fn lemma_hom_injective_mod_kernel(h: HomomorphismData, w1: Word, w2: Word)
    requires
        is_valid_homomorphism(h),
        equiv_in_presentation(h.target, apply_hom(h, w1), apply_hom(h, w2)),
    ensures
        in_kernel(h, concat(w1, inverse_word(w2))),
{
    // hom(w1 · w2⁻¹) =~= hom(w1) · hom(w2⁻¹) =~= hom(w1) · hom(w2)⁻¹
    lemma_hom_respects_concat(h, w1, inverse_word(w2));
    lemma_hom_respects_inverse(h, w2);

    // hom(w1) ≡ hom(w2), so hom(w1) · hom(w2)⁻¹ ≡ hom(w2) · hom(w2)⁻¹ ≡ ε
    lemma_equiv_concat_left(h.target,
        apply_hom(h, w1),
        apply_hom(h, w2),
        inverse_word(apply_hom(h, w2)),
    );
    lemma_word_inverse_right(h.target, apply_hom(h, w2));
    lemma_equiv_transitive(h.target,
        concat(apply_hom(h, w1), inverse_word(apply_hom(h, w2))),
        concat(apply_hom(h, w2), inverse_word(apply_hom(h, w2))),
        empty_word(),
    );

    // connect: apply_hom(w1 · w2⁻¹) =~= hom(w1) · hom(w2)⁻¹
    // =~= hom(w1) · inverse_word(hom(w2))
    // We have: apply_hom(concat(w1, inv(w2))) =~= concat(hom(w1), hom(inv(w2)))
    //                                         =~= concat(hom(w1), inv(hom(w2)))
}

} // verus!
