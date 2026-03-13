use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;

verus! {

// ============================================================
// Equivalence respects group operations
// ============================================================

/// If w1 ≡ w1' then w1·w2 ≡ w1'·w2.
///
/// Proof idea: apply the same derivation steps to the left part,
/// with positions unchanged (the right part w2 is just carried along).
pub proof fn lemma_equiv_concat_left(p: Presentation, w1: Word, w1_prime: Word, w2: Word)
    requires
        equiv_in_presentation(p, w1, w1_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1_prime, w2)),
{
    admit(); // TODO: lift derivation through concatenation
}

/// If w2 ≡ w2' then w1·w2 ≡ w1·w2'.
pub proof fn lemma_equiv_concat_right(p: Presentation, w1: Word, w2: Word, w2_prime: Word)
    requires
        equiv_in_presentation(p, w2, w2_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1, w2_prime)),
{
    admit(); // TODO: lift derivation with offset positions
}

/// Equivalence respects concatenation on both sides.
pub proof fn lemma_equiv_concat(
    p: Presentation, w1: Word, w1_prime: Word, w2: Word, w2_prime: Word,
)
    requires
        equiv_in_presentation(p, w1, w1_prime),
        equiv_in_presentation(p, w2, w2_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1_prime, w2_prime)),
{
    lemma_equiv_concat_left(p, w1, w1_prime, w2);
    lemma_equiv_concat_right(p, w1_prime, w2, w2_prime);
    lemma_equiv_transitive(p, concat(w1, w2), concat(w1_prime, w2), concat(w1_prime, w2_prime));
}

// ============================================================
// Identity and inverses
// ============================================================

/// The empty word is the identity: w·ε ≡ w.
pub proof fn lemma_concat_identity_right(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(w, empty_word()), w),
{
    assert(concat(w, empty_word()) =~= w);
    lemma_equiv_refl(p, w);
}

/// ε·w ≡ w.
pub proof fn lemma_concat_identity_left(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(empty_word(), w), w),
{
    assert(concat(empty_word(), w) =~= w);
    lemma_equiv_refl(p, w);
}

/// w · w⁻¹ ≡ ε (right inverse).
///
/// Proof: reduce the adjacent inverse pairs one by one from inside out.
pub proof fn lemma_word_inverse_right(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(w, inverse_word(w)), empty_word()),
    decreases w.len(),
{
    admit(); // TODO: induction on word length, reducing inner pairs
}

/// w⁻¹ · w ≡ ε (left inverse).
pub proof fn lemma_word_inverse_left(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(inverse_word(w), w), empty_word()),
    decreases w.len(),
{
    admit(); // TODO: similar to right inverse
}

// ============================================================
// Relators
// ============================================================

/// Each relator is equivalent to the identity.
pub proof fn lemma_relator_is_identity(p: Presentation, i: int)
    requires
        0 <= i < p.relators.len(),
    ensures
        equiv_in_presentation(p, p.relators[i], empty_word()),
{
    let r = p.relators[i];
    let step = DerivationStep::RelatorDelete {
        position: 0,
        relator_index: i as nat,
        inverted: false,
    };
    // get_relator(p, i as nat, false) == p.relators[i] == r
    // apply_step checks: r.subrange(0, 0+r.len()) == r, which is trivially true
    assert(r.subrange(0, r.len() as int) =~= r);
    assert(get_relator(p, i as nat, false) == r);
    // After deletion: r.subrange(0, 0) + r.subrange(r.len(), r.len()) == empty
    assert(r.subrange(0, 0int) + r.subrange(r.len() as int, r.len() as int) =~= empty_word());
    assert(apply_step(p, r, step) == Some(empty_word()));
    let d = Derivation { steps: Seq::new(1, |_j: int| step) };
    assert(derivation_produces(p, d.steps, r) == Some(empty_word())) by {
        assert(d.steps.first() == step);
        assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    };
    assert(derivation_valid(p, d, r, empty_word()));
}

/// Conjugation: if r is a relator, then w·r·w⁻¹ ≡ ε.
pub proof fn lemma_conjugate_relator_is_identity(p: Presentation, w: Word, i: int)
    requires
        0 <= i < p.relators.len(),
    ensures
        equiv_in_presentation(
            p,
            concat(concat(w, p.relators[i]), inverse_word(w)),
            empty_word(),
        ),
{
    // w · r · w⁻¹ ≡ w · ε · w⁻¹ = w · w⁻¹ ≡ ε
    lemma_relator_is_identity(p, i);
    lemma_equiv_concat_left(p, p.relators[i], empty_word(), inverse_word(w));
    // concat(r, w⁻¹) ≡ concat(ε, w⁻¹) = w⁻¹
    lemma_equiv_concat_left(p, concat(p.relators[i], inverse_word(w)), concat(empty_word(), inverse_word(w)), w);
    // Need: w · (r · w⁻¹) ≡ w · w⁻¹ ≡ ε
    admit(); // TODO: chain the equivalences properly
}

// ============================================================
// The presented group is indeed a group
// ============================================================

/// Summary: the quotient Free(S)/⟨⟨R⟩⟩ satisfies the group axioms:
/// - Associativity: (w1·w2)·w3 ≡ w1·(w2·w3)      (follows from Seq concat assoc)
/// - Identity: ε·w ≡ w ≡ w·ε                        (above)
/// - Inverses: w·w⁻¹ ≡ ε ≡ w⁻¹·w                   (above)
/// - Closure: concat and inverse_word are total      (by construction)
/// - Well-defined: equiv respects concat             (above)

/// Associativity is definitional (Seq concatenation is associative).
pub proof fn lemma_group_associative(p: Presentation, w1: Word, w2: Word, w3: Word)
    ensures
        equiv_in_presentation(
            p,
            concat(concat(w1, w2), w3),
            concat(w1, concat(w2, w3)),
        ),
{
    lemma_concat_assoc(w1, w2, w3);
    // They're extensionally equal, so trivially equivalent
    assert(concat(concat(w1, w2), w3) =~= concat(w1, concat(w2, w3)));
    lemma_equiv_refl(p, concat(w1, concat(w2, w3)));
}

} // verus!
