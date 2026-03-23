use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::rewrite::*;
use crate::rewrite_sound::*;
use crate::presentation::*;

verus! {

// ============================================================
// Normal form uniqueness and decidability
// ============================================================
//
// Separated into its own module to keep the Z3 context clean.
// These proofs only need rewrite.rs specs + rewrite_sound lemmas.

/// If two irreducible words are joinable, they are equal.
pub proof fn lemma_unique_normal_form(
    sys: RewriteSystem,
    nf1: Word, nf2: Word,
)
    requires
        joinable(sys, nf1, nf2),
        is_irreducible(sys, nf1),
        is_irreducible(sys, nf2),
    ensures
        nf1 =~= nf2,
{
    let w3 = choose|w3: Word| rewrites_to(sys, nf1, w3) && rewrites_to(sys, nf2, w3);
    lemma_irreducible_only_rewrites_to_self(sys, nf1, w3);
    lemma_irreducible_only_rewrites_to_self(sys, nf2, w3);
}

/// An irreducible word can only rewrite to itself.
pub proof fn lemma_irreducible_only_rewrites_to_self(
    sys: RewriteSystem, w: Word, w2: Word,
)
    requires
        is_irreducible(sys, w),
        rewrites_to(sys, w, w2),
    ensures
        w =~= w2,
{
    let n = choose|n: nat| rewrites_in_steps(sys, w, w2, n);
    lemma_irreducible_only_rewrites_to_self_aux(sys, w, w2, n);
}

proof fn lemma_irreducible_only_rewrites_to_self_aux(
    sys: RewriteSystem, w: Word, w2: Word, n: nat,
)
    requires
        is_irreducible(sys, w),
        rewrites_in_steps(sys, w, w2, n),
    ensures
        w =~= w2,
    decreases n,
{
    if n == 0 {
    } else if w =~= w2 {
    } else {
        let w_mid = choose|w_mid: Word|
            rewrites_one_step(sys, w, w_mid)
            && rewrites_in_steps(sys, w_mid, w2, (n - 1) as nat);
        lemma_irreducible_no_step(sys, w);
        assert(false);
    }
}

/// The easy direction: same normal form implies equivalence.
pub proof fn lemma_same_normal_form_implies_equiv(
    sys: RewriteSystem, p: Presentation,
    w1: Word, w2: Word,
    nf: Word,
)
    requires
        presentation_valid(p),
        system_sound(sys, p),
        system_wf(sys),
        word_valid(w1, p.num_generators),
        word_valid(w2, p.num_generators),
        rewrites_to(sys, w1, nf),
        rewrites_to(sys, w2, nf),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let n1 = choose|n: nat| rewrites_in_steps(sys, w1, nf, n);
    let n2 = choose|n: nat| rewrites_in_steps(sys, w2, nf, n);
    lemma_rewrite_preserves_equiv(sys, p, w1, nf, n1);
    lemma_rewrite_preserves_equiv(sys, p, w2, nf, n2);
    lemma_equiv_symmetric(p, w2, nf);
    lemma_equiv_transitive(p, w1, nf, w2);
}

} // verus!
