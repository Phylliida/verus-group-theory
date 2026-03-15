use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::benign::*;
use crate::quotient::*;

verus! {

// ============================================================
// Higman Operations
// ============================================================
//
// The Higman operations transform benign subgroups into new
// benign subgroups. They are the key tool in Higman's embedding
// theorem for showing that recursively enumerable sets
// correspond to benign subgroups of free groups.
//
// Following Mikaelian (arXiv:2507.04347), the operations are:
//   ζ (zero), σ (shift/successor), θ (composition),
//   υ (union), ρ (primitive recursion)
//
// Each operation preserves benignness.
//
// For our purposes, the critical result is:
//   If a set of relators is recursively enumerable, then the
//   normal closure of those relators forms a benign subgroup
//   of the free group.

// ============================================================
// Free group on n generators
// ============================================================

/// The free group on n generators: no relators.
pub open spec fn free_group(n: nat) -> Presentation {
    Presentation {
        num_generators: n,
        relators: Seq::<Word>::empty(),
    }
}

/// The free group is always presentation_valid.
pub proof fn lemma_free_group_valid(n: nat)
    ensures
        presentation_valid(free_group(n)),
{
    reveal(presentation_valid);
}

/// In the free group, two words are equivalent iff they are freely equal.
/// (No relators means no relator steps in derivations.)
/// This is stated as: word_valid base words that are equiv in free_group
/// must reduce to the same normal form.
/// For our purposes, the key property is that free groups are nontrivial.

// ============================================================
// Normal closure as a subgroup
// ============================================================

/// The normal closure of a set of words in a presentation p is
/// the smallest normal subgroup containing those words.
/// A word w is in the normal closure of gens if w ≡ ε in the
/// quotient p' = p + gens as relators.
pub open spec fn in_normal_closure(
    p: Presentation, gens: Seq<Word>, w: Word,
) -> bool {
    let p_prime = add_relators(p, gens);
    equiv_in_presentation(p_prime, w, empty_word())
}

// ============================================================
// Rope Trick: benign subgroup → finitely presented group
// ============================================================
//
// The Rope Trick (Higman's construction) takes:
//   - A group G (presented)
//   - A benign subgroup A ≤ G (with witness K, L)
// And constructs a finitely presented group H with G/⟨⟨A⟩⟩ ↪ H.
//
// The construction uses HNN extensions and amalgamated free products
// to "tie" the benign subgroup into a finitely presented structure.
//
// For our purposes, we axiomatize the final result:

/// The Rope Trick: if A is a benign subgroup of F₂ (the 2-generator
/// free group), then the quotient F₂/⟨⟨A⟩⟩ embeds in a finitely
/// presented group.
///
/// This is Higman's key construction: the benignness witness provides
/// the overgroup K and the finitely generated L. The Rope Trick
/// builds H from K using HNN extensions, ensuring that the quotient
/// embeds injectively.
///
/// The proof requires:
/// 1. Building an HNN extension that identifies the benign subgroup
/// 2. Using amalgamated free products to merge with K
/// 3. Proving injectivity via Britton's Lemma
///
/// This is axiomatized as the construction is intricate but standard.
#[verifier::external_body]
pub proof fn axiom_rope_trick(
    gens: Seq<Word>,
    witness: BenignWitness,
)
    requires
        benign_witness_valid(free_group(2), gens, witness),
    ensures
        exists|p: Presentation, emb: Seq<Word>|
            presentation_valid(p) &&
            emb.len() == 2 &&
            (forall|i: int| 0 <= i < emb.len() ==>
                word_valid(#[trigger] emb[i], p.num_generators)) &&
            // Embedding preserves: equiv in quotient → equiv in H
            (forall|w1: Word, w2: Word|
                word_valid(w1, 2) && word_valid(w2, 2) &&
                equiv_in_presentation(add_relators(free_group(2), gens), w1, w2)
                ==> #[trigger] equiv_in_presentation(p, apply_embedding(emb, w1), apply_embedding(emb, w2))) &&
            // Embedding reflects: equiv in H → equiv in quotient
            (forall|w1: Word, w2: Word|
                word_valid(w1, 2) && word_valid(w2, 2) &&
                equiv_in_presentation(p, apply_embedding(emb, w1), apply_embedding(emb, w2))
                ==> #[trigger] equiv_in_presentation(add_relators(free_group(2), gens), w1, w2)),
{
}

} // verus!
