use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;

verus! {

// ============================================================
// HNN Extensions
// ============================================================
//
// Given a base group G = ⟨S | R⟩ and pairs of associated words (a_i, b_i),
// the HNN extension is:
//   G*_φ = ⟨S, t | R, t⁻¹·a_i·t·b_i⁻¹ for each i⟩
//
// The stable letter t is Gen(|S|), the new generator.

/// Data for an HNN extension: base presentation plus association pairs.
pub struct HNNData {
    pub base: Presentation,
    /// Each pair (a_i, b_i) represents the relation t⁻¹·a_i·t = b_i.
    pub associations: Seq<(Word, Word)>,
}

/// The stable letter symbol: Gen(base.num_generators).
pub open spec fn stable_letter(data: HNNData) -> Symbol {
    Symbol::Gen(data.base.num_generators)
}

/// The inverse of the stable letter.
pub open spec fn stable_letter_inv(data: HNNData) -> Symbol {
    Symbol::Inv(data.base.num_generators)
}

/// Build the i-th HNN relator: t⁻¹ · a_i · t · b_i⁻¹.
pub open spec fn hnn_relator(data: HNNData, i: int) -> Word
    recommends
        0 <= i < data.associations.len(),
{
    let (a_i, b_i) = data.associations[i];
    let t = stable_letter(data);
    let t_inv = stable_letter_inv(data);
    // t⁻¹ · a_i · t · b_i⁻¹
    Seq::new(1, |_j: int| t_inv) + a_i + Seq::new(1, |_j: int| t) + inverse_word(b_i)
}

/// Build the sequence of all HNN relators.
pub open spec fn hnn_relators(data: HNNData) -> Seq<Word> {
    Seq::new(data.associations.len(), |i: int| hnn_relator(data, i))
}

/// The HNN presentation: base generators + t, base relators + HNN relators.
pub open spec fn hnn_presentation(data: HNNData) -> Presentation {
    Presentation {
        num_generators: data.base.num_generators + 1,
        relators: data.base.relators + hnn_relators(data),
    }
}

/// The HNN presentation extends the base presentation
/// (base relators come first, same plus one generator but apply_step ignores num_generators).
proof fn lemma_hnn_extends_base(data: HNNData)
    ensures ({
        let hp = hnn_presentation(data);
        let bp = data.base;
        &&& bp.relators.len() <= hp.relators.len()
        &&& hp.relators.subrange(0, bp.relators.len() as int) == bp.relators
    }),
{
    let hp = hnn_presentation(data);
    let bp = data.base;
    assert(hp.relators.subrange(0, bp.relators.len() as int) =~= bp.relators);
}

/// A derivation step valid in the base is valid in the HNN presentation.
proof fn lemma_step_valid_in_hnn(
    data: HNNData,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        apply_step(data.base, w, step) == Some(w_prime),
    ensures
        apply_step(hnn_presentation(data), w, step) == Some(w_prime),
{
    let hp = hnn_presentation(data);
    let bp = data.base;
    match step {
        DerivationStep::FreeReduce { position } => {},
        DerivationStep::FreeExpand { position, symbol } => {},
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= relator_index < bp.relators.len());
            assert(hp.relators[relator_index as int] == bp.relators[relator_index as int]);
            assert(get_relator(hp, relator_index, inverted) == get_relator(bp, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < bp.relators.len());
            assert(hp.relators[relator_index as int] == bp.relators[relator_index as int]);
            assert(get_relator(hp, relator_index, inverted) == get_relator(bp, relator_index, inverted));
        },
    }
}

/// A derivation valid in the base is valid in the HNN presentation.
proof fn lemma_derivation_valid_in_hnn(
    data: HNNData,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(data.base, steps, w1) == Some(w2),
    ensures
        derivation_produces(hnn_presentation(data), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let next = apply_step(data.base, w1, step).unwrap();
        lemma_step_valid_in_hnn(data, w1, step, next);
        lemma_derivation_valid_in_hnn(data, steps.drop_first(), next, w2);
    }
}

/// Base group embeds in HNN extension:
/// if w1 ≡ w2 in base, then w1 ≡ w2 in hnn_presentation.
pub proof fn lemma_base_embeds_in_hnn(data: HNNData, w1: Word, w2: Word)
    requires
        equiv_in_presentation(data.base, w1, w2),
    ensures
        equiv_in_presentation(hnn_presentation(data), w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(data.base, d, w1, w2);
    lemma_derivation_valid_in_hnn(data, d.steps, w1, w2);
    let d_hnn = Derivation { steps: d.steps };
    assert(derivation_valid(hnn_presentation(data), d_hnn, w1, w2));
}

/// The HNN conjugation relation: t⁻¹·a_i·t ≡ b_i in the HNN presentation.
/// This is by construction: t⁻¹·a_i·t·b_i⁻¹ is a relator, so it equals ε,
/// hence t⁻¹·a_i·t ≡ b_i.
pub proof fn lemma_hnn_conjugation(data: HNNData, i: int)
    requires
        0 <= i < data.associations.len(),
    ensures
        equiv_in_presentation(
            hnn_presentation(data),
            Seq::new(1, |_j: int| stable_letter_inv(data))
                + data.associations[i].0
                + Seq::new(1, |_j: int| stable_letter(data)),
            data.associations[i].1,
        ),
{
    let hp = hnn_presentation(data);
    let bp = data.base;
    let (a_i, b_i) = data.associations[i];
    let t = stable_letter(data);
    let t_inv = stable_letter_inv(data);
    let lhs = Seq::new(1, |_j: int| t_inv) + a_i + Seq::new(1, |_j: int| t);

    // The relator is t⁻¹·a_i·t·b_i⁻¹ at index bp.relators.len() + i
    let rel_idx = (bp.relators.len() + i) as nat;
    let relator = hnn_relator(data, i);
    assert(hp.relators[rel_idx as int] == relator);

    // relator = lhs + inverse_word(b_i)
    // So lhs · inverse_word(b_i) is a relator, hence ≡ ε
    // Which means lhs ≡ b_i (lhs · b_i⁻¹ ≡ ε ⟹ lhs ≡ b_i)

    // Step 1: relator ≡ ε (delete the relator)
    let step = DerivationStep::RelatorDelete {
        position: 0,
        relator_index: rel_idx,
        inverted: false,
    };
    assert(relator.subrange(0, 0int + relator.len() as int) =~= relator);
    let result = relator.subrange(0, 0int) + relator.subrange(0 + relator.len() as int, relator.len() as int);
    assert(result =~= empty_word());
    assert(apply_step(hp, relator, step) == Some(result));
    let d_del = Derivation { steps: Seq::new(1, |_j: int| step) };
    assert(d_del.steps.first() == step);
    assert(d_del.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(derivation_produces(hp, d_del.steps.drop_first(), result) == Some(result));
    assert(result == empty_word());
    assert(derivation_valid(hp, d_del, relator, empty_word()));
    // relator ≡ ε

    // relator =~= lhs + inverse_word(b_i)
    assert(relator =~= concat(lhs, inverse_word(b_i)));

    // So lhs · b_i⁻¹ ≡ ε
    // lhs ≡ lhs · ε (identity)
    // lhs · ε ≡ lhs · (b_i⁻¹ · b_i) (right inverse, inverted)
    // lhs · (b_i⁻¹ · b_i) =~= (lhs · b_i⁻¹) · b_i ≡ ε · b_i ≡ b_i

    // More directly: lhs · b_i⁻¹ ≡ ε, so lhs ≡ b_i
    // Since (lhs · b_i⁻¹) · b_i ≡ ε · b_i ≡ b_i
    // and (lhs · b_i⁻¹) · b_i =~= lhs · (b_i⁻¹ · b_i) =~= lhs · ε =~= lhs... wait that's circular.

    // Let's use: lhs · b_i⁻¹ ≡ ε
    // ⟹ (lhs · b_i⁻¹) · b_i ≡ ε · b_i ≡ b_i  (concat on right)
    // And lhs · (b_i⁻¹ · b_i) ≡ lhs · ε ≡ lhs  (right inverse + identity)
    // But (lhs · b_i⁻¹) · b_i =~= lhs · (b_i⁻¹ · b_i) by assoc
    // So lhs ≡ b_i

    // Step: relator ≡ ε → concat(relator, b_i) ≡ concat(ε, b_i) ≡ b_i
    lemma_equiv_concat_left(hp, relator, empty_word(), b_i);
    assert(concat(empty_word(), b_i) =~= b_i);
    lemma_equiv_refl(hp, b_i);

    // concat(relator, b_i) ≡ b_i
    lemma_equiv_transitive(hp, concat(relator, b_i), concat(empty_word(), b_i), b_i);

    // concat(relator, b_i) =~= concat(lhs + inverse_word(b_i), b_i)
    //                       =~= lhs + (inverse_word(b_i) + b_i)
    assert(concat(relator, b_i) =~= concat(lhs, concat(inverse_word(b_i), b_i)));

    // inverse_word(b_i) · b_i ≡ ε (left inverse)
    lemma_word_inverse_left(hp, b_i);

    // lhs · (b_i⁻¹ · b_i) ≡ lhs · ε
    lemma_equiv_concat_right(hp, lhs, concat(inverse_word(b_i), b_i), empty_word());
    assert(concat(lhs, empty_word()) =~= lhs);
    lemma_equiv_refl(hp, lhs);
    // lhs · (b_i⁻¹ · b_i) ≡ lhs
    lemma_equiv_transitive(hp, concat(lhs, concat(inverse_word(b_i), b_i)), concat(lhs, empty_word()), lhs);

    // Chain: lhs ≡ concat(lhs, concat(inv(b_i), b_i)) =~= concat(relator, b_i) ≡ b_i
    // Need: lhs ≡ concat(lhs, concat(inv(b_i), b_i))
    lemma_equiv_symmetric(hp, concat(lhs, concat(inverse_word(b_i), b_i)), lhs);
    // lhs ≡ concat(relator, b_i) (they're =~= via assoc)
    lemma_equiv_transitive(hp, lhs, concat(lhs, concat(inverse_word(b_i), b_i)), b_i);
}

/// The i-th HNN relator has the expected structure: t⁻¹·a_i·t·b_i⁻¹.
pub proof fn lemma_hnn_relator_structure(data: HNNData, i: int)
    requires
        0 <= i < data.associations.len(),
    ensures ({
        let hp = hnn_presentation(data);
        let bp = data.base;
        let rel_idx = bp.relators.len() + i;
        let (a_i, b_i) = data.associations[i];
        let t = stable_letter(data);
        let t_inv = stable_letter_inv(data);
        hp.relators[rel_idx] == Seq::new(1, |_j: int| t_inv) + a_i + Seq::new(1, |_j: int| t) + inverse_word(b_i)
    }),
{
    let hp = hnn_presentation(data);
    let bp = data.base;
    let rel_idx = (bp.relators.len() + i) as int;
    assert(hp.relators[rel_idx] == hnn_relator(data, i));
}

} // verus!
