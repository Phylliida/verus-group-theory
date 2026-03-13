use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;

verus! {

/// Data defining a group homomorphism via generator images.
/// A homomorphism φ: G → H is determined by the images of each generator.
pub struct HomomorphismData {
    pub source: Presentation,
    pub target: Presentation,
    /// images[i] = the image of Gen(i) in the target group.
    pub generator_images: Seq<Word>,
}

/// Image of a single symbol under the homomorphism.
/// Gen(i) → images[i], Inv(i) → inverse_word(images[i]).
pub open spec fn apply_hom_symbol(h: HomomorphismData, s: Symbol) -> Word {
    match s {
        Symbol::Gen(i) => h.generator_images[i as int],
        Symbol::Inv(i) => inverse_word(h.generator_images[i as int]),
    }
}

/// Image of a word under the homomorphism (recursive concatenation of symbol images).
pub open spec fn apply_hom(h: HomomorphismData, w: Word) -> Word
    decreases w.len(),
{
    if w.len() == 0 {
        empty_word()
    } else {
        concat(apply_hom_symbol(h, w.first()), apply_hom(h, w.drop_first()))
    }
}

/// A homomorphism is valid if:
/// 1. images.len() == source.num_generators (one image per generator)
/// 2. Each source relator maps to a word equivalent to ε in the target
pub open spec fn is_valid_homomorphism(h: HomomorphismData) -> bool {
    h.generator_images.len() == h.source.num_generators
    && forall|i: int| 0 <= i < h.source.relators.len() ==>
        equiv_in_presentation(h.target, apply_hom(h, h.source.relators[i]), empty_word())
}

/// The identity homomorphism: Gen(i) → [Gen(i)].
pub open spec fn identity_hom(p: Presentation) -> HomomorphismData {
    HomomorphismData {
        source: p,
        target: p,
        generator_images: Seq::new(p.num_generators as int, |i: int| {
            Seq::new(1, |_j: int| Symbol::Gen(i as nat))
        }),
    }
}

/// Composition of homomorphisms: Gen(i) → apply_hom(h2, h1.images[i]).
pub open spec fn compose_hom(h1: HomomorphismData, h2: HomomorphismData) -> HomomorphismData {
    HomomorphismData {
        source: h1.source,
        target: h2.target,
        generator_images: Seq::new(h1.generator_images.len() as int, |i: int| {
            apply_hom(h2, h1.generator_images[i])
        }),
    }
}

// --- Lemmas ---

/// Homomorphism of empty word is empty.
pub proof fn lemma_hom_empty(h: HomomorphismData)
    ensures
        apply_hom(h, empty_word()) =~= empty_word(),
{
}

/// Homomorphism respects concatenation.
pub proof fn lemma_hom_respects_concat(h: HomomorphismData, w1: Word, w2: Word)
    ensures
        apply_hom(h, concat(w1, w2)) =~= concat(apply_hom(h, w1), apply_hom(h, w2)),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(apply_hom(h, w1) =~= empty_word());
        assert(concat(empty_word(), apply_hom(h, w2)) =~= apply_hom(h, w2));
    } else {
        // w1 = s · rest, so concat(w1, w2) = s · concat(rest, w2)
        let s = w1.first();
        let rest = w1.drop_first();
        assert(concat(w1, w2).first() == s);
        assert(concat(w1, w2).drop_first() =~= concat(rest, w2));

        // IH: apply_hom(concat(rest, w2)) =~= concat(apply_hom(rest), apply_hom(w2))
        lemma_hom_respects_concat(h, rest, w2);

        // apply_hom(concat(w1, w2))
        //   = concat(apply_hom_symbol(s), apply_hom(concat(rest, w2)))
        //   =~= concat(apply_hom_symbol(s), concat(apply_hom(rest), apply_hom(w2)))
        //   =~= concat(concat(apply_hom_symbol(s), apply_hom(rest)), apply_hom(w2))
        //   = concat(apply_hom(w1), apply_hom(w2))
        lemma_concat_assoc(apply_hom_symbol(h, s), apply_hom(h, rest), apply_hom(h, w2));
    }
}

/// Homomorphism respects word inverse.
pub proof fn lemma_hom_respects_inverse(h: HomomorphismData, w: Word)
    ensures
        apply_hom(h, inverse_word(w)) =~= inverse_word(apply_hom(h, w)),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        // inverse_word(w) = inverse_word(rest) ++ [inverse_symbol(s)]
        // apply_hom(inverse_word(w))
        //   =~= concat(apply_hom(inverse_word(rest)), apply_hom([inv_s]))
        //   by hom_respects_concat

        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        assert(inverse_word(w) =~= concat(inverse_word(rest), inv_s_word));
        lemma_hom_respects_concat(h, inverse_word(rest), inv_s_word);

        // IH
        lemma_hom_respects_inverse(h, rest);

        // apply_hom([inv_s]) = apply_hom_symbol(inv_s)
        assert(apply_hom(h, inv_s_word) =~= concat(apply_hom_symbol(h, inverse_symbol(s)), empty_word()));
        assert(concat(apply_hom_symbol(h, inverse_symbol(s)), empty_word()) =~= apply_hom_symbol(h, inverse_symbol(s)));

        // apply_hom_symbol(inv_s) = inverse of apply_hom_symbol(s)
        // For Gen(i): apply_hom_symbol(Inv(i)) = inverse_word(images[i]) = inverse_word(apply_hom_symbol(Gen(i)))
        // For Inv(i): apply_hom_symbol(Gen(i)) = images[i] = inverse_word(inverse_word(images[i]))
        //             = inverse_word(apply_hom_symbol(Inv(i)))
        match s {
            Symbol::Gen(idx) => {
                // apply_hom_symbol(Gen(idx)) = images[idx]
                // apply_hom_symbol(Inv(idx)) = inverse_word(images[idx])
                // Good: inverse_word(images[idx]) = inverse_word(apply_hom_symbol(Gen(idx)))
            },
            Symbol::Inv(idx) => {
                // apply_hom_symbol(Inv(idx)) = inverse_word(images[idx])
                // apply_hom_symbol(Gen(idx)) = images[idx]
                // Need: images[idx] =~= inverse_word(inverse_word(images[idx]))
                lemma_inverse_involution(h.generator_images[idx as int]);
            },
        }

        // Now: apply_hom(inverse_word(w))
        //   =~= concat(apply_hom(inverse_word(rest)), apply_hom_symbol(h, inverse_symbol(s)))
        //   =~= concat(inverse_word(apply_hom(rest)), inverse_word(apply_hom_symbol(h, s)))

        // inverse_word(apply_hom(w))
        //   = inverse_word(concat(apply_hom_symbol(s), apply_hom(rest)))
        //   =~= concat(inverse_word(apply_hom(rest)), inverse_word(apply_hom_symbol(s)))
        lemma_inverse_concat(apply_hom_symbol(h, s), apply_hom(h, rest));
    }
}

/// Homomorphism preserves a single derivation step.
pub proof fn lemma_hom_preserves_single_step(
    h: HomomorphismData,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        is_valid_homomorphism(h),
        apply_step(h.source, w, step) == Some(w_prime),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w), apply_hom(h, w_prime)),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            lemma_hom_preserves_free_reduce(h, w, position);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            lemma_hom_preserves_free_expand(h, w, position, symbol);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            lemma_hom_preserves_relator_insert(h, w, position, relator_index, inverted);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            lemma_hom_preserves_relator_delete(h, w, position, relator_index, inverted);
        },
    }
}

/// Helper: hom preserves FreeReduce step.
proof fn lemma_hom_preserves_free_reduce(
    h: HomomorphismData, w: Word, position: int,
)
    requires
        is_valid_homomorphism(h),
        has_cancellation_at(w, position),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w), apply_hom(h, reduce_at(w, position))),
{
    let s1 = w[position];
    let s2 = w[position + 1];
    // s2 == inverse_symbol(s1), so their images concatenate to ε

    // w = prefix ++ [s1, s2] ++ suffix
    let prefix = w.subrange(0, position);
    let pair = Seq::new(1, |_i: int| s1) + Seq::new(1, |_i: int| s2);
    let suffix = w.subrange(position + 2, w.len() as int);
    assert(w =~= prefix + pair + suffix);

    // reduce_at(w, position) = prefix ++ suffix
    let reduced = reduce_at(w, position);
    assert(reduced =~= prefix + suffix);

    // apply_hom distributes over concat
    lemma_hom_respects_concat(h, prefix, pair + suffix);
    lemma_hom_respects_concat(h, pair, suffix);
    lemma_hom_respects_concat(h, prefix, suffix);

    // apply_hom(pair) = concat(image(s1), image(s2))
    // image(s2) = image(inverse_symbol(s1)) = inverse_word(image(s1))
    let pair_seq = Seq::new(1, |_i: int| s1) + Seq::new(1, |_i: int| s2);
    lemma_hom_respects_concat(h, Seq::new(1, |_i: int| s1), Seq::new(1, |_i: int| s2));

    let img_s1 = apply_hom_symbol(h, s1);
    let img_s2 = apply_hom_symbol(h, s2);
    assert(apply_hom(h, Seq::new(1, |_i: int| s1)) =~= concat(img_s1, empty_word()));
    assert(concat(img_s1, empty_word()) =~= img_s1);
    assert(apply_hom(h, Seq::new(1, |_i: int| s2)) =~= concat(img_s2, empty_word()));
    assert(concat(img_s2, empty_word()) =~= img_s2);

    // img_s2 = inverse_word(img_s1)
    match s1 {
        Symbol::Gen(idx) => {
            assert(img_s2 == inverse_word(h.generator_images[idx as int]));
            assert(img_s1 == h.generator_images[idx as int]);
        },
        Symbol::Inv(idx) => {
            assert(img_s2 == h.generator_images[idx as int]);
            assert(img_s1 == inverse_word(h.generator_images[idx as int]));
            lemma_inverse_involution(h.generator_images[idx as int]);
        },
    }

    // concat(img_s1, img_s2) ≡ ε in target
    lemma_word_inverse_right(h.target, img_s1);

    // apply_hom(w) =~= concat(apply_hom(prefix), concat(concat(img_s1, img_s2), apply_hom(suffix)))
    // apply_hom(reduced) =~= concat(apply_hom(prefix), apply_hom(suffix))
    // concat(img_s1, img_s2) ≡ ε
    // So concat(concat(img_s1, img_s2), apply_hom(suffix)) ≡ concat(ε, apply_hom(suffix)) =~= apply_hom(suffix)
    lemma_equiv_concat_left(h.target, concat(img_s1, img_s2), empty_word(), apply_hom(h, suffix));
    assert(concat(empty_word(), apply_hom(h, suffix)) =~= apply_hom(h, suffix));

    // Now chain through the associativity
    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let pair_img = concat(img_s1, img_s2);

    assert(apply_hom(h, w) =~= concat(hom_prefix, concat(pair_img, hom_suffix)));
    assert(apply_hom(h, reduced) =~= concat(hom_prefix, hom_suffix));

    // pair_img ≡ ε, so concat(pair_img, hom_suffix) ≡ hom_suffix
    lemma_equiv_transitive(
        h.target,
        concat(pair_img, hom_suffix),
        concat(empty_word(), hom_suffix),
        hom_suffix,
    ) by {
        assert(concat(empty_word(), hom_suffix) =~= hom_suffix);
        lemma_equiv_refl(h.target, hom_suffix);
    }

    // concat(hom_prefix, concat(pair_img, hom_suffix)) ≡ concat(hom_prefix, hom_suffix)
    lemma_equiv_concat_right(h.target, hom_prefix, concat(pair_img, hom_suffix), hom_suffix);

    // apply_hom(w) =~= that, so equiv
    assert(apply_hom(h, w) =~= concat(hom_prefix, concat(pair_img, hom_suffix)));
    assert(apply_hom(h, reduced) =~= concat(hom_prefix, hom_suffix));
    lemma_equiv_refl(h.target, apply_hom(h, w));
}

/// Helper: hom preserves FreeExpand step.
proof fn lemma_hom_preserves_free_expand(
    h: HomomorphismData, w: Word, position: int, symbol: Symbol,
)
    requires
        is_valid_homomorphism(h),
        0 <= position <= w.len(),
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, w),
            apply_hom(h, apply_step(h.source, w, DerivationStep::FreeExpand { position, symbol }).unwrap()),
        ),
{
    let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
    let w_prime = w.subrange(0, position) + pair + w.subrange(position, w.len() as int);
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position, w.len() as int);
    assert(w =~= prefix + suffix);

    lemma_hom_respects_concat(h, prefix, suffix);
    lemma_hom_respects_concat(h, prefix, pair + suffix);
    lemma_hom_respects_concat(h, pair, suffix);

    // apply_hom(pair) = concat(image(symbol), image(inv(symbol)))
    lemma_hom_respects_concat(h, Seq::new(1, |_i: int| symbol), Seq::new(1, |_i: int| inverse_symbol(symbol)));
    let img_s = apply_hom_symbol(h, symbol);
    let img_inv_s = apply_hom_symbol(h, inverse_symbol(symbol));
    assert(apply_hom(h, Seq::new(1, |_i: int| symbol)) =~= img_s);
    assert(apply_hom(h, Seq::new(1, |_i: int| inverse_symbol(symbol))) =~= img_inv_s);

    // img_inv_s = inverse_word(img_s)
    match symbol {
        Symbol::Gen(idx) => {},
        Symbol::Inv(idx) => {
            lemma_inverse_involution(h.generator_images[idx as int]);
        },
    }

    // concat(img_s, img_inv_s) ≡ ε
    lemma_word_inverse_right(h.target, img_s);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let pair_img = concat(img_s, img_inv_s);

    // apply_hom(w) =~= concat(hom_prefix, hom_suffix)
    // apply_hom(w') =~= concat(hom_prefix, concat(pair_img, hom_suffix))
    // pair_img ≡ ε, so concat(pair_img, hom_suffix) ≡ hom_suffix
    lemma_equiv_concat_left(h.target, pair_img, empty_word(), hom_suffix);
    assert(concat(empty_word(), hom_suffix) =~= hom_suffix);
    lemma_equiv_transitive(
        h.target,
        concat(pair_img, hom_suffix),
        concat(empty_word(), hom_suffix),
        hom_suffix,
    ) by {
        assert(concat(empty_word(), hom_suffix) =~= hom_suffix);
        lemma_equiv_refl(h.target, hom_suffix);
    }

    // concat(hom_prefix, hom_suffix) ≡ concat(hom_prefix, concat(pair_img, hom_suffix))
    lemma_equiv_concat_right(h.target, hom_prefix, hom_suffix, concat(pair_img, hom_suffix));
    lemma_equiv_symmetric(h.target,
        concat(hom_prefix, hom_suffix),
        concat(hom_prefix, concat(pair_img, hom_suffix)),
    );

    assert(apply_hom(h, w) =~= concat(hom_prefix, hom_suffix));
    assert(apply_hom(h, w_prime) =~= concat(hom_prefix, concat(pair_img, hom_suffix)));
    lemma_equiv_refl(h.target, apply_hom(h, w));
}

/// Helper: hom preserves RelatorInsert step.
proof fn lemma_hom_preserves_relator_insert(
    h: HomomorphismData, w: Word,
    position: int, relator_index: nat, inverted: bool,
)
    requires
        is_valid_homomorphism(h),
        0 <= position <= w.len(),
        0 <= relator_index < h.source.relators.len(),
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, w),
            apply_hom(h, apply_step(h.source, w,
                DerivationStep::RelatorInsert { position, relator_index, inverted }).unwrap()),
        ),
{
    let r = get_relator(h.source, relator_index, inverted);
    let w_prime = w.subrange(0, position) + r + w.subrange(position, w.len() as int);
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position, w.len() as int);
    assert(w =~= prefix + suffix);

    lemma_hom_respects_concat(h, prefix, suffix);
    lemma_hom_respects_concat(h, prefix, r + suffix);
    lemma_hom_respects_concat(h, r, suffix);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let hom_r = apply_hom(h, r);

    // hom_r ≡ ε in target (from is_valid_homomorphism)
    // For inverted case: r = inverse_word(relator), need apply_hom(inverse_word(relator)) ≡ ε
    if inverted {
        let orig_r = h.source.relators[relator_index as int];
        // apply_hom(inverse_word(orig_r)) =~= inverse_word(apply_hom(orig_r))
        lemma_hom_respects_inverse(h, orig_r);
        // apply_hom(orig_r) ≡ ε
        // inverse_word(apply_hom(orig_r)) ≡ inverse_word(ε) =~= ε
        lemma_equiv_refl(h.target, inverse_word(apply_hom(h, orig_r)));
        // We need hom_r ≡ ε. hom_r =~= inverse_word(apply_hom(orig_r))
        // apply_hom(orig_r) ≡ ε, so inverse_word(apply_hom(orig_r)) ≡ inverse_word(ε) =~= ε
        // Use: w·w⁻¹ ≡ ε and w ≡ ε → w⁻¹ ≡ ε
        let hom_orig = apply_hom(h, orig_r);
        // hom_orig ≡ ε
        // inverse_word(hom_orig) · hom_orig ≡ ε (left inverse)
        lemma_word_inverse_left(h.target, hom_orig);
        // ε ≡ hom_orig
        lemma_equiv_symmetric(h.target, hom_orig, empty_word());
        // inverse_word(hom_orig) · hom_orig ≡ inverse_word(hom_orig) · ε
        lemma_equiv_concat_right(h.target, inverse_word(hom_orig), hom_orig, empty_word());
        // inverse_word(hom_orig) · ε =~= inverse_word(hom_orig)
        assert(concat(inverse_word(hom_orig), empty_word()) =~= inverse_word(hom_orig));
        // So inverse_word(hom_orig) ≡ ε (via transitivity)
        lemma_equiv_refl(h.target, inverse_word(hom_orig));
        lemma_equiv_transitive(h.target,
            inverse_word(hom_orig),
            concat(inverse_word(hom_orig), hom_orig),
            empty_word(),
        ) by {
            assert(inverse_word(hom_orig) =~= concat(inverse_word(hom_orig), empty_word()));
            lemma_equiv_symmetric(h.target,
                concat(inverse_word(hom_orig), hom_orig),
                concat(inverse_word(hom_orig), empty_word()),
            );
            lemma_equiv_transitive(h.target,
                inverse_word(hom_orig),
                concat(inverse_word(hom_orig), empty_word()),
                concat(inverse_word(hom_orig), hom_orig),
            ) by {
                assert(inverse_word(hom_orig) =~= concat(inverse_word(hom_orig), empty_word()));
                lemma_equiv_refl(h.target, inverse_word(hom_orig));
            }
        }
        assert(hom_r =~= inverse_word(hom_orig));
    } else {
        // direct: apply_hom(relator) ≡ ε
    }

    // Now hom_r ≡ ε
    // concat(hom_r, hom_suffix) ≡ concat(ε, hom_suffix) =~= hom_suffix
    lemma_equiv_concat_left(h.target, hom_r, empty_word(), hom_suffix);
    assert(concat(empty_word(), hom_suffix) =~= hom_suffix);
    lemma_equiv_transitive(h.target,
        concat(hom_r, hom_suffix),
        concat(empty_word(), hom_suffix),
        hom_suffix,
    ) by {
        assert(concat(empty_word(), hom_suffix) =~= hom_suffix);
        lemma_equiv_refl(h.target, hom_suffix);
    }

    // concat(hom_prefix, hom_suffix) ≡ concat(hom_prefix, concat(hom_r, hom_suffix))
    lemma_equiv_concat_right(h.target, hom_prefix, hom_suffix, concat(hom_r, hom_suffix));
    lemma_equiv_symmetric(h.target,
        concat(hom_prefix, hom_suffix),
        concat(hom_prefix, concat(hom_r, hom_suffix)),
    );

    assert(apply_hom(h, w) =~= concat(hom_prefix, hom_suffix));
    assert(apply_hom(h, w_prime) =~= concat(hom_prefix, concat(hom_r, hom_suffix)));
    lemma_equiv_refl(h.target, apply_hom(h, w));
}

/// Helper: hom preserves RelatorDelete step.
proof fn lemma_hom_preserves_relator_delete(
    h: HomomorphismData, w: Word,
    position: int, relator_index: nat, inverted: bool,
)
    requires
        is_valid_homomorphism(h),
        0 <= relator_index < h.source.relators.len(),
        apply_step(h.source, w, DerivationStep::RelatorDelete { position, relator_index, inverted }) is Some,
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, w),
            apply_hom(h, apply_step(h.source, w,
                DerivationStep::RelatorDelete { position, relator_index, inverted }).unwrap()),
        ),
{
    let r = get_relator(h.source, relator_index, inverted);
    let rlen = r.len();
    let w_prime = w.subrange(0, position) + w.subrange(position + rlen as int, w.len() as int);

    // w = prefix ++ r ++ suffix
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position + rlen as int, w.len() as int);
    assert(w.subrange(position, position + rlen as int) == r);
    assert(w =~= prefix + r + suffix);

    lemma_hom_respects_concat(h, prefix, r + suffix);
    lemma_hom_respects_concat(h, r, suffix);
    lemma_hom_respects_concat(h, prefix, suffix);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let hom_r = apply_hom(h, r);

    // Same logic as insert: hom_r ≡ ε
    if inverted {
        let orig_r = h.source.relators[relator_index as int];
        lemma_hom_respects_inverse(h, orig_r);
        let hom_orig = apply_hom(h, orig_r);
        lemma_word_inverse_left(h.target, hom_orig);
        lemma_equiv_symmetric(h.target, hom_orig, empty_word());
        lemma_equiv_concat_right(h.target, inverse_word(hom_orig), hom_orig, empty_word());
        assert(concat(inverse_word(hom_orig), empty_word()) =~= inverse_word(hom_orig));
        lemma_equiv_transitive(h.target,
            inverse_word(hom_orig),
            concat(inverse_word(hom_orig), hom_orig),
            empty_word(),
        ) by {
            lemma_equiv_symmetric(h.target,
                concat(inverse_word(hom_orig), hom_orig),
                concat(inverse_word(hom_orig), empty_word()),
            );
            lemma_equiv_transitive(h.target,
                inverse_word(hom_orig),
                concat(inverse_word(hom_orig), empty_word()),
                concat(inverse_word(hom_orig), hom_orig),
            ) by {
                assert(inverse_word(hom_orig) =~= concat(inverse_word(hom_orig), empty_word()));
                lemma_equiv_refl(h.target, inverse_word(hom_orig));
            }
        }
        assert(hom_r =~= inverse_word(hom_orig));
    }

    // concat(hom_r, hom_suffix) ≡ hom_suffix
    lemma_equiv_concat_left(h.target, hom_r, empty_word(), hom_suffix);
    assert(concat(empty_word(), hom_suffix) =~= hom_suffix);
    lemma_equiv_transitive(h.target,
        concat(hom_r, hom_suffix),
        concat(empty_word(), hom_suffix),
        hom_suffix,
    ) by {
        assert(concat(empty_word(), hom_suffix) =~= hom_suffix);
        lemma_equiv_refl(h.target, hom_suffix);
    }

    // concat(hom_prefix, concat(hom_r, hom_suffix)) ≡ concat(hom_prefix, hom_suffix)
    lemma_equiv_concat_right(h.target, hom_prefix, concat(hom_r, hom_suffix), hom_suffix);

    assert(apply_hom(h, w) =~= concat(hom_prefix, concat(hom_r, hom_suffix)));
    assert(apply_hom(h, w_prime) =~= concat(hom_prefix, hom_suffix));
    lemma_equiv_refl(h.target, apply_hom(h, w));
}

/// Homomorphism preserves a derivation (sequence of steps).
pub proof fn lemma_hom_preserves_derivation(
    h: HomomorphismData,
    steps: Seq<DerivationStep>, w: Word, w_prime: Word,
)
    requires
        is_valid_homomorphism(h),
        derivation_produces(h.source, steps, w) == Some(w_prime),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w), apply_hom(h, w_prime)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        lemma_equiv_refl(h.target, apply_hom(h, w));
    } else {
        let step = steps.first();
        let rest = steps.drop_first();
        let w_mid = apply_step(h.source, w, step).unwrap();

        // Step: apply_hom(w) ≡ apply_hom(w_mid)
        lemma_hom_preserves_single_step(h, w, step, w_mid);

        // IH: apply_hom(w_mid) ≡ apply_hom(w_prime)
        lemma_hom_preserves_derivation(h, rest, w_mid, w_prime);

        // Chain
        lemma_equiv_transitive(h.target,
            apply_hom(h, w), apply_hom(h, w_mid), apply_hom(h, w_prime));
    }
}

/// **Main theorem**: Homomorphisms preserve equivalence.
/// If w1 ≡ w2 in source, then φ(w1) ≡ φ(w2) in target.
pub proof fn lemma_hom_preserves_equiv(
    h: HomomorphismData, w1: Word, w2: Word,
)
    requires
        is_valid_homomorphism(h),
        equiv_in_presentation(h.source, w1, w2),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w1), apply_hom(h, w2)),
{
    let d = choose|d: Derivation| derivation_valid(h.source, d, w1, w2);
    lemma_hom_preserves_derivation(h, d.steps, w1, w2);
}

/// The identity homomorphism is valid.
pub proof fn lemma_identity_hom_valid(p: Presentation)
    ensures
        is_valid_homomorphism(identity_hom(p)),
{
    let h = identity_hom(p);
    assert(h.generator_images.len() == p.num_generators);

    // For each relator r, apply_hom(h, r) =~= r
    assert forall|i: int| 0 <= i < p.relators.len() implies
        equiv_in_presentation(h.target, apply_hom(h, h.source.relators[i]), empty_word())
    by {
        let r = p.relators[i];
        lemma_identity_hom_apply(h, r);
        assert(apply_hom(h, r) =~= r);
        lemma_equiv_refl(h.target, apply_hom(h, r));
        lemma_relator_is_identity(p, i);
    }
}

/// Helper: identity homomorphism preserves words.
proof fn lemma_identity_hom_apply(h: HomomorphismData, w: Word)
    requires
        h.generator_images.len() == h.source.num_generators,
        forall|i: int| 0 <= i < h.generator_images.len() ==>
            h.generator_images[i] =~= Seq::new(1, |_j: int| Symbol::Gen(i as nat)),
    ensures
        apply_hom(h, w) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        lemma_identity_hom_apply(h, rest);

        // apply_hom_symbol(h, s) =~= Seq::new(1, |_| s)
        match s {
            Symbol::Gen(idx) => {
                assert(apply_hom_symbol(h, s) == h.generator_images[idx as int]);
                assert(h.generator_images[idx as int] =~= Seq::new(1, |_j: int| Symbol::Gen(idx)));
            },
            Symbol::Inv(idx) => {
                assert(apply_hom_symbol(h, s) == inverse_word(h.generator_images[idx as int]));
                assert(h.generator_images[idx as int] =~= Seq::new(1, |_j: int| Symbol::Gen(idx)));
                lemma_inverse_singleton(Symbol::Gen(idx));
            },
        }
        // concat(singleton(s), rest) =~= w
        assert(concat(Seq::new(1, |_j: int| s), rest) =~= w);
    }
}

} // verus!
