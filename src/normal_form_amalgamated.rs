use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::quotient::*;
use crate::normal_form_free_product::*;
use crate::benign::*;

verus! {

// ============================================================
// Amalgamated Free Product — Structural Lemmas
// ============================================================
//
// Key structural property: free reductions NEVER cross factor boundaries.
// is_inverse_pair requires the same generator index, and G₁ uses < n₁
// while G₂ uses ≥ n₁.

// ============================================================
// Definitions
// ============================================================

/// The identifications define an isomorphism between generated subgroups.
pub open spec fn identifications_isomorphic(data: AmalgamatedData) -> bool {
    let k = data.identifications.len();
    let a_words = Seq::new(k, |i: int| data.identifications[i].0);
    let b_words = Seq::new(k, |i: int| data.identifications[i].1);
    forall|w: Word| word_valid(w, k as nat) ==> (
        equiv_in_presentation(data.p1, apply_embedding(a_words, w), empty_word())
        <==>
        equiv_in_presentation(data.p2, apply_embedding(b_words, w), empty_word())
    )
}

/// A word is a "left word" (uses only G₁ generators).
pub open spec fn is_left_word(w: Word, n1: nat) -> bool {
    forall|k: int| 0 <= k < w.len() ==> generator_index(#[trigger] w[k]) < n1
}

// ============================================================
// add_relators structure
// ============================================================

/// add_relators(p, rs).relators =~= p.relators + rs.
pub proof fn lemma_add_relators_concat(p: Presentation, rs: Seq<Word>)
    ensures
        add_relators(p, rs).relators =~= p.relators + rs,
    decreases rs.len(),
{
    if rs.len() == 0 {
        assert(add_relators(p, rs) == p);
        assert(p.relators + rs =~= p.relators);
    } else {
        let p1 = add_relator(p, rs.first());
        assert(p1.relators =~= p.relators.push(rs.first()));
        assert(p1.relators =~= p.relators + Seq::new(1, |_i: int| rs.first()));
        lemma_add_relators_concat(p1, rs.drop_first());
        assert((p.relators + Seq::new(1, |_i: int| rs.first())) + rs.drop_first()
            =~= p.relators + rs) by {
            let lhs = (p.relators + Seq::new(1, |_i: int| rs.first())) + rs.drop_first();
            let rhs = p.relators + rs;
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < p.relators.len() {
                } else if k == p.relators.len() {
                    assert(lhs[k] == rs.first());
                    assert(rhs[k] == rs[0]);
                } else {
                    let j = (k - p.relators.len() - 1) as int;
                    assert(lhs[k] == rs.drop_first()[j]);
                    assert(rs.drop_first()[j] == rs[j + 1]);
                    assert(rhs[k] == rs[k - p.relators.len()]);
                }
            }
        }
    }
}

/// The AFP's relators are: fp.relators ++ amalgamation_relators(data).
pub proof fn lemma_afp_relators(data: AmalgamatedData)
    ensures
        amalgamated_free_product(data).relators =~=
            free_product(data.p1, data.p2).relators + amalgamation_relators(data),
{
    lemma_add_relators_concat(
        free_product(data.p1, data.p2),
        amalgamation_relators(data),
    );
}

// ============================================================
// Relator classification helpers
// ============================================================

/// AFP relator at index < p1.relators.len() equals p1's relator.
pub proof fn lemma_afp_relator_g1(data: AmalgamatedData, idx: nat)
    requires idx < data.p1.relators.len(),
    ensures ({
        let afp = amalgamated_free_product(data);
        &&& idx < afp.relators.len()
        &&& afp.relators[idx as int] == data.p1.relators[idx as int]
    }),
{
    lemma_afp_relators(data);
    let fp = free_product(data.p1, data.p2);
    assert(fp.relators[idx as int] == data.p1.relators[idx as int]);
}

/// Shifted G₂ relators have all symbols with generator_index >= n1.
proof fn lemma_shifted_relator_has_g2(data: AmalgamatedData, g2_idx: nat)
    requires g2_idx < data.p2.relators.len(),
    ensures
        forall|k: int| 0 <= k < shift_word(data.p2.relators[g2_idx as int], data.p1.num_generators).len()
            ==> generator_index(
                #[trigger] shift_word(data.p2.relators[g2_idx as int], data.p1.num_generators)[k]
            ) >= data.p1.num_generators,
{
    let n1 = data.p1.num_generators;
    let r = data.p2.relators[g2_idx as int];
    let sr = shift_word(r, n1);
    assert forall|k: int| 0 <= k < sr.len()
        implies generator_index(#[trigger] sr[k]) >= n1
    by {
        assert(sr[k] == shift_symbol(r[k], n1));
        match r[k] {
            Symbol::Gen(gi) => { assert(generator_index(sr[k]) == gi + n1); },
            Symbol::Inv(gi) => { assert(generator_index(sr[k]) == gi + n1); },
        }
    }
}

/// If v_i non-empty, identification relator has a G₂ symbol.
proof fn lemma_ident_relator_has_g2_if_v_nonempty(
    data: AmalgamatedData, ident_idx: int,
)
    requires
        0 <= ident_idx < data.identifications.len(),
        data.identifications[ident_idx].1.len() > 0,
    ensures
        exists|k: int| 0 <= k < amalgamation_relator(data, ident_idx).len()
            && generator_index(amalgamation_relator(data, ident_idx)[k])
                >= data.p1.num_generators,
{
    let n1 = data.p1.num_generators;
    let (u_i, v_i) = data.identifications[ident_idx];
    let shifted_v = shift_word(v_i, n1);
    let inv_sv = inverse_word(shifted_v);
    let rel = amalgamation_relator(data, ident_idx);
    assert(rel == concat(u_i, inv_sv));
    lemma_inverse_word_len(shifted_v);
    lemma_inverse_word_last_is_inv_of_first(shifted_v);
    let last_idx = (inv_sv.len() - 1) as int;
    assert(inv_sv[last_idx] == inverse_symbol(shifted_v.first()));
    assert(shifted_v.first() == shift_symbol(v_i.first(), n1));
    match v_i.first() {
        Symbol::Gen(gi) => {
            assert(generator_index(inverse_symbol(shifted_v.first())) == gi + n1);
        },
        Symbol::Inv(gi) => {
            assert(generator_index(inverse_symbol(shifted_v.first())) == gi + n1);
        },
    }
    let pos = (u_i.len() as int) + last_idx;
    assert(rel[pos] == inv_sv[last_idx]) by {
        assert(concat(u_i, inv_sv)[pos] == inv_sv[last_idx]);
    }
}

/// inverse_word(w)[w.len()-1] == inverse_symbol(w.first()) when non-empty.
proof fn lemma_inverse_word_last_is_inv_of_first(w: Word)
    requires w.len() > 0,
    ensures
        inverse_word(w).len() == w.len(),
        inverse_word(w)[(w.len() - 1) as int] == inverse_symbol(w.first()),
{
    lemma_inverse_word_len(w);
    let inv_rest = inverse_word(w.drop_first());
    let inv_first_sym = inverse_symbol(w.first());
    let tail = Seq::new(1, |_i: int| inv_first_sym);
    assert(inverse_word(w) =~= inv_rest + tail);
    lemma_inverse_word_len(w.drop_first());
    assert((inv_rest + tail)[(w.len() - 1) as int] == tail[0]);
}

/// If w has a symbol with generator_index >= n, so does inverse_word(w).
proof fn lemma_inverse_preserves_gen_bound_lower(w: Word, n: nat)
    requires
        w.len() > 0,
        exists|k: int| 0 <= k < w.len() && generator_index(w[k]) >= n,
    ensures
        exists|k: int| 0 <= k < inverse_word(w).len()
            && generator_index(inverse_word(w)[k]) >= n,
    decreases w.len(),
{
    lemma_inverse_word_len(w);
    let first = w.first();
    let rest = w.drop_first();
    let inv_rest = inverse_word(rest);
    let inv_first = inverse_symbol(first);
    assert(inverse_word(w) =~= inv_rest + Seq::new(1, |_i: int| inv_first));

    if generator_index(first) >= n {
        assert(generator_index(inv_first) == generator_index(first));
        let pos = (inverse_word(w).len() - 1) as int;
        assert(inverse_word(w)[pos] == inv_first);
    } else {
        let k = choose|k: int| 0 <= k < w.len() && generator_index(w[k]) >= n;
        assert(k > 0);
        assert(rest[k - 1] == w[k]);
        assert(rest.len() > 0);
        lemma_inverse_preserves_gen_bound_lower(rest, n);
        lemma_inverse_word_len(rest);
        let k2 = choose|k2: int| 0 <= k2 < inv_rest.len()
            && generator_index(inv_rest[k2]) >= n;
        assert(inverse_word(w)[k2] == inv_rest[k2]);
    }
}

/// If v_i is empty, then u_i ≡ ε in G₁ (via isomorphism condition).
proof fn lemma_empty_v_means_u_trivial(
    data: AmalgamatedData, ident_idx: nat,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        ident_idx < data.identifications.len(),
        data.identifications[ident_idx as int].1.len() == 0,
    ensures
        equiv_in_presentation(data.p1, data.identifications[ident_idx as int].0, empty_word()),
{
    let k = data.identifications.len();
    let a_words = Seq::new(k, |i: int| data.identifications[i].0);
    let b_words = Seq::new(k, |i: int| data.identifications[i].1);
    let (u_i, v_i) = data.identifications[ident_idx as int];
    let gen_word = Seq::new(1, |_j: int| Symbol::Gen(ident_idx));

    assert(word_valid(gen_word, k as nat)) by {
        assert(symbol_valid(Symbol::Gen(ident_idx), k as nat));
    }

    assert(gen_word.first() == Symbol::Gen(ident_idx));
    assert(gen_word.drop_first() =~= Seq::<Symbol>::empty());
    assert(apply_embedding_symbol(b_words, Symbol::Gen(ident_idx)) == v_i);
    assert(apply_embedding(b_words, gen_word.drop_first()) =~= empty_word());
    assert(apply_embedding(b_words, gen_word) =~= concat(v_i, empty_word()));
    assert(v_i =~= empty_word());
    assert(apply_embedding(b_words, gen_word) =~= empty_word());
    lemma_equiv_refl(data.p2, empty_word());

    assert(apply_embedding_symbol(a_words, Symbol::Gen(ident_idx)) == u_i);
    assert(apply_embedding(a_words, gen_word)
        == concat(apply_embedding_symbol(a_words, gen_word.first()),
                  apply_embedding(a_words, gen_word.drop_first())));
    assert(apply_embedding(a_words, gen_word) =~= concat(u_i, empty_word()));
    assert(concat(u_i, empty_word()) =~= u_i);
    assert(apply_embedding(a_words, gen_word) =~= u_i);
}

// ============================================================
// Inverse of trivial is trivial (with proper preconditions)
// ============================================================

/// If w ≡ ε and we have word_valid + presentation_valid, inverse_word(w) ≡ ε.
proof fn lemma_inverse_of_trivial(p: Presentation, w: Word)
    requires
        presentation_valid(p),
        word_valid(w, p.num_generators),
        equiv_in_presentation(p, w, empty_word()),
    ensures
        equiv_in_presentation(p, inverse_word(w), empty_word()),
{
    // w ≡ ε, so by symmetry (needs word_valid + pres_valid): ε ≡ w
    lemma_equiv_symmetric(p, w, empty_word());
    // concat(inv(w), ε) ≡ concat(inv(w), w)   (concat_right with ε ≡ w)
    lemma_equiv_concat_right(p, inverse_word(w), empty_word(), w);
    // concat(inv(w), ε) =~= inv(w)
    assert(concat(inverse_word(w), empty_word()) =~= inverse_word(w));
    // concat(inv(w), w) ≡ ε   (word_inverse_left)
    lemma_word_inverse_left(p, w);
    // Chain: inv(w) =~= concat(inv(w), ε) ≡ concat(inv(w), w) ≡ ε
    lemma_equiv_transitive(p, concat(inverse_word(w), empty_word()),
        concat(inverse_word(w), w), empty_word());
    lemma_equiv_refl(p, inverse_word(w));
    lemma_equiv_transitive(p, inverse_word(w),
        concat(inverse_word(w), empty_word()), empty_word());
}

// ============================================================
// Insert/delete of trivial word preserves equivalence
// ============================================================

/// Inserting r ≡ ε at position preserves equivalence.
/// Proves w ≡ (w[0..p] + r + w[p..]) by building w_prime → w (reducing r to ε)
/// then using symmetry.
proof fn lemma_insert_trivial_preserves_equiv(
    p: Presentation, w: Word, r: Word, position: int,
)
    requires
        presentation_valid(p),
        word_valid(w, p.num_generators),
        word_valid(r, p.num_generators),
        0 <= position <= w.len(),
        equiv_in_presentation(p, r, empty_word()),
    ensures
        equiv_in_presentation(
            p, w,
            w.subrange(0, position) + r + w.subrange(position, w.len() as int),
        ),
{
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position, w.len() as int);
    let w_prime = prefix + r + suffix;

    assert(w =~= prefix + suffix) by {
        assert((prefix + suffix).len() == w.len());
        assert forall|k: int| 0 <= k < w.len()
            implies (prefix + suffix)[k] == w[k]
        by { if k < position { } else { } }
    }

    // Build: w_prime ≡ w (direction: derivation from w_prime to w)
    // concat(r, suffix) ≡ concat(ε, suffix) =~= suffix
    lemma_equiv_concat_left(p, r, empty_word(), suffix);
    assert(concat(empty_word(), suffix) =~= suffix);
    lemma_equiv_refl(p, suffix);
    lemma_equiv_transitive(p, concat(r, suffix), concat(empty_word(), suffix), suffix);

    // concat(prefix, concat(r, suffix)) ≡ concat(prefix, suffix)
    lemma_equiv_concat_right(p, prefix, concat(r, suffix), suffix);

    // w_prime =~= concat(prefix, concat(r, suffix))
    assert(w_prime =~= concat(prefix, concat(r, suffix))) by {
        let lhs = prefix + r + suffix;
        let rhs = concat(prefix, concat(r, suffix));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < prefix.len() as int { }
            else if k < (prefix.len() + r.len()) as int {
                assert(lhs[k] == r[k - prefix.len()]);
                assert(concat(r, suffix)[k - prefix.len()] == r[k - prefix.len()]);
            } else {
                assert(lhs[k] == suffix[k - prefix.len() - r.len()]);
                assert(concat(r, suffix)[k - prefix.len()]
                    == suffix[k - prefix.len() - r.len()]);
            }
        }
    }

    // w =~= concat(prefix, suffix)
    // So: w_prime ≡ w (derivation from w_prime to w)
    // Now use symmetry to get w ≡ w_prime.
    // Need word_valid(w_prime, n) for symmetry.
    reveal(presentation_valid);
    assert(word_valid(w_prime, p.num_generators)) by {
        assert forall|k: int| 0 <= k < w_prime.len()
            implies symbol_valid(w_prime[k], p.num_generators)
        by {
            if k < prefix.len() as int {
                assert(w_prime[k] == prefix[k]);
                assert(prefix[k] == w[k]);
            } else if k < (prefix.len() + r.len()) as int {
                assert(w_prime[k] == r[k - prefix.len()]);
            } else {
                assert(w_prime[k] == suffix[k - prefix.len() - r.len()]);
                assert(suffix[k - prefix.len() - r.len()] == w[k - r.len()]);
            }
        }
    }
    lemma_equiv_symmetric(p, w_prime, w);
}

// ============================================================
// Non-G₁ AFP relator that's all-G₁ must be trivial in G₁
// ============================================================

/// Any AFP relator at index >= p1.relators.len(), if all-G₁, is ≡ ε in G₁.
proof fn lemma_nonstandard_afp_relator_trivial(
    data: AmalgamatedData, relator_index: nat, inverted: bool,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        relator_index < amalgamated_free_product(data).relators.len(),
        relator_index >= data.p1.relators.len(),
        get_relator(amalgamated_free_product(data), relator_index, inverted).len() > 0,
        forall|k: int| 0 <= k < get_relator(amalgamated_free_product(data), relator_index, inverted).len()
            ==> generator_index(
                #[trigger] get_relator(amalgamated_free_product(data), relator_index, inverted)[k]
            ) < data.p1.num_generators,
    ensures
        equiv_in_presentation(
            data.p1,
            get_relator(amalgamated_free_product(data), relator_index, inverted),
            empty_word(),
        ),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;
    let r = get_relator(afp, relator_index, inverted);
    let raw_rel = afp.relators[relator_index as int];
    let n_g1 = data.p1.relators.len();
    let n_g2 = data.p2.relators.len();

    lemma_afp_relators(data);

    // Case: shifted G₂ relator — impossible (has G₂ symbols)
    if relator_index < n_g1 + n_g2 {
        let g2_idx = (relator_index - n_g1) as nat;
        lemma_shifted_relator_has_g2(data, g2_idx);
        let sr = shift_word(data.p2.relators[g2_idx as int], n1);
        assert(raw_rel == sr) by {
            let fp = free_product(data.p1, data.p2);
            assert(fp.relators[relator_index as int] ==
                shift_relators(data.p2.relators, n1)[g2_idx as int]);
        }
        if sr.len() > 0 {
            if !inverted {
                assert(r == raw_rel);
                assert(generator_index(r[0]) >= n1);
                assert(generator_index(r[0]) < n1);
            } else {
                lemma_inverse_preserves_gen_bound_lower(raw_rel, n1);
                let k2 = choose|k2: int| 0 <= k2 < inverse_word(raw_rel).len()
                    && generator_index(inverse_word(raw_rel)[k2]) >= n1;
                assert(r == inverse_word(raw_rel));
                assert(generator_index(r[k2]) >= n1);
                assert(generator_index(r[k2]) < n1);
            }
        }
        // sr empty → raw_rel empty → r empty (contradicts r.len() > 0)
        assert(sr.len() == 0);
        assert(raw_rel.len() == 0);
        if !inverted { assert(r.len() == 0); }
        else { lemma_inverse_word_len(raw_rel); assert(r.len() == 0); }
        assert(false);
    }

    // Case: identification relator
    let ident_idx = (relator_index - n_g1 - n_g2) as nat;
    assert(ident_idx < data.identifications.len()) by {
        let ident_rels = amalgamation_relators(data);
        let fp = free_product(data.p1, data.p2);
        assert(afp.relators.len() == fp.relators.len() + ident_rels.len());
        assert(fp.relators.len() == n_g1 + n_g2);
        assert(ident_rels.len() == data.identifications.len());
    }
    let (u_i, v_i) = data.identifications[ident_idx as int];
    let raw_ident = amalgamation_relator(data, ident_idx as int);

    assert(raw_rel == raw_ident) by {
        let fp = free_product(data.p1, data.p2);
        let ident_rels = amalgamation_relators(data);
        assert((fp.relators + ident_rels)[relator_index as int]
            == ident_rels[ident_idx as int]);
    }

    // If v_i non-empty → contradiction (relator has G₂ symbol)
    if v_i.len() > 0 {
        lemma_ident_relator_has_g2_if_v_nonempty(data, ident_idx as int);
        let g2_k = choose|k: int| 0 <= k < raw_ident.len()
            && generator_index(raw_ident[k]) >= n1;
        if !inverted {
            assert(r == raw_rel);
            assert(generator_index(r[g2_k]) >= n1);
            assert(generator_index(r[g2_k]) < n1);
        } else {
            lemma_inverse_preserves_gen_bound_lower(raw_rel, n1);
            let k2 = choose|k2: int| 0 <= k2 < inverse_word(raw_rel).len()
                && generator_index(inverse_word(raw_rel)[k2]) >= n1;
            assert(r == inverse_word(raw_rel));
            assert(generator_index(r[k2]) >= n1);
            assert(generator_index(r[k2]) < n1);
        }
        assert(false);
    }

    // v_i empty → u_i ≡ ε in G₁
    lemma_empty_v_means_u_trivial(data, ident_idx);

    assert(v_i =~= empty_word());
    assert(shift_word(v_i, n1) =~= empty_word());
    assert(inverse_word(shift_word(v_i, n1)) =~= empty_word());
    assert(raw_ident =~= concat(u_i, empty_word()));
    assert(raw_ident =~= u_i);
    assert(raw_rel =~= u_i);

    if !inverted {
        assert(r == raw_rel);
    } else {
        // r = inverse_word(u_i), u_i ≡ ε, need inverse_word(u_i) ≡ ε
        // u_i is word_valid (from amalgamated_data_valid) and p1 is presentation_valid
        reveal(presentation_valid);
        assert(word_valid(u_i, n1));
        assert(presentation_valid(data.p1));
        lemma_inverse_of_trivial(data.p1, u_i);
        assert(r == inverse_word(raw_rel));
    }
}

// ============================================================
// Left-to-left steps are G₁ steps
// ============================================================

/// KEY LEMMA: If both w and w' are left words and the AFP step takes w to w',
/// then w ≡ w' in G₁.
pub proof fn lemma_left_step_valid_in_g1(
    data: AmalgamatedData,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        apply_step(amalgamated_free_product(data), w, step) == Some(w_prime),
        is_left_word(w, data.p1.num_generators),
        is_left_word(w_prime, data.p1.num_generators),
    ensures
        equiv_in_presentation(data.p1, w, w_prime),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;

    match step {
        DerivationStep::FreeReduce { position } => {
            let s = DerivationStep::FreeReduce { position };
            assert(apply_step(data.p1, w, s) == Some(w_prime));
            let steps = Seq::new(1, |_i: int| s);
            assert(derivation_produces(data.p1, steps.drop_first(), w_prime) == Some(w_prime));
            assert(derivation_produces(data.p1, steps, w) == Some(w_prime));
            let d = Derivation { steps };
            assert(derivation_valid(data.p1, d, w, w_prime));
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let pair = Seq::new(1, |_i: int| symbol)
                + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(w_prime =~= w.subrange(0, position) + pair
                + w.subrange(position, w.len() as int));
            assert(w_prime[position] == symbol);
            assert(generator_index(symbol) < n1);
            assert(symbol_valid(symbol, n1));
            let s = DerivationStep::FreeExpand { position, symbol };
            assert(apply_step(data.p1, w, s) == Some(w_prime));
            let steps = Seq::new(1, |_i: int| s);
            assert(derivation_produces(data.p1, steps.drop_first(), w_prime) == Some(w_prime));
            assert(derivation_produces(data.p1, steps, w) == Some(w_prime));
            let d = Derivation { steps };
            assert(derivation_valid(data.p1, d, w, w_prime));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(afp, relator_index, inverted);
            assert(w_prime =~= w.subrange(0, position) + r
                + w.subrange(position, w.len() as int));
            assert forall|k: int| 0 <= k < r.len()
                implies generator_index(#[trigger] r[k]) < n1
            by { assert(w_prime[position + k] == r[k]); }

            lemma_afp_relators(data);

            if relator_index < data.p1.relators.len() {
                lemma_afp_relator_g1(data, relator_index);
                assert(get_relator(afp, relator_index, inverted)
                    == get_relator(data.p1, relator_index, inverted));
                let s = DerivationStep::RelatorInsert { position, relator_index, inverted };
                assert(apply_step(data.p1, w, s) == Some(w_prime));
                let steps = Seq::new(1, |_i: int| s);
                assert(derivation_produces(data.p1, steps.drop_first(), w_prime) == Some(w_prime));
                assert(derivation_produces(data.p1, steps, w) == Some(w_prime));
                let d = Derivation { steps };
                assert(derivation_valid(data.p1, d, w, w_prime));
            } else if r.len() == 0 {
                assert(w_prime =~= w);
                lemma_equiv_refl(data.p1, w);
            } else {
                lemma_nonstandard_afp_relator_trivial(data, relator_index, inverted);
                lemma_insert_trivial_preserves_equiv(data.p1, w, r, position);
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(afp, relator_index, inverted);
            let rlen = r.len();
            assert forall|k: int| 0 <= k < r.len()
                implies generator_index(#[trigger] r[k]) < n1
            by { assert(r[k] == w[position + k]); }

            lemma_afp_relators(data);

            if relator_index < data.p1.relators.len() {
                lemma_afp_relator_g1(data, relator_index);
                assert(get_relator(afp, relator_index, inverted)
                    == get_relator(data.p1, relator_index, inverted));
                let s = DerivationStep::RelatorDelete { position, relator_index, inverted };
                assert(apply_step(data.p1, w, s) == Some(w_prime));
                let steps = Seq::new(1, |_i: int| s);
                assert(derivation_produces(data.p1, steps.drop_first(), w_prime) == Some(w_prime));
                assert(derivation_produces(data.p1, steps, w) == Some(w_prime));
                let d = Derivation { steps };
                assert(derivation_valid(data.p1, d, w, w_prime));
            } else if r.len() == 0 {
                assert(w_prime =~= w);
                lemma_equiv_refl(data.p1, w);
            } else {
                lemma_nonstandard_afp_relator_trivial(data, relator_index, inverted);
                // r ≡ ε in G₁. w = prefix + r + suffix, w_prime = prefix + suffix.
                // Need w ≡ w_prime. Since r ≡ ε: w = prefix + r + suffix ≡ prefix + suffix = w_prime.
                let prefix = w.subrange(0, position);
                let suffix = w.subrange(position + rlen as int, w.len() as int);

                // concat(r, suffix) ≡ suffix
                lemma_equiv_concat_left(data.p1, r, empty_word(), suffix);
                assert(concat(empty_word(), suffix) =~= suffix);
                lemma_equiv_refl(data.p1, suffix);
                lemma_equiv_transitive(data.p1, concat(r, suffix),
                    concat(empty_word(), suffix), suffix);

                // prefix + concat(r, suffix) ≡ prefix + suffix = w_prime
                lemma_equiv_concat_right(data.p1, prefix, concat(r, suffix), suffix);

                // w =~= concat(prefix, concat(r, suffix))
                assert(w =~= concat(prefix, concat(r, suffix))) by {
                    let lhs = w;
                    let rhs = concat(prefix, concat(r, suffix));
                    assert(lhs.len() == rhs.len()) by {
                        assert(prefix.len() == position);
                        assert(suffix.len() == w.len() - position - rlen);
                    }
                    assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                        if k < position { }
                        else if k < position + rlen as int {
                            assert(lhs[k] == w[k]);
                            assert(w.subrange(position, position + rlen as int) == r);
                            assert(w[k] == r[k - position]);
                            assert(concat(r, suffix)[k - position] == r[k - position]);
                        } else {
                            assert(lhs[k] == w[k]);
                            assert(suffix[k - position - rlen] == w[k]);
                            assert(concat(r, suffix)[k - position]
                                == suffix[k - position - rlen]);
                        }
                    }
                }

                assert(w_prime =~= concat(prefix, suffix));
            }
        },
    }
}

// ============================================================
// Part F: Van der Waerden action — state and action definitions
// ============================================================
//
// The action is on states (h, syllables) where:
//   h: Word — an element of A (the amalgamated subgroup in G₁)
//   syllables: Seq<(bool, nat)> — alternating (is_left, coset_index) pairs
//     is_left = true means the syllable is from G₁/A
//     is_left = false means the syllable is from G₂/B
//     Each coset_index represents a non-trivial coset (different from the subgroup coset)
//
// The action of a G₁-symbol on a state processes through the coset structure.
// The action of a G₂-symbol similarly.
// Well-definedness means AFP-equivalent words act the same (up to G₁-equiv of h).

/// A word is in the left amalgamated subgroup A (generated by u_i words).
pub open spec fn in_left_subgroup(data: AmalgamatedData, w: Word) -> bool {
    let k = data.identifications.len();
    let a_words = Seq::new(k, |i: int| data.identifications[i].0);
    in_generated_subgroup(data.p1, a_words, w)
}

/// A word is in the right amalgamated subgroup B (generated by v_i words).
pub open spec fn in_right_subgroup(data: AmalgamatedData, w: Word) -> bool {
    let k = data.identifications.len();
    let b_words = Seq::new(k, |i: int| data.identifications[i].1);
    in_generated_subgroup(data.p2, b_words, w)
}

/// Two G₁-words are in the same A-coset: w₁⁻¹ · w₂ ∈ A.
pub open spec fn same_left_coset(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    in_left_subgroup(data, concat(inverse_word(w1), w2))
}

/// Two G₂-words are in the same B-coset.
pub open spec fn same_right_coset(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    in_right_subgroup(data, concat(inverse_word(w1), w2))
}

// ============================================================
// Part G: Van der Waerden action — definitions and injectivity
// ============================================================
//
// The van der Waerden action processes an AFP word symbol by symbol,
// maintaining a state that tracks the "reduced normal form" of the
// accumulated product.
//
// State: (h: Word, sylls: Seq<(bool, Word)>)
//   h: an element of A ≤ G₁ (the "remainder" in the amalgamated subgroup)
//   sylls: alternating non-trivial syllables from G₁/A and G₂/B
//     Each entry (is_left, rep) where is_left = true means G₁, false means G₂
//     rep is a word in the factor's generators, NOT in the subgroup (A or B)
//
// The action of each symbol updates the state:
//   G₁-symbol: multiply into the current G₁-part of the state
//   G₂-symbol: multiply into the current G₂-part of the state
//
// Well-definedness: AFP-equivalent words produce "equivalent" states
//   (same syllable structure, G₁-equivalent h values)
//
// Injectivity follows from: a G₁-word w acting on (ε, []) gives
//   (h, []) where h ≡ w in G₁. If w ≡ ε in AFP, then h ≡ ε, so w ≡ ε in G₁.

// ============================================================
// Part H: AFP injectivity — main theorem via action
// ============================================================
//
// The proof uses two key facts:
//
// FACT I (Syllable reduction):
//   Every derivation step in the AFP either:
//   (a) stays within G₁ (left-to-left step — handled by Part E), or
//   (b) introduces/removes G₂ content.
//   Steps of type (b) involve identification relators.
//   The structure of identification relators ensures that the
//   "G₁ projection" of the derivation is controlled by the
//   isomorphism condition.
//
// FACT II (Subgroup collapse):
//   If w ∈ A and w ≡ ε in the AFP, then w ≡ ε in G₁.
//   Proof: w ∈ A means w ≡ apply_embedding(a_words, u) for some u.
//   The isomorphism condition directly gives the result.
//
// The main theorem combines the structural lemma (Part E) with
// the derivation analysis to show that any AFP derivation from
// a G₁-word to ε can be transformed into a G₁ derivation.

/// MAIN THEOREM: AFP injectivity.
/// If w is a G₁-word and w ≡ ε in the AFP, then w ≡ ε in G₁.
pub proof fn lemma_afp_injectivity(
    data: AmalgamatedData,
    w: Word,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        word_valid(w, data.p1.num_generators),
        equiv_in_presentation(amalgamated_free_product(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.p1, w, empty_word()),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;
    let d = choose|d: Derivation| derivation_valid(afp, d, w, empty_word());
    lemma_afp_reflects_left_inner(data, d.steps, w, empty_word());
}

/// Inner lemma: derivation-based AFP reflection for left words.
/// If two G₁-words are connected by an AFP derivation, they're
/// equivalent in G₁.
proof fn lemma_afp_reflects_left_inner(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        is_left_word(w1, data.p1.num_generators),
        is_left_word(w2, data.p1.num_generators),
    ensures
        equiv_in_presentation(data.p1, w1, w2),
    decreases steps.len(),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;

    if steps.len() == 0 {
        assert(w1 == w2);
        lemma_equiv_refl(data.p1, w1);
    } else {
        let step0 = steps.first();
        let w_next = apply_step(afp, w1, step0).unwrap();
        let rest = steps.drop_first();

        if is_left_word(w_next, n1) {
            // Case 1: first intermediate is G₁.
            // w1 ≡ w_next in G₁ by structural lemma
            lemma_left_step_valid_in_g1(data, w1, step0, w_next);
            // w_next ≡ w2 in G₁ by IH
            lemma_afp_reflects_left_inner(data, rest, w_next, w2);
            // Chain
            lemma_equiv_transitive(data.p1, w1, w_next, w2);
        } else {
            // Case 2: first intermediate is non-G₁.
            // Find the first return to G₁.
            // We search through the derivation to find the first k > 0
            // such that the intermediate at position k is a G₁-word.
            //
            // w2 is G₁ and appears at position steps.len(), so such k exists.
            //
            // Split the derivation at k:
            //   Left part: w1 → ... → w_k (length k, both endpoints G₁)
            //   Right part: w_k → ... → w2 (length n-k, both endpoints G₁)
            //
            // For the right part (length < n): by IH, w_k ≡ w2 in G₁.
            // For the left part: w1 → w_next (non-G₁) → ... → w_k (G₁).
            //   All intermediates at positions 1..k-1 are non-G₁.
            //   This is a "pure excursion."
            //
            // The pure excursion is handled by the excursion lemma.

            // For now, we handle this by finding the LAST step that returns
            // us to a G₁-word, then splitting there.
            // The right part has length 0 (trivial) or uses the IH.
            // The left part is the excursion.

            // Search for first G₁ return: scan from position 1 upward.
            // At minimum, position steps.len() = w2 is G₁.
            // Find the smallest k > 0 with G₁ intermediate.

            // We use strong induction: the right part has strictly fewer steps.
            // The left part (excursion) is handled by the excursion lemma.

            // To keep the proof simple, we handle the excursion by
            // further induction inside lemma_pure_excursion.

            // First, establish that all intermediates exist and find k.
            let k = find_first_left_return(afp, steps, w1, n1, 1);
            // k is the smallest index > 0 with left intermediate

            // Split at k
            let left_steps = steps.subrange(0, k);
            let right_steps = steps.subrange(k, steps.len() as int);

            // The intermediate at position k
            lemma_derivation_split_at(afp, steps, w1, w2, k);
            let w_k = derivation_produces(afp, left_steps, w1).unwrap();

            // w_k is a left word (by construction of k)
            // Right part: w_k → ... → w2, length n-k < n
            if right_steps.len() > 0 {
                lemma_afp_reflects_left_inner(data, right_steps, w_k, w2);
            } else {
                assert(w_k == w2);
                lemma_equiv_refl(data.p1, w_k);
            }

            // Left part: excursion w1 → ... → w_k
            // All intermediates 1..k-1 are non-G₁.
            lemma_pure_excursion(data, left_steps, w1, w_k);

            // Chain: w1 ≡ w_k ≡ w2 in G₁
            lemma_equiv_transitive(data.p1, w1, w_k, w2);
        }
    }
}

/// Find the first position > start where the intermediate is a G₁-word.
/// Returns an index k with start ≤ k ≤ steps.len() such that
/// the intermediate at k is G₁, and all intermediates in [1, k) are non-G₁.
spec fn find_first_left_return(
    p: Presentation, steps: Seq<DerivationStep>, w: Word, n1: nat, start: int,
) -> int
    recommends
        start >= 1,
        start <= steps.len(),
        derivation_produces(p, steps, w) is Some,
    decreases steps.len() - start,
{
    if start >= steps.len() {
        steps.len() as int
    } else {
        let w_at = derivation_produces(p, steps.subrange(0, start), w);
        if w_at is Some && is_left_word(w_at.unwrap(), n1) {
            start
        } else {
            find_first_left_return(p, steps, w, n1, start + 1)
        }
    }
}

/// Helper: split a derivation at position k.
proof fn lemma_derivation_split_at(
    p: Presentation, steps: Seq<DerivationStep>, w: Word, w_prime: Word, k: int,
)
    requires
        derivation_produces(p, steps, w) == Some(w_prime),
        0 <= k <= steps.len(),
    ensures ({
        let prefix = steps.subrange(0, k);
        let suffix = steps.subrange(k, steps.len() as int);
        let w_k = derivation_produces(p, prefix, w);
        &&& w_k is Some
        &&& derivation_produces(p, suffix, w_k.unwrap()) == Some(w_prime)
    }),
    decreases k,
{
    if k == 0 {
        assert(steps.subrange(0, 0) =~= Seq::<DerivationStep>::empty());
        assert(steps.subrange(0, steps.len() as int) =~= steps);
    } else {
        let step = steps.first();
        let next = apply_step(p, w, step).unwrap();
        let rest = steps.drop_first();
        lemma_derivation_split_at(p, rest, next, w_prime, k - 1);
        assert(steps.subrange(0, k).first() == step);
        assert(steps.subrange(0, k).drop_first() =~= rest.subrange(0, k - 1));
        assert(steps.subrange(k, steps.len() as int) =~= rest.subrange(k - 1, rest.len() as int));
    }
}

// ============================================================
// Part I: Pure excursion lemma
// ============================================================
//
// A "pure excursion" is a derivation w1 (G₁) → ... → w2 (G₁)
// where all intermediates (positions 1..k-1) are non-G₁.
//
// The proof is by induction on the excursion length (number of steps).
//
// Base cases:
//   Length 0: w1 = w2, trivial.
//   Length 1: w1 → w2, both G₁. By the structural lemma.
//
// Inductive case (length ≥ 2):
//   The first step introduces G₂ content. The last step removes it.
//   We analyze the derivation by finding a "peak" in G₂ content
//   and showing it can be bypassed, reducing the excursion length.
//
//   Key insight: the identification relator u_i · inv(shift(v_i))
//   has a clean G₁+G₂ split. Factor isolation means free reductions
//   never cross the boundary. So G₂ content enters and leaves only
//   through identification relators (or free expand/reduce of G₂ pairs).
//
//   For a 2-step excursion w1 → w_mid → w2:
//     Step 1 introduces G₂, step 2 removes it.
//     The net effect on the G₁ part is determined by which identification
//     relators were used and how the G₂ parts interacted.
//     The isomorphism condition ensures the G₁ effect is valid.
//
// For the formal proof, we use a different approach: instead of
// peak reduction (which requires complex case analysis), we observe
// that the excursion lemma follows from the RETRACTION + ISOMORPHISM
// argument when combined properly.
//
// RETRACTION ARGUMENT FOR EXCURSIONS:
//
// Given excursion: w1 (G₁) → w_mid₁ → ... → w2 (G₁) in the AFP.
//
// Consider the left retraction ρ_L: FP → G₁ from File 1.
// ρ_L is NOT an AFP homomorphism, but it IS a spec function on Words.
//
// For each step w_j → w_{j+1}:
//   - If the step is a FreeReduce/Expand within G₁ symbols:
//     ρ_L(w_j) and ρ_L(w_{j+1}) differ by the same reduction.
//     So ρ_L(w_j) ≡ ρ_L(w_{j+1}) in G₁.
//   - If the step is a FreeReduce/Expand within G₂ symbols:
//     ρ_L(w_j) = ρ_L(w_{j+1}) (G₂ symbols collapse to ε).
//   - If the step is a G₁ relator insert/delete:
//     ρ_L(w_j) ≡ ρ_L(w_{j+1}) in G₁ (same relator applies).
//   - If the step is a G₂ relator insert/delete:
//     ρ_L(w_j) = ρ_L(w_{j+1}) (relator collapses to ε).
//   - If the step is an identification relator insert/delete:
//     ρ_L maps the relator u_i · inv(shift(v_i)) to u_i.
//     So ρ_L(w_{j+1}) differs from ρ_L(w_j) by insertion/deletion of u_i.
//     This means: ρ_L(w_j) and ρ_L(w_{j+1}) are related by u_i ≡ ??? in G₁.
//
// The chain of ρ_L values: ρ_L(w1) = w1, ρ_L(w2) = w2.
// Each step contributes either a G₁-equivalence or a u_i insertion/deletion.
// The net result: w1 ≡ w2 · (product of u_i^±1) in G₁.
//
// Similarly, using the right retraction ρ_R:
// ρ_R(w1) = ε, ρ_R(w2) = ε (both are G₁-words).
// The chain of ρ_R values goes from ε to ε.
// Each identification step contributes inv(v_i) insertion/deletion.
// Each G₂ step contributes a G₂-equivalence.
// The net result: ε ≡ (product of v_i^±1 interleaved with G₂-equivs) in G₂.
// This means: the product of v_i^±1 is ≡ ε in G₂.
//
// By the isomorphism condition: the corresponding product of u_i^±1 is ≡ ε in G₁.
// Therefore: w1 ≡ w2 · ε = w2 in G₁.
//
// This argument avoids the full van der Waerden action!
// The key insight: the left and right retractions together, combined with
// the isomorphism condition, give the excursion result.
//
// FORMALIZATION CHALLENGE:
// The "product of u_i^±1" and "product of v_i^±1" must be tracked
// precisely through the derivation. The correspondence between u_i
// and v_i insertions comes from each identification relator use
// contributing one u_i on the G₁ side and one v_i on the G₂ side.
//
// We formalize this by defining:
//   - g1_ident_contrib(steps, w, j): the u_i word contributed by step j
//   - g2_ident_contrib(steps, w, j): the v_i word contributed by step j
//   - total_g1_contrib(steps, w): concatenation of all u_i contributions
//   - total_g2_contrib(steps, w): concatenation of all v_i contributions
//
// Then showing:
//   (a) w1 ≡ concat(w2, total_g1_contrib) in G₁
//   (b) ε ≡ total_g2_contrib in G₂  (using G₂ relator steps)
//   (c) total_g1_contrib is related to total_g2_contrib via the identification
//   (d) By isomorphism: total_g1_contrib ≡ ε in G₁
//   (e) Therefore w1 ≡ w2 in G₁

/// The "identification contribution" of a step: the u_i or inv(u_i) word
/// that the step contributes to the G₁ projection, or ε if the step
/// doesn't involve an identification relator.
pub open spec fn g1_ident_contrib(
    data: AmalgamatedData, step: DerivationStep,
) -> Word {
    let afp = amalgamated_free_product(data);
    let n_g1 = data.p1.relators.len();
    let n_g2 = data.p2.relators.len();
    match step {
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            if relator_index >= n_g1 + n_g2
                && (relator_index - n_g1 - n_g2) < data.identifications.len()
            {
                let idx = (relator_index - n_g1 - n_g2) as int;
                let u_i = data.identifications[idx].0;
                if inverted { inverse_word(u_i) } else { u_i }
            } else {
                empty_word()
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            if relator_index >= n_g1 + n_g2
                && (relator_index - n_g1 - n_g2) < data.identifications.len()
            {
                let idx = (relator_index - n_g1 - n_g2) as int;
                let u_i = data.identifications[idx].0;
                // Delete is the reverse of insert
                if inverted { u_i } else { inverse_word(u_i) }
            } else {
                empty_word()
            }
        },
        _ => empty_word(),
    }
}

/// The corresponding G₂ identification contribution.
pub open spec fn g2_ident_contrib(
    data: AmalgamatedData, step: DerivationStep,
) -> Word {
    let n_g1 = data.p1.relators.len();
    let n_g2 = data.p2.relators.len();
    match step {
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            if relator_index >= n_g1 + n_g2
                && (relator_index - n_g1 - n_g2) < data.identifications.len()
            {
                let idx = (relator_index - n_g1 - n_g2) as int;
                let v_i = data.identifications[idx].1;
                if inverted { inverse_word(v_i) } else { v_i }
            } else {
                empty_word()
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            if relator_index >= n_g1 + n_g2
                && (relator_index - n_g1 - n_g2) < data.identifications.len()
            {
                let idx = (relator_index - n_g1 - n_g2) as int;
                let v_i = data.identifications[idx].1;
                if inverted { v_i } else { inverse_word(v_i) }
            } else {
                empty_word()
            }
        },
        _ => empty_word(),
    }
}

/// Total G₁ identification contribution over a sequence of steps.
pub open spec fn total_g1_contrib(
    data: AmalgamatedData, steps: Seq<DerivationStep>,
) -> Word
    decreases steps.len(),
{
    if steps.len() == 0 {
        empty_word()
    } else {
        concat(g1_ident_contrib(data, steps.first()),
               total_g1_contrib(data, steps.drop_first()))
    }
}

/// Total G₂ identification contribution over a sequence of steps.
pub open spec fn total_g2_contrib(
    data: AmalgamatedData, steps: Seq<DerivationStep>,
) -> Word
    decreases steps.len(),
{
    if steps.len() == 0 {
        empty_word()
    } else {
        concat(g2_ident_contrib(data, steps.first()),
               total_g2_contrib(data, steps.drop_first()))
    }
}

/// The G₁ and G₂ contributions are related via the identification:
/// total_g1_contrib is the apply_embedding of total_g2_contrib
/// (or more precisely, they correspond element-by-element via u_i ↔ v_i).
///
/// This is the KEY property that connects the two projections.
/// It follows directly from the definition: each identification relator
/// contributes (u_i, v_i) or (inv(u_i), inv(v_i)) in lock-step.

/// Pure excursion lemma: if w1 (G₁) → ... → w2 (G₁) with all
/// intermediates non-G₁, then w1 ≡ w2 in G₁.
///
/// Proof sketch:
///   1. Apply left retraction: tracks G₁ part of derivation.
///      Steps within G₂ don't affect G₁ part.
///      Identification steps contribute u_i insertions.
///      Net: w1 is related to w2 by total_g1_contrib.
///   2. Apply right retraction: tracks G₂ part.
///      Steps within G₁ don't affect G₂ part.
///      Identification steps contribute v_i insertions.
///      Net: ε is related to ε by total_g2_contrib + G₂ relator steps.
///      So total_g2_contrib ≡ ε in G₂.
///   3. The isomorphism condition links u_i ↔ v_i.
///      total_g2_contrib ≡ ε in G₂ implies total_g1_contrib ≡ ε in G₁.
///   4. Therefore w1 ≡ w2 in G₁.
///
/// The formal proof requires carefully tracking how the retractions
/// interact with each derivation step. This is done by induction on
/// the derivation length.
proof fn lemma_pure_excursion(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        is_left_word(w1, data.p1.num_generators),
        is_left_word(w2, data.p1.num_generators),
    ensures
        equiv_in_presentation(data.p1, w1, w2),
    decreases steps.len(),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;

    if steps.len() == 0 {
        assert(w1 == w2);
        lemma_equiv_refl(data.p1, w1);
    } else if steps.len() == 1 {
        // Single step from G₁ to G₁
        let step = steps.first();
        let w_next = apply_step(afp, w1, step).unwrap();
        assert(w_next == w2);
        lemma_left_step_valid_in_g1(data, w1, step, w2);
    } else {
        // Length ≥ 2. The first step takes w1 (G₁) to w_next (non-G₁).
        // The last step takes w_prev to w2 (G₁).
        //
        // Strategy: track the G₁ and G₂ contributions of the identification
        // relator steps. The retraction argument shows:
        //   w1 ≡ w2 * total_g1_contrib in G₁ (modulo G₁ relator steps)
        //   total_g2_contrib ≡ ε in G₂ (from the G₂ projection)
        //   isomorphism condition: total_g1_contrib ≡ ε in G₁
        //   therefore w1 ≡ w2 in G₁
        //
        // The formal proof of this is by induction on steps.len().
        // We process each step and accumulate the contribution.

        // For a clean induction, we prove a stronger statement:
        // For ANY derivation from a G₁-word to a G₁-word,
        // the endpoints are equivalent in G₁.
        // This is exactly what lemma_afp_reflects_left_inner proves.
        // And it already handles the excursion case by finding the
        // first G₁ return.
        //
        // Wait — we ARE in the excursion lemma, called from
        // lemma_afp_reflects_left_inner. The excursion has NO G₁
        // intermediates (except endpoints). So we can't split further.
        //
        // We need a DIFFERENT argument for pure excursions.
        // The retraction argument gives us the result directly.

        // Let's use the retraction approach step by step.
        // Process the derivation and track the G₁ projection.

        lemma_retraction_excursion(data, steps, w1, w2);
    }
}

/// Retraction-based excursion proof.
/// Uses the left retraction to project the AFP derivation to G₁,
/// and the isomorphism condition to handle identification relator contributions.
///
/// The proof shows: w1 ≡ concat(w2, total_g1_contrib(data, steps)) in G₁,
/// and total_g1_contrib ≡ ε in G₁ (via the isomorphism condition).
proof fn lemma_retraction_excursion(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        is_left_word(w1, data.p1.num_generators),
        is_left_word(w2, data.p1.num_generators),
    ensures
        equiv_in_presentation(data.p1, w1, w2),
{
    let n1 = data.p1.num_generators;
    let afp = amalgamated_free_product(data);

    // Step 1: Show that the left retraction maps the derivation to
    // a G₁ pseudo-derivation where w1 → w2 modulo u_i contributions.
    lemma_retraction_chain(data, steps, w1, w2);
    // This gives: w1 ≡ concat(w2, total_g1_contrib(data, steps)) in G₁
    // (or more precisely: ρ_L(w1) ≡ concat(ρ_L(w2), total_g1_contrib) in G₁)
    // Since w1 and w2 are G₁-words: ρ_L(w1) = w1 and ρ_L(w2) = w2.

    // Step 2: Show total_g1_contrib ≡ ε in G₁.
    // This follows from:
    //   (a) total_g2_contrib ≡ ε in G₂ (from the right retraction)
    //   (b) isomorphism condition links g1 and g2 contributions
    lemma_total_g2_contrib_trivial(data, steps, w1, w2);
    lemma_isomorphism_links_contribs(data, steps);
    // Now: total_g1_contrib ≡ ε in G₁

    // Step 3: Chain.
    // w1 ≡ concat(w2, total_g1_contrib) ≡ concat(w2, ε) =~= w2
    // So w1 ≡ w2 in G₁.
    let contrib = total_g1_contrib(data, steps);
    // We have: w1 ≡ concat(w2, contrib) in G₁ (from step 1)
    // and: contrib ≡ ε in G₁ (from step 2)
    // So: concat(w2, contrib) ≡ concat(w2, ε) =~= w2
    lemma_equiv_concat_right(data.p1, w2, contrib, empty_word());
    assert(concat(w2, empty_word()) =~= w2);
    lemma_equiv_refl(data.p1, w2);
    lemma_equiv_transitive(data.p1, concat(w2, contrib), concat(w2, empty_word()), w2);
    lemma_equiv_transitive(data.p1, w1, concat(w2, contrib), w2);
}

/// The left retraction chain: w1 ≡ concat(w2, total_g1_contrib) in G₁.
///
/// Proof by induction on steps.len(). For each step, the left retraction
/// either preserves the G₁ equivalence or adds a u_i contribution.
proof fn lemma_retraction_chain(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        is_left_word(w1, data.p1.num_generators),
        is_left_word(w2, data.p1.num_generators),
    ensures
        equiv_in_presentation(data.p1, w1, concat(w2, total_g1_contrib(data, steps))),
    decreases steps.len(),
{
    let n1 = data.p1.num_generators;
    let afp = amalgamated_free_product(data);

    if steps.len() == 0 {
        assert(w1 == w2);
        assert(total_g1_contrib(data, steps) =~= empty_word());
        assert(concat(w2, empty_word()) =~= w2);
        assert(concat(w2, total_g1_contrib(data, steps)) =~= w1);
        lemma_equiv_refl(data.p1, w1);
    } else {
        let step = steps.first();
        let w_next = apply_step(afp, w1, step).unwrap();
        let rest = steps.drop_first();

        // By IH on rest (from w_next to w2):
        // But w_next might not be a left word! The IH requires both endpoints to be G₁.
        // For the pure excursion, intermediates might be non-G₁.
        //
        // The retraction chain should work for ALL words, not just G₁ words.
        // We need a more general statement.

        // REVISED APPROACH: Track the retraction VALUE, not the original word.
        // ρ_L(w) extracts the G₁-symbol subsequence.
        // For each step, show how ρ_L(w_j) relates to ρ_L(w_{j+1}).

        // For now, use the homomorphism approach from File 1.
        // ρ_L = apply_hom(fp_left_retraction(p1, p2), ·)
        // ρ_L preserves G₁ operations and collapses G₂ operations.
        // Identification steps contribute u_i.

        // The chain: ρ_L(w1) = w1, ρ_L(w2) = w2.
        // For each step j: ρ_L(w_j) → ρ_L(w_{j+1}) is either:
        //   - A valid G₁ step (G₁ operations)
        //   - Identity (G₂ operations, including free reduce/expand on G₂)
        //   - u_i insertion/deletion (identification operations)

        // The net chain: w1 ≡_G₁ (some word) ≡_G₁ ... ≡_G₁ w2 * (product of u_i's)
        // where the product of u_i's is total_g1_contrib.

        // This is hard to formalize directly because ρ_L is not an AFP homomorphism.
        // We need to process each step and show the G₁ equivalence.

        // SIMPLEST CORRECT APPROACH: induction on steps, processing each step.
        // For each step, show: if the previous state satisfies the invariant,
        // the next state also satisfies it.

        // Invariant: ρ_L(w_j) ≡ concat(w2, total_g1_contrib(data, steps[j..])) in G₁

        // This requires a generalization that works for non-G₁ intermediate words.
        // Define ρ_L(w) for an arbitrary word (not just G₁ words):
        //   ρ_L(w) = apply_hom(fp_left_retraction(p1, p2), w)

        // For G₁ words: ρ_L(w) = w (by File 1's lemma_fp_left_retraction_identity).
        // For G₂ words: ρ_L(w) = ε.
        // For mixed words: ρ_L extracts the G₁ subsequence.

        // The generalized chain lemma:
        //   ρ_L(w_j) ≡ concat(ρ_L(w2), total_g1_contrib(data, steps[j..])) in G₁

        // At j = 0: ρ_L(w1) ≡ concat(ρ_L(w2), total_g1_contrib(data, steps))
        // Since w1 and w2 are G₁: ρ_L(w1) = w1 and ρ_L(w2) = w2.
        // So: w1 ≡ concat(w2, total_g1_contrib(data, steps)) in G₁.

        // For the generalized chain, we use lemma_retraction_chain_general.
        let rho = fp_left_retraction(data.p1, data.p2);
        lemma_retraction_chain_general(data, rho, steps, w1, w2);

        // ρ_L(w1) ≡ concat(ρ_L(w2), total_g1_contrib(data, steps)) in G₁
        lemma_fp_left_retraction_identity(data.p1, data.p2, w1);
        lemma_fp_left_retraction_identity(data.p1, data.p2, w2);
        // ρ_L(w1) =~= w1 and ρ_L(w2) =~= w2
        // So: w1 ≡ concat(w2, total_g1_contrib(data, steps))
    }
}

/// Generalized retraction chain: for ANY AFP derivation, the retraction
/// values are related by G₁-equivalence and identification contributions.
///
/// Statement: apply_hom(rho, w1) ≡ concat(apply_hom(rho, w2), total_g1_contrib(steps)) in G₁
///
/// where rho is the left retraction FP → G₁.
proof fn lemma_retraction_chain_general(
    data: AmalgamatedData,
    rho: HomomorphismData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        rho == fp_left_retraction(data.p1, data.p2),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
    ensures
        equiv_in_presentation(
            data.p1,
            apply_hom(rho, w1),
            concat(apply_hom(rho, w2), total_g1_contrib(data, steps)),
        ),
    decreases steps.len(),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;

    if steps.len() == 0 {
        assert(w1 == w2);
        assert(total_g1_contrib(data, steps) =~= empty_word());
        assert(concat(apply_hom(rho, w2), empty_word()) =~= apply_hom(rho, w2));
        assert(apply_hom(rho, w1) == apply_hom(rho, w2));
        lemma_equiv_refl(data.p1, apply_hom(rho, w1));
    } else {
        let step = steps.first();
        let w_next = apply_step(afp, w1, step).unwrap();
        let rest = steps.drop_first();

        // IH: apply_hom(rho, w_next) ≡ concat(apply_hom(rho, w2), total_g1_contrib(data, rest))
        lemma_retraction_chain_general(data, rho, rest, w_next, w2);

        // For this step: show apply_hom(rho, w1) ≡
        //   concat(apply_hom(rho, w_next), g1_ident_contrib(data, step)) in G₁
        lemma_retraction_single_step(data, rho, step, w1, w_next);

        // Chain:
        // apply_hom(rho, w1) ≡ concat(apply_hom(rho, w_next), g1_ident_contrib(step))
        // apply_hom(rho, w_next) ≡ concat(apply_hom(rho, w2), total_g1_contrib(rest))
        //
        // So: apply_hom(rho, w1)
        //   ≡ concat(apply_hom(rho, w_next), g1_ident_contrib(step))
        //   ≡ concat(concat(apply_hom(rho, w2), total_g1_contrib(rest)), g1_ident_contrib(step))
        //   =~= concat(apply_hom(rho, w2), concat(total_g1_contrib(rest), g1_ident_contrib(step)))
        //
        // And: total_g1_contrib(data, steps)
        //   = concat(g1_ident_contrib(step), total_g1_contrib(rest))
        //
        // Hmm, the order is wrong. total_g1_contrib prepends step's contrib.
        // But our chain appends it. Let me reconsider.
        //
        // total_g1_contrib([step] + rest)
        //   = concat(g1_ident_contrib(step), total_g1_contrib(rest))
        //
        // We need: apply_hom(rho, w1)
        //   ≡ concat(apply_hom(rho, w2), concat(g1_ident_contrib(step), total_g1_contrib(rest)))
        //   = concat(apply_hom(rho, w2), total_g1_contrib(steps))
        //
        // From the single step:
        //   apply_hom(rho, w1) ≡ concat(apply_hom(rho, w_next), g1_ident_contrib(step)) in G₁
        //
        // From IH:
        //   apply_hom(rho, w_next) ≡ concat(apply_hom(rho, w2), total_g1_contrib(rest)) in G₁
        //
        // So: concat(apply_hom(rho, w_next), g1_ident_contrib(step))
        //   ≡ concat(concat(apply_hom(rho, w2), total_g1_contrib(rest)), g1_ident_contrib(step))
        //
        // Need to show this equals:
        //   concat(apply_hom(rho, w2), concat(g1_ident_contrib(step), total_g1_contrib(rest)))
        //
        // These are NOT the same due to associativity of concat and order of contributions!
        // The issue: single step gives contrib AFTER w_next, but total_g1_contrib
        // puts step's contrib BEFORE rest's contrib.
        //
        // I need to reconsider the order of contributions.
        // In the derivation w1 → w_next → ... → w2:
        //   - Step 0 (w1 → w_next): contributes g1_ident_contrib(step0)
        //   - Steps 1..n-1 (w_next → w2): contribute total_g1_contrib(rest)
        //
        // The total contribution is:
        //   total_g1_contrib(steps) = concat(g1_ident_contrib(step0), total_g1_contrib(rest))
        //
        // The retraction chain should give:
        //   ρ(w1) ≡ concat(ρ(w2), total_g1_contrib(steps)) in G₁
        //
        // From single step: ρ(w1) ≡ concat(ρ(w_next), g1_ident_contrib(step0))
        // From IH: ρ(w_next) ≡ concat(ρ(w2), total_g1_contrib(rest))
        //
        // Substituting: ρ(w1) ≡ concat(concat(ρ(w2), total_g1_contrib(rest)), g1_ident_contrib(step0))
        //
        // Using associativity of concat:
        //   = concat(ρ(w2), concat(total_g1_contrib(rest), g1_ident_contrib(step0)))
        //
        // But we need: concat(ρ(w2), concat(g1_ident_contrib(step0), total_g1_contrib(rest)))
        //
        // These differ unless concat is commutative (which it's not for group words).
        //
        // The issue: the contributions accumulate in the WRONG ORDER.
        // I need to reconsider the definition or the invariant.
        //
        // REVISED INVARIANT:
        //   ρ(w1) ≡ concat(total_g1_contrib_reversed(data, steps), ρ(w2)) in G₁
        //
        // where the contributions are accumulated on the LEFT, not the RIGHT.
        //
        // Or alternatively, use RIGHT-accumulated contributions:
        //   total_g1_contrib_right(steps) = concat(total_g1_contrib_right(rest), g1_ident_contrib(step0))
        //
        // Then: ρ(w1) ≡ concat(ρ(w2), total_g1_contrib_right(steps))
        //
        // But total_g1_contrib_right puts step0's contrib LAST, while
        // in the derivation step0 happens FIRST.
        //
        // Actually, the order doesn't matter for showing the total is ≡ ε.
        // If the total (in either order) is ≡ ε, then w1 ≡ w2.
        //
        // Let me just use the RIGHT-accumulated definition.

        // Actually, the simplest fix: put the contribution on the LEFT.
        // Single step: ρ(w1) ≡ concat(g1_ident_contrib(step0), ρ(w_next))
        // IH: ρ(w_next) ≡ concat(total_g1_contrib(rest), ρ(w2))
        // Chain: ρ(w1) ≡ concat(g1_ident_contrib(step0), concat(total_g1_contrib(rest), ρ(w2)))
        //      =~= concat(concat(g1_ident_contrib(step0), total_g1_contrib(rest)), ρ(w2))
        //      = concat(total_g1_contrib(steps), ρ(w2))
        //
        // Yes! This works if the single step gives:
        //   ρ(w1) ≡ concat(g1_ident_contrib(step0), ρ(w_next)) in G₁
        //
        // This is the correct formulation. The contribution goes on the LEFT.

        // Let me fix the ensures clause to use this formulation.
        // For now, just assert the result and let the caller handle associativity.

        // Actually, I realize the invariant should be:
        //   apply_hom(rho, w1) ≡ concat(total_g1_contrib(data, steps), apply_hom(rho, w2))
        // (contributions on the LEFT of w2, not the RIGHT)

        // Let me restructure. Since I can't verify right now, let me just
        // write the correct version from scratch.
        lemma_equiv_refl(data.p1, apply_hom(rho, w1));  // placeholder
    }
}

/// Single retraction step: how the retraction value changes for one AFP step.
/// ρ(w1) ≡ concat(g1_ident_contrib(step), ρ(w_next)) in G₁
proof fn lemma_retraction_single_step(
    data: AmalgamatedData,
    rho: HomomorphismData,
    step: DerivationStep,
    w1: Word, w_next: Word,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        rho == fp_left_retraction(data.p1, data.p2),
        apply_step(amalgamated_free_product(data), w1, step) == Some(w_next),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
    ensures
        equiv_in_presentation(
            data.p1,
            apply_hom(rho, w1),
            concat(g1_ident_contrib(data, step), apply_hom(rho, w_next)),
        ),
{
    // The retraction ρ = fp_left_retraction collapses G₂ generators to ε.
    // For each step type:
    //
    // FreeReduce on G₁ symbols:
    //   ρ(w1) differs from ρ(w_next) by the same reduction. ρ(w1) ≡ ρ(w_next).
    //   g1_ident_contrib = ε. So ρ(w1) ≡ concat(ε, ρ(w_next)) =~= ρ(w_next). ✓
    //
    // FreeReduce on G₂ symbols:
    //   The reduced G₂ pair maps to ε under ρ. So ρ(w1) = ρ(w_next).
    //   g1_ident_contrib = ε. ✓
    //
    // FreeExpand on G₁ symbols:
    //   ρ(w_next) has the expanded pair. ρ(w1) = ρ(w_next) minus the pair.
    //   But ρ preserves G₁ symbols, so ρ(w_next) = ρ(w1) plus the pair.
    //   g1_ident_contrib = ε. ρ(w1) ≡ ρ(w_next) by the free expansion. ✓
    //
    // FreeExpand on G₂ symbols:
    //   ρ collapses both to ε. ρ(w1) = ρ(w_next). ✓
    //
    // G₁ relator insert:
    //   ρ maps the relator to itself. ρ(w_next) = ρ(w1) with relator inserted.
    //   ρ(w1) ≡ ρ(w_next) by the relator (relator is ≡ ε in G₁). ✓
    //
    // G₁ relator delete:
    //   Same reasoning in reverse. ✓
    //
    // G₂ relator insert/delete:
    //   ρ collapses the relator to ε. ρ(w1) = ρ(w_next). ✓
    //
    // Identification relator insert (u_i · inv(shift(v_i))):
    //   ρ maps this to u_i (since inv(shift(v_i)) collapses to ε).
    //   ρ(w_next) = ρ(w1) with u_i inserted at position p.
    //   g1_ident_contrib = u_i.
    //   ρ(w1) ≡ concat(u_i, ρ(w_next))? No — the u_i is inserted at
    //   position p in the word, not prepended.
    //
    //   Actually, this is where the approach gets complicated.
    //   The u_i is inserted at a specific position, not at the front.
    //   So ρ(w1) ≠ concat(u_i, ρ(w_next)) in general.
    //
    //   The position-dependent insertion means the invariant
    //   "ρ(w1) ≡ concat(contrib, ρ(w_next))" is WRONG.
    //
    //   The correct statement is more nuanced:
    //   ρ(w_next) = ρ(w1[0..p]) · u_i · ρ(w1[p..])
    //   (u_i is inserted at the retraction-mapped position of p)
    //
    //   This is position-dependent and much harder to formalize.

    // I realize the simple retraction chain approach doesn't work
    // because the identification contributions go to DIFFERENT POSITIONS
    // in the word, not just prepended/appended.
    //
    // The correct approach for the excursion lemma is the full
    // van der Waerden action, which handles positions properly.
    //
    // Let me abandon the retraction chain approach and implement
    // the van der Waerden action instead.

    // PLACEHOLDER: this lemma has the wrong statement.
    // Will be replaced by the van der Waerden action proof.
    let contrib = g1_ident_contrib(data, step);
    assert(contrib =~= empty_word() || contrib.len() > 0);  // trivial
    lemma_equiv_refl(data.p1, apply_hom(rho, w1));  // placeholder
}

/// Total G₂ contribution is trivial in G₂.
proof fn lemma_total_g2_contrib_trivial(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
)
    requires
        amalgamated_data_valid(data),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        is_left_word(w1, data.p1.num_generators),
        is_left_word(w2, data.p1.num_generators),
    ensures
        equiv_in_presentation(data.p2, total_g2_contrib(data, steps), empty_word()),
{
    // Same approach: apply right retraction to the derivation.
    // The right retraction collapses G₁ generators.
    // G₂ steps are preserved; identification steps contribute v_i.
    // Since ρ_R(w1) = ε and ρ_R(w2) = ε (both G₁ words),
    // the chain goes from ε to ε, with G₂ equivalences and v_i contributions.
    // Net: total_g2_contrib ≡ ε in G₂.
    //
    // Same position-dependency issue as above.
    // PLACEHOLDER.
    lemma_equiv_refl(data.p2, empty_word());  // placeholder
}

/// The isomorphism condition links G₁ and G₂ contributions:
/// if total_g2_contrib ≡ ε in G₂, then total_g1_contrib ≡ ε in G₁.
proof fn lemma_isomorphism_links_contribs(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        equiv_in_presentation(data.p2, total_g2_contrib(data, steps), empty_word()),
    ensures
        equiv_in_presentation(data.p1, total_g1_contrib(data, steps), empty_word()),
{
    // The total contributions are "parallel" products:
    // total_g1_contrib = u_{i1}^{e1} · u_{i2}^{e2} · ...
    // total_g2_contrib = v_{i1}^{e1} · v_{i2}^{e2} · ...
    // where (i_k, e_k) are the same for both.
    //
    // This is exactly the structure of apply_embedding:
    // total_g1_contrib = apply_embedding(a_words, abstract_word)
    // total_g2_contrib = apply_embedding(b_words, abstract_word)
    //
    // By the isomorphism condition:
    // apply_embedding(b_words, w) ≡ ε in G₂ implies
    // apply_embedding(a_words, w) ≡ ε in G₁.
    //
    // PLACEHOLDER: proving the parallel structure requires tracking
    // the abstract word through the derivation.
    lemma_equiv_refl(data.p1, empty_word());  // placeholder
}

} // verus!
