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
// Part G: AFP injectivity — main theorem
// ============================================================
//
// The proof uses the structural lemma (lemma_left_step_valid_in_g1)
// combined with the van der Waerden action for pure excursions.
//
// Current status:
//   - The structural lemma handles derivations where all intermediates are G₁-words.
//   - Pure excursions (G₁ → non-G₁ → ... → G₁) require the van der Waerden action.
//   - The action proof is ~500 lines (standard textbook, Lyndon-Schupp Ch. IV).
//   - To be implemented in the next iteration.

// ============================================================
// Part H: Derivation splitting helper
// ============================================================

/// Split a derivation at position k: prefix produces w → w_k, suffix produces w_k → w'.
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
        assert(steps.subrange(k, steps.len() as int)
            =~= rest.subrange(k - 1, rest.len() as int));
    }
}

// ============================================================
// Part I: AFP injectivity — main theorem
// ============================================================

/// AFP reflects left equivalence: two G₁-words equivalent in the AFP
/// are equivalent in G₁.
///
/// Proof by induction on derivation length.
/// Uses the structural lemma for steps between G₁-words.
/// Uses the pure excursion lemma for passages through non-G₁ intermediates.
pub proof fn lemma_afp_reflects_left(
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
            lemma_left_step_valid_in_g1(data, w1, step0, w_next);
            lemma_afp_reflects_left(data, rest, w_next, w2);
            lemma_equiv_transitive(data.p1, w1, w_next, w2);
        } else {
            // Case 2: first intermediate is non-G₁.
            // Find the first G₁ return (scanning from position 2 onwards).
            // w2 is G₁ at position steps.len(), so a return exists.
            // Split there: left part is an excursion, right part uses IH.
            //
            // For the excursion: handled by lemma_pure_excursion.
            // For now, we search by checking each position.

            // Check position 2, 3, ... until we find a G₁ intermediate.
            // The position steps.len() (= w2) is G₁.
            // We use the recursive helper lemma_find_and_split.
            lemma_find_and_split(data, steps, w1, w2, 2);
        }
    }
}

/// Helper: search for the first G₁ intermediate from position `start` and split there.
/// Precondition: position 1 is non-G₁ (the first intermediate is non-G₁).
proof fn lemma_find_and_split(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
    start: int,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        is_left_word(w1, data.p1.num_generators),
        is_left_word(w2, data.p1.num_generators),
        2 <= start <= steps.len(),
        steps.len() >= 2,
        // All intermediates at positions 1..start-1 are non-G₁
        !is_left_word(
            apply_step(amalgamated_free_product(data), w1, steps.first()).unwrap(),
            data.p1.num_generators,
        ),
    ensures
        equiv_in_presentation(data.p1, w1, w2),
    decreases steps.len() - start,
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;

    if start == steps.len() {
        // We've reached the end. The excursion is the ENTIRE derivation.
        // w1 → w_1 (non-G₁) → ... → w2 (G₁)
        // This is a pure excursion of length steps.len().
        lemma_pure_excursion(data, steps, w1, w2);
    } else {
        // Check if position `start` has a G₁ intermediate.
        lemma_derivation_split_at(afp, steps, w1, w2, start);
        let prefix = steps.subrange(0, start);
        let suffix = steps.subrange(start, steps.len() as int);
        let w_k = derivation_produces(afp, prefix, w1).unwrap();

        if is_left_word(w_k, n1) {
            // Found G₁ at position `start`. Split.
            // Left: pure excursion w1 → ... → w_k (length start)
            lemma_pure_excursion(data, prefix, w1, w_k);
            // Right: w_k → ... → w2 (length steps.len() - start < steps.len())
            lemma_afp_reflects_left(data, suffix, w_k, w2);
            // Chain
            lemma_equiv_transitive(data.p1, w1, w_k, w2);
        } else {
            // Position `start` is non-G₁. Continue searching.
            lemma_find_and_split(data, steps, w1, w2, start + 1);
        }
    }
}

/// Pure excursion: a derivation from G₁-word to G₁-word.
/// This handles ALL cases, including those where intermediates are non-G₁.
///
/// For length 0 or 1: trivial or structural lemma.
/// For length ≥ 2: uses the two-step excursion as the base case of
/// a backward induction (peeling off the last step or last two steps).
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
        let w_next = apply_step(afp, w1, steps.first()).unwrap();
        assert(w_next == w2);
        lemma_left_step_valid_in_g1(data, w1, steps.first(), w2);
    } else {
        // Length ≥ 2. Peel off the last step.
        let k = (steps.len() - 1) as int;
        lemma_derivation_split_at(afp, steps, w1, w2, k);
        let prefix = steps.subrange(0, k);
        let last_step = steps[k];
        let w_prev = derivation_produces(afp, prefix, w1).unwrap();

        // w_prev → w2 is the last step
        assert(apply_step(afp, w_prev, last_step) == Some(w2));

        if is_left_word(w_prev, n1) {
            // w_prev is G₁. Split: prefix is shorter excursion, last step is structural.
            lemma_pure_excursion(data, prefix, w1, w_prev);
            lemma_left_step_valid_in_g1(data, w_prev, last_step, w2);
            lemma_equiv_transitive(data.p1, w1, w_prev, w2);
        } else {
            // w_prev is non-G₁. Peel off TWO steps from the end.
            if k >= 2 {
                let k2 = k - 1;
                lemma_derivation_split_at(afp, prefix, w1, w_prev, k2);
                let prefix2 = prefix.subrange(0, k2);
                let penult_step = prefix[k2];
                let w_prev2 = derivation_produces(afp, prefix2, w1).unwrap();

                if is_left_word(w_prev2, n1) {
                    // w_prev2 is G₁. Split:
                    // prefix2: shorter excursion w1 → w_prev2
                    // two-step: w_prev2 → w_prev → w2
                    lemma_pure_excursion(data, prefix2, w1, w_prev2);
                    lemma_two_step_excursion(data, penult_step, last_step,
                        w_prev2, w_prev, w2);
                    lemma_equiv_transitive(data.p1, w1, w_prev2, w2);
                } else {
                    // w_prev2 also non-G₁. Continue peeling backwards.
                    // Recursive: the prefix has length k2 < steps.len().
                    // We handle the last step (w_prev → w2) separately.
                    //
                    // Strategy: use lemma_afp_reflects_left which handles
                    // the general case by scanning forward for G₁ intermediates.
                    // Since lemma_pure_excursion is called FROM lemma_afp_reflects_left,
                    // we need to be careful about circular dependencies.
                    //
                    // The key observation: we can always peel backwards until
                    // we find a G₁ intermediate. At worst, we reach w1 (which IS G₁).
                    // So backward peeling always terminates.
                    //
                    // Use the backward scan helper.
                    lemma_backward_scan(data, steps, w1, w2, k2);
                }
            } else {
                // k == 1, so steps.len() == 2.
                // Two-step excursion: w1 → w_prev → w2.
                // w_prev is non-G₁ (we checked above).
                let step0 = steps.first();
                let w_mid = apply_step(afp, w1, step0).unwrap();
                assert(w_mid == w_prev);
                lemma_two_step_excursion(data, step0, last_step, w1, w_mid, w2);
            }
        }
    }
}

/// Backward scan: search backwards from position `pos` for a G₁ intermediate.
proof fn lemma_backward_scan(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
    pos: int,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        is_left_word(w1, data.p1.num_generators),
        is_left_word(w2, data.p1.num_generators),
        0 <= pos < steps.len(),
        steps.len() >= 3,
    ensures
        equiv_in_presentation(data.p1, w1, w2),
    decreases pos,
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;

    lemma_derivation_split_at(afp, steps, w1, w2, pos);
    let prefix = steps.subrange(0, pos);
    let suffix = steps.subrange(pos, steps.len() as int);
    let w_pos = derivation_produces(afp, prefix, w1).unwrap();

    if is_left_word(w_pos, n1) {
        // Found G₁ at position pos. Split.
        if prefix.len() > 0 {
            lemma_pure_excursion(data, prefix, w1, w_pos);
        } else {
            assert(w1 == w_pos);
            lemma_equiv_refl(data.p1, w1);
        }
        lemma_afp_reflects_left(data, suffix, w_pos, w2);
        lemma_equiv_transitive(data.p1, w1, w_pos, w2);
    } else if pos == 0 {
        // pos = 0 means w_pos = w1 which IS G₁. Contradiction with the else branch.
        assert(w_pos == w1);
        assert(is_left_word(w1, n1));
        assert(false); // w_pos is both G₁ and non-G₁
    } else {
        // Continue scanning backwards.
        lemma_backward_scan(data, steps, w1, w2, pos - 1);
    }
}

/// Two-step excursion: w1 (G₁) → w_mid (non-G₁) → w2 (G₁).
/// Proves w1 ≡ w2 in G₁.
///
/// This is the BASE CASE of the excursion analysis.
/// Case analysis on the two step types shows that the net G₁ effect
/// is always valid in G₁.
proof fn lemma_two_step_excursion(
    data: AmalgamatedData,
    step1: DerivationStep, step2: DerivationStep,
    w1: Word, w_mid: Word, w2: Word,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        apply_step(amalgamated_free_product(data), w1, step1) == Some(w_mid),
        apply_step(amalgamated_free_product(data), w_mid, step2) == Some(w2),
        is_left_word(w1, data.p1.num_generators),
        !is_left_word(w_mid, data.p1.num_generators),
        is_left_word(w2, data.p1.num_generators),
    ensures
        equiv_in_presentation(data.p1, w1, w2),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;

    // The two-step derivation is: w1 →[step1] w_mid →[step2] w2
    // This is a valid 2-step derivation in the AFP from w1 to w2.
    // Both w1 and w2 are G₁ words.
    // By composing both steps into a single derivation and using
    // the AFP reflects left lemma structure:
    //
    // We build a 2-step derivation and show it produces w1 → w2 in the AFP.
    // Then w1 ≡ w2 in the AFP.
    // Since w1 and w2 are G₁-words, we need w1 ≡ w2 in G₁.
    //
    // For the two-step case, the only way G₂ content enters and leaves
    // is through the two steps. Let's analyze what step1 and step2 do.
    //
    // Step1 introduces G₂ content (w_mid has G₂ symbols, w1 doesn't).
    // Step2 removes all G₂ content (w2 has no G₂ symbols).
    //
    // The step1 MUST be one of:
    //   (a) FreeExpand with G₂ symbol (introduces 2 G₂ symbols)
    //   (b) RelatorInsert of a relator with G₂ content
    //       (shifted G₂ relator or identification relator)
    //
    // For (a): the 2 G₂ symbols must be removed by step2.
    //   The ONLY way to remove exactly those 2 G₂ symbols in one step
    //   is FreeReduce at the same position. This gives w2 = w1.
    //
    // For (b): the relator's G₂ content must be removed by step2.
    //   This requires step2 to be a RelatorDelete of the same relator
    //   (or a FreeReduce that partially cancels, but factor isolation
    //   prevents cross-boundary reductions).
    //
    // The detailed case analysis is complex but each case is straightforward.
    // The KEY case is identification relator insert + identification relator delete,
    // where the isomorphism condition is used.
    //
    // For the FORMAL proof, we observe that:
    //   w1 ≡ w2 in the AFP (by the 2-step derivation).
    //   w1 and w2 are both G₁-words.
    //   We need: w1 ≡ w2 in G₁.
    //
    // By the AFP structure: the 2-step derivation uses AFP relators.
    // We can "undo" the derivation in G₁ if both steps are G₁-valid,
    // which happens when the intermediate word is also G₁ (structural lemma).
    // But w_mid is NON-G₁, so we can't directly apply the structural lemma.
    //
    // Instead, we use the 2-step derivation in the AFP:
    //   w1 → w_mid → w2 in AFP means w1 ≡ w2 in AFP.
    //   The FULL AFP injectivity (which we're proving) gives w1 ≡ w2 in G₁.
    //
    // But this is circular! We're using the result we're trying to prove.
    //
    // The resolution: the two-step case can be handled DIRECTLY by case analysis
    // on step1 and step2, without the general induction.
    // Each case either:
    //   - Shows w2 = w1 (e.g., FreeExpand then FreeReduce at same position)
    //   - Shows the net G₁ effect is a valid G₁ operation
    //   - Uses the isomorphism condition for the identification relator case

    // For now, handle the FreeExpand + FreeReduce case (the most common case)
    // and the case where step1 and step2 are inverse relator operations.

    match step1 {
        DerivationStep::FreeExpand { position: p1, symbol: s1 } => {
            // s1 must be G₂ (introduces G₂ content)
            // because w1 is G₁-only and w_mid is not
            assert(generator_index(s1) >= n1) by {
                // If s1 were G₁: w_mid would still be G₁ (contradiction)
                if generator_index(s1) < n1 {
                    assert forall|k: int| 0 <= k < w_mid.len()
                        implies generator_index(w_mid[k]) < n1
                    by {
                        let pair = Seq::new(1, |_| s1)
                            + Seq::new(1, |_| inverse_symbol(s1));
                        assert(w_mid =~= w1.subrange(0, p1) + pair
                            + w1.subrange(p1, w1.len() as int));
                        if k < p1 { assert(w_mid[k] == w1[k]); }
                        else if k == p1 as int { assert(w_mid[k] == s1); }
                        else if k == p1 + 1 {
                            assert(w_mid[k] == inverse_symbol(s1));
                            assert(generator_index(inverse_symbol(s1))
                                == generator_index(s1));
                        }
                        else { assert(w_mid[k] == w1[k - 2]); }
                    }
                    assert(is_left_word(w_mid, n1));
                }
            };

            // Step2 must remove the G₂ pair. Only FreeReduce at p1 can do this.
            // (Other steps can't remove exactly these 2 G₂ symbols in one step
            //  while leaving only G₁ symbols.)
            match step2 {
                DerivationStep::FreeReduce { position: p2 } => {
                    // Must be at the same position as the expand.
                    // The G₂ pair is at positions p1, p1+1 in w_mid.
                    // A FreeReduce at any other position either:
                    //   - Reduces a G₁ pair (leaving G₂ symbols in w2, contradiction)
                    //   - Tries to reduce across G₁/G₂ boundary (impossible by factor isolation)
                    //
                    // So p2 must be p1. Then w2 = w1 (expand+reduce cancel).
                    // Proof that p2 = p1:
                    //   w_mid[p2] and w_mid[p2+1] must be an inverse pair.
                    //   The G₂ symbols are at p1 and p1+1 in w_mid.
                    //   All other positions are G₁ symbols.
                    //   An inverse pair requires same generator_index.
                    //   If p2 ≠ p1: the pair at p2,p2+1 is either:
                    //     - Both G₁: reducing them leaves G₂ at p1,p1+1 → w2 non-G₁.
                    //     - One G₁, one G₂: can't be inverse pair (different gen indices).
                    //   So p2 = p1.
                    assert(has_cancellation_at(w_mid, p2));
                    if p2 != p1 {
                        // The pair at p2 is either both-G₁ or crosses boundary
                        if p2 + 2 <= p1 || p2 > p1 + 1 {
                            // Both in G₁ region. After reduce, G₂ pair remains.
                            // w2 has G₂ symbols → contradiction with is_left_word(w2).
                            if p2 + 2 <= p1 {
                                // G₂ pair shifts to p1-2, p1-1 in w2
                                assert(w2[p1 - 2] == w_mid[p1]) by {
                                    assert(w2 =~= reduce_at(w_mid, p2));
                                }
                                assert(generator_index(w_mid[p1]) >= n1);
                                assert(generator_index(w2[p1 - 2]) >= n1);
                            } else {
                                // p2 > p1 + 1: G₂ pair stays at p1, p1+1 in w2
                                assert(w2[p1] == w_mid[p1]) by {
                                    assert(w2 =~= reduce_at(w_mid, p2));
                                }
                                assert(generator_index(w_mid[p1]) >= n1);
                                assert(generator_index(w2[p1]) >= n1);
                            }
                            assert(false); // w2 has G₂ symbol but is G₁-only
                        } else {
                            // p2 = p1 + 1 or p2 = p1 - 1 (overlaps with G₂ pair)
                            // p2 = p1 + 1: pair at p1+1, p1+2.
                            //   w_mid[p1+1] = inv(s1) (G₂), w_mid[p1+2] = w1[p1] (G₁)
                            //   Different generator indices → not inverse pair.
                            // p2 = p1 - 1: pair at p1-1, p1.
                            //   w_mid[p1-1] = w1[p1-1] (G₁), w_mid[p1] = s1 (G₂)
                            //   Different generator indices → not inverse pair.
                            if p2 == p1 + 1 {
                                assert(w_mid[p2] == inverse_symbol(s1));
                                assert(generator_index(w_mid[p2]) >= n1);
                                assert(w_mid[p2 + 1] == w1[p1 as int]);
                                assert(generator_index(w1[p1 as int]) < n1);
                                // is_inverse_pair requires same gen index
                                assert(is_inverse_pair(w_mid[p2], w_mid[p2 + 1]));
                                // But gen indices differ → contradiction
                                assert(false);
                            } else {
                                // p2 = p1 - 1
                                assert(p2 == p1 - 1);
                                assert(w_mid[p2] == w1[(p1 - 1) as int]);
                                assert(generator_index(w1[(p1 - 1) as int]) < n1);
                                assert(w_mid[p2 + 1] == s1);
                                assert(generator_index(s1) >= n1);
                                assert(is_inverse_pair(w_mid[p2], w_mid[p2 + 1]));
                                assert(false);
                            }
                        }
                    }
                    // p2 = p1. The expand+reduce cancel: w2 = w1.
                    assert(p2 == p1);
                    assert(w2 =~= w1) by {
                        assert(w2 =~= reduce_at(w_mid, p1));
                        let pair = Seq::new(1, |_| s1)
                            + Seq::new(1, |_| inverse_symbol(s1));
                        assert(w_mid =~= w1.subrange(0, p1) + pair
                            + w1.subrange(p1, w1.len() as int));
                    }
                    lemma_equiv_refl(data.p1, w1);
                },
                _ => {
                    // TODO: Other step2 types after FreeExpand G₂.
                    // These include RelatorDelete (of a G₂ or identification relator)
                    // and other rare cases.
                    // Each requires that the 2 G₂ symbols align with a relator.
                    // Factor isolation severely constrains what's possible.
                    //
                    // For now, this is an incomplete case.
                    // The mathematical argument is the same: the G₂ symbols
                    // can only be removed by operations that correspond to
                    // valid G₁ transformations (or identity).
                    assert(false); // TODO: complete case analysis
                },
            }
        },
        DerivationStep::FreeReduce { .. } | DerivationStep::RelatorDelete { .. } => {
            // FreeReduce and RelatorDelete REMOVE content from w1.
            // w1 is G₁-only, so they only remove G₁ content.
            // w_mid has FEWER G₁ symbols (or same) and NO G₂ symbols.
            // But w_mid IS non-G₁ → contradiction.
            match step1 {
                DerivationStep::FreeReduce { position } => {
                    // w_mid = reduce_at(w1, position). All symbols from w1 (G₁).
                    assert forall|k: int| 0 <= k < w_mid.len()
                        implies generator_index(w_mid[k]) < n1
                    by {
                        if k < position { assert(w_mid[k] == w1[k]); }
                        else { assert(w_mid[k] == w1[k + 2]); }
                    }
                    assert(is_left_word(w_mid, n1));
                    assert(false);
                },
                DerivationStep::RelatorDelete { position, relator_index, inverted } => {
                    let r = get_relator(afp, relator_index, inverted);
                    assert forall|k: int| 0 <= k < w_mid.len()
                        implies generator_index(w_mid[k]) < n1
                    by {
                        if k < position { assert(w_mid[k] == w1[k]); }
                        else { assert(w_mid[k] == w1[k + r.len()]); }
                    }
                    assert(is_left_word(w_mid, n1));
                    assert(false);
                },
                _ => { assert(false); }, // unreachable
            }
        },
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            // Relator insert that introduces G₂ content.
            // The relator must have G₂ symbols (otherwise w_mid would be G₁).
            // This is either a shifted G₂ relator or an identification relator.
            //
            // TODO: Handle the RelatorInsert cases.
            // Key case: identification relator insert + delete uses isomorphism condition.
            // This is the mathematically interesting case.
            //
            // For a complete proof, need ~100 more lines of case analysis here.
            assert(false); // TODO: complete case analysis for RelatorInsert
        },
        DerivationStep::FreeExpand { .. } => {
            // Already handled above (the G₂ FreeExpand case)
            assert(false); // unreachable
        },
    }
}

/// AFP injectivity: if w is a G₁-word and w ≡ ε in the AFP, then w ≡ ε in G₁.
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
    let d = choose|d: Derivation| derivation_valid(afp, d, w, empty_word());
    lemma_afp_reflects_left(data, d.steps, w, empty_word());
}

} // verus!
