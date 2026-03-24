use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::quotient::*;
use crate::reduction::*;
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
// Part G: Derivation splitting helper
// ============================================================

/// Split a derivation at position k.
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
// Part H: AFP reflects left — single unified function
// ============================================================
//
// This single function handles ALL cases:
// - All intermediates are G₁ (structural lemma chain)
// - First intermediate is non-G₁ (search for G₁ return, split)
// - Pure excursion (backward scan for G₁ intermediate)
//
// The key: all recursive calls use STRICTLY SHORTER step sequences,
// so termination is guaranteed by decreasing steps.len().

/// AFP reflects left equivalence: two G₁-words connected by an AFP derivation
/// are equivalent in G₁.
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
        return;
    }

    let step0 = steps.first();
    let w_next = apply_step(afp, w1, step0).unwrap();
    let rest = steps.drop_first();

    if is_left_word(w_next, n1) {
        // First intermediate is G₁. Use structural lemma + recurse.
        lemma_left_step_valid_in_g1(data, w1, step0, w_next);
        lemma_afp_reflects_left(data, rest, w_next, w2);
        lemma_equiv_transitive(data.p1, w1, w_next, w2);
        return;
    }

    // First intermediate is non-G₁. Search backwards from the end
    // for a G₁ intermediate. w2 is G₁ at position steps.len().
    // w1 is G₁ at position 0. Some intermediate in between must be G₁
    // (at worst, peel off the last step to find w_prev, and if it's G₁
    // we can split; if not, peel further back).

    // Peel off the last step.
    let k = (steps.len() - 1) as int;
    lemma_derivation_split_at(afp, steps, w1, w2, k);
    let prefix = steps.subrange(0, k);
    let suffix_step = steps.subrange(k, steps.len() as int);
    let w_prev = derivation_produces(afp, prefix, w1).unwrap();

    if is_left_word(w_prev, n1) {
        // w_prev is G₁. Split into prefix (shorter) and last step (structural).
        lemma_afp_reflects_left(data, prefix, w1, w_prev);  // length k < steps.len() ✓
        // For the last step: w_prev (G₁) → w2 (G₁)
        assert(suffix_step =~= Seq::new(1, |_i: int| steps[k]));
        assert(suffix_step.first() == steps[k]);
        assert(apply_step(afp, w_prev, steps[k]) == Some(w2)) by {
            assert(suffix_step.drop_first() =~= Seq::<DerivationStep>::empty());
        }
        lemma_left_step_valid_in_g1(data, w_prev, steps[k], w2);
        lemma_equiv_transitive(data.p1, w1, w_prev, w2);
        return;
    }

    // w_prev is non-G₁. Continue backwards.
    if k < 2 {
        // steps.len() == 2 (since k == steps.len() - 1 and k < 2 means steps.len() <= 2).
        // Two-step excursion: w1 (G₁) → w_next (non-G₁) → w2 (G₁).
        assert(steps.len() == 2);
        assert(rest.len() == 1);
        let w_mid = w_next;
        lemma_two_step_excursion(data, step0, rest.first(), w1, w_mid, w2);
        return;
    }

    // k >= 2. Peel off the penultimate step.
    let k2 = k - 1;
    lemma_derivation_split_at(afp, prefix, w1, w_prev, k2);
    let prefix2 = prefix.subrange(0, k2);
    let w_prev2 = derivation_produces(afp, prefix2, w1).unwrap();

    if is_left_word(w_prev2, n1) {
        // w_prev2 is G₁. Split: prefix2 + two-step excursion.
        lemma_afp_reflects_left(data, prefix2, w1, w_prev2);  // length k2 < steps.len() ✓
        // Two-step: w_prev2 (G₁) → w_prev (non-G₁) → w2 (G₁)
        assert(apply_step(afp, w_prev2, prefix[k2]) == Some(w_prev)) by {
            let mid = prefix.subrange(k2, prefix.len() as int);
            assert(mid =~= Seq::new(1, |_i: int| prefix[k2]));
            assert(mid.first() == prefix[k2]);
            assert(mid.drop_first() =~= Seq::<DerivationStep>::empty());
        }
        assert(apply_step(afp, w_prev, steps[k]) == Some(w2)) by {
            assert(suffix_step.first() == steps[k]);
            assert(suffix_step.drop_first() =~= Seq::<DerivationStep>::empty());
        }
        lemma_two_step_excursion(data, prefix[k2], steps[k], w_prev2, w_prev, w2);
        lemma_equiv_transitive(data.p1, w1, w_prev2, w2);
        return;
    }

    // Neither w_prev nor w_prev2 is G₁. Continue backward scan.
    // Use a helper that scans backwards from position k2-1.
    lemma_backward_scan_and_split(data, steps, w1, w2, k2 - 1);
}

/// Backward scan: find a G₁ intermediate at or before position `pos`,
/// then split the derivation there.
/// w1 is G₁ at position 0, so the scan always finds one.
proof fn lemma_backward_scan_and_split(
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
        0 <= pos,
        pos < steps.len(),
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

    if pos == 0 {
        // w_pos == w1 which IS G₁.
        assert(prefix =~= Seq::<DerivationStep>::empty());
        assert(w_pos == w1);
        assert(suffix =~= steps);
        // The whole derivation goes from w1 (G₁) to w2 (G₁).
        // suffix = steps, and we need to split it.
        // Since pos = 0 and steps.len() >= 3, the suffix is the full derivation.
        // We can use lemma_afp_reflects_left on the suffix.
        // But that's the same length — no progress!
        // Actually, w_pos = w1 is G₁. We split at 0:
        //   prefix (length 0): trivial
        //   suffix (length steps.len()): use lemma_afp_reflects_left
        // But that's the original call. Circular!
        //
        // The resolution: at pos = 0, w_pos = w1 is G₁. We already know this.
        // The backward scan should have stopped earlier.
        // In fact, lemma_afp_reflects_left should have handled this case
        // before calling backward_scan.
        //
        // Since w1 IS G₁ and we scanned all the way back to 0,
        // all intermediates 1..steps.len()-1 are non-G₁.
        // This is a pure excursion that we can't split further.
        // We need the two-step excursion applied repeatedly from the back.
        //
        // Peel off the last two steps:
        lemma_peel_last_two(data, steps, w1, w2);
    } else if is_left_word(w_pos, n1) {
        // Found G₁ at position pos. Split.
        // prefix: length pos < steps.len()
        // suffix: length steps.len() - pos
        // Both are strictly shorter than steps.len(), so they terminate.
        lemma_afp_reflects_left(data, prefix, w1, w_pos);  // length pos < steps.len() ✓
        lemma_afp_reflects_left(data, suffix, w_pos, w2);   // length steps.len()-pos ≤ steps.len()-1 ✓
        lemma_equiv_transitive(data.p1, w1, w_pos, w2);
    } else {
        // Continue scanning backwards.
        lemma_backward_scan_and_split(data, steps, w1, w2, pos - 1);
    }
}

/// Peel the last two steps off a pure excursion (no G₁ intermediates).
/// w1 (G₁) → ... → w_{n-2} → w_{n-1} → w2 (G₁)
/// All intermediates non-G₁.
/// The last two steps form a two-step excursion IF w_{n-2} is G₁.
/// If not, we peel further back.
///
/// Since w1 is G₁ at position 0, at some point we find a G₁ intermediate.
/// This function peels from the back in steps of 2 (two-step excursions).
proof fn lemma_peel_last_two(
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
        steps.len() >= 2,
    ensures
        equiv_in_presentation(data.p1, w1, w2),
    decreases steps.len(),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;

    if steps.len() == 2 {
        // Two-step excursion
        let step0 = steps[0];
        let step1 = steps[1];
        let w_mid = apply_step(afp, w1, step0).unwrap();
        assert(steps.first() == step0);
        assert(steps.drop_first() =~= Seq::new(1, |_i: int| step1));
        assert(apply_step(afp, w_mid, step1) == Some(w2)) by {
            assert(steps.drop_first().first() == step1);
            assert(steps.drop_first().drop_first() =~= Seq::<DerivationStep>::empty());
        }
        if is_left_word(w_mid, n1) {
            // Both steps are G₁-to-G₁. Use structural lemma.
            lemma_left_step_valid_in_g1(data, w1, step0, w_mid);
            lemma_left_step_valid_in_g1(data, w_mid, step1, w2);
            lemma_equiv_transitive(data.p1, w1, w_mid, w2);
        } else {
            lemma_two_step_excursion(data, step0, step1, w1, w_mid, w2);
        }
    } else {
        // steps.len() >= 3. Peel off last two steps.
        let k = (steps.len() - 2) as int;
        lemma_derivation_split_at(afp, steps, w1, w2, k);
        let prefix = steps.subrange(0, k);
        let last_two = steps.subrange(k, steps.len() as int);
        let w_k = derivation_produces(afp, prefix, w1).unwrap();

        // last_two has length 2
        assert(last_two.len() == 2);
        let step_a = last_two[0];
        let step_b = last_two[1];
        let w_mid = apply_step(afp, w_k, step_a).unwrap();

        assert(last_two.first() == step_a);
        assert(last_two.drop_first() =~= Seq::new(1, |_i: int| step_b));
        assert(apply_step(afp, w_mid, step_b) == Some(w2)) by {
            assert(last_two.drop_first().first() == step_b);
            assert(last_two.drop_first().drop_first() =~= Seq::<DerivationStep>::empty());
        }

        if is_left_word(w_k, n1) {
            // w_k is G₁. prefix: w1 → w_k, last_two: w_k → w2.
            lemma_afp_reflects_left(data, prefix, w1, w_k);  // length k < steps.len() ✓
            // Handle last two steps
            if is_left_word(w_mid, n1) {
                lemma_left_step_valid_in_g1(data, w_k, step_a, w_mid);
                lemma_left_step_valid_in_g1(data, w_mid, step_b, w2);
                lemma_equiv_transitive(data.p1, w_k, w_mid, w2);
            } else {
                lemma_two_step_excursion(data, step_a, step_b, w_k, w_mid, w2);
            }
            lemma_equiv_transitive(data.p1, w1, w_k, w2);
        } else if is_left_word(w_mid, n1) {
            // w_mid is G₁ but w_k isn't. The last step is structural.
            // prefix + [step_a]: w1 → w_mid (length k+1 < steps.len())
            let prefix_plus = steps.subrange(0, k + 1);
            lemma_derivation_split_at(afp, steps, w1, w2, k + 1);
            lemma_afp_reflects_left(data, prefix_plus, w1, w_mid);  // length k+1 < steps.len() ✓
            lemma_left_step_valid_in_g1(data, w_mid, step_b, w2);
            lemma_equiv_transitive(data.p1, w1, w_mid, w2);
        } else {
            // Neither w_k nor w_mid is G₁. Recurse with prefix (shorter).
            // prefix goes w1 → w_k (non-G₁). We need w1 ≡ w_k in G₁.
            // But w_k is non-G₁, so we can't use reflects_left directly.
            //
            // Instead: the ORIGINAL two-step excursion w_k → w_mid → w2
            // doesn't help because w_k isn't G₁.
            //
            // We need to peel further. Recurse on the full derivation
            // minus the last two steps, extended by finding a G₁ point.
            //
            // Actually, we can recurse on lemma_peel_last_two with prefix.
            // prefix goes from w1 (G₁) to w_k (non-G₁).
            // But lemma_peel_last_two requires both endpoints to be G₁!
            //
            // We're stuck. The non-G₁ endpoint w_k prevents direct recursion.
            // We need a DIFFERENT splitting strategy.
            //
            // INSIGHT: Instead of peeling from the back, scan from the FRONT.
            // We already know position 1 might be non-G₁. Check position 2.
            // If position 2 is G₁, split there. If not, check 3, etc.
            // This is what lemma_afp_reflects_left already does.
            //
            // But we're here because the backward scan reached position 0.
            // All intermediates 1..n-1 are non-G₁.
            // The only G₁ points are w1 (pos 0) and w2 (pos n).
            //
            // For this case, we CANNOT split. We need the two-step excursion
            // to handle it directly. But the two-step excursion needs the
            // first endpoint to be G₁. If we take ANY two consecutive steps
            // w_{j} → w_{j+1} → w_{j+2} where w_{j} is G₁, we can apply it.
            //
            // The only G₁ endpoint available is w1 (pos 0).
            // So: take the first two steps: w1 → w_next → w_next2.
            // w_next is non-G₁ (checked in lemma_afp_reflects_left).
            // w_next2 might be G₁ or non-G₁.
            //
            // If w_next2 is G₁: two-step excursion w1 → w_next → w_next2.
            //   Then recurse on w_next2 → ... → w2 (length n-2 < n). ✓
            //
            // If w_next2 is non-G₁: we can't do a two-step excursion.
            //   We need to go further. But the FIRST two steps don't form
            //   a useful two-step excursion.
            //
            // This is the fundamental issue. For a pure excursion with NO
            // G₁ intermediates, the two-step excursion approach doesn't work
            // because consecutive pairs of intermediates are non-G₁.
            //
            // We genuinely need the van der Waerden action for this case.
            // The two-step excursion can only be applied when one endpoint is G₁.
            //
            // FOR NOW: handle the case where w_next2 is G₁ (making progress),
            // and leave the pure-excursion case for the van der Waerden action.

            // Check w_next2:
            if steps.len() >= 3 {
                let step0 = steps[0];
                let step1 = steps[1];
                let w_next = apply_step(afp, w1, step0).unwrap();
                lemma_derivation_split_at(afp, steps, w1, w2, 2);
                let first_two = steps.subrange(0, 2);
                let rest_after_two = steps.subrange(2, steps.len() as int);
                let w_next2 = derivation_produces(afp, first_two, w1).unwrap();

                assert(first_two.first() == step0);
                assert(first_two.drop_first() =~= Seq::new(1, |_i: int| step1));
                let w_mid2 = apply_step(afp, w_next, step1).unwrap();
                assert(w_next2 == w_mid2) by {
                    assert(first_two.drop_first().first() == step1);
                    assert(first_two.drop_first().drop_first() =~= Seq::<DerivationStep>::empty());
                }

                if is_left_word(w_next2, n1) {
                    // Two-step excursion: w1 → w_next (non-G₁) → w_next2 (G₁)
                    lemma_two_step_excursion(data, step0, step1, w1, w_next, w_next2);
                    // Recurse on rest: w_next2 → ... → w2 (length n-2)
                    lemma_afp_reflects_left(data, rest_after_two, w_next2, w2);
                    lemma_equiv_transitive(data.p1, w1, w_next2, w2);
                } else {
                    // Pure excursion: no G₁ at positions 1 or 2.
                    // NEED VAN DER WAERDEN ACTION.
                    // This is the remaining gap.
                    //
                    // For a complete proof: implement the action.
                    // For now: this case is not handled.
                    // assert(false) marks the gap.
                    assert(false);  // REMAINING GAP: pure excursion, no G₁ intermediates
                }
            } else {
                // steps.len() == 2 (handled above in the if branch)
                assert(false); // unreachable
            }
        }
    }
}

/// Two-step excursion: w1 (G₁) → w_mid (non-G₁) → w2 (G₁).
/// Proves w1 ≡ w2 in G₁ by case analysis.
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

    // Step1 must introduce G₂ content. Step2 must remove it.
    // Possible step1: FreeExpand(G₂), G₂ RelatorInsert, IdentRelatorInsert.
    // FreeReduce/G₁-RelatorInsert/G₁-RelatorDelete don't introduce G₂.

    match step1 {
        DerivationStep::FreeExpand { position: p1, symbol: s1 } => {
            // s1 must be G₂
            if generator_index(s1) < n1 {
                // G₁ symbol: w_mid still all-G₁. Contradiction.
                assert forall|k: int| 0 <= k < w_mid.len()
                    implies generator_index(w_mid[k]) < n1
                by {
                    let pair = Seq::new(1, |_i: int| s1)
                        + Seq::new(1, |_i: int| inverse_symbol(s1));
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
                assert(false);
            }
            // s1 is G₂ (index >= n1).
            // Step2 must be FreeReduce at p1 (the only way to remove exactly
            // these 2 G₂ symbols). See the argument in the FreeExpand+FreeReduce
            // case analysis above.
            match step2 {
                DerivationStep::FreeReduce { position: p2 } => {
                    if p2 == p1 {
                        assert(w2 =~= w1) by {
                            let pair = Seq::new(1, |_i: int| s1)
                                + Seq::new(1, |_i: int| inverse_symbol(s1));
                            assert(w_mid =~= w1.subrange(0, p1) + pair
                                + w1.subrange(p1, w1.len() as int));
                        }
                        lemma_equiv_refl(data.p1, w1);
                    } else {
                        // p2 ≠ p1: the reduction is at a different position.
                        // After reducing a non-G₂ pair, G₂ symbols remain → w2 non-G₁.
                        // Contradiction with is_left_word(w2).
                        //
                        // The G₂ symbols are at positions p1, p1+1 in w_mid.
                        // Any FreeReduce at p2 ≠ p1 leaves them in w2.
                        if p2 + 2 <= p1 {
                            assert(reduce_at(w_mid, p2)[p1 - 2] == w_mid[p1]);
                            assert(generator_index(w_mid[p1]) >= n1);
                            assert(w2 =~= reduce_at(w_mid, p2));
                            assert(generator_index(w2[p1 - 2]) >= n1);
                            assert(false);
                        } else if p2 > p1 + 1 {
                            assert(reduce_at(w_mid, p2)[p1] == w_mid[p1]);
                            assert(generator_index(w_mid[p1]) >= n1);
                            assert(w2 =~= reduce_at(w_mid, p2));
                            assert(generator_index(w2[p1]) >= n1);
                            assert(false);
                        } else if p2 == p1 + 1 {
                            // Pair at p1+1, p1+2: inv(s1) and w1[p1]. Different gen indices.
                            assert(has_cancellation_at(w_mid, p2));
                            assert(is_inverse_pair(w_mid[p2], w_mid[p2 + 1]));
                            assert(generator_index(w_mid[p2]) >= n1);
                            assert(w_mid[p2 + 1] == w1[p1 as int]);
                            assert(generator_index(w1[p1 as int]) < n1);
                            assert(false); // different gen indices can't be inverse pair
                        } else {
                            // p2 == p1 - 1: pair at p1-1, p1. w1[p1-1] and s1. Different gen indices.
                            assert(p2 == p1 - 1);
                            assert(has_cancellation_at(w_mid, p2));
                            assert(is_inverse_pair(w_mid[p2], w_mid[p2 + 1]));
                            assert(w_mid[p2] == w1[(p1 - 1) as int]);
                            assert(generator_index(w1[(p1 - 1) as int]) < n1);
                            assert(w_mid[p2 + 1] == s1);
                            assert(generator_index(s1) >= n1);
                            assert(false); // different gen indices
                        }
                    }
                },
                _ => {
                    // Other step2 after FreeExpand(G₂).
                    // The 2 G₂ symbols need to be removed in one step.
                    // FreeExpand adds only 2 G₂ symbols.
                    // Only FreeReduce can remove exactly 2 adjacent symbols.
                    // RelatorDelete could remove a G₂ relator that happens to
                    // be exactly [s1, inv(s1)] — but that's a 2-symbol relator.
                    // This is a rare edge case. TODO for complete proof.
                    assert(false); // REMAINING GAP: FreeExpand + non-FreeReduce
                }
            }
        },
        DerivationStep::FreeReduce { position } => {
            // FreeReduce only removes G₁ symbols from a G₁ word. w_mid still G₁.
            assert forall|k: int| 0 <= k < w_mid.len()
                implies generator_index(w_mid[k]) < n1
            by {
                if k < position { assert(w_mid[k] == w1[k]); }
                else { assert(w_mid[k] == w1[k + 2]); }
            }
            assert(is_left_word(w_mid, n1));
            assert(false); // contradiction with !is_left_word(w_mid)
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            // RelatorDelete removes a substring from w1. w1 is G₁-only.
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
        DerivationStep::RelatorInsert { position: p1, relator_index: ri1, inverted: inv1 } => {
            // RelatorInsert of a relator with G₂ content.
            // The relator is either a shifted G₂ relator or an identification relator.
            // TODO: Handle this case. The identification relator case
            // uses the isomorphism condition.
            // This is ~100 lines of case analysis.
            assert(false); // REMAINING GAP: RelatorInsert case
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
    assert(is_left_word(w, data.p1.num_generators)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies generator_index(w[k]) < data.p1.num_generators
        by {
            assert(symbol_valid(w[k], data.p1.num_generators));
        }
    }
    lemma_afp_reflects_left(data, d.steps, w, empty_word());
}

} // verus!
