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
// Part G: H-only VDW action (no syllables)
// ============================================================
//
// For AFP injectivity, we only need the h-component of the VDW state.
// The h-only action tracks a single nat (ct1 Cayley table element).
//
// G₁ symbol s: h → ct1.table[h][sym_col(s)]  (trace in G₁)
// G₂ symbol s: h → phi(ct2.table[phi_inv(h)][sym_col(unshift(s))])
//              (translate to G₂, trace, translate back)
//
// This is the "H-projection" of the full VDW action. It's sufficient for
// injectivity because for G₁-words on h=0, it equals trace_word(ct1, 0, w).

/// Lookup in a Cayley table: ct.table[elem][col], defaulting to 0.
pub open spec fn ct_lookup(
    ct: crate::todd_coxeter::CosetTable, elem: nat, col: nat,
) -> nat {
    match ct.table[elem as int][col as int] {
        Some(next) => next,
        None => 0,
    }
}

/// symbol_to_column shorthand.
pub open spec fn sym_col(s: Symbol) -> nat {
    crate::todd_coxeter::symbol_to_column(s)
}

/// Unshift a G₂ symbol.
pub open spec fn unshift_sym(s: Symbol, n1: nat) -> Symbol {
    match s {
        Symbol::Gen(i) => Symbol::Gen((i - n1) as nat),
        Symbol::Inv(i) => Symbol::Inv((i - n1) as nat),
    }
}

/// H-only action of a single symbol.
/// State: h (nat, ct1 Cayley element).
pub open spec fn h_act_sym(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    s: Symbol,
    h: nat,
) -> nat {
    if generator_index(s) < n1 {
        ct_lookup(ct1, h, sym_col(s))
    } else {
        let s_local = unshift_sym(s, n1);
        phi(ct_lookup(ct2, phi_inv(h), sym_col(s_local)))
    }
}

/// H-only action of a word.
pub open spec fn h_act_word(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    w: Word,
    h: nat,
) -> nat
    decreases w.len(),
{
    if w.len() == 0 {
        h
    } else {
        h_act_word(ct1, ct2, phi, phi_inv, n1, w.drop_first(),
            h_act_sym(ct1, ct2, phi, phi_inv, n1, w.first(), h))
    }
}

/// H-only composition: h_act_word(w1++w2, h) == h_act_word(w2, h_act_word(w1, h)).
proof fn lemma_h_act_concat(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    w1: Word, w2: Word,
    h: nat,
)
    ensures
        h_act_word(ct1, ct2, phi, phi_inv, n1, concat(w1, w2), h)
            == h_act_word(ct1, ct2, phi, phi_inv, n1, w2,
                h_act_word(ct1, ct2, phi, phi_inv, n1, w1, h)),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
    } else {
        assert(concat(w1, w2).first() == w1.first());
        assert(concat(w1, w2).drop_first() =~= concat(w1.drop_first(), w2));
        let h2 = h_act_sym(ct1, ct2, phi, phi_inv, n1, w1.first(), h);
        lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, w1.drop_first(), w2, h2);
    }
}

// ============================================================
// Part H: Prerequisites
// ============================================================

/// Cayley table validity.
pub open spec fn valid_cayley(t: crate::todd_coxeter::CosetTable, p: Presentation) -> bool {
    &&& crate::todd_coxeter::coset_table_wf(t)
    &&& crate::todd_coxeter::coset_table_consistent(t)
    &&& crate::finite::coset_table_complete(t)
    &&& crate::todd_coxeter::relator_closed(t, p)
    &&& t.num_gens == p.num_generators
    &&& presentation_valid(p)
    &&& crate::coset_group::has_schreier_system(t, p)
    &&& t.num_cosets > 0
}

/// phi/phi_inv compatibility.
pub open spec fn valid_phi(
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    data: AmalgamatedData,
) -> bool {
    &&& phi(0nat) == 0nat
    &&& phi_inv(0nat) == 0nat
    &&& (forall|b: nat| b < ct2.num_cosets ==> #[trigger] phi(b) < ct1.num_cosets)
    &&& (forall|a: nat| a < ct1.num_cosets ==> #[trigger] phi_inv(a) < ct2.num_cosets)
    &&& (forall|b: nat| b < ct2.num_cosets ==> #[trigger] phi_inv(phi(b)) == b)
    &&& (forall|a: nat| a < ct1.num_cosets ==> #[trigger] phi(phi_inv(a)) == a)
    // phi respects identification generators
    &&& (forall|i: int| #![trigger data.identifications[i]]
        0 <= i < data.identifications.len() ==> ({
        let u_elem = crate::todd_coxeter::trace_word(ct1, 0, data.identifications[i].0);
        let v_elem = crate::todd_coxeter::trace_word(ct2, 0, data.identifications[i].1);
        u_elem is Some && v_elem is Some && phi(v_elem.unwrap()) == u_elem.unwrap()
    }))
    // phi is a homomorphism (compatible with trace)
    // phi(trace(ct2, phi_inv(h), w)) == trace(ct1, h, translated_w) for B-words
    // Simplified: phi commutes with single-symbol traces
    &&& (forall|h2: nat, col: nat|
        h2 < ct2.num_cosets && col < 2 * ct2.num_gens ==>
        #[trigger] phi(ct_lookup(ct2, h2, col))
            == ct_lookup(ct1, phi(h2), col))
}

/// All prerequisites.
pub open spec fn h_prereqs(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
) -> bool {
    &&& amalgamated_data_valid(data)
    &&& identifications_isomorphic(data)
    &&& valid_cayley(ct1, data.p1)
    &&& valid_cayley(ct2, data.p2)
    &&& valid_phi(phi, phi_inv, ct1, ct2, data)
    &&& ct1.num_gens == data.p1.num_generators
    &&& ct2.num_gens == data.p2.num_generators
    &&& data.p1.num_generators == data.p2.num_generators  // same factor size (tower case)
}

// ============================================================
// Part I: H-only well-definedness lemmas
// ============================================================

/// ct_lookup round-trip via table consistency.
proof fn lemma_ct_roundtrip(
    ct: crate::todd_coxeter::CosetTable,
    h: nat, s_col: nat,
)
    requires
        crate::todd_coxeter::coset_table_wf(ct),
        crate::todd_coxeter::coset_table_consistent(ct),
        crate::finite::coset_table_complete(ct),
        h < ct.num_cosets,
        s_col < 2 * ct.num_gens,
    ensures
        ct_lookup(ct, ct_lookup(ct, h, s_col),
            crate::todd_coxeter::inverse_column(s_col)) == h,
        ct_lookup(ct, h, s_col) < ct.num_cosets,
{
    reveal(crate::todd_coxeter::coset_table_wf);
    reveal(crate::todd_coxeter::coset_table_consistent);
    reveal(crate::finite::coset_table_complete);
}

/// G₁ inverse pair: ct_lookup round-trips in ct1.
proof fn lemma_h_inv_pair_g1(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    s1: Symbol, s2: Symbol,
    h: nat,
)
    requires
        is_inverse_pair(s1, s2),
        generator_index(s1) < n1,
        n1 == ct1.num_gens,
        crate::todd_coxeter::coset_table_wf(ct1),
        crate::todd_coxeter::coset_table_consistent(ct1),
        crate::finite::coset_table_complete(ct1),
        h < ct1.num_cosets,
    ensures ({
        let pair = Seq::new(1, |_i: int| s1) + Seq::new(1, |_i: int| s2);
        h_act_word(ct1, ct2, phi, phi_inv, n1, pair, h) == h
    }),
{
    reveal(crate::todd_coxeter::coset_table_wf);
    reveal(crate::todd_coxeter::coset_table_consistent);
    reveal(crate::finite::coset_table_complete);

    let pair = Seq::new(1, |_i: int| s1) + Seq::new(1, |_i: int| s2);
    assert(pair.first() == s1);
    assert(pair.drop_first() =~= Seq::new(1, |_i: int| s2));
    assert(pair.drop_first().first() == s2);
    assert(pair.drop_first().drop_first() =~= Seq::<Symbol>::empty());
    assert(generator_index(s2) == generator_index(s1));

    let s1_col = sym_col(s1);
    let s2_col = sym_col(s2);
    assert(s2_col == crate::todd_coxeter::inverse_column(s1_col)) by {
        match s1 { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    lemma_ct_roundtrip(ct1, h, s1_col);
    let h1 = ct_lookup(ct1, h, s1_col);
    // h1 < ct1.num_cosets (from roundtrip ensures)
    // ct_lookup(ct1, h1, s2_col) == h (from roundtrip ensures)

    // h_act_word(pair, h) unrolls to:
    //   h_act_word([s2], h_act_sym(s1, h))
    //   = h_act_word([s2], ct_lookup(ct1, h, s1_col))   [since gen_index(s1) < n1]
    //   = h_act_word([s2], h1)
    //   = h_act_word([], h_act_sym(s2, h1))
    //   = h_act_sym(s2, h1)
    //   = ct_lookup(ct1, h1, s2_col)  [since gen_index(s2) < n1]
    //   = h                            [from roundtrip]
    assert(h_act_sym(ct1, ct2, phi, phi_inv, n1, s1, h) == h1);
    let h2 = h_act_sym(ct1, ct2, phi, phi_inv, n1, s2, h1);
    assert(h2 == ct_lookup(ct1, h1, s2_col));
    assert(h2 == h);

    // Explicitly unroll h_act_word for the pair:
    // h_act_word(pair, h) = h_act_word(pair.drop_first(), h_act_sym(pair.first(), h))
    //                     = h_act_word([s2], h1)
    //                     = h_act_word([], h_act_sym(s2, h1))
    //                     = h_act_sym(s2, h1)
    //                     = h2 = h
    assert(h_act_word(ct1, ct2, phi, phi_inv, n1, pair, h)
        == h_act_word(ct1, ct2, phi, phi_inv, n1, pair.drop_first(), h1));
    assert(h_act_word(ct1, ct2, phi, phi_inv, n1, pair.drop_first(), h1)
        == h_act_word(ct1, ct2, phi, phi_inv, n1,
            pair.drop_first().drop_first(), h2));
    assert(pair.drop_first().drop_first().len() == 0);
}

/// G₂ inverse pair: ct_lookup round-trips in ct2, phi translates.
proof fn lemma_h_inv_pair_g2(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    s1: Symbol, s2: Symbol,
    h: nat,
)
    requires
        is_inverse_pair(s1, s2),
        generator_index(s1) >= n1,
        generator_index(s1) < 2 * n1,  // valid AFP symbol (< n1 + n2 where n2 = n1)
        n1 == ct1.num_gens,
        n1 == ct2.num_gens,
        crate::todd_coxeter::coset_table_wf(ct2),
        crate::todd_coxeter::coset_table_consistent(ct2),
        crate::finite::coset_table_complete(ct2),
        h < ct1.num_cosets,
        forall|a: nat| a < ct1.num_cosets ==> #[trigger] phi_inv(a) < ct2.num_cosets,
        forall|b: nat| b < ct2.num_cosets ==> #[trigger] phi(b) < ct1.num_cosets,
        forall|b: nat| b < ct2.num_cosets ==> #[trigger] phi_inv(phi(b)) == b,
        forall|a: nat| a < ct1.num_cosets ==> #[trigger] phi(phi_inv(a)) == a,
    ensures ({
        let pair = Seq::new(1, |_i: int| s1) + Seq::new(1, |_i: int| s2);
        h_act_word(ct1, ct2, phi, phi_inv, n1, pair, h) == h
    }),
{
    reveal(crate::todd_coxeter::coset_table_wf);
    reveal(crate::todd_coxeter::coset_table_consistent);
    reveal(crate::finite::coset_table_complete);

    let pair = Seq::new(1, |_i: int| s1) + Seq::new(1, |_i: int| s2);
    assert(pair.first() == s1);
    assert(pair.drop_first() =~= Seq::new(1, |_i: int| s2));
    assert(pair.drop_first().first() == s2);
    assert(pair.drop_first().drop_first() =~= Seq::<Symbol>::empty());
    assert(generator_index(s2) == generator_index(s1));

    let s1_local = unshift_sym(s1, n1);
    let s1_local_col = sym_col(s1_local);
    // s1_local_col < 2 * ct2.num_gens because generator_index(s1) - n1 < n1 = ct2.num_gens
    assert(s1_local_col < 2 * ct2.num_gens) by {
        match s1 {
            Symbol::Gen(i) => {
                assert(s1_local == Symbol::Gen((i - n1) as nat));
                assert(s1_local_col == 2 * ((i - n1) as nat));
            }
            Symbol::Inv(i) => {
                assert(s1_local == Symbol::Inv((i - n1) as nat));
                assert(s1_local_col == 2 * ((i - n1) as nat) + 1);
            }
        }
    }

    let s2_local = unshift_sym(s2, n1);
    let s2_local_col = sym_col(s2_local);
    assert(s2_local_col == crate::todd_coxeter::inverse_column(s1_local_col)) by {
        match s1_local {
            Symbol::Gen(i) => {}
            Symbol::Inv(i) => {}
        }
    }

    let phi_inv_h = phi_inv(h);
    lemma_ct_roundtrip(ct2, phi_inv_h, s1_local_col);
    let mid = ct_lookup(ct2, phi_inv_h, s1_local_col);
    // mid < ct2.num_cosets (from roundtrip ensures)
    // ct_lookup(ct2, mid, s2_local_col) == phi_inv_h (from roundtrip ensures)

    // h1 = h_act_sym(s1, h) = phi(ct_lookup(ct2, phi_inv(h), s1_local_col)) = phi(mid)
    assert(h_act_sym(ct1, ct2, phi, phi_inv, n1, s1, h) == phi(mid));

    // phi_inv(h1) = phi_inv(phi(mid)) = mid (since mid < ct2.num_cosets)
    assert(phi_inv(phi(mid)) == mid);

    // h2 = h_act_sym(s2, h1) = phi(ct_lookup(ct2, phi_inv(phi(mid)), s2_local_col))
    //     = phi(ct_lookup(ct2, mid, s2_local_col))
    //     = phi(phi_inv_h)
    //     = h
    assert(ct_lookup(ct2, mid, s2_local_col) == phi_inv_h);

    // h1 = phi(mid)
    let h1 = phi(mid);
    assert(h_act_sym(ct1, ct2, phi, phi_inv, n1, s1, h) == h1);

    // phi_inv(h1) = phi_inv(phi(mid)) = mid
    assert(phi_inv(h1) == mid);

    // h_act_sym(s2, h1): s2 is G₂, so unshift, trace from phi_inv(h1) = mid
    let h2 = h_act_sym(ct1, ct2, phi, phi_inv, n1, s2, h1);
    // h2 = phi(ct_lookup(ct2, phi_inv(h1), s2_local_col))
    //    = phi(ct_lookup(ct2, mid, s2_local_col))
    //    = phi(phi_inv_h)
    //    = h
    assert(h2 == phi(ct_lookup(ct2, mid, s2_local_col)));
    assert(h2 == phi(phi_inv_h));
    assert(h2 == h);

    // Explicitly unroll h_act_word for the pair:
    assert(h_act_word(ct1, ct2, phi, phi_inv, n1, pair, h)
        == h_act_word(ct1, ct2, phi, phi_inv, n1, pair.drop_first(), h1));
    assert(h_act_word(ct1, ct2, phi, phi_inv, n1, pair.drop_first(), h1)
        == h_act_word(ct1, ct2, phi, phi_inv, n1,
            pair.drop_first().drop_first(), h2));
    assert(pair.drop_first().drop_first().len() == 0);
}

/// Combined inverse pair lemma dispatching to G₁ or G₂.
proof fn lemma_h_inv_pair(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    s1: Symbol, s2: Symbol,
    h: nat,
)
    requires
        is_inverse_pair(s1, s2),
        generator_index(s1) < 2 * n1,
        crate::todd_coxeter::coset_table_wf(ct1),
        crate::todd_coxeter::coset_table_consistent(ct1),
        crate::finite::coset_table_complete(ct1),
        crate::todd_coxeter::coset_table_wf(ct2),
        crate::todd_coxeter::coset_table_consistent(ct2),
        crate::finite::coset_table_complete(ct2),
        h < ct1.num_cosets,
        n1 == ct1.num_gens,
        n1 == ct2.num_gens,
        forall|a: nat| a < ct1.num_cosets ==> #[trigger] phi_inv(a) < ct2.num_cosets,
        forall|b: nat| b < ct2.num_cosets ==> #[trigger] phi(b) < ct1.num_cosets,
        forall|b: nat| b < ct2.num_cosets ==> #[trigger] phi_inv(phi(b)) == b,
        forall|a: nat| a < ct1.num_cosets ==> #[trigger] phi(phi_inv(a)) == a,
    ensures ({
        let pair = Seq::new(1, |_i: int| s1) + Seq::new(1, |_i: int| s2);
        h_act_word(ct1, ct2, phi, phi_inv, n1, pair, h) == h
    }),
{
    if generator_index(s1) < n1 {
        lemma_h_inv_pair_g1(ct1, ct2, phi, phi_inv, n1, s1, s2, h);
    } else {
        lemma_h_inv_pair_g2(ct1, ct2, phi, phi_inv, n1, s1, s2, h);
    }
}

// ============================================================
// Part J: AFP injectivity via h-only action
// ============================================================

/// H-only composition for split words.
proof fn lemma_h_act_step(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    w: Word, step: DerivationStep, w_prime: Word,
    h: nat,
)
    requires
        h_prereqs(ct1, ct2, phi, phi_inv, data),
        apply_step(amalgamated_free_product(data), w, step) == Some(w_prime),
        h < ct1.num_cosets,
        word_valid(w, data.p1.num_generators + data.p2.num_generators),
    ensures
        h_act_word(ct1, ct2, phi, phi_inv, data.p1.num_generators, w, h)
            == h_act_word(ct1, ct2, phi, phi_inv, data.p1.num_generators, w_prime, h),
{
    let n1 = data.p1.num_generators;
    let n_total = n1 + data.p2.num_generators;
    let afp = amalgamated_free_product(data);

    match step {
        DerivationStep::FreeReduce { position } => {
            let prefix = w.subrange(0, position);
            let pair = w.subrange(position, position + 2);
            let suffix = w.subrange(position + 2, w.len() as int);
            assert(w =~= prefix + pair + suffix) by {
                assert((prefix + pair + suffix).len() == w.len());
                assert forall|k: int| 0 <= k < w.len()
                    implies (prefix + pair + suffix)[k] == w[k] by {
                    if k < position {} else if k < position + 2 {} else {}
                }
            }
            assert(w_prime =~= prefix + suffix);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, prefix, pair + suffix, h);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, prefix, suffix, h);
            let hm = h_act_word(ct1, ct2, phi, phi_inv, n1, prefix, h);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, pair, suffix, hm);
            // Prove prefix is word_valid for the bound lemma
            assert(word_valid(prefix, n_total)) by {
                assert forall|k: int| 0 <= k < prefix.len()
                    implies symbol_valid(prefix[k], n_total)
                by { assert(prefix[k] == w[k]); }
            }
            lemma_h_act_bound(ct1, ct2, phi, phi_inv, data, prefix, h);
            // generator_index < 2*n1 for inv_pair (if n1 == data.p2.num_generators)
            assert(generator_index(w[position]) < n_total) by {
                assert(symbol_valid(w[position], n_total));
            }
            assert(generator_index(w[position + 1]) < n_total) by {
                assert(symbol_valid(w[position + 1], n_total));
            }
            lemma_h_inv_pair(ct1, ct2, phi, phi_inv, n1,
                w[position], w[position + 1], hm);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let prefix = w.subrange(0, position);
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            let suffix = w.subrange(position, w.len() as int);
            assert(w =~= prefix + suffix) by {
                assert((prefix + suffix).len() == w.len());
                assert forall|k: int| 0 <= k < w.len()
                    implies (prefix + suffix)[k] == w[k] by { if k < position {} else {} }
            }
            assert(w_prime =~= prefix + pair + suffix);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, prefix, suffix, h);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, prefix, pair + suffix, h);
            let hm = h_act_word(ct1, ct2, phi, phi_inv, n1, prefix, h);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, pair, suffix, hm);
            assert(word_valid(prefix, n_total)) by {
                assert forall|k: int| 0 <= k < prefix.len()
                    implies symbol_valid(prefix[k], n_total)
                by { assert(prefix[k] == w[k]); }
            }
            lemma_h_act_bound(ct1, ct2, phi, phi_inv, data, prefix, h);
            // symbol_valid from apply_step: AFP uses n1+n2 generators
            lemma_add_relators_num_generators(
                free_product(data.p1, data.p2), amalgamation_relators(data));
            assert(generator_index(symbol) < n_total);
            lemma_h_inv_pair(ct1, ct2, phi, phi_inv, n1,
                symbol, inverse_symbol(symbol), hm);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(afp, relator_index, inverted);
            let prefix = w.subrange(0, position);
            let suffix = w.subrange(position, w.len() as int);
            assert(w =~= prefix + suffix) by {
                assert((prefix + suffix).len() == w.len());
                assert forall|k: int| 0 <= k < w.len()
                    implies (prefix + suffix)[k] == w[k] by { if k < position {} else {} }
            }
            assert(w_prime =~= prefix + r + suffix);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, prefix, suffix, h);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, prefix, r + suffix, h);
            let hm = h_act_word(ct1, ct2, phi, phi_inv, n1, prefix, h);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, r, suffix, hm);
            assert(word_valid(prefix, n_total)) by {
                assert forall|k: int| 0 <= k < prefix.len()
                    implies symbol_valid(prefix[k], n_total)
                by { assert(prefix[k] == w[k]); }
            }
            lemma_h_act_bound(ct1, ct2, phi, phi_inv, data, prefix, h);
            lemma_h_relator(ct1, ct2, phi, phi_inv, data, relator_index, inverted, hm);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(afp, relator_index, inverted);
            let rlen = r.len();
            let prefix = w.subrange(0, position);
            let suffix = w.subrange(position + rlen as int, w.len() as int);
            assert(w =~= prefix + r + suffix) by {
                assert((prefix + r + suffix).len() == w.len());
                assert forall|k: int| 0 <= k < w.len()
                    implies (prefix + r + suffix)[k] == w[k] by {
                    if k < position {} else if k < position + rlen as int {
                        assert(w.subrange(position, position + rlen as int) == r);
                    } else {}
                }
            }
            assert(w_prime =~= prefix + suffix);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, prefix, r + suffix, h);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, prefix, suffix, h);
            let hm = h_act_word(ct1, ct2, phi, phi_inv, n1, prefix, h);
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, r, suffix, hm);
            assert(word_valid(prefix, n_total)) by {
                assert forall|k: int| 0 <= k < prefix.len()
                    implies symbol_valid(prefix[k], n_total)
                by { assert(prefix[k] == w[k]); }
            }
            lemma_h_act_bound(ct1, ct2, phi, phi_inv, data, prefix, h);
            lemma_h_relator(ct1, ct2, phi, phi_inv, data, relator_index, inverted, hm);
        },
    }
}

/// AFP relator acts trivially on h-only action.
proof fn lemma_h_relator(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    relator_index: nat, inverted: bool,
    h: nat,
)
    requires
        h_prereqs(ct1, ct2, phi, phi_inv, data),
        relator_index < amalgamated_free_product(data).relators.len(),
        h < ct1.num_cosets,
    ensures ({
        let r = get_relator(amalgamated_free_product(data), relator_index, inverted);
        let n1 = data.p1.num_generators;
        h_act_word(ct1, ct2, phi, phi_inv, n1, r, h) == h
    }),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;
    let r = get_relator(afp, relator_index, inverted);
    lemma_afp_relators(data);

    if relator_index < data.p1.relators.len() {
        // G₁ relator: r is a G₁-word, trace returns to start.
        lemma_afp_relator_g1(data, relator_index);
        // r = get_relator(p1, relator_index, inverted) — same relator
        // r is a left word (all generators < n1 from presentation_valid)
        reveal(presentation_valid);
        let raw = data.p1.relators[relator_index as int];
        assert(word_valid(raw, n1));
        // r is either raw or inverse_word(raw), both word_valid for n1
        assert(is_left_word(r, n1)) by {
            if inverted {
                crate::word::lemma_inverse_word_valid(raw, n1);
                assert(word_valid(inverse_word(raw), n1));
                assert forall|k: int| 0 <= k < r.len()
                    implies generator_index(r[k]) < n1
                by { assert(symbol_valid(r[k], n1)); }
            } else {
                assert forall|k: int| 0 <= k < r.len()
                    implies generator_index(r[k]) < n1
                by { assert(symbol_valid(r[k], n1)); }
            }
        }
        // By h_act_is_trace: trace_word(ct1, h, r) == Some(h_act_word(..., r, h))
        lemma_h_act_is_trace(ct1, ct2, phi, phi_inv, n1, r, h);
        // trace_word(ct1, h, r) == Some(h) by relator_closed
        // relator_closed says: for all c, trace_word(ct1, c, p1.relators[i]) == Some(c)
        // We need: trace_word(ct1, h, r) == Some(h)
        // r = get_relator(p1, relator_index, inverted)
        // If not inverted: r = p1.relators[relator_index]. relator_closed gives trace == Some(h).
        // If inverted: r = inverse_word(p1.relators[relator_index]).
        //   Need trace of inverse relator also returns to start.
        //   This follows from table consistency: trace(w) = h iff trace(inv(w)) = h
        //   (since the table is consistent, tracing back along inverse returns to start).
        //
        // For the non-inverted case:
        if !inverted {
            // r == p1.relators[relator_index]
            // relator_closed(ct1, p1) says trace_word(ct1, h, r) == Some(h)
            // The ensures of relator_closed uses the relator index.
            // relator_closed = forall c, r_idx: trace_word(ct1, c, p1.relators[r_idx]) == Some(c)
            // But ct1 is relator-closed for p1 (from valid_cayley).
            // So trace_word(ct1, h, data.p1.relators[relator_index]) == Some(h).
            reveal(crate::todd_coxeter::relator_closed);
            // Fire triggers: ct1.table[h] and data.p1.relators[relator_index]
            let _ = ct1.table[h as int];
            let _ = data.p1.relators[relator_index as int];
            assert(crate::todd_coxeter::trace_word(ct1, h, data.p1.relators[relator_index as int]) == Some(h));
            assert(r == data.p1.relators[relator_index as int]);
        } else {
            // Inverted: r = inverse_word(p1.relators[relator_index])
            // trace(ct1, h, inv(relator)) also returns h because:
            // trace(ct1, h, relator) == Some(h) means h --relator--> h in the table.
            // By consistency: h --inv(relator)--> h as well.
            // This is a standard property of consistent relator-closed tables.
            // Use lemma_trace_word_concat: trace(h, relator ++ inv(relator)) = trace(trace(h, relator), inv(relator))
            // And trace(h, relator) = h. So trace(h, inv(relator)) follows from
            // trace(h, relator ++ inv(relator)) = h (since relator ++ inv(relator) traces to h
            // because relator-closed on the trivial word... hmm, this isn't quite right).
            //
            // Actually: for a consistent complete table, trace(c, inv(w)) is the unique d such that
            // trace(d, w) = c. Since trace(h, w) = h: trace(h, inv(w)) = h.
            // This follows from a lemma about inverse word traces.
            // For now: assume this standard property.
            // TODO: prove or call existing lemma for inverse-word trace.
            // trace(ct1, h, relator) == Some(h) by relator_closed
            reveal(crate::todd_coxeter::relator_closed);
            let _ = ct1.table[h as int];
            let _ = data.p1.relators[relator_index as int];
            assert(crate::todd_coxeter::trace_word(ct1, h, raw) == Some(h));
            // By lemma_trace_inverse_word: trace(h, inv(relator)) == Some(h)
            crate::completeness::lemma_trace_inverse_word(ct1, h, raw);
            assert(crate::todd_coxeter::trace_word(ct1, h, inverse_word(raw)) == Some(h));
            assert(r == inverse_word(raw));
        }
    } else if relator_index < data.p1.relators.len() + data.p2.relators.len() {
        // G₂ relator: all symbols have gen_index >= n1.
        // The h-only action: each G₂ symbol does phi(ct_lookup(ct2, phi_inv(h), col)).
        // For a G₂ relator r_g2: processing all symbols traces through ct2.
        // ct2 is relator-closed: trace_word(ct2, phi_inv(h), r_g2) == Some(phi_inv(h)).
        // After translating back via phi: phi(phi_inv(h)) == h.
        //
        // More precisely: h_act_word(r, h) where r is a shifted G₂ relator.
        // Each symbol of r has gen_index >= n1, so h_act_sym uses the G₂ branch:
        //   h → phi(ct_lookup(ct2, phi_inv(h), col_local))
        // The composition of all symbols = phi(trace_word(ct2, phi_inv(h), unshifted_r)).
        // By relator_closed(ct2, p2): trace_word(ct2, phi_inv(h), unshifted_r) == Some(phi_inv(h)).
        // So the result = phi(phi_inv(h)) = h. ✓
        // G₂ relator: call lemma_h_act_g2_relator
        let g2_idx = (relator_index - data.p1.relators.len()) as nat;
        lemma_h_act_g2_relator(ct1, ct2, phi, phi_inv, data, g2_idx, inverted, h);
        // The ensures of lemma_h_act_g2_relator gives:
        // h_act_word(shift(p2.relators[g2_idx]), h) == h (for non-inverted)
        // h_act_word(inverse(shift(p2.relators[g2_idx])), h) == h (for inverted)
        // We need: h_act_word(r, h) == h where r = get_relator(afp, relator_index, inverted).
        // r is the AFP relator at the G₂ relator position.
        // Need to connect r to shift(p2.relators[g2_idx]) or its inverse.
        // By the AFP relator structure: afp.relators[relator_index] == shift(p2.relators[g2_idx]).
        // get_relator either returns it or its inverse.
    } else {
        // Identification relator: u_i · inv(shift(v_i)).
        // Identification relator: u_i · inv(shift(v_i)).
        let ident_idx = (relator_index - data.p1.relators.len() - data.p2.relators.len()) as nat;
        let (u_i, v_i) = data.identifications[ident_idx as int];
        let shifted_v = shift_word(v_i, n1);
        let inv_shifted_v = inverse_word(shifted_v);
        let raw_rel = amalgamation_relator(data, ident_idx as int);
        // raw_rel = concat(u_i, inv_shifted_v)

        // AFP relator at this index = raw_rel = concat(u_i, inv_shifted_v)
        assert(raw_rel == concat(u_i, inv_shifted_v));
        lemma_afp_relator_ident(data, ident_idx);
        // afp.relators[relator_index] == raw_rel

        // For non-inverted: r = raw_rel = concat(u_i, inv_shifted_v)
        // For inverted: r = inverse_word(raw_rel)
        if !inverted {
            assert(r == raw_rel);
            // r = concat(u_i, inv_shifted_v)
            // By h_act_concat: h_act_word(r, h) = h_act_word(inv_shifted_v, h_act_word(u_i, h))
            lemma_h_act_concat(ct1, ct2, phi, phi_inv, n1, u_i, inv_shifted_v, h);
            let h_mid = h_act_word(ct1, ct2, phi, phi_inv, n1, u_i, h);

            // u_i is a G₁-word: h_act_is_trace gives trace_word(ct1, h, u_i) = Some(h_mid)
            reveal(presentation_valid);
            assert(word_valid(u_i, n1));
            assert(is_left_word(u_i, n1)) by {
                assert forall|k: int| 0 <= k < u_i.len()
                    implies generator_index(u_i[k]) < n1
                by { assert(symbol_valid(u_i[k], n1)); }
            }
            lemma_h_act_is_trace(ct1, ct2, phi, phi_inv, n1, u_i, h);
            // trace_word(ct1, h, u_i) == Some(h_mid)

            // inv_shifted_v is a G₂-word (shifted inverse of v_i)
            // inverse_word(shift_word(v_i, n1)) =~= shift_word(inverse_word(v_i), n1)
            crate::free_product::lemma_shift_inverse_word(v_i, n1);
            let inv_v = inverse_word(v_i);
            let shift_inv_v = shift_word(inv_v, n1);
            assert(inv_shifted_v =~= shift_inv_v);

            // inv_v is word_valid for p2
            assert(word_valid(v_i, data.p2.num_generators));
            crate::word::lemma_inverse_word_valid(v_i, data.p2.num_generators);
            assert(word_valid(inv_v, data.p2.num_generators));

            // shift relation
            assert forall|k: int| 0 <= k < shift_inv_v.len()
                implies shift_inv_v[k] == shift_symbol(#[trigger] inv_v[k], n1)
            by {}

            // h_mid < ct1.num_cosets (needed for h_act_g2_phi_inv_trace)
            crate::completeness::lemma_trace_complete(ct1, h, u_i);
            reveal(crate::todd_coxeter::coset_table_wf);
            // trace_word is Some, so h_mid is the unwrapped value < ct1.num_cosets
            // Actually h_act_is_trace gives trace_word(ct1, h, u_i) == Some(h_mid)
            // and h_mid = h_act_word(..., u_i, h). We need h_mid < ct1.num_cosets.
            lemma_h_act_bound(ct1, ct2, phi, phi_inv, data, u_i, h);

            // By h_act_g2_phi_inv_trace on inv_shifted_v:
            // trace_word(ct2, phi_inv(h_mid), inv_v) == Some(phi_inv(h_act_word(inv_shifted_v, h_mid)))
            lemma_h_act_g2_phi_inv_trace(ct1, ct2, phi, phi_inv, data,
                shift_inv_v, inv_v, h_mid);

            // Now: trace_word(ct2, phi_inv(h_mid), inv_v) == Some(phi_inv(result))
            // where result = h_act_word(inv_shifted_v, h_mid)
            //
            // We need result == h.
            // phi_inv(h_mid) = phi_inv(trace_word(ct1, h, u_i).unwrap())
            // By phi compatibility (generator respecting):
            //   phi(trace(ct2, 0, v_i)) == trace(ct1, 0, u_i)
            // But we need the trace from h, not from 0...
            //
            // Actually, the phi compatibility in valid_phi says:
            //   phi(ct_lookup(ct2, h2, col)) == ct_lookup(ct1, phi(h2), col)
            // This means: for EACH SYMBOL, the phi-translated action equals the ct1 action.
            // So: phi_inv(h_mid) = phi_inv(trace(ct1, h, u_i))
            //   = trace(ct2, phi_inv(h), unshift(u_i))  [by phi_inv compatibility]
            // But u_i IS a G₁-word, not a G₂-word. The phi compatibility applies to
            // ct2 columns, not ct1 columns directly.
            //
            // Wait — the phi compatibility says phi(ct_lookup(ct2, h2, col)) == ct_lookup(ct1, phi(h2), col).
            // Taking phi_inv: ct_lookup(ct2, h2, col) == phi_inv(ct_lookup(ct1, phi(h2), col)).
            // With h2 = phi_inv(h) and phi(h2) = h:
            //   ct_lookup(ct2, phi_inv(h), col) == phi_inv(ct_lookup(ct1, h, col))
            //
            // So for EACH SYMBOL col of u_i:
            //   phi_inv(ct_lookup(ct1, h, col)) == ct_lookup(ct2, phi_inv(h), col)
            //
            // This means: phi_inv(trace(ct1, h, u_i)) == trace(ct2, phi_inv(h), u_i)
            // (where u_i is viewed as using the SAME columns in ct2).
            //
            // And then: trace(ct2, phi_inv(h_mid), inv(v_i))
            //   = trace(ct2, trace(ct2, phi_inv(h), u_i), inv(v_i))
            //
            // Hmm, this needs u_i and v_i to be related via the identification.
            // The phi generator compatibility says: phi(trace(ct2, 0, v_i)) == trace(ct1, 0, u_i).
            // This is a GLOBAL statement about the complete words, not per-symbol.
            //
            // For the identification relator to act trivially:
            // After u_i: h_mid = trace(ct1, h, u_i)
            // phi_inv(h_mid) should equal trace(ct2, phi_inv(h), u_i) [by phi compat per-symbol]
            //
            // BUT u_i uses G₁ generators (columns 0..2n1-1). And ct2 also has columns
            // 0..2n1-1 (since ct2.num_gens == n1). So tracing u_i through ct2 IS valid.
            //
            // Then: trace(ct2, phi_inv(h), u_i) — what does this represent?
            // u_i is a word in G₁'s generators. Tracing it through ct2 (G₂'s Cayley table)
            // gives... well, ct2 has the same columns as ct1 (same num_gens).
            // By the phi compatibility: phi_inv(trace(ct1, h, u_i)) == trace(ct2, phi_inv(h), u_i).
            // So phi_inv(h_mid) == trace(ct2, phi_inv(h), u_i).
            //
            // Then: trace(ct2, phi_inv(h_mid), inv(v_i))
            //   = trace(ct2, trace(ct2, phi_inv(h), u_i), inv(v_i))
            //   = trace(ct2, phi_inv(h), concat(u_i, inv(v_i)))  [by trace concat]
            //
            // Now: the valid_phi generator-respecting says:
            //   phi(trace(ct2, 0, v_i)) == trace(ct1, 0, u_i)
            // This doesn't directly give: trace(ct2, phi_inv(h), concat(u_i, inv(v_i))) == phi_inv(h).
            //
            // I think I need a STRONGER phi compatibility: not just for generators,
            // but for entire words. Or use the per-symbol compatibility to show
            // phi_inv(trace(ct1, h, u_i)) == trace(ct2, phi_inv(h), u_i).
            //
            // This per-symbol compatibility (phi_inv commutes with ct1/ct2 traces)
            // is the KEY property that makes the identification relator trivial.
            // It follows from the existing valid_phi per-column property by induction.
            //
            // Let me just assert the conclusion and see if Z3 can derive it.
            // The conclusion: trace(ct2, phi_inv(h_mid), inv(v_i)) == Some(phi_inv(h)).
            // This means: phi_inv(result) == phi_inv(h), hence result == h.

            // For now: this is the deepest mathematical step.
            // It requires proving phi_inv commutes with multi-symbol traces,
            // which needs another inductive lemma.
            assert(false); // LAST GAP: phi_inv commutes with trace
    }
}

/// H-only action respects AFP derivation.
proof fn lemma_h_act_deriv(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
    h: nat,
)
    requires
        h_prereqs(ct1, ct2, phi, phi_inv, data),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        h < ct1.num_cosets,
        word_valid(w1, data.p1.num_generators + data.p2.num_generators),
    ensures
        h_act_word(ct1, ct2, phi, phi_inv, data.p1.num_generators, w1, h)
            == h_act_word(ct1, ct2, phi, phi_inv, data.p1.num_generators, w2, h),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(w1 == w2);
    } else {
        let afp = amalgamated_free_product(data);
        let step = steps.first();
        let w_mid = apply_step(afp, w1, step).unwrap();
        lemma_h_act_step(ct1, ct2, phi, phi_inv, data, w1, step, w_mid, h);
        // w_mid is word_valid (derivation step preserves word_valid)
        lemma_add_relators_num_generators(
            free_product(data.p1, data.p2), amalgamation_relators(data));
        lemma_amalgamated_valid(data);
        lemma_step_preserves_word_valid_pres(afp, w1, step, w_mid);
        lemma_h_act_deriv(ct1, ct2, phi, phi_inv, data, steps.drop_first(), w_mid, w2, h);
    }
}

/// For a G₁-word: h_act_word(w, h) matches trace_word(ct1, h, w) for any h.
proof fn lemma_h_act_is_trace(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    w: Word,
    h: nat,
)
    requires
        is_left_word(w, n1),
        n1 == ct1.num_gens,
        crate::todd_coxeter::coset_table_wf(ct1),
        crate::finite::coset_table_complete(ct1),
        h < ct1.num_cosets,
    ensures
        crate::todd_coxeter::trace_word(ct1, h, w) == Some(h_act_word(ct1, ct2, phi, phi_inv, n1, w, h)),
    decreases w.len(),
{
    if w.len() == 0 {
        // h_act_word(ε, h) = h
        // trace_word(ct1, h, ε) = Some(h)
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(generator_index(s) < n1);
        assert(is_left_word(rest, n1)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies generator_index(rest[k]) < n1
            by { assert(rest[k] == w[k + 1]); }
        }
        // h_act_sym(s, h) = ct_lookup(ct1, h, sym_col(s))
        //                  = match ct1.table[h][sym_col(s)] { Some(v) => v, None => 0 }
        // trace_word(ct1, h, w):
        //   col = symbol_to_column(w.first()) = sym_col(s)
        //   match ct1.table[h][col] { Some(next) => trace_word(ct1, next, rest), None => None }
        //
        // If table[h][col] is Some(next):
        //   ct_lookup(ct1, h, col) = next = h_act_sym result
        //   trace_word continues with (next, rest)
        //   By IH: h_act_word(rest, next) == trace_word(ct1, next, rest)
        //
        // If table[h][col] is None:
        //   ct_lookup returns 0
        //   trace_word returns None
        //   ensures says h_act_word(...) == h (the None branch)
        //   This case shouldn't happen for complete tables.
        // h_act_sym for G₁ symbol = ct_lookup(ct1, h, sym_col(s))
        // trace_word for first symbol = match ct1.table[h][symbol_to_column(s)]
        // sym_col == symbol_to_column, and ct_lookup unwraps the match.
        // They compute the same next value.
        // Both h_act_sym and trace_word use ct1.table[h][sym_col(s)] for the next value.
        // Help Z3 see this by asserting the table entry explicitly.
        let col = sym_col(s);
        let next_h = h_act_sym(ct1, ct2, phi, phi_inv, n1, s, h);
        assert(next_h == ct_lookup(ct1, h, col));
        // trace_word(ct1, h, w) = match ct1.table[h][col] {
        //     Some(next) => trace_word(ct1, next, rest),
        //     None => None
        // }
        // ct_lookup(ct1, h, col) = match ct1.table[h][col] {
        //     Some(v) => v, None => 0
        // }
        // When Some(v): next_h == v and both continue from v.
        // When None: trace_word returns None, ensures rhs = h.
        //   But h_act_word continues with 0, not h. This is a discrepancy.
        //   For complete tables: entry is always Some, so None doesn't happen.
        //
        // With completeness: entry is always Some, so next_h < ct1.num_cosets.
        reveal(crate::todd_coxeter::coset_table_wf);
        reveal(crate::finite::coset_table_complete);
        assert(col < 2 * ct1.num_gens) by {
            match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
        }
        assert(next_h < ct1.num_cosets);
        lemma_h_act_is_trace(ct1, ct2, phi, phi_inv, n1, rest, next_h);
    }
}

/// h_act_word preserves the bound h < ct1.num_cosets.
proof fn lemma_h_act_bound(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    w: Word,
    h: nat,
)
    requires
        h_prereqs(ct1, ct2, phi, phi_inv, data),
        h < ct1.num_cosets,
        word_valid(w, data.p1.num_generators + data.p2.num_generators),
    ensures
        h_act_word(ct1, ct2, phi, phi_inv, data.p1.num_generators, w, h) < ct1.num_cosets,
    decreases w.len(),
{
    reveal(crate::todd_coxeter::coset_table_wf);
    reveal(crate::finite::coset_table_complete);
    let n1 = data.p1.num_generators;

    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, n1 + data.p2.num_generators));
        assert(word_valid(rest, n1 + data.p2.num_generators)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], n1 + data.p2.num_generators)
            by { assert(rest[k] == w[k + 1]); }
        }

        let next_h = h_act_sym(ct1, ct2, phi, phi_inv, n1, s, h);
        // Prove next_h < ct1.num_cosets by case analysis
        if generator_index(s) < n1 {
            // G₁ symbol: next_h = ct_lookup(ct1, h, sym_col(s))
            // sym_col(s) < 2 * ct1.num_gens because gen_index(s) < n1 = ct1.num_gens
            let col = sym_col(s);
            assert(col < 2 * ct1.num_gens) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
            // By wf + complete: table[h][col] is Some(v) with v < ct1.num_cosets
        } else {
            // G₂ symbol: next_h = phi(ct_lookup(ct2, phi_inv(h), sym_col(unshift(s))))
            // gen_index(s) < n1 + n2, gen_index(s) >= n1, so gen_index(s) - n1 < n2 = ct2.num_gens
            let s_local = unshift_sym(s, n1);
            let col = sym_col(s_local);
            assert(col < 2 * ct2.num_gens) by {
                match s {
                    Symbol::Gen(i) => {
                        assert(generator_index(s) == i);
                        assert(i < n1 + data.p2.num_generators);
                        assert(s_local == Symbol::Gen((i - n1) as nat));
                    }
                    Symbol::Inv(i) => {
                        assert(generator_index(s) == i);
                        assert(i < n1 + data.p2.num_generators);
                        assert(s_local == Symbol::Inv((i - n1) as nat));
                    }
                }
            }
            // phi_inv(h) < ct2.num_cosets, ct_lookup < ct2.num_cosets, phi(that) < ct1.num_cosets
        }
        assert(next_h < ct1.num_cosets);
        lemma_h_act_bound(ct1, ct2, phi, phi_inv, data, rest, next_h);
    }
}

/// For a pure G₂-word (shifted `sw`, corresponding unshifted `uw`):
/// phi_inv(h_act_word(sw, h)) matches the ct2-trace of phi_inv(h) through uw.
///
/// Specifically: phi_inv(result) == trace_word(ct2, phi_inv(h), uw).unwrap().
/// And result < ct1.num_cosets.
proof fn lemma_h_act_g2_phi_inv_trace(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    sw: Word,  // shifted G₂-word
    uw: Word,  // unshifted (corresponding symbols in ct2's generators)
    h: nat,
)
    requires
        h_prereqs(ct1, ct2, phi, phi_inv, data),
        h < ct1.num_cosets,
        sw.len() == uw.len(),
        // sw is the shift of uw
        forall|k: int| 0 <= k < sw.len() ==> sw[k] == shift_symbol(#[trigger] uw[k], data.p1.num_generators),
        // uw is word_valid for p2
        word_valid(uw, data.p2.num_generators),
    ensures
        h_act_word(ct1, ct2, phi, phi_inv, data.p1.num_generators, sw, h) < ct1.num_cosets,
        crate::todd_coxeter::trace_word(ct2, phi_inv(h), uw)
            == Some(phi_inv(h_act_word(ct1, ct2, phi, phi_inv, data.p1.num_generators, sw, h))),
    decreases sw.len(),
{
    reveal(crate::todd_coxeter::coset_table_wf);
    reveal(crate::finite::coset_table_complete);
    let n1 = data.p1.num_generators;

    if sw.len() == 0 {
        assert(uw.len() == 0);
        assert(sw =~= Seq::<Symbol>::empty());
        assert(uw =~= Seq::<Symbol>::empty());
        assert(h_act_word(ct1, ct2, phi, phi_inv, n1, sw, h) == h);
        assert(crate::todd_coxeter::trace_word(ct2, phi_inv(h), uw) == Some(phi_inv(h)));
    } else {
        let s = sw.first();
        let s_uw = uw.first();
        let rest_sw = sw.drop_first();
        let rest_uw = uw.drop_first();

        assert(s == shift_symbol(s_uw, n1));
        assert(symbol_valid(s_uw, data.p2.num_generators));
        assert(word_valid(rest_uw, data.p2.num_generators)) by {
            assert forall|k: int| 0 <= k < rest_uw.len()
                implies symbol_valid(rest_uw[k], data.p2.num_generators)
            by { assert(rest_uw[k] == uw[k + 1]); }
        }
        assert forall|k: int| 0 <= k < rest_sw.len()
            implies rest_sw[k] == shift_symbol(#[trigger] rest_uw[k], n1)
        by { assert(rest_sw[k] == sw[k + 1]); assert(rest_uw[k] == uw[k + 1]); }

        // s is a G₂ symbol: generator_index(s) >= n1
        assert(generator_index(s) >= n1) by {
            match s_uw {
                Symbol::Gen(i) => { assert(s == Symbol::Gen(i + n1)); }
                Symbol::Inv(i) => { assert(s == Symbol::Inv(i + n1)); }
            }
        }

        // h_act_sym(s, h) = phi(ct_lookup(ct2, phi_inv(h), sym_col(unshift(s))))
        // unshift(s) = s_uw
        assert(unshift_sym(s, n1) == s_uw) by {
            match s_uw {
                Symbol::Gen(i) => { assert(s == Symbol::Gen(i + n1)); }
                Symbol::Inv(i) => { assert(s == Symbol::Inv(i + n1)); }
            }
        }

        let col = sym_col(s_uw);
        assert(col < 2 * ct2.num_gens) by {
            match s_uw { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
        }
        let h_g2 = phi_inv(h);
        let next_g2 = ct_lookup(ct2, h_g2, col);
        assert(next_g2 < ct2.num_cosets);
        let next_h = phi(next_g2);
        assert(next_h < ct1.num_cosets);
        assert(phi_inv(next_h) == next_g2);

        // IH on rest
        lemma_h_act_g2_phi_inv_trace(ct1, ct2, phi, phi_inv, data, rest_sw, rest_uw, next_h);

        // trace_word(ct2, h_g2, uw) unfolds:
        // col = symbol_to_column(uw.first()) = sym_col(s_uw) = col
        // ct2.table[h_g2][col] is Some(next_g2) [by complete+wf]
        assert(ct2.table[h_g2 as int][col as int] is Some);
        assert(ct2.table[h_g2 as int][col as int] == Some(next_g2));
        // trace_word(ct2, h_g2, uw) = trace_word(ct2, next_g2, rest_uw)
        assert(crate::todd_coxeter::symbol_to_column(uw.first()) == col);
    }
}

/// For a pure G₂ relator (shifted), h_act_word returns h.
/// Uses: ct2 is relator-closed, phi compatibility.
proof fn lemma_h_act_g2_relator(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    g2_idx: nat,
    inverted: bool,
    h: nat,
)
    requires
        h_prereqs(ct1, ct2, phi, phi_inv, data),
        g2_idx < data.p2.relators.len(),
        h < ct1.num_cosets,
    ensures ({
        let n1 = data.p1.num_generators;
        let shifted_rel = shift_word(data.p2.relators[g2_idx as int], n1);
        let r = if inverted { inverse_word(shifted_rel) } else { shifted_rel };
        h_act_word(ct1, ct2, phi, phi_inv, n1, r, h) == h
    }),
{
    // Use the phi compatibility: each G₂ symbol action via phi equals a ct1 trace step.
    // phi(ct_lookup(ct2, phi_inv(h), col)) == ct_lookup(ct1, h, col) [phi compatibility]
    // So h_act_word on a shifted G₂ word acts the same as tracing the UNSHIFTED word through ct1.
    // But the relator is from p2, and ct1 is for p1. Unless p1 == p2...
    //
    // Better approach: track phi_inv through the word.
    // phi_inv(h_act_word(shifted_relator, h)) = trace_word(ct2, phi_inv(h), unshifted_relator)
    // By relator_closed(ct2, p2): = phi_inv(h)
    // phi of both sides: h_act_word = phi(phi_inv(h)) = h.
    //
    // We prove this using lemma_h_act_g2_phi_inv_trace which establishes the phi_inv tracking.
    let n1 = data.p1.num_generators;
    let raw = data.p2.relators[g2_idx as int];
    let shifted = shift_word(raw, n1);
    let r = if inverted { inverse_word(shifted) } else { shifted };

    // For the non-inverted case: use h_act_g2_phi_inv_trace on the shifted relator
    // Prove preconditions for lemma_h_act_g2_phi_inv_trace
    // 1. shift_word(raw, n1)[k] == shift_symbol(raw[k], n1) — by definition of shift_word
    assert forall|k: int| 0 <= k < shifted.len()
        implies shifted[k] == shift_symbol(#[trigger] raw[k], n1)
    by {}
    // 2. word_valid(raw, data.p2.num_generators) — from presentation_valid(p2)
    reveal(presentation_valid);
    assert(word_valid(raw, data.p2.num_generators));

    if !inverted {
        lemma_h_act_g2_phi_inv_trace(ct1, ct2, phi, phi_inv, data, shifted, raw, h);
        // Now: phi_inv(h_act_word(shifted, h)) == match trace_word(ct2, phi_inv(h), raw) { Some(v) => v, None => phi_inv(h) }
        // By relator_closed(ct2, p2): trace_word(ct2, phi_inv(h), raw) == Some(phi_inv(h))
        reveal(crate::todd_coxeter::relator_closed);
        let _ = ct2.table[phi_inv(h) as int];
        let _ = data.p2.relators[g2_idx as int];
        assert(crate::todd_coxeter::trace_word(ct2, phi_inv(h), raw) == Some(phi_inv(h)));
        // phi_inv(h_act_word(shifted, h)) == phi_inv(h)
        // h_act_word(shifted, h) == h (since phi is injective on the range)
    } else {
        // Inverted: r = inverse_word(shifted)
        // trace(ct2, phi_inv(h), raw) == Some(phi_inv(h)) by relator_closed
        // trace(ct2, phi_inv(h), inverse_word(raw)) == Some(phi_inv(h)) by lemma_trace_inverse_word
        reveal(crate::todd_coxeter::relator_closed);
        let _ = ct2.table[phi_inv(h) as int];
        let _ = data.p2.relators[g2_idx as int];
        assert(crate::todd_coxeter::trace_word(ct2, phi_inv(h), raw) == Some(phi_inv(h)));
        crate::completeness::lemma_trace_inverse_word(ct2, phi_inv(h), raw);
        // trace(ct2, phi_inv(h), inverse_word(raw)) == Some(phi_inv(h))

        // Now need to connect inverse_word(shifted) to shifted(inverse_word(raw))
        // inverse_word(shift_word(raw, n1)): reverses and inverts each symbol.
        // shift_word(inverse_word(raw), n1): shifts each symbol of the inverse.
        // These are NOT the same in general... inverse reverses order, shift doesn't.
        // Actually: inverse_word(shift_word(w, n)) =~= shift_word(inverse_word(w), n)
        // This is because shift preserves inverse pairs and commutes with reversal.
        // Let me use the existing lemma_shift_inverse_word from free_product.rs.
        crate::free_product::lemma_shift_inverse_word(raw, n1);
        // inverse_word(shift_word(raw, n1)) =~= shift_word(inverse_word(raw), n1)
        // So r =~= shift_word(inverse_word(raw), n1)

        let inv_raw = inverse_word(raw);
        crate::word::lemma_inverse_word_valid(raw, data.p2.num_generators);
        let shifted_inv = shift_word(inv_raw, n1);
        assert forall|k: int| 0 <= k < shifted_inv.len()
            implies shifted_inv[k] == shift_symbol(#[trigger] inv_raw[k], n1)
        by {}
        lemma_h_act_g2_phi_inv_trace(ct1, ct2, phi, phi_inv, data,
            shifted_inv, inv_raw, h);
        // phi_inv(h_act_word(shift_word(inverse_word(raw), n1), h))
        //   == trace(ct2, phi_inv(h), inverse_word(raw)) == phi_inv(h)
    }
}

/// AFP injectivity for finite groups.
pub proof fn lemma_afp_injectivity(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    w: Word,
)
    requires
        h_prereqs(ct1, ct2, phi, phi_inv, data),
        word_valid(w, data.p1.num_generators),
        equiv_in_presentation(amalgamated_free_product(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.p1, w, empty_word()),
{
    let n1 = data.p1.num_generators;
    let afp = amalgamated_free_product(data);
    let d = choose|d: Derivation| derivation_valid(afp, d, w, empty_word());

    // w is word_valid for n1, hence for n1+n2 (monotonicity)
    assert(word_valid(w, n1 + data.p2.num_generators)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies symbol_valid(w[k], n1 + data.p2.num_generators)
        by { assert(symbol_valid(w[k], n1)); }
    }

    // Step 1: h_act_word(w, 0) == h_act_word(ε, 0) == 0
    lemma_h_act_deriv(ct1, ct2, phi, phi_inv, data, d.steps, w, empty_word(), 0);

    // Step 2: for G₁-word w, h_act_word(w, 0) == trace_word(ct1, 0, w)
    assert(is_left_word(w, n1)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies generator_index(w[k]) < n1
        by { assert(symbol_valid(w[k], n1)); }
    }
    lemma_h_act_is_trace(ct1, ct2, phi, phi_inv, n1, w, 0);

    // Step 3: trace_word(ct1, 0, w) == 0 → w ≡ ε in G₁
    crate::completeness::lemma_trace_complete(ct1, 0, w);
    assert(crate::todd_coxeter::trace_word(ct1, 0, empty_word()) == Some(0nat));
    crate::coset_group::axiom_coset_table_sound(ct1, data.p1, w, empty_word());
}

} // verus!
