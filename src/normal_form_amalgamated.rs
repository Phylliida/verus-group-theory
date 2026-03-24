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
// Part G: Van der Waerden action — correct definition
// ============================================================
//
// Prerequisites:
//   ct1: Cayley table for G₁ (every G₁-element is a nat < ct1.num_cosets)
//   ct2: Cayley table for G₂
//   st1: Subgroup coset table for A ≤ G₁ (coset 0 = A itself)
//   st2: Subgroup coset table for B ≤ G₂ (coset 0 = B itself)
//   phi: B→A isomorphism at table level (ct2 elements → ct1 elements)
//   phi_inv: A→B isomorphism at table level (ct1 elements → ct2 elements)
//
// State: (h: nat, sylls: Seq<(bool, nat)>)
//   h: ct1-element in A (always stored in G₁'s Cayley table)
//   sylls: alternating (is_left, st-coset-number) pairs, each coset > 0
//
// Action of G₁-symbol s on (h, sylls):
//   new_elem = ct1.table[h][s_col]  (s · h in G₁)
//   If sylls starts with Left(c₁): combine new_elem with c₁ in G₁
//   Else: decompose new_elem in G₁/A
//
// Action of G₂-symbol s on (h, sylls):
//   h_g2 = phi_inv(h)  (translate h to G₂)
//   new_elem = ct2.table[h_g2][s_col]  (s · h_g2 in G₂)
//   If sylls starts with Right(c₁): combine new_elem with c₁ in G₂
//   Else: decompose new_elem in G₂/B, translate B-part back via phi

/// symbol_to_column: Gen(i) → 2*i, Inv(i) → 2*i+1.
/// Re-export for convenience.
pub open spec fn sym_col(s: Symbol) -> nat {
    crate::todd_coxeter::symbol_to_column(s)
}

/// Unshift a G₂ symbol: Gen(n1+j) → Gen(j), Inv(n1+j) → Inv(j).
pub open spec fn unshift_sym(s: Symbol, n1: nat) -> Symbol {
    match s {
        Symbol::Gen(i) => Symbol::Gen((i - n1) as nat),
        Symbol::Inv(i) => Symbol::Inv((i - n1) as nat),
    }
}

/// Lookup in a Cayley table: ct.table[elem][col], defaulting to 0.
pub open spec fn ct_lookup(
    ct: crate::todd_coxeter::CosetTable, elem: nat, col: nat,
) -> nat {
    match ct.table[elem as int][col as int] {
        Some(next) => next,
        None => 0,
    }
}

/// Coset decomposition in G/H using a Cayley table + subgroup coset table.
/// Returns (h_part, coset) where h_part is the H-component (ct-element in H)
/// and coset is the st-coset number (0 if in H, >0 otherwise).
///
/// The element = h_part * coset_rep(coset) in the group.
/// h_part = element * inv(coset_rep(coset)).
pub open spec fn coset_decomp(
    ct: crate::todd_coxeter::CosetTable,
    st: crate::todd_coxeter::CosetTable,
    elem: nat,
) -> (nat, nat) {
    // Get the subgroup coset of elem
    let rep_word = crate::coset_group::coset_rep(ct, elem);
    let coset = match crate::todd_coxeter::trace_word(st, 0, rep_word) {
        Some(c) => c,
        None => 0,
    };
    if coset == 0 {
        // elem ∈ H. h_part = elem.
        (elem, 0)
    } else {
        // elem ∉ H. h_part = elem * inv(coset_rep_elem).
        let coset_rep_word = crate::coset_group::coset_rep(st, coset);
        let coset_rep_elem = match crate::todd_coxeter::trace_word(ct, 0, coset_rep_word) {
            Some(e) => e,
            None => 0,
        };
        let coset_rep_inv = crate::coset_group::coset_inv(ct, coset_rep_elem);
        (crate::coset_group::coset_mul(ct, elem, coset_rep_inv), coset)
    }
}

/// VDW action of a G₁-symbol on state (h, sylls).
/// h is a ct1-element in A. s has generator_index < n1.
pub open spec fn vdw_g1(
    ct1: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    s: Symbol,
    h: nat,
    sylls: Seq<(bool, nat)>,
) -> (nat, Seq<(bool, nat)>) {
    let new_elem = ct_lookup(ct1, h, sym_col(s));
    if sylls.len() > 0 && sylls[0].0 == true {
        // First syllable is Left. Combine new_elem with c₁ in G₁.
        let c1_rep = crate::coset_group::coset_rep(st1, sylls[0].1);
        let c1_elem = match crate::todd_coxeter::trace_word(ct1, 0, c1_rep) {
            Some(e) => e, None => 0,
        };
        let combined = crate::coset_group::coset_mul(ct1, new_elem, c1_elem);
        let (h_new, c_new) = coset_decomp(ct1, st1, combined);
        if c_new == 0 {
            (h_new, sylls.drop_first())
        } else {
            (h_new, Seq::new(1, |_i: int| (true, c_new)) + sylls.drop_first())
        }
    } else {
        // First syllable is Right or empty. Decompose new_elem in G₁/A.
        let (h_new, c_new) = coset_decomp(ct1, st1, new_elem);
        if c_new == 0 {
            (h_new, sylls)
        } else {
            (h_new, Seq::new(1, |_i: int| (true, c_new)) + sylls)
        }
    }
}

/// VDW action of a G₂-symbol on state (h, sylls).
/// h is a ct1-element in A. s has generator_index >= n1.
/// phi_inv translates A-elements (ct1) to B-elements (ct2).
/// phi translates B-elements (ct2) back to A-elements (ct1).
pub open spec fn vdw_g2(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    s: Symbol,
    h: nat,
    sylls: Seq<(bool, nat)>,
) -> (nat, Seq<(bool, nat)>) {
    // Translate h to G₂
    let h_g2 = phi_inv(h);
    let s_local = unshift_sym(s, n1);
    let new_elem = ct_lookup(ct2, h_g2, sym_col(s_local));
    if sylls.len() > 0 && sylls[0].0 == false {
        // First syllable is Right. Combine new_elem with c₁ in G₂.
        let c1_rep = crate::coset_group::coset_rep(st2, sylls[0].1);
        let c1_elem = match crate::todd_coxeter::trace_word(ct2, 0, c1_rep) {
            Some(e) => e, None => 0,
        };
        let combined = crate::coset_group::coset_mul(ct2, new_elem, c1_elem);
        let (b_part, c_new) = coset_decomp(ct2, st2, combined);
        let h_new = phi(b_part);
        if c_new == 0 {
            (h_new, sylls.drop_first())
        } else {
            (h_new, Seq::new(1, |_i: int| (false, c_new)) + sylls.drop_first())
        }
    } else {
        // First syllable is Left or empty. Decompose new_elem in G₂/B.
        let (b_part, c_new) = coset_decomp(ct2, st2, new_elem);
        let h_new = phi(b_part);
        if c_new == 0 {
            (h_new, sylls)
        } else {
            (h_new, Seq::new(1, |_i: int| (false, c_new)) + sylls)
        }
    }
}

/// VDW action of a single AFP symbol.
pub open spec fn vdw_sym(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    s: Symbol,
    h: nat,
    sylls: Seq<(bool, nat)>,
) -> (nat, Seq<(bool, nat)>) {
    if generator_index(s) < n1 {
        vdw_g1(ct1, st1, s, h, sylls)
    } else {
        vdw_g2(ct1, ct2, st2, phi, phi_inv, n1, s, h, sylls)
    }
}

/// VDW action of a full word (process symbols left to right).
pub open spec fn vdw_word(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    w: Word,
    h: nat,
    sylls: Seq<(bool, nat)>,
) -> (nat, Seq<(bool, nat)>)
    decreases w.len(),
{
    if w.len() == 0 {
        (h, sylls)
    } else {
        let (h2, s2) = vdw_sym(ct1, ct2, st1, st2, phi, phi_inv, n1, w.first(), h, sylls);
        vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1, w.drop_first(), h2, s2)
    }
}

/// Composition lemma: vdw_word(w1++w2) = vdw_word(w2, vdw_word(w1)).
proof fn lemma_vdw_concat(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    w1: Word, w2: Word,
    h: nat, sylls: Seq<(bool, nat)>,
)
    ensures ({
        let (hm, sm) = vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1, w1, h, sylls);
        vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1, concat(w1, w2), h, sylls)
            == vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1, w2, hm, sm)
    }),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
    } else {
        assert(concat(w1, w2).first() == w1.first());
        assert(concat(w1, w2).drop_first() =~= concat(w1.drop_first(), w2));
        let (h2, s2) = vdw_sym(ct1, ct2, st1, st2, phi, phi_inv, n1, w1.first(), h, sylls);
        lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, w1.drop_first(), w2, h2, s2);
    }
}

// ============================================================
// Part H: Prerequisites bundle
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

/// Subgroup coset table validity (no Schreier system required).
pub open spec fn valid_sub_table(t: crate::todd_coxeter::CosetTable, p: Presentation) -> bool {
    &&& crate::todd_coxeter::coset_table_wf(t)
    &&& crate::todd_coxeter::coset_table_consistent(t)
    &&& crate::finite::coset_table_complete(t)
    &&& crate::todd_coxeter::relator_closed(t, p)
    &&& t.num_gens == p.num_generators
    &&& presentation_valid(p)
    &&& t.num_cosets > 0
}

/// phi is a valid B→A isomorphism at the Cayley table level.
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
    // phi and phi_inv are inverses
    &&& (forall|b: nat| b < ct2.num_cosets ==> #[trigger] phi_inv(phi(b)) == b)
    &&& (forall|a: nat| a < ct1.num_cosets ==> #[trigger] phi(phi_inv(a)) == a)
    // phi respects identification generators
    &&& (forall|i: int| #![trigger data.identifications[i]]
        0 <= i < data.identifications.len() ==> ({
        let u_elem = crate::todd_coxeter::trace_word(ct1, 0, data.identifications[i].0);
        let v_elem = crate::todd_coxeter::trace_word(ct2, 0, data.identifications[i].1);
        u_elem is Some && v_elem is Some && phi(v_elem.unwrap()) == u_elem.unwrap()
    }))
    // phi is a homomorphism
    &&& (forall|x: nat, y: nat|
        x < ct2.num_cosets && y < ct2.num_cosets ==>
        phi(crate::coset_group::coset_mul(ct2, x, y))
            == crate::coset_group::coset_mul(ct1, phi(x), phi(y)))
    // phi respects inverses
    &&& (forall|x: nat|
        x < ct2.num_cosets ==>
        phi(crate::coset_group::coset_inv(ct2, x))
            == crate::coset_group::coset_inv(ct1, phi(x)))
}

/// All VDW prerequisites bundled.
pub open spec fn vdw_prereqs(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
) -> bool {
    &&& amalgamated_data_valid(data)
    &&& identifications_isomorphic(data)
    &&& valid_cayley(ct1, data.p1)
    &&& valid_cayley(ct2, data.p2)
    &&& valid_sub_table(st1, data.p1)
    &&& valid_sub_table(st2, data.p2)
    &&& ct1.num_gens == st1.num_gens
    &&& ct2.num_gens == st2.num_gens
    &&& valid_phi(phi, phi_inv, ct1, ct2, data)
    // Subgroup generators trace to coset 0 in subgroup tables
    &&& (forall|i: int| 0 <= i < data.identifications.len() ==>
        crate::todd_coxeter::trace_word(st1, 0, data.identifications[i].0) == Some(0nat))
    &&& (forall|i: int| 0 <= i < data.identifications.len() ==>
        crate::todd_coxeter::trace_word(st2, 0, data.identifications[i].1) == Some(0nat))
}

// ============================================================
// Part I: AFP injectivity theorem
// ============================================================

/// AFP injectivity for finite groups.
///
/// If w is a G₁-word and w ≡ ε in the AFP, then w ≡ ε in G₁.
///
/// Proof: the VDW action is well-defined on AFP equivalence classes
/// (each relator acts trivially). Therefore w ≡ ε implies
/// vdw_word(w) == vdw_word(ε) == (0, []). For a G₁-word, this means
/// the Cayley table element is 0, so w ≡ ε in G₁.
pub proof fn lemma_afp_injectivity(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    w: Word,
)
    requires
        vdw_prereqs(ct1, ct2, st1, st2, phi, phi_inv, data),
        word_valid(w, data.p1.num_generators),
        equiv_in_presentation(amalgamated_free_product(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.p1, w, empty_word()),
{
    let n1 = data.p1.num_generators;
    let afp = amalgamated_free_product(data);
    let d = choose|d: Derivation| derivation_valid(afp, d, w, empty_word());

    // Step 1: VDW action is well-defined — AFP derivation preserves the action
    lemma_vdw_deriv(ct1, ct2, st1, st2, phi, phi_inv, data, d.steps,
        w, empty_word(), 0, Seq::empty());
    // Now: vdw_word(w, 0, []) == vdw_word(ε, 0, []) == (0, [])

    // Step 2: (0, []) means trivial in G₁
    // vdw_word(ε, 0, []) == (0, []) trivially
    assert(vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1,
        empty_word(), 0, Seq::empty()) == (0nat, Seq::<(bool, nat)>::empty()));

    // Step 3: vdw_word(w, 0, []) == (0, [])
    // → Cayley element of w is 0 → w ≡ ε in G₁
    lemma_vdw_faithful(ct1, ct2, st1, st2, phi, phi_inv, data, w);
}

/// VDW action respects AFP derivation.
proof fn lemma_vdw_deriv(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
    h: nat, sylls: Seq<(bool, nat)>,
)
    requires
        vdw_prereqs(ct1, ct2, st1, st2, phi, phi_inv, data),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
    ensures
        vdw_word(ct1, ct2, st1, st2, phi, phi_inv, data.p1.num_generators, w1, h, sylls)
            == vdw_word(ct1, ct2, st1, st2, phi, phi_inv, data.p1.num_generators, w2, h, sylls),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(w1 == w2);
    } else {
        let afp = amalgamated_free_product(data);
        let step = steps.first();
        let w_mid = apply_step(afp, w1, step).unwrap();
        lemma_vdw_step(ct1, ct2, st1, st2, phi, phi_inv, data, w1, step, w_mid, h, sylls);
        lemma_vdw_deriv(ct1, ct2, st1, st2, phi, phi_inv, data, steps.drop_first(),
            w_mid, w2, h, sylls);
    }
}

/// VDW action respects a single derivation step.
/// This is the core well-definedness check: each AFP relator acts trivially.
proof fn lemma_vdw_step(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    w: Word, step: DerivationStep, w_prime: Word,
    h: nat, sylls: Seq<(bool, nat)>,
)
    requires
        vdw_prereqs(ct1, ct2, st1, st2, phi, phi_inv, data),
        apply_step(amalgamated_free_product(data), w, step) == Some(w_prime),
    ensures
        vdw_word(ct1, ct2, st1, st2, phi, phi_inv, data.p1.num_generators, w, h, sylls)
            == vdw_word(ct1, ct2, st1, st2, phi, phi_inv, data.p1.num_generators, w_prime, h, sylls),
{
    let n1 = data.p1.num_generators;
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
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, pair + suffix, h, sylls);
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, suffix, h, sylls);
            let (hm, sm) = vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, h, sylls);
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, pair, suffix, hm, sm);
            lemma_vdw_inv_pair(ct1, ct2, st1, st2, phi, phi_inv, n1,
                w[position], w[position + 1], hm, sm);
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
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, suffix, h, sylls);
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, pair + suffix, h, sylls);
            let (hm, sm) = vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, h, sylls);
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, pair, suffix, hm, sm);
            lemma_vdw_inv_pair(ct1, ct2, st1, st2, phi, phi_inv, n1,
                symbol, inverse_symbol(symbol), hm, sm);
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
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, suffix, h, sylls);
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, r + suffix, h, sylls);
            let (hm, sm) = vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, h, sylls);
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, r, suffix, hm, sm);
            lemma_vdw_relator(ct1, ct2, st1, st2, phi, phi_inv, data,
                relator_index, inverted, hm, sm);
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
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, r + suffix, h, sylls);
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, suffix, h, sylls);
            let (hm, sm) = vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1, prefix, h, sylls);
            lemma_vdw_concat(ct1, ct2, st1, st2, phi, phi_inv, n1, r, suffix, hm, sm);
            lemma_vdw_relator(ct1, ct2, st1, st2, phi, phi_inv, data,
                relator_index, inverted, hm, sm);
        },
    }
}

/// Inverse pair acts trivially.
proof fn lemma_vdw_inv_pair(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    n1: nat,
    s1: Symbol, s2: Symbol,
    h: nat, sylls: Seq<(bool, nat)>,
)
    requires is_inverse_pair(s1, s2),
    ensures ({
        let pair = Seq::new(1, |_i: int| s1) + Seq::new(1, |_i: int| s2);
        vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1, pair, h, sylls) == (h, sylls)
    }),
{
    // TODO: case analysis on G₁ vs G₂ symbol, use table consistency
    assert(false);
}

/// AFP relator acts trivially.
proof fn lemma_vdw_relator(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    relator_index: nat, inverted: bool,
    h: nat, sylls: Seq<(bool, nat)>,
)
    requires
        vdw_prereqs(ct1, ct2, st1, st2, phi, phi_inv, data),
        relator_index < amalgamated_free_product(data).relators.len(),
    ensures ({
        let r = get_relator(amalgamated_free_product(data), relator_index, inverted);
        let n1 = data.p1.num_generators;
        vdw_word(ct1, ct2, st1, st2, phi, phi_inv, n1, r, h, sylls) == (h, sylls)
    }),
{
    // TODO: classify relator (G₁/G₂/identification), prove each acts trivially
    assert(false);
}

/// Faithfulness: vdw_word(w, 0, []) == (0, []) implies w ≡ ε in G₁.
proof fn lemma_vdw_faithful(
    ct1: crate::todd_coxeter::CosetTable,
    ct2: crate::todd_coxeter::CosetTable,
    st1: crate::todd_coxeter::CosetTable,
    st2: crate::todd_coxeter::CosetTable,
    phi: spec_fn(nat) -> nat,
    phi_inv: spec_fn(nat) -> nat,
    data: AmalgamatedData,
    w: Word,
)
    requires
        vdw_prereqs(ct1, ct2, st1, st2, phi, phi_inv, data),
        word_valid(w, data.p1.num_generators),
        vdw_word(ct1, ct2, st1, st2, phi, phi_inv, data.p1.num_generators,
            w, 0, Seq::empty()) == (0nat, Seq::<(bool, nat)>::empty()),
    ensures
        equiv_in_presentation(data.p1, w, empty_word()),
{
    // TODO: prove trace_word(ct1, 0, w) == Some(0) from the action result,
    // then use axiom_coset_table_sound
    assert(false);
}

} // verus!
