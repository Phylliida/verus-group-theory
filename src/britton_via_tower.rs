// Britton's Lemma via Tower Construction
//
// Translates HNN extension derivations to tower derivations.
// Faithful to Lyndon-Schupp Chapter IV: the tower unfolds the HNN extension
// by replacing the stable letter with explicit copies of the base group.
//
// Key insight: the HNN relator t⁻¹·a_i·t·inv(b_i) at level k corresponds
// exactly to the AFP identification relator shift(a_i, (k-1)·ng)·inv(shift(b_i, k·ng))
// at tower junction (k-1)↔k.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::hnn::*;
use crate::tower::*;

verus! {

// ============================================================
// Part A: Level tracking and word translation
// ============================================================

/// Whether symbol s is the stable letter t or t⁻¹.
pub open spec fn is_stable(data: HNNData, s: Symbol) -> bool {
    let ng = data.base.num_generators;
    s == Symbol::Gen(ng) || s == Symbol::Inv(ng)
}

/// Net level change of a word: count of t minus count of t⁻¹.
pub open spec fn net_level(data: HNNData, w: Word) -> int
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
        0
    } else {
        let s = w.first();
        let rest_level = net_level(data, w.drop_first());
        if s == Symbol::Gen(ng) {
            1 + rest_level
        } else if s == Symbol::Inv(ng) {
            -1 + rest_level
        } else {
            rest_level
        }
    }
}

/// Translate an HNN word to a tower word, starting at a given base level.
/// - Stable letters are REMOVED (encode level changes)
/// - Base symbol at current level k becomes shifted by k·ng
/// - base_level tracks the accumulated level from earlier context
pub open spec fn translate_word_at(data: HNNData, w: Word, base_level: int) -> Word
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
        empty_word()
    } else {
        let s = w.first();
        let rest = w.drop_first();
        if s == Symbol::Gen(ng) {
            // t: level +1, skip symbol
            translate_word_at(data, rest, base_level + 1)
        } else if s == Symbol::Inv(ng) {
            // t⁻¹: level -1, skip symbol
            translate_word_at(data, rest, base_level - 1)
        } else {
            // Base symbol: shift by base_level · ng, include in output
            let shifted_s = match s {
                Symbol::Gen(i) => Symbol::Gen((i + base_level * ng) as nat),
                Symbol::Inv(i) => Symbol::Inv((i + base_level * ng) as nat),
            };
            concat(Seq::new(1, |_j: int| shifted_s),
                translate_word_at(data, rest, base_level))
        }
    }
}

/// Top-level translation: start at level 0.
pub open spec fn translate_word(data: HNNData, w: Word) -> Word {
    translate_word_at(data, w, 0)
}

// ============================================================
// Part B: Base word translation = identity
// ============================================================

/// A base word has net level 0.
proof fn lemma_base_word_net_level_zero(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        net_level(data, w) == 0,
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
        lemma_base_word_net_level_zero(data, w.drop_first());
    }
}

/// A base word translates to itself at level 0.
pub proof fn lemma_translate_base_word(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        translate_word(data, w) =~= w,
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); assert(!is_stable(data, s)); }
            Symbol::Inv(i) => { assert(i < ng); assert(!is_stable(data, s)); }
        }
        assert(word_valid(w.drop_first(), ng));
        lemma_translate_base_word(data, w.drop_first());
    }
}

/// The empty word translates to the empty word.
pub proof fn lemma_translate_empty(data: HNNData)
    ensures translate_word(data, empty_word()) =~= empty_word(),
{
}

// ============================================================
// Part C: Concat decomposition for translate_word_at
// ============================================================

/// translate_word_at distributes over concat (with level offset).
pub proof fn lemma_translate_concat(data: HNNData, w1: Word, w2: Word, base_level: int)
    ensures
        translate_word_at(data, concat(w1, w2), base_level)
            =~= concat(translate_word_at(data, w1, base_level),
                        translate_word_at(data, w2, base_level + net_level(data, w1))),
    decreases w1.len(),
{
    let ng = data.base.num_generators;
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(net_level(data, w1) == 0);
        assert(translate_word_at(data, w1, base_level) =~= empty_word());
    } else {
        let s = w1.first();
        let rest1 = w1.drop_first();
        assert(concat(w1, w2).first() == s);
        assert(concat(w1, w2).drop_first() =~= concat(rest1, w2));

        if s == Symbol::Gen(ng) {
            lemma_translate_concat(data, rest1, w2, base_level + 1);
        } else if s == Symbol::Inv(ng) {
            lemma_translate_concat(data, rest1, w2, base_level - 1);
        } else {
            lemma_translate_concat(data, rest1, w2, base_level);
        }
    }
}

// ============================================================
// Part D: Derivation lifting — equiv in p1 → equiv in free_product(p1, p2)
// ============================================================

/// A single derivation step valid in p1 is also valid in free_product(p1, p2).
proof fn lemma_step_valid_in_fp_left(
    p1: Presentation, p2: Presentation,
    w: Word, step: DerivationStep,
)
    requires
        apply_step(p1, w, step) is Some,
    ensures
        apply_step(free_product(p1, p2), w, step) == apply_step(p1, w, step),
{
    let fp = free_product(p1, p2);
    match step {
        DerivationStep::FreeReduce { position } => {},
        DerivationStep::FreeExpand { position, symbol } => {
            assert(symbol_valid(symbol, fp.num_generators)) by {
                match symbol {
                    Symbol::Gen(i) => {}
                    Symbol::Inv(i) => {}
                }
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
        },
    }
}

/// A full derivation valid in p1 is also valid in free_product(p1, p2).
proof fn lemma_derivation_valid_in_fp_left(
    p1: Presentation, p2: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(p1, steps, w1) == Some(w2),
    ensures
        derivation_produces(free_product(p1, p2), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let w_mid = apply_step(p1, w1, steps.first()).unwrap();
        lemma_step_valid_in_fp_left(p1, p2, w1, steps.first());
        lemma_derivation_valid_in_fp_left(p1, p2, steps.drop_first(), w_mid, w2);
    }
}

/// Equivalence in p1 implies equivalence in free_product(p1, p2).
pub proof fn lemma_left_embeds_in_fp(
    p1: Presentation, p2: Presentation, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(p1, w1, w2),
    ensures
        equiv_in_presentation(free_product(p1, p2), w1, w2),
{
    let d: Derivation = choose|d: Derivation| derivation_valid(p1, d, w1, w2);
    lemma_derivation_valid_in_fp_left(p1, p2, d.steps, w1, w2);
    let d_fp = Derivation { steps: d.steps };
    assert(derivation_valid(free_product(p1, p2), d_fp, w1, w2));
}

/// Equivalence in tower(k) implies equivalence in tower(m) for k ≤ m.
pub proof fn lemma_tower_monotone(
    data: HNNData, k: nat, m: nat, w1: Word, w2: Word,
)
    requires
        hnn_data_valid(data),
        k <= m,
        equiv_in_presentation(tower_presentation(data, k), w1, w2),
    ensures
        equiv_in_presentation(tower_presentation(data, m), w1, w2),
    decreases m - k,
{
    if k == m {
    } else {
        let afp_data = tower_afp_data(data, k);
        lemma_left_embeds_in_fp(afp_data.p1, afp_data.p2, w1, w2);
        crate::quotient::lemma_add_relators_preserves_equiv(
            free_product(afp_data.p1, afp_data.p2),
            amalgamation_relators(afp_data), w1, w2);
        lemma_tower_monotone(data, k + 1, m, w1, w2);
    }
}

// ============================================================
// Part E: Tower relator correspondence
// ============================================================

/// A base relator at copy k is equiv to ε in tower(m) when k ≤ m.
pub proof fn lemma_base_relator_in_tower(
    data: HNNData, m: nat, k: nat, r: int,
)
    requires
        hnn_data_valid(data),
        k <= m,
        0 <= r < data.base.relators.len(),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            shift_word(data.base.relators[r], k * data.base.num_generators),
            empty_word()),
    decreases m,
{
    let ng = data.base.num_generators;
    if k == 0 && m == 0 {
        assert(shift_word(data.base.relators[r], 0) =~= data.base.relators[r]);
        lemma_relator_is_identity(data.base, r);
    } else if k < m {
        if k == 0 {
            assert(shift_word(data.base.relators[r], 0) =~= data.base.relators[r]);
            lemma_relator_is_identity(data.base, r);
            lemma_tower_monotone(data, 0, m, data.base.relators[r], empty_word());
        } else {
            lemma_base_relator_in_tower(data, (m - 1) as nat, k, r);
            lemma_tower_monotone(data, (m - 1) as nat, m,
                shift_word(data.base.relators[r], k * ng), empty_word());
        }
    } else {
        // k == m > 0: relator in the new copy (right factor)
        let prev = (m - 1) as nat;
        let afp_data = tower_afp_data(data, prev);
        let fp = free_product(afp_data.p1, afp_data.p2);
        lemma_tower_num_generators(data, prev);
        let fp_idx = (afp_data.p1.relators.len() + r) as nat;
        assert(fp.relators[fp_idx as int]
            == shift_word(data.base.relators[r], m * ng));
        lemma_relator_is_identity(fp, fp_idx as int);
        crate::quotient::lemma_add_relators_preserves_equiv(
            fp, amalgamation_relators(afp_data),
            shift_word(data.base.relators[r], m * ng), empty_word());
    }
}

/// An identification relator at junction k↔k+1 is equiv to ε in tower(m) when k+1 ≤ m.
pub proof fn lemma_ident_relator_in_tower(
    data: HNNData, m: nat, k: nat, i: int,
)
    requires
        hnn_data_valid(data),
        k + 1 <= m,
        0 <= i < data.associations.len() as int,
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            amalgamation_relator(tower_afp_data(data, k), i),
            empty_word()),
    decreases m,
{
    let prev = (m - 1) as nat;
    let afp_data = tower_afp_data(data, prev);
    let fp = free_product(afp_data.p1, afp_data.p2);

    if k == prev {
        crate::quotient::lemma_each_added_relator_is_identity(
            fp, amalgamation_relators(afp_data), i);
    } else {
        lemma_ident_relator_in_tower(data, prev, k, i);
        lemma_tower_monotone(data, prev, m,
            amalgamation_relator(tower_afp_data(data, k), i), empty_word());
    }
}

// ============================================================
// Part F: Context insertion — if r ≡ ε, then prefix·suffix ≡ prefix·r·suffix
// ============================================================

/// If r ≡ ε, then prefix·r·suffix ≡ prefix·suffix (deletion direction).
pub proof fn lemma_delete_equiv_empty(
    p: Presentation, prefix: Word, r: Word, suffix: Word,
)
    requires
        equiv_in_presentation(p, r, empty_word()),
    ensures
        equiv_in_presentation(p, concat(prefix, concat(r, suffix)),
            concat(prefix, suffix)),
{
    // r ≡ ε → concat(r, suffix) ≡ concat(ε, suffix) =~= suffix
    lemma_equiv_concat_left(p, r, empty_word(), suffix);
    // concat(prefix, concat(r, suffix)) ≡ concat(prefix, suffix)
    lemma_equiv_concat_right(p, prefix, concat(r, suffix), suffix);
}

/// If r ≡ ε, then prefix·suffix ≡ prefix·r·suffix (insertion direction).
/// Requires symmetry infrastructure (word_valid + presentation_valid).
pub proof fn lemma_insert_equiv_empty(
    p: Presentation, prefix: Word, r: Word, suffix: Word,
)
    requires
        equiv_in_presentation(p, r, empty_word()),
        presentation_valid(p),
        word_valid(r, p.num_generators),
    ensures
        equiv_in_presentation(p, concat(prefix, suffix),
            concat(prefix, concat(r, suffix))),
{
    // ε ≡ r (by symmetry)
    crate::presentation::lemma_equiv_symmetric(p, r, empty_word());
    // concat(ε, suffix) ≡ concat(r, suffix) → suffix ≡ concat(r, suffix)
    lemma_equiv_concat_left(p, empty_word(), r, suffix);
    // concat(prefix, suffix) ≡ concat(prefix, concat(r, suffix))
    lemma_equiv_concat_right(p, prefix, suffix, concat(r, suffix));
}

// ============================================================
// Part G: Translation of base words at arbitrary level
// ============================================================

/// A base word at level L translates to shift_word(w, L * ng).
pub proof fn lemma_translate_base_word_at(data: HNNData, w: Word, base_level: nat)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        translate_word_at(data, w, base_level as int)
            =~= shift_word(w, base_level * data.base.num_generators),
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
        lemma_translate_base_word_at(data, w.drop_first(), base_level);
    }
}

/// A single stable letter translates to empty at any level.
proof fn lemma_translate_stable_empty(data: HNNData, s: Symbol, base_level: int)
    requires is_stable(data, s),
    ensures
        translate_word_at(data, Seq::new(1, |_j: int| s), base_level) =~= empty_word(),
{
    let w = Seq::new(1, |_j: int| s);
    assert(w.first() == s);
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    reveal_with_fuel(translate_word_at, 2);
}

/// Net level of a base word is 0.
proof fn lemma_net_level_base_word(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        net_level(data, w) == 0,
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
        lemma_net_level_base_word(data, w.drop_first());
    }
}

/// Net level of a single stable letter.
proof fn lemma_net_level_stable(data: HNNData, s: Symbol)
    requires is_stable(data, s),
    ensures
        net_level(data, Seq::new(1, |_j: int| s)) ==
            (if s == Symbol::Gen(data.base.num_generators) { 1int } else { -1int }),
{
    let w = Seq::new(1, |_j: int| s);
    assert(w.first() == s);
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    reveal_with_fuel(net_level, 2);
}

/// Net level distributes over concat.
pub proof fn lemma_net_level_concat(data: HNNData, w1: Word, w2: Word)
    ensures
        net_level(data, concat(w1, w2)) == net_level(data, w1) + net_level(data, w2),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
    } else {
        assert(concat(w1, w2).first() == w1.first());
        assert(concat(w1, w2).drop_first() =~= concat(w1.drop_first(), w2));
        lemma_net_level_concat(data, w1.drop_first(), w2);
    }
}

// ============================================================
// Part H: HNN relator translates to identification relator
// ============================================================

/// The HNN relator t⁻¹·a_i·t·inv(b_i) at level k translates to
/// the AFP identification relator at junction (k-1)↔k.
///
/// This is the textbook correspondence (Lyndon-Schupp Ch. IV):
/// each HNN relation at level k becomes an identification relation
/// between copy k-1 and copy k in the tower.
pub proof fn lemma_translate_hnn_relator(
    data: HNNData, i: int, k: int,
)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
        k >= 1,
    ensures ({
        let ng = data.base.num_generators;
        let r = hnn_relator(data, i);
        let afp_data = tower_afp_data(data, (k - 1) as nat);
        translate_word_at(data, r, k)
            =~= amalgamation_relator(afp_data, i)
    }),
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    let t_inv = Seq::new(1, |_j: int| Symbol::Inv(ng));
    let t_gen = Seq::new(1, |_j: int| Symbol::Gen(ng));

    // r = concat(part1, part2) where part1 = concat(t_inv, a_i), part2 = concat(t_gen, inv(b_i))
    let part1 = concat(t_inv, a_i);
    let part2 = concat(t_gen, inverse_word(b_i));

    // Step 1: decompose r = concat(part1, part2)
    lemma_translate_concat(data, part1, part2, k);

    // Step 2: net_level(part1) = -1 (t⁻¹ contributes -1, a_i contributes 0)
    lemma_net_level_concat(data, t_inv, a_i);
    lemma_net_level_stable(data, Symbol::Inv(ng));
    lemma_net_level_base_word(data, a_i);
    assert(net_level(data, part1) == -1);

    // Step 3: translate(part1, k) =~= shift(a_i, (k-1)*ng)
    lemma_translate_concat(data, t_inv, a_i, k);
    lemma_net_level_stable(data, Symbol::Inv(ng));
    lemma_translate_stable_empty(data, Symbol::Inv(ng), k);
    lemma_translate_base_word_at(data, a_i, (k - 1) as nat);

    // Step 4: translate(part2, k-1) =~= shift(inv(b_i), k*ng)
    lemma_translate_concat(data, t_gen, inverse_word(b_i), k - 1);
    lemma_net_level_stable(data, Symbol::Gen(ng));
    lemma_translate_stable_empty(data, Symbol::Gen(ng), k - 1);
    crate::word::lemma_inverse_word_valid(b_i, ng);
    lemma_translate_base_word_at(data, inverse_word(b_i), k as nat);

    // Intermediate assertions to chain the =~= results
    assert(translate_word_at(data, part1, k)
        =~= shift_word(a_i, ((k - 1) as nat) * ng));
    assert(translate_word_at(data, part2, k - 1)
        =~= shift_word(inverse_word(b_i), k as nat * ng));

    // Step 5: shift(inv(b_i), k*ng) =~= inv(shift(b_i, k*ng))
    crate::free_product::lemma_shift_inverse_word(b_i, k as nat * ng);

    // Step 6: connect to amalgamation_relator
    lemma_tower_num_generators(data, (k - 1) as nat);
    assert(translate_word_at(data, part2, k - 1)
        =~= inverse_word(shift_word(b_i, k as nat * ng)));

    // Connect hnn_relator to concat(part1, part2)
    assert(hnn_relator(data, i) =~= concat(part1, part2));

    // Final chain
    assert(translate_word_at(data, concat(part1, part2), k)
        =~= concat(shift_word(a_i, ((k - 1) as nat) * ng),
                    inverse_word(shift_word(b_i, k as nat * ng))));
}

// ============================================================
// Part I: General middle-deletion lemma for translation
// ============================================================

/// If the translated middle ≡ ε in tower and net_level(middle) == 0,
/// then translate(prefix · middle · suffix) ≡ translate(prefix · suffix) in tower.
///
/// This handles ALL step types uniformly:
/// - FreeReduce/Delete: w = prefix · middle · suffix → w' = prefix · suffix
/// - FreeExpand/Insert: w = prefix · suffix → w' = prefix · middle · suffix (reverse direction)
pub proof fn lemma_translate_delete_middle(
    data: HNNData, m: nat,
    prefix: Word, middle: Word, suffix: Word,
)
    requires
        hnn_data_valid(data),
        net_level(data, middle) == 0,
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, middle, net_level(data, prefix)),
            empty_word()),
        presentation_valid(tower_presentation(data, m)),
        word_valid(translate_word_at(data, middle, net_level(data, prefix)),
            tower_presentation(data, m).num_generators),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word(data, concat(prefix, concat(middle, suffix))),
            translate_word(data, concat(prefix, suffix))),
{
    let tp = tower_presentation(data, m);
    let lp = net_level(data, prefix);

    // Decompose translate of w = prefix · middle · suffix
    lemma_translate_concat(data, prefix, concat(middle, suffix), 0);
    lemma_translate_concat(data, middle, suffix, lp);
    lemma_net_level_concat(data, prefix, concat(middle, suffix));
    lemma_net_level_concat(data, middle, suffix);
    // translate(w) =~= concat(tr(prefix, 0), concat(tr(middle, lp), tr(suffix, lp)))
    // (since net_level(middle) == 0: suffix starts at level lp + 0 = lp)

    // Decompose translate of w' = prefix · suffix
    lemma_translate_concat(data, prefix, suffix, 0);
    // translate(w') =~= concat(tr(prefix, 0), tr(suffix, lp))

    // tr(middle, lp) ≡ ε → delete the middle from the translation
    let tr_prefix = translate_word_at(data, prefix, 0);
    let tr_middle = translate_word_at(data, middle, lp);
    let tr_suffix = translate_word_at(data, suffix, lp);

    lemma_delete_equiv_empty(tp, tr_prefix, tr_middle, tr_suffix);
}

/// Reverse direction: translate(prefix · suffix) ≡ translate(prefix · middle · suffix).
/// Needs symmetry infrastructure.
pub proof fn lemma_translate_insert_middle(
    data: HNNData, m: nat,
    prefix: Word, middle: Word, suffix: Word,
)
    requires
        hnn_data_valid(data),
        net_level(data, middle) == 0,
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, middle, net_level(data, prefix)),
            empty_word()),
        presentation_valid(tower_presentation(data, m)),
        word_valid(translate_word_at(data, middle, net_level(data, prefix)),
            tower_presentation(data, m).num_generators),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word(data, concat(prefix, suffix)),
            translate_word(data, concat(prefix, concat(middle, suffix)))),
{
    let tp = tower_presentation(data, m);
    let lp = net_level(data, prefix);

    lemma_translate_concat(data, prefix, concat(middle, suffix), 0);
    lemma_translate_concat(data, middle, suffix, lp);
    lemma_net_level_concat(data, prefix, concat(middle, suffix));
    lemma_net_level_concat(data, middle, suffix);
    lemma_translate_concat(data, prefix, suffix, 0);

    let tr_prefix = translate_word_at(data, prefix, 0);
    let tr_middle = translate_word_at(data, middle, lp);
    let tr_suffix = translate_word_at(data, suffix, lp);

    lemma_insert_equiv_empty(tp, tr_prefix, tr_middle, tr_suffix);
}

// ============================================================
// Part J: Specific middle ≡ ε results
// ============================================================

/// A stable inverse pair translates to ε (=~=, not just ≡).
proof fn lemma_translate_stable_pair(data: HNNData, s: Symbol, base_level: int)
    requires
        is_stable(data, s),
    ensures
        translate_word_at(data,
            concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| inverse_symbol(s))),
            base_level)
            =~= empty_word(),
        net_level(data,
            concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| inverse_symbol(s))))
            == 0,
{
    let s_word = Seq::new(1, |_j: int| s);
    let inv_s_word = Seq::new(1, |_j: int| inverse_symbol(s));
    let pair = concat(s_word, inv_s_word);

    lemma_translate_concat(data, s_word, inv_s_word, base_level);
    lemma_net_level_concat(data, s_word, inv_s_word);
    lemma_net_level_stable(data, s);

    // inverse_symbol of stable is also stable
    let ng = data.base.num_generators;
    assert(is_stable(data, inverse_symbol(s))) by {
        if s == Symbol::Gen(ng) {
            assert(inverse_symbol(s) == Symbol::Inv(ng));
        } else {
            assert(inverse_symbol(s) == Symbol::Gen(ng));
        }
    }
    lemma_translate_stable_empty(data, s, base_level);
    lemma_net_level_stable(data, inverse_symbol(s));

    if s == Symbol::Gen(ng) {
        lemma_translate_stable_empty(data, inverse_symbol(s), base_level + 1);
    } else {
        lemma_translate_stable_empty(data, inverse_symbol(s), base_level - 1);
    }
}

} // verus!
