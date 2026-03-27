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
use crate::reduction::*;
use crate::benign::*;
use crate::hnn::*;
use crate::tower::*;
use crate::normal_form_afp_textbook::Syllable;

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
    data: HNNData, m: nat, base_level: int,
    prefix: Word, middle: Word, suffix: Word,
)
    requires
        hnn_data_valid(data),
        net_level(data, middle) == 0,
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, middle, base_level + net_level(data, prefix)),
            empty_word()),
        presentation_valid(tower_presentation(data, m)),
        word_valid(translate_word_at(data, middle, base_level + net_level(data, prefix)),
            tower_presentation(data, m).num_generators),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, concat(prefix, concat(middle, suffix)), base_level),
            translate_word_at(data, concat(prefix, suffix), base_level)),
{
    let tp = tower_presentation(data, m);
    let lp = base_level + net_level(data, prefix);

    // Decompose translate of w = prefix · middle · suffix
    lemma_translate_concat(data, prefix, concat(middle, suffix), base_level);
    lemma_translate_concat(data, middle, suffix, lp);
    lemma_net_level_concat(data, prefix, concat(middle, suffix));
    lemma_net_level_concat(data, middle, suffix);

    // Decompose translate of w' = prefix · suffix
    lemma_translate_concat(data, prefix, suffix, base_level);

    let tr_prefix = translate_word_at(data, prefix, base_level);
    let tr_middle = translate_word_at(data, middle, lp);
    let tr_suffix = translate_word_at(data, suffix, lp);

    lemma_delete_equiv_empty(tp, tr_prefix, tr_middle, tr_suffix);
}

/// Reverse direction: translate(prefix · suffix) ≡ translate(prefix · middle · suffix).
/// Needs symmetry infrastructure.
pub proof fn lemma_translate_insert_middle(
    data: HNNData, m: nat, base_level: int,
    prefix: Word, middle: Word, suffix: Word,
)
    requires
        hnn_data_valid(data),
        net_level(data, middle) == 0,
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, middle, base_level + net_level(data, prefix)),
            empty_word()),
        presentation_valid(tower_presentation(data, m)),
        word_valid(translate_word_at(data, middle, base_level + net_level(data, prefix)),
            tower_presentation(data, m).num_generators),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, concat(prefix, suffix), base_level),
            translate_word_at(data, concat(prefix, concat(middle, suffix)), base_level)),
{
    let tp = tower_presentation(data, m);
    let lp = base_level + net_level(data, prefix);

    lemma_translate_concat(data, prefix, concat(middle, suffix), base_level);
    lemma_translate_concat(data, middle, suffix, lp);
    lemma_net_level_concat(data, prefix, concat(middle, suffix));
    lemma_net_level_concat(data, middle, suffix);
    lemma_translate_concat(data, prefix, suffix, base_level);

    let tr_prefix = translate_word_at(data, prefix, base_level);
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

// ============================================================
// Part G2: Base at copy k embeds in tower via shift homomorphism
// ============================================================

/// Shift homomorphism: base → tower(m), mapping Gen(i) → [Gen(i + k*ng)].
pub open spec fn shift_hom(data: HNNData, m: nat, k: nat) -> crate::homomorphism::HomomorphismData {
    let ng = data.base.num_generators;
    crate::homomorphism::HomomorphismData {
        source: data.base,
        target: tower_presentation(data, m),
        generator_images: Seq::new(ng, |i: int| Seq::new(1, |_j: int| Symbol::Gen((i + k * ng) as nat))),
    }
}

/// The shift homomorphism maps words to their shifted versions.
#[verifier::rlimit(200)]
proof fn lemma_shift_hom_applies(data: HNNData, k: nat, m: nat, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        crate::homomorphism::apply_hom(shift_hom(data, m, k), w)
            =~= shift_word(w, k * data.base.num_generators),
    decreases w.len(),
{
    let h = shift_hom(data, m, k);
    let ng = data.base.num_generators;
    let result = crate::homomorphism::apply_hom(h, w);
    let shifted = shift_word(w, k * ng);
    if w.len() == 0 {
        assert(result.len() == 0);
        assert(shifted.len() == 0);
    } else {
        lemma_shift_hom_applies(data, k, m, w.drop_first());
        // IH: apply_hom(h, rest) =~= shift_word(rest, k*ng)
        // result = concat(apply_hom_symbol(h, w.first()), apply_hom(h, rest))
        // shifted = Seq::new(w.len(), |j| shift_symbol(w[j], k*ng))
        // Element-wise: result[0] == shifted[0] and result[j] == shifted[j] for j > 0

        // The result has same length as shifted
        let s = w.first();
        assert(symbol_valid(s, ng));
        let sym_img = crate::homomorphism::apply_hom_symbol(h, s);
        // For both Gen and Inv: sym_img is a 1-element word = [shift_symbol(s, k*ng)]
        match s {
            Symbol::Gen(i) => {
                assert(sym_img.len() == 1);
                assert(sym_img[0] == shift_symbol(s, k * ng));
            }
            Symbol::Inv(i) => {
                // sym_img = inverse_word([Gen(i+k*ng)]) = [Inv(i+k*ng)]
                let gen_img = h.generator_images[i as int];
                assert(gen_img.len() == 1);
                assert(gen_img[0] == Symbol::Gen((i + k * ng) as nat));
                // inverse_word definition: Seq::new(w.len(), |j| inverse_symbol(w[w.len()-1-j]))
                // For len=1: Seq::new(1, |j| inverse_symbol(gen_img[0])) = [Inv(i+k*ng)]
                crate::word::lemma_inverse_word_len(gen_img);
                assert(sym_img.len() == 1);
                assert(sym_img[0] == shift_symbol(s, k * ng));
            }
        }
    }
}

/// The shift homomorphism is valid: relator images ≡ ε in tower(m).
proof fn lemma_shift_hom_valid(data: HNNData, m: nat, k: nat)
    requires
        hnn_data_valid(data),
        k <= m,
    ensures
        crate::homomorphism::is_valid_homomorphism(shift_hom(data, m, k)),
{
    let h = shift_hom(data, m, k);
    let ng = data.base.num_generators;
    reveal(presentation_valid);
    lemma_tower_valid(data, m);
    lemma_tower_num_generators(data, m);

    // Generator images are word_valid for tower(m)
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(h.generator_images[i], h.target.num_generators)
    by {
        assert(h.generator_images[i].len() == 1);
        assert((i + k * ng) < (m + 1) * ng) by (nonlinear_arith)
            requires i < ng as int, k <= m;
    }

    // Relator images ≡ ε: shift(relator, k*ng) ≡ ε in tower(m)
    assert forall|i: int| 0 <= i < h.source.relators.len()
        implies equiv_in_presentation(h.target,
            crate::homomorphism::apply_hom(h, h.source.relators[i]), empty_word())
    by {
        lemma_shift_hom_applies(data, k, m, h.source.relators[i]);
        // apply_hom(h, relator) =~= shift(relator, k*ng)
        lemma_base_relator_in_tower(data, m, k, i);
        // shift(relator, k*ng) ≡ ε in tower(m)
    }
}

/// Base at copy k embeds in tower(m): equiv(base, w1, w2) → equiv(tower(m), shift(w1, k*ng), shift(w2, k*ng)).
pub proof fn lemma_base_at_copy_k_embeds(
    data: HNNData, m: nat, k: nat, w1: Word, w2: Word,
)
    requires
        hnn_data_valid(data),
        k <= m,
        word_valid(w1, data.base.num_generators),
        word_valid(w2, data.base.num_generators),
        equiv_in_presentation(data.base, w1, w2),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            shift_word(w1, k * data.base.num_generators),
            shift_word(w2, k * data.base.num_generators)),
{
    lemma_shift_hom_valid(data, m, k);
    crate::homomorphism::lemma_hom_preserves_equiv(shift_hom(data, m, k), w1, w2);
    lemma_shift_hom_applies(data, k, m, w1);
    lemma_shift_hom_applies(data, k, m, w2);
}

// Tower identifications_isomorphic from hnn_associations_isomorphic.
//
// Infrastructure proven:
// - Backward: base_at_copy_k_embeds ✓ (shift homomorphism)
//   equiv(base, v, ε) → equiv(tower(m), shift(v, k*ng), ε)
// - Forward: lemma_afp_injectivity_right ✓ (G₂ one-shot)
//   equiv(AFP, shift(w, n1), ε) → equiv(base, w, ε)
//
// Remaining connection (~30 lines):
// - Show embed_a_tower(w) =~= shift(embed_a_hnn(w), k*ng) (shift-embedding distributivity)
// - Combine with hnn_associations_isomorphic for the biconditional
// - The Seq::new closure matching for a_words_tower vs shifted a_words_hnn
//   is the technical blocker (same issue as inverse_word_len was before finding it in word.rs)

/// Shift-embedding distributivity: embedding with shifted images = shift of embedding.
/// apply_embedding(shift_each(images, offset), w) =~= shift(apply_embedding(images, w), offset)
/// Shift-embedding distributivity: embedding with shifted images = shift of embedding.
/// Takes shifted_images as parameter to avoid Seq::new closure mismatch in ensures.
proof fn lemma_shift_embedding_distributes(
    images: Seq<Word>, shifted_images: Seq<Word>, w: Word, offset: nat,
)
    requires
        shifted_images.len() == images.len(),
        word_valid(w, images.len()),
        forall|i: int| 0 <= i < images.len() ==>
            #[trigger] shifted_images[i] =~= shift_word(images[i], offset),
    ensures
        apply_embedding(shifted_images, w)
            =~= shift_word(apply_embedding(images, w), offset),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        lemma_shift_embedding_distributes(images, shifted_images, w.drop_first(), offset);
        let s = w.first();
        crate::free_product::lemma_shift_concat(
            apply_embedding_symbol(images, s),
            apply_embedding(images, w.drop_first()), offset);
        // Trigger the forall for the specific symbol index and establish symbol-level =~=
        match s {
            Symbol::Gen(i) => {
                assert(shifted_images[i as int] =~= shift_word(images[i as int], offset));
            }
            Symbol::Inv(i) => {
                assert(shifted_images[i as int] =~= shift_word(images[i as int], offset));
                crate::free_product::lemma_shift_inverse_word(images[i as int], offset);
            }
        }
    }
}

/// Tower identifications_isomorphic from hnn_associations_isomorphic.
/// Uses shift-embedding distributivity + AFP right-injectivity + base_at_copy_k_embeds.
#[verifier::rlimit(300)]
/// Forward: tower(k) equiv → base equiv for embed_a_hnn.
proof fn lemma_tower_iso_forward_mid(
    data: HNNData, k: nat, embed_a_hnn: Word,
)
    requires
        hnn_data_valid(data),
        tower_textbook_chain(data, k),
        word_valid(embed_a_hnn, data.base.num_generators),
        equiv_in_presentation(tower_presentation(data, k),
            shift_word(embed_a_hnn, k * data.base.num_generators), empty_word()),
    ensures
        equiv_in_presentation(data.base, embed_a_hnn, empty_word()),
{
    let ng = data.base.num_generators;
    reveal(presentation_valid);
    if k == 0 {
        // tower(0) = base, shift by 0 = identity
        assert(k * ng == 0) by (nonlinear_arith) requires k == 0;
        assert(shift_word(embed_a_hnn, 0nat) =~= embed_a_hnn);
    } else {
        assert(tower_textbook_prereqs_at(data, (k - 1) as nat));
        lemma_tower_afp_data_valid(data, (k - 1) as nat);
        lemma_tower_valid(data, (k - 1) as nat);
        lemma_tower_num_generators(data, (k - 1) as nat);
        crate::normal_form_afp_textbook::lemma_afp_injectivity_right(
            tower_afp_data(data, (k - 1) as nat), embed_a_hnn);
    }
}

/// Backward: base equiv → tower(k) equiv for embed_a_hnn.
proof fn lemma_tower_iso_backward_mid(
    data: HNNData, k: nat, embed_a_hnn: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(embed_a_hnn, data.base.num_generators),
        equiv_in_presentation(data.base, embed_a_hnn, empty_word()),
    ensures
        equiv_in_presentation(tower_presentation(data, k),
            shift_word(embed_a_hnn, k * data.base.num_generators), empty_word()),
{
    // shift(ε, k*ng) =~= ε
    assert(shift_word(empty_word(), k * data.base.num_generators) =~= empty_word());
    lemma_base_at_copy_k_embeds(data, k, k, embed_a_hnn, empty_word());
}

// lemma_tower_iso_per_word: per-word biconditional for tower isomorphism.
// Logic complete (forward via AFP right-injectivity + hnn_iso, backward via base_at_copy_k_embeds + hnn_iso).
// Z3 engineering: needs explicit assertion chain connecting AFP right-injectivity output
// (equiv(tower_afp_data(k-1).p2, embed_a_hnn, ε)) to equiv(data.base, embed_a_hnn, ε)
// and shift(embed_a_hnn, k*ng) to embed_a_tower. ~10 more lines of intermediate assertions.
//
// All building blocks verified (0 assumes):
// - lemma_afp_injectivity_right ✓
// - lemma_base_at_copy_k_embeds ✓ (shift homomorphism)
// - lemma_shift_embedding_distributes ✓
// - hnn_associations_isomorphic ✓ (precondition)

/// Helper: per-word proof of the tower isomorphism biconditional.
#[verifier::rlimit(1000)]
proof fn lemma_tower_iso_per_word(
    data: HNNData, k: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        tower_textbook_chain(data, k),
        word_valid(w, data.associations.len() as nat),
    ensures ({
        let afp_data = tower_afp_data(data, k);
        let a_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].0);
        let b_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].1);
        equiv_in_presentation(afp_data.p1, apply_embedding(a_words_tower, w), empty_word())
        <==>
        equiv_in_presentation(afp_data.p2, apply_embedding(b_words_tower, w), empty_word())
    }),
{
    let ng = data.base.num_generators;
    let afp_data = tower_afp_data(data, k);
    let kk = data.associations.len();
    reveal(presentation_valid);

    assert(afp_data.identifications.len() == kk);
    let a_words_hnn = Seq::new(kk, |i: int| data.associations[i].0);
    let b_words_hnn = Seq::new(kk, |i: int| data.associations[i].1);
    // EXACTLY match ensures clause's Seq::new (same length expression)
    let a_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].0);
    let b_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].1);

    // Element-wise: a_words_tower[i] = shift(a_words_hnn[i], k*ng) and b_words_tower[i] = b_words_hnn[i]
    assert forall|i: int| 0 <= i < kk implies
        afp_data.identifications[i].1 == data.associations[i].1 by {}
    assert forall|i: int| 0 <= i < kk implies
        #[trigger] b_words_tower[i] =~= b_words_hnn[i] by {}
    assert(b_words_tower =~= b_words_hnn);

    // Shift-embedding distributivity
    assert forall|i: int| 0 <= i < a_words_hnn.len() implies
        #[trigger] a_words_tower[i] =~= shift_word(a_words_hnn[i], k * ng) by {}
    lemma_shift_embedding_distributes(a_words_hnn, a_words_tower, w, k * ng);
    let embed_a_hnn = apply_embedding(a_words_hnn, w);

    // word_valid for embed_a_hnn
    assert forall|j: int| 0 <= j < a_words_hnn.len()
        implies word_valid(#[trigger] a_words_hnn[j], ng)
    by { assert(word_valid(data.associations[j].0, ng)); }
    lemma_apply_embedding_valid(a_words_hnn, w, ng);

    let embed_a_tower = apply_embedding(a_words_tower, w);
    let embed_b_tower = apply_embedding(b_words_tower, w);

    // Connect embed_b_tower to embed_b_hnn (shift by 0 = identity)
    assert forall|i: int| 0 <= i < b_words_hnn.len() implies
        #[trigger] b_words_tower[i] =~= shift_word(b_words_hnn[i], 0nat) by {}
    lemma_shift_embedding_distributes(b_words_hnn, b_words_tower, w, 0nat);
    // embed_b_tower =~= shift(embed_b_hnn, 0) =~= embed_b_hnn
    assert(embed_b_tower =~= apply_embedding(b_words_hnn, w));

    // HNN biconditional (should fire from hnn_associations_isomorphic)
    assert(equiv_in_presentation(data.base, embed_a_hnn, empty_word())
        <==> equiv_in_presentation(data.base, apply_embedding(b_words_hnn, w), empty_word()));

    // Key =~= connections
    assert(b_words_tower =~= b_words_hnn);
    assert(embed_b_tower =~= apply_embedding(b_words_hnn, w));

    // Explicitly trigger hnn_iso biconditional
    assert(word_valid(w, kk as nat));
    assert(equiv_in_presentation(data.base, embed_a_hnn, empty_word())
        <==> equiv_in_presentation(data.base, apply_embedding(b_words_hnn, w), empty_word()));

    // Forward: equiv(p1, embed_a_tower, ε) → equiv(base, embed_a_hnn, ε)
    // Then hnn_iso → equiv(base, embed_b_hnn, ε) =~= equiv(p2, embed_b_tower, ε)
    // Setup for forward direction (AFP right-injectivity needs these)
    if k > 0 {
        assert(tower_textbook_prereqs_at(data, (k - 1) as nat));
        lemma_tower_afp_data_valid(data, (k - 1) as nat);
        lemma_tower_valid(data, (k - 1) as nat);
        lemma_tower_num_generators(data, (k - 1) as nat);
    }

    // Establish the two intermediate biconditionals, then chain
    let mid = equiv_in_presentation(data.base, embed_a_hnn, empty_word());
    let lhs = equiv_in_presentation(afp_data.p1, apply_embedding(a_words_tower, w), empty_word());
    let rhs = equiv_in_presentation(afp_data.p2, apply_embedding(b_words_tower, w), empty_word());

    // (1) mid ↔ rhs: from hnn_iso + embed_b connection
    // Already have: mid ↔ equiv(base, embed_b_hnn, ε) from hnn_iso
    // And: rhs = equiv(base, embed_b_tower, ε) = equiv(base, embed_b_hnn, ε) (from =~=)
    // So: mid ↔ rhs

    // (2) lhs → mid: tower equiv → base equiv
    if lhs {
        lemma_tower_iso_forward_mid(data, k, embed_a_hnn);
    }

    // (3) mid → lhs: base equiv → tower equiv
    if mid {
        lemma_tower_iso_backward_mid(data, k, embed_a_hnn);
    }
}

pub proof fn lemma_tower_identifications_isomorphic(
    data: HNNData, k: nat,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        tower_textbook_chain(data, k),
    ensures
        crate::normal_form_amalgamated::identifications_isomorphic(tower_afp_data(data, k)),
{
    let ng = data.base.num_generators;
    let afp_data = tower_afp_data(data, k);
    let kk = afp_data.identifications.len();
    reveal(presentation_valid);

    assert(kk == data.associations.len());
    assert forall|w: Word| word_valid(w, kk as nat) implies (
        equiv_in_presentation(afp_data.p1,
            apply_embedding(Seq::new(kk, |i: int| afp_data.identifications[i].0), w),
            empty_word())
        <==>
        equiv_in_presentation(afp_data.p2,
            apply_embedding(Seq::new(kk, |i: int| afp_data.identifications[i].1), w),
            empty_word()))
    by {
        lemma_tower_iso_per_word(data, k, w);
    }
}

/// A base inverse pair [s, inv(s)] at level k: net_level is 0 and translation ≡ ε in tower.
proof fn lemma_translate_base_pair_trivial(
    data: HNNData, m: nat, s: Symbol, base_level: nat,
)
    requires
        hnn_data_valid(data),
        !is_stable(data, s),
        symbol_valid(s, data.base.num_generators),
        base_level <= m,
    ensures ({
        let pair = concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| inverse_symbol(s)));
        &&& net_level(data, pair) == 0
        &&& equiv_in_presentation(tower_presentation(data, m),
                translate_word_at(data, pair, base_level as int), empty_word())
    }),
{
    let ng = data.base.num_generators;
    let s_word = Seq::new(1, |_j: int| s);
    let inv_s_word = Seq::new(1, |_j: int| inverse_symbol(s));
    let pair = concat(s_word, inv_s_word);

    // net_level(pair) = 0 (neither s nor inv(s) is stable)
    lemma_net_level_concat(data, s_word, inv_s_word);
    assert(s_word.first() == s);
    assert(s_word.drop_first() =~= Seq::<Symbol>::empty());
    assert(inv_s_word.first() == inverse_symbol(s));
    assert(inv_s_word.drop_first() =~= Seq::<Symbol>::empty());
    reveal_with_fuel(net_level, 2);
    assert(net_level(data, s_word) == 0) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert(net_level(data, inv_s_word) == 0) by {
        match s {
            Symbol::Gen(i) => { assert(!is_stable(data, Symbol::Inv(i))); }
            Symbol::Inv(i) => { assert(!is_stable(data, Symbol::Gen(i))); }
        }
    }

    // Fully unfold translate for 2-element pair
    reveal_with_fuel(translate_word_at, 3);
    // translate(pair, bl) = [shift_symbol(s, bl*ng), shift_symbol(inv(s), bl*ng)]
    // These form a cancelling pair
    let ss = shift_symbol(s, base_level * ng);
    let iss = shift_symbol(inverse_symbol(s), base_level * ng);
    // ss and iss are inverses: Gen(j+k) and Inv(j+k)
    assert(is_inverse_pair(ss, iss)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    // The translated pair has a cancellation at position 0
    let translated = translate_word_at(data, pair, base_level as int);
    assert(has_cancellation_at(translated, 0));
    assert(reduce_at(translated, 0) =~= empty_word());
    // Free reduction gives a 1-step derivation proving ≡ ε
    let step = DerivationStep::FreeReduce { position: 0 };
    assert(apply_step(tower_presentation(data, m), translated, step)
        == Some(empty_word()));
    let d = Derivation { steps: Seq::new(1, |_i: int| step) };
    assert(d.steps.len() == 1);
    assert(d.steps.first() == step);
    assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    reveal_with_fuel(derivation_produces, 2);
    assert(derivation_valid(tower_presentation(data, m), d, translated, empty_word()));
}

// ============================================================
// Part K: Level bounds and prefix_levels_bounded
// ============================================================

/// All prefix net_levels of w are in [0, m].
/// This means: for every j in [0, w.len()], net_level(w[0..j]) is in [0, m].
pub open spec fn prefix_levels_bounded(data: HNNData, w: Word, m: nat) -> bool {
    forall|j: int| #![trigger w.subrange(0, j)]
        0 <= j <= w.len() ==>
            0 <= net_level(data, w.subrange(0, j)) <= m as int
}

/// Net level of a subrange [0, j] decomposes via concat.
proof fn lemma_net_level_subrange_prefix(data: HNNData, w: Word, pos: int)
    requires 0 <= pos <= w.len(),
    ensures
        w =~= concat(w.subrange(0, pos), w.subrange(pos, w.len() as int)),
        net_level(data, w) == net_level(data, w.subrange(0, pos))
            + net_level(data, w.subrange(pos, w.len() as int)),
{
    assert(w =~= w.subrange(0, pos) + w.subrange(pos, w.len() as int));
    lemma_net_level_concat(data, w.subrange(0, pos), w.subrange(pos, w.len() as int));
}

// ============================================================
// Part L: word_valid for shift_word at arbitrary offset
// ============================================================

/// shift_word(w, k * ng) is word_valid for (m+1)*ng when w is base-valid and k <= m.
proof fn lemma_shift_word_valid_for_tower(
    data: HNNData, w: Word, k: nat, m: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        k <= m,
    ensures
        word_valid(shift_word(w, k * data.base.num_generators),
            (m + 1) * data.base.num_generators),
{
    let ng = data.base.num_generators;
    let sw = shift_word(w, k * ng);
    let n = (m + 1) * ng;
    // k <= m implies k*ng <= m*ng, so i + k*ng < ng + m*ng = (m+1)*ng = n
    assert(k * ng <= m * ng) by(nonlinear_arith)
        requires k <= m
    {}
    assert(n == m * ng + ng) by(nonlinear_arith)
        requires n == (m + 1) * ng
    {}
    assert forall|j: int| 0 <= j < sw.len()
        implies symbol_valid(#[trigger] sw[j], n)
    by {
        assert(sw[j] == shift_symbol(w[j], k * ng));
        assert(symbol_valid(w[j], ng));
        match w[j] {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
    }
}

/// inverse_word(shift_word(w, k*ng)) is word_valid for tower(m).
proof fn lemma_inv_shift_word_valid_for_tower(
    data: HNNData, w: Word, k: nat, m: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        k <= m,
    ensures
        word_valid(inverse_word(shift_word(w, k * data.base.num_generators)),
            (m + 1) * data.base.num_generators),
{
    let ng = data.base.num_generators;
    lemma_shift_word_valid_for_tower(data, w, k, m);
    crate::word::lemma_inverse_word_valid(
        shift_word(w, k * ng), (m + 1) * ng);
}

// ============================================================
// Part M: Net level helpers for relators
// ============================================================

/// Net level of inverse_word is the negation.
proof fn lemma_net_level_inverse(data: HNNData, w: Word)
    ensures
        net_level(data, inverse_word(w)) == -net_level(data, w),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(inverse_word(w) =~= empty_word());
    } else {
        let ng = data.base.num_generators;
        let s = w.first();
        let rest = w.drop_first();

        // inverse_word(w) = concat(inverse_word(rest), [inv(s)])
        let inv_s_word = Seq::new(1, |_j: int| inverse_symbol(s));
        assert(inverse_word(w) =~= concat(inverse_word(rest), inv_s_word));

        // net_level decomposes
        lemma_net_level_concat(data, inverse_word(rest), inv_s_word);
        lemma_net_level_inverse(data, rest);

        // net_level of [inv(s)]
        assert(inv_s_word.first() == inverse_symbol(s));
        assert(inv_s_word.drop_first() =~= Seq::<Symbol>::empty());
        reveal_with_fuel(net_level, 2);

        // Case analysis: net_level([inv(s)]) == -net_level_contribution(s)
        if s == Symbol::Gen(ng) {
            assert(inverse_symbol(s) == Symbol::Inv(ng));
        } else if s == Symbol::Inv(ng) {
            assert(inverse_symbol(s) == Symbol::Gen(ng));
        } else {
            match s {
                Symbol::Gen(i) => {
                    assert(i != ng);
                    assert(inverse_symbol(s) == Symbol::Inv(i));
                    assert(Symbol::Inv(i) != Symbol::Gen(ng));
                    assert(Symbol::Inv(i) != Symbol::Inv(ng));
                }
                Symbol::Inv(i) => {
                    assert(i != ng);
                    assert(inverse_symbol(s) == Symbol::Gen(i));
                    assert(Symbol::Gen(i) != Symbol::Gen(ng));
                    assert(Symbol::Gen(i) != Symbol::Inv(ng));
                }
            }
        }
    }
}

/// HNN relator has net_level 0.
proof fn lemma_net_level_hnn_relator(data: HNNData, i: int)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
    ensures
        net_level(data, hnn_relator(data, i)) == 0,
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    let t_inv = Seq::new(1, |_j: int| Symbol::Inv(ng));
    let t_gen = Seq::new(1, |_j: int| Symbol::Gen(ng));
    let part1 = concat(t_inv, a_i);
    let part2 = concat(t_gen, inverse_word(b_i));

    assert(hnn_relator(data, i) =~= concat(part1, part2));
    lemma_net_level_concat(data, part1, part2);
    lemma_net_level_concat(data, t_inv, a_i);
    lemma_net_level_concat(data, t_gen, inverse_word(b_i));
    lemma_net_level_stable(data, Symbol::Inv(ng));
    lemma_net_level_stable(data, Symbol::Gen(ng));
    lemma_net_level_base_word(data, a_i);
    crate::word::lemma_inverse_word_valid(b_i, ng);
    lemma_net_level_base_word(data, inverse_word(b_i));
}

/// Any relator in hnn_presentation has net_level 0.
proof fn lemma_net_level_hnn_pres_relator(data: HNNData, idx: int)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
    ensures
        net_level(data, hnn_presentation(data).relators[idx]) == 0,
{
    let p = hnn_presentation(data);
    let nb = data.base.relators.len();
    if idx < nb {
        assert(p.relators[idx] == data.base.relators[idx]);
        reveal(presentation_valid);
        lemma_net_level_base_word(data, data.base.relators[idx]);
    } else {
        let hi = (idx - nb) as int;
        assert(p.relators[idx] == hnn_relator(data, hi));
        lemma_net_level_hnn_relator(data, hi);
    }
}

/// get_relator has net_level 0 when the underlying relator does.
proof fn lemma_net_level_get_relator(data: HNNData, idx: nat, inverted: bool)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
    ensures
        net_level(data, get_relator(hnn_presentation(data), idx, inverted)) == 0,
{
    let p = hnn_presentation(data);
    lemma_net_level_hnn_pres_relator(data, idx as int);
    if inverted {
        lemma_net_level_inverse(data, p.relators[idx as int]);
    }
}

/// Decompose inverse_word(hnn_relator):
/// inv(t⁻¹ · a_i · t · inv(b_i)) = b_i · t⁻¹ · inv(a_i) · t
proof fn lemma_inverse_hnn_relator_decomp(data: HNNData, i: int)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
    ensures ({
        let ng = data.base.num_generators;
        let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
        let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
        let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
        inverse_word(hnn_relator(data, i)) =~=
            concat(b_i, concat(t_inv_word, concat(inverse_word(a_i), t_word)))
    }),
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
    let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
    let inv_b_i = inverse_word(b_i);

    // hnn_relator = concat(t_inv_word, concat(a_i, concat(t_word, inv_b_i)))
    let r = hnn_relator(data, i);
    assert(r =~= concat(t_inv_word, concat(a_i, concat(t_word, inv_b_i))));

    // Apply inverse_concat repeatedly
    crate::word::lemma_inverse_concat(t_inv_word, concat(a_i, concat(t_word, inv_b_i)));
    crate::word::lemma_inverse_concat(a_i, concat(t_word, inv_b_i));
    crate::word::lemma_inverse_concat(t_word, inv_b_i);

    // inverse of single-symbol words
    assert(inverse_word(t_inv_word) =~= t_word) by {
        reveal_with_fuel(inverse_word, 2);
    }
    assert(inverse_word(t_word) =~= t_inv_word) by {
        reveal_with_fuel(inverse_word, 2);
    }

    // inverse of inverse_word(b_i) = b_i
    crate::word::lemma_inverse_involution(b_i);

    // Chain: inv(r) = inv(inv_b_i) ++ inv(t_word) ++ inv(a_i) ++ inv(t_inv_word)
    //               = b_i ++ t_inv_word ++ inv(a_i) ++ t_word
}

// ============================================================
// Part N: Per-step translation — the core case analysis
// ============================================================

/// Helper: A single free-reduce or free-expand step preserves translation equivalence.
/// The inverse pair [s, inv(s)] either:
///  - stable pair: translates to ε (=~=)
///  - base pair: translates to a cancelling pair ≡ ε in tower
proof fn lemma_pair_translate_equiv_empty(
    data: HNNData, m: nat, s: Symbol, base_level: int,
)
    requires
        hnn_data_valid(data),
        symbol_valid(s, hnn_presentation(data).num_generators),
        0 <= base_level <= m as int,
    ensures ({
        let pair = concat(Seq::new(1, |_j: int| s),
                          Seq::new(1, |_j: int| inverse_symbol(s)));
        &&& net_level(data, pair) == 0
        &&& equiv_in_presentation(tower_presentation(data, m),
                translate_word_at(data, pair, base_level), empty_word())
        &&& word_valid(translate_word_at(data, pair, base_level),
                tower_presentation(data, m).num_generators)
    }),
{
    let ng = data.base.num_generators;
    let pair = concat(Seq::new(1, |_j: int| s),
                      Seq::new(1, |_j: int| inverse_symbol(s)));
    let tp = tower_presentation(data, m);

    if is_stable(data, s) {
        // Stable pair: translate =~= ε
        lemma_translate_stable_pair(data, s, base_level);
        assert(translate_word_at(data, pair, base_level) =~= empty_word());
        // empty word ≡ ε trivially
        lemma_equiv_refl(tp, empty_word());
        // word_valid of empty word
        assert(word_valid(empty_word(), tp.num_generators));
    } else {
        // Base pair: use existing lemma
        assert(symbol_valid(s, ng)) by {
            match s {
                Symbol::Gen(i) => { assert(i < ng + 1); assert(i != ng); assert(i < ng); }
                Symbol::Inv(i) => { assert(i < ng + 1); assert(i != ng); assert(i < ng); }
            }
        }
        lemma_translate_base_pair_trivial(data, m, s, base_level as nat);

        // word_valid: the translated pair is a 2-symbol word with shifted symbols
        lemma_tower_num_generators(data, m);
        reveal_with_fuel(translate_word_at, 3);
        let translated = translate_word_at(data, pair, base_level);
        let bl = base_level as nat;
        assert(bl * ng <= m * ng) by(nonlinear_arith)
            requires bl <= m
        {}
        assert((m + 1) * ng == m * ng + ng) by(nonlinear_arith) {}
        assert forall|j: int| 0 <= j < translated.len()
            implies symbol_valid(#[trigger] translated[j], tp.num_generators)
        by {
            match s {
                Symbol::Gen(i) => { assert(i < ng); }
                Symbol::Inv(i) => { assert(i < ng); }
            }
        }
    }
}

/// Helper: word_valid for the translation of a base relator at level k.
proof fn lemma_translate_base_relator_valid(
    data: HNNData, m: nat, k: nat, r_idx: int,
)
    requires
        hnn_data_valid(data),
        0 <= r_idx < data.base.relators.len(),
        k <= m,
    ensures
        word_valid(
            translate_word_at(data, data.base.relators[r_idx], k as int),
            tower_presentation(data, m).num_generators),
{
    let ng = data.base.num_generators;
    let r = data.base.relators[r_idx];
    reveal(presentation_valid);
    lemma_translate_base_word_at(data, r, k);
    lemma_tower_num_generators(data, m);
    lemma_shift_word_valid_for_tower(data, r, k, m);
}

/// Helper: word_valid for the translation of an HNN relator at level k.
proof fn lemma_translate_hnn_relator_valid(
    data: HNNData, m: nat, k: nat, i: int,
)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
        k >= 1,
        k <= m,
    ensures
        word_valid(
            translate_word_at(data, hnn_relator(data, i), k as int),
            tower_presentation(data, m).num_generators),
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    lemma_translate_hnn_relator(data, i, k as int);
    lemma_tower_num_generators(data, m);
    // translate = amalgamation_relator(tower_afp_data(data, (k-1)), i)
    //           = concat(shift_word(a_i, (k-1)*ng), inverse_word(shift_word(b_i, k*ng)))
    let afp_data = tower_afp_data(data, (k - 1) as nat);
    let tr = amalgamation_relator(afp_data, i);
    assert(translate_word_at(data, hnn_relator(data, i), k as int) =~= tr);

    // Need tower_num_generators at k-1 to connect afp_data.p1.num_generators = k*ng
    lemma_tower_num_generators(data, (k - 1) as nat);

    let sa = shift_word(a_i, ((k - 1) as nat) * ng);
    crate::word::lemma_inverse_word_valid(b_i, ng);
    let sb = shift_word(b_i, k * ng);
    let inv_sb = inverse_word(sb);

    let tp = tower_presentation(data, m);
    lemma_shift_word_valid_for_tower(data, a_i, (k - 1) as nat, m);
    lemma_shift_word_valid_for_tower(data, b_i, k, m);
    crate::word::lemma_inverse_word_valid(sb, (m + 1) * ng);
    crate::word::lemma_concat_word_valid(sa, inv_sb, (m + 1) * ng);

    // Connect tr to concat(sa, inv_sb) via afp_data decomposition
    assert(afp_data.p1.num_generators == k * ng);
    assert(tr =~= concat(sa, inv_sb));

    // Transfer word_valid through =~= to the translate
    let tw = translate_word_at(data, hnn_relator(data, i), k as int);
    assert forall|j: int| 0 <= j < tw.len()
        implies symbol_valid(#[trigger] tw[j], tp.num_generators)
    by {
        assert(tw[j] == tr[j]);
    }
}

/// Helper: translated relator (base or HNN, possibly inverted) is word_valid for tower(m).
proof fn lemma_translate_relator_valid(
    data: HNNData, m: nat, idx: nat, inverted: bool, level: int,
)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
        0 <= level <= m as int,
        // HNN relators need level >= 1
        idx >= data.base.relators.len() ==> level >= 1,
    ensures
        word_valid(
            translate_word_at(data,
                get_relator(hnn_presentation(data), idx, inverted), level),
            tower_presentation(data, m).num_generators),
{
    let p = hnn_presentation(data);
    let ng = data.base.num_generators;
    let nb = data.base.relators.len();
    let tp = tower_presentation(data, m);

    lemma_tower_num_generators(data, m);
    lemma_tower_valid(data, m);

    if !inverted {
        if idx < nb {
            // Base relator
            assert(p.relators[idx as int] == data.base.relators[idx as int]);
            lemma_translate_base_relator_valid(data, m, level as nat, idx as int);
        } else {
            // HNN relator
            let hi = (idx - nb) as int;
            assert(p.relators[idx as int] == hnn_relator(data, hi));
            lemma_translate_hnn_relator_valid(data, m, level as nat, hi);
        }
    } else {
        // Inverted relator: get_relator = inverse_word(p.relators[idx])
        if idx < nb {
            // Inverted base relator: inverse_word of a base word is still base-valid
            assert(p.relators[idx as int] == data.base.relators[idx as int]);
            let base_r = data.base.relators[idx as int];
            reveal(presentation_valid);
            crate::word::lemma_inverse_word_valid(base_r, ng);
            lemma_translate_base_word_at(data, inverse_word(base_r), level as nat);
            lemma_tower_num_generators(data, m);
            lemma_shift_word_valid_for_tower(data, inverse_word(base_r), level as nat, m);
        } else {
            // Inverted HNN relator: inv(t⁻¹·a_i·t·inv(b_i)) = b_i·t⁻¹·inv(a_i)·t
            let hi = (idx - nb) as int;
            assert(p.relators[idx as int] == hnn_relator(data, hi));
            lemma_inverse_hnn_relator_decomp(data, hi);
            let (a_i, b_i) = (data.associations[hi].0, data.associations[hi].1);
            let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
            let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
            crate::word::lemma_inverse_word_valid(a_i, ng);
            let inv_a_i = inverse_word(a_i);
            let k = level as nat;

            // Decompose and translate each part
            let part_a = b_i;
            let part_b = t_inv_word;
            let part_c = inv_a_i;
            let part_d = t_word;
            let part_cd = concat(part_c, part_d);
            let part_bcd = concat(part_b, part_cd);

            assert(inverse_word(hnn_relator(data, hi))
                =~= concat(part_a, part_bcd));

            // net_level computations
            lemma_net_level_base_word(data, b_i);
            lemma_net_level_base_word(data, inv_a_i);
            lemma_net_level_stable(data, Symbol::Inv(ng));
            lemma_net_level_stable(data, Symbol::Gen(ng));
            lemma_net_level_concat(data, part_c, part_d);
            lemma_net_level_concat(data, part_b, part_cd);

            // translate_concat decompositions
            lemma_translate_concat(data, part_a, part_bcd, k as int);
            lemma_translate_concat(data, part_b, part_cd, k as int);
            lemma_translate_concat(data, part_c, part_d, (k - 1) as int);
            lemma_translate_base_word_at(data, b_i, k);
            lemma_translate_stable_empty(data, Symbol::Inv(ng), k as int);
            lemma_translate_base_word_at(data, inv_a_i, (k - 1) as nat);
            lemma_translate_stable_empty(data, Symbol::Gen(ng), (k - 1) as int);

            let tr = translate_word_at(data, inverse_word(hnn_relator(data, hi)), k as int);
            assert(tr =~= concat(
                shift_word(b_i, k * ng),
                shift_word(inv_a_i, ((k - 1) as nat) * ng)));

            // word_valid of the translated parts
            lemma_shift_word_valid_for_tower(data, b_i, k, m);
            lemma_shift_word_valid_for_tower(data, inv_a_i, (k - 1) as nat, m);
            crate::word::lemma_concat_word_valid(
                shift_word(b_i, k * ng),
                shift_word(inv_a_i, ((k - 1) as nat) * ng),
                (m + 1) * ng);
        }
    }
}

/// Helper: translated relator (base or HNN, possibly inverted) ≡ ε in tower(m).
proof fn lemma_translate_relator_equiv_empty(
    data: HNNData, m: nat, idx: nat, inverted: bool, level: int,
)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
        0 <= level <= m as int,
        idx >= data.base.relators.len() ==> level >= 1,
    ensures ({
        let r = get_relator(hnn_presentation(data), idx, inverted);
        &&& net_level(data, r) == 0
        &&& equiv_in_presentation(tower_presentation(data, m),
                translate_word_at(data, r, level), empty_word())
    }),
{
    let p = hnn_presentation(data);
    let ng = data.base.num_generators;
    let nb = data.base.relators.len();
    let tp = tower_presentation(data, m);
    let r = get_relator(p, idx, inverted);

    lemma_net_level_get_relator(data, idx, inverted);

    if !inverted {
        if idx < nb {
            // Base relator at level k
            assert(r == data.base.relators[idx as int]);
            reveal(presentation_valid);
            lemma_translate_base_word_at(data, r, level as nat);
            lemma_base_relator_in_tower(data, m, level as nat, idx as int);
        } else {
            // HNN relator at level k
            let hi = (idx - nb) as int;
            assert(r == hnn_relator(data, hi));
            lemma_translate_hnn_relator(data, hi, level);
            lemma_ident_relator_in_tower(data, m, (level - 1) as nat, hi);
        }
    } else {
        // Inverted: get_relator = inverse_word(relator)
        if idx < nb {
            assert(r == inverse_word(data.base.relators[idx as int]));
            let base_r = data.base.relators[idx as int];
            reveal(presentation_valid);
            // First show non-inverted translate ≡ ε
            lemma_translate_base_word_at(data, base_r, level as nat);
            lemma_base_relator_in_tower(data, m, level as nat, idx as int);

            // Now show inverted: inverse_word(base_r) is still base-valid
            crate::word::lemma_inverse_word_valid(base_r, ng);
            lemma_translate_base_word_at(data, inverse_word(base_r), level as nat);

            // shift(inv(r), k*ng) = inv(shift(r, k*ng))
            crate::free_product::lemma_shift_inverse_word(base_r, (level as nat) * ng);

            // translate(inv(r), k) =~= inv(shift(r, k*ng)) and translate(r, k) ≡ ε
            // so inv(translate(r, k)) ≡ ε
            lemma_tower_valid(data, m);
            lemma_tower_num_generators(data, m);
            lemma_shift_word_valid_for_tower(data, base_r, level as nat, m);
            crate::normal_form_amalgamated::lemma_inverse_of_trivial(
                tp,
                shift_word(base_r, (level as nat) * ng));
        } else {
            let hi = (idx - nb) as int;
            assert(r == inverse_word(hnn_relator(data, hi)));
            // Decompose inv(hnn_relator) = b_i · t⁻¹ · inv(a_i) · t
            lemma_inverse_hnn_relator_decomp(data, hi);
            let (a_i, b_i) = (data.associations[hi].0, data.associations[hi].1);
            let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
            let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
            crate::word::lemma_inverse_word_valid(a_i, ng);
            let inv_a_i = inverse_word(a_i);
            let k = level as nat;

            let part_a = b_i;
            let part_b = t_inv_word;
            let part_c = inv_a_i;
            let part_d = t_word;
            let part_cd = concat(part_c, part_d);
            let part_bcd = concat(part_b, part_cd);

            assert(r =~= concat(part_a, part_bcd));

            // net_level and translate decomposition
            lemma_net_level_base_word(data, b_i);
            lemma_net_level_base_word(data, inv_a_i);
            lemma_net_level_stable(data, Symbol::Inv(ng));
            lemma_net_level_stable(data, Symbol::Gen(ng));
            lemma_net_level_concat(data, part_c, part_d);
            lemma_net_level_concat(data, part_b, part_cd);
            lemma_translate_concat(data, part_a, part_bcd, k as int);
            lemma_translate_concat(data, part_b, part_cd, k as int);
            lemma_translate_concat(data, part_c, part_d, (k - 1) as int);
            lemma_translate_base_word_at(data, b_i, k);
            lemma_translate_stable_empty(data, Symbol::Inv(ng), k as int);
            lemma_translate_base_word_at(data, inv_a_i, (k - 1) as nat);
            lemma_translate_stable_empty(data, Symbol::Gen(ng), (k - 1) as int);

            // translate(r, k) =~= concat(shift(b_i, k*ng), shift(inv(a_i), (k-1)*ng))
            let tr_inv = translate_word_at(data, r, k as int);
            assert(tr_inv =~= concat(
                shift_word(b_i, k * ng),
                shift_word(inv_a_i, ((k - 1) as nat) * ng)));

            // This equals inverse_word(amalgamation_relator(afp_data, hi))
            // amal_r = concat(shift(a_i, (k-1)*ng), inv(shift(b_i, k*ng)))
            // inv(amal_r) = concat(shift(b_i, k*ng), inv(shift(a_i, (k-1)*ng)))
            crate::free_product::lemma_shift_inverse_word(a_i, ((k - 1) as nat) * ng);
            // shift(inv(a_i), (k-1)*ng) =~= inv(shift(a_i, (k-1)*ng))

            // amal_r ≡ ε, so inv(amal_r) ≡ ε
            let afp_data = tower_afp_data(data, (level - 1) as nat);
            let amal_r = amalgamation_relator(afp_data, hi);
            lemma_translate_hnn_relator(data, hi, level);
            lemma_ident_relator_in_tower(data, m, (level - 1) as nat, hi);

            lemma_tower_valid(data, m);
            lemma_tower_num_generators(data, m);

            // word_valid of amal_r for lemma_inverse_of_trivial
            lemma_tower_num_generators(data, (level - 1) as nat);
            let sa = shift_word(a_i, ((k - 1) as nat) * ng);
            let sb = shift_word(b_i, k * ng);
            lemma_shift_word_valid_for_tower(data, a_i, (k - 1) as nat, m);
            lemma_shift_word_valid_for_tower(data, b_i, k, m);
            crate::word::lemma_inverse_word_valid(sb, (m + 1) * ng);
            crate::word::lemma_concat_word_valid(sa, inverse_word(sb), (m + 1) * ng);
            // amal_r =~= concat(sa, inverse_word(sb))
            assert(amal_r =~= concat(sa, inverse_word(sb)));
            // Transfer word_valid through =~=
            assert forall|j: int| 0 <= j < amal_r.len()
                implies symbol_valid(#[trigger] amal_r[j], tp.num_generators)
            by {
                let cv = concat(sa, inverse_word(sb));
                assert(amal_r[j] == cv[j]);
            }

            crate::normal_form_amalgamated::lemma_inverse_of_trivial(tp, amal_r);
            // inv(amal_r) = inv(concat(sa, inv(sb))) =~= concat(inv(inv(sb)), inv(sa)) =~= concat(sb, inv(sa))
            crate::word::lemma_inverse_concat(sa, inverse_word(sb));
            crate::word::lemma_inverse_involution(sb);
            // inv(sa) =~= shift(inv(a_i), (k-1)*ng)
            crate::free_product::lemma_shift_inverse_word(a_i, ((k - 1) as nat) * ng);
            assert(inverse_word(amal_r) =~= concat(sb, shift_word(inv_a_i, ((k - 1) as nat) * ng)));
            assert(tr_inv =~= inverse_word(amal_r));
        }
    }
}

// ============================================================
// Part O: The per-step lemma
// ============================================================

/// For FreeReduce/RelatorDelete at position pos:
/// the level at pos determines the middle's translation.
/// Need: 0 <= net_level(prefix) <= m, and for HNN relators, >= 1.
///
/// For FreeExpand/RelatorInsert at position pos:
/// the level at pos determines the middle's translation.
/// Same level requirements.
///
/// In all cases: translate(w) ≡ translate(w_next) in tower(m).
pub proof fn lemma_hnn_step_tower_equiv(
    data: HNNData, m: nat, base_level: int, w: Word, step: DerivationStep,
)
    requires
        hnn_data_valid(data),
        word_valid(w, hnn_presentation(data).num_generators),
        apply_step(hnn_presentation(data), w, step) is Some,
        step_level_ok(data, m, base_level, w, step),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, w, base_level),
            translate_word_at(data, apply_step(hnn_presentation(data), w, step).unwrap(), base_level)),
{
    let p = hnn_presentation(data);
    let tp = tower_presentation(data, m);
    let w_next = apply_step(p, w, step).unwrap();
    lemma_tower_valid(data, m);
    lemma_tower_num_generators(data, m);

    match step {
        DerivationStep::FreeReduce { position } => {
            let pos = position;
            let s = w[pos];
            let prefix = w.subrange(0, pos);
            let middle = concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| w[pos + 1]));
            let suffix = w.subrange(pos + 2, w.len() as int);

            assert(w =~= concat(prefix, concat(middle, suffix)));
            assert(w_next =~= concat(prefix, suffix));

            assert(is_inverse_pair(w[pos], w[pos + 1]));
            assert(w[pos + 1] == inverse_symbol(s));
            assert(middle =~= concat(Seq::new(1, |_j: int| s),
                                      Seq::new(1, |_j: int| inverse_symbol(s))));

            let level = base_level + net_level(data, prefix);

            assert(symbol_valid(s, p.num_generators));

            lemma_pair_translate_equiv_empty(data, m, s, level);

            lemma_translate_delete_middle(data, m, base_level, prefix, middle, suffix);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let pos = position;
            let prefix = w.subrange(0, pos);
            let suffix = w.subrange(pos, w.len() as int);
            let middle = concat(Seq::new(1, |_j: int| symbol),
                                Seq::new(1, |_j: int| inverse_symbol(symbol)));

            assert(w =~= concat(prefix, suffix));
            assert(w_next =~= concat(prefix, concat(middle, suffix)));

            let level = base_level + net_level(data, prefix);
            lemma_pair_translate_equiv_empty(data, m, symbol, level);

            lemma_translate_insert_middle(data, m, base_level, prefix, middle, suffix);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let pos = position;
            let r = get_relator(p, relator_index, inverted);
            let prefix = w.subrange(0, pos);
            let middle = r;
            let suffix = w.subrange(pos + r.len(), w.len() as int);

            assert(w.subrange(pos, pos + r.len() as int) == r);
            assert(w =~= concat(prefix, concat(middle, suffix)));
            assert(w_next =~= concat(prefix, suffix));

            let level = base_level + net_level(data, prefix);

            lemma_translate_relator_equiv_empty(data, m, relator_index, inverted, level);
            lemma_translate_relator_valid(data, m, relator_index, inverted, level);

            lemma_translate_delete_middle(data, m, base_level, prefix, middle, suffix);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let pos = position;
            let r = get_relator(p, relator_index, inverted);
            let prefix = w.subrange(0, pos);
            let suffix = w.subrange(pos, w.len() as int);
            let middle = r;

            assert(w =~= concat(prefix, suffix));
            assert(w_next =~= concat(prefix, concat(middle, suffix)));

            let level = base_level + net_level(data, prefix);

            lemma_translate_relator_equiv_empty(data, m, relator_index, inverted, level);
            lemma_translate_relator_valid(data, m, relator_index, inverted, level);

            lemma_translate_insert_middle(data, m, base_level, prefix, middle, suffix);
        },
    }
}

// ============================================================
// Part P: Derivation-level induction
// ============================================================

/// Get the position of a derivation step.
pub open spec fn step_position(step: DerivationStep) -> int {
    match step {
        DerivationStep::FreeReduce { position } => position,
        DerivationStep::FreeExpand { position, .. } => position,
        DerivationStep::RelatorInsert { position, .. } => position,
        DerivationStep::RelatorDelete { position, .. } => position,
    }
}

/// Whether a step involves an HNN relator (not a base relator).
pub open spec fn step_is_hnn_relator(data: HNNData, step: DerivationStep) -> bool {
    match step {
        DerivationStep::RelatorInsert { relator_index, .. } |
        DerivationStep::RelatorDelete { relator_index, .. } =>
            relator_index >= data.base.relators.len(),
        _ => false,
    }
}

/// Level condition for a single step applied to word w.
pub open spec fn step_level_ok(data: HNNData, m: nat, base_level: int, w: Word, step: DerivationStep) -> bool {
    let pos = step_position(step);
    let level = net_level(data, w.subrange(0, pos)) + base_level;
    &&& 0 <= level <= m as int
    &&& (step_is_hnn_relator(data, step) ==> level >= 1)
}

/// A full derivation from w producing w', where every step has valid levels.
/// Returns the final word (should equal w') when the derivation is valid.
pub open spec fn derivation_levels_ok(
    data: HNNData, m: nat, base_level: int,
    steps: Seq<DerivationStep>, start: Word,
) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 {
        true
    } else {
        let p = hnn_presentation(data);
        match apply_step(p, start, steps.first()) {
            Some(next) => {
                step_level_ok(data, m, base_level, start, steps.first())
                && derivation_levels_ok(data, m, base_level, steps.drop_first(), next)
            },
            None => false,
        }
    }
}

/// Main induction: if all steps in a derivation have valid (shifted) levels,
/// then translate_at(start, base_level) ≡ translate_at(end, base_level) in tower(m).
pub proof fn lemma_hnn_derivation_to_tower_equiv(
    data: HNNData, m: nat, base_level: int,
    steps: Seq<DerivationStep>, start: Word, end: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(start, hnn_presentation(data).num_generators),
        derivation_produces(hnn_presentation(data), steps, start) == Some(end),
        derivation_levels_ok(data, m, base_level, steps, start),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, start, base_level),
            translate_word_at(data, end, base_level)),
    decreases steps.len(),
{
    let p = hnn_presentation(data);
    let tp = tower_presentation(data, m);

    if steps.len() == 0 {
        assert(start == end);
        lemma_equiv_refl(tp, translate_word_at(data, start, base_level));
    } else {
        let step = steps.first();
        let mid = apply_step(p, start, step).unwrap();

        // Per-step: translate(start) ≡ translate(mid)
        lemma_hnn_step_tower_equiv(data, m, base_level, start, step);

        // mid is word_valid (step preserves word_valid)
        crate::britton_proof::lemma_hnn_presentation_valid(data);
        crate::presentation::lemma_step_preserves_word_valid_pres(p, start, step, mid);

        // Inductive: translate(mid) ≡ translate(end)
        lemma_hnn_derivation_to_tower_equiv(data, m, base_level, steps.drop_first(), mid, end);

        // Chain: translate(start) ≡ translate(end)
        lemma_equiv_transitive(tp,
            translate_word_at(data, start, base_level),
            translate_word_at(data, mid, base_level),
            translate_word_at(data, end, base_level));
    }
}

/// **Britton's Lemma (Lyndon-Schupp Ch. IV):**
/// If w is a base word (no stable letters) and w ≡ ε in the HNN extension G*,
/// then w ≡ ε in the base group G.
///
/// Proof:
/// 1. w ≡ ε in G* → derivation D with levels fitting in tower(m)
/// 2. lemma_hnn_derivation_to_tower_equiv → translate(w) ≡ translate(ε) in tower(m)
/// 3. translate(w) = w (base word), translate(ε) = ε
/// 4. lemma_g0_embeds_in_tower_textbook → w ≡ ε in G
pub proof fn britton_lemma(
    data: HNNData, m: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
        // The derivation fits within tower height m (at base_level 0)
        ({
            let d: Derivation = choose|d: Derivation|
                derivation_valid(hnn_presentation(data), d, w, empty_word());
            derivation_levels_ok(data, m, 0, d.steps, w)
        }),
        // Tower textbook prerequisites
        tower_textbook_chain(data, m),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    let hp = hnn_presentation(data);
    let d: Derivation = choose|d: Derivation|
        derivation_valid(hp, d, w, empty_word());

    assert(word_valid(w, hp.num_generators)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies symbol_valid(#[trigger] w[k], hp.num_generators)
        by {}
    }

    lemma_hnn_derivation_to_tower_equiv(data, m, 0, d.steps, w, empty_word());

    lemma_translate_base_word(data, w);
    lemma_translate_empty(data);

    lemma_g0_embeds_in_tower_textbook(data, m, w);
}

// ============================================================
// Part S: Derivation level bounds for shifted translation
// ============================================================

/// Minimum "adjusted" step level across a derivation.
/// For HNN relator steps, returns level - 1 (since they need level >= 1).
/// For other steps, returns level (since they need level >= 0).
/// Shift >= -derivation_min_adj_level ensures all shifted levels are valid.
pub open spec fn derivation_min_adj_level(
    data: HNNData, steps: Seq<DerivationStep>, start: Word,
) -> int
    decreases steps.len(),
{
    let hp = hnn_presentation(data);
    if steps.len() == 0 { 0 }
    else {
        match apply_step(hp, start, steps.first()) {
            Some(next) => {
                let pos = step_position(steps.first());
                let level = net_level(data, start.subrange(0, pos));
                let adj = if step_is_hnn_relator(data, steps.first()) { level - 1 } else { level };
                let rest_min = derivation_min_adj_level(data, steps.drop_first(), next);
                if adj < rest_min { adj } else { rest_min }
            }
            None => 0
        }
    }
}

/// Maximum step level across a derivation.
pub open spec fn derivation_max_step_level(
    data: HNNData, steps: Seq<DerivationStep>, start: Word,
) -> int
    decreases steps.len(),
{
    let hp = hnn_presentation(data);
    if steps.len() == 0 { 0 }
    else {
        match apply_step(hp, start, steps.first()) {
            Some(next) => {
                let pos = step_position(steps.first());
                let level = net_level(data, start.subrange(0, pos));
                let rest_max = derivation_max_step_level(data, steps.drop_first(), next);
                if level > rest_max { level } else { rest_max }
            }
            None => 0
        }
    }
}

/// If base_level >= -min_adj and m >= max_level + base_level,
/// then derivation_levels_ok holds.
proof fn lemma_derivation_levels_ok_from_bounds(
    data: HNNData, m: nat, base_level: int,
    steps: Seq<DerivationStep>, start: Word,
)
    requires
        derivation_produces(hnn_presentation(data), steps, start) is Some,
        base_level >= -derivation_min_adj_level(data, steps, start),
        m as int >= derivation_max_step_level(data, steps, start) + base_level,
    ensures
        derivation_levels_ok(data, m, base_level, steps, start),
    decreases steps.len(),
{
    if steps.len() == 0 {} else {
        let hp = hnn_presentation(data);
        let step = steps.first();
        let next = apply_step(hp, start, step).unwrap();
        let pos = step_position(step);
        let level = net_level(data, start.subrange(0, pos));
        let adj = if step_is_hnn_relator(data, step) { level - 1 } else { level };

        // adj >= derivation_min_adj_level, so base_level >= -adj, so level + base_level >= 0 (or >= 1)
        assert(adj >= derivation_min_adj_level(data, steps, start));
        // level <= derivation_max_step_level, so level + base_level <= m
        assert(level <= derivation_max_step_level(data, steps, start));

        // Recurse: rest_min >= whole_min and rest_max <= whole_max
        let rest_min = derivation_min_adj_level(data, steps.drop_first(), next);
        let rest_max = derivation_max_step_level(data, steps.drop_first(), next);
        assert(rest_min >= derivation_min_adj_level(data, steps, start)) by {
            if adj < rest_min {} else {}
        }
        assert(rest_max <= derivation_max_step_level(data, steps, start)) by {
            if level > rest_max {} else {}
        }

        lemma_derivation_levels_ok_from_bounds(data, m, base_level, steps.drop_first(), next);
    }
}

// ============================================================
// Part T: Tower textbook chain from HNN associations
// ============================================================

/// Derive tower_textbook_chain from hnn_associations_isomorphic by induction.
pub proof fn lemma_tower_textbook_chain_from_hnn_iso(data: HNNData, m: nat)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
    ensures
        tower_textbook_chain(data, m),
    decreases m,
{
    if m == 0 {
        assert forall|k: nat| k < 0nat
            implies #[trigger] tower_textbook_prereqs_at(data, k) by {}
    } else {
        // IH: tower_textbook_chain(data, m-1)
        lemma_tower_textbook_chain_from_hnn_iso(data, (m - 1) as nat);

        let k = (m - 1) as nat;
        let afp_data = tower_afp_data(data, k);

        // Prove identifications_isomorphic at level k
        lemma_tower_identifications_isomorphic(data, k);

        // Prove action_preserves_canonical at level k
        lemma_tower_afp_data_valid(data, k);
        lemma_tower_valid(data, k);
        reveal(presentation_valid);
        crate::normal_form_afp_textbook::lemma_iso_implies_apc(afp_data);

        assert(tower_textbook_prereqs_at(data, k));

        assert forall|j: nat| j < m
            implies #[trigger] tower_textbook_prereqs_at(data, j)
        by {
            if j < k {} // from IH
        }
    }
}

// ============================================================
// Part U: Copy-s tower embedding
// ============================================================

/// Generalized tower embedding: if shift(w, s*ng) ≡ ε in tower(m) where s <= m,
/// then w ≡ ε in base. Uses AFP left-injectivity to peel from tower(m) down to
/// tower(s), then AFP right-injectivity at level s-1.
pub proof fn lemma_copy_s_embeds(data: HNNData, m: nat, s: nat, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        s <= m,
        tower_textbook_chain(data, m),
        equiv_in_presentation(tower_presentation(data, m),
            shift_word(w, s * data.base.num_generators), empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
    decreases m,
{
    let ng = data.base.num_generators;
    if m == 0 {
        assert(s == 0);
        assert(s * ng == 0) by (nonlinear_arith) requires s == 0;
        assert(shift_word(w, 0nat) =~= w);
    } else if s == m {
        // shift(w, m*ng) is in the G₂ part of AFP at level m-1
        let prev = (m - 1) as nat;
        assert(tower_textbook_prereqs_at(data, prev));
        lemma_tower_afp_data_valid(data, prev);
        lemma_tower_valid(data, prev);
        lemma_tower_num_generators(data, prev);
        reveal(presentation_valid);
        crate::normal_form_afp_textbook::lemma_afp_injectivity_right(
            tower_afp_data(data, prev), w);
    } else {
        // s < m: shift(w, s*ng) is a tower(m-1) word
        let prev = (m - 1) as nat;
        assert(tower_textbook_prereqs_at(data, prev));
        lemma_tower_afp_data_valid(data, prev);
        lemma_tower_valid(data, prev);
        lemma_tower_num_generators(data, prev);
        reveal(presentation_valid);

        lemma_shift_word_valid_for_tower(data, w, s, prev);
        crate::normal_form_afp_textbook::lemma_afp_injectivity(
            tower_afp_data(data, prev), shift_word(w, s * ng));

        assert(tower_textbook_chain(data, prev)) by {
            assert forall|k: nat| k < prev
                implies #[trigger] tower_textbook_prereqs_at(data, k)
            by { assert(k < m); }
        }
        lemma_copy_s_embeds(data, prev, s, w);
    }
}

// ============================================================
// Part V: Translation of base word at shifted level
// ============================================================

/// translate_word_at(data, ε, base_level) = ε for any base_level.
proof fn lemma_translate_empty_at(data: HNNData, base_level: int)
    ensures
        translate_word_at(data, empty_word(), base_level) =~= empty_word(),
{}

/// **Britton's Lemma (Unconditional, Lyndon-Schupp Ch. IV):**
/// If w is a base word and w ≡ ε in the HNN extension G*, then w ≡ ε in G.
///
/// No additional assumptions beyond hnn_data_valid and hnn_associations_isomorphic.
/// The tower textbook prerequisites are derived from hnn_associations_isomorphic,
/// and the derivation levels are handled by shifting to a non-negative base level.
pub proof fn britton_lemma_unconditional(
    data: HNNData, w: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    let hp = hnn_presentation(data);
    let ng = data.base.num_generators;

    // Get the derivation
    let d: Derivation = choose|d: Derivation|
        derivation_valid(hp, d, w, empty_word());

    // Compute shift amount from derivation bounds
    let min_adj = derivation_min_adj_level(data, d.steps, w);
    let max_lev = derivation_max_step_level(data, d.steps, w);
    // base_level >= -min_adj ensures shifted levels are valid
    let base_level: nat = if min_adj >= 0 { 0 } else { (-min_adj) as nat };
    // m >= max_lev + base_level and m >= base_level (since max_lev >= 0 for base word derivations)
    // Use base_level + max_lev.abs() + 1 as a safe upper bound
    let max_lev_abs: nat = if max_lev >= 0 { max_lev as nat } else { (-max_lev) as nat };
    let m: nat = (base_level + max_lev_abs + 1) as nat;

    // base_level <= m (since m = base_level + max_lev_abs + 1 > base_level)
    assert(base_level <= m);
    // m >= max_lev + base_level (since m = base_level + |max_lev| + 1 >= base_level + max_lev)
    assert(m as int >= max_lev + base_level as int);

    // word_valid(w, hp.num_generators) — weaken from ng to ng+1
    assert(word_valid(w, hp.num_generators)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies symbol_valid(#[trigger] w[k], hp.num_generators)
        by {}
    }

    // Step 1: Levels are OK with the chosen base_level
    lemma_derivation_levels_ok_from_bounds(data, m, base_level as int, d.steps, w);

    // Step 2: Translate derivation to tower equivalence
    lemma_hnn_derivation_to_tower_equiv(data, m, base_level as int, d.steps, w, empty_word());

    // Step 3: translate_at(w, base_level) = shift_word(w, base_level * ng)
    lemma_translate_base_word_at(data, w, base_level);
    // Step 3b: translate_at(ε, base_level) = ε
    lemma_translate_empty_at(data, base_level as int);

    // Step 4: Tower textbook chain from hnn_associations_isomorphic
    lemma_tower_textbook_chain_from_hnn_iso(data, m);

    // Step 5: Copy-s tower embedding → w ≡ ε in base
    lemma_copy_s_embeds(data, m, base_level, w);
}

// ============================================================
// Part W: Full Britton's Lemma — right syllable count preservation
// ============================================================

/// Count right syllables in a syllable sequence.
pub open spec fn right_syllable_count(syls: Seq<Syllable>) -> nat
    decreases syls.len(),
{
    if syls.len() == 0 { 0 }
    else {
        (if !syls.first().is_left { 1nat } else { 0nat })
            + right_syllable_count(syls.drop_first())
    }
}

/// G₁ single-symbol action never changes the right syllable count.
proof fn lemma_act_left_sym_preserves_right_count(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires generator_index(s) < data.p1.num_generators,
    ensures
        right_syllable_count(
            crate::normal_form_afp_textbook::act_left_sym(data, s, h, syls).1)
            == right_syllable_count(syls),
{
    let product = concat(Seq::new(1, |_j: int| s),
        apply_embedding(crate::normal_form_afp_textbook::a_words(data), h));
    let new_rep = crate::normal_form_afp_textbook::a_rcoset_rep(data, product);

    if new_rep =~= empty_word() {
        // Absorbed: syllables unchanged
    } else if syls.len() == 0 || !syls.first().is_left {
        // Prepend LEFT syllable: right count unchanged
        let new_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: new_rep }) + syls;
        assert(new_syls.first().is_left);
        assert(new_syls.drop_first() =~= syls);
    } else {
        // Merge with existing LEFT syllable
        let full_product = concat(product, syls.first().rep);
        let merged_rep = crate::normal_form_afp_textbook::a_rcoset_rep(data, full_product);
        if merged_rep =~= empty_word() {
            // Absorbed left syllable
            assert(syls.first().is_left);
        } else {
            // Replace left syllable with new left
            let new_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep })
                + syls.drop_first();
            assert(new_syls.first().is_left);
            assert(new_syls.drop_first() =~= syls.drop_first());
        }
    }
}

/// G₁ full-word action preserves right syllable count.
proof fn lemma_act_g1_word_preserves_right_count(
    data: AmalgamatedData, w: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        crate::normal_form_amalgamated::identifications_isomorphic(data),
        crate::normal_form_afp_textbook::action_preserves_canonical(data),
        crate::normal_form_afp_textbook::is_canonical_state(data, h, syls),
        word_valid(w, data.p1.num_generators),
    ensures
        right_syllable_count(
            crate::normal_form_afp_textbook::act_word(data, w, h, syls).1)
            == right_syllable_count(syls),
    decreases w.len(),
{
    use crate::normal_form_afp_textbook::*;
    if w.len() == 0 {
        lemma_act_word_empty(data, h, syls);
    } else {
        let n = data.p1.num_generators;
        let s = w.last();
        let w_prefix = w.drop_last();
        assert(symbol_valid(s, n));
        assert(generator_index(s) < n);
        let (h1, syls1) = act_sym(data, s, h, syls);

        // act_sym for G₁ = act_left_sym
        assert(act_sym(data, s, h, syls) == act_left_sym(data, s, h, syls));
        lemma_act_left_sym_preserves_right_count(data, s, h, syls);

        // Canonical preservation: action_preserves_canonical is about act_word
        // Use single-symbol word to trigger it
        let s_word: Word = Seq::new(1, |_i: int| s);
        assert(word_valid(s_word, data.p1.num_generators + data.p2.num_generators)) by {
            let n12 = data.p1.num_generators + data.p2.num_generators;
            assert(symbol_valid(s, n));
            match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
        }
        // act_word([s], h, syls) gives canonical state
        assert(is_canonical_state(data,
            act_word(data, s_word, h, syls).0,
            act_word(data, s_word, h, syls).1));
        // act_word([s], ...) == act_sym(s, ...) — connect to h1, syls1
        lemma_act_word_single(data, s, h, syls);
        assert(is_canonical_state(data, h1, syls1));

        // IH
        assert(word_valid(w_prefix, n)) by {
            assert forall|k: int| 0 <= k < w_prefix.len()
                implies symbol_valid(#[trigger] w_prefix[k], n)
            by { assert(w_prefix[k] == w[k]); }
        }
        lemma_act_g1_word_preserves_right_count(data, w_prefix, h1, syls1);
    }
}

// ============================================================
// Part X: Full Britton's Lemma (Pinch Theorem)
// Lyndon-Schupp Ch. IV, Thm 2.1: if w ≡ ε in G* and w has
// stable letters, then w has a pinch.
// ============================================================

// --- X.1: Definitions ---

/// Whether word w contains at least one stable letter (t or t⁻¹).
pub open spec fn has_stable_letter(data: HNNData, w: Word) -> bool {
    exists|i: int| 0 <= i < w.len() && is_stable(data, #[trigger] w[i])
}

/// Adjacent opposite stable letters with only base symbols between.
pub open spec fn has_adjacent_opposite_at(data: HNNData, w: Word, i: int, j: int) -> bool {
    let ng = data.base.num_generators;
    &&& 0 <= i < j < w.len()
    &&& is_stable(data, w[i])
    &&& is_stable(data, w[j])
    &&& w[i] != w[j]
    &&& forall|k: int| i < k < j ==> !is_stable(data, #[trigger] w[k])
}

/// A pinch at (i, j): adjacent opposite stable letters whose intervening
/// base word lies in the appropriate associated subgroup.
/// - t·g·t⁻¹ (Gen then Inv at positions i,j): pinch iff g ∈ B
/// - t⁻¹·g·t (Inv then Gen at positions i,j): pinch iff g ∈ A
pub open spec fn has_pinch_at(data: HNNData, w: Word, i: int, j: int) -> bool {
    let ng = data.base.num_generators;
    let base_word = w.subrange(i + 1, j);
    let nk = data.associations.len();
    let a_gens = Seq::new(nk, |k: int| data.associations[k].0);
    let b_gens = Seq::new(nk, |k: int| data.associations[k].1);
    &&& has_adjacent_opposite_at(data, w, i, j)
    &&& (
        // t·g·t⁻¹: pinch iff g ∈ B
        (w[i] == Symbol::Gen(ng) && w[j] == Symbol::Inv(ng)
         && in_generated_subgroup(data.base, b_gens, base_word))
        ||
        // t⁻¹·g·t: pinch iff g ∈ A
        (w[i] == Symbol::Inv(ng) && w[j] == Symbol::Gen(ng)
         && in_generated_subgroup(data.base, a_gens, base_word))
    )
}

/// Word w has a pinch somewhere.
pub open spec fn has_pinch(data: HNNData, w: Word) -> bool {
    exists|i: int, j: int| has_pinch_at(data, w, i, j)
}

// --- X.2: Net level preservation ---

/// Net level of a single-symbol word.
proof fn lemma_net_level_single(data: HNNData, s: Symbol)
    ensures
        net_level(data, Seq::new(1, |_j: int| s)) == (
            if s == Symbol::Gen(data.base.num_generators) { 1int }
            else if s == Symbol::Inv(data.base.num_generators) { -1int }
            else { 0int }
        ),
{
    let w: Word = Seq::new(1, |_j: int| s);
    assert(w.first() == s);
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    reveal_with_fuel(net_level, 2);
}

/// Net level of an inverse pair [s, inv(s)] is 0.
proof fn lemma_net_level_inverse_pair(data: HNNData, s: Symbol)
    ensures
        net_level(data, Seq::new(1, |_j: int| s)
            + Seq::new(1, |_j: int| inverse_symbol(s))) == 0,
{
    let sw: Word = Seq::new(1, |_j: int| s);
    let iw: Word = Seq::new(1, |_j: int| inverse_symbol(s));
    lemma_net_level_concat(data, sw, iw);
    lemma_net_level_single(data, s);
    lemma_net_level_single(data, inverse_symbol(s));
    let ng = data.base.num_generators;
    match s {
        Symbol::Gen(i) => {
            assert(inverse_symbol(s) == Symbol::Inv(i));
            if i == ng {
                // Gen(ng) + Inv(ng): 1 + (-1) = 0
            } else {
                // Gen(i) + Inv(i): 0 + 0 = 0
                assert(Symbol::Inv(i) != Symbol::Gen(ng));
                assert(Symbol::Inv(i) != Symbol::Inv(ng));
            }
        }
        Symbol::Inv(i) => {
            assert(inverse_symbol(s) == Symbol::Gen(i));
            if i == ng {
                // Inv(ng) + Gen(ng): (-1) + 1 = 0
            } else {
                assert(Symbol::Gen(i) != Symbol::Gen(ng));
                assert(Symbol::Gen(i) != Symbol::Inv(ng));
            }
        }
    }
}

/// Each derivation step preserves net_level.
proof fn lemma_step_preserves_net_level(data: HNNData, w: Word, step: DerivationStep)
    requires
        hnn_data_valid(data),
        apply_step(hnn_presentation(data), w, step).is_Some(),
    ensures
        net_level(data, apply_step(hnn_presentation(data), w, step).unwrap())
            == net_level(data, w),
{
    let hp = hnn_presentation(data);
    let w2 = apply_step(hp, w, step).unwrap();
    match step {
        DerivationStep::FreeReduce { position } => {
            let p = position;
            let prefix = w.subrange(0, p);
            let suffix = w.subrange(p + 2, w.len() as int);
            let s = w[p];
            assert(w[p + 1] == inverse_symbol(s));
            let pair: Word = Seq::new(1, |_j: int| s)
                + Seq::new(1, |_j: int| inverse_symbol(s));
            // Decompose: w =~= prefix ++ pair ++ suffix, w2 =~= prefix ++ suffix
            assert(concat(pair, suffix) =~= w.subrange(p, w.len() as int)) by {
                assert(pair.len() == 2);
                assert(pair[0] == w[p]);
                assert(pair[1] == w[p + 1]);
                assert forall|k: int| 0 <= k < concat(pair, suffix).len()
                    implies concat(pair, suffix)[k] == w.subrange(p, w.len() as int)[k]
                by {}
            }
            assert(w =~= concat(prefix, concat(pair, suffix)));
            assert(w2 =~= concat(prefix, suffix));
            lemma_net_level_concat(data, prefix, concat(pair, suffix));
            lemma_net_level_concat(data, pair, suffix);
            lemma_net_level_concat(data, prefix, suffix);
            lemma_net_level_inverse_pair(data, s);
        }
        DerivationStep::FreeExpand { position, symbol } => {
            let p = position;
            let prefix = w.subrange(0, p);
            let suffix = w.subrange(p, w.len() as int);
            let pair: Word = Seq::new(1, |_j: int| symbol)
                + Seq::new(1, |_j: int| inverse_symbol(symbol));
            assert(w =~= concat(prefix, suffix));
            assert(w2 =~= concat(prefix, concat(pair, suffix)));
            lemma_net_level_concat(data, prefix, suffix);
            lemma_net_level_concat(data, prefix, concat(pair, suffix));
            lemma_net_level_concat(data, pair, suffix);
            lemma_net_level_inverse_pair(data, symbol);
        }
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let p = position;
            let r = get_relator(hp, relator_index, inverted);
            let prefix = w.subrange(0, p);
            let suffix = w.subrange(p, w.len() as int);
            assert(w =~= concat(prefix, suffix));
            assert(w2 =~= concat(prefix, concat(r, suffix)));
            lemma_net_level_concat(data, prefix, suffix);
            lemma_net_level_concat(data, prefix, concat(r, suffix));
            lemma_net_level_concat(data, r, suffix);
            lemma_net_level_get_relator(data, relator_index, inverted);
        }
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let p = position;
            let r = get_relator(hp, relator_index, inverted);
            let rlen = r.len();
            let prefix = w.subrange(0, p);
            let suffix = w.subrange(p + rlen as int, w.len() as int);
            assert(w.subrange(p, p + rlen as int) == r);
            assert(concat(r, suffix) =~= w.subrange(p, w.len() as int)) by {
                assert forall|k: int| 0 <= k < concat(r, suffix).len()
                    implies concat(r, suffix)[k] == w.subrange(p, w.len() as int)[k]
                by {}
            }
            assert(w =~= concat(prefix, concat(r, suffix)));
            assert(w2 =~= concat(prefix, suffix));
            lemma_net_level_concat(data, prefix, concat(r, suffix));
            lemma_net_level_concat(data, r, suffix);
            lemma_net_level_concat(data, prefix, suffix);
            lemma_net_level_get_relator(data, relator_index, inverted);
        }
    }
}

/// A derivation preserves net_level.
proof fn lemma_derivation_preserves_net_level(
    data: HNNData, steps: Seq<DerivationStep>, w: Word,
)
    requires
        hnn_data_valid(data),
        derivation_produces(hnn_presentation(data), steps, w).is_Some(),
    ensures
        net_level(data, derivation_produces(hnn_presentation(data), steps, w).unwrap())
            == net_level(data, w),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let hp = hnn_presentation(data);
        let first = steps[0];
        let rest = steps.drop_first();
        let w2 = apply_step(hp, w, first).unwrap();
        lemma_step_preserves_net_level(data, w, first);
        lemma_derivation_preserves_net_level(data, rest, w2);
    }
}

/// If w ≡ ε in the HNN extension, then net_level(w) = 0.
proof fn lemma_equiv_net_level_zero(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    ensures
        net_level(data, w) == 0,
{
    let hp = hnn_presentation(data);
    let d: Derivation = choose|d: Derivation| derivation_valid(hp, d, w, empty_word());
    lemma_derivation_preserves_net_level(data, d.steps, w);
}

// --- X.3: Adjacent opposite pair existence ---

/// Count of stable letters (Gen(ng) or Inv(ng)) in w starting from position `from`.
pub open spec fn stable_count_from(data: HNNData, w: Word, from: int) -> nat
    decreases (w.len() - from),
{
    if from >= w.len() { 0 }
    else {
        (if is_stable(data, w[from]) { 1nat } else { 0nat })
            + stable_count_from(data, w, from + 1)
    }
}

/// Find the next stable letter position at or after `from`.
pub open spec fn next_stable(data: HNNData, w: Word, from: int) -> int
    decreases (w.len() - from),
{
    if from >= w.len() { w.len() as int }
    else if is_stable(data, w[from]) { from }
    else { next_stable(data, w, from + 1) }
}

/// next_stable finds a stable letter if one exists from `from` onward.
proof fn lemma_next_stable_props(data: HNNData, w: Word, from: int)
    requires 0 <= from <= w.len(),
    ensures
        from <= next_stable(data, w, from) <= w.len(),
        next_stable(data, w, from) < w.len() ==>
            is_stable(data, w[next_stable(data, w, from)]),
        next_stable(data, w, from) < w.len() ==>
            forall|k: int| from <= k < next_stable(data, w, from)
                ==> !is_stable(data, #[trigger] w[k]),
        (next_stable(data, w, from) == w.len()) ==>
            forall|k: int| from <= k < w.len()
                ==> !is_stable(data, #[trigger] w[k]),
    decreases (w.len() - from),
{
    if from >= w.len() {
    } else if is_stable(data, w[from]) {
    } else {
        lemma_next_stable_props(data, w, from + 1);
    }
}

/// If all stable letters in w have the same sign, net_level has that sign.
/// Specifically: if every stable letter is Gen(ng), then net_level ≥ 0.
proof fn lemma_net_level_same_sign_nonneg(data: HNNData, w: Word)
    requires
        forall|k: int| 0 <= k < w.len() && is_stable(data, #[trigger] w[k])
            ==> w[k] == Symbol::Gen(data.base.num_generators),
    ensures
        net_level(data, w) >= 0,
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert forall|k: int| 0 <= k < rest.len() && is_stable(data, #[trigger] rest[k])
            implies rest[k] == Symbol::Gen(data.base.num_generators)
        by { assert(rest[k] == w[k + 1]); }
        lemma_net_level_same_sign_nonneg(data, rest);
    }
}

/// Symmetric: all Inv(ng) → net_level ≤ 0.
proof fn lemma_net_level_same_sign_nonpos(data: HNNData, w: Word)
    requires
        forall|k: int| 0 <= k < w.len() && is_stable(data, #[trigger] w[k])
            ==> w[k] == Symbol::Inv(data.base.num_generators),
    ensures
        net_level(data, w) <= 0,
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert forall|k: int| 0 <= k < rest.len() && is_stable(data, #[trigger] rest[k])
            implies rest[k] == Symbol::Inv(data.base.num_generators)
        by { assert(rest[k] == w[k + 1]); }
        lemma_net_level_same_sign_nonpos(data, rest);
    }
}

/// If net_level = 0 and the word has stable letters, there exist adjacent
/// opposite stable letters with only base symbols between.
proof fn lemma_adjacent_opposite_exists(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        has_stable_letter(data, w),
        net_level(data, w) == 0,
    ensures
        exists|i: int, j: int| has_adjacent_opposite_at(data, w, i, j),
{
    let witness_k: int = choose|i: int| 0 <= i < w.len() && is_stable(data, w[i]);
    lemma_next_stable_props(data, w, 0);
    let first_pos = next_stable(data, w, 0);
    assert(first_pos < w.len());
    // All stable letters before first_pos have same sign (vacuously: there are none).
    assert forall|k: int| 0 <= k < first_pos && is_stable(data, #[trigger] w[k])
        implies w[k] == w[first_pos] by {}
    lemma_scan_for_sign_change(data, w, first_pos);
}

/// Scan from position `pos` for the first adjacent opposite pair.
/// Invariant: all stable letters in w[0..pos] have the same sign as w[pos].
proof fn lemma_scan_for_sign_change(data: HNNData, w: Word, pos: int)
    requires
        hnn_data_valid(data),
        0 <= pos < w.len(),
        is_stable(data, w[pos]),
        net_level(data, w) == 0,
        forall|k: int| 0 <= k < pos && is_stable(data, #[trigger] w[k])
            ==> w[k] == w[pos],
    ensures
        exists|i: int, j: int| has_adjacent_opposite_at(data, w, i, j),
    decreases w.len() - pos,
{
    let ng = data.base.num_generators;
    lemma_next_stable_props(data, w, pos + 1);
    let next_pos = next_stable(data, w, pos + 1);

    if next_pos >= w.len() {
        // All stable letters have the same sign as w[pos].
        // If w[pos] = Gen(ng): all stable are Gen → net_level ≥ 0.
        //   But w[pos] = Gen(ng) contributes +1 so net_level ≥ 1 > 0. Contradiction.
        // If w[pos] = Inv(ng): all stable are Inv → net_level ≤ 0.
        //   But w[pos] = Inv(ng) contributes -1 so net_level ≤ -1 < 0. Contradiction.
        assert forall|k: int| 0 <= k < w.len() && is_stable(data, #[trigger] w[k])
            implies w[k] == w[pos]
        by {}
        if w[pos] == Symbol::Gen(ng) {
            lemma_net_level_same_sign_nonneg(data, w);
            // net_level ≥ 0 but we need > 0. Since w[pos] = Gen(ng):
            // Split at pos: net_level = net_level(w[0..pos]) + 1 + net_level(w[pos+1..])
            // w[0..pos] has all Gen stable → net_level ≥ 0
            // w[pos+1..] has no stable → net_level = 0
            // Total ≥ 0 + 1 + 0 = 1 > 0. Contradicts net_level = 0.
            lemma_net_level_subrange_prefix(data, w, pos);
            let before = w.subrange(0, pos);
            let tail = w.subrange(pos, w.len() as int);
            lemma_net_level_subrange_prefix(data, tail, 1);
            let after = tail.subrange(1, tail.len() as int);
            assert(after =~= w.subrange(pos + 1, w.len() as int));
            let s_word: Word = Seq::new(1, |_j: int| w[pos]);
            assert(tail.subrange(0, 1) =~= s_word);
            lemma_net_level_single(data, w[pos]);
            assert forall|k: int| 0 <= k < before.len() && is_stable(data, #[trigger] before[k])
                implies before[k] == Symbol::Gen(ng)
            by { assert(before[k] == w[k]); }
            lemma_net_level_same_sign_nonneg(data, before);
            assert forall|k: int| 0 <= k < after.len()
                implies !is_stable(data, #[trigger] after[k])
            by { assert(after[k] == w[pos + 1 + k]); }
            lemma_net_level_no_stable(data, after, 0);
        } else {
            assert(w[pos] == Symbol::Inv(ng));
            lemma_net_level_same_sign_nonpos(data, w);
            lemma_net_level_subrange_prefix(data, w, pos);
            let before = w.subrange(0, pos);
            let tail = w.subrange(pos, w.len() as int);
            lemma_net_level_subrange_prefix(data, tail, 1);
            let after = tail.subrange(1, tail.len() as int);
            assert(after =~= w.subrange(pos + 1, w.len() as int));
            let s_word: Word = Seq::new(1, |_j: int| w[pos]);
            assert(tail.subrange(0, 1) =~= s_word);
            lemma_net_level_single(data, w[pos]);
            assert forall|k: int| 0 <= k < before.len() && is_stable(data, #[trigger] before[k])
                implies before[k] == Symbol::Inv(ng)
            by { assert(before[k] == w[k]); }
            lemma_net_level_same_sign_nonpos(data, before);
            assert forall|k: int| 0 <= k < after.len()
                implies !is_stable(data, #[trigger] after[k])
            by { assert(after[k] == w[pos + 1 + k]); }
            lemma_net_level_no_stable(data, after, 0);
        }
        assert(false);
    } else if w[pos] != w[next_pos] {
        assert(has_adjacent_opposite_at(data, w, pos, next_pos));
    } else {
        // Same sign — extend the invariant and recurse
        assert forall|k: int| 0 <= k < next_pos && is_stable(data, #[trigger] w[k])
            implies w[k] == w[next_pos]
        by {
            if k <= pos {
                if k < pos {
                    assert(w[k] == w[pos]);
                }
                assert(w[pos] == w[next_pos]);
            } else {
                // k is between pos+1 and next_pos-1: not stable
                assert(!is_stable(data, w[k]));
            }
        }
        lemma_scan_for_sign_change(data, w, next_pos);
    }
}

/// A word with no stable letters from position `offset` onward has net_level = 0.
proof fn lemma_net_level_no_stable(data: HNNData, w: Word, offset: int)
    requires
        hnn_data_valid(data),
        forall|k: int| 0 <= k < w.len()
            ==> !is_stable(data, #[trigger] w[k]),
    ensures
        net_level(data, w) == 0,
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(!is_stable(data, s));
        assert(s != Symbol::Gen(data.base.num_generators));
        assert(s != Symbol::Inv(data.base.num_generators));
        assert forall|k: int| 0 <= k < rest.len()
            implies !is_stable(data, #[trigger] rest[k])
        by { assert(rest[k] == w[k + 1]); }
        lemma_net_level_no_stable(data, rest, offset + 1);
    }
}

// --- X.4: Subgroup helpers ---

/// If b_rcoset_rep(g) = ε, then g is in the right subgroup (B).
proof fn lemma_b_rcoset_empty_implies_in_right_subgroup(
    data: AmalgamatedData, g: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p2.num_generators),
        b_rcoset_rep(data, g) =~= empty_word(),
    ensures
        crate::normal_form_amalgamated::in_right_subgroup(data, g),
{
    use crate::normal_form_afp_textbook::*;
    lemma_b_rcoset_rep_props(data, g);
    // same_b_rcoset(data, g, rep) where rep =~= ε
    // same_b_rcoset(data, g, ε) = in_right_subgroup(data, concat(g, inverse_word(ε)))
    let rep = b_rcoset_rep(data, g);
    assert(same_b_rcoset(data, g, rep));
    // rep =~= ε implies inverse_word(rep) =~= ε
    assert(inverse_word(empty_word()) =~= empty_word()) by {
        assert(inverse_word(empty_word()).len() == 0);
    }
    // concat(g, inverse_word(ε)) =~= g
    assert(concat(g, inverse_word(empty_word())) =~= g) by {
        let e = inverse_word(empty_word());
        assert(e.len() == 0);
        assert forall|k: int| 0 <= k < concat(g, e).len()
            implies concat(g, e)[k] == g[k] by {}
    }
}

/// Contrapositive: if g ∉ B, then b_rcoset_rep(g) ≠ ε.
proof fn lemma_not_in_right_subgroup_rep_nonempty(
    data: AmalgamatedData, g: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p2.num_generators),
        !crate::normal_form_amalgamated::in_right_subgroup(data, g),
    ensures
        !(b_rcoset_rep(data, g) =~= empty_word()),
{
    use crate::normal_form_afp_textbook::*;
    if b_rcoset_rep(data, g) =~= empty_word() {
        lemma_b_rcoset_empty_implies_in_right_subgroup(data, g);
    }
}

/// Subgroup right cancellation: if concat(g, b) ∈ S and b ∈ S, then g ∈ S.
proof fn lemma_subgroup_right_cancel(
    p: Presentation, gens: Seq<Word>, g: Word, b: Word,
)
    requires
        presentation_valid(p),
        word_valid(g, p.num_generators),
        word_valid(b, p.num_generators),
        in_generated_subgroup(p, gens, concat(g, b)),
        in_generated_subgroup(p, gens, b),
        forall|i: int| 0 <= i < gens.len()
            ==> word_valid(#[trigger] gens[i], p.num_generators),
    ensures
        in_generated_subgroup(p, gens, g),
{
    use crate::normal_form_afp_textbook::*;
    // inv(b) ∈ S
    lemma_subgroup_inverse(p, gens, b);
    // concat(concat(g, b), inv(b)) ∈ S
    lemma_subgroup_concat(p, gens, concat(g, b), inverse_word(b));
    // concat(concat(g, b), inv(b)) ≡ g
    lemma_right_cancel(p, g, b);
    // g ∈ S (by equiv closure)
    lemma_in_subgroup_equiv(
        p, gens,
        concat(concat(g, b), inverse_word(b)), g,
    );
}

/// If g ∉ B and embed_b(h) ∈ B, then concat(g, embed_b(h)) ∉ B.
proof fn lemma_not_in_subgroup_concat_embed_b(
    data: AmalgamatedData, g: Word, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        word_valid(h, crate::normal_form_afp_textbook::k_size(data)),
        !crate::normal_form_amalgamated::in_right_subgroup(data, g),
        forall|i: int| 0 <= i < crate::normal_form_afp_textbook::b_words(data).len()
            ==> word_valid(
                #[trigger] crate::normal_form_afp_textbook::b_words(data)[i],
                data.p2.num_generators),
    ensures
        !crate::normal_form_amalgamated::in_right_subgroup(
            data, concat(g, apply_embedding(
                crate::normal_form_afp_textbook::b_words(data), h))),
{
    use crate::normal_form_afp_textbook::*;
    use crate::normal_form_amalgamated::in_right_subgroup;
    let embed = apply_embedding(b_words(data), h);
    // embed is word_valid
    lemma_apply_embedding_valid(b_words(data), h, data.p2.num_generators);
    // embed_b(h) ∈ B
    lemma_apply_embedding_in_subgroup_g2(data.p2, b_words(data), h);
    // in_right_subgroup(data, w) == in_generated_subgroup(data.p2, b_words(data), w)
    assert(b_words(data) =~= Seq::new(data.identifications.len(), |i: int| data.identifications[i].1));
    // If concat(g, embed) were in B, then g ∈ B by right cancel. Contradiction.
    if in_right_subgroup(data, concat(g, embed)) {
        let b_gens = b_words(data);
        lemma_subgroup_right_cancel(data.p2, b_gens, g, embed);
    }
}

// --- X.5: Tower injectivity (peeling) ---

/// If w is a word in tower(k) and w ≡ ε in tower(m), then w ≡ ε in tower(k).
/// (Tower embedding is injective.)
pub proof fn lemma_tower_injectivity_peel(
    data: HNNData, k: nat, m: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        k <= m,
        tower_textbook_chain(data, m),
        word_valid(w, tower_presentation(data, k).num_generators),
        equiv_in_presentation(tower_presentation(data, m), w, empty_word()),
    ensures
        equiv_in_presentation(tower_presentation(data, k), w, empty_word()),
    decreases m - k,
{
    if k == m {
    } else {
        let prev = (m - 1) as nat;
        assert(tower_textbook_prereqs_at(data, prev));
        lemma_tower_afp_data_valid(data, prev);
        lemma_tower_valid(data, prev);
        lemma_tower_num_generators(data, prev);
        lemma_tower_num_generators(data, k);
        reveal(presentation_valid);

        // w is word_valid for tower(k), weaken to tower(prev) since k ≤ prev
        assert(word_valid(w, tower_presentation(data, prev).num_generators)) by {
            assert((k + 1) * data.base.num_generators
                <= (prev + 1) * data.base.num_generators)
                by(nonlinear_arith) requires k <= prev;
            assert forall|i: int| 0 <= i < w.len()
                implies symbol_valid(#[trigger] w[i],
                    tower_presentation(data, prev).num_generators)
            by {}
        }

        // AFP left-injectivity: w ∈ tower(prev) ≡ G₁, w ≡ ε in AFP → w ≡ ε in tower(prev)
        crate::normal_form_afp_textbook::lemma_afp_injectivity(
            tower_afp_data(data, prev), w);

        assert(tower_textbook_chain(data, prev)) by {
            assert forall|k2: nat| k2 < prev
                implies #[trigger] tower_textbook_prereqs_at(data, k2)
            by { assert(k2 < m); }
        }
        lemma_tower_injectivity_peel(data, k, prev, w);
    }
}

// --- X.6: Translate word_valid for the word's own levels ---

/// translate_word_at produces a valid word for tower(m) when the running
/// levels stay in [0, m].
proof fn lemma_translate_word_valid_for_level(
    data: HNNData, w: Word, bl: int, m: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, hnn_presentation(data).num_generators),
        // All shifted running levels in [0, m]
        forall|k: int| #![trigger w.subrange(0, k)]
            0 <= k <= w.len() ==>
            0 <= bl + net_level(data, w.subrange(0, k)) <= m as int,
    ensures
        word_valid(translate_word_at(data, w, bl),
            tower_presentation(data, m).num_generators),
    decreases w.len(),
{
    let ng = data.base.num_generators;
    let hp = hnn_presentation(data);
    lemma_tower_num_generators(data, m);
    let n_tower = tower_presentation(data, m).num_generators;
    assert(n_tower == (m + 1) * ng);

    if w.len() == 0 {
        assert(translate_word_at(data, w, bl) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();

        // rest is word_valid for hp
        assert(word_valid(rest, hp.num_generators)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(#[trigger] rest[k], hp.num_generators)
            by { assert(rest[k] == w[k + 1]); }
        }

        // Transfer the running level bounds to rest
        assert forall|k: int| #![trigger rest.subrange(0, k)]
            0 <= k <= rest.len()
            implies ({
                let new_bl = bl + (
                    if s == Symbol::Gen(ng) { 1int }
                    else if s == Symbol::Inv(ng) { -1int }
                    else { 0int }
                );
                0 <= new_bl + net_level(data, rest.subrange(0, k)) <= m as int
            })
        by {
            let prefix_rest = rest.subrange(0, k);
            let prefix_w = w.subrange(0, k + 1);
            assert(prefix_w.subrange(1, prefix_w.len() as int) =~= prefix_rest);
            assert(prefix_w =~= Seq::new(1, |_j: int| s) + prefix_rest);
            lemma_net_level_concat(data, Seq::new(1, |_j: int| s), prefix_rest);
            lemma_net_level_single(data, s);
            // net_level(w.subrange(0, k+1)) = net_level([s]) + net_level(rest.subrange(0, k))
            assert(w.subrange(0, k + 1) =~= prefix_w);
        }

        if s == Symbol::Gen(ng) {
            lemma_translate_word_valid_for_level(data, rest, bl + 1, m);
        } else if s == Symbol::Inv(ng) {
            lemma_translate_word_valid_for_level(data, rest, bl - 1, m);
        } else {
            // Base symbol: translate = [shifted_s] ++ translate(rest)
            lemma_translate_word_valid_for_level(data, rest, bl, m);
            let shifted_s = match s {
                Symbol::Gen(i) => Symbol::Gen((i + bl * ng) as nat),
                Symbol::Inv(i) => Symbol::Inv((i + bl * ng) as nat),
            };
            // shifted_s is valid for tower(m)
            // generator index = i + bl*ng where i < ng and 0 <= bl <= m
            // So index < ng + m*ng = (m+1)*ng = n_tower
            assert(bl >= 0) by {
                // From the level bounds: bl + net_level(w.subrange(0, 0)) >= 0
                // net_level(w.subrange(0, 0)) = net_level(ε) = 0
                assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
            }
            assert(bl <= m as int) by {
                assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
            }
            // shifted_s has index i + bl*ng. Need i + bl*ng < (m+1)*ng.
            // Since i < ng, bl >= 0, bl <= m: i + bl*ng < ng + m*ng = (m+1)*ng. ✓
            assert(bl * (ng as int) <= (m as int) * (ng as int))
                by(nonlinear_arith) requires bl >= 0, bl <= m as int;
            assert(symbol_valid(shifted_s, n_tower)) by {
                match s {
                    Symbol::Gen(i) => {
                        assert(i < ng);
                        assert(i as int + bl * (ng as int) >= 0);
                        assert(i as int + bl * (ng as int)
                            < (ng as int) + (m as int) * (ng as int));
                        assert((ng as int) + (m as int) * (ng as int)
                            == ((m as int) + 1) * (ng as int))
                            by(nonlinear_arith);
                    }
                    Symbol::Inv(i) => {
                        assert(i < ng);
                        assert(i as int + bl * (ng as int) >= 0);
                        assert(i as int + bl * (ng as int)
                            < (ng as int) + (m as int) * (ng as int));
                        assert((ng as int) + (m as int) * (ng as int)
                            == ((m as int) + 1) * (ng as int))
                            by(nonlinear_arith);
                    }
                }
            }
            let tw_rest = translate_word_at(data, rest, bl);
            let tw = translate_word_at(data, w, bl);
            assert(tw =~= concat(Seq::new(1, |_j: int| shifted_s), tw_rest));
            assert forall|k: int| 0 <= k < tw.len()
                implies symbol_valid(#[trigger] tw[k], n_tower)
            by {
                if k == 0 {
                    assert(tw[0] == shifted_s);
                } else {
                    assert(tw[k] == tw_rest[k - 1]);
                }
            }
        }
    }
}

// --- X.7: Running level bounds ---

/// Each symbol changes the running level by at most 1, so after k symbols
/// the level is in [-k, k].
proof fn lemma_prefix_level_bounded_by_k(data: HNNData, w: Word, k: int)
    requires 0 <= k <= w.len(),
    ensures
        -k <= net_level(data, w.subrange(0, k)) <= k,
    decreases k,
{
    if k == 0 {
        assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
    } else {
        lemma_prefix_level_bounded_by_k(data, w, k - 1);
        let prefix = w.subrange(0, k);
        let prev = w.subrange(0, k - 1);
        assert(prefix =~= concat(prev, Seq::new(1, |_j: int| w[k - 1])));
        lemma_net_level_concat(data, prev, Seq::new(1, |_j: int| w[k - 1]));
        lemma_net_level_single(data, w[k - 1]);
    }
}

/// With base_level = w.len(), all shifted running levels are in [0, 2*w.len()].
proof fn lemma_word_level_bounds(data: HNNData, w: Word, k: int)
    requires 0 <= k <= w.len(),
    ensures
        0 <= (w.len() as int) + net_level(data, w.subrange(0, k)) <= 2 * (w.len() as int),
{
    lemma_prefix_level_bounded_by_k(data, w, k);
}


// --- X.8: Left syllable count + G₂ preservation (dual of Part W) ---
// Textbook (Miller p.48-49): the permutation representation handles BOTH
// p and p⁻¹. G₁ processing creates LEFT syllables (A-cosets), G₂ creates
// RIGHT syllables (B-cosets). Each type preserves the other's count.

/// Count left syllables in a syllable sequence.
pub open spec fn left_syllable_count(syls: Seq<Syllable>) -> nat
    decreases syls.len(),
{
    if syls.len() == 0 { 0 }
    else {
        (if syls.first().is_left { 1nat } else { 0nat })
            + left_syllable_count(syls.drop_first())
    }
}

/// G₂ single-symbol action never changes the left syllable count.
proof fn lemma_act_right_sym_preserves_left_count(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires generator_index(s) < data.p2.num_generators,
    ensures
        left_syllable_count(
            crate::normal_form_afp_textbook::act_right_sym(data, s, h, syls).1)
            == left_syllable_count(syls),
{
    let product = concat(Seq::new(1, |_i: int| s),
        apply_embedding(crate::normal_form_afp_textbook::b_words(data), h));
    let new_rep = crate::normal_form_afp_textbook::b_rcoset_rep(data, product);

    if new_rep =~= empty_word() {
    } else if syls.len() == 0 || syls.first().is_left {
        let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: new_rep }) + syls;
        assert(!new_syls.first().is_left);
        assert(new_syls.drop_first() =~= syls);
    } else {
        let full_product = concat(product, syls.first().rep);
        let merged_rep = crate::normal_form_afp_textbook::b_rcoset_rep(data, full_product);
        if merged_rep =~= empty_word() {
            assert(!syls.first().is_left);
        } else {
            let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
                + syls.drop_first();
            assert(!new_syls.first().is_left);
            assert(new_syls.drop_first() =~= syls.drop_first());
        }
    }
}

/// G₂ full-word action preserves left syllable count.
proof fn lemma_act_g2_word_preserves_left_count(
    data: AmalgamatedData, w: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        crate::normal_form_amalgamated::identifications_isomorphic(data),
        crate::normal_form_afp_textbook::action_preserves_canonical(data),
        crate::normal_form_afp_textbook::is_canonical_state(data, h, syls),
        word_valid(w, data.p2.num_generators),
    ensures
        left_syllable_count(
            crate::normal_form_afp_textbook::act_word(
                data, shift_word(w, data.p1.num_generators), h, syls).1)
            == left_syllable_count(syls),
    decreases w.len(),
{
    use crate::normal_form_afp_textbook::*;
    let n1 = data.p1.num_generators;
    let sw = shift_word(w, n1);
    if w.len() == 0 {
        assert(sw =~= empty_word());
        lemma_act_word_empty(data, h, syls);
    } else {
        let s = w.last();
        let w_prefix = w.drop_last();
        assert(symbol_valid(s, data.p2.num_generators));
        assert(generator_index(s) < data.p2.num_generators);

        // Connect shift_word structure
        let shifted_s = shift_symbol(s, n1);
        assert(sw.last() == shifted_s);
        let sw_prefix = shift_word(w_prefix, n1);
        assert(sw.drop_last() =~= sw_prefix) by {
            assert(sw.drop_last().len() == sw_prefix.len());
            assert forall|k: int| 0 <= k < sw_prefix.len()
                implies sw.drop_last()[k] == sw_prefix[k]
            by { assert(w_prefix[k] == w[k]); }
        }

        let (h1, syls1) = act_sym(data, shifted_s, h, syls);
        assert(act_sym(data, shifted_s, h, syls) == act_right_sym(data, s, h, syls));
        lemma_act_right_sym_preserves_left_count(data, s, h, syls);

        let s_word: Word = Seq::new(1, |_i: int| shifted_s);
        assert(word_valid(s_word, n1 + data.p2.num_generators)) by {
            match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
        }
        assert(is_canonical_state(data,
            act_word(data, s_word, h, syls).0,
            act_word(data, s_word, h, syls).1));
        lemma_act_word_single(data, shifted_s, h, syls);
        assert(is_canonical_state(data, h1, syls1));

        assert(word_valid(w_prefix, data.p2.num_generators)) by {
            assert forall|k: int| 0 <= k < w_prefix.len()
                implies symbol_valid(#[trigger] w_prefix[k], data.p2.num_generators)
            by { assert(w_prefix[k] == w[k]); }
        }
        // IH: act on shifted prefix preserves left_count
        lemma_act_g2_word_preserves_left_count(data, w_prefix, h1, syls1);
        // Connect: act(sw, h, syls) = act(sw_prefix, h1, syls1)
        // since sw = sw_prefix ++ [shifted_s] and act processes right-to-left
    }
}

// --- X.9: A-side subgroup helpers (dual of X.4) ---

/// If a_rcoset_rep(g) = ε, then g is in the left subgroup (A).
proof fn lemma_a_rcoset_empty_implies_in_left_subgroup(
    data: AmalgamatedData, g: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        crate::normal_form_afp_textbook::a_rcoset_rep(data, g) =~= empty_word()
            ==> crate::normal_form_amalgamated::in_left_subgroup(data, g),
{
    use crate::normal_form_afp_textbook::*;
    if a_rcoset_rep(data, g) =~= empty_word() {
        lemma_a_rcoset_rep_props(data, g);
        assert(inverse_word(empty_word()) =~= empty_word()) by {
            assert(inverse_word(empty_word()).len() == 0);
        }
        assert(concat(g, inverse_word(empty_word())) =~= g) by {
            assert forall|k: int| 0 <= k < concat(g, empty_word()).len()
                implies concat(g, empty_word())[k] == g[k] by {}
        }
    }
}

/// If g ∉ A and embed_a(h) ∈ A, then concat(g, embed_a(h)) ∉ A.
proof fn lemma_not_in_left_subgroup_concat_embed_a(
    data: AmalgamatedData, g: Word, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        word_valid(h, crate::normal_form_afp_textbook::k_size(data)),
        !crate::normal_form_amalgamated::in_left_subgroup(data, g),
        forall|i: int| 0 <= i < crate::normal_form_afp_textbook::a_words(data).len()
            ==> word_valid(
                #[trigger] crate::normal_form_afp_textbook::a_words(data)[i],
                data.p1.num_generators),
    ensures
        !crate::normal_form_amalgamated::in_left_subgroup(
            data, concat(g, apply_embedding(
                crate::normal_form_afp_textbook::a_words(data), h))),
{
    use crate::normal_form_afp_textbook::*;
    use crate::normal_form_amalgamated::in_left_subgroup;
    let embed = apply_embedding(a_words(data), h);
    lemma_apply_embedding_valid(a_words(data), h, data.p1.num_generators);
    lemma_apply_embedding_in_subgroup(data.p1, a_words(data), h);
    assert(a_words(data) =~= Seq::new(data.identifications.len(), |i: int| data.identifications[i].0));
    if in_left_subgroup(data, concat(g, embed)) {
        let a_gens = a_words(data);
        lemma_subgroup_right_cancel(data.p1, a_gens, g, embed);
    }
}



// --- X.10: Translate of a Gen·base·Inv segment ---

/// translate(Gen · g · Inv, bl) = shift(g, (bl+1)*ng) where g is a base word.
/// This is the G₂ segment at junction bl↔(bl+1).
proof fn lemma_translate_gen_base_inv(data: HNNData, g: Word, bl: int)
    requires
        hnn_data_valid(data),
        word_valid(g, data.base.num_generators),
        bl >= 0,
    ensures ({
        let ng = data.base.num_generators;
        let gen_sym: Word = Seq::new(1, |_j: int| Symbol::Gen(ng));
        let inv_sym: Word = Seq::new(1, |_j: int| Symbol::Inv(ng));
        let segment = concat(gen_sym, concat(g, inv_sym));
        &&& net_level(data, segment) == 0
        &&& translate_word_at(data, segment, bl) =~=
                shift_word(g, ((bl + 1) * ng) as nat)
    }),
{
    let ng = data.base.num_generators;
    let gen_sym: Word = Seq::new(1, |_j: int| Symbol::Gen(ng));
    let inv_sym: Word = Seq::new(1, |_j: int| Symbol::Inv(ng));
    let segment = concat(gen_sym, concat(g, inv_sym));

    // net_level: Gen(+1) + base(0) + Inv(-1) = 0
    lemma_net_level_concat(data, gen_sym, concat(g, inv_sym));
    lemma_net_level_single(data, Symbol::Gen(ng));
    lemma_net_level_concat(data, g, inv_sym);
    lemma_net_level_single(data, Symbol::Inv(ng));
    lemma_net_level_base_word(data, g);

    // translate: Gen is skipped (bl→bl+1), g at level bl+1 → shift(g, (bl+1)*ng),
    // Inv is skipped (bl+1→bl).
    // translate(segment, bl) = translate(concat(g, inv_sym), bl + 1)
    //   = concat(translate(g, bl+1), translate(inv_sym, bl+1))
    //   = concat(shift(g, (bl+1)*ng), translate(Inv, bl+1))
    //   = concat(shift(g, (bl+1)*ng), ε)   [Inv skipped]
    //   =~= shift(g, (bl+1)*ng)

    // The translate recursion: first symbol = Gen(ng), skipped, recurse with bl+1.
    // After Gen: translate(concat(g, inv_sym), bl+1).
    // g is a base word: translate(g, bl+1) = shift(g, (bl+1)*ng).
    assert(bl + 1 >= 0);
    lemma_translate_base_word_at(data, g, (bl + 1) as nat);
    // Then Inv: translate(inv_sym, bl+1) = translate(ε, bl+1-1) = ε.
    lemma_translate_empty_at(data, bl);

    // Connect: translate(segment, bl) starts with Gen → skip → translate(concat(g, inv_sym), bl+1)
    // translate(concat(g, inv_sym), bl+1): by lemma_translate_concat:
    // = concat(translate(g, bl+1), translate(inv_sym, bl+1 + net_level(g)))
    // = concat(shift(g, (bl+1)*ng), translate(inv_sym, bl+1))  [net_level(g) = 0]
    // = concat(shift(g, (bl+1)*ng), ε)
    lemma_translate_concat(data, g, inv_sym, bl + 1);
    lemma_net_level_base_word(data, g);

    // Now: translate(inv_sym, bl+1): Inv at bl+1 → skip, translate(ε, bl) = ε.
    assert(translate_word_at(data, inv_sym, bl + 1) =~= empty_word()) by {
        // inv_sym = [Inv(ng)]. translate: first sym = Inv(ng) → skip → translate(ε, bl) = ε.
        assert(inv_sym.first() == Symbol::Inv(ng));
        assert(inv_sym.drop_first() =~= Seq::<Symbol>::empty());
    }

    // Combine:
    // translate(segment, bl):
    // first sym = Gen(ng) → skip → translate(concat(g, inv_sym), bl+1)
    // = concat(shift(g, (bl+1)*ng), ε) =~= shift(g, (bl+1)*ng)
    assert(segment.first() == Symbol::Gen(ng));
    assert(segment.drop_first() =~= concat(g, inv_sym));
    assert(concat(shift_word(g, ((bl + 1) * ng) as nat), empty_word())
        =~= shift_word(g, ((bl + 1) * ng) as nat)) by {
        let sw = shift_word(g, ((bl + 1) * ng) as nat);
        assert(concat(sw, empty_word()).len() == sw.len());
        assert forall|k: int| 0 <= k < sw.len()
            implies concat(sw, empty_word())[k] == sw[k] by {}
    }
}


// --- X.10b: Max prefix level (re-added) ---

/// Max prefix net level: max of net_level(w[0..k]) for k in [0, |w|].
pub open spec fn max_prefix_level(data: HNNData, w: Word) -> int
    decreases w.len(),
{
    if w.len() == 0 { 0 }
    else {
        let ng = data.base.num_generators;
        let s = w.first();
        let s_val = if s == Symbol::Gen(ng) { 1int }
            else if s == Symbol::Inv(ng) { -1int }
            else { 0int };
        let rest_max = s_val + max_prefix_level(data, w.drop_first());
        if rest_max > 0 { rest_max } else { 0 }
    }
}

/// max_prefix_level ≥ 0 and bounds all prefix levels.
proof fn lemma_max_prefix_bounds(data: HNNData, w: Word, k: int)
    requires 0 <= k <= w.len(),
    ensures
        max_prefix_level(data, w) >= 0,
        net_level(data, w.subrange(0, k)) <= max_prefix_level(data, w),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
    } else if k == 0 {
        assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let sw: Word = Seq::new(1, |_j: int| s);
        assert(w.subrange(0, k) =~= concat(sw, rest.subrange(0, k - 1)));
        lemma_net_level_concat(data, sw, rest.subrange(0, k - 1));
        lemma_net_level_single(data, s);
        lemma_max_prefix_bounds(data, rest, k - 1);
    }
}

/// The max is achieved at some k.
proof fn lemma_max_prefix_achieved(data: HNNData, w: Word)
    ensures
        exists|k: int| 0 <= k <= w.len()
            && net_level(data, w.subrange(0, k)) == max_prefix_level(data, w),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
    } else {
        let ng = data.base.num_generators;
        let s = w.first();
        let rest = w.drop_first();
        let s_val = if s == Symbol::Gen(ng) { 1int }
            else if s == Symbol::Inv(ng) { -1int }
            else { 0int };
        let rest_max = s_val + max_prefix_level(data, rest);

        if rest_max <= 0 {
            assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
        } else {
            lemma_max_prefix_achieved(data, rest);
            let k_rest: int = choose|k: int| 0 <= k <= rest.len()
                && net_level(data, rest.subrange(0, k)) == max_prefix_level(data, rest);
            let k_w = k_rest + 1;
            let sw: Word = Seq::new(1, |_j: int| s);
            assert(w.subrange(0, k_w) =~= concat(sw, rest.subrange(0, k_rest)));
            lemma_net_level_concat(data, sw, rest.subrange(0, k_rest));
            lemma_net_level_single(data, s);
        }
    }
}

// --- X.11: Gen-Inv pair when max_prefix_level ≥ 1 ---

/// Forward scan: find first k in [from, bound] achieving max after a drop.
/// Ensures the pair is at the max prefix level.
proof fn lemma_find_gen_inv_forward(data: HNNData, w: Word, from: int, bound: int)
    requires
        hnn_data_valid(data),
        has_stable_letter(data, w),
        net_level(data, w) == 0,
        max_prefix_level(data, w) >= 1,
        1 <= from <= bound <= w.len(),
        net_level(data, w.subrange(0, bound)) == max_prefix_level(data, w),
        net_level(data, w.subrange(0, from - 1)) < max_prefix_level(data, w),
    ensures
        exists|i: int, j: int|
            has_adjacent_opposite_at(data, w, i, j)
            && w[i] == Symbol::Gen(data.base.num_generators)
            && w[j] == Symbol::Inv(data.base.num_generators)
            && net_level(data, w.subrange(0, i + 1)) == max_prefix_level(data, w),
    decreases bound - from,
{
    let ng = data.base.num_generators;
    let max_lev = max_prefix_level(data, w);
    lemma_max_prefix_bounds(data, w, from);

    if net_level(data, w.subrange(0, from)) == max_lev {
        // First achiever after drop. Contribution = max - prev ≥ 1 → Gen.
        let prev = w.subrange(0, from - 1);
        let curr = w.subrange(0, from);
        assert(curr =~= concat(prev, Seq::new(1, |_j: int| w[from - 1])));
        lemma_net_level_concat(data, prev, Seq::new(1, |_j: int| w[from - 1]));
        lemma_net_level_single(data, w[from - 1]);
        assert(w[from - 1] == Symbol::Gen(ng));

        // Next stable after from: must be Inv (Gen would exceed max).
        lemma_next_stable_props(data, w, from);
        let ns = next_stable(data, w, from);

        if ns >= w.len() {
            // No stable after → suffix net = 0 → total = max ≥ 1 ≠ 0. Contradiction.
            lemma_net_level_subrange_prefix(data, w, from);
            let suffix = w.subrange(from, w.len() as int);
            assert forall|k: int| 0 <= k < suffix.len()
                implies !is_stable(data, #[trigger] suffix[k])
            by { assert(suffix[k] == w[from + k]); }
            lemma_net_level_no_stable(data, suffix, 0);
            // net(w) = max + 0 = max ≥ 1 ≠ 0. Contradiction.
        } else if w[ns] == Symbol::Gen(ng) {
            // Level goes to max + 1 > max. Contradiction with max bound.
            let mid = w.subrange(from, ns);
            assert forall|k: int| 0 <= k < mid.len()
                implies !is_stable(data, #[trigger] mid[k])
            by { assert(mid[k] == w[from + k]); }
            lemma_net_level_no_stable(data, mid, 0);
            assert(w.subrange(0, ns + 1) =~=
                concat(w.subrange(0, from), w.subrange(from, ns + 1)));
            let tail = w.subrange(from, ns + 1);
            assert(tail =~= concat(mid, Seq::new(1, |_j: int| w[ns])));
            lemma_net_level_concat(data, mid, Seq::new(1, |_j: int| w[ns]));
            lemma_net_level_single(data, w[ns]);
            lemma_net_level_concat(data, w.subrange(0, from), tail);
            lemma_max_prefix_bounds(data, w, ns + 1);
        } else {
            // Inv! Gen-Inv pair found at max level.
            assert(w[ns] == Symbol::Inv(ng));
            assert(has_adjacent_opposite_at(data, w, from - 1, ns));
            // net_level(w[0..(from-1)+1]) = net_level(w[0..from]) = max ✓
            assert(w.subrange(0, (from - 1) + 1) =~= w.subrange(0, from));
        }
    } else {
        // from doesn't achieve max. net(w[0..from]) < max (since ≤ max and ≠ max).
        // Recurse forward.
        lemma_find_gen_inv_forward(data, w, from + 1, bound);
    }
}

/// When max_prefix_level ≥ 1, there exists a Gen-Inv adjacent pair AT the max level.
proof fn lemma_gen_inv_pair_when_max_ge_1(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        has_stable_letter(data, w),
        net_level(data, w) == 0,
        max_prefix_level(data, w) >= 1,
    ensures
        exists|i: int, j: int|
            has_adjacent_opposite_at(data, w, i, j)
            && w[i] == Symbol::Gen(data.base.num_generators)
            && w[j] == Symbol::Inv(data.base.num_generators)
            && net_level(data, w.subrange(0, i + 1)) == max_prefix_level(data, w),
{
    lemma_max_prefix_achieved(data, w);
    let any_k: int = choose|k: int| 0 <= k <= w.len()
        && net_level(data, w.subrange(0, k)) == max_prefix_level(data, w);
    assert(any_k > 0) by {
        assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
    }
    assert(net_level(data, w.subrange(0, 0int)) < max_prefix_level(data, w)) by {
        assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
    }
    lemma_find_gen_inv_forward(data, w, 1, any_k);
}

// --- X.12: Last max-level position ---

/// Given a position achieving max, find the LAST such position (scanning forward).
/// Everything after is strictly below max.
proof fn lemma_last_max_position(data: HNNData, w: Word, pos: int)
    requires
        0 <= pos <= w.len(),
        net_level(data, w.subrange(0, pos)) == max_prefix_level(data, w),
    ensures
        exists|k: int|
            #![trigger w.subrange(0, k)]
            pos <= k <= w.len()
            && net_level(data, w.subrange(0, k)) == max_prefix_level(data, w)
            && (forall|k2: int| k < k2 <= w.len()
                ==> net_level(data, #[trigger] w.subrange(0, k2))
                    < max_prefix_level(data, w)),
    decreases w.len() - pos,
{
    let max_lev = max_prefix_level(data, w);
    if pos >= w.len() as int {
        // pos = w.len(). k = pos works. No k2 > pos ≤ w.len() exists.
    } else {
        lemma_max_prefix_bounds(data, w, pos + 1);
        if net_level(data, w.subrange(0, pos + 1)) == max_lev {
            lemma_last_max_position(data, w, pos + 1);
        } else {
            // pos+1 is < max. Scan forward for any later achiever.
            lemma_last_max_scan(data, w, pos, pos + 1);
        }
    }
}

/// Scan forward: either find a later achiever, or confirm last_known is the last.
proof fn lemma_last_max_scan(data: HNNData, w: Word, last_known: int, from: int)
    requires
        0 <= last_known < from <= w.len(),
        net_level(data, w.subrange(0, last_known)) == max_prefix_level(data, w),
        forall|k: int| last_known < k < from
            ==> net_level(data, #[trigger] w.subrange(0, k))
                < max_prefix_level(data, w),
    ensures
        exists|k: int|
            #![trigger w.subrange(0, k)]
            last_known <= k <= w.len()
            && net_level(data, w.subrange(0, k)) == max_prefix_level(data, w)
            && (forall|k2: int| k < k2 <= w.len()
                ==> net_level(data, #[trigger] w.subrange(0, k2))
                    < max_prefix_level(data, w)),
    decreases w.len() - from,
{
    let max_lev = max_prefix_level(data, w);
    if from >= w.len() as int {
        lemma_max_prefix_bounds(data, w, w.len() as int);
        if net_level(data, w.subrange(0, w.len() as int)) == max_lev {
            // w.len() is a later achiever. It's the last (nothing after).
            assert(w.subrange(0, w.len() as int) =~= w);
        } else {
            // last_known is the last achiever.
        }
    } else {
        lemma_max_prefix_bounds(data, w, from);
        if net_level(data, w.subrange(0, from)) == max_lev {
            // from achieves max. Update last_known and continue scanning.
            lemma_last_max_scan(data, w, from, from + 1);
        } else {
            // from doesn't achieve max. Continue.
            lemma_last_max_scan(data, w, last_known, from + 1);
        }
    }
}

// --- X.13: Rightmost Gen-Inv pair (suffix strictly below max) ---

/// Find a Gen-Inv pair where the Inv is at the LAST max position.
/// Everything after the Inv is strictly below max → suffix is G₁.
proof fn lemma_rightmost_gen_inv(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        has_stable_letter(data, w),
        net_level(data, w) == 0,
        max_prefix_level(data, w) >= 1,
    ensures
        exists|i: int, j: int|
            has_adjacent_opposite_at(data, w, i, j)
            && w[i] == Symbol::Gen(data.base.num_generators)
            && w[j] == Symbol::Inv(data.base.num_generators)
            && net_level(data, w.subrange(0, i + 1)) == max_prefix_level(data, w)
            && (forall|k: int| j < k <= w.len()
                ==> net_level(data, w.subrange(0, k)) < max_prefix_level(data, w)),
{
    let ng = data.base.num_generators;
    let max_lev = max_prefix_level(data, w);

    // Step 1: Find ANY Gen-Inv pair at max level (leftmost)
    lemma_gen_inv_pair_when_max_ge_1(data, w);
    let first_i: int = choose|i: int|
        #[trigger] w[i] == Symbol::Gen(ng)
        && exists|j: int| has_adjacent_opposite_at(data, w, i, j)
            && w[j] == Symbol::Inv(ng)
            && net_level(data, w.subrange(0, i + 1)) == max_lev;
    let first_j: int = choose|j: int|
        #[trigger] w[j] == Symbol::Inv(ng)
        && has_adjacent_opposite_at(data, w, first_i, j)
        && net_level(data, w.subrange(0, first_i + 1)) == max_lev;

    // Step 2: first_i + 1 achieves max. Find the LAST position achieving max.
    assert(net_level(data, w.subrange(0, first_i + 1)) == max_lev);
    lemma_last_max_position(data, w, first_i + 1);
    let last_k: int = choose|k: int|
        #![trigger w.subrange(0, k)]
        first_i + 1 <= k <= w.len()
        && net_level(data, w.subrange(0, k)) == max_lev
        && (forall|k2: int| k < k2 <= w.len()
            ==> net_level(data, w.subrange(0, k2)) < max_lev);

    // Step 3: At last_k, the level = max. At last_k + 1, level < max.
    // So w[last_k] contributed < 0, i.e., w[last_k] = Inv(ng) (going from max to max-1).
    // Wait: last_k is the LAST position where prefix level = max.
    // The position last_k has net_level(w[0..last_k]) = max.
    // Position last_k + 1 (if exists) has net_level < max.
    // Contribution of w[last_k] = net(w[0..last_k+1]) - net(w[0..last_k]) = (< max) - max < 0.
    // So w[last_k] = Inv(ng).
    // But last_k could = w.len() (if net(w) = max).
    // Since net(w) = 0 < max ≥ 1: last_k < w.len().
    assert(last_k < w.len()) by {
        assert(w.subrange(0, w.len() as int) =~= w);
    }

    // w[last_k] = Inv (contribution = net(w[0..last_k+1]) - max < 0)
    let prev_word = w.subrange(0, last_k);
    let next_word = w.subrange(0, last_k + 1);
    assert(next_word =~= concat(prev_word, Seq::new(1, |_j: int| w[last_k])));
    lemma_net_level_concat(data, prev_word, Seq::new(1, |_j: int| w[last_k]));
    lemma_net_level_single(data, w[last_k]);
    // net(next) = max + contribution. net(next) < max. So contribution < 0 → = -1 → Inv.
    assert(w[last_k] == Symbol::Inv(ng));

    // Step 4: Find the Gen that entered max before last_k.
    // The level at last_k is max. Going left: find where it first rose to max.
    // From last_k: level = max. last_k - 1: level might be max (plateau).
    // Keep going left until level < max. That position + 1 was the Gen.
    // Use forward scan from position 1 to last_k.
    assert(net_level(data, w.subrange(0, 0int)) < max_lev) by {
        assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
    }
    lemma_find_gen_inv_forward(data, w, 1, last_k);

    // This gives a Gen-Inv pair (gen_pos, inv_pos) where:
    // - gen_pos < inv_pos ≤ last_k (from forward scan up to last_k)
    // - net_level(w[0..gen_pos+1]) = max
    // - w[gen_pos] = Gen, w[inv_pos] = Inv
    // But we need the Inv at last_k specifically for the suffix property.
    //
    // Actually: the forward scan finds a pair (i, j) with j ≤ w.len() (any Inv after Gen).
    // It might find j < last_k. We need j such that after j, levels < max.
    //
    // Better: use last_k directly as the Inv position. We know w[last_k] = Inv.
    // We need a Gen before last_k such that between them only base symbols.
    // This is the Gen that first reached max level before last_k.
    //
    // Actually, the positions between first_i+1 and last_k are all at level max
    // (they're between two max-achieving positions with no drop below max...
    // wait, that's not necessarily true. There could be drops between first_i+1 and last_k.)
    //
    // Hmm. Let me just use the Gen-Inv pair from the forward scan.
    // The pair (i, j) has net(w[0..i+1]) = max and all symbols between i and j are base.
    // After j: the level drops. But does it come back to max later?
    // If j < last_k: yes, it does (last_k achieves max again).
    // In that case: the suffix after j is NOT strictly below max.
    //
    // So I need to find the Gen-Inv pair ending AT last_k.
    // This means: the Gen before last_k, at the max plateau,
    // with all base symbols between them.
    //
    // last_k: net = max, w[last_k] = Inv.
    // last_k - 1: if net = max → base symbol (contribution 0). Part of plateau.
    //             if net < max → Gen (contribution +1 to reach max).
    // Scan left from last_k to find where the plateau started.
    // The position just before the plateau is at level max - 1 and has Gen.

    // Let me scan left from last_k.
    lemma_find_gen_before_last_inv(data, w, last_k);
}

/// Find the Gen entering the max-level plateau that ends at `inv_pos`.
proof fn lemma_find_gen_before_last_inv(data: HNNData, w: Word, inv_pos: int)
    requires
        hnn_data_valid(data),
        0 < inv_pos < w.len(),
        max_prefix_level(data, w) >= 1,
        net_level(data, w.subrange(0, inv_pos)) == max_prefix_level(data, w),
        w[inv_pos] == Symbol::Inv(data.base.num_generators),
        // Everything after inv_pos is strictly below max
        forall|k: int| inv_pos < k <= w.len()
            ==> net_level(data, w.subrange(0, k)) < max_prefix_level(data, w),
    ensures
        exists|i: int, j: int|
            has_adjacent_opposite_at(data, w, i, j)
            && w[i] == Symbol::Gen(data.base.num_generators)
            && w[j] == Symbol::Inv(data.base.num_generators)
            && net_level(data, w.subrange(0, i + 1)) == max_prefix_level(data, w)
            && (forall|k: int| j < k <= w.len()
                ==> net_level(data, w.subrange(0, k)) < max_prefix_level(data, w)),
    decreases inv_pos,
{
    let ng = data.base.num_generators;
    let max_lev = max_prefix_level(data, w);
    lemma_max_prefix_bounds(data, w, inv_pos - 1);

    // net(w[0..inv_pos - 1]) vs max
    if net_level(data, w.subrange(0, inv_pos - 1)) < max_lev {
        // inv_pos - 1 is below max. So w[inv_pos - 1] brought us to max.
        // Contribution = max - (< max) ≥ 1 → = 1 → w[inv_pos - 1] = Gen.
        let prev = w.subrange(0, inv_pos - 1);
        let curr = w.subrange(0, inv_pos);
        assert(curr =~= concat(prev, Seq::new(1, |_j: int| w[inv_pos - 1])));
        lemma_net_level_concat(data, prev, Seq::new(1, |_j: int| w[inv_pos - 1]));
        lemma_net_level_single(data, w[inv_pos - 1]);
        assert(w[inv_pos - 1] == Symbol::Gen(ng));

        // The pair is (inv_pos - 1, inv_pos): Gen followed immediately by Inv.
        // No base symbols between. This IS a valid adjacent opposite pair.
        // has_adjacent_opposite_at: no symbols between (j = i + 1).
        assert(has_adjacent_opposite_at(data, w, inv_pos - 1, inv_pos));
        // net_level(w[0..(inv_pos-1)+1]) = net(w[0..inv_pos]) = max. ✓
        assert(w.subrange(0, (inv_pos - 1) + 1) =~= w.subrange(0, inv_pos));
        // Suffix property: forall k > inv_pos: already in our requires. ✓
    } else {
        // inv_pos - 1 also at max. w[inv_pos - 1] has contribution 0 → base symbol.
        let prev = w.subrange(0, inv_pos - 1);
        let curr = w.subrange(0, inv_pos);
        assert(curr =~= concat(prev, Seq::new(1, |_j: int| w[inv_pos - 1])));
        lemma_net_level_concat(data, prev, Seq::new(1, |_j: int| w[inv_pos - 1]));
        lemma_net_level_single(data, w[inv_pos - 1]);
        // contribution = max - max = 0 → base symbol (not stable)
        assert(!is_stable(data, w[inv_pos - 1]));

        // Find the Inv that ENTERS this plateau segment.
        // The plateau extends from inv_pos back to some earlier position.
        // At the start of the plateau: a Gen entered from level max-1.
        // We need an Inv at the end of the plateau → that's our inv_pos.
        // But there might be earlier Inv's within the plateau? No:
        // within the plateau, all symbols have contribution 0 → base symbols.
        // Inv has contribution -1 ≠ 0. So inv_pos is the only Inv in the plateau.

        // The Gen entering the plateau is somewhere before inv_pos - 1.
        // Recurse: look for the Gen before this base-symbol plateau.
        if inv_pos == 1 {
            // inv_pos - 1 = 0, net(w[0..0]) = 0. For this = max ≥ 1: impossible.
            assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
        } else {
            // Find the Gen-Inv pair where the Inv is at inv_pos and the Gen
            // is wherever the level first rose to max in this plateau.
            // The plateau: positions from some start_pos to inv_pos-1, all at max.
            // The Gen is at start_pos - 1 (contribution +1 → level from max-1 to max).
            // And the pair is (start_pos - 1, inv_pos) with all base between.
            // Everything between start_pos and inv_pos - 1 is at max → base → non-stable. ✓

            // To find this: recurse leftward, maintaining that all positions from
            // inv_pos - 1 down to the current position are at max (base symbols).
            lemma_find_plateau_gen(data, w, inv_pos - 1, inv_pos);
        }
    }
}

/// Scan left through a max-level plateau to find the Gen that entered it.
proof fn lemma_find_plateau_gen(data: HNNData, w: Word, pos: int, inv_pos: int)
    requires
        hnn_data_valid(data),
        0 < pos < inv_pos < w.len(),
        max_prefix_level(data, w) >= 1,
        net_level(data, w.subrange(0, pos)) == max_prefix_level(data, w),
        w[inv_pos] == Symbol::Inv(data.base.num_generators),
        net_level(data, w.subrange(0, inv_pos)) == max_prefix_level(data, w),
        // All symbols from pos to inv_pos-1 are base (non-stable)
        forall|k: int| pos <= k < inv_pos ==> !is_stable(data, #[trigger] w[k]),
        // Everything after inv_pos is strictly below max
        forall|k: int| inv_pos < k <= w.len()
            ==> net_level(data, w.subrange(0, k)) < max_prefix_level(data, w),
    ensures
        exists|i: int, j: int|
            has_adjacent_opposite_at(data, w, i, j)
            && w[i] == Symbol::Gen(data.base.num_generators)
            && w[j] == Symbol::Inv(data.base.num_generators)
            && net_level(data, w.subrange(0, i + 1)) == max_prefix_level(data, w)
            && (forall|k: int| j < k <= w.len()
                ==> net_level(data, w.subrange(0, k)) < max_prefix_level(data, w)),
    decreases pos,
{
    let ng = data.base.num_generators;
    let max_lev = max_prefix_level(data, w);
    lemma_max_prefix_bounds(data, w, pos - 1);

    if net_level(data, w.subrange(0, pos - 1)) < max_lev {
        // Found the Gen! w[pos-1] contributed +1 to reach max.
        let prev = w.subrange(0, pos - 1);
        let curr = w.subrange(0, pos);
        assert(curr =~= concat(prev, Seq::new(1, |_j: int| w[pos - 1])));
        lemma_net_level_concat(data, prev, Seq::new(1, |_j: int| w[pos - 1]));
        lemma_net_level_single(data, w[pos - 1]);
        assert(w[pos - 1] == Symbol::Gen(ng));

        // The pair is (pos-1, inv_pos).
        // Between them (pos to inv_pos-1): all base (from our requires).
        // Also w[pos-1] = Gen (stable) is not in the "between" range.
        assert(has_adjacent_opposite_at(data, w, pos - 1, inv_pos));
        assert(w.subrange(0, (pos - 1) + 1) =~= w.subrange(0, pos));
    } else {
        // pos-1 also at max. Contribution = 0 → base symbol.
        let prev = w.subrange(0, pos - 1);
        let curr = w.subrange(0, pos);
        assert(curr =~= concat(prev, Seq::new(1, |_j: int| w[pos - 1])));
        lemma_net_level_concat(data, prev, Seq::new(1, |_j: int| w[pos - 1]));
        lemma_net_level_single(data, w[pos - 1]);
        assert(!is_stable(data, w[pos - 1]));

        if pos == 1 {
            assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
            // net(w[0..0]) = 0 = max ≥ 1. Contradiction.
        } else {
            // Extend the plateau and recurse.
            assert forall|k: int| pos - 1 <= k < inv_pos
                implies !is_stable(data, #[trigger] w[k])
            by {
                if k >= pos {} // from requires
                else { assert(k == pos - 1); }
            }
            lemma_find_plateau_gen(data, w, pos - 1, inv_pos);
        }
    }
}

// --- X.14: Tower setup for the rightmost Gen-Inv pair ---

/// Set up tower at the max level, get translate ≡ ε, return (bl, pair_level).
proof fn lemma_tower_setup(data: HNNData, w: Word) -> (result: (nat, nat))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, hnn_presentation(data).num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
        net_level(data, w) == 0,
        max_prefix_level(data, w) >= 1,
    ensures ({
        let (bl, pl) = result;
        let tw = translate_word_at(data, w, bl as int);
        &&& pl >= 1
        &&& pl == (bl + max_prefix_level(data, w)) as nat
        &&& bl >= w.len()
        &&& tower_textbook_chain(data, pl)
        &&& word_valid(tw, tower_presentation(data, pl).num_generators)
        &&& equiv_in_presentation(tower_presentation(data, pl), tw, empty_word())
    }),
{
    let hp = hnn_presentation(data);
    let ng = data.base.num_generators;
    let max_lev = max_prefix_level(data, w);

    let d: Derivation = choose|d: Derivation|
        derivation_valid(hp, d, w, empty_word());
    let min_adj = derivation_min_adj_level(data, d.steps, w);
    let max_step = derivation_max_step_level(data, d.steps, w);
    let bl_deriv: nat = if min_adj >= 0 { 0 } else { (-min_adj) as nat };
    let max_step_abs: nat = if max_step >= 0 { max_step as nat } else { (-max_step) as nat };

    let bl: nat = (w.len() + bl_deriv) as nat;
    let m: nat = (bl + w.len() as nat + max_step_abs + 1) as nat;
    let pl: nat = (bl + max_lev) as nat;

    assert(bl as int >= -(min_adj));
    assert(m as int >= max_step + bl as int);
    assert(word_valid(w, hp.num_generators)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies symbol_valid(#[trigger] w[k], hp.num_generators) by {}
    }

    lemma_derivation_levels_ok_from_bounds(data, m, bl as int, d.steps, w);
    lemma_hnn_derivation_to_tower_equiv(data, m, bl as int, d.steps, w, empty_word());
    lemma_translate_empty_at(data, bl as int);
    lemma_tower_textbook_chain_from_hnn_iso(data, m);

    // tw valid for tower(pl)
    assert forall|k: int| #![trigger w.subrange(0, k)]
        0 <= k <= w.len() ==>
        0 <= bl as int + net_level(data, w.subrange(0, k)) <= pl as int
    by {
        if 0 <= k && k <= w.len() {
            lemma_prefix_level_bounded_by_k(data, w, k);
            lemma_max_prefix_bounds(data, w, k);
        }
    }
    lemma_translate_word_valid_for_level(data, w, bl as int, pl);

    // Peel to tower(pl)
    assert(pl <= m) by {
        lemma_max_prefix_achieved(data, w);
        let kk: int = choose|k: int| 0 <= k <= w.len()
            && net_level(data, w.subrange(0, k)) == max_lev;
        lemma_prefix_level_bounded_by_k(data, w, kk);
    }
    lemma_tower_injectivity_peel(data, pl, m, translate_word_at(data, w, bl as int));

    (bl, pl)
}


// --- X.15: Suffix level bound ---

/// Key lemma: the suffix of w after a concat split has net_level equal to
/// the difference of the full word's prefix levels.
/// Specifically: if w = w1 · w2, then net_level(w2[0..k]) = net_level(w[0..w1.len()+k]) - net_level(w1).
proof fn lemma_suffix_net_level(data: HNNData, w: Word, split: int, k: int)
    requires
        0 <= split <= w.len(),
        0 <= k <= w.len() - split,
    ensures
        net_level(data, w.subrange(split, split + k))
            == net_level(data, w.subrange(0, split + k))
                - net_level(data, w.subrange(0, split)),
{
    let prefix = w.subrange(0, split);
    let suffix_k = w.subrange(split, split + k);
    let full = w.subrange(0, split + k);
    assert(full =~= concat(prefix, suffix_k)) by {
        assert(full.len() == prefix.len() + suffix_k.len());
        assert forall|i: int| 0 <= i < full.len()
            implies full[i] == concat(prefix, suffix_k)[i]
        by {
            if i < split {} else { assert(suffix_k[i - split] == w[i]); }
        }
    }
    lemma_net_level_concat(data, prefix, suffix_k);
}

// --- X.16: Suffix is G₁ at the top junction ---

/// The suffix w[split..] has all shifted running levels ≤ junc (strictly < pair_level).
/// Stated in terms of w.subrange to avoid =~= issues with net_level.
proof fn lemma_suffix_levels_bounded(
    data: HNNData, w: Word, split: int, bl: int, pl: nat,
)
    requires
        hnn_data_valid(data),
        0 <= split <= w.len(),
        bl >= 0,
        pl >= 1,
        pl == (bl + max_prefix_level(data, w)) as nat,
        forall|k: int| split <= k <= w.len()
            ==> net_level(data, w.subrange(0, k)) < max_prefix_level(data, w),
        bl + net_level(data, w.subrange(0, split)) <= (pl - 1) as int,
        bl >= w.len(),
    ensures
        // All shifted levels of suffix positions are in [0, junc]
        forall|k: int| #![trigger w.subrange(0, split + k)]
            0 <= k <= w.len() - split ==>
            0 <= bl + net_level(data, w.subrange(0, split + k)) <= (pl - 1) as int,
{
    assert forall|k: int| #![trigger w.subrange(0, split + k)]
        0 <= k <= w.len() - split ==>
        0 <= bl + net_level(data, w.subrange(0, split + k)) <= (pl - 1) as int
    by {
        if 0 <= k && k <= w.len() - split {
            lemma_prefix_level_bounded_by_k(data, w, split + k);
            // bl ≥ w.len() ≥ split + k, so bl + net_level ≥ bl - (split+k) ≥ 0
            // net_level(w[0..split+k]) < max (from requires, since split+k ≥ split)
            // bl + net_level < bl + max = pl → ≤ pl - 1 = junc
        }
    }
}

// --- X.17: Small helpers for the action chain ---

/// The Gen·base·Inv segment has net_level 0, so the level after pair_j+1
/// returns to prefix_level.
proof fn lemma_pair_net_level_return(
    data: HNNData, w: Word, pair_i: int, pair_j: int,
)
    requires
        hnn_data_valid(data),
        word_valid(w, hnn_presentation(data).num_generators),
        has_adjacent_opposite_at(data, w, pair_i, pair_j),
        w[pair_i] == Symbol::Gen(data.base.num_generators),
        w[pair_j] == Symbol::Inv(data.base.num_generators),
        net_level(data, w.subrange(0, pair_i + 1)) == max_prefix_level(data, w),
    ensures
        net_level(data, w.subrange(0, pair_j + 1))
            == net_level(data, w.subrange(0, pair_i)),
{
    let ng = data.base.num_generators;
    // net(w[0..pair_j+1]) = net(w[0..pair_i]) + net(w[pair_i..pair_j+1])
    // net(w[pair_i..pair_j+1]) = net([Gen]) + net(base) + net([Inv]) = 1 + 0 + (-1) = 0
    // So net(w[0..pair_j+1]) = net(w[0..pair_i]) = prefix_level.
    lemma_suffix_net_level(data, w, pair_i, pair_j + 1 - pair_i);
    // net(w.subrange(pair_i, pair_j+1)) = net(w[0..pair_j+1]) - net(w[0..pair_i])
    // We need net(w.subrange(pair_i, pair_j+1)) = 0.
    // The subrange pair_i..pair_j+1 contains Gen at pair_i, base, Inv at pair_j.
    // Each non-stable symbol between pair_i+1 and pair_j-1 contributes 0.
    // Gen contributes +1, Inv contributes -1. Base contributes 0.
    // Total contribution: 1 + 0 + (-1) = 0.
    // Express this via subrange decompositions:
    lemma_suffix_net_level(data, w, pair_i, 1);
    // net(w.subrange(pair_i, pair_i+1)) = net(w[0..pair_i+1]) - net(w[0..pair_i])
    //   = max_prefix_level - prefix_level = 1  (since max = prefix_level + 1 from requires)
    lemma_suffix_net_level(data, w, pair_i + 1, pair_j - pair_i - 1);
    // net(w.subrange(pair_i+1, pair_j)) = net(w[0..pair_j]) - net(w[0..pair_i+1])
    // = net(w[0..pair_j]) - max_prefix_level

    // Base word between pair: all non-stable.
    // net of base word = 0 (from lemma_net_level_no_stable on the base word)
    let base_word = w.subrange(pair_i + 1, pair_j);
    assert forall|k: int| 0 <= k < base_word.len()
        implies !is_stable(data, #[trigger] base_word[k])
    by {
        assert(base_word[k] == w[pair_i + 1 + k]);
    }
    lemma_net_level_no_stable(data, base_word, 0);

    // net(w.subrange(pair_i+1, pair_j)) = 0 (same as base_word)
    assert(w.subrange(pair_i + 1, pair_j) =~= base_word);

    // Now: net(w.subrange(pair_i, pair_j+1)) = 1 + 0 + (-1) = 0
    // Using: net(w.subrange(pair_i, pair_j+1))
    //   = net(w[0..pair_j+1]) - net(w[0..pair_i]) (from suffix_net_level)
    // And: net(w[0..pair_j+1]) = net(w[0..pair_i]) + 0 = net(w[0..pair_i])
    // So we need to show net(w[0..pair_j+1]) = net(w[0..pair_i]).
    // From suffix_net_level: net(w.subrange(pair_i, pair_j+1)) = net(w[0..pair_j+1]) - prefix_level.
    // If we can show net(w.subrange(pair_i, pair_j+1)) = 0: then net(w[0..pair_j+1]) = prefix_level. ✓

    // Show net(w.subrange(pair_i, pair_j+1)) = 0 by decomposing it:
    // w.subrange(pair_i, pair_j+1) = [w[pair_i]] ++ base_word ++ [w[pair_j]]
    let gen_s: Word = Seq::new(1, |_j: int| w[pair_i]);
    let inv_s: Word = Seq::new(1, |_j: int| w[pair_j]);
    let mid = w.subrange(pair_i, pair_j + 1);
    assert(mid =~= concat(gen_s, concat(base_word, inv_s))) by {
        assert(mid.len() == gen_s.len() + base_word.len() + inv_s.len());
        assert forall|k: int| 0 <= k < mid.len()
            implies mid[k] == concat(gen_s, concat(base_word, inv_s))[k]
        by {
            if k == 0 {} else if k < pair_j - pair_i { assert(mid[k] == base_word[k - 1]); }
            else {}
        }
    }
    lemma_net_level_concat(data, gen_s, concat(base_word, inv_s));
    lemma_net_level_single(data, w[pair_i]);
    lemma_net_level_concat(data, base_word, inv_s);
    lemma_net_level_single(data, w[pair_j]);
    // net(mid) = 1 + 0 + (-1) = 0
}

/// The suffix w[pair_j+1..] translates to a G₁ word at junction junc↔pl.
/// Uses: suffix levels < max → translate valid for tower(junc).
proof fn lemma_suffix_translate_g1(
    data: HNNData, w: Word, pair_i: int, pair_j: int, bl: nat, pl: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, hnn_presentation(data).num_generators),
        has_adjacent_opposite_at(data, w, pair_i, pair_j),
        w[pair_i] == Symbol::Gen(data.base.num_generators),
        w[pair_j] == Symbol::Inv(data.base.num_generators),
        net_level(data, w.subrange(0, pair_i + 1)) == max_prefix_level(data, w),
        max_prefix_level(data, w) >= 1,
        forall|k: int| pair_j < k <= w.len()
            ==> net_level(data, w.subrange(0, k)) < max_prefix_level(data, w),
        net_level(data, w.subrange(0, pair_j + 1))
            == net_level(data, w.subrange(0, pair_i)),
        pl >= 1,
        pl == (bl + max_prefix_level(data, w)) as nat,
        bl >= w.len(),
    ensures ({
        let junc = (pl - 1) as nat;
        let prefix_level = net_level(data, w.subrange(0, pair_i));
        let w_suffix = w.subrange(pair_j + 1, w.len() as int);
        let tw_suffix = translate_word_at(data, w_suffix, bl as int + prefix_level);
        word_valid(tw_suffix, tower_presentation(data, junc).num_generators)
    }),
{
    let ng = data.base.num_generators;
    let junc = (pl - 1) as nat;
    let prefix_level = net_level(data, w.subrange(0, pair_i));
    let w_suffix = w.subrange(pair_j + 1, w.len() as int);

    // Suffix word_valid for HNN pres
    assert(word_valid(w_suffix, hnn_presentation(data).num_generators)) by {
        assert forall|k: int| 0 <= k < w_suffix.len()
            implies symbol_valid(#[trigger] w_suffix[k], hnn_presentation(data).num_generators)
        by { assert(w_suffix[k] == w[pair_j + 1 + k]); }
    }

    // Suffix running levels bounded: use lemma_suffix_levels_bounded
    // Need: pair_j + 1 as split point, bl + prefix_level as shifted level at split
    // bl + net_level(w[0..pair_j+1]) = bl + prefix_level = junc (from pair_net_level_return)
    lemma_suffix_levels_bounded(data, w, pair_j + 1, bl as int, pl);

    // Connect suffix subrange levels to translate validity
    assert forall|k: int| #![trigger w_suffix.subrange(0, k)]
        0 <= k <= w_suffix.len() ==>
        0 <= (bl as int + prefix_level) + net_level(data, w_suffix.subrange(0, k)) <= junc as int
    by {
        if 0 <= k && k <= w_suffix.len() {
            assert(w_suffix.subrange(0, k) =~= w.subrange(pair_j + 1, pair_j + 1 + k)) by {
                assert forall|i: int| 0 <= i < k
                    implies w_suffix.subrange(0, k)[i] == w.subrange(pair_j + 1, pair_j + 1 + k)[i]
                by {}
            }
            lemma_suffix_net_level(data, w, pair_j + 1, k);
            lemma_prefix_level_bounded_by_k(data, w, pair_j + 1 + k);
        }
    }
    lemma_translate_word_valid_for_level(data, w_suffix, bl as int + prefix_level, junc);
}

/// Decompose translate(w) = tw_prefix · tw_g2 · tw_suffix at the Gen-Inv pair.
proof fn lemma_translate_decompose_at_pair(
    data: HNNData, w: Word, pair_i: int, pair_j: int, bl: int,
)
    requires
        hnn_data_valid(data),
        word_valid(w, hnn_presentation(data).num_generators),
        has_adjacent_opposite_at(data, w, pair_i, pair_j),
        w[pair_i] == Symbol::Gen(data.base.num_generators),
        w[pair_j] == Symbol::Inv(data.base.num_generators),
        bl >= w.len() as int,
    ensures ({
        let ng = data.base.num_generators;
        let prefix_level = net_level(data, w.subrange(0, pair_i));
        let base_word = w.subrange(pair_i + 1, pair_j);
        let tw = translate_word_at(data, w, bl);
        let tw_prefix = translate_word_at(data, w.subrange(0, pair_i), bl);
        let tw_g2 = shift_word(base_word, ((bl + prefix_level + 1) * ng) as nat);
        let tw_suffix = translate_word_at(data, w.subrange(pair_j + 1, w.len() as int),
            bl + prefix_level);
        &&& word_valid(base_word, ng)
        &&& tw =~= concat(tw_prefix, concat(tw_g2, tw_suffix))
    }),
{
    let ng = data.base.num_generators;
    let prefix_level = net_level(data, w.subrange(0, pair_i));
    let base_word = w.subrange(pair_i + 1, pair_j);
    let w_prefix = w.subrange(0, pair_i);
    let w_suffix = w.subrange(pair_j + 1, w.len() as int);

    // base_word valid
    assert(word_valid(base_word, ng)) by {
        assert forall|k: int| 0 <= k < base_word.len()
            implies symbol_valid(#[trigger] base_word[k], ng)
        by {
            assert(base_word[k] == w[pair_i + 1 + k]);
            assert(!is_stable(data, w[pair_i + 1 + k]));
            match w[pair_i + 1 + k] {
                Symbol::Gen(idx) => { assert(idx < ng); }
                Symbol::Inv(idx) => { assert(idx < ng); }
            }
        }
    }

    // Gen·base·Inv segment
    let gen_base_inv = concat(Seq::new(1, |_j: int| Symbol::Gen(ng)),
        concat(base_word, Seq::new(1, |_j: int| Symbol::Inv(ng))));

    // Net levels for the segment
    lemma_net_level_concat(data, Seq::new(1, |_j: int| Symbol::Gen(ng)),
        concat(base_word, Seq::new(1, |_j: int| Symbol::Inv(ng))));
    lemma_net_level_single(data, Symbol::Gen(ng));
    lemma_net_level_concat(data, base_word, Seq::new(1, |_j: int| Symbol::Inv(ng)));
    lemma_net_level_single(data, Symbol::Inv(ng));
    lemma_net_level_base_word(data, base_word);
    // net_level(gen_base_inv) = 0

    // w = w_prefix · gen_base_inv · w_suffix
    assert(w =~= concat(w_prefix, concat(gen_base_inv, w_suffix))) by {
        assert forall|k: int| 0 <= k < w.len()
            implies w[k] == concat(w_prefix, concat(gen_base_inv, w_suffix))[k]
        by {
            if k < pair_i {} else if k == pair_i {}
            else if k < pair_j { assert(w[k] == base_word[k - pair_i - 1]); }
            else if k == pair_j {} else { assert(w[k] == w_suffix[k - pair_j - 1]); }
        }
    }

    // bl + prefix_level >= 0 (since bl >= 0 and prefix_level >= -bl from level bounds)
    assert(bl + prefix_level >= 0) by {
        lemma_prefix_level_bounded_by_k(data, w, pair_i);
    }

    // Translate distributes
    lemma_translate_concat(data, w_prefix, concat(gen_base_inv, w_suffix), bl);
    lemma_translate_concat(data, gen_base_inv, w_suffix, bl + prefix_level);
    lemma_translate_gen_base_inv(data, base_word, bl + prefix_level);
}

/// G₂ one-shot on the base word creates a right syllable when starting
/// from a state with right_count = 0 (left-topped or empty).
/// base_word ∉ B (from no-pinch) → product ∉ B → rep ≠ ε → prepend.
proof fn lemma_g2_creates_right_syllable(
    data: HNNData, base_word: Word,
    afp: AmalgamatedData, h: Word, syls: Seq<crate::normal_form_afp_textbook::Syllable>,
)
    requires
        hnn_data_valid(data),
        amalgamated_data_valid(afp),
        presentation_valid(afp.p1),
        presentation_valid(afp.p2),
        crate::normal_form_amalgamated::identifications_isomorphic(afp),
        crate::normal_form_afp_textbook::action_preserves_canonical(afp),
        crate::normal_form_afp_textbook::is_canonical_state(afp, h, syls),
        word_valid(base_word, afp.p2.num_generators),
        // base_word ∉ B (in the AFP's B-subgroup)
        !crate::normal_form_amalgamated::in_right_subgroup(afp, base_word),
        // State has right_count = 0
        right_syllable_count(syls) == 0,
        // b_words are valid
        forall|i: int| 0 <= i < crate::normal_form_afp_textbook::b_words(afp).len()
            ==> word_valid(
                #[trigger] crate::normal_form_afp_textbook::b_words(afp)[i],
                afp.p2.num_generators),
        // K-size and h valid
        word_valid(h, crate::normal_form_afp_textbook::k_size(afp)),
    ensures ({
        use crate::normal_form_afp_textbook::*;
        let tw_g2 = shift_word(base_word, afp.p1.num_generators);
        right_syllable_count(
            act_word(afp, tw_g2, h, syls).1) >= 1
    }),
{
    use crate::normal_form_afp_textbook::*;

    // G₂ one-shot
    lemma_act_word_eq_g2_one_shot(afp, base_word, h, syls);
    let product = concat(base_word, apply_embedding(b_words(afp), h));
    let result = g2_one_shot_action(afp, product, syls);

    // product ∉ B (from base_word ∉ B + embed_b(h) ∈ B + right-cancel)
    lemma_not_in_subgroup_concat_embed_b(afp, base_word, h);
    // product is word_valid for p2
    lemma_apply_embedding_valid(b_words(afp), h, afp.p2.num_generators);
    crate::word::lemma_concat_word_valid(
        base_word, apply_embedding(b_words(afp), h), afp.p2.num_generators);
    // So rep ≠ ε
    lemma_not_in_right_subgroup_rep_nonempty(afp, product);
    let rep = b_rcoset_rep(afp, product);

    // right_count(syls) = 0 → syls empty or left-topped.
    // If empty: g2_one_shot case 2 → prepend right → right_count = 1
    // If left-topped: g2_one_shot case 2 → prepend right → right_count = 1
    // (Both go to the "prepend" branch since syls.len() == 0 || syls.first().is_left)

    // Need to show: syls.len() == 0 || syls.first().is_left
    // This follows from right_count(syls) = 0: if syls non-empty and first is right,
    // then right_count ≥ 1. Contradiction.
    if syls.len() > 0 && !syls.first().is_left {
        // syls.first() is right → right_count ≥ 1. But right_count = 0. Contradiction.
    }
    // So: syls.len() == 0 || syls.first().is_left ✓
    // g2_one_shot: rep ≠ ε and (empty or left-topped) → prepend right syllable
    // result = (h_new, [Syllable(false, rep)] ++ syls)
    // right_count of result = 1 + right_count(syls) = 1 + 0 = 1 ≥ 1. ✓
}

/// Case A helper part 1: tower + AFP + act = identity.
proof fn lemma_case_a_act_identity(data: HNNData, w: Word) -> (result: (nat, nat))
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, hnn_presentation(data).num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
        net_level(data, w) == 0,
        max_prefix_level(data, w) >= 1,
    ensures ({
        let (bl, pl) = result;
        let tw = translate_word_at(data, w, bl as int);
        let junc = (pl - 1) as nat;
        let afp = tower_afp_data(data, junc);
        let e = empty_word();
        let es = Seq::<crate::normal_form_afp_textbook::Syllable>::empty();
        &&& pl >= 1
        &&& pl == (bl + max_prefix_level(data, w)) as nat
        &&& bl >= w.len()
        &&& tower_textbook_chain(data, pl)
        &&& word_valid(tw, tower_presentation(data, pl).num_generators)
        &&& crate::normal_form_afp_textbook::act_word(afp, tw, e, es) == (e, es)
    }),
{
    use crate::normal_form_afp_textbook::*;
    let (bl, pl) = lemma_tower_setup(data, w);
    let tw = translate_word_at(data, w, bl as int);
    let junc = (pl - 1) as nat;
    let afp = tower_afp_data(data, junc);

    assert(tower_textbook_prereqs_at(data, junc));
    lemma_tower_afp_data_valid(data, junc);
    lemma_tower_valid(data, junc);
    reveal(presentation_valid);
    lemma_iso_implies_apc(afp);
    lemma_action_well_defined_proof(afp);
    lemma_identity_state_canonical(afp);

    let e_h = empty_word();
    let e_s = Seq::<Syllable>::empty();
    let d_tw: Derivation = choose|d: Derivation|
        derivation_valid(tower_presentation(data, pl), d, tw, empty_word());
    lemma_act_word_deriv(afp, d_tw.steps, tw, empty_word(), e_h, e_s);
    lemma_act_word_empty(afp, e_h, e_s);
    (bl, pl)
}

/// Case A helper part 2: decompose + G₂ one-shot + G₁ prefix → contradiction.
proof fn lemma_case_a_contradiction(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, hnn_presentation(data).num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
        !has_pinch(data, w),
        has_stable_letter(data, w),
        net_level(data, w) == 0,
        max_prefix_level(data, w) >= 1,
    ensures false,
{
    use crate::normal_form_afp_textbook::*;
    let ng = data.base.num_generators;
    let max_lev = max_prefix_level(data, w);

    // Part 1: tower + act = identity
    let (bl, pl) = lemma_case_a_act_identity(data, w);
    let tw = translate_word_at(data, w, bl as int);
    let junc = (pl - 1) as nat;
    let afp = tower_afp_data(data, junc);
    let e_h = empty_word();
    let e_s = Seq::<Syllable>::empty();

    // Part 2: find pair + decompose + chain
    lemma_gen_inv_pair_when_max_ge_1(data, w);
    let pair_i: int = choose|i: int|
        #[trigger] w[i] == Symbol::Gen(ng)
        && exists|j: int| has_adjacent_opposite_at(data, w, i, j)
            && w[j] == Symbol::Inv(ng)
            && net_level(data, w.subrange(0, i + 1)) == max_lev;
    let pair_j: int = choose|j: int|
        #[trigger] w[j] == Symbol::Inv(ng)
        && has_adjacent_opposite_at(data, w, pair_i, j)
        && net_level(data, w.subrange(0, pair_i + 1)) == max_lev;
    assert(!has_pinch_at(data, w, pair_i, pair_j));

    lemma_translate_decompose_at_pair(data, w, pair_i, pair_j, bl as int);
    lemma_pair_net_level_return(data, w, pair_i, pair_j);
    let prefix_level = net_level(data, w.subrange(0, pair_i));
    let base_word = w.subrange(pair_i + 1, pair_j);
    let tw_prefix = translate_word_at(data, w.subrange(0, pair_i), bl as int);
    let tw_g2 = shift_word(base_word, (pl * ng) as nat);
    let tw_suffix = translate_word_at(data,
        w.subrange(pair_j + 1, w.len() as int), bl as int + prefix_level);

    // Connect prefix_level + 1 = max_lev
    // From choose: net_level(w[0..pair_i+1]) = max_lev.
    // net_level(w[0..pair_i+1]) = prefix_level + 1 (Gen at pair_i contributes +1).
    assert(prefix_level + 1 == max_lev) by {
        let pw = w.subrange(0, pair_i);
        let gw: Word = Seq::new(1, |_j: int| w[pair_i]);
        assert(w.subrange(0, pair_i + 1) =~= concat(pw, gw)) by {
            assert forall|k: int| 0 <= k < (pair_i + 1)
                implies w.subrange(0, pair_i + 1)[k] == concat(pw, gw)[k]
            by { if k < pair_i {} else {} }
        }
        lemma_net_level_concat(data, pw, gw);
        lemma_net_level_single(data, w[pair_i]);
    }
    assert(bl as int + prefix_level + 1 == pl as int);
    assert(tw =~= concat(tw_prefix, concat(tw_g2, tw_suffix)));

    // Chain action via separate helper to stay under rlimit
    lemma_case_a_chain(data, w, pair_i, pair_j, bl, pl);
}

/// Case A final chain: split action, apply G₂ one-shot, apply G₁ prefix preservation.
proof fn lemma_case_a_chain(
    data: HNNData, w: Word, pair_i: int, pair_j: int, bl: nat, pl: nat,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, hnn_presentation(data).num_generators),
        !has_pinch(data, w),
        has_adjacent_opposite_at(data, w, pair_i, pair_j),
        w[pair_i] == Symbol::Gen(data.base.num_generators),
        w[pair_j] == Symbol::Inv(data.base.num_generators),
        net_level(data, w.subrange(0, pair_i + 1)) == max_prefix_level(data, w),
        max_prefix_level(data, w) >= 1,
        pl >= 1,
        pl == (bl + max_prefix_level(data, w)) as nat,
        bl >= w.len(),
        tower_textbook_chain(data, pl),
        word_valid(translate_word_at(data, w, bl as int),
            tower_presentation(data, pl).num_generators),
        // act = identity
        crate::normal_form_afp_textbook::act_word(
            tower_afp_data(data, (pl - 1) as nat),
            translate_word_at(data, w, bl as int),
            empty_word(), Seq::<crate::normal_form_afp_textbook::Syllable>::empty())
            == (empty_word(), Seq::<crate::normal_form_afp_textbook::Syllable>::empty()),
        // Decomposition
        net_level(data, w.subrange(0, pair_i)) + 1 == max_prefix_level(data, w),
        translate_word_at(data, w, bl as int) =~= concat(
            translate_word_at(data, w.subrange(0, pair_i), bl as int),
            concat(
                shift_word(w.subrange(pair_i + 1, pair_j), (pl * data.base.num_generators) as nat),
                translate_word_at(data, w.subrange(pair_j + 1, w.len() as int),
                    bl as int + net_level(data, w.subrange(0, pair_i))))),
        word_valid(w.subrange(pair_i + 1, pair_j), data.base.num_generators),
    ensures false,
{
    use crate::normal_form_afp_textbook::*;
    let ng = data.base.num_generators;
    let junc = (pl - 1) as nat;
    let afp = tower_afp_data(data, junc);
    let e_h = empty_word();
    let e_s = Seq::<Syllable>::empty();
    let prefix_level = net_level(data, w.subrange(0, pair_i));
    let base_word = w.subrange(pair_i + 1, pair_j);
    let tw_prefix = translate_word_at(data, w.subrange(0, pair_i), bl as int);
    let tw_g2 = shift_word(base_word, (pl * ng) as nat);
    let tw_suffix = translate_word_at(data,
        w.subrange(pair_j + 1, w.len() as int), bl as int + prefix_level);
    let tw = translate_word_at(data, w, bl as int);

    // AFP prerequisites
    assert(tower_textbook_prereqs_at(data, junc));
    lemma_tower_afp_data_valid(data, junc);
    lemma_tower_valid(data, junc);
    lemma_tower_num_generators(data, junc);
    reveal(presentation_valid);
    lemma_iso_implies_apc(afp);
    lemma_identity_state_canonical(afp);

    // Split action: act(tw, ε, []) = act(tw_prefix, act(tw_g2, act(tw_suffix, ε, [])))
    lemma_act_word_concat(afp, tw_prefix, concat(tw_g2, tw_suffix), e_h, e_s);
    lemma_act_word_concat(afp, tw_g2, tw_suffix, e_h, e_s);

    // Suffix: act(tw_suffix, ε, []) has right_count = 0
    // (tw_suffix is at levels < pl → G₁ at this junction)
    // G₂ one-shot: creates right_count ≥ 1
    // Prefix: preserves right_count ≥ 1 (for single visit, prefix is G₁)

    // For now: the chain is set up. The remaining formal steps:
    // 1. Show base_word ∉ B at this junction (from ¬has_pinch_at)
    // 2. Call lemma_g2_creates_right_syllable
    // 3. Show tw_prefix is G₁ (from forward scan: prefix levels < max)
    // 4. Call lemma_act_g1_word_preserves_right_count on prefix
    // 5. Contradiction: right_count ≥ 1 but final = 0

    assert(false); // base∉B + G₂ one-shot + prefix G₁ + final chain
}

/// **Britton's Lemma (Full, Miller Thm 3.10):**
/// If w ≡ ε in G* and w has stable letters, then w has a pinch.
///
/// Proof outline (textbook permutation representation):
/// 1. net_level(w) = 0 (from w ≡ ε)
/// 2. Find rightmost Gen-Inv pair at max level (suffix strictly below max)
/// 3. Translate to tower, peel to pair_level, get act = (ε, [])
/// 4. Decompose: translate = tw_prefix · tw_g2 · tw_suffix
/// 5. G₁ suffix → right_count = 0
/// 6. G₂ one-shot → right_count = 1 (base ∉ B, top left/empty)
/// 7. Prefix preserves right_count ≥ 1
/// 8. Contradiction: right_count ≥ 1 but (ε, []) has right_count = 0
pub proof fn britton_lemma_full(
    data: HNNData, w: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, hnn_presentation(data).num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
        has_stable_letter(data, w),
    ensures
        has_pinch(data, w),
{
    if !has_pinch(data, w) {
        lemma_equiv_net_level_zero(data, w);

        let max_lev = max_prefix_level(data, w);
        lemma_max_prefix_bounds(data, w, 0);

        if max_lev >= 1 {
            // Case A: max ≥ 1 → contradiction via lemma_case_a_contradiction
            lemma_case_a_contradiction(data, w);
        } else {
            // Case B: max = 0. Use dual (Inv-Gen + left_count) argument.
            lemma_adjacent_opposite_exists(data, w);
            assert(false); // PLACEHOLDER: symmetric argument
        }
    }
}

} // verus!
