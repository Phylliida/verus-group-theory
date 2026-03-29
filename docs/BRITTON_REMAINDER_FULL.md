# Britton's Lemma Formalization — Complete Reference

## Overview

This document describes the state of the Britton's Lemma formalization in `verus-group-theory`.

**Active file:** `britton_via_tower.rs` — the AFP injectivity + tower construction approach (Lyndon-Schupp Ch. IV).

---

## Two Theorems

### Britton's Lemma (Standard Form)

**Statement:** If `w` is a base word (no stable letters) and `w = 1` in the HNN extension `G*`, then `w = 1` in the base group `G`.

**Status:** ✅ **`britton_lemma_unconditional`** in `britton_via_tower.rs` (line 2203) — **FULLY PROVED.** No extra preconditions beyond `hnn_data_valid` and `hnn_associations_isomorphic`.

### Britton's Lemma (Stronger / Pinch Form)

**Statement (Miller Thm 3.10):** If `w` involves stable letters and `w = 1` in `G*`, then `w` has a pinch (a subword `t⁻¹·a·t` or `t·b·t⁻¹` where `a ∈ A` or `b ∈ B`).

**Status:** ❌ **`britton_lemma_full`** in `britton_via_tower.rs` (line 5911) — **2 `assert(false)` placeholders** at lines 5931 and 5935.

---

## Architecture of `britton_via_tower.rs`

| Part | Lines | Content |
|------|-------|---------|
| A | 1-200 | Basic HNN definitions, `net_level`, `stable_letter_count` |
| B | 201-500 | HNN presentation, relator, derived data |
| C | 501-800 | Derivation infrastructure |
| D | 801-1200 | Derivation step application |
| E | 1201-1600 | Level computation |
| F | 1601-2000 | AFP injectivity → tower |
| G | 2001-2400 | Tower construction |
| H | 2401-2800 | Tower embedding lemmas |
| I | 2801-3200 | Derivation translation |
| J | 3201-3600 | AFP injectivity + tower prerequisites |
| K | 3601-4000 | AFP normal form (from `normal_form_afp_textbook.rs`) |
| L | 4001-4400 | Tower AFP data |
| M | 4401-4800 | Right syllable count + length properties |
| N | 4801-5200 | AFP-level action: `textbook_g2_action`, `textbook_g1_action` |
| O | 5201-5600 | HNN-level action: `textbook_psi_p`, `textbook_psi_p_inv`, no-collapse |
| P | 5601-5873 | No-collapse proof — `lemma_p_reduced_no_collapse` |
| Q | 5874-5940 | **Well-definedness TODO** + `britton_lemma_full` |

---

## The Textbook Proof (Miller, Ch. IV, p.49)

### The Argument

Miller's proof of Theorem 3.10 (the pinch theorem) proceeds as follows:

1. **Define ψ(p) and ψ(p⁻¹) as permutations of Ω** (the set of normal forms), using the 3-case definitions.

2. **Routine check**: Show ψ(p)∘ψ(p⁻¹) = id and ψ(p⁻¹)∘ψ(p) = id on all states. This is case analysis on the 9 combinations (Verus: 4, from merged PREPEND).

3. **HNN relation**: From step 2, `ψ(p⁻¹)∘ψ(p) = id` on the coset rep, so `ψ(p⁻¹)∘θ(a)∘ψ(p) = θ(a)`. Thus `θ⋆ψ(p⁻¹ap) = θ(a)∘θ(b)⁻¹ = id` since `b = φ(a)`. The HNN relation acts trivially.

4. **Well-defined permutation representation**: Steps 1-3 give a well-defined homomorphism `θ⋆ψ: G* → Sym(Ω)`.

5. **Key lemma** (Miller p.49): For any **non-empty normal form** `w` with `m ≥ 1` stable letters, `θ⋆ψ(w)(∅)` is **never the empty syllable sequence**. The right-to-left processing gives exactly `m` syllables (each stable letter PREPENDs; COLLAPSE never triggers because there is no pinch).

6. **Contradiction**: If `w ≡ ε` in `G*` and `w` has stable letters but no pinch, then `w` is a normal form. By step 5, `θ⋆ψ(w)(∅)` is non-empty. But `w ≡ ε` implies the action fixes ∅. Contradiction. Therefore `w` has a pinch.

### The Direct Argument (no tower decomposition needed)

The contradiction in step 6 is **direct** — it does NOT use tower decomposition:

- `w ≡ ε` → by well-definedness, `textbook_act_hnn(w, ε, []) = (ε, [])` (empty syllables)
- `w` has no pinch → `lemma_p_reduced_no_collapse` → no COLLAPSE → `textbook_act_hnn(w, ε, [])` has exactly `stable_count(w) ≥ 1` syllables
- Contradiction

The tower decomposition is only needed for `britton_lemma_unconditional` (the base word case), where we apply AFP injectivity at each tower level to show `w ≡ ε` in the HNN extension implies `w ≡ ε` in the base group.

### The Two Branches in `britton_lemma_full`

The code splits on `max_lev` because `has_adjacent_opposite_exists` needs to find the relevant pair differently:

- **Case A (`max_lev ≥ 1`)**: The rightmost Gen-Inv pair is at the end of the word (suffix is empty). The pair itself contributes non-empty syllables.
- **Case B (`max_lev = 0`)**: The word oscillates but never goes above level 0. We find the leftmost Inv-Gen at minimum level. The suffix after the pair needs analysis.

Both cases use the same core fact: `no_pinch ∧ m ≥ 1 → non-empty syllables`. The case split is structural, not mathematical.

---

## What Is Already Proved

### 1. Miller's Action Implementation (Parts N and O) ✅

| Function | Line | Description |
|----------|------|-------------|
| `textbook_g2_action` | 4480 | AFP-level ψ(p): B-coset decompose + PREPEND/COLLAPSE |
| `textbook_g1_action` | 4506 | AFP-level ψ(p⁻¹): A-coset decompose + PREPEND/COLLAPSE |
| `textbook_psi_p` | 4592 | HNN-level ψ(p): wraps `tower_afp_data` + `textbook_g2_action` |
| `textbook_psi_p_inv` | 4613 | HNN-level ψ(p⁻¹): wraps `tower_afp_data` + `textbook_g1_action` |
| `textbook_act_hnn` | 4635 | Process HNN word right-to-left using ψ(p)/ψ(p⁻¹) |

**Length lemmas:**
- `lemma_textbook_g2_prepend_length` (4531): PREPEND → +1 syllable
- `lemma_textbook_psi_p_length` (5150): ψ(p) PREPEND → +1, COLLAPSE → -1
- `lemma_textbook_psi_p_inv_length` (5172): ψ(p⁻¹) PREPEND → +1, COLLAPSE → -1
- `lemma_textbook_act_single_stable` (5194): single stable letter = ψ(p) or ψ(p⁻¹)

### 2. No-Collapse Proof (Part P, lines 5580-5805) ✅

**`lemma_p_reduced_no_collapse`** (line 5580): If `w` is p-reduced (no pinch), `textbook_act_hnn` never triggers COLLAPSE.

**Supporting lemmas:**
- `lemma_no_collapse_gives_m` (5392): `syls.len() = stable_count(w)` when no collapse
- `lemma_gen_inv_base_not_in_B` (5478): Gen-Inv pair without pinch → base word ∉ B
- `lemma_inv_gen_base_not_in_A` (5521): Inv-Gen pair without pinch → base word ∉ A
- `lemma_psi_p_h_valid` (5808): output h of ψ(p) is valid base word
- `lemma_psi_p_inv_h_valid` (5836): output h of ψ(p⁻¹) is valid base word

### 3. Syllable Counting Infrastructure (Part M) ✅

| Function/Lemma | Line | Description |
|----------------|------|-------------|
| `right_syllable_count` | 2266 | Count RIGHT (p) syllables |
| `lemma_act_left_sym_preserves_right_count` | 2277 | G₁ action never changes right count |
| `lemma_act_g1_word_preserves_right_count` | 2315 | Full G₁ word preserves right count |

### 4. AFP Injectivity (in `normal_form_afp_textbook.rs`) ✅

| Lemma | Line | Description |
|-------|------|-------------|
| `action_well_defined` (spec) | 1936 | All AFP relators + inverse pairs act trivially |
| `lemma_identification_relator_acts_trivially` | 4501 | Identification relators act trivially |
| `lemma_action_well_defined_proof` | 5821 | Full proof of `action_well_defined` |

### 5. `britton_lemma_full` Structure (lines 5923-5937) ✅

```rust
if !has_pinch(data, w) {
    lemma_equiv_net_level_zero(data, w);  //  w = ε → net_level(w) = 0
    let max_lev = max_prefix_level(data, w);
    lemma_max_prefix_bounds(data, w, 0);

    if max_lev >= 1 {
        assert(false); //  TODO: lemma_case_a_contradiction (line 5931)
    } else {
        lemma_adjacent_opposite_exists(data, w);
        assert(false); //  TODO: symmetric argument (line 5935)
    }
}
```

All supporting infrastructure exists:
- `lemma_equiv_net_level_zero` (2582): w ≡ ε → net_level(w) = 0
- `max_prefix_level` (3410): maximum level reached by any prefix
- `lemma_max_prefix_bounds` (3426): max_prefix_level ≥ 0
- `lemma_adjacent_opposite_exists` (2681): net_level=0 + stable letters → adjacent opposite pair

---

## What Remains

8 lemmas total. All follow Miller's direct argument (no tower decomposition needed for `britton_lemma_full`).

---

### Tier 1: Well-definedness — the "routine check" (Part Y.7, lines 5875-5897)

These establish that `textbook_act_hnn` is a well-defined permutation representation of G*. The 5 lemmas form a chain: Lemmas 1-4 prove Lemma 5; Lemma 5 gives `w ≡ ε → empty syllables`.

---

#### Lemma 1: `lemma_psi_p_psi_p_inv_id`

```rust
pub proof fn lemma_psi_p_psi_p_inv_id(
    data: HNNData,
    h: Word,
    syls: Seq<Syllable>,
)
requires
    hnn_data_valid(data),
    word_valid(h, data.base.num_generators),
ensures
    textbook_psi_p_inv(
        data,
        textbook_psi_p(data, h, syls).0,
        textbook_psi_p(data, h, syls).1,
    ) == (h, syls)
```

**Proof**: 4-case analysis on PREPEND/COLLAPSE combinations of ψ(p) and ψ(p⁻¹). Uses identification isomorphism `embed_a(embed_b(x)) ≡ x ≡ embed_b(embed_a(x))`.

---

#### Lemma 2: `lemma_psi_p_inv_psi_p_id`

```rust
pub proof fn lemma_psi_p_inv_psi_p_id(
    data: HNNData,
    h: Word,
    syls: Seq<Syllable>,
)
requires
    hnn_data_valid(data),
    word_valid(h, data.base.num_generators),
ensures
    textbook_psi_p(
        data,
        textbook_psi_p_inv(data, h, syls).0,
        textbook_psi_p_inv(data, h, syls).1,
    ) == (h, syls)
```

**Proof**: Symmetric to Lemma 1. Swaps A↔B and LEFT↔RIGHT throughout.

---

#### Lemma 3: `lemma_hnn_relator_acts_trivially`

```rust
pub proof fn lemma_hnn_relator_acts_trivially(
    data: HNNData,
    i: int,
)
requires
    hnn_data_valid(data),
    0 <= i < data.associations.len(),
ensures
    textbook_act_hnn(
        data,
        hnn_relator(data, i),
        empty_word(),
        Seq::<Syllable>::empty(),
    ) == (empty_word(), Seq::<Syllable>::empty())
```

**Proof**: `hnn_relator(data, i)` is `t⁻¹·a_i·t·b_i⁻¹` where `b_i = φ(a_i)`. Process right-to-left:
1. `t⁻¹` → `(ε, [LEFT ε])`
2. `a_i` → `(a_i, [LEFT ε])`
3. `t` → PREPEND (since `a_i ∉ B` from `hnn_associations_isomorphic`) → `(φ⁻¹(b_i), [RIGHT ε, LEFT ε])`
4. `b_i⁻¹` → `(ε, [LEFT ε])` after absorption

Alternative: use Lemmas 1+2 to show `ψ(p⁻¹)∘ψ(p) = id` on the coset rep, giving `ψ(p⁻¹)∘θ(a_i)∘ψ(p) = θ(a_i)`. Then `θ⋆ψ(r) = θ(a_i)∘θ(b_i)⁻¹ = id` since `b_i = φ(a_i)`.

---

#### Lemma 4: `lemma_base_relators_preserve_syllables`

```rust
pub proof fn lemma_base_relators_preserve_syllables(
    data: HNNData,
    w: Word,
    h: Word,
    syls: Seq<Syllable>,
)
requires
    hnn_data_valid(data),
    hnn_associations_isomorphic(data),
    word_valid(w, data.base.num_generators),      //  w is a BASE word
    word_valid(h, data.base.num_generators),
    textbook_no_collapse(data, w, h, syls),       //  no collapse during processing
ensures
    textbook_act_hnn(data, w, h, syls).1.len() == syls.len()
```

**Proof**: Base words act via G₁ or G₂ in the AFP. By `normal_form_afp_textbook::action_well_defined`, AFP relators act trivially. The no-collapse precondition means the syllable count is preserved. For non-relator base words, use `lemma_act_g1_word_preserves_right_count`.

---

#### Lemma 5: `lemma_textbook_act_hnn_respects_derivation`

```rust
pub proof fn lemma_textbook_act_hnn_respects_derivation(
    data: HNNData,
    w1: Word,
    w2: Word,
    step: DerivationStep,
)
requires
    hnn_data_valid(data),
    hnn_associations_isomorphic(data),
    apply_step(hnn_presentation(data), w1, step) == Some(w2),
ensures
    textbook_act_hnn(data, w1, empty_word(), Seq::<Syllable>::empty())
        == textbook_act_hnn(data, w2, empty_word(), Seq::<Syllable>::empty())
```

**Proof**: Induction on derivation structure. For `RelatorInsert`/`RelatorDelete` of an HNN relator: uses Lemma 1 or 2 (ψ(p)∘ψ(p⁻¹) = id). For base relator: uses Lemma 4.

**Consequence** (proved after this lemma):
```rust
//  If w ≡ ε in G*, the action gives empty syllables
requires hnn_data_valid(data), hnn_associations_isomorphic(data), equiv_in_presentation(hnn_presentation(data), w, empty_word())
ensures textbook_act_hnn(data, w, empty_word(), Seq::<Syllable>::empty())
    == (empty_word(), Seq::<Syllable>::empty())
```

---

### Tier 2: The core — non-empty syllables from no-pinch

#### Lemma 6: `lemma_no_pinch_action_nontrivial`

```rust
pub proof fn lemma_no_pinch_action_nontrivial(
    data: HNNData,
    w: Word,
)
requires
    hnn_data_valid(data),
    word_valid(w, hnn_presentation(data).num_generators),
    has_stable_letter(data, w),
    !has_pinch(data, w),
ensures
    textbook_act_hnn(data, w, empty_word(), Seq::<Syllable>::empty()).1.len() >= 1
```

**Proof**: Trivial from existing infrastructure:
- `!has_pinch` → `lemma_p_reduced_no_collapse` → no COLLAPSE during processing
- `has_stable_letter` → `stable_count(w) >= 1`
- `lemma_p_reduced_no_collapse` + `lemma_no_collapse_gives_m` → `syls.len() = stable_count(w) >= 1`

---

### Tier 3: The two branches

#### Lemma 7: `lemma_case_a_contradiction` (Case A — `max_lev >= 1`, line 5931)

```rust
pub proof fn lemma_case_a_contradiction(
    data: HNNData,
    w: Word,
    max_lev: int,
)
requires
    hnn_data_valid(data),
    hnn_associations_isomorphic(data),
    word_valid(w, hnn_presentation(data).num_generators),
    equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    has_stable_letter(data, w),
    !has_pinch(data, w),
    max_lev == max_prefix_level(data, w),
    max_lev >= 1,
ensures
    false
```

**Proof**:
1. `max_lev >= 1` → `stable_count(w) >= 1` (there are stable letters)
2. `!has_pinch` → Lemma 6 → `textbook_act_hnn(w, ε, []).1.len() >= 1`
3. `equiv_in_presentation` → Lemma 5 → `textbook_act_hnn(w, ε, []) = (ε, [])` → `syls.len() == 0`
4. Contradiction: `>= 1` vs `== 0`

---

#### Lemma 8: `lemma_case_b_contradiction` (Case B — `max_lev = 0`, line 5935)

```rust
pub proof fn lemma_case_b_contradiction(
    data: HNNData,
    w: Word,
)
requires
    hnn_data_valid(data),
    hnn_associations_isomorphic(data),
    word_valid(w, hnn_presentation(data).num_generators),
    equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    has_stable_letter(data, w),
    !has_pinch(data, w),
    max_prefix_level(data, w) == 0,  //  Note: lemma_max_prefix_bounds gives >= 0, so = 0
ensures
    false
```

**Proof**: Same as Lemma 7. `max_lev = 0` still gives `stable_count(w) >= 1` (from `has_stable_letter`). `!has_pinch` → Lemma 6 → non-empty syllables. `w ≡ ε` → Lemma 5 → empty syllables. Contradiction.

**Note**: The `max_lev = 0` vs `max_lev >= 1` split is only about locating the relevant adjacent pair via `lemma_adjacent_opposite_exists`. The contradiction itself is identical: `!has_pinch ∧ has_stable_letter` → non-empty syllables; `w ≡ ε` → empty syllables.

---

## Dependency Graph

```
britton_lemma_full
├── lemma_equiv_net_level_zero               [✅ exists, line 2582]
├── max_prefix_level                          [✅ exists, line 3410]
├── lemma_max_prefix_bounds                   [✅ exists, line 3426]
├── lemma_adjacent_opposite_exists            [✅ exists, line 2681]
│
├── [TODO] TIER 1 — Well-definedness (Part Y.7, line 5875)
│   ├── lemma_psi_p_psi_p_inv_id             [Lemma 1]
│   ├── lemma_psi_p_inv_psi_p_id             [Lemma 2]
│   ├── lemma_hnn_relator_acts_trivially      [Lemma 3]
│   ├── lemma_base_relators_preserve_syllables [Lemma 4]
│   └── lemma_textbook_act_hnn_respects_derivation [Lemma 5]
│       ├── uses Lemma 1 (HNNInsert/Delete)
│       └── uses Lemma 4 (base relator)
│
├── [TODO] TIER 2 — Core contradiction
│   └── lemma_no_pinch_action_nontrivial      [Lemma 6]
│       ├── uses lemma_p_reduced_no_collapse  [✅ exists]
│       └── uses lemma_no_collapse_gives_m    [✅ exists]
│
├── [TODO] TIER 3A — Case A (line 5931)
│   └── lemma_case_a_contradiction            [Lemma 7]
│       ├── uses Lemma 6
│       └── uses Lemma 5 (from Tier 1)
│
└── [TODO] TIER 3B — Case B (line 5935)
    └── lemma_case_b_contradiction            [Lemma 8]
        ├── uses Lemma 6
        └── uses Lemma 5 (from Tier 1)
```

**Total: 8 new lemmas.** Lemmas 1-5 are the critical path. Lemma 6 is trivial (combines existing infrastructure). Lemmas 7-8 are nearly identical — just `max_lev >= 1` vs `max_lev = 0` in the requires.

---

## Key Insight: The Direct Miller Argument

The tower decomposition (prefix/G₂-one-shot/suffix) is **NOT needed** for `britton_lemma_full`. It belongs to `britton_lemma_unconditional`, where we decompose the tower word to apply AFP injectivity level by level.

For the pinch theorem, Miller's argument is simpler:
- If `w ≡ ε` and `w` has no pinch → `w` is a normal form → `textbook_act_hnn(w, ε, [])` has `stable_count(w) ≥ 1` syllables
- Well-definedness: `w ≡ ε` → empty syllables
- Contradiction

The `max_lev ≥ 1` vs `max_lev = 0` split in the current code is about finding the relevant adjacent pair, not about the contradiction itself. The contradiction is the same in both cases: non-empty syllables from no-pinch, vs empty syllables from `w ≡ ε`.

---

## Textbook Alignment

### Difference 1: Verus merges Miller's Cases 1 and 2 into PREPEND ✅ (documented, acceptable)

Miller (p.49) has three distinct cases; Verus merges Cases 1 and 2 because both produce the same state representation `(φ⁻¹(b), [RIGHT z₀])`. The routine check has 4 cases instead of 9 — mathematically equivalent.

### Difference 2: Comment error at `textbook_g2_action` line 4487

Comment says `φ⁻¹(g)` but should say `φ⁻¹(b)` where `b = h_new = b_rcoset_h(data, g)`. **Needs fixing.**

### Difference 3: COLLAPSE output normalization ✅ (acceptable)

Verus re-decomposes through `a_rcoset_h`, producing the A-canonical representative instead of Miller's direct `(ag₁)`. Both represent the same element in canonical form.

---

## Summary

**`britton_lemma_full`** has exactly **2 remaining `assert(false)` placeholders** (lines 5931, 5935). Everything else is in place.

**Critical path:** The 5 well-definedness lemmas (Tier 1) are the critical path. They establish that `textbook_act_hnn` is a well-defined permutation representation of G*. Once done, Case A and Case B follow from the direct Miller argument: `no_pinch ∧ m ≥ 1 → non-empty syllables` contradicts `w ≡ ε → empty syllables`.

**The tower decomposition is NOT needed for the pinch theorem.** It belongs to `britton_lemma_unconditional` (base word case), where we apply AFP injectivity via tower level decomposition.

---

## References

- Miller, Ch. IV, Theorem 3.10 (Embedding and Reduction / Britton's Lemma), p.45-49
- Lyndon & Schupp, Combinatorial Group Theory, Ch. IV
