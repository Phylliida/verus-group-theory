# AFP Textbook One-Shot Proof — Complete Reference

## Overview

This document describes the Verus formalization of the normal form theorem for amalgamated free products (AFP) following Lyndon-Schupp Chapter IV. The proof establishes that the van der Waerden action on reduced sequences is well-defined, which gives AFP injectivity (each factor group embeds into the AFP).

**File:** `normal_form_afp_textbook.rs` (~10,000 lines, 195+ verified functions, 0 assumes)

## Architecture: The One-Shot Approach

The textbook defines a GROUP-LEVEL action of each factor G₁, G₂ on the set S of reduced sequences. Each group element g ∈ G₁ acts via a single coset decomposition ("one-shot"). The word-level action (`act_word`) processes symbols one at a time. The key theorem: these are equal.

### Key Spec Functions

```
g1_one_shot_action(data, g, syls)  — G₁ one-shot: single A-coset decomposition of g
g2_one_shot_action(data, g, syls)  — G₂ one-shot: single B-coset decomposition of g
act_word(data, w, h, syls)         — sequential action, RIGHT-TO-LEFT processing
act_left_sym(data, s, h, syls)     — single G₁ symbol action
act_right_sym(data, s, h, syls)    — single G₂ symbol action
```

### Critical Convention: RIGHT-TO-LEFT Processing

`act_word` processes the word RIGHT-TO-LEFT (last symbol first). This matches the textbook LEFT action convention: φ(g₁·g₂) = φ(g₁) ∘ φ(g₂), so for word [s₁,...,sₙ], sₙ is applied first.

**Why this matters:** LEFT-TO-RIGHT with LEFT multiplication gives the REVERSED group element. For a relator r = s₁·...·sₙ = ε, the reverse sₙ·...·s₁ is NOT ε in general. The counterexample `G = ⟨a,b,c | abc=1⟩` proves this: cba = b⁻¹a⁻¹ba ≠ ε.

Consequence: `inverse_pair_word(s) = [inv(s), s]` (not [s, inv(s)]) so that RIGHT-TO-LEFT processes s first, then inv(s) — matching the existing proof structure.

### Composition Property: `act_word_concat`

```
act_word(concat(w1, w2), h, syls) = act_word(w1, act_word(w2, h, syls))
```

With RIGHT-TO-LEFT: w2 is processed first, then w1. This is the textbook left action composition.

## The Three Relator Triviality Theorems

### 1. G₁ Relator Triviality (`lemma_g1_relator_acts_trivially`)

**Statement:** If `w ≡ ε in G₁` and `word_valid(w, n1)`, then `act_word(w, h, syls) = (h, syls)` for any canonical state.

**Proof chain:**
1. `lemma_act_word_eq_one_shot`: `act_word(w, h, syls) = g1_one_shot_action(concat(w, embed_a(h)), syls)`
2. Since `w ≡ ε`: `concat(w, embed_a(h)) ≡ embed_a(h)` in G₁
3. `lemma_one_shot_subgroup_restore`: `g1_one_shot_action(g, syls) = (h, syls)` when `g ≡ embed_a(h)` and h canonical

**Key helper chain for step 1 (the hard part):**
- `lemma_one_shot_step` — dispatches to subgroup/prepend/merge cases
- `lemma_one_shot_step_prepend` — prepend case (uses `prepend_cancel` or `subgroup_prepend`)
- `lemma_one_shot_step_merge` — merge absorbed case
- `lemma_one_shot_step_merge_replaced` — merge replaced case
- `lemma_embed_hs_equiv_chain` — derives `concat(w, embed_a(h_s)) ≡ concat(concat(w, g_s), inv(rep_s))`
- `lemma_peeled_concat_bridge` — derives `concat(peeled, rep) ≡ w_full`

### 2. G₂ Relator Triviality (`lemma_g2_relator_acts_trivially`)

**Statement:** If `w ≡ ε in G₂` and `word_valid(w, n2)`, then `act_word(shift_word(w, n1), h, syls) = (h, syls)`.

Mirrors G₁ exactly with `b_rcoset` instead of `a_rcoset`, `b_words` instead of `a_words`, `!is_left` instead of `is_left`.

### 3. Identification Relator Triviality (`lemma_identification_relator_acts_trivially`)

**Statement:** For identification generator i, `act_word(u_i · inv(shift(v_i)), h, syls) = (h, syls)`.

**Proof sketch (the mathematical heart):**
1. Process `inv(shift(v_i))` via G₂ one-shot: product `inv(v_i) · embed_b(h)` is in B-subgroup → gives `(h', syls)` (syllables unchanged since product in subgroup)
2. Process `u_i` via G₁ one-shot: product `u_i · embed_a(h')` — need to show this ≡ `embed_a(h)` in G₁
3. Define K-word difference `k_diff = concat(h', inv(concat(Inv(i), h)))`
4. Show `embed_b(k_diff) ≡ ε` in G₂ (from the decomposition: embed_b(h') ≡ embed_b(k_combined))
5. By `identifications_isomorphic`: `embed_a(k_diff) ≡ ε` in G₁
6. Unpack: `embed_a(h') ≡ concat(inv(u_i), embed_a(h))` → `concat(u_i, embed_a(h')) ≡ embed_a(h)`
7. `one_shot_subgroup_restore` gives `(h, syls)`

**Status: COMPLETE (200 verified, 0 errors, 0 assumes)**

## Key Infrastructure

### Right A-Coset Decomposition
- `a_rcoset_rep(data, g)` — canonical coset representative (three-step choose: min-len → min-lex → unique word)
- `a_rcoset_h(data, g)` — canonical K-word h such that `embed_a(h) · rep ≡ g` in G₁
- `same_a_rcoset(data, g1, g2)` — g1 and g2 in same A-coset

### Right B-Coset Decomposition (mirrors A-coset)
- `b_rcoset_rep`, `b_rcoset_h`, `same_b_rcoset` — same structure with b_words/p2

### H-Part Equivalence Invariance
- `lemma_a_rcoset_h_equiv_invariant(data, g1, g2, hw1, hw2)` — if g1 ≡ g2 in G₁ with same rep, h-parts match
- `lemma_a_rcoset_h_min_len_equiv` — min-len equality from equiv targets
- `lemma_b_rcoset_h_equiv_invariant_general` — B-coset mirror for general reps

### One-Shot Invariance
- `lemma_one_shot_g1_invariant` — if g ≡ g' in G₁, `g1_one_shot_action(g, syls) = g1_one_shot_action(g', syls)`
- `lemma_g2_one_shot_g2_invariant` — G₂ mirror

### Composition Helpers
- `lemma_one_shot_prepend_cancel` — peeling off coset rep and prepending as syllable gives same result
- `lemma_one_shot_subgroup_prepend` — subgroup case of prepend (q ∈ A: different proof path via target-based h-part invariance)
- `lemma_g2_prepend_cancel`, `lemma_g2_subgroup_prepend` — G₂ mirrors

### Embedding Properties (in `benign.rs`)
- `lemma_apply_embedding_concat` — `embed(concat(w1, w2)) =~= concat(embed(w1), embed(w2))`
- `lemma_apply_embedding_inverse` — `embed(inv(w)) =~= inv(embed(w))`

## Lessons Learned

### 1. RIGHT-TO-LEFT Processing is Essential
LEFT-TO-RIGHT with LEFT multiplication gives the reversed group element. The textbook's LEFT action requires RIGHT-TO-LEFT processing. Counterexample: `abc = 1` does NOT imply `cba = 1`.

### 2. Seq::new Lambda Closures Don't Match Across Call Sites
Z3 treats each `Seq::new(n, |i| f(i))` at a different call site as a distinct opaque sequence. Even if two closures compute the same values, Z3 can't see they're equal. **Fix:** Pass the constructed Seq as a parameter (`new_syls`) instead of constructing it internally in the ensures clause.

### 3. The Subgroup Sub-Case is Non-Trivial
When the "peeled product" `concat(w, g_s) · inv(rep_s)` falls into the subgroup (rep = ε), the composition proof takes a completely different path via `subgroup_prepend` with target-based h-part invariance. Both the prepend and merge cases need this sub-split.

### 4. Module Size Causes Rlimit Pressure
With 195+ functions in one module, every function's body is in every other function's SMT context. Functions that verified at rlimit 30 now need 100-300. **Mitigation:** Split heavy helpers, use `assert-by` scoping, move utility lemmas to other modules (e.g., `benign.rs`).

### 5. The Three-Step Choose Pattern
Canonical representatives use a three-step choose (min-length → min-lex-rank → unique word via lex rank injectivity). This ensures coset/h-part invariance under equivalence: same equivalence class → same min-length → same min-lex → same word.

### 6. Embedding Properties Belong in `benign.rs`
`lemma_apply_embedding_concat` and `lemma_apply_embedding_inverse` need to be in the same module as `apply_embedding` for Z3 to see the internal structure. Placed in `normal_form_afp_textbook.rs`, they fail due to closure mismatch.

## Remaining Work

### DONE: Identification Relator (all 3 errors fixed, 2026-03-25)
- `lemma_ident_g2_diff_trivial`: used k_combined directly as h_witness, switched to equiv_concat_left
- `lemma_ident_g1_product_equiv`: reveal_with_fuel for single-symbol embedding, lemma_diff_trivial_implies_equiv helper
- Main function: extracted K-word construction into `lemma_ident_isomorphism_transfer`, used action_preserves_canonical

### DONE: Assembly (2026-03-25)
- `lemma_inv_r_concat_r_trivial`: concat(inv(r), r) trivial via inverse pairs (induction)
- `lemma_trivial_action_inverse`: r trivial → inv(r) trivial
- `lemma_action_well_defined_proof`: all AFP relators + inverse pairs act trivially
- `lemma_afp_injectivity`: **MAIN THEOREM** — w ≡ ε in AFP → w ≡ ε in G₁

### DONE: Tower wiring (2026-03-25)
- `lemma_g0_embeds_in_tower_textbook`: textbook AFP injectivity at each tower level
- `britton_lemma_via_tower`: Britton's lemma statement (tower embedding)

### Remaining: Derivation Translation (~400 lines)
- `lemma_action_well_defined_proof`: combine G₁ + G₂ + identification + inverse pair triviality into the `action_well_defined` spec
- Requires mapping AFP relator indices to the three categories (G₁ relators at indices 0..n1_rel, shifted G₂ relators at n1_rel..n1_rel+n2_rel, identification relators at n1_rel+n2_rel..end)

### Main Theorem
- `lemma_afp_injectivity_textbook`: if `w` is a G₁-word and `w ≡ ε` in the AFP, then `w ≡ ε` in G₁
- Uses `action_well_defined` → `lemma_act_word_deriv` → the action of `w` on the identity state gives `(ε, [])` → by `g1_decompose_converse`: `w ≡ ε` in G₁

### Tower and Britton's Lemma
- Wire the textbook AFP injectivity into `tower.rs` (replaces the old Cayley-table approach)
- Derive Britton's lemma as a corollary via the tower construction
