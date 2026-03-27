# Britton's Lemma via Tower Construction — Session Summary

## Overview

This document summarizes the formalization of Britton's lemma via the tower construction, following Lyndon-Schupp Chapter IV. Starting from 195 verified functions with 3 errors, we reached **293 verified, 0 errors, 0 assumes** across 3 files (223 + 15 + 55).

**Gaps closed:** All 4 gaps (action_preserves_canonical, identity canonical, tower isomorphism, AFP right-injectivity). Only Gap 3 (level normalization, ~50 lines) remains for fully unconditional Britton.

**Theorem (Britton's Lemma):** If `w` is a base word (no stable letters) and `w = 1` in the HNN extension `G*`, then `w = 1` in the base group `G`.

**Proof approach:** Unfold the HNN extension into a tower of iterated amalgamated free products. AFP injectivity at each level gives the base group embedding. HNN relators translate to AFP identification relators at tower junctions.

## Files

| File | Verified | Role |
|------|----------|------|
| `normal_form_afp_textbook.rs` | 223 | AFP injectivity via textbook one-shot action |
| `tower.rs` | 15 | Tower construction + textbook embedding |
| `britton_via_tower.rs` | 52 | Derivation translation + Britton's lemma |

## Architecture

```
AFP injectivity (one-shot action, Lyndon-Schupp Ch. IV)
    |
    |--- action_preserves_canonical (from identifications_isomorphic)
    |--- action_well_defined (G1 + G2 + identification relator triviality)
    |--- act_word_deriv (derivation-level well-definedness)
    |
Tower embedding (inductive AFP injectivity at each level)
    |
    |--- lemma_g0_embeds_in_tower_textbook
    |--- lemma_afp_injectivity_right (right factor embedding)
    |
Derivation translation (HNN steps -> tower steps)
    |
    |--- translate_word_at (level-aware word translation)
    |--- lemma_translate_hnn_relator (HNN relator = identification relator)
    |--- lemma_hnn_step_tower_equiv (per-step translation)
    |--- lemma_hnn_derivation_to_tower_equiv (full induction)
    |
Britton's lemma
    |--- britton_lemma (conditional on tower prerequisites)
```

## Key Theorems (all 0 assumes)

### AFP Injectivity
- `lemma_afp_injectivity`: If w is a G1-word and w = 1 in AFP, then w = 1 in G1.
- `lemma_afp_injectivity_right`: If shift(w, n1) = 1 in AFP, then w = 1 in G2.

### Action Preserves Canonical
- `lemma_action_preserves_canonical_spec`: `identifications_isomorphic(data)` implies `action_preserves_canonical(data)`.
- Proof chain: A-side canonical (left_h_part fixed point) + B-side canonical (b_rcoset_h fixed point via A<->B witness transfer) + syllable case analysis.
- The A<->B transfer is the mathematical heart: `identifications_isomorphic` makes A and B equivalence classes on K-words coincide, so the three-step choose (min-len, min-lex, unique word) gives the same result for both decompositions.

### Tower Embedding
- `lemma_g0_embeds_in_tower_textbook`: w = 1 in tower(n) implies w = 1 in base.
- `lemma_base_at_copy_k_embeds`: equiv(base, w1, w2) implies equiv(tower(m), shift(w1, k*ng), shift(w2, k*ng)) via shift homomorphism.

### Derivation Translation
- `lemma_translate_hnn_relator`: HNN relator t^-1 * a_i * t * inv(b_i) at level k translates to AFP identification relator at tower junction (k-1)<->k.
- `lemma_hnn_derivation_to_tower_equiv`: Full HNN derivation translates to tower equivalence.

### Britton's Lemma
- `britton_lemma`: If w is a base word, w = 1 in G*, tower prerequisites hold, and derivation levels are OK, then w = 1 in G.

## Lessons Learned

### 1. Seq::new Closure Mismatch is the #1 Z3 Engineering Issue

Z3 treats each `Seq::new(n, |i| f(i))` at a different call site as a distinct opaque sequence, even if the closures compute identical values. This manifests as:

- `inverse_word(Seq::new(1, |_| s)).len() == 1` — Z3 can't unfold `inverse_word` when its argument is from a different Seq::new
- `apply_embedding(shifted_images, w) =~= shift_word(apply_embedding(images, w), offset)` — Z3 can't see the distributivity through Seq::new
- `a_words_tower =~= b_words_hnn` — element-wise equal but Z3 doesn't see Seq =~=

**Fixes that work:**
- Pass constructed Seqs as PARAMETERS instead of building them in `ensures` clauses
- Use `reveal_with_fuel(fn, depth)` for recursive functions on Seq::new arguments
- Assert element-wise facts to trigger Seq axioms: `seq[i] == expected_value`
- Put helper lemmas in the SAME MODULE as the spec function (e.g., `lemma_inverse_word_len` in `word.rs`)
- Use `lemma_shift_embedding_distributes` with shifted images as parameter to avoid Seq::new in ensures

### 2. The Three-Step Choose Pattern Requires Careful Uniqueness Arguments

The canonical K-word choose (min-length -> min-lex -> unique word) is deterministic but Z3 can't derive `choose_result == specific_value` without:

1. Showing specific_value satisfies the predicate (from satisfiability)
2. Showing specific_value is the ONLY satisfier (from min-len/min-lex uniqueness)
3. Using `lemma_word_lex_rank_base_injective` for the final word equality

**Pattern for proving choose equals a specific value:**
```
// Step 1: Establish min-len equality (h.len() == choose_min_len)
// Step 2: Transfer no_pred_below between A and B sides
// Step 3: Establish min-lex equality (h.lex == choose_min_lex)
// Step 4: Apply lex rank injectivity (same length + same lex -> same word)
```

### 3. identifications_isomorphic is the Key to Everything

The `identifications_isomorphic` condition (embed_a(w) = 1 iff embed_b(w) = 1) is far more powerful than it appears:

- **A<->B witness transfer**: `has_left_h_witness_of_len(embed_a(h), l) <-> has_right_h_witness_of_len(embed_b(h), l)`
- **Canonical preservation**: A-canonical implies B-canonical (and vice versa)
- **action_preserves_canonical**: Follows from the above
- **Tower isomorphism**: `hnn_associations_isomorphic` lifts to `identifications_isomorphic` at each tower level

### 4. assert-by Scoping is Essential for Large Proofs

The rlimit guide's #1 recommendation: use `assert(F) by { lemma(); }` to scope fact pollution. In a module with 220+ functions, every lemma call adds facts to the context. Without scoping:
- Functions that verified at rlimit 30 need 300+
- Z3 spends time on irrelevant quantifier instantiations

**What works:**
- Extract sub-proofs into helper lemmas (reduces per-function context)
- Use `assert-by` for lemma calls only needed for one assertion
- Use `reveal(presentation_valid)` explicitly rather than leaving it auto-unfolded

### 5. The Homomorphism Infrastructure is Powerful

The `HomomorphismData` + `lemma_hom_preserves_equiv` pattern cleanly proves embeddings:
- Shift homomorphism: base -> tower(m) mapping Gen(i) -> Gen(i + k*ng)
- Only need: generator images are word_valid + relator images = 1 in target
- `lemma_hom_preserves_equiv` handles the derivation lifting automatically

### 6. RIGHT-TO-LEFT Processing is Non-Negotiable

The textbook LEFT action requires RIGHT-TO-LEFT processing (`w.last()/w.drop_last()`). LEFT-TO-RIGHT gives the REVERSED group element. Counterexample: `abc = 1` does NOT imply `cba = 1`.

### 7. Never Use assume()

The user blocks ALL tool calls containing `assume()` or `admit()`. When stuck:
- Split into smaller helpers
- Add intermediate assertions
- Use `reveal_with_fuel` for recursive unfolding
- Move helper lemmas to the defining module
- Document the gap and return later — never write assume as a placeholder

## Remaining Work

### Gap 4: Tower Isomorphism — CLOSED

`lemma_tower_identifications_isomorphic` proved via:
- `lemma_tower_iso_forward_mid`: tower equiv → base equiv (AFP right-injectivity for k>0, shift-by-0 identity for k=0)
- `lemma_tower_iso_backward_mid`: base equiv → tower equiv (shift homomorphism + base_at_copy_k_embeds)
- `lemma_shift_embedding_distributes`: apply_embedding distributes over shift
- hnn_associations_isomorphic biconditional for the A↔B connection

Key Z3 engineering lesson: extracting implications into separate helper functions gives Z3 a clean context. The biconditional `mid <==> rhs` fires automatically from hnn_iso, but `lhs ==> mid` and `mid ==> lhs` need separate functions because `if A { proof_of_B }` does NOT give `A ==> B` in the outer Z3 context.

### Gap 4 (ORIGINAL): Tower Isomorphism (10 lines of Z3 assertions)

`lemma_tower_iso_per_word` has the complete proof logic:
- Forward: AFP right-injectivity + hnn_iso
- Backward: base_at_copy_k_embeds + hnn_iso

Z3 needs ~10 more intermediate assertions to connect:
1. `tower_afp_data(data, k-1).p2 == data.base` (spec function unfolding)
2. `shift(embed_a_hnn, tower(k-1).num_generators) =~= embed_a_tower` (shift distributivity already proven)
3. The hnn_iso biconditional firing inside the if-blocks

### Gap 3: Level Normalization (~50 lines)

HNN derivations can have negative levels. The one-sided tower only handles levels [0, m]. Need either:
- Prove derivations of base words can be normalized to non-negative levels
- Or add a level-shift preprocessing step

### Gap 1+2+4: ALL CLOSED

With `lemma_tower_identifications_isomorphic` proven, `tower_textbook_chain` can now be established from `hnn_associations_isomorphic` alone (the `action_preserves_canonical` follows from `identifications_isomorphic` via `lemma_action_preserves_canonical_spec`).

### Final Assembly

After gap 3: update `britton_lemma` to remove `tower_textbook_chain` and `derivation_levels_ok` preconditions. The theorem becomes:

```
britton_lemma(data, w):
    requires: hnn_data_valid(data), hnn_associations_isomorphic(data),
              word_valid(w, base.num_generators), equiv(hnn, w, empty)
    ensures: equiv(base, w, empty)
```

With 0 assumes, 0 axioms — a complete formalization of Britton's lemma.
