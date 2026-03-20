# Britton Lemma Proof - Notes for Future Work

## Overview
The Britton's lemma proof in `britton_proof.rs` is substantially complete (~95%).
There are 2 remaining gaps marked with `assume(false)`.

## Gap 1: Overlapping Relator Case (line ~10104)

**Location:** `lemma_k3_ri_hnn_reldelete_base` - the `else` branch for `p0 < p1 < p0 + r0_len`

**What it represents:** When inserting an HNN relator r0 at position p0, then deleting a base relator r1, the deletion might fall *within* the inserted relator region (overlapping case).

**Why it's hard:**
1. r1 is a base relator (gen_idx < n) contained within the middle part of r0 (a_j or inv(b_j))
2. The stable letters of r0 are at positions p0 and p0+|a_j|+1, which are NOT being deleted
3. After deletion, w2 has stable_count = 2 (stable letters separated by base material)
4. For w_end to be base after step2, step2 must somehow resolve these stable letters

**Failed approach:** Tried to prove contradiction by showing w2 cannot reach base in one step.
- The match on step2 branch approach failed because each branch just asserted false without proof
- The issue is that the contradiction isn't immediate - we need to show the specific structure
  of w2 makes it impossible to reach a base word

**What a correct proof would need:**
1. Show that when r1 is a sub-relator of a_j (or inv(b_j)), the deletion leaves the stable
   letters at positions that are separated by base words
2. Show that no single derivation step can make these stable letters adjacent for cancellation
3. Consider all step2 types: FreeReduce, FreeExpand, RelatorDelete(HNN), RelatorInsert

**Suggested approach for future:**
- Analyze the word structure more carefully
- Use `stable_letter_count` arguments more precisely
- Consider the case where r1 = a_j (rem_a empty) vs r1 is proper subword

## Gap 2: Peak Elimination for k >= 4 (line ~10329)

**Location:** `lemma_single_segment_hard` - the `else` branch for `steps.len() >= 4`

**What it represents:** When ALL intermediates in a derivation from base w to base w_end are non-base, and there are 4+ steps.

**Why it's hard:**
- The k=3 case was already complex with ~30 specialized lemmas
- k=4 would require analyzing many more combinations of step types
- The "peak elimination" argument: in a T-free derivation, there must be a "peak" (maximal stable letter count) that can be eliminated

**What a correct proof would need:**
- Implement the peak elimination strategy from combinatorial group theory
- Show that in a long derivation with all intermediates non-base, one can find adjacent steps that can be commuted/replaced to shorten the derivation
- This is essentially showing the derivation can be reduced to k=3 or less

## Failed Approach for Overlapping Case

```
Proof attempt:
- Tried to use stable_letter_count arguments
- Tried to match on step2 and assert false in each branch
- Issue: the assertions weren't proven, just stated

The fundamental issue:
- The contradiction isn't immediate from the preconditions
- Need to carefully track word structure after deletion
- The overlap case might actually be possible in some scenarios
```

## File Structure Recommendation

The file `britton_proof.rs` is ~11,000 lines. Suggested split:

1. `britton_proof_base.rs` - Core infrastructure lemmas
   - Derivation helpers
   - Stable letter count lemmas
   - Base/non-base characterization

2. `britton_proof_k2.rs` - k=2 case lemmas
   - `lemma_single_segment_k2`
   - Related step-type specific lemmas

3. `britton_proof_k3.rs` - k=3 case lemmas (~4000 lines)
   - All `lemma_k3_*` functions
   - The k=3 hard case dispatch

4. `britton_proof_induction.rs` - Induction and splitting
   - `lemma_single_segment`
   - `lemma_single_segment_hard` (with assume(false) placeholders)
   - `lemma_base_derivation_equiv`
   - `britton_lemma_with_derivation`
   - `britton_lemma`

5. `britton_proof_helpers.rs` - Already exists, contains 3 helper lemmas

## Key Lemmas and Their Relationships

```
britton_lemma
  └── britton_lemma_with_derivation
          └── lemma_base_derivation_equiv
                  ├── [steps.len() == 0] → reflexivity
                  ├── [w1 is base] → T-free step + recurse
                  └── [w1 is non-base]
                          ├── [w2 is base] → split at position 2
                          │       ├── lemma_single_segment_k2
                          │       └── lemma_base_derivation_equiv (right, shorter)
                          └── [w2 is non-base]
                                  ├── lemma_first_base_is_base → find first base at k
                                  ├── [k < steps.len()] → split and recurse
                                  └── [k == steps.len()] → lemma_single_segment_hard
                                                                  └── [k==3] → case analysis
                                                                          └── [k>=4] → assume(false) ⚠️
```

## Useful Helper Functions

- `stable_letter_count(w, n)` - counts stable letters (gen_idx == n) in word
- `is_base_word(w, n)` - true if stable_letter_count is 0
- `lemma_hnn_relator_stable_positions` - shows stable letters at positions 0 and |a_j|+1
- `apply_step(hp, w, step)` - applies a derivation step, returns Option<Word>
