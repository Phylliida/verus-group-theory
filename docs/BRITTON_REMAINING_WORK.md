# Remaining Work: Eliminating assume(false) in Britton's Lemma Proof

## Current State
- **62 verified, 4 errors** on helpers3 (postcondition proofs + termination)
- **0 assume(false)** in `lemma_k4_peak_ri_fr` (all replaced with `(false, ...)` + contradiction proofs)
- Full `(bool, ...)` cascade through the peak commutation chain
- Architecture is correct — just needs the isomorphism proofs filled in

## The 4 Remaining Errors

### Error 1: `lemma_k4_peak_ri_fr` postcondition `!ok ==> equiv(w1, w3)`

**File:** `britton_proof_helpers3.rs`, function `lemma_k4_peak_ri_fr` (~line 506)

The function returns `(false, arbitrary(), arbitrary(), arbitrary())` for genuine overlap sub-cases.
The postcondition requires: when `!ok`, prove `equiv_in_presentation(data.base, w1, w3)`.

**Sub-cases that return false (7 total):**

| Line | Sub-case | What happens | How to prove equiv(w1, w3) |
|------|----------|-------------|---------------------------|
| ~642 | Left boundary, inverted, b_j=[] | r1[0]=Inv(n), w1[p1-1]=Gen(n). FR removes [Gen(n),Inv(n)] at boundary | w3 = w1 with inv(a_j) inserted. Since a_j may be non-empty, use `lemma_insert_trivial_equiv` with a_j ≡ ε (need to prove from isomorphism) |
| ~648 | Left boundary, non-inverted | r1[0]=Inv(n), w1[p1-1]=Gen(n). FR removes boundary pair | w3 = w1 with a_j + [Gen(n)] + inv(b_j) remaining from relator. Need position arithmetic to show w3 = w1 + inserted_content, then isomorphism |
| ~761 | Inside relator, non-inverted, a_j=[], b_j≠[] | FR removes [Inv(n),Gen(n)] inside relator | w3 = w1 with inv(b_j) inserted at p1. **Already have `lemma_overlap_ri_fr_w1_equiv_w3` for this case!** Just call it. |
| ~809 | Inside relator, inverted, a_j=[], b_j≠[] | Inverted version of above | w3 = w1 with b_j inserted. Need inverted version of `lemma_overlap_ri_fr_w1_equiv_w3` |
| ~821 | Inside relator, inverted, a_j=[], b_j≠[] (second branch) | Same as above | Same as above |
| ~840 | Right boundary, non-inverted, b_j=[] | r1 ends with Gen(n), w1[p1]=Inv(n) | w3 = w1 with a_j removed or modified at boundary. Position arithmetic + isomorphism |
| ~845 | Right boundary, inverted | r1 ends with Gen(n) | Similar boundary analysis |

**Approach for each:**
1. Determine w3's structure by position arithmetic (what elements were removed/added)
2. Express w3 as w1 with some base content inserted/removed
3. Show the inserted/removed content is ≡ ε using the isomorphism (`lemma_aj_empty_bj_trivial` or similar)
4. Use `lemma_insert_trivial_equiv` or `lemma_remove_trivial_equiv` to conclude

**Easiest to prove:** Line ~761 (inside, non-inverted, a_j=[], b_j≠[]) — just call existing `lemma_overlap_ri_fr_w1_equiv_w3`.

**Helpers needed:**
- `lemma_overlap_ri_fr_w1_equiv_w3_inverted`: inverted version for inside-relator case
- `lemma_overlap_ri_fr_w1_equiv_w3_boundary_left`: left boundary straddle
- `lemma_overlap_ri_fr_w1_equiv_w3_boundary_right`: right boundary straddle
- Or: one general `lemma_overlap_ri_fr_w1_equiv_w3_general` that handles all sub-cases

### Error 2: `lemma_eliminate_peak_with_bypass` postcondition

**File:** `britton_proof_helpers3.rs`, function `lemma_eliminate_peak_with_bypass` (~line 1215)

Two issues:
1. The `!ok` return at the `else` branch (line ~1333) needs to prove `equiv(w1, w3)` — cascades from Error 1 via `lemma_k4_peak_noncancel_commute`
2. The `lemma_peak_bypass_commuted` return (line ~1297) might propagate `!ok` — need `!ok ==> equiv(w1, w3)` from `lemma_peak_bypass_commuted` as well

**Fix:** Once Error 1 is fixed, `lemma_k4_peak_noncancel_commute` will propagate `!ok ==> equiv(w1, w3)` through its postcondition. Then `lemma_eliminate_peak_with_bypass` just passes it through.

**Also needed:** `lemma_k4_peak_noncancel_commute` postcondition should include `!ok ==> equiv(w1, w3)`. Currently only `lemma_k4_peak_ri_fr` returns `!ok`; the other sub-helpers (fe_fr, fe_rd, ri_rd) always return `(true, ...)`. So this cascades naturally.

### Error 3: `lemma_bubble_peak_to_front` postcondition

**File:** `britton_proof_helpers3.rs`, function `lemma_bubble_peak_to_front` (~line 3936)

The base case calls `lemma_eliminate_peak_with_bypass` which returns `(bool, ...)`. When `!ok`, the caller can't produce valid `(w_base, left, right)`.

**Fix:** When `!ok_`, use the `equiv(w1, w3)` postcondition to build the proof differently:
1. `equiv(w1, w3)` from the postcondition
2. Build HP derivation [step0] + [base_steps from w1 to w3] + [suffix]
3. Call `lemma_overlap_peak_elimination` on this new derivation
4. This avoids the peak entirely

But `lemma_bubble_peak_to_front` returns `(w_base, left, right)` not `equiv(...)`. So it needs to return an actual base intermediate. The new derivation [step0, base_steps, suffix] can be processed by `lemma_overlap_peak_elimination` which proves the equiv. But `lemma_bubble_peak_to_front` needs to RETURN the split.

**Alternative:** Change `lemma_bubble_peak_to_front` to also return `(bool, ...)`. But that cascades to `lemma_scan_and_handle` which cascades to `lemma_overlap_peak_elimination`. The cascade already reaches `lemma_overlap_peak_elimination` which handles `!ok_` via the isomorphism path.

**Simplest fix:** In `lemma_bubble_peak_to_front` base case, when `!ok_`, DON'T return `(w_base, left, right)`. Instead, have a separate proof path that proves `equiv(w, w_end)` directly. Then the caller (`lemma_scan_and_handle` or `lemma_overlap_peak_elimination`) can use this equivalence.

This requires changing `lemma_bubble_peak_to_front`'s return type or ensuring convention. The cleanest: make it return `(bool, Word, Seq, Seq)` where `!ok` means "couldn't split, but equiv(w, w_end) is proved as side effect."

### Error 4: Termination in `lemma_overlap_peak_elimination`

**File:** `britton_proof_helpers3.rs`, in the `!ok_` branch of `lemma_overlap_peak_elimination` (~line 5758)

When `!ok_`, the code builds a new derivation [step0, base_steps, suffix] and calls `lemma_overlap_peak_elimination` recursively. But `base_steps` has unknown length (from `choose`), so termination can't be proved.

**Fix options:**

1. **Bound the base derivation length:** We know `equiv(data.base, w1, w3)` but don't know the derivation length. We CANNOT bound it in general.

2. **Don't recurse — prove directly:** Instead of recursing on the new derivation, prove `equiv(data.base, w, w_end)` by transitivity:
   - `equiv(data.base, w1, w3)` (from isomorphism)
   - Call `lemma_overlap_peak_elimination` on [step0] (1 step, w → w1)
   - Call `lemma_overlap_peak_elimination` on suffix (shorter than original, w3 → w_end)

   But [step0] alone proves `w → w1` in HP, not `w ≡_base w1`. And `w1` has stable letters, so `equiv(data.base, w, w1)` doesn't hold.

3. **Use the derivation structure directly:**
   - [step0] takes w (base) to w1 (count 2)
   - [suffix] takes w3 (count 2) to w_end (base)
   - These are the "brackets" of the HNN structure
   - The k=3 inside-relator analysis handles exactly this: step0 creates HNN structure, suffix removes it
   - But calling the k=3 analysis from `lemma_overlap_peak_elimination` creates a cycle

4. **Don't use fuel — prove by structural argument:**
   - The new derivation has c2 = 2 (first step after step0 is T-free base step)
   - The c2=2 case in `lemma_overlap_peak_elimination` handles T-free commutation
   - T-free commutation DOESN'T have overlapping peaks (it's base-only)
   - So the recursion terminates without hitting the overlap case
   - For termination proof: show steps.len() of new derivation < steps.len() of original
     (only works if base_steps.len() ≤ 1, which we can't guarantee)

   **Alternative:** Show count_sum of new derivation < count_sum of original.
   - Original count_sum includes 2 + 4 + 2 = 8 for the peak
   - New count_sum includes 2 + 2*m for the base steps
   - For m ≤ 2: 2 + 2*m ≤ 6 < 8. Fuel decreases! ✓
   - For m ≥ 3: fuel might not decrease

   **Practical fix:** Use `choose` with a BOUND. Instead of choosing ANY base derivation, choose one with length ≤ 2. If no such derivation exists, fall back.

   Actually, we CAN always find a derivation of bounded length! The effect of step1+step2 is inserting inv(b_j) at p1. We can construct a SPECIFIC 2-step derivation:
   - Step A: FreeExpand some symbol from inv(b_j)
   - Step B: Something else

   But inv(b_j) might have length > 2 and not decompose into 2 steps.

5. **Best approach: Directly prove equiv without recursion.**

   Since we have `equiv(data.base, w1, w3)` and the full HP derivation [step0, step1, step2, suffix], we can prove `equiv(data.base, w, w_end)` by calling the k=3 inside-relator machinery. But `lemma_overlap_peak_elimination` can't call the mutual recursion group.

   However, `lemma_single_segment_hard` CAN call both. So the fix: handle the `!ok_` case at the `lemma_single_segment_hard` level, not inside `lemma_overlap_peak_elimination`.

   In `lemma_single_segment_hard`: when `lemma_eliminate_peak_with_bypass` returns `!ok_`, call the k=3 inside-relator analysis directly (which IS in the mutual recursion group and can be called from `lemma_single_segment_hard`).

## Recommended Implementation Order

1. **Prove `equiv(w1, w3)` for the non-inverted inside-relator case** (line ~761): just call existing `lemma_overlap_ri_fr_w1_equiv_w3`. This fixes 1 of 7 false branches.

2. **Write `lemma_overlap_ri_fr_w1_equiv_w3_inverted`**: handles the inverted case. Same pattern as the non-inverted version but with inverted relator structure. Fixes 2 more false branches.

3. **Write boundary straddle equivalence helpers**: for left and right boundary cases. These require more position arithmetic but follow the same isomorphism pattern. Fixes remaining 4 false branches.

4. **Cascade the `!ok ==> equiv(w1, w3)` postcondition** through `lemma_k4_peak_noncancel_commute` and `lemma_eliminate_peak_with_bypass`.

5. **Handle `!ok_` in `lemma_single_segment_hard`** (not in `lemma_overlap_peak_elimination`): call the k=3 inside-relator analysis from the mutual recursion group. This avoids the termination issue entirely.

6. **Fix `lemma_bubble_peak_to_front`**: either change return type or handle `!ok_` via the isomorphism path directly.

## Summary

The ONE genuinely hard mathematical case is: **proving `equiv_in_presentation(data.base, w1, w3)` for each overlap sub-case of RI+FR**. This is provable using the isomorphism argument (a_j/b_j equivalence). We already have it for the simplest sub-case. We need to generalize to boundary straddles and the inverted relator case.

Once all 7 false branches prove `equiv(w1, w3)`, the rest is mechanical cascading through the call chain.
