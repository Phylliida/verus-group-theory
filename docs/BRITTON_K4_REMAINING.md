# Britton's Lemma k≥4: Remaining assume(false) — Plan to Zero

**Current state:** 550 verified, 0 errors, 13 active `assume(false)` in britton_proof.rs and britton_proof_helpers2.rs.

**All main commutation paths (before/after position cases) are proved.** The remaining gaps are edge cases (rare positions) and peak elimination (deepest math).

---

## Category 1: Edge Cases — FreeExpand step0 (2 assume(false))

**Files:** `britton_proof.rs` lines 13089-13090, 13245-13246

**What:** When step0 = FreeExpand(stable, p0) and step1 is T-free with position p1 = p0 + 1 (exactly between the two stable letters).

**Functions:**
- `lemma_k4_tfree_expand_commute_fe` — step1 = FreeExpand(base, p0+1)
- `lemma_k4_tfree_expand_commute_ri` — step1 = RelatorInsert(base, p0+1)

**Why it's tricky:** Simple commutation doesn't work here. FreeExpand(stable) at p0 creates `[sym, inv(sym)]`. The T-free step inserts between them, creating e.g. `[sym, sym1, inv(sym1), inv(sym)]`. No single adjusted FreeExpand on w' produces this interleaved structure.

**Plan:**
1. **Analyze the word structure:** w2 = w[0..p0] ++ [sym, base_stuff, inv(sym)] ++ w[p0..]. The base_stuff is the inserted T-free material.
2. **Two approaches:**
   - **Approach A (direct):** Show the combined effect of steps 0+1 is equivalent to: insert base_stuff at p0 on w (base step, giving w'), then FreeExpand(sym, p0) on w' (adjusted). This requires showing the interleaved result matches.
   - **Approach B (k=3 reuse):** The k=3 code handles this via `lemma_k3_freeexpand_gen_contra` (Gen case — contradiction) and `lemma_k3_freeexpand_inv_iso` (Inv case — isomorphism argument). For k≥4, the Gen contradiction may NOT hold (more steps available). The Inv isomorphism argument might generalize. Check if the k=3 code for these cases derives contradiction from step2, or from structure alone.
3. **Estimated effort:** Medium. Need to understand the k=3 edge case analysis and adapt or find new argument.

---

## Category 2: Edge Cases — RelatorInsert(HNN) step0 (6 assume(false))

**Files:**
- `britton_proof.rs` lines 13628, 13654, 13658 (in `lemma_k4_tfree_ri_commute_fr`)
- `britton_proof_helpers2.rs` lines 65, 134, 214 (in `_fe`, `_ri`, `_rd`)

**What:** When step0 = RelatorInsert(HNN, ri0, inv0, p0) and step1 is T-free acting INSIDE the HNN relator region [p0, p0+r0_len).

### Sub-case 2a: FreeReduce boundary (3 assume(false) in `_fr`)

**Lines:** 13628 (p1=p0-1), 13654 (p1=p0+r0_len-1), 13658 (p0 ≤ p1 < p0+r0_len)

**What:** FreeReduce at a position that spans the boundary between w's elements and the HNN relator's elements, or is entirely inside the relator.

**Plan:**
- **Boundary cases (p1=p0-1, p1=p0+r0_len-1):** The FreeReduce pair includes one element from w and one from the relator (or vice versa). Need to check if this pair is actually base (T-free requires gen_idx < n for both). If the relator element at the boundary is stable (gen_idx = n), the pair can't be base → contradiction. If the relator element is base, standard commutation applies with adjusted position.
  - For non-inverted HNN relator: r0[0] = Inv(n) (stable), so p1=p0 is impossible for T-free FreeReduce. p1=p0-1 boundary: w[p0-1] and r0[0]=Inv(n) — one is base, one stable, can't cancel → contradiction.
  - For inverted HNN relator: r0 starts with b_j elements (base). Boundary analysis depends on specific relator structure.
- **Inside relator (p0 ≤ p1 < p0+r0_len):** The FreeReduce removes a base pair from within the relator. The pair existed in the relator itself. After removal, the relator is modified. Can't directly commute (modified relator isn't a valid relator for RelatorInsert). Need different argument — possibly show this case is impossible (HNN relators might not contain cancellable base pairs in their interior), or handle by constructing a different derivation.
- **Estimated effort:** Medium-Hard. Requires understanding HNN relator internal structure.

### Sub-case 2b: FreeExpand/RelatorInsert/RelatorDelete inside (3 assume(false) in helpers2)

**Lines:** helpers2:65 (_fe), helpers2:134 (_ri), helpers2:214 (_rd)

**What:** The T-free step acts at a position p0 < p1 < p0+r0_len, inside the HNN relator region.

**Plan:**
- **FreeExpand(base) inside relator:** Inserts a base pair within the relator. The relator is now longer. Can't commute directly. Approach: show that inserting a base pair inside the relator and then inserting the modified relator is equivalent to inserting the original relator and then FreeExpand inside. This is actually commutation with the relator insert, but the T-free step acts on material that didn't exist before the relator was inserted.
- **RelatorInsert(base) inside relator:** Inserts a base relator within the HNN relator. Similar issue.
- **RelatorDelete(base) inside relator:** Deletes a base relator from within the HNN relator. The base relator is a subword of the HNN relator.
- **Common pattern:** All three are T-free steps acting on material created by the RelatorInsert(HNN). The commutation needs to "absorb" the T-free step into a modification of the base word, then re-insert the HNN relator. The key insight: since the T-free step only modifies base parts of the relator (not stable letters), the stable letter structure is preserved.
- **Alternative approach:** Prove these cases are impossible. T-free steps inside the relator require specific subword structure (cancellable pairs, relator subwords) within the HNN relator. These might not exist for valid HNN relators. If proved impossible → contradiction.
- **Estimated effort:** Hard. Requires deep HNN relator structure analysis.

---

## Category 3: Peak Elimination — k=4 Non-Cancel (1 assume(false))

**File:** `britton_proof.rs` line 14587

**What:** k=4 derivation where c_2=4 and steps 1&2 form a peak (+2 then -2), but w3 ≠ w1 (they don't cancel).

**Context already proved:**
- c_3 = 2 (forced by count4 barrier)
- step3 produces w_end from w3
- Cancel case (w3 = w1) → 2-step derivation → `lemma_base_derivation_equiv` ✓

**Plan for non-cancel case:**
1. Step 1 introduces 2 stable letters (A, A') at some position in w1.
2. Step 2 removes 2 stable letters from w2 (which has 4: the 2 from step0 + 2 from step1).
3. Since w3 ≠ w1 (non-cancel), step 2 removes DIFFERENT stable letters than what step 1 introduced. Specifically, step 2 removes the stable letters from step 0.
4. **Commutation:** Apply step 2 (adjusted) to w1 BEFORE step 1:
   - step2' on w1 (count 2) → w1' (count 0 = BASE!)
   - step1' on w1' → w3
5. **Construct two 2-step derivations:**
   - [step0, step2'] from w (base) to w1' (base): 2 steps → `lemma_single_segment_k2` or `lemma_base_derivation_equiv`
   - [step1', step3] from w1' (base) to w_end (base): 2 steps → `lemma_base_derivation_equiv`
   - Chain: w ≡ w1' ≡ w_end

**Implementation:**
- Match on step1 type (FreeExpand(stable) or RelatorInsert(HNN)) × step2 type (FreeReduce(stable) or RelatorDelete(HNN)) → 4 combinations.
- For each: analyze position relationship between step1's insertion and step2's removal.
- Position cases:
  - Non-overlapping: step2 removes from a region not affected by step1. Adjust positions.
  - Overlapping: step2 removes elements that include parts of step1's insertion. This would mean step2 acts on the SAME stable letters → should be the cancel case (w3=w1).
- So non-cancel implies non-overlapping → standard position adjustment works.
- **Key insight:** The non-cancel case is actually SIMPLER than it seems — non-cancel means the steps act on different positions, which is exactly when commutation works.

**Estimated effort:** Medium. 4 sub-cases of position arithmetic, similar to existing commutation helpers. Can reuse the module splitting pattern. Need to be careful with the `lemma_base_derivation_equiv` call (decreases must work).

---

## Category 4: Peak Elimination — k≥5 (1 assume(false))

**File:** `britton_proof.rs` line 14605

**What:** k≥5 derivation where c_2=4 and c_1=2. All intermediates non-base.

**Plan — several approaches:**

### Approach A: Commute from the end
Mirror the front-commutation for the last two steps:
- c_{k-1} = 2 always. Check c_{k-2}: if c_{k-2} = 2, step k-2 is T-free.
- Commute step k-2 (T-free) past step k-1 (reducing) — same position arithmetic as front commutation but mirrored.
- Produces base w' from the last two steps, reducing to a (k-1)-step problem.
- **Issue:** Requires "commute from end" infrastructure (mirror of front commutation). ~8 new helpers.

### Approach B: Recursive peak reduction
Find the first descent in the count sequence and commute:
- Among steps 1..k-2, find the first step j where Δ_j = -2 (count decreases).
- Steps j-1 and j form a local peak. Commute step j backward past step j-1.
- If j=2: commuting creates base intermediate at w_1 (count 2→0). Split there.
- If j>2: commuting creates a lower intermediate count. Recurse.
- **Termination measure:** (steps.len(), count_sum) where count_sum = Σ c_i decreases with each commutation.

### Approach C: Observe that k≥5 with c_2=4 implies ∃ T-free interior step
- For odd k≥5: by parity argument, there MUST be a T-free step among interior steps. Commute it.
- For even k≥4: might not have T-free interior step. But k=4 is handled separately.
- For even k≥6 with no T-free step: all interior changes are ±2. Count sequence oscillates. There's a peak somewhere that can be reduced.

### Recommended: Approach A (commute from end)
Most mechanical and closest to existing code. Requires:
1. Check c_{k-2} via stable count of w_{k-2} = derivation_word_at(steps, w, k-2).
2. If T-free: construct mirror commutation helpers.
3. If not T-free (c_{k-2} = 4): use Approach C for odd k (guaranteed T-free exists) or Approach B for even k.
4. Recursive: `lemma_single_segment_hard` called with k-1 steps (decreases works since k-1 < k).

**Estimated effort:** Hard. Mirror commutation is ~8 helpers × ~50 lines each = ~400 lines. Plus the recursive argument for the no-T-free case.

---

## Summary & Priority Order

| Priority | Category | assume(false) | Effort | Impact |
|----------|----------|---------------|--------|--------|
| 1 | k=4 peak non-cancel | 1 | Medium | High — closes k=4 |
| 2 | k≥5 peak | 1 | Hard | High — closes general case |
| 3 | RI(HNN) FR boundary | 3 | Medium | Medium — edge cases |
| 4 | FE p1=p0+1 edge | 2 | Medium | Low — rare position |
| 5 | RI(HNN) inside relator | 6 | Hard | Low — very rare |

**Total estimated new code:** ~800-1200 lines across britton_proof.rs and helper modules.

**Architectural notes:**
- All commutation helpers return `(w', step1_base, step0_adj)` tuples — NOT in the mutual recursion group.
- Only `lemma_single_segment_hard` calls `lemma_base_derivation_equiv` (decreases: steps.len(), 0nat).
- Module splitting essential for rlimit: put heavy helpers in britton_proof_helpers2.rs or a new helpers3.rs.
- Key Z3 hint for baseness proofs: must explicitly chain `w =~= left + right`, `count(left+right) == 0`, then `count(w_prime) == 0`.
