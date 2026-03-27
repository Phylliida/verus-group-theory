# Full Britton's Lemma (Pinch Theorem) — Completion Plan

## Reference
- Miller, "Combinatorial Group Theory," Theorem 3.10 (pages 45-49)

## Current Status

**127 verified lemmas, 2 `assert(false)` gaps remaining.**

File: `verus-group-theory/src/britton_via_tower.rs` (Part X = infrastructure, Part Y = textbook proof)

### What's done (verified):
- Part X: All infrastructure (116 lemmas) — tower, AFP, subgroups, level analysis, pairs
- Y.1: textbook_g2_action, textbook_g1_action (always prepend, never merge)
- Y.2: Length properties (rep ≠ ε → length + 1)
- Y.3: Agreement with existing one-shots when top has opposite type
- Y.4: Segment decomposition specs (stable_count, last_stable_pos, trailing_segment, leading_part)
- Y.5: Segment properties (partition, trailing no stable, last_stable_pos bounds, no_stable helpers)
- Y.5 partial: lemma_leading_part_props — first two ensures verified (len > 0, last is stable), third needs stable_count connection

### What's next:
- Finish lemma_leading_part_props: prove stable_count(leading_part.drop_last()) == stable_count(w) - 1
- Then tasks G, D, H, I, J from the plan below

## The Textbook Proof (Miller pp.45-49)

### The Permutation Representation (p.48-49)

θ⋆ψ : G* → Sym(Ω) where Ω = set of normal forms.

**θ(g)**: left-multiply leading coefficient g₀.

**ψ(p)** on g₀·p^{ε₁}·g₁·...·gₘ where g₀ = b·z₀ (B-coset, b ∈ B, z₀ ∈ Z):
- z₀ ≠ ε OR ε₁ = +1: **PREPEND** a·p·z₀ before rest
- z₀ = ε AND ε₁ = -1: **COLLAPSE** to (a·g₁)·p^{ε₂}·...

**ψ(p⁻¹)** symmetric with A-coset.

Key: ψ(p) either PREPENDS (length +1) or COLLAPSES (length -1). **Never merges.**

### The Core Argument

For p-reduced word: coset rep always non-trivial → always PREPEND → never COLLAPSE.
After m stable letters: length m ≥ 1. Non-trivial. Contradiction with w ≡ ε.

## Why Our Current Formalization Differs

Our `g2_one_shot_action` has THREE branches:
1. rep = ε: ABSORB (length unchanged)
2. rep ≠ ε, top left/empty: **PREPEND** (length +1) ← matches textbook
3. rep ≠ ε, top right: **MERGE** (length 0 or -1) ← NOT in textbook

Branch 3 (MERGE) is an artifact of our canonical state representation. The textbook
always prepends when rep ≠ ε, allowing consecutive same-type syllables. Our canonical
states force merging.

**Rather than proving merge never happens (the alternation invariant), we should
define a textbook-faithful action that always prepends, matching the textbook exactly.**

## Infrastructure Plan

### A. Textbook-Faithful Actions (~20 lines)

Define new spec functions that match the textbook's ψ(p) and ψ(p⁻¹) exactly:

```rust
/// Textbook's ψ(p): always PREPEND when rep ≠ ε, ABSORB when rep = ε.
/// Never merges. Matches Miller p.49 Cases 1+2 (prepend) and Case 3 (collapse).
pub open spec fn textbook_g2_action(
    data: AmalgamatedData, g: Word, syls: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let rep = b_rcoset_rep(data, g);
    let h_new = b_rcoset_h(data, g);
    if rep =~= empty_word() {
        (h_new, syls)  // ABSORB (textbook Case 3)
    } else {
        // PREPEND (textbook Cases 1+2) — always, regardless of top type
        (h_new, Seq::new(1, |_| Syllable { is_left: false, rep: rep }) + syls)
    }
}

/// Textbook's ψ(p⁻¹): symmetric for G₁/A-coset.
pub open spec fn textbook_g1_action(
    data: AmalgamatedData, g: Word, syls: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let rep = a_rcoset_rep(data, g);
    let h_new = a_rcoset_h(data, g);
    if rep =~= empty_word() {
        (h_new, syls)  // ABSORB
    } else {
        // PREPEND — always
        (h_new, Seq::new(1, |_| Syllable { is_left: true, rep: rep }) + syls)
    }
}
```

Maps to: Miller p.49, ψ(p) and ψ(p⁻¹) exactly.

### B. Length Property for Textbook Actions (~15 lines)

Trivial with prepend-only:

```rust
/// rep ≠ ε → length increases by 1. rep = ε → length unchanged.
proof fn lemma_textbook_g2_length(data, g, syls)
    ensures
        if !(b_rcoset_rep(data, g) =~= empty_word()) {
            textbook_g2_action(data, g, syls).1.len() == syls.len() + 1
        } else {
            textbook_g2_action(data, g, syls).1.len() == syls.len()
        }

/// Symmetric for G₁.
proof fn lemma_textbook_g1_length(data, g, syls)
```

Maps to: The textbook's "each stable letter adds 1 to the length."

### C. Connection to Existing act_word (~20 lines)

Show the textbook action agrees with our existing one-shots when the top has
opposite type (or is empty). This lets us reuse `lemma_act_word_deriv` (well-definedness).

```rust
/// When top is left/empty: textbook_g2 = g2_one_shot (both prepend).
proof fn lemma_textbook_g2_agrees_prepend(data, g, syls)
    requires syls.len() == 0 || syls.first().is_left
    ensures textbook_g2_action(data, g, syls) == g2_one_shot_action(data, g, syls)

/// When top is right/empty: textbook_g1 = g1_one_shot (both prepend).
proof fn lemma_textbook_g1_agrees_prepend(data, g, syls)
    requires syls.len() == 0 || !syls.first().is_left
    ensures textbook_g1_action(data, g, syls) == g1_one_shot_action(data, g, syls)
```

Maps to: Connecting our formalization to the existing verified infrastructure.

### D. Textbook Action on Full Segments (~20 lines)

Process a full base segment (a Word of base symbols) through the textbook action,
analogous to `lemma_act_word_eq_g2_one_shot`.

```rust
/// Processing a full G₂ segment via textbook action = textbook_g2_action on the product.
proof fn lemma_textbook_g2_segment(data, base_word, h, syls)
    ensures
        // act_word using textbook semantics on shift(base_word)
        // = textbook_g2_action(concat(base_word, embed_b(h)), syls)

/// Symmetric for G₁.
proof fn lemma_textbook_g1_segment(data, base_word, h, syls)
```

Maps to: The textbook's processing of one gᵢ element.

### E. HNN Word Segment Decomposition (~40 lines)

The textbook's g₀·s₁·g₁·...·sₘ·gₘ structure, formalized:

```rust
/// Number of stable letters in w.
pub open spec fn stable_count(data, w) -> nat

/// The k-th base segment (0 ≤ k ≤ stable_count).
pub open spec fn kth_segment(data, w, k) -> Word

/// Level of the k-th segment.
pub open spec fn kth_segment_level(data, w, bl, k) -> int
```

Maps to: The textbook's p-expression structure.

### F. Segment Properties (~30 lines)

```rust
/// Each segment is a base word.
proof fn lemma_segment_is_base(data, w, k)

/// Segments + stable letters partition w.
proof fn lemma_segments_partition(data, w)

/// translate(w, bl) = concat of shift(segₖ, levelₖ * ng)
proof fn lemma_translate_segments(data, w, bl)
```

Maps to: The textbook's implicit use of p-expression structure.

### G. p-Reduced → Non-Trivial Coset Reps (~25 lines)

```rust
/// For segment at max level (between Gen-Inv): ∉ B.
proof fn lemma_segment_not_in_B(data, w, k)
    requires !has_pinch(w), segment is at max level
    ensures !in_right_subgroup(afp, kth_segment(data, w, k))

/// For inter-visit segment (between Inv-Gen): ∉ A.
proof fn lemma_segment_not_in_A(data, w, k)
    requires !has_pinch(w), segment is inter-visit
    ensures !in_left_subgroup(afp, kth_segment(data, w, k))
```

Maps to: "coset representative is non-trivial" for p-reduced words.

### H. Main Inductive Lemma (~40 lines)

The textbook proof, directly:

```rust
proof fn lemma_textbook_nontrivial(data, w, bl, pl, h, syls)
    requires !has_pinch(w), stable_count(w) >= 1
    ensures
        // Using textbook actions: syls.len() increases by stable_count
        result_syls.len() >= syls.len() + stable_count(w)
    decreases stable_count(w)
{
    // Decompose w = prefix · last_stable · last_segment
    // Process last_segment via textbook action (D):
    //   rep ≠ ε (from G, p-reduced) → PREPEND → length + 1
    // Process prefix by IH (stable_count - 1):
    //   length + (stable_count - 1)
    // Total: syls.len() + stable_count ✓
}
```

Maps to: Miller p.49, "it is clear that θ⋆ψ(nf)(1) = nf."

### I. Connect Textbook Action to act_word (~25 lines)

For p-reduced words processed from (ε, []), the textbook action and act_word
give the same result. This is because the textbook action always prepends,
and with alternating syllable types, the existing one-shot also prepends
(the merge branch is never reached).

But we don't even NEED this connection for the contradiction! We just need:
1. textbook_action is well-defined on G* (respects relations)
2. textbook_action(translate(w), ε, []).1.len() ≥ 1 (from H)
3. w ≡ ε → textbook_action gives identity → length = 0
4. Contradiction: 0 ≥ 1

For (1): show textbook_action agrees with act_word on the specific translate
of a p-reduced word, then reuse act_word's well-definedness.

Actually, the simplest connection: for a p-reduced word from (ε, []), the
syllables will alternate (right from G₂, left from G₁). With alternating
syllables, the textbook action and canonical one-shot agree (both prepend).
So textbook_action(translate(w)) = act_word(translate(w)).

```rust
proof fn lemma_textbook_equals_act_word_for_p_reduced(data, w, bl, pl)
    requires !has_pinch(w)
    ensures
        textbook_process(translate(w, bl), ε, [])
            == act_word(afp, translate(w, bl), ε, [])
```

Then: act_word gives (ε, []) (from w ≡ ε). So textbook gives (ε, []).
But textbook gives length ≥ 1 (from H). Contradiction.

Maps to: Connecting the textbook's θ⋆ψ to our verified act_word.

### J. Final Assembly (~30 lines)

```rust
proof fn lemma_case_a_contradiction(data, w)  // max_prefix_level ≥ 1
proof fn lemma_case_b_contradiction(data, w)  // max_prefix_level = 0 (symmetric)
pub proof fn britton_lemma_full(data, w)       // case split
```

## Implementation Order

1. **A**: textbook_g2_action, textbook_g1_action specs (~20 lines)
2. **B**: length properties (~15 lines)
3. **C**: agreement with one-shots when top has opposite type (~20 lines)
4. **E**: segment decomposition specs (~40 lines)
5. **F**: segment properties (~30 lines)
6. **G**: p-reduced → non-trivial reps (~25 lines)
7. **D**: textbook action on full segments (~20 lines)
8. **H**: main induction (~40 lines)
9. **I**: connect to act_word (~25 lines)
10. **J**: final assembly (~30 lines)

**Total: ~265 lines**

## Shortcuts to Avoid

1. **Don't merge same-type syllables** — use textbook_g2/g1_action which always prepend
2. **Don't decompose at a specific pair** — use segment infrastructure, process all pairs uniformly
3. **Don't find special pairs** — the induction on stable_count handles all pairs
4. **Don't track only right_count** — track total syls.len(), which increases by 1 per stable letter
5. **Don't work with flat words** — use segment decomposition throughout
6. **Don't skip the well-definedness connection** — need textbook_action = act_word for p-reduced
7. **Don't try to prove alternation separately** — it falls out automatically from the prepend-only action
