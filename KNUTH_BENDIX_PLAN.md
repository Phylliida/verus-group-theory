# Verified Knuth-Bendix Completion for Group Presentations

## Goal

Implement a formally verified Knuth-Bendix (KB) completion algorithm in Verus,
operating on finitely presented groups. When the algorithm terminates, it produces
a confluent, terminating string rewriting system equivalent to the input
presentation — giving a verified decision procedure for the word problem.

## Background

Given a presentation `⟨S | R⟩`, the word problem asks: are two words over `S`
equal in the presented group? KB solves this (when it terminates) by:

1. Orienting the relators as rewrite rules `lhs → rhs` using a reduction ordering
   (shortlex is standard for groups).
2. Computing **critical pairs** — overlaps between rule left-hand sides.
3. Reducing both sides of each critical pair to normal forms.
4. If the normal forms differ, adding a new oriented rule.
5. Repeating until no new rules are generated (the system is confluent).

The key theorem: a terminating, confluent rewriting system gives unique normal
forms, so two words are equal in the group iff they have the same normal form.

## Existing Infrastructure

The codebase already provides strong foundations:

| What | Where | Relevance |
|------|-------|-----------|
| Free reduction + confluence (Newman's lemma) | `reduction.rs` | Direct template for generalized Newman's lemma |
| Presentations, derivations, equivalence | `presentation.rs` | Semantic ground truth for rewrite system correctness |
| Tietze transformations | `tietze.rs` | Adding/removing relators with correctness — KB rules are oriented relators |
| Equivalence-preserving concat | `presentation_lemmas.rs` | `lemma_equiv_concat_left/right` — core of soundness proof |
| Homomorphisms preserve equivalence | `homomorphism.rs` | Pattern for proving rewrite steps preserve group equality |
| Free reduction → presentation equiv | `presentation_lemmas.rs` | `lemma_freely_equivalent_implies_equiv` bridges free and presented |
| Runtime word manipulation | `runtime.rs` | `reduce_word_exec` etc. — exec patterns to follow |
| Word/Symbol basics | `word.rs`, `symbol.rs` | Concat, inverse, validity, all with lemmas |
| Todd-Coxeter coset enumeration | `todd_coxeter.rs` | Independent verification oracle; also useful for testing |

### The confluence proof pattern (reduction.rs)

This is the single most important existing piece. The current proof structure:

```
lemma_confluence            — Newman's lemma: termination + local confluence → confluence
  ├── by induction on |w| (word length decreases by 2 each step)
  └── lemma_local_confluence   — if w →¹ w₁ and w →¹ w₂ then joinable
        ├── same position: trivial (w₁ = w₂)
        ├── lemma_overlapping_confluence — adjacent positions (|i-j| = 1)
        └── lemma_disjoint_confluence   — separated positions (|i-j| ≥ 2)
```

KB correctness follows this exact pattern, generalized from "cancel inverse pair
at position i" to "apply rule r at position i".

## Architecture

Six layers, each building on the previous:

```
┌─────────────────────────────────────────────────┐
│  Layer 6: Completion Procedure (exec + proof)   │  knuth_bendix.rs
│  - Main loop: find critical pairs, orient, add  │
│  - Partial correctness: if terminates, correct   │
├─────────────────────────────────────────────────┤
│  Layer 5: Critical Pair Lemma                   │  critical_pairs.rs
│  - Overlap detection between rules              │
│  - All CPs joinable ↔ locally confluent         │
│  - Case split: disjoint / overlapping / nested  │
├─────────────────────────────────────────────────┤
│  Layer 4: Generalized Newman's Lemma            │  newman.rs
│  - Terminating + locally confluent → confluent  │
│  - Well-founded induction on reduction ordering │
├─────────────────────────────────────────────────┤
│  Layer 3: Soundness & Completeness              │  rewrite_sound.rs
│  - Rule application preserves group equivalence │
│  - Confluent system decides word problem        │
├─────────────────────────────────────────────────┤
│  Layer 2: Rewrite System                        │  rewrite.rs
│  - Rules, rule application at positions         │
│  - Subword matching, one-step/multi-step rewrite│
│  - Irreducibility, normal forms                 │
├─────────────────────────────────────────────────┤
│  Layer 1: Reduction Ordering (Shortlex)         │  shortlex.rs
│  - shortlex_lt on Words                         │
│  - Well-foundedness, totality                   │
│  - Compatibility with concatenation             │
└─────────────────────────────────────────────────┘
```

## Layer Details

### Layer 1: Shortlex Ordering (`shortlex.rs`)

**Definitions:**

```rust
//  Compare words: shorter is smaller; equal length → lexicographic by generator index
pub open spec fn shortlex_lt(w1: Word, w2: Word) -> bool {
    w1.len() < w2.len() || (w1.len() == w2.len() && lex_lt(w1, w2))
}

//  Lexicographic comparison using a total order on symbols
//  Symbols ordered: Gen(0) < Inv(0) < Gen(1) < Inv(1) < ...
pub open spec fn symbol_ord(s: Symbol) -> nat;
pub open spec fn lex_lt(w1: Word, w2: Word) -> bool;
```

**Key lemmas (~300-500 lines):**

- `lemma_shortlex_irreflexive` — `¬ shortlex_lt(w, w)`
- `lemma_shortlex_transitive` — standard
- `lemma_shortlex_total` — any two distinct words are comparable
- `lemma_shortlex_well_founded` — no infinite descending chain; encode as:
  `shortlex_lt(w1, w2) → shortlex_rank(w1) < shortlex_rank(w2)` where rank is a nat
- `lemma_shortlex_compatible_concat` — `shortlex_lt(u, v) → shortlex_lt(w·u·x, w·v·x)`
  This is the **reduction ordering** property. It holds because:
  - If `|u| < |v|` then `|wux| < |wvx|`
  - If `|u| = |v|` and `lex_lt(u, v)` then `lex_lt(wux, wvx)` (same prefix/suffix)
- `lemma_shortlex_inverse_compatible` — `shortlex_lt(u, v) → shortlex_lt(inv(v), inv(u))`
  Needed for orienting rules from relators like `w = ε` → the larger half rewrites to smaller.

**Shortlex rank (for well-founded induction):**

The rank of a word is its position in the shortlex enumeration. For an alphabet of
size `2n` (n generators + n inverses):

```
rank(w) = Σ_{k=0}^{|w|-1} (2n)^k + position_in_length_class(w)
```

This is a nat, so Verus's `decreases` clause works directly. Alternatively, use
a two-component `decreases (w.len(), lex_rank(w))` which Verus handles via
lexicographic tuples.

### Layer 2: Rewrite System (`rewrite.rs`)

**Definitions:**

```rust
pub struct RewriteRule {
    pub lhs: Word,  //  left-hand side (the larger word)
    pub rhs: Word,  //  right-hand side (the smaller word)
}

pub struct RewriteSystem {
    pub rules: Seq<RewriteRule>,
}

//  Rule is well-formed: lhs is strictly greater in the ordering
pub open spec fn rule_wf(rule: RewriteRule) -> bool {
    shortlex_lt(rule.rhs, rule.lhs) && rule.lhs.len() > 0
}

//  Subword match: w[pos..pos+lhs.len()] == rule.lhs
pub open spec fn matches_at(w: Word, rule: RewriteRule, pos: int) -> bool {
    pos >= 0 && pos + rule.lhs.len() <= w.len()
    && w.subrange(pos, pos + rule.lhs.len()) == rule.lhs
}

//  Apply rule at position: replace lhs with rhs
pub open spec fn apply_rule_at(w: Word, rule: RewriteRule, pos: int) -> Word {
    w.subrange(0, pos) + rule.rhs + w.subrange(pos + rule.lhs.len(), w.len() as int)
}

//  One-step rewrite: exists a rule and position
pub open spec fn rewrites_one_step(sys: RewriteSystem, w1: Word, w2: Word) -> bool;

//  Multi-step rewrite (transitive-reflexive closure)
pub open spec fn rewrites_to(sys: RewriteSystem, w1: Word, w2: Word) -> bool;

//  No rule applies
pub open spec fn is_irreducible(sys: RewriteSystem, w: Word) -> bool;

//  Normal form under the rewrite system
pub open spec fn rewrite_normal_form(sys: RewriteSystem, w: Word) -> Word;
```

**Key lemmas (~400-600 lines):**

- `lemma_apply_rule_at_len` — resulting word length = `|w| - |lhs| + |rhs|`
- `lemma_rule_wf_decreases` — `rule_wf(r) ∧ matches_at(w,r,i) → shortlex_lt(apply_rule_at(w,r,i), w)`
  Critical: each rewrite step makes the word strictly smaller in shortlex.
- `lemma_rewrite_concat_left` — rewriting in `w` lifts to `u·w`
- `lemma_rewrite_concat_right` — rewriting in `w` lifts to `w·v`
- `lemma_rewrites_to_refl` — reflexivity
- `lemma_rewrites_to_transitive` — transitivity

**Note on subword matching:** This is where `Seq::subrange` does the heavy lifting.
The existing `reduce_at` in `reduction.rs` is the special case where `lhs = [s, inv(s)]`
and `rhs = []`. The generalization is straightforward.

### Layer 3: Soundness (`rewrite_sound.rs`)

**Definitions:**

```rust
//  A rewrite system is sound for a presentation if every rule lhs ≡ rhs
pub open spec fn system_sound(sys: RewriteSystem, p: Presentation) -> bool {
    forall|i: int| 0 <= i < sys.rules.len() ==>
        equiv_in_presentation(p, sys.rules[i].lhs, sys.rules[i].rhs)
}

//  A rewrite system is complete if equivalent words have the same normal form
pub open spec fn system_complete(sys: RewriteSystem, p: Presentation) -> bool {
    forall|w1: Word, w2: Word|
        equiv_in_presentation(p, w1, w2) ==>
        rewrite_normal_form(sys, w1) == rewrite_normal_form(sys, w2)
}
```

**Key lemmas (~200-400 lines):**

- `lemma_rule_preserves_equiv` — if `system_sound(sys, p)` and `rewrites_one_step(sys, w1, w2)`
  then `equiv_in_presentation(p, w1, w2)`.
  Proof: `w1 = u·lhs·v`, `w2 = u·rhs·v`, `lhs ≡ rhs` in p, use `lemma_equiv_concat_left/right`.
- `lemma_rewrite_preserves_equiv` — extends to multi-step by induction.
- `lemma_confluent_decides_word_problem` — if confluent and sound, then:
  `equiv_in_presentation(p, w1, w2) ↔ rewrite_normal_form(sys, w1) == rewrite_normal_form(sys, w2)`

The hard direction (completeness: if `w1 ≡ w2` then same normal form) requires showing
that derivation steps in the presentation can be simulated by the rewrite system.
This is where the initial rule set must include oriented versions of all relators
AND the free reduction rules (`s·s⁻¹ → ε`).

**Important design choice:** Include the free cancellation rules `Gen(i)·Inv(i) → ε`
and `Inv(i)·Gen(i) → ε` as permanent rules in every system. These are always
terminating (they shorten the word) and always sound. This means the rewrite
system subsumes free reduction, and we can reuse `lemma_freely_equivalent_implies_equiv`.

### Layer 4: Generalized Newman's Lemma (`newman.rs`)

**Statement:**

```rust
proof fn lemma_newman(sys: RewriteSystem, w: Word, w1: Word, w2: Word)
    requires
        system_terminating(sys),      //  all rules decrease shortlex
        system_locally_confluent(sys), //  all local forks are joinable
        rewrites_to(sys, w, w1),
        rewrites_to(sys, w, w2),
    ensures
        exists|w3: Word| rewrites_to(sys, w1, w3) && rewrites_to(sys, w2, w3)
    decreases shortlex_rank(w)        //  or (w.len(), lex_rank(w))
```

**Proof sketch (follows `lemma_confluence` in reduction.rs):**

```
If w = w1 or w = w2: trivial.
Otherwise: w →¹ w1' →* w1  and  w →¹ w2' →* w2.
By local confluence on (w →¹ w1', w →¹ w2'):
  ∃ w'. w1' →* w' ∧ w2' →* w'.
Since w →¹ w1' means shortlex_rank(w1') < shortlex_rank(w), apply IH:
  w1' →* w1 and w1' →* w' are joinable → ∃ w3. w1 →* w3 ∧ w' →* w3.
  w2' →* w2 and w2' →* w' are joinable → ∃ w4. w2 →* w4 ∧ w' →* w4.
Chain: w1 →* w3, w2 →* w4, and w3, w4 both reachable from w'.
Apply IH again to join w3 and w4.
```

**Difficulty:** ~400-800 lines. The main challenge is encoding the well-founded
induction. Two approaches:

1. **Nat encoding**: Define `shortlex_rank(w) -> nat` and use `decreases shortlex_rank(w)`.
   The rank is bounded by `(2n)^(|w|+1)` which is computable. Need to prove
   `rewrites_one_step(sys, w, w') → shortlex_rank(w') < shortlex_rank(w)`.

2. **Lexicographic decreases**: Use `decreases w.len(), lex_rank(w)`. Since rule
   application either decreases length (most rules) or preserves length and
   decreases lex rank (length-preserving rules from length-equal relators, rare),
   this works naturally.

Option 2 is cleaner. Verus supports lexicographic `decreases` tuples.

### Layer 5: Critical Pairs (`critical_pairs.rs`)

This is the largest and most novel layer.

**Definitions:**

```rust
//  An overlap: a suffix of r1.lhs of length `overlap` matches a prefix of r2.lhs
//  where 1 ≤ overlap ≤ min(|r1.lhs|, |r2.lhs|)
pub open spec fn is_overlap(r1: RewriteRule, r2: RewriteRule, overlap: nat) -> bool {
    overlap >= 1
    && overlap <= r1.lhs.len()
    && overlap <= r2.lhs.len()
    && r1.lhs.subrange(r1.lhs.len() - overlap, r1.lhs.len())
       == r2.lhs.subrange(0, overlap)
}

//  The critical pair from an overlap:
//  The overlapping word is: r1.lhs + r2.lhs[overlap..]
//  Applying r1 gives: r1.rhs + r2.lhs[overlap..]
//  Applying r2 gives: r1.lhs[..len-overlap] + r2.rhs
pub open spec fn critical_pair(
    r1: RewriteRule, r2: RewriteRule, overlap: nat
) -> (Word, Word);

//  An inclusion: r2.lhs appears as a subword of r1.lhs at position pos
pub open spec fn is_inclusion(r1: RewriteRule, r2: RewriteRule, pos: nat) -> bool {
    pos + r2.lhs.len() <= r1.lhs.len()
    && r1.lhs.subrange(pos, pos + r2.lhs.len()) == r2.lhs
}

//  The critical pair from an inclusion:
//  Applying r1 to the whole word gives: r1.rhs
//  Applying r2 at position pos gives: r1.lhs[..pos] + r2.rhs + r1.lhs[pos+|r2.lhs|..]
pub open spec fn inclusion_critical_pair(
    r1: RewriteRule, r2: RewriteRule, pos: nat
) -> (Word, Word);

//  All critical pairs are joinable under the system
pub open spec fn all_critical_pairs_joinable(sys: RewriteSystem) -> bool;
```

**The Critical Pair Lemma:**

```rust
proof fn lemma_critical_pair_lemma(sys: RewriteSystem)
    requires
        system_terminating(sys),
        all_critical_pairs_joinable(sys),
    ensures
        system_locally_confluent(sys)
```

**Proof structure (mirrors `lemma_local_confluence` in reduction.rs):**

Given `w →¹ w₁` via rule `r₁` at position `p₁` and `w →¹ w₂` via rule `r₂` at
position `p₂`, there are three cases for how the match regions relate:

```
Case 1: Disjoint
  w = ...[ r1.lhs ]...[ r2.lhs ]...
  Both rewrites commute. Apply r1 then r2 (or vice versa) to reach common reduct.
  (Analogous to lemma_disjoint_confluence)

Case 2: Overlap
  w = ...[ r1.lhs    ]
              [ r2.lhs    ]...
  The overlapping portion generates a critical pair. Since it's joinable by
  hypothesis, the surrounding context can be added back via concat lemmas.
  (Analogous to lemma_overlapping_confluence)

Case 3: Inclusion
  w = ...[ r1.lhs              ]...
         ...[ r2.lhs ]...
  r2's match is inside r1's match. This is an inclusion critical pair.
  (New case — free reduction doesn't have this because all rules are length 2)
```

**Estimated size:** ~800-1500 lines. The disjoint case is straightforward (similar
to existing). The overlap case requires careful index arithmetic on `Seq::subrange`.
The inclusion case is new but follows the same pattern.

### Layer 6: Completion Procedure (`knuth_bendix.rs`)

**Exec implementation:**

```rust
exec fn orient_rule(lhs: Word, rhs: Word) -> RewriteRule
    requires shortlex_lt(rhs, lhs) || shortlex_lt(lhs, rhs)
    ensures rule_wf(result)

exec fn compute_critical_pairs(sys: &RewriteSystem) -> Vec<(Word, Word)>
    ensures forall pairs appear in result

exec fn reduce_to_normal_form(sys: &RewriteSystem, w: &Word) -> Word
    ensures rewrites_to(sys, w, result) && is_irreducible(sys, result)

exec fn knuth_bendix(p: &Presentation, max_rules: usize) -> Option<RewriteSystem>
    ensures
        result.is_some() ==> {
            let sys = result.unwrap();
            system_sound(sys, p)
            && system_terminating(sys)
            && system_confluent(sys)
            //  Therefore decides the word problem for p
        }
```

**The main loop:**

```
1. Initialize rules from relators:
   For each relator w in p.relators:
     If w = u·v where u > v in shortlex: add rule u → v
     (For group relators w = ε: orient as w → ε if |w| > 0)
   Also add free cancellation rules: Gen(i)·Inv(i) → ε, Inv(i)·Gen(i) → ε

2. Repeat:
   a. Pick an unprocessed critical pair (w₁, w₂)
   b. Reduce both to normal forms: nf₁ = reduce(w₁), nf₂ = reduce(w₂)
   c. If nf₁ ≠ nf₂:
      Orient: if nf₁ > nf₂, add rule nf₁ → nf₂, else add nf₂ → nf₁
      Recompute critical pairs involving the new rule
   d. If no unprocessed pairs remain: done (confluent)
   e. If max_rules exceeded: return None

3. Interreduce: simplify existing rules using new ones (optional optimization)
```

**Loop invariant (proof obligation):**

At each iteration:
- `system_sound(sys, p)` — every rule `lhs ≡ rhs` in the presentation
- `system_terminating(sys)` — every rule has `shortlex_lt(rhs, lhs)`
- All processed critical pairs are joinable

When the loop exits with no unprocessed pairs: all critical pairs joinable →
locally confluent (Layer 5) → confluent (Layer 4) → decides word problem (Layer 3).

## Suggested Build Order

1. **Layer 1** (shortlex) — no dependencies, can start immediately
2. **Layer 2** (rewrite system) — depends on Layer 1 for `rule_wf`
3. **Layer 3** (soundness) — depends on Layer 2 + existing `presentation.rs`
4. **Layer 4** (Newman) — depends on Layer 2 + Layer 1 well-foundedness
5. **Layer 5** (critical pairs) — depends on Layer 2, hardest layer
6. **Layer 6** (completion) — depends on everything

Layers 1-3 could be done in parallel with Layer 4. Layer 5 is the critical path.

## Testing Strategy

Before attempting the full verification of each layer, test exec implementations
against known examples:

- **Trivial group** `⟨a | a⟩`: should produce `{a → ε}`, confluent immediately
- **Cyclic group** `⟨a | a³⟩`: should produce `{a³ → ε, a² → a⁻¹}` (or similar)
- **Dihedral group** `⟨a,b | a², b², (ab)³⟩`: KB terminates, 6 rules
- **Free abelian** `⟨a,b | aba⁻¹b⁻¹⟩`: KB terminates, produces commutation rules
- **Braid group B₃** `⟨a,b | aba = bab⟩`: KB terminates with ~6-8 rules

The existing `concrete.rs` already defines cyclic and dihedral presentations, and
`todd_coxeter.rs` can independently verify the group orders.

## Open Questions

1. **Interreduction:** Should we verify the interreduction step (simplifying
   existing rules when a new rule is added)? It's an optimization that reduces
   the rule set but isn't needed for correctness. Probably skip for v1.

2. **Rule selection strategy:** The order in which critical pairs are processed
   affects termination speed. Verify a simple FIFO strategy first.

3. **Infinite systems:** Some groups (e.g., `Z × Z`) have infinite confluent
   rewriting systems. Could we support "lazy" KB that produces a finite prefix
   sufficient for specific word problem instances? This would be a significant
   extension.

4. **Connection to decidability.rs:** The existing `decide_word_problem_exec`
   uses Todd-Coxeter. A KB-based decision procedure would be a second verified
   algorithm. Should they share an interface/trait?

## Estimated Effort

~2500-4600 lines of Verus spec+proof+exec, comparable to a medium subsystem in
the existing codebase. The Britton's lemma proof (`britton_proof.rs`) is ~14k lines
for reference, so this is well within demonstrated capability.

The proof patterns needed are all present in the codebase — this is primarily a
generalization and assembly project, not a fundamentally new proof technique.
