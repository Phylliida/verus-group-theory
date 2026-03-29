# ZFC-Encoding Group: Full Pipeline Design

## Goal

Construct (in verified Rust/Verus) a finitely generated group G with generator
set A, and a computable function f from first-order set-theory sentences to
words on A, such that:

    ZFC ⊢ φ↔ψ   iff   f(φ) =_G f(ψ)

This follows the answer to [MathOverflow #369106](https://mathoverflow.net/questions/369106),
which chains three results:

1. ZFC provability induces a CEER (computably enumerable equivalence relation)
2. There exists a Σ₀₁-universal CEER (Neis-Sorbi, building on Gao-Gerdes)
3. Any CEER can be realized as the word problem of a finitely generated group
   (Miller's construction, extended by Neis-Sorbi Theorem 3.2)

---

## Phase 1: Group Theory Foundations

**No dependencies on other phases. Can be built and verified independently.**

### 1a. Words and Symbols

```
enum Symbol { Gen(nat), Inv(nat) }
type Word = Seq<Symbol>
```

- `concat(w1, w2)` — word concatenation
- `inverse_word(w)` — reverse and flip each symbol
- `is_inverse_pair(s1, s2)` — Gen(i)/Inv(i) or vice versa
- Lemmas: concat associativity, inverse_word involution, inverse of concat

### 1b. Free Reduction

- `has_cancellation(w)` — ∃ adjacent inverse pair
- `reduce_at(w, i)` — remove the pair at position i
- `is_reduced(w)` — no adjacent inverse pairs
- `reduces_to(w1, w2)` — transitive-reflexive closure of single-step reduction
- **Key theorem**: Church-Rosser / confluence — every word has a unique reduced form
- `normal_form(w)` — the unique reduced word equivalent to w (spec function)
- Exec: `reduce_word(w) -> w'` that computes the normal form

### 1c. Group Presentations

```
struct Presentation {
    num_generators: nat,        //  generators are 0..n-1
    relators: Seq<Word>,        //  words that equal identity
}
```

- `elementary_step`: free reduction, free expansion, relator insertion, relator
  deletion, conjugate insertion/deletion
- `derivation`: `Seq<(Word, ElementaryStep)>` — chain of steps from w1 to w2
- `equiv_in_presentation(P, w1, w2)` — ∃ derivation from w1 to w2
- Lemmas: equiv is an equivalence relation (refl, sym, trans)
- Lemmas: equiv respects concatenation (if w1≡w1' and w2≡w2' then w1·w2 ≡ w1'·w2')

### 1d. Basic Group Theory

- The quotient `Free(S) / ⟨⟨R⟩⟩` forms a group (closure under concat + inverse)
- Identity element: the empty word (mod equivalence)
- Subgroup generation, normal closure
- Possibly: homomorphisms between presented groups, quotient maps

---

## Phase 2: Computability Theory

### 2a. Computation Model

Choose one (register machines are simpler to formalize than Turing machines):

```
//  Register machine: finite program, unbounded nat registers
struct RegisterMachine {
    instructions: Seq<Instruction>,
}

enum Instruction {
    Inc(nat),           //  increment register
    DecJump(nat, nat),  //  decrement or jump if zero
    Halt,
}
```

- `configuration`: (program counter, register state)
- `step(machine, config) -> Option<config>` — single step
- `halts(machine, input)` — ∃ n such that n steps reach Halt
- `computes(machine, f)` — machine computes function f

### 2b. Computably Enumerable Sets

```
//  A set S ⊆ ℕ is c.e. if there exists a machine that enumerates it
spec fn is_ce(S: Set<nat>) -> bool {
    exists|m: RegisterMachine| forall|n: nat|
        S.contains(n) <==> halts(m, n)
}
```

- `is_computable(S)` — both S and its complement are c.e.
- Basic closure: c.e. sets closed under union, intersection, projection
- Halting problem: the set { (m,x) | m halts on x } is c.e. but not computable

### 2c. CEERs (Computably Enumerable Equivalence Relations)

```
//  A CEER on ℕ: an equivalence relation whose graph is c.e.
struct CEER {
    //  The enumerator: at stage s, it may declare pairs equivalent
    enumerator: RegisterMachine,
}
```

- `equiv_at_stage(ceer, s, a, b)` — a≡b is declared by stage s
- `equiv(ceer, a, b)` — ∃ s. equiv_at_stage(ceer, s, a, b)
- Lemma: equiv is an equivalence relation (by transitive closure of declared pairs)

### 2d. Reductions Between CEERs

```
//  A computable reduction from CEER E to CEER F
spec fn reduces_to(E: CEER, F: CEER) -> bool {
    exists|f: RegisterMachine| forall|a: nat, b: nat|
        E.equiv(a, b) <==> F.equiv(f.compute(a), f.compute(b))
}
```

- `is_sigma01_universal(F)` — every CEER reduces to F
- **Theorem (Neis-Sorbi)**: There exists a Σ₀₁-universal CEER

---

## Phase 3: First-Order Logic & ZFC

### 3a. Syntax

```
enum Formula {
    Eq(Term, Term),             //  t₁ = t₂
    In(Term, Term),             //  t₁ ∈ t₂
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    Forall(nat, Box<Formula>),  //  ∀ x_n. φ
    Exists(nat, Box<Formula>),  //  ∃ x_n. φ
}

enum Term {
    Var(nat),
}
```

- Gödel numbering: `encode(φ) -> nat`, `decode(n) -> Option<Formula>`
- Substitution, free variables, sentences (closed formulas)

### 3b. ZFC Axiom Schema

Encode each ZFC axiom as a Formula:
- Extensionality, Pairing, Union, Powerset, Infinity, Replacement schema,
  Foundation, Choice

Or more practically: define a proof checker.

### 3c. Provability

```
struct Proof {
    steps: Seq<(Formula, Justification)>,
}

enum Justification {
    Axiom,
    ModusPonens(nat, nat),      //  indices of φ→ψ and φ
    Generalization(nat, nat),   //  ∀-introduction
    //  ... standard proof rules
}
```

- `is_valid_proof(proof, conclusion)` — proof-checking is decidable
- `provable(φ)` — ∃ proof with conclusion φ
- `zfc_equiv(φ, ψ)` ≡ `provable(Iff(φ, ψ))` — this is a CEER

### 3d. ZFC Provability Is a CEER

- Lemma: `zfc_equiv` is an equivalence relation
  - Reflexivity: ZFC ⊢ φ↔φ (trivial proof)
  - Symmetry: from proof of φ↔ψ, construct proof of ψ↔φ
  - Transitivity: from proofs of φ↔ψ and ψ↔χ, construct proof of φ↔χ
- Lemma: `zfc_equiv` is c.e. (enumerate all proofs, check conclusions)

---

## Phase 4: The Universal Construction

### 4a. The Σ₀₁-Universal CEER

Following Neis-Sorbi / Gao-Gerdes:
- Construct a specific CEER U that is universal
- Key idea: U(⟨e,x⟩, ⟨e,y⟩) iff the e-th CEER identifies x and y
- Prove universality: for any CEER E, there's a computable f with
  E(a,b) ↔ U(f(a), f(b))

### 4b. Miller's Construction: CEER → Group

Given a CEER E on ℕ, construct group G_E:
1. Start with generators {a_0, a_1, ...} (one per natural number)
   plus finitely many auxiliary generators
2. At each stage s of the enumeration of E:
   - When E declares i ≡ j at stage s, add a relator making a_i = a_j in G
3. The group has decidable word problem iff E is decidable
4. **Key property**: a_i =_{G_E} a_j iff E(i,j)

The Neis-Sorbi refinement ensures this works with finitely many generators
(using a finite generating set via Higman-like embedding tricks).

### 4c. Main Theorem

```
proof fn main_theorem()
    ensures
        exists|G: Presentation, f: RegisterMachine|
            G.num_generators < omega &&  //  finitely generated
            forall|phi: Formula, psi: Formula|
                phi.is_sentence() && psi.is_sentence() ==>
                (zfc_equiv(phi, psi) <==>
                 equiv_in_presentation(G, f.compute(phi.encode()), f.compute(psi.encode())))
```

Proof: compose
1. `zfc_equiv` is a CEER (Phase 3d)
2. Universal CEER U exists (Phase 4a)
3. `zfc_equiv` reduces to U via some computable g (by universality)
4. U is realized as word problem of finitely generated G_U (Phase 4b)
5. Take f = (encoding into G_U's generators) ∘ g ∘ (Gödel encoding)

---

## Module Structure

```
verus-group-theory/src/
├── lib.rs
│
├── # Phase 1: Group Theory
├── symbol.rs              — Symbol enum, inverse
├── word.rs                — Word type, concat, inverse, basic lemmas
├── reduction.rs           — Free reduction, Church-Rosser
├── presentation.rs        — Presentations, derivations, equivalence
├── presentation_lemmas.rs — equiv is equivalence relation, respects concat
├── subgroup.rs            — Normal closure, subgroup generation
│
├── # Phase 2: Computability
├── machine.rs             — Register machines, configurations, step
├── computation.rs         — Halting, computable functions, c.e. sets
├── ceer.rs                — CEERs, staged equivalence
├── reduction_ce.rs        — Reductions between CEERs
│
├── # Phase 3: First-Order Logic
├── formula.rs             — Terms, formulas, substitution
├── goedel.rs              — Gödel numbering (encode/decode)
├── proof_system.rs        — Proofs, proof checking
├── zfc.rs                 — ZFC axioms, provability
├── zfc_ceer.rs            — ZFC provability is a CEER
│
├── # Phase 4: Universal Construction
├── universal_ceer.rs      — The Σ₀₁-universal CEER
├── miller.rs              — Miller's construction: CEER → group
├── main_theorem.rs        — Composition: the final result
│
└── # Runtime (exec layer)
    └── runtime/
        ├── mod.rs
        ├── word_ops.rs    — Word reduction, equality checking
        ├── machine_exec.rs — Register machine interpreter
        └── encoding.rs    — Formula → word encoding
```

---

## Key References

1. **Neis & Sorbi** — "Calibrating word problems of groups via the complexity of
   equivalence relations" (2009). Theorem 3.2: Σ₀₁-universal CEER → finitely
   generated group. [arXiv:1609.03371](https://arxiv.org/abs/1609.03371)

2. **Miller** — "An Elementary Construction of Unsolvable Word Problems in Group
   Theory" (McKenzie & Thompson, 1973). The base CEER → group construction.

3. **Gao & Gerdes** — Earlier work on Σ₀₁-complete CEERs.

4. **Higman** — Embedding theorem: every recursively presented group embeds in a
   finitely presented group (1961). Used implicitly in the finite generation step.

---

## Verification Strategy

- **Phase 1** is fully self-contained and independently verifiable
- **Phase 2** depends only on vstd (Seq, Set, nat arithmetic)
- **Phase 3** depends on Phase 2 for computability notions
- **Phase 4** ties everything together

Each phase should have 0 `assume(false)` before moving to the next.

Within each phase, start with spec functions, add proof lemmas for key
properties, then add exec implementations where meaningful (Phases 1 & 2
especially benefit from exec-layer word reduction and machine simulation).
