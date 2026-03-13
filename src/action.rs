use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::reduction::*;

verus! {

/// A finite group action: generators act as permutations on {0, ..., set_size-1}.
pub struct FiniteAction {
    pub presentation: Presentation,
    pub set_size: nat,
    /// perm_images[gen_idx] is a permutation of {0..set_size}.
    pub perm_images: Seq<Seq<nat>>,
}

/// Check that a sequence is a permutation of {0..n}.
pub open spec fn is_permutation(perm: Seq<nat>, n: nat) -> bool {
    perm.len() == n
    && (forall|i: int| 0 <= i < n ==> (#[trigger] perm[i]) < n)
    && (forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j
        ==> #[trigger] perm[i] != #[trigger] perm[j])
}

/// Inverse permutation lookup: find the preimage of y.
pub open spec fn inverse_perm_lookup(perm: Seq<nat>, y: nat) -> nat
    recommends is_permutation(perm, perm.len()), y < perm.len(),
{
    choose|x: nat| x < perm.len() && perm[x as int] == y
}

/// A finite action is valid if all generator images are permutations
/// and relators act as the identity (presented group action, not just free group).
pub open spec fn action_valid(a: FiniteAction) -> bool {
    a.perm_images.len() == a.presentation.num_generators
    && (forall|i: int| #![trigger a.perm_images[i]]
        0 <= i < a.perm_images.len() ==> is_permutation(a.perm_images[i], a.set_size))
    && (forall|c: int, x: nat| #![trigger apply_action(a, a.presentation.relators[c], x)]
        0 <= c < a.presentation.relators.len() && x < a.set_size ==>
            apply_action(a, a.presentation.relators[c], x) == x)
}

/// Apply a single symbol's action to a point.
pub open spec fn apply_action_symbol(a: FiniteAction, s: Symbol, x: nat) -> nat
    recommends x < a.set_size,
{
    match s {
        Symbol::Gen(i) => a.perm_images[i as int][x as int],
        Symbol::Inv(i) => inverse_perm_lookup(a.perm_images[i as int], x),
    }
}

/// Apply a word's action to a point (right-to-left composition).
/// apply_action(w, x) = w[0](w[1](...(w[n-1](x))...))
pub open spec fn apply_action(a: FiniteAction, w: Word, x: nat) -> nat
    recommends x < a.set_size,
    decreases w.len(),
{
    if w.len() == 0 {
        x
    } else {
        apply_action_symbol(a, w.first(), apply_action(a, w.drop_first(), x))
    }
}

/// A point y is in the orbit of x if some word maps x to y.
pub open spec fn in_orbit(a: FiniteAction, x: nat, y: nat) -> bool {
    exists|w: Word| apply_action(a, w, x) == y
}

/// A word is in the stabilizer of x if it fixes x.
pub open spec fn in_stabilizer(a: FiniteAction, x: nat, w: Word) -> bool {
    apply_action(a, w, x) == x
}

// --- Lemmas ---

/// The empty word acts as the identity.
pub proof fn lemma_action_identity(a: FiniteAction, x: nat)
    ensures
        apply_action(a, empty_word(), x) == x,
{
}

/// Action is compatible with concatenation:
/// apply_action(w1·w2, x) == apply_action(w1, apply_action(w2, x)).
pub proof fn lemma_action_compatible(a: FiniteAction, w1: Word, w2: Word, x: nat)
    ensures
        apply_action(a, concat(w1, w2), x) == apply_action(a, w1, apply_action(a, w2, x)),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
    } else {
        let s = w1.first();
        let rest = w1.drop_first();
        assert(concat(w1, w2).first() == s);
        assert(concat(w1, w2).drop_first() =~= concat(rest, w2));
        lemma_action_compatible(a, rest, w2, x);
    }
}

/// Orbit is reflexive: x is in its own orbit.
pub proof fn lemma_orbit_reflexive(a: FiniteAction, x: nat)
    ensures
        in_orbit(a, x, x),
{
    assert(apply_action(a, empty_word(), x) == x);
}

/// Orbit is transitive: if y in orbit(x) and z in orbit(y), then z in orbit(x).
pub proof fn lemma_orbit_transitive(a: FiniteAction, x: nat, y: nat, z: nat)
    requires
        in_orbit(a, x, y),
        in_orbit(a, y, z),
    ensures
        in_orbit(a, x, z),
{
    let w1 = choose|w: Word| apply_action(a, w, x) == y;
    let w2 = choose|w: Word| apply_action(a, w, y) == z;
    // apply_action(w2 · w1, x) = apply_action(w2, apply_action(w1, x)) = apply_action(w2, y) = z
    // Wait: we need w2(w1(x)) but concat is left-to-right
    // apply_action(concat(w2, w1), x) = apply_action(w2, apply_action(w1, x))
    lemma_action_compatible(a, w2, w1, x);
    let w = concat(w2, w1);
    assert(apply_action(a, w, x) == z);
}

/// Stabilizer contains the identity.
pub proof fn lemma_stabilizer_contains_identity(a: FiniteAction, x: nat)
    ensures
        in_stabilizer(a, x, empty_word()),
{
}

/// Stabilizer is closed under concatenation.
pub proof fn lemma_stabilizer_closed_under_concat(a: FiniteAction, x: nat, w1: Word, w2: Word)
    requires
        in_stabilizer(a, x, w1),
        in_stabilizer(a, x, w2),
    ensures
        in_stabilizer(a, x, concat(w1, w2)),
{
    lemma_action_compatible(a, w1, w2, x);
}

/// Inverse permutation cancellation: perm(inv_perm(y)) == y.
pub proof fn lemma_perm_inverse_right(perm: Seq<nat>, n: nat, y: nat)
    requires
        is_permutation(perm, n),
        y < n,
    ensures
        perm[inverse_perm_lookup(perm, y) as int] == y,
{
    // inverse_perm_lookup chooses x such that perm[x] == y
    // Since perm is a permutation and y < n, such x exists
    // (surjectivity from injectivity + finiteness)
    lemma_permutation_surjective(perm, n, y);
    let x = inverse_perm_lookup(perm, y);
    assert(x < n && perm[x as int] == y);
}

/// Skip a value: maps {0..n}\{z} bijectively to {0..n-1}.
spec fn skip_val(v: nat, z: nat) -> nat {
    if v < z { v } else { (v - 1) as nat }
}

/// skip_val is injective on {0..n}\{z}.
proof fn lemma_skip_val_injective(a: nat, b: nat, z: nat, n: nat)
    requires
        a < n, b < n, a != z, b != z, z < n,
        skip_val(a, z) == skip_val(b, z),
    ensures
        a == b,
{
    if a < z && b < z {
    } else if a > z && b > z {
    } else if a < z && b > z {
        // a == b-1, a < z, b > z >= a+1, so b-1 >= z > a. Contradiction: a == b-1 >= z > a.
    } else {
        // a > z && b < z: symmetric
    }
}

/// A finite injection is surjective (pigeonhole).
/// Proof: induction on n. Remove the last element's image via skip_val,
/// giving a permutation of size n-1. By IH, find preimage, then lift.
proof fn lemma_permutation_surjective(perm: Seq<nat>, n: nat, y: nat)
    requires
        is_permutation(perm, n),
        y < n,
    ensures
        exists|x: nat| x < n && perm[x as int] == y,
    decreases n,
{
    if n == 0 {
    } else if perm[(n - 1) as int] == y {
        assert(((n - 1) as nat) < n && perm[(n - 1) as int] == y);
    } else {
        let z = perm[(n - 1) as int];
        let n1 = (n - 1) as nat;
        // Build restricted permutation: skip z from all values
        let perm2 = Seq::new(n1, |i: int| skip_val(perm[i], z));

        // All values < n-1
        assert forall|i: int| 0 <= i < n1 implies (#[trigger] perm2[i]) < n1
        by {
            assert(perm[i] != z); // injectivity: i != n-1, perm[n-1] = z
            if perm[i] < z {
                // skip_val = perm[i] < z <= n-1
            } else {
                // perm[i] > z, skip_val = perm[i]-1 < n-1
            }
        }

        // Injectivity
        assert forall|i: int, j: int| 0 <= i < n1 && 0 <= j < n1 && i != j
            implies #[trigger] perm2[i] != #[trigger] perm2[j]
        by {
            assert(perm[i] != z);
            assert(perm[j] != z);
            if perm2[i] == perm2[j] {
                lemma_skip_val_injective(perm[i], perm[j], z, n);
            }
        }

        assert(is_permutation(perm2, n1));

        // y != z, so skip_val(y, z) < n-1
        let y2 = skip_val(y, z);

        // Apply IH
        lemma_permutation_surjective(perm2, n1, y2);
        let x = choose|x: nat| x < n1 && perm2[x as int] == y2;
        // perm2[x] = skip_val(perm[x], z) = skip_val(y, z)
        assert(perm[x as int] != z); // injectivity: x < n-1, perm[n-1] = z
        lemma_skip_val_injective(perm[x as int], y, z, n);
        assert(x < n && perm[x as int] == y);
    }
}

/// Gen followed by Inv cancels on any point (for valid actions).
pub proof fn lemma_gen_inv_cancels(a: FiniteAction, gen_idx: nat, x: nat)
    requires
        action_valid(a),
        gen_idx < a.presentation.num_generators,
        x < a.set_size,
    ensures
        apply_action_symbol(a, Symbol::Inv(gen_idx),
            apply_action_symbol(a, Symbol::Gen(gen_idx), x)) == x,
{
    let perm = a.perm_images[gen_idx as int];
    let y = perm[x as int];
    // apply_action_symbol(Gen(gen_idx), x) == perm[x] == y
    // apply_action_symbol(Inv(gen_idx), y) == inverse_perm_lookup(perm, y)
    // We need: inverse_perm_lookup(perm, y) == x
    // i.e., the chosen x' with perm[x'] == y is x
    // Since perm is injective and perm[x] == y, any x' with perm[x'] == y must equal x
    assert(is_permutation(perm, a.set_size));
    assert(y < a.set_size);
    lemma_perm_inverse_right(perm, a.set_size, y);
    let x2 = inverse_perm_lookup(perm, y);
    // perm[x2] == y == perm[x], and perm is injective, so x2 == x
    assert(perm[x2 as int] == y);
    assert(perm[x as int] == y);
    // Injectivity: x2 != x would give perm[x2] == perm[x] with x2 != x, contradiction
}

} // verus!
