use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::shortlex::*;
use crate::rewrite::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::reduction::*;

verus! {

// ============================================================
// Soundness: rewrite systems and group presentations
// ============================================================

/// A rewrite system is sound for a presentation: every rule lhs ≡ rhs in the presented group.
pub open spec fn system_sound(sys: RewriteSystem, p: Presentation) -> bool {
    forall|i: int| 0 <= i < sys.rules.len() ==> (#[trigger] sys.rules[i]).lhs.len() > 0 && {
        let rule = sys.rules[i];
        &&& word_valid(rule.lhs, p.num_generators)
        &&& word_valid(rule.rhs, p.num_generators)
        &&& equiv_in_presentation(p, rule.lhs, rule.rhs)
    }
}

/// A single rule application at position `pos` preserves equivalence in the presentation.
/// w = prefix · lhs · suffix ≡ prefix · rhs · suffix = apply_rule_at(w, rule, pos)
pub proof fn lemma_rule_preserves_equiv(
    p: Presentation, w: Word, rule: RewriteRule, pos: int,
)
    requires
        presentation_valid(p),
        matches_at(w, rule, pos),
        word_valid(w, p.num_generators),
        word_valid(rule.lhs, p.num_generators),
        word_valid(rule.rhs, p.num_generators),
        equiv_in_presentation(p, rule.lhs, rule.rhs),
    ensures
        equiv_in_presentation(p, w, apply_rule_at(w, rule, pos)),
{
    let prefix = w.subrange(0, pos);
    let suffix = w.subrange(pos + rule.lhs.len() as int, w.len() as int);
    let result = apply_rule_at(w, rule, pos);

    // w =~= prefix + lhs + suffix
    assert(w =~= prefix + rule.lhs + suffix) by {
        assert(w =~= w.subrange(0, pos) + w.subrange(pos, w.len() as int));
        assert(w.subrange(pos, w.len() as int) =~=
            w.subrange(pos, pos + rule.lhs.len() as int)
            + w.subrange(pos + rule.lhs.len() as int, w.len() as int));
        assert(w.subrange(pos, pos + rule.lhs.len() as int) =~= rule.lhs);
    }

    assert(result =~= prefix + rule.rhs + suffix);

    assert(word_valid(prefix, p.num_generators)) by {
        assert forall|k: int| 0 <= k < prefix.len()
            implies symbol_valid(prefix[k], p.num_generators) by {
            assert(prefix[k] == w[k]);
        }
    }
    assert(word_valid(suffix, p.num_generators)) by {
        assert forall|k: int| 0 <= k < suffix.len()
            implies symbol_valid(suffix[k], p.num_generators) by {
            assert(suffix[k] == w[k + pos + rule.lhs.len()]);
        }
    }

    // lhs ≡ rhs  →  prefix + lhs ≡ prefix + rhs
    lemma_equiv_concat_left(p, rule.lhs, rule.rhs, prefix);

    // (prefix + lhs) + suffix ≡ (prefix + rhs) + suffix
    lemma_equiv_concat_right(p, prefix + rule.lhs, prefix + rule.rhs, suffix);

    assert((prefix + rule.lhs + suffix) =~= ((prefix + rule.lhs) + suffix));
    assert((prefix + rule.rhs + suffix) =~= ((prefix + rule.rhs) + suffix));
}

/// A one-step rewrite in a sound system preserves group equivalence.
pub proof fn lemma_one_step_preserves_equiv(
    sys: RewriteSystem, p: Presentation, w1: Word, w2: Word,
)
    requires
        presentation_valid(p),
        system_sound(sys, p),
        word_valid(w1, p.num_generators),
        rewrites_one_step(sys, w1, w2),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let (ri, pos) = choose|ri: int, pos: int|
        0 <= ri < sys.rules.len()
        && #[trigger] matches_at(w1, sys.rules[ri], pos)
        && w2 == apply_rule_at(w1, sys.rules[ri], pos);
    let rule = sys.rules[ri];
    lemma_rule_preserves_equiv(p, w1, rule, pos);
}

/// A one-step rewrite in a sound system preserves word validity.
pub proof fn lemma_one_step_preserves_word_valid(
    sys: RewriteSystem, p: Presentation, w1: Word, w2: Word,
)
    requires
        system_sound(sys, p),
        word_valid(w1, p.num_generators),
        rewrites_one_step(sys, w1, w2),
    ensures
        word_valid(w2, p.num_generators),
{
    let (ri, pos) = choose|ri: int, pos: int|
        0 <= ri < sys.rules.len()
        && #[trigger] matches_at(w1, sys.rules[ri], pos)
        && w2 == apply_rule_at(w1, sys.rules[ri], pos);
    let rule = sys.rules[ri];
    let n = p.num_generators;

    let prefix = w1.subrange(0, pos);
    let suffix = w1.subrange(pos + rule.lhs.len() as int, w1.len() as int);

    assert(word_valid(prefix, n)) by {
        assert forall|k: int| 0 <= k < prefix.len()
            implies symbol_valid(prefix[k], n) by { assert(prefix[k] == w1[k]); }
    }
    assert(word_valid(suffix, n)) by {
        assert forall|k: int| 0 <= k < suffix.len()
            implies symbol_valid(suffix[k], n) by {
            assert(suffix[k] == w1[k + pos + rule.lhs.len()]);
        }
    }

    assert(w2 =~= prefix + rule.rhs + suffix);
    assert forall|k: int| 0 <= k < w2.len()
        implies symbol_valid(w2[k], n)
    by {
        if k < prefix.len() {
            assert(w2[k] == prefix[k]);
        } else if k < prefix.len() + rule.rhs.len() {
            assert(w2[k] == rule.rhs[k - prefix.len()]);
        } else {
            assert(w2[k] == suffix[k - prefix.len() - rule.rhs.len()]);
        }
    }
}

/// Multi-step rewriting in a sound system preserves group equivalence.
pub proof fn lemma_rewrite_preserves_equiv(
    sys: RewriteSystem, p: Presentation, w1: Word, w2: Word, n: nat,
)
    requires
        presentation_valid(p),
        system_sound(sys, p),
        system_wf(sys),
        word_valid(w1, p.num_generators),
        rewrites_in_steps(sys, w1, w2, n),
    ensures
        equiv_in_presentation(p, w1, w2),
    decreases n,
{
    if n == 0 {
        lemma_equiv_refl(p, w1);
    } else if w1 =~= w2 {
        lemma_equiv_refl(p, w1);
    } else {
        let w_mid = choose|w_mid: Word|
            rewrites_one_step(sys, w1, w_mid)
            && rewrites_in_steps(sys, w_mid, w2, (n - 1) as nat);
        lemma_one_step_preserves_equiv(sys, p, w1, w_mid);
        lemma_one_step_preserves_word_valid(sys, p, w1, w_mid);
        lemma_rewrite_preserves_equiv(sys, p, w_mid, w2, (n - 1) as nat);
        lemma_equiv_transitive(p, w1, w_mid, w2);
    }
}

// ============================================================
// Confluence implies decidability
// ============================================================

/// In a confluent system, any two rewriting paths from the same word
/// lead to the same irreducible form.
pub proof fn lemma_unique_normal_form(
    sys: RewriteSystem,
    w: Word, nf1: Word, nf2: Word,
)
    requires
        confluent(sys),
        rewrites_to(sys, w, nf1),
        rewrites_to(sys, w, nf2),
        is_irreducible(sys, nf1),
        is_irreducible(sys, nf2),
    ensures
        nf1 =~= nf2,
{
    // Explicitly instantiate the confluent forall with (w, nf1, nf2)
    // instead of letting Z3 search the quantifier space.
    assert(rewrites_to(sys, w, nf1) && rewrites_to(sys, w, nf2));
    assert(joinable(sys, nf1, nf2)) by {
        // confluent says: forall w, w1, w2. rewrites_to(w,w1) && rewrites_to(w,w2) ==> joinable(w1,w2)
        // instantiate with w=w, w1=nf1, w2=nf2
        assert(rewrites_to(sys, w, nf1));
        assert(rewrites_to(sys, w, nf2));
    }
    let w3 = choose|w3: Word| rewrites_to(sys, nf1, w3) && rewrites_to(sys, nf2, w3);
    lemma_irreducible_only_rewrites_to_self(sys, nf1, w3);
    lemma_irreducible_only_rewrites_to_self(sys, nf2, w3);
}

/// An irreducible word can only rewrite to itself.
proof fn lemma_irreducible_only_rewrites_to_self(
    sys: RewriteSystem, w: Word, w2: Word,
)
    requires
        is_irreducible(sys, w),
        rewrites_to(sys, w, w2),
    ensures
        w =~= w2,
{
    let n = choose|n: nat| rewrites_in_steps(sys, w, w2, n);
    lemma_irreducible_only_rewrites_to_self_aux(sys, w, w2, n);
}

proof fn lemma_irreducible_only_rewrites_to_self_aux(
    sys: RewriteSystem, w: Word, w2: Word, n: nat,
)
    requires
        is_irreducible(sys, w),
        rewrites_in_steps(sys, w, w2, n),
    ensures
        w =~= w2,
    decreases n,
{
    if n == 0 {
    } else if w =~= w2 {
    } else {
        let w_mid = choose|w_mid: Word|
            rewrites_one_step(sys, w, w_mid)
            && rewrites_in_steps(sys, w_mid, w2, (n - 1) as nat);
        lemma_irreducible_no_step(sys, w);
        assert(false);
    }
}

/// The easy direction: same normal form implies equivalence.
pub proof fn lemma_same_normal_form_implies_equiv(
    sys: RewriteSystem, p: Presentation,
    w1: Word, w2: Word,
    nf: Word,
)
    requires
        presentation_valid(p),
        system_sound(sys, p),
        system_wf(sys),
        word_valid(w1, p.num_generators),
        word_valid(w2, p.num_generators),
        rewrites_to(sys, w1, nf),
        rewrites_to(sys, w2, nf),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let n1 = choose|n: nat| rewrites_in_steps(sys, w1, nf, n);
    let n2 = choose|n: nat| rewrites_in_steps(sys, w2, nf, n);
    lemma_rewrite_preserves_equiv(sys, p, w1, nf, n1);
    lemma_rewrite_preserves_equiv(sys, p, w2, nf, n2);
    lemma_equiv_symmetric(p, w2, nf);
    lemma_equiv_transitive(p, w1, nf, w2);
}

} // verus!
