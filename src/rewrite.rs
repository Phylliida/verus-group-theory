use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::shortlex::*;

verus! {

//  ============================================================
//  Rewrite rules and systems
//  ============================================================

///  A rewrite rule: lhs → rhs, where lhs is strictly greater than rhs in shortlex.
pub struct RewriteRule {
    pub lhs: Word,
    pub rhs: Word,
}

///  A rewrite system: an ordered collection of rewrite rules.
pub struct RewriteSystem {
    pub rules: Seq<RewriteRule>,
}

///  A rewrite rule is well-formed: lhs > rhs in shortlex, and lhs is nonempty.
pub open spec fn rule_wf(rule: RewriteRule) -> bool {
    rule.lhs.len() > 0 && shortlex_lt(rule.rhs, rule.lhs)
}

///  All rules in the system are well-formed.
pub open spec fn system_wf(sys: RewriteSystem) -> bool {
    forall|i: int| 0 <= i < sys.rules.len() ==> rule_wf(#[trigger] sys.rules[i])
}

//  ============================================================
//  Subword matching and rule application
//  ============================================================

///  The lhs of a rule matches at position `pos` in word `w`.
pub open spec fn matches_at(w: Word, rule: RewriteRule, pos: int) -> bool {
    pos >= 0
    && pos + rule.lhs.len() <= w.len()
    && w.subrange(pos, pos + rule.lhs.len() as int) =~= rule.lhs
}

///  Apply a rule at position `pos`: replace the matched lhs with rhs.
///  Result: w[0..pos] ++ rhs ++ w[pos+|lhs|..]
pub open spec fn apply_rule_at(w: Word, rule: RewriteRule, pos: int) -> Word
    recommends
        matches_at(w, rule, pos),
{
    w.subrange(0, pos) + rule.rhs + w.subrange(pos + rule.lhs.len() as int, w.len() as int)
}

///  One-step rewrite: w1 rewrites to w2 by applying some rule at some position.
pub open spec fn rewrites_one_step(sys: RewriteSystem, w1: Word, w2: Word) -> bool {
    exists|ri: int, pos: int|
        0 <= ri < sys.rules.len()
        && #[trigger] matches_at(w1, sys.rules[ri], pos)
        && w2 == apply_rule_at(w1, sys.rules[ri], pos)
}

///  Multi-step rewrite: w1 rewrites to w2 in at most n steps.
pub open spec fn rewrites_in_steps(sys: RewriteSystem, w1: Word, w2: Word, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        w1 =~= w2
    } else {
        w1 =~= w2 || exists|w_mid: Word|
            rewrites_one_step(sys, w1, w_mid)
            && rewrites_in_steps(sys, w_mid, w2, (n - 1) as nat)
    }
}

///  w1 rewrites to w2 (in some number of steps).
pub open spec fn rewrites_to(sys: RewriteSystem, w1: Word, w2: Word) -> bool {
    exists|n: nat| rewrites_in_steps(sys, w1, w2, n)
}

///  No rule applies to w: it is irreducible (a normal form) under the system.
pub open spec fn is_irreducible(sys: RewriteSystem, w: Word) -> bool {
    forall|ri: int, pos: int|
        0 <= ri < sys.rules.len()
        ==> !#[trigger] matches_at(w, sys.rules[ri], pos)
}

///  Two words are joinable: they rewrite to a common word.
pub open spec fn joinable(sys: RewriteSystem, w1: Word, w2: Word) -> bool {
    exists|w: Word| rewrites_to(sys, w1, w) && rewrites_to(sys, w2, w)
}

///  The system is locally confluent: any one-step fork is joinable.
pub open spec fn locally_confluent(sys: RewriteSystem) -> bool {
    forall|w: Word, w1: Word, w2: Word|
        rewrites_one_step(sys, w, w1) && rewrites_one_step(sys, w, w2)
        ==> joinable(sys, w1, w2)
}

///  The system is confluent: any fork is joinable.
pub open spec fn confluent(sys: RewriteSystem) -> bool {
    forall|w: Word, w1: Word, w2: Word|
        rewrites_to(sys, w, w1) && rewrites_to(sys, w, w2)
        ==> joinable(sys, w1, w2)
}

//  ============================================================
//  Basic rewrite lemmas
//  ============================================================

///  Applying a well-formed rule produces a shortlex-smaller word.
pub proof fn lemma_rule_application_decreases(w: Word, rule: RewriteRule, pos: int)
    requires
        rule_wf(rule),
        matches_at(w, rule, pos),
    ensures
        shortlex_lt(apply_rule_at(w, rule, pos), w),
{
    lemma_shortlex_subword_replace(
        w, pos, rule.lhs.len(), rule.rhs, rule.lhs,
    );
}

///  Applying a well-formed rule strictly decreases word length (or preserves it with lex decrease).
pub proof fn lemma_rule_application_len(w: Word, rule: RewriteRule, pos: int)
    requires
        rule_wf(rule),
        matches_at(w, rule, pos),
    ensures
        apply_rule_at(w, rule, pos).len() <= w.len(),
        apply_rule_at(w, rule, pos).len() == w.len() - rule.lhs.len() + rule.rhs.len(),
{
    let result = apply_rule_at(w, rule, pos);
    let prefix = w.subrange(0, pos);
    let suffix = w.subrange(pos + rule.lhs.len() as int, w.len() as int);
    assert(result.len() == prefix.len() + rule.rhs.len() + suffix.len());
    assert(w.len() == prefix.len() + rule.lhs.len() + suffix.len()) by {
        assert(w =~= prefix + w.subrange(pos, w.len() as int));
        assert(w.subrange(pos, w.len() as int).len() == w.len() - pos);
    }
    lemma_shortlex_lt_len_bound(rule.rhs, rule.lhs);
}

///  Every word rewrites to itself (zero steps).
pub proof fn lemma_rewrites_to_refl(sys: RewriteSystem, w: Word)
    ensures
        rewrites_to(sys, w, w),
{
    assert(rewrites_in_steps(sys, w, w, 0));
}

///  If w1 rewrites to w2 in n steps, also in n+1 steps.
pub proof fn lemma_rewrites_in_steps_monotone(
    sys: RewriteSystem, w1: Word, w2: Word, n: nat,
)
    requires
        rewrites_in_steps(sys, w1, w2, n),
    ensures
        rewrites_in_steps(sys, w1, w2, (n + 1) as nat),
    decreases n,
{
    if n == 0 {
    } else {
        if w1 =~= w2 {
        } else {
            let w_mid = choose|w_mid: Word|
                rewrites_one_step(sys, w1, w_mid)
                && rewrites_in_steps(sys, w_mid, w2, (n - 1) as nat);
            lemma_rewrites_in_steps_monotone(sys, w_mid, w2, (n - 1) as nat);
        }
    }
}

///  Transitivity of multi-step rewriting.
pub proof fn lemma_rewrites_to_transitive(
    sys: RewriteSystem, w1: Word, w2: Word, w3: Word,
)
    requires
        rewrites_to(sys, w1, w2),
        rewrites_to(sys, w2, w3),
    ensures
        rewrites_to(sys, w1, w3),
{
    let n1 = choose|n: nat| rewrites_in_steps(sys, w1, w2, n);
    let n2 = choose|n: nat| rewrites_in_steps(sys, w2, w3, n);
    lemma_rewrites_chain(sys, w1, w2, w3, n1, n2);
}

///  Helper: chaining multi-step rewrites with explicit step counts.
proof fn lemma_rewrites_chain(
    sys: RewriteSystem, w1: Word, w2: Word, w3: Word, n1: nat, n2: nat,
)
    requires
        rewrites_in_steps(sys, w1, w2, n1),
        rewrites_in_steps(sys, w2, w3, n2),
    ensures
        rewrites_to(sys, w1, w3),
    decreases n1,
{
    if n1 == 0 {
        assert(rewrites_in_steps(sys, w1, w3, n2));
    } else {
        if w1 =~= w2 {
            assert(rewrites_in_steps(sys, w1, w3, n2));
        } else {
            let w_mid = choose|w_mid: Word|
                rewrites_one_step(sys, w1, w_mid)
                && rewrites_in_steps(sys, w_mid, w2, (n1 - 1) as nat);
            lemma_rewrites_chain(sys, w_mid, w2, w3, (n1 - 1) as nat, n2);
            let n3 = choose|n: nat| rewrites_in_steps(sys, w_mid, w3, n);
            assert(rewrites_in_steps(sys, w1, w3, (n3 + 1) as nat));
        }
    }
}

///  One-step rewrite implies multi-step.
pub proof fn lemma_one_step_implies_rewrites_to(
    sys: RewriteSystem, w1: Word, w2: Word,
)
    requires
        rewrites_one_step(sys, w1, w2),
    ensures
        rewrites_to(sys, w1, w2),
{
    lemma_rewrites_to_refl(sys, w2);
    assert(rewrites_in_steps(sys, w2, w2, 0));
    assert(rewrites_in_steps(sys, w1, w2, 1nat));
}

///  A one-step rewrite in a well-formed system decreases word length.
pub proof fn lemma_one_step_decreases_len(sys: RewriteSystem, w1: Word, w2: Word)
    requires
        system_wf(sys),
        rewrites_one_step(sys, w1, w2),
    ensures
        w2.len() <= w1.len(),
{
    let (ri, pos) = choose|ri: int, pos: int|
        0 <= ri < sys.rules.len()
        && #[trigger] matches_at(w1, sys.rules[ri], pos)
        && w2 == apply_rule_at(w1, sys.rules[ri], pos);
    lemma_rule_application_len(w1, sys.rules[ri], pos);
}

///  Multi-step rewriting in a well-formed system cannot increase length.
pub proof fn lemma_rewrites_to_len(
    sys: RewriteSystem, w1: Word, w2: Word, n: nat,
)
    requires
        system_wf(sys),
        rewrites_in_steps(sys, w1, w2, n),
    ensures
        w2.len() <= w1.len(),
    decreases n,
{
    if n == 0 {
    } else {
        if w1 =~= w2 {
        } else {
            let w_mid = choose|w_mid: Word|
                rewrites_one_step(sys, w1, w_mid)
                && rewrites_in_steps(sys, w_mid, w2, (n - 1) as nat);
            lemma_one_step_decreases_len(sys, w1, w_mid);
            lemma_rewrites_to_len(sys, w_mid, w2, (n - 1) as nat);
        }
    }
}

///  An irreducible word only rewrites to itself.
pub proof fn lemma_irreducible_no_step(sys: RewriteSystem, w: Word)
    requires
        is_irreducible(sys, w),
    ensures
        !exists|w2: Word| rewrites_one_step(sys, w, w2),
{
}

///  Joinability is symmetric.
pub proof fn lemma_joinable_symmetric(sys: RewriteSystem, w1: Word, w2: Word)
    requires
        joinable(sys, w1, w2),
    ensures
        joinable(sys, w2, w1),
{
    let w = choose|w: Word| rewrites_to(sys, w1, w) && rewrites_to(sys, w2, w);
    assert(rewrites_to(sys, w2, w) && rewrites_to(sys, w1, w));
}

//  ============================================================
//  Length-decreasing systems (stronger than shortlex-decreasing)
//  ============================================================

///  Every rule strictly decreases word length: |rhs| < |lhs|.
///  This is stronger than shortlex_lt but simpler for the Newman's lemma proof.
///  Most group presentation rules satisfy this (relator → shorter form).
pub open spec fn system_length_decreasing(sys: RewriteSystem) -> bool {
    forall|i: int| 0 <= i < sys.rules.len() ==> {
        let rule = #[trigger] sys.rules[i];
        rule.lhs.len() > 0 && rule.rhs.len() < rule.lhs.len()
    }
}

///  Length-decreasing implies well-formed (shortlex decreasing).
pub proof fn lemma_length_decreasing_implies_wf(sys: RewriteSystem)
    requires
        system_length_decreasing(sys),
    ensures
        system_wf(sys),
{
    assert forall|i: int| 0 <= i < sys.rules.len()
        implies rule_wf(#[trigger] sys.rules[i])
    by {
        let rule = sys.rules[i];
        assert(rule.rhs.len() < rule.lhs.len());
        //  shortlex_lt(rhs, lhs) because rhs.len() < lhs.len()
    }
}

///  A one-step rewrite in a length-decreasing system strictly decreases length.
pub proof fn lemma_one_step_strictly_decreases_len(
    sys: RewriteSystem, w1: Word, w2: Word,
)
    requires
        system_length_decreasing(sys),
        rewrites_one_step(sys, w1, w2),
    ensures
        w2.len() < w1.len(),
{
    let (ri, pos) = choose|ri: int, pos: int|
        0 <= ri < sys.rules.len()
        && #[trigger] matches_at(w1, sys.rules[ri], pos)
        && w2 == apply_rule_at(w1, sys.rules[ri], pos);
    let rule = sys.rules[ri];
    lemma_length_decreasing_implies_wf(sys);
    lemma_rule_application_len(w1, rule, pos);
    //  w2.len() == w1.len() - rule.lhs.len() + rule.rhs.len()
    //  Since rule.rhs.len() < rule.lhs.len(), we get w2.len() < w1.len()
}

} //  verus!
