use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::rewrite::*;

verus! {

// ============================================================
// Critical Pairs for String Rewriting Systems
// ============================================================
//
// The Critical Pair Lemma: a terminating system is confluent iff all
// critical pairs are joinable. We prove the "if" direction:
//   all CPs joinable + terminating → locally confluent → confluent (by Newman)
//
// Critical pairs arise from overlaps between rule LHS patterns.
// Given two rules r1: l1 → r1, r2: l2 → r2, overlaps occur when:
//   (a) A suffix of l1 equals a prefix of l2 (or vice versa) — "overlap"
//   (b) l2 occurs as a subword of l1 (or vice versa) — "inclusion"

// ============================================================
// Overlap critical pairs
// ============================================================

/// An overlap of length `olen` between rules r1 and r2:
/// the last `olen` symbols of r1.lhs equal the first `olen` symbols of r2.lhs.
pub open spec fn is_overlap(r1: RewriteRule, r2: RewriteRule, olen: nat) -> bool {
    olen >= 1
    && olen <= r1.lhs.len()
    && olen <= r2.lhs.len()
    && r1.lhs.subrange(r1.lhs.len() - olen, r1.lhs.len() as int)
       =~= r2.lhs.subrange(0, olen as int)
}

/// The overlapping word: l1 ++ l2[olen..].
/// This is the minimal word where both rules can fire.
pub open spec fn overlap_word(r1: RewriteRule, r2: RewriteRule, olen: nat) -> Word
    recommends is_overlap(r1, r2, olen),
{
    r1.lhs + r2.lhs.subrange(olen as int, r2.lhs.len() as int)
}

/// The critical pair from an overlap: applying r1 at 0 vs r2 at |l1|-olen.
/// Left:  r1.rhs ++ l2[olen..]
/// Right: l1[0..|l1|-olen] ++ r2.rhs
pub open spec fn overlap_cp_left(r1: RewriteRule, r2: RewriteRule, olen: nat) -> Word
    recommends is_overlap(r1, r2, olen),
{
    r1.rhs + r2.lhs.subrange(olen as int, r2.lhs.len() as int)
}

pub open spec fn overlap_cp_right(r1: RewriteRule, r2: RewriteRule, olen: nat) -> Word
    recommends is_overlap(r1, r2, olen),
{
    r1.lhs.subrange(0, r1.lhs.len() - olen) + r2.rhs
}

// ============================================================
// Inclusion critical pairs
// ============================================================

/// An inclusion: r2.lhs appears inside r1.lhs starting at position `ipos`.
pub open spec fn is_inclusion(r1: RewriteRule, r2: RewriteRule, ipos: nat) -> bool {
    ipos + r2.lhs.len() <= r1.lhs.len()
    && r1.lhs.subrange(ipos as int, ipos + r2.lhs.len() as int) =~= r2.lhs
}

/// The inclusion critical pair: applying r1 to the whole l1 vs r2 at ipos within l1.
/// Left:  r1.rhs
/// Right: l1[0..ipos] ++ r2.rhs ++ l1[ipos+|l2|..]
pub open spec fn inclusion_cp_left(r1: RewriteRule) -> Word {
    r1.rhs
}

pub open spec fn inclusion_cp_right(r1: RewriteRule, r2: RewriteRule, ipos: nat) -> Word
    recommends is_inclusion(r1, r2, ipos),
{
    r1.lhs.subrange(0, ipos as int)
    + r2.rhs
    + r1.lhs.subrange(ipos + r2.lhs.len() as int, r1.lhs.len() as int)
}

// ============================================================
// All critical pairs joinable
// ============================================================

/// All overlap critical pairs between all rule pairs are joinable.
pub open spec fn all_overlap_cps_joinable(sys: RewriteSystem) -> bool {
    forall|i: int, j: int, olen: nat|
        0 <= i < sys.rules.len() && 0 <= j < sys.rules.len()
        && is_overlap(sys.rules[i], sys.rules[j], olen)
        ==> joinable(sys,
                overlap_cp_left(sys.rules[i], sys.rules[j], olen),
                overlap_cp_right(sys.rules[i], sys.rules[j], olen))
}

/// All inclusion critical pairs between all rule pairs are joinable.
pub open spec fn all_inclusion_cps_joinable(sys: RewriteSystem) -> bool {
    forall|i: int, j: int, ipos: nat|
        0 <= i < sys.rules.len() && 0 <= j < sys.rules.len()
        && is_inclusion(sys.rules[i], sys.rules[j], ipos)
        ==> joinable(sys,
                inclusion_cp_left(sys.rules[i]),
                inclusion_cp_right(sys.rules[i], sys.rules[j], ipos))
}

/// All critical pairs (both kinds) are joinable.
pub open spec fn all_cps_joinable(sys: RewriteSystem) -> bool {
    all_overlap_cps_joinable(sys) && all_inclusion_cps_joinable(sys)
}

// ============================================================
// Disjoint case: non-overlapping rule applications commute
// ============================================================

/// When two rule matches don't overlap, the result of applying both
/// (in either order) is the same word.
pub proof fn lemma_disjoint_commute(
    w: Word,
    r1: RewriteRule, p1: int,
    r2: RewriteRule, p2: int,
)
    requires
        matches_at(w, r1, p1),
        matches_at(w, r2, p2),
        // r1's match region ends before r2's starts
        p1 + r1.lhs.len() <= p2,
    ensures
        // Both orderings yield the same word
        ({
            let w1 = apply_rule_at(w, r1, p1);
            let w2 = apply_rule_at(w, r2, p2);
            // After applying r1 at p1, r2's match shifts by the length difference
            let p2_adj = p2 - r1.lhs.len() + r2.lhs.len();
            // Hmm, that's not right. Let me think again.
            // After applying r1 at p1: w becomes prefix + r1.rhs + middle + r2_region + suffix
            // The shift is: p2 in w maps to p2 - |r1.lhs| + |r1.rhs| in w1.
            let shift = r1.rhs.len() - r1.lhs.len();
            let p2_in_w1: int = p2 + shift;
            &&& matches_at(w1, r2, p2_in_w1)
            &&& apply_rule_at(w1, r2, p2_in_w1) =~= apply_rule_at(w2, r1, p1)
        }),
{
    let w1 = apply_rule_at(w, r1, p1);
    let w2 = apply_rule_at(w, r2, p2);
    let shift: int = r1.rhs.len() - r1.lhs.len();
    let p2_in_w1: int = p2 + shift;

    // Decompose w = A ++ l1 ++ B ++ l2 ++ C
    let a = w.subrange(0, p1);
    let l1 = w.subrange(p1, p1 + r1.lhs.len() as int);
    let b = w.subrange(p1 + r1.lhs.len() as int, p2);
    let l2 = w.subrange(p2, p2 + r2.lhs.len() as int);
    let c = w.subrange(p2 + r2.lhs.len() as int, w.len() as int);

    assert(l1 =~= r1.lhs);
    assert(l2 =~= r2.lhs);

    // w1 = A ++ r1.rhs ++ B ++ l2 ++ C
    assert(w1 =~= a + r1.rhs + (b + l2 + c)) by {
        assert(w =~= a + l1 + (b + l2 + c)) by {
            // w = a + w[p1..] = a + l1 + w[p1+|l1|..]
            // w[p1+|l1|..] = b + w[p2..] = b + l2 + c
            assert(w =~= a + w.subrange(p1, w.len() as int));
            assert(w.subrange(p1, w.len() as int) =~= l1 + w.subrange(p1 + r1.lhs.len() as int, w.len() as int));
            assert(w.subrange(p1 + r1.lhs.len() as int, w.len() as int) =~= b + w.subrange(p2, w.len() as int));
            assert(w.subrange(p2, w.len() as int) =~= l2 + c);
        }
    }

    // w2 = A ++ l1 ++ B ++ r2.rhs ++ C
    assert(w2 =~= a + l1 + (b + r2.rhs + c)) by {
        assert(w =~= (a + l1 + b) + l2 + c) by {
            assert(w =~= a + l1 + (b + l2 + c));
        }
    }

    // In w1: l2 appears at position p2_in_w1 = p2 + |r1.rhs| - |r1.lhs|
    // because a + r1.rhs + b has length |a| + |r1.rhs| + |b| = p1 + |r1.rhs| + (p2 - p1 - |r1.lhs|) = p2 + shift
    assert(matches_at(w1, r2, p2_in_w1)) by {
        assert(w1.subrange(p2_in_w1, p2_in_w1 + r2.lhs.len() as int) =~= l2) by {
            assert forall|k: int| 0 <= k < r2.lhs.len()
                implies w1[(p2_in_w1 + k) as int] == l2[k]
            by {
                // w1 = a ++ r1.rhs ++ b ++ l2 ++ c
                // Index p2_in_w1 + k is in the l2 region
                let idx = (p2_in_w1 + k) as int;
                let a_len: int = a.len() as int;
                let rhs_len: int = r1.rhs.len() as int;
                let b_len: int = b.len() as int;
                assert(a_len == p1);
                assert(b_len == p2 - p1 - r1.lhs.len());
                assert(p2_in_w1 == a_len + rhs_len + b_len);
                // So idx = a_len + rhs_len + b_len + k, which is in the l2 portion
            }
        }
    }

    // Common reduct: A ++ r1.rhs ++ B ++ r2.rhs ++ C
    let common = a + r1.rhs + (b + r2.rhs + c);

    // apply_rule_at(w1, r2, p2_in_w1) replaces l2 with r2.rhs in w1
    assert(apply_rule_at(w1, r2, p2_in_w1) =~= common) by {
        assert(w1.subrange(0, p2_in_w1) =~= a + r1.rhs + b) by {
            assert forall|k: int| 0 <= k < p2_in_w1
                implies w1[k] == (a + r1.rhs + b)[k] by {}
        }
        assert(w1.subrange(p2_in_w1 + r2.lhs.len() as int, w1.len() as int) =~= c) by {
            assert forall|k: int| 0 <= k < c.len()
                implies w1[(p2_in_w1 + r2.lhs.len() + k) as int] == c[k] by {}
        }
    }

    // apply_rule_at(w2, r1, p1) replaces l1 with r1.rhs in w2
    assert(apply_rule_at(w2, r1, p1) =~= common) by {
        assert(matches_at(w2, r1, p1)) by {
            assert(w2.subrange(p1, p1 + r1.lhs.len() as int) =~= l1) by {
                assert forall|k: int| 0 <= k < r1.lhs.len()
                    implies w2[(p1 + k) as int] == l1[k]
                by {
                    // w2 = a + l1 + (b + r2.rhs + c)
                    // at position p1 + k we're in the l1 region
                }
            }
        }
        assert(w2.subrange(0, p1) =~= a) by {
            assert forall|k: int| 0 <= k < p1
                implies w2[k] == a[k] by {}
        }
        assert(w2.subrange(p1 + r1.lhs.len() as int, w2.len() as int) =~= b + r2.rhs + c) by {
            assert forall|k: int| 0 <= k < (b + r2.rhs + c).len()
                implies w2[(p1 + r1.lhs.len() + k) as int] == (b + r2.rhs + c)[k] by {}
        }
    }
}

// ============================================================
// Overlap case: reducing to a critical pair + context
// ============================================================

/// When two rule matches overlap (suffix of r1 at p1 overlaps prefix of r2 at p2),
/// the local fork reduces to an overlap critical pair with surrounding context.
pub proof fn lemma_overlap_reduces_to_cp(
    sys: RewriteSystem,
    w: Word,
    ri1: int, p1: int,
    ri2: int, p2: int,
)
    requires
        0 <= ri1 < sys.rules.len(),
        0 <= ri2 < sys.rules.len(),
        matches_at(w, sys.rules[ri1], p1),
        matches_at(w, sys.rules[ri2], p2),
        // r1 starts before r2 and they overlap
        p1 < p2,
        p2 < p1 + sys.rules[ri1].lhs.len(),  // overlap exists
        p1 + sys.rules[ri1].lhs.len() <= p2 + sys.rules[ri2].lhs.len(),  // r1 doesn't fully contain r2
    ensures
        ({
            let r1 = sys.rules[ri1];
            let r2 = sys.rules[ri2];
            let olen: nat = (p1 + r1.lhs.len() - p2) as nat;
            let w1 = apply_rule_at(w, r1, p1);
            let w2 = apply_rule_at(w, r2, p2);
            let prefix = w.subrange(0, p1);
            let suffix = w.subrange(p2 + r2.lhs.len() as int, w.len() as int);
            let cp_l = overlap_cp_left(r1, r2, olen);
            let cp_r = overlap_cp_right(r1, r2, olen);
            &&& is_overlap(r1, r2, olen)
            &&& w1 =~= prefix + cp_l + suffix
            &&& w2 =~= prefix + cp_r + suffix
        }),
{
    let r1 = sys.rules[ri1];
    let r2 = sys.rules[ri2];
    let olen: nat = (p1 + r1.lhs.len() - p2) as nat;
    let prefix = w.subrange(0, p1);
    let suffix = w.subrange(p2 + r2.lhs.len() as int, w.len() as int);

    // The overlap: last olen of r1.lhs = first olen of r2.lhs
    assert(is_overlap(r1, r2, olen)) by {
        assert(r1.lhs.subrange(r1.lhs.len() - olen, r1.lhs.len() as int)
            =~= r2.lhs.subrange(0, olen as int)) by {
            assert forall|k: int| 0 <= k < olen as int
                implies r1.lhs[(r1.lhs.len() - olen + k) as int] == r2.lhs[k]
            by {
                // Both equal w[p2 + k]
                let wk = (p2 + k) as int;
                assert(r1.lhs[(r1.lhs.len() - olen + k) as int] == w[wk]) by {
                    assert(w.subrange(p1, p1 + r1.lhs.len() as int) =~= r1.lhs);
                }
                assert(r2.lhs[k] == w[wk]) by {
                    assert(w.subrange(p2, p2 + r2.lhs.len() as int) =~= r2.lhs);
                }
            }
        }
    }

    // w1 = apply_rule_at(w, r1, p1) = prefix + r1.rhs + w[p1+|l1|..]
    //     = prefix + r1.rhs + l2[olen..] + suffix = prefix + cp_l + suffix
    let w1 = apply_rule_at(w, r1, p1);
    let l2_tail = r2.lhs.subrange(olen as int, r2.lhs.len() as int);
    let cp_l = overlap_cp_left(r1, r2, olen);
    assert(cp_l =~= r1.rhs + l2_tail);

    assert(w1 =~= prefix + cp_l + suffix) by {
        // w[p1+|l1|..p2+|l2|] = l2[olen..] because the first olen of l2 overlaps with l1
        assert(w.subrange(p1 + r1.lhs.len() as int, p2 + r2.lhs.len() as int) =~= l2_tail) by {
            assert forall|k: int| 0 <= k < l2_tail.len()
                implies w[(p1 + r1.lhs.len() + k) as int] == l2_tail[k]
            by {
                assert(w[(p1 + r1.lhs.len() + k) as int] == w[(p2 + olen + k) as int]);
                assert(r2.lhs[(olen + k) as int] == w[(p2 + olen + k) as int]) by {
                    assert(w.subrange(p2, p2 + r2.lhs.len() as int) =~= r2.lhs);
                }
            }
        }
        // w1 = prefix + r1.rhs + w[p1+|l1|..end]
        //    = prefix + r1.rhs + l2_tail + suffix
        //    = prefix + (r1.rhs + l2_tail) + suffix
        //    = prefix + cp_l + suffix
        assert(w.subrange(p1 + r1.lhs.len() as int, w.len() as int) =~= l2_tail + suffix);
    }

    // w2 = apply_rule_at(w, r2, p2) = w[..p2] + r2.rhs + suffix
    //    = prefix + l1[..|l1|-olen] + r2.rhs + suffix = prefix + cp_r + suffix
    let w2 = apply_rule_at(w, r2, p2);
    let l1_head = r1.lhs.subrange(0, r1.lhs.len() - olen);
    let cp_r = overlap_cp_right(r1, r2, olen);
    assert(cp_r =~= l1_head + r2.rhs);

    assert(w2 =~= prefix + cp_r + suffix) by {
        // w[p1..p2] = l1[0..|l1|-olen]
        assert(w.subrange(p1, p2) =~= l1_head) by {
            assert forall|k: int| 0 <= k < l1_head.len()
                implies w[(p1 + k) as int] == l1_head[k]
            by {
                assert(r1.lhs[k] == w[(p1 + k) as int]) by {
                    assert(w.subrange(p1, p1 + r1.lhs.len() as int) =~= r1.lhs);
                }
            }
        }
        // w[0..p2] = prefix + l1_head
        assert(w.subrange(0, p2) =~= prefix + l1_head) by {
            assert forall|k: int| 0 <= k < p2
                implies w[k] == (prefix + l1_head)[k] by {}
        }
    }
}

// ============================================================
// Inclusion case: reducing to an inclusion critical pair + context
// ============================================================

/// When r2's LHS is entirely inside r1's match, the fork reduces to
/// an inclusion critical pair with surrounding context.
pub proof fn lemma_inclusion_reduces_to_cp(
    sys: RewriteSystem,
    w: Word,
    ri1: int, p1: int,
    ri2: int, p2: int,
)
    requires
        0 <= ri1 < sys.rules.len(),
        0 <= ri2 < sys.rules.len(),
        matches_at(w, sys.rules[ri1], p1),
        matches_at(w, sys.rules[ri2], p2),
        // r2's match is entirely within r1's match
        p1 <= p2,
        p2 + sys.rules[ri2].lhs.len() <= p1 + sys.rules[ri1].lhs.len(),
    ensures
        ({
            let r1 = sys.rules[ri1];
            let r2 = sys.rules[ri2];
            let ipos: nat = (p2 - p1) as nat;
            let w1 = apply_rule_at(w, r1, p1);
            let w2 = apply_rule_at(w, r2, p2);
            let prefix = w.subrange(0, p1);
            let suffix = w.subrange(p1 + r1.lhs.len() as int, w.len() as int);
            let cp_l = inclusion_cp_left(r1);
            let cp_r = inclusion_cp_right(r1, r2, ipos);
            &&& is_inclusion(r1, r2, ipos)
            &&& w1 =~= prefix + cp_l + suffix
            &&& w2 =~= prefix + cp_r + suffix
        }),
{
    let r1 = sys.rules[ri1];
    let r2 = sys.rules[ri2];
    let ipos: nat = (p2 - p1) as nat;
    let prefix = w.subrange(0, p1);
    let suffix = w.subrange(p1 + r1.lhs.len() as int, w.len() as int);

    // r2.lhs appears inside r1.lhs at position ipos
    assert(is_inclusion(r1, r2, ipos)) by {
        assert(r1.lhs.subrange(ipos as int, ipos + r2.lhs.len() as int) =~= r2.lhs) by {
            assert forall|k: int| 0 <= k < r2.lhs.len()
                implies r1.lhs[(ipos + k) as int] == r2.lhs[k]
            by {
                // Both equal w[p2 + k]
                assert(r1.lhs[(ipos + k) as int] == w[(p1 + ipos + k) as int]) by {
                    assert(w.subrange(p1, p1 + r1.lhs.len() as int) =~= r1.lhs);
                }
                assert(r2.lhs[k] == w[(p2 + k) as int]) by {
                    assert(w.subrange(p2, p2 + r2.lhs.len() as int) =~= r2.lhs);
                }
            }
        }
    }

    // w1 = prefix + r1.rhs + suffix (applying r1 replaces all of l1)
    let w1 = apply_rule_at(w, r1, p1);
    assert(w1 =~= prefix + r1.rhs + suffix);

    // w2 = prefix + l1[0..ipos] + r2.rhs + l1[ipos+|l2|..] + suffix
    //    = prefix + inclusion_cp_right(r1, r2, ipos) + suffix
    let w2 = apply_rule_at(w, r2, p2);
    let cp_r = inclusion_cp_right(r1, r2, ipos);
    assert(w2 =~= prefix + cp_r + suffix) by {
        // w[0..p2] = prefix + l1[0..ipos]
        assert(w.subrange(0, p2) =~= prefix + r1.lhs.subrange(0, ipos as int)) by {
            assert forall|k: int| 0 <= k < p2
                implies w[k] == (prefix + r1.lhs.subrange(0, ipos as int))[k]
            by {
                if k < p1 {
                    assert(w[k] == prefix[k]);
                } else {
                    assert(w[k] == r1.lhs[(k - p1) as int]) by {
                        assert(w.subrange(p1, p1 + r1.lhs.len() as int) =~= r1.lhs);
                    }
                }
            }
        }
        // w[p2+|l2|..p1+|l1|] = l1[ipos+|l2|..]
        assert(w.subrange(p2 + r2.lhs.len() as int, p1 + r1.lhs.len() as int)
            =~= r1.lhs.subrange(ipos + r2.lhs.len() as int, r1.lhs.len() as int)) by {
            assert forall|k: int| 0 <= k < (r1.lhs.len() - ipos - r2.lhs.len())
                implies w[(p2 + r2.lhs.len() + k) as int]
                    == r1.lhs[(ipos + r2.lhs.len() + k) as int]
            by {
                assert(w.subrange(p1, p1 + r1.lhs.len() as int) =~= r1.lhs);
            }
        }
        // Combine: w2 = w[0..p2] + r2.rhs + w[p2+|l2|..end]
        //             = (prefix + l1[0..ipos]) + r2.rhs + (l1[ipos+|l2|..] + suffix)
        //             = prefix + (l1[0..ipos] + r2.rhs + l1[ipos+|l2|..]) + suffix
        //             = prefix + cp_r + suffix
    }
}

// ============================================================
// The Critical Pair Lemma
// ============================================================

/// If joinability is preserved under adding context (prefix/suffix),
/// and all critical pairs are joinable, then any local fork is joinable.
///
/// Context lifting: if joinable(sys, u, v) then joinable(sys, p++u++s, p++v++s).
/// This holds when the system is length-decreasing (rules can fire in context).
pub proof fn lemma_joinable_in_context(
    sys: RewriteSystem, u: Word, v: Word, prefix: Word, suffix: Word,
)
    requires
        system_length_decreasing(sys),
        joinable(sys, u, v),
    ensures
        joinable(sys, prefix + u + suffix, prefix + v + suffix),
{
    // If u →* w and v →* w, then p++u++s →* p++w++s and p++v++s →* p++w++s.
    // Each rewrite step in u at position pos becomes a step in p++u++s at position |p|+pos.
    let w = choose|w: Word| rewrites_to(sys, u, w) && rewrites_to(sys, v, w);
    let n1 = choose|n: nat| rewrites_in_steps(sys, u, w, n);
    let n2 = choose|n: nat| rewrites_in_steps(sys, v, w, n);
    lemma_rewrites_in_context(sys, u, w, prefix, suffix, n1);
    lemma_rewrites_in_context(sys, v, w, prefix, suffix, n2);
}

/// Helper: if u →* v in n steps, then p++u++s →* p++v++s in n steps.
proof fn lemma_rewrites_in_context(
    sys: RewriteSystem, u: Word, v: Word,
    prefix: Word, suffix: Word, n: nat,
)
    requires
        rewrites_in_steps(sys, u, v, n),
    ensures
        rewrites_to(sys, prefix + u + suffix, prefix + v + suffix),
    decreases n,
{
    if n == 0 {
        assert((prefix + u + suffix) =~= (prefix + v + suffix));
        lemma_rewrites_to_refl(sys, prefix + u + suffix);
    } else if u =~= v {
        assert((prefix + u + suffix) =~= (prefix + v + suffix));
        lemma_rewrites_to_refl(sys, prefix + u + suffix);
    } else {
        let u_mid = choose|u_mid: Word|
            rewrites_one_step(sys, u, u_mid)
            && rewrites_in_steps(sys, u_mid, v, (n - 1) as nat);
        // u →¹ u_mid: exists ri, pos. matches_at(u, rule, pos) ...
        // In prefix + u + suffix, the same rule matches at |prefix| + pos
        lemma_one_step_in_context(sys, u, u_mid, prefix, suffix);
        // IH
        lemma_rewrites_in_context(sys, u_mid, v, prefix, suffix, (n - 1) as nat);
        // Chain
        lemma_one_step_implies_rewrites_to(sys, prefix + u + suffix, prefix + u_mid + suffix);
        lemma_rewrites_to_transitive(sys,
            prefix + u + suffix,
            prefix + u_mid + suffix,
            prefix + v + suffix);
    }
}

/// A one-step rewrite lifts to context: u →¹ v implies p++u++s →¹ p++v++s.
proof fn lemma_one_step_in_context(
    sys: RewriteSystem, u: Word, v: Word,
    prefix: Word, suffix: Word,
)
    requires
        rewrites_one_step(sys, u, v),
    ensures
        rewrites_one_step(sys, prefix + u + suffix, prefix + v + suffix),
{
    let (ri, pos) = choose|ri: int, pos: int|
        0 <= ri < sys.rules.len()
        && #[trigger] matches_at(u, sys.rules[ri], pos)
        && v == apply_rule_at(u, sys.rules[ri], pos);
    let rule = sys.rules[ri];
    let pu = prefix + u + suffix;
    let pv = prefix + v + suffix;
    let new_pos: int = prefix.len() + pos;

    // rule matches at new_pos in pu
    assert(matches_at(pu, rule, new_pos)) by {
        assert(pu.subrange(new_pos, new_pos + rule.lhs.len() as int) =~= rule.lhs) by {
            assert forall|k: int| 0 <= k < rule.lhs.len()
                implies pu[(new_pos + k) as int] == rule.lhs[k]
            by {
                assert(pu[(new_pos + k) as int] == u[(pos + k) as int]) by {
                    assert((prefix + u + suffix) =~= (prefix + (u + suffix)));
                }
                assert(u[(pos + k) as int] == rule.lhs[k]) by {
                    assert(u.subrange(pos, pos + rule.lhs.len() as int) =~= rule.lhs);
                }
            }
        }
    }

    // apply_rule_at(pu, rule, new_pos) =~= pv
    assert(pv =~= apply_rule_at(pu, rule, new_pos)) by {
        let result = apply_rule_at(pu, rule, new_pos);
        assert forall|k: int| 0 <= k < pv.len() implies pv[k] == result[k] by {
            // pv = prefix + v + suffix where v = u[..pos] + rule.rhs + u[pos+|lhs|..]
            // result = pu[..new_pos] + rule.rhs + pu[new_pos+|lhs|..]
        }
        assert(pv.len() == result.len());
    }
}

// ============================================================
// Main theorem: all CPs joinable → locally confluent
// ============================================================

/// The Critical Pair Lemma: if all critical pairs are joinable (and the system
/// is length-decreasing), then the system is locally confluent.
pub proof fn lemma_critical_pair_lemma(sys: RewriteSystem)
    requires
        system_length_decreasing(sys),
        all_cps_joinable(sys),
    ensures
        locally_confluent(sys),
{
    assert forall|w: Word, w1: Word, w2: Word|
        rewrites_one_step(sys, w, w1) && rewrites_one_step(sys, w, w2)
        implies joinable(sys, w1, w2)
    by {
        lemma_local_fork_joinable(sys, w, w1, w2);
    }
}

/// Any local fork in a system with all CPs joinable is joinable.
proof fn lemma_local_fork_joinable(
    sys: RewriteSystem, w: Word, w1: Word, w2: Word,
)
    requires
        system_length_decreasing(sys),
        all_cps_joinable(sys),
        rewrites_one_step(sys, w, w1),
        rewrites_one_step(sys, w, w2),
    ensures
        joinable(sys, w1, w2),
{
    let (ri1, p1) = choose|ri: int, pos: int|
        0 <= ri < sys.rules.len()
        && #[trigger] matches_at(w, sys.rules[ri], pos)
        && w1 == apply_rule_at(w, sys.rules[ri], pos);
    let (ri2, p2) = choose|ri: int, pos: int|
        0 <= ri < sys.rules.len()
        && #[trigger] matches_at(w, sys.rules[ri], pos)
        && w2 == apply_rule_at(w, sys.rules[ri], pos);
    let r1 = sys.rules[ri1];
    let r2 = sys.rules[ri2];

    // Determine the relationship between the two match regions
    // Region 1: [p1, p1 + |l1|)
    // Region 2: [p2, p2 + |l2|)

    if p1 + r1.lhs.len() <= p2 {
        // Disjoint: r1 entirely before r2
        lemma_disjoint_commute(w, r1, p1, r2, p2);
        // Both orderings give the same word → joinable via that word
        let common = apply_rule_at(apply_rule_at(w, r1, p1), r2,
            p2 + r1.rhs.len() - r1.lhs.len());
        lemma_rewrites_to_refl(sys, common);
        lemma_one_step_implies_rewrites_to(sys, w1, common);
        // For w2: apply r1 at p1
        assert(matches_at(w2, r1, p1)) by {
            lemma_disjoint_commute(w, r1, p1, r2, p2);
        }
        lemma_one_step_implies_rewrites_to(sys, w2, common);
    } else if p2 + r2.lhs.len() <= p1 {
        // Disjoint: r2 entirely before r1 (symmetric)
        lemma_disjoint_commute(w, r2, p2, r1, p1);
        let common = apply_rule_at(apply_rule_at(w, r2, p2), r1,
            p1 + r2.rhs.len() - r2.lhs.len());
        lemma_rewrites_to_refl(sys, common);
        lemma_one_step_implies_rewrites_to(sys, w2, common);
        assert(matches_at(w1, r2, p2)) by {
            lemma_disjoint_commute(w, r2, p2, r1, p1);
        }
        lemma_one_step_implies_rewrites_to(sys, w1, common);
    } else if p1 <= p2 && p2 + r2.lhs.len() <= p1 + r1.lhs.len() {
        // Inclusion: r2 inside r1
        lemma_inclusion_reduces_to_cp(sys, w, ri1, p1, ri2, p2);
        let ipos: nat = (p2 - p1) as nat;
        let prefix = w.subrange(0, p1);
        let suffix = w.subrange(p1 + r1.lhs.len() as int, w.len() as int);
        // w1 = prefix + cp_l + suffix, w2 = prefix + cp_r + suffix
        // cp_l and cp_r are joinable by hypothesis
        assert(joinable(sys, inclusion_cp_left(r1), inclusion_cp_right(r1, r2, ipos)));
        lemma_joinable_in_context(sys,
            inclusion_cp_left(r1), inclusion_cp_right(r1, r2, ipos),
            prefix, suffix);
    } else if p2 <= p1 && p1 + r1.lhs.len() <= p2 + r2.lhs.len() {
        // Inclusion: r1 inside r2 (symmetric)
        lemma_inclusion_reduces_to_cp(sys, w, ri2, p2, ri1, p1);
        let ipos: nat = (p1 - p2) as nat;
        let prefix = w.subrange(0, p2);
        let suffix = w.subrange(p2 + r2.lhs.len() as int, w.len() as int);
        assert(joinable(sys, inclusion_cp_left(r2), inclusion_cp_right(r2, r1, ipos)));
        lemma_joinable_in_context(sys,
            inclusion_cp_left(r2), inclusion_cp_right(r2, r1, ipos),
            prefix, suffix);
        // Need to swap: w2 = prefix + cp_l, w1 = prefix + cp_r
        lemma_joinable_symmetric(sys, prefix + inclusion_cp_left(r2) + suffix,
            prefix + inclusion_cp_right(r2, r1, ipos) + suffix);
    } else if p1 < p2 {
        // Overlap: r1 starts first, overlaps with r2
        assert(p2 < p1 + r1.lhs.len());  // from falling through disjoint
        assert(p1 + r1.lhs.len() <= p2 + r2.lhs.len());  // from falling through inclusion
        lemma_overlap_reduces_to_cp(sys, w, ri1, p1, ri2, p2);
        let olen: nat = (p1 + r1.lhs.len() - p2) as nat;
        let prefix = w.subrange(0, p1);
        let suffix = w.subrange(p2 + r2.lhs.len() as int, w.len() as int);
        assert(joinable(sys,
            overlap_cp_left(r1, r2, olen),
            overlap_cp_right(r1, r2, olen)));
        lemma_joinable_in_context(sys,
            overlap_cp_left(r1, r2, olen),
            overlap_cp_right(r1, r2, olen),
            prefix, suffix);
    } else {
        // Overlap: r2 starts first (p2 < p1), symmetric
        assert(p2 < p1);
        assert(p1 < p2 + r2.lhs.len());
        assert(p2 + r2.lhs.len() <= p1 + r1.lhs.len());
        lemma_overlap_reduces_to_cp(sys, w, ri2, p2, ri1, p1);
        let olen: nat = (p2 + r2.lhs.len() - p1) as nat;
        let prefix = w.subrange(0, p2);
        let suffix = w.subrange(p1 + r1.lhs.len() as int, w.len() as int);
        assert(joinable(sys,
            overlap_cp_left(r2, r1, olen),
            overlap_cp_right(r2, r1, olen)));
        lemma_joinable_in_context(sys,
            overlap_cp_left(r2, r1, olen),
            overlap_cp_right(r2, r1, olen),
            prefix, suffix);
        lemma_joinable_symmetric(sys,
            prefix + overlap_cp_left(r2, r1, olen) + suffix,
            prefix + overlap_cp_right(r2, r1, olen) + suffix);
    }
}

} // verus!
