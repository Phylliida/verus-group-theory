use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::rewrite::*;
use crate::runtime::*;

verus! {

// ============================================================
// Knuth-Bendix Completion — Exec Implementation
// ============================================================

/// A runtime rewrite rule: lhs → rhs.
pub struct RuntimeRule {
    pub lhs: Vec<RuntimeSymbol>,
    pub rhs: Vec<RuntimeSymbol>,
}

/// A runtime rewrite system.
pub struct RuntimeRewriteSystem {
    pub rules: Vec<RuntimeRule>,
}

/// Result of Knuth-Bendix completion.
pub enum KBResult {
    Complete { system: RuntimeRewriteSystem },
    Incomplete { system: RuntimeRewriteSystem },
}

// ============================================================
// Word operations
// ============================================================

/// Check if `pattern` matches at position `pos` in `word`.
pub fn matches_at_exec(
    word: &Vec<RuntimeSymbol>,
    pattern: &Vec<RuntimeSymbol>,
    pos: usize,
) -> (out: bool)
    requires
        pos as int + pattern@.len() <= word@.len(),
        word@.len() < usize::MAX,
{
    let mut i: usize = 0;
    while i < pattern.len()
        invariant
            0 <= i <= pattern.len(),
            pos + pattern.len() <= word.len(),
            word.len() < usize::MAX,
        decreases pattern.len() - i,
    {
        if word[pos + i] != pattern[i] {
            return false;
        }
        i = i + 1;
    }
    true
}

/// Find the first position where `pattern` matches in `word`, or None.
pub fn find_match_exec(
    word: &Vec<RuntimeSymbol>,
    pattern: &Vec<RuntimeSymbol>,
) -> (out: Option<usize>)
    requires
        pattern@.len() > 0,
        word@.len() < usize::MAX,
    ensures
        out.is_some() ==> out.unwrap() as int + pattern@.len() <= word@.len(),
{
    if word.len() < pattern.len() {
        return None;
    }
    let limit = word.len() - pattern.len();
    let mut pos: usize = 0;
    while pos <= limit
        invariant
            0 <= pos,
            limit == word.len() - pattern.len(),
            pattern@.len() > 0,
            word@.len() < usize::MAX,
        decreases limit - pos + 1,
    {
        if matches_at_exec(word, pattern, pos) {
            return Some(pos);
        }
        if pos == limit { return None; }
        pos = pos + 1;
    }
    None
}

/// Apply a rule at position `pos`: replace word[pos..pos+|lhs|] with rhs.
pub fn apply_rule_at_exec(
    word: &Vec<RuntimeSymbol>,
    lhs_len: usize,
    rhs: &Vec<RuntimeSymbol>,
    pos: usize,
) -> (out: Vec<RuntimeSymbol>)
    requires
        pos as int + lhs_len as int <= word@.len(),
        lhs_len > 0,
        rhs@.len() < lhs_len,  // length-decreasing
        word@.len() < usize::MAX,
    ensures
        out@.len() == word@.len() - lhs_len + rhs@.len(),
        out@.len() < word@.len(),
{
    let mut result: Vec<RuntimeSymbol> = Vec::new();
    // prefix
    let mut i: usize = 0;
    while i < pos
        invariant 0 <= i <= pos, pos <= word.len(), result@.len() == i as int,
        decreases pos - i,
    {
        result.push(word[i]);
        i = i + 1;
    }
    // rhs
    let mut j: usize = 0;
    while j < rhs.len()
        invariant 0 <= j <= rhs.len(), result@.len() == pos as int + j as int,
        decreases rhs.len() - j,
    {
        result.push(rhs[j]);
        j = j + 1;
    }
    // suffix
    let skip = pos + lhs_len;
    let mut m: usize = skip;
    while m < word.len()
        invariant
            skip <= m <= word.len(),
            skip == pos + lhs_len,
            result@.len() == pos as int + rhs@.len() + (m - skip) as int,
        decreases word.len() - m,
    {
        result.push(word[m]);
        m = m + 1;
    }
    result
}

/// Reduce a word to normal form under a rewrite system.
pub fn reduce_to_normal_form_exec(
    sys: &RuntimeRewriteSystem,
    word: &Vec<RuntimeSymbol>,
) -> (out: Vec<RuntimeSymbol>)
    requires
        word@.len() < usize::MAX,
        forall|i: int| 0 <= i < sys.rules@.len() ==>
            (#[trigger] sys.rules@[i]).lhs@.len() > 0
            && sys.rules@[i].rhs@.len() < sys.rules@[i].lhs@.len(),
    ensures
        out@.len() <= word@.len(),
{
    let mut current = word.clone();
    let mut fuel: usize = word.len();
    while fuel > 0
        invariant
            current@.len() <= word@.len(),
            current@.len() <= fuel,
            word@.len() < usize::MAX,
            forall|i: int| 0 <= i < sys.rules@.len() ==>
                (#[trigger] sys.rules@[i]).lhs@.len() > 0
                && sys.rules@[i].rhs@.len() < sys.rules@[i].lhs@.len(),
        decreases fuel,
    {
        let mut found = false;
        let mut ri: usize = 0;
        while ri < sys.rules.len()
            invariant_except_break
                0 <= ri <= sys.rules.len(),
                !found,
                current@.len() <= word@.len(),
                current@.len() <= fuel,
                current@.len() < usize::MAX,
                forall|i: int| 0 <= i < sys.rules@.len() ==>
                    (#[trigger] sys.rules@[i]).lhs@.len() > 0
                    && sys.rules@[i].rhs@.len() < sys.rules@[i].lhs@.len(),
            ensures
                current@.len() <= word@.len(),
                found ==> current@.len() < fuel,
                !found ==> current@.len() <= fuel,
            decreases sys.rules.len() - ri,
        {
            let rule = &sys.rules[ri];
            if rule.lhs.len() > 0 && current.len() >= rule.lhs.len() {
                match find_match_exec(&current, &rule.lhs) {
                    Some(pos) => {
                        let old_len = current.len();
                        let new_word = apply_rule_at_exec(&current, rule.lhs.len(), &rule.rhs, pos);
                        current = new_word;
                        found = true;
                        break;
                    }
                    None => { ri = ri + 1; }
                }
            } else {
                ri = ri + 1;
            }
        }
        if !found {
            return current;
        }
        fuel = fuel - 1;
    }
    current
}

// ============================================================
// Critical pair computation
// ============================================================

/// Compute overlap critical pairs between two rules.
pub fn compute_overlap_cps_exec(
    r1: &RuntimeRule,
    r2: &RuntimeRule,
) -> (out: Vec<(Vec<RuntimeSymbol>, Vec<RuntimeSymbol>)>)
    requires
        r1.lhs@.len() > 0,
        r2.lhs@.len() > 0,
{
    let mut pairs: Vec<(Vec<RuntimeSymbol>, Vec<RuntimeSymbol>)> = Vec::new();
    let max_ov = if r1.lhs.len() < r2.lhs.len() { r1.lhs.len() } else { r2.lhs.len() };

    let mut olen: usize = 1;
    while olen <= max_ov
        invariant 1 <= olen, max_ov <= r1.lhs.len(), max_ov <= r2.lhs.len(),
        decreases max_ov - olen + 1,
    {
        // Check if last `olen` of r1.lhs == first `olen` of r2.lhs
        let offset = r1.lhs.len() - olen;
        let mut ok = true;
        let mut k: usize = 0;
        while k < olen
            invariant
                0 <= k <= olen,
                olen <= r1.lhs.len(),
                olen <= r2.lhs.len(),
                offset == r1.lhs.len() - olen,
                offset + olen == r1.lhs.len(),
            decreases olen - k,
        {
            if r1.lhs[offset + k] != r2.lhs[k] {
                ok = false;
                break;
            }
            k = k + 1;
        }

        if ok {
            // cp_left: r1.rhs ++ r2.lhs[olen..]
            let mut cp_left: Vec<RuntimeSymbol> = Vec::new();
            let mut i: usize = 0;
            while i < r1.rhs.len()
                invariant 0 <= i <= r1.rhs.len(),
                decreases r1.rhs.len() - i,
            { cp_left.push(r1.rhs[i]); i = i + 1; }
            let mut j: usize = olen;
            while j < r2.lhs.len()
                invariant olen <= j <= r2.lhs.len(),
                decreases r2.lhs.len() - j,
            { cp_left.push(r2.lhs[j]); j = j + 1; }

            // cp_right: r1.lhs[0..offset] ++ r2.rhs
            let mut cp_right: Vec<RuntimeSymbol> = Vec::new();
            let mut i2: usize = 0;
            while i2 < offset
                invariant 0 <= i2 <= offset, offset < r1.lhs.len(),
                decreases offset - i2,
            { cp_right.push(r1.lhs[i2]); i2 = i2 + 1; }
            let mut j2: usize = 0;
            while j2 < r2.rhs.len()
                invariant 0 <= j2 <= r2.rhs.len(),
                decreases r2.rhs.len() - j2,
            { cp_right.push(r2.rhs[j2]); j2 = j2 + 1; }

            pairs.push((cp_left, cp_right));
        }

        if olen == max_ov { break; }
        olen = olen + 1;
    }
    pairs
}

// ============================================================
// Shortlex comparison and word equality
// ============================================================

/// Compare two words: true if w1 > w2 in shortlex.
pub fn shortlex_gt_exec(w1: &Vec<RuntimeSymbol>, w2: &Vec<RuntimeSymbol>) -> (out: bool)
    requires
        // Generator indices small enough to avoid overflow in 2*n+1
        forall|k: int| 0 <= k < w1@.len() ==> match #[trigger] w1@[k] {
            RuntimeSymbol::Gen(n) => n < usize::MAX / 2,
            RuntimeSymbol::Inv(n) => n < usize::MAX / 2,
        },
        forall|k: int| 0 <= k < w2@.len() ==> match #[trigger] w2@[k] {
            RuntimeSymbol::Gen(n) => n < usize::MAX / 2,
            RuntimeSymbol::Inv(n) => n < usize::MAX / 2,
        },
{
    if w1.len() > w2.len() { return true; }
    if w1.len() < w2.len() { return false; }
    let mut i: usize = 0;
    while i < w1.len()
        invariant 0 <= i <= w1.len(), w1.len() == w2.len(),
            forall|k: int| 0 <= k < w1@.len() ==> match #[trigger] w1@[k] {
                RuntimeSymbol::Gen(n) => n < usize::MAX / 2,
                RuntimeSymbol::Inv(n) => n < usize::MAX / 2,
            },
            forall|k: int| 0 <= k < w2@.len() ==> match #[trigger] w2@[k] {
                RuntimeSymbol::Gen(n) => n < usize::MAX / 2,
                RuntimeSymbol::Inv(n) => n < usize::MAX / 2,
            },
        decreases w1.len() - i,
    {
        let o1: usize = match w1[i] {
            RuntimeSymbol::Gen(n) => 2 * n,
            RuntimeSymbol::Inv(n) => 2 * n + 1,
        };
        let o2: usize = match w2[i] {
            RuntimeSymbol::Gen(n) => 2 * n,
            RuntimeSymbol::Inv(n) => 2 * n + 1,
        };
        if o1 > o2 { return true; }
        if o1 < o2 { return false; }
        i = i + 1;
    }
    false
}

/// Check two runtime words for equality.
pub fn words_equal_exec(w1: &Vec<RuntimeSymbol>, w2: &Vec<RuntimeSymbol>) -> (out: bool)
{
    if w1.len() != w2.len() { return false; }
    let mut i: usize = 0;
    while i < w1.len()
        invariant 0 <= i <= w1.len(), w1.len() == w2.len(),
        decreases w1.len() - i,
    {
        if w1[i] != w2[i] { return false; }
        i = i + 1;
    }
    true
}

// ============================================================
// Main completion loop
// ============================================================

/// Try to find one unresolved critical pair and add a new rule.
/// Returns Some(rule) if a new rule was found, None if all CPs resolve.
/// Returns Err if a non-length-decreasing rule would be needed.
fn find_new_rule_exec(
    sys: &RuntimeRewriteSystem,
) -> (out: Option<Option<RuntimeRule>>)
    requires
        forall|i: int| 0 <= i < sys.rules@.len() ==>
            (#[trigger] sys.rules@[i]).lhs@.len() > 0
            && sys.rules@[i].rhs@.len() < sys.rules@[i].lhs@.len(),
    ensures
        // Some(Some(rule)): new rule found, length-decreasing
        // Some(None): non-length-decreasing pair found (incomplete)
        // None: all CPs resolve (confluent)
        match out {
            Some(Some(rule)) => rule.lhs@.len() > 0 && rule.rhs@.len() < rule.lhs@.len(),
            _ => true,
        },
{
    let num_rules = sys.rules.len();
    let mut i: usize = 0;
    while i < num_rules
        invariant
            0 <= i <= num_rules,
            num_rules == sys.rules@.len(),
            forall|k: int| 0 <= k < sys.rules@.len() ==>
                (#[trigger] sys.rules@[k]).lhs@.len() > 0
                && sys.rules@[k].rhs@.len() < sys.rules@[k].lhs@.len(),
        decreases num_rules - i,
    {
        let mut j: usize = 0;
        while j < num_rules
            invariant
                0 <= j <= num_rules,
                0 <= i < num_rules,
                num_rules == sys.rules@.len(),
                forall|k: int| 0 <= k < sys.rules@.len() ==>
                    (#[trigger] sys.rules@[k]).lhs@.len() > 0
                    && sys.rules@[k].rhs@.len() < sys.rules@[k].lhs@.len(),
            decreases num_rules - j,
        {
            let cps = compute_overlap_cps_exec(&sys.rules[i], &sys.rules[j]);
            let mut cp_idx: usize = 0;
            while cp_idx < cps.len()
                invariant
                    0 <= cp_idx <= cps.len(),
                    num_rules == sys.rules@.len(),
                    forall|k: int| 0 <= k < sys.rules@.len() ==>
                        (#[trigger] sys.rules@[k]).lhs@.len() > 0
                        && sys.rules@[k].rhs@.len() < sys.rules@[k].lhs@.len(),
                decreases cps.len() - cp_idx,
            {
                let (ref cp_l, ref cp_r) = cps[cp_idx];
                if cp_l.len() < usize::MAX && cp_r.len() < usize::MAX {
                    let nf_l = reduce_to_normal_form_exec(sys, cp_l);
                    let nf_r = reduce_to_normal_form_exec(sys, cp_r);

                    if !words_equal_exec(&nf_l, &nf_r) {
                        // Orient: larger → smaller
                        if nf_l.len() > nf_r.len() {
                            return Some(Some(RuntimeRule { lhs: nf_l, rhs: nf_r }));
                        } else if nf_r.len() > nf_l.len() {
                            return Some(Some(RuntimeRule { lhs: nf_r, rhs: nf_l }));
                        } else {
                            // Same length, can't orient as length-decreasing
                            return Some(None);
                        }
                    }
                }
                cp_idx = cp_idx + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    None  // all CPs resolve
}

/// Run Knuth-Bendix completion.
///
/// `initial_rules`: starting rules (from oriented relators + free cancellations)
/// `max_rules`: maximum number of rules before aborting
pub fn knuth_bendix_exec(
    initial_rules: Vec<RuntimeRule>,
    max_rules: usize,
) -> (out: KBResult)
    requires
        max_rules > 0,
        max_rules < 10000,
        initial_rules@.len() <= max_rules,
        forall|i: int| 0 <= i < initial_rules@.len() ==>
            (#[trigger] initial_rules@[i]).lhs@.len() > 0
            && initial_rules@[i].rhs@.len() < initial_rules@[i].lhs@.len(),
{
    let mut sys = RuntimeRewriteSystem { rules: initial_rules };
    let mut fuel: usize = max_rules;
    while fuel > 0
        invariant
            sys.rules@.len() <= max_rules,
            max_rules < 10000,
            forall|i: int| 0 <= i < sys.rules@.len() ==>
                (#[trigger] sys.rules@[i]).lhs@.len() > 0
                && sys.rules@[i].rhs@.len() < sys.rules@[i].lhs@.len(),
        decreases fuel,
    {
        fuel = fuel - 1;
        match find_new_rule_exec(&sys) {
            None => {
                // All CPs resolve — confluent!
                return KBResult::Complete { system: sys };
            }
            Some(None) => {
                // Can't orient as length-decreasing
                return KBResult::Incomplete { system: sys };
            }
            Some(Some(new_rule)) => {
                if sys.rules.len() < max_rules {
                    sys.rules.push(new_rule);
                } else {
                    return KBResult::Incomplete { system: sys };
                }
            }
        }
    }
    KBResult::Incomplete { system: sys }
}

// ============================================================
// Build initial rules from a presentation
// ============================================================

/// Build initial rewrite rules from relators + free cancellation rules.
pub fn build_initial_rules_exec(
    num_generators: usize,
    relators: &Vec<Vec<RuntimeSymbol>>,
) -> (out: Vec<RuntimeRule>)
    requires
        num_generators < 10000,
        relators@.len() < 10000,
    ensures
        out@.len() <= 2 * num_generators + relators@.len(),
        forall|i: int| 0 <= i < out@.len() ==>
            (#[trigger] out@[i]).lhs@.len() > 0
            && out@[i].rhs@.len() < out@[i].lhs@.len(),
{
    let mut rules: Vec<RuntimeRule> = Vec::new();

    // Free cancellation rules: Gen(i)·Inv(i) → ε, Inv(i)·Gen(i) → ε
    let mut g: usize = 0;
    while g < num_generators
        invariant
            0 <= g <= num_generators,
            num_generators < 10000,
            rules@.len() == 2 * g,
            forall|k: int| 0 <= k < rules@.len() ==>
                (#[trigger] rules@[k]).lhs@.len() > 0
                && rules@[k].rhs@.len() < rules@[k].lhs@.len(),
        decreases num_generators - g,
    {
        let mut lhs1: Vec<RuntimeSymbol> = Vec::new();
        lhs1.push(RuntimeSymbol::Gen(g));
        lhs1.push(RuntimeSymbol::Inv(g));
        rules.push(RuntimeRule { lhs: lhs1, rhs: Vec::new() });

        let mut lhs2: Vec<RuntimeSymbol> = Vec::new();
        lhs2.push(RuntimeSymbol::Inv(g));
        lhs2.push(RuntimeSymbol::Gen(g));
        rules.push(RuntimeRule { lhs: lhs2, rhs: Vec::new() });

        g = g + 1;
    }

    // Relator rules: w → ε
    let mut r: usize = 0;
    while r < relators.len()
        invariant
            0 <= r <= relators.len(),
            rules@.len() <= 2 * num_generators + r,
            forall|k: int| 0 <= k < rules@.len() ==>
                (#[trigger] rules@[k]).lhs@.len() > 0
                && rules@[k].rhs@.len() < rules@[k].lhs@.len(),
        decreases relators.len() - r,
    {
        if relators[r].len() > 0 {
            let rel = &relators[r];
            let mut lhs: Vec<RuntimeSymbol> = Vec::new();
            let mut k: usize = 0;
            while k < rel.len()
                invariant 0 <= k <= rel.len(), lhs@.len() == k as int,
                decreases rel.len() - k,
            { lhs.push(rel[k]); k = k + 1; }
            rules.push(RuntimeRule { lhs, rhs: Vec::new() });
        }
        r = r + 1;
    }
    rules
}

} // verus!
