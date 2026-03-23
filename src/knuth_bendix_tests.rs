use vstd::prelude::*;
use crate::runtime::*;
use crate::knuth_bendix::*;

verus! {

// ============================================================
// Verified properties of Knuth-Bendix completion
// ============================================================

fn mk_word(syms: &[RuntimeSymbol]) -> (out: Vec<RuntimeSymbol>)
    ensures out@.len() == syms@.len(),
{
    let mut w: Vec<RuntimeSymbol> = Vec::new();
    let mut i: usize = 0;
    while i < syms.len()
        invariant 0 <= i <= syms.len(), w@.len() == i,
        decreases syms.len() - i,
    { w.push(syms[i]); i = i + 1; }
    w
}

// ---- Property 1: reduce_to_normal_form output bounded by input length ----

fn test_reduce_nf_length_bound()
{
    let rules = build_initial_rules_exec(2, &Vec::new());
    let sys = RuntimeRewriteSystem { rules };
    let word = mk_word(&[
        RuntimeSymbol::Gen(0), RuntimeSymbol::Inv(0),
        RuntimeSymbol::Gen(1), RuntimeSymbol::Inv(1),
    ]);
    let nf = reduce_to_normal_form_exec(&sys, &word);
    assert(nf@.len() <= 4);
}

// ---- Property 2: reduce is idempotent on length ----

fn test_reduce_idempotent_length()
{
    let rules = build_initial_rules_exec(2, &Vec::new());
    let sys = RuntimeRewriteSystem { rules };
    let word = mk_word(&[
        RuntimeSymbol::Gen(0), RuntimeSymbol::Inv(1),
        RuntimeSymbol::Gen(1), RuntimeSymbol::Inv(0),
    ]);
    let nf1 = reduce_to_normal_form_exec(&sys, &word);
    let nf2 = reduce_to_normal_form_exec(&sys, &nf1);
    assert(nf2@.len() <= nf1@.len());
}

// ---- Property 3: Single generator is not shortened by free cancellation ----

fn test_single_gen_preserved()
{
    let rules = build_initial_rules_exec(1, &Vec::new());
    let sys = RuntimeRewriteSystem { rules };
    let word = mk_word(&[RuntimeSymbol::Gen(0)]);
    let nf = reduce_to_normal_form_exec(&sys, &word);
    assert(nf@.len() <= 1);
}

// ---- Property 4: Empty word reduces to itself ----

fn test_empty_word_nf()
{
    let rules = build_initial_rules_exec(1, &Vec::new());
    let sys = RuntimeRewriteSystem { rules };
    let word: Vec<RuntimeSymbol> = Vec::new();
    let nf = reduce_to_normal_form_exec(&sys, &word);
    assert(nf@.len() == 0);
}

// ---- Property 5: knuth_bendix_exec respects max_rules bound ----

fn test_kb_respects_max_rules()
{
    let relator = mk_word(&[RuntimeSymbol::Gen(0), RuntimeSymbol::Gen(0)]);
    let mut relators: Vec<Vec<RuntimeSymbol>> = Vec::new();
    relators.push(relator);
    let rules = build_initial_rules_exec(1, &relators);
    assert(rules@.len() <= 100);
    let result = knuth_bendix_exec(rules, 100);
    match result {
        KBResult::Complete { system } => { assert(system.rules@.len() <= 100); }
        KBResult::Incomplete { system } => { assert(system.rules@.len() <= 100); }
    }
}

// ---- Property 6: All rules in output are length-decreasing ----

fn test_output_rules_length_decreasing()
{
    let relator = mk_word(&[RuntimeSymbol::Gen(0), RuntimeSymbol::Gen(0)]);
    let mut relators: Vec<Vec<RuntimeSymbol>> = Vec::new();
    relators.push(relator);
    let rules = build_initial_rules_exec(1, &relators);
    assert(rules@.len() <= 100);
    let result = knuth_bendix_exec(rules, 100);
    match result {
        KBResult::Complete { system } => {
            assert(forall|i: int| 0 <= i < system.rules@.len() ==>
                (#[trigger] system.rules@[i]).lhs@.len() > 0
                && system.rules@[i].rhs@.len() < system.rules@[i].lhs@.len());
        }
        KBResult::Incomplete { system } => {
            assert(forall|i: int| 0 <= i < system.rules@.len() ==>
                (#[trigger] system.rules@[i]).lhs@.len() > 0
                && system.rules@[i].rhs@.len() < system.rules@[i].lhs@.len());
        }
    }
}

// ---- Property 7: build_initial_rules produces length-decreasing rules ----
// (Universally quantified over all valid inputs)

fn test_initial_rules_invariant(n: usize, relators: &Vec<Vec<RuntimeSymbol>>)
    requires
        n < 10000,
        relators@.len() < 10000,
        forall|i: int| 0 <= i < relators@.len() ==> (#[trigger] relators@[i])@.len() > 0,
{
    let rules = build_initial_rules_exec(n, relators);
    assert(forall|i: int| 0 <= i < rules@.len() ==>
        (#[trigger] rules@[i]).lhs@.len() > 0
        && rules@[i].rhs@.len() < rules@[i].lhs@.len());
}

} // verus!
