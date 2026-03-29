use vstd::prelude::*;
use crate::runtime::*;
use crate::knuth_bendix::*;

verus! {

//  ============================================================
//  Verified properties of Knuth-Bendix completion
//  ============================================================

//  ---- Property 1: reduce output bounded by input ----

fn test_reduce_nf_length_bound()
{
    let rules = build_initial_rules_exec(2, &Vec::new());
    //  rules.len() <= 2*2 + 0 = 4
    let sys = RuntimeRewriteSystem { rules };
    let mut word: Vec<RuntimeSymbol> = Vec::new();
    word.push(RuntimeSymbol::Gen(0));
    word.push(RuntimeSymbol::Inv(0));
    word.push(RuntimeSymbol::Gen(1));
    word.push(RuntimeSymbol::Inv(1));
    assert(word@.len() == 4);
    assert(word@.len() < usize::MAX);
    let nf = reduce_to_normal_form_exec(&sys, &word);
    assert(nf@.len() <= 4);
}

//  ---- Property 2: reduce is idempotent on length ----

fn test_reduce_idempotent_length()
{
    let rules = build_initial_rules_exec(2, &Vec::new());
    let sys = RuntimeRewriteSystem { rules };
    let mut word: Vec<RuntimeSymbol> = Vec::new();
    word.push(RuntimeSymbol::Gen(0));
    word.push(RuntimeSymbol::Inv(1));
    word.push(RuntimeSymbol::Gen(1));
    word.push(RuntimeSymbol::Inv(0));
    assert(word@.len() < usize::MAX);
    let nf1 = reduce_to_normal_form_exec(&sys, &word);
    assert(nf1@.len() <= word@.len());
    assert(nf1@.len() < usize::MAX);
    let nf2 = reduce_to_normal_form_exec(&sys, &nf1);
    assert(nf2@.len() <= nf1@.len());
}

//  ---- Property 3: Single generator stays length ≤ 1 ----

fn test_single_gen_preserved()
{
    let rules = build_initial_rules_exec(1, &Vec::new());
    let sys = RuntimeRewriteSystem { rules };
    let mut word: Vec<RuntimeSymbol> = Vec::new();
    word.push(RuntimeSymbol::Gen(0));
    assert(word@.len() < usize::MAX);
    let nf = reduce_to_normal_form_exec(&sys, &word);
    assert(nf@.len() <= 1);
}

//  ---- Property 4: Empty word reduces to empty ----

fn test_empty_word_nf()
{
    let rules = build_initial_rules_exec(1, &Vec::new());
    let sys = RuntimeRewriteSystem { rules };
    let word: Vec<RuntimeSymbol> = Vec::new();
    assert(word@.len() < usize::MAX);
    let nf = reduce_to_normal_form_exec(&sys, &word);
    assert(nf@.len() == 0);
}

//  ---- Property 5: KB respects max_rules bound ----

fn test_kb_respects_max_rules()
{
    let mut relator: Vec<RuntimeSymbol> = Vec::new();
    relator.push(RuntimeSymbol::Gen(0));
    relator.push(RuntimeSymbol::Gen(0));
    let mut relators: Vec<Vec<RuntimeSymbol>> = Vec::new();
    relators.push(relator);
    let rules = build_initial_rules_exec(1, &relators);
    //  rules.len() <= 2*1 + 1 = 3 <= 100
    assert(rules@.len() <= 3);
    let result = knuth_bendix_exec(rules, 100);
    match result {
        KBResult::Complete { system } => { assert(system.rules@.len() <= 100); }
        KBResult::Incomplete { system } => { assert(system.rules@.len() <= 100); }
    }
}

//  ---- Property 6: Output rules are all length-decreasing ----

fn test_output_rules_length_decreasing()
{
    let mut relator: Vec<RuntimeSymbol> = Vec::new();
    relator.push(RuntimeSymbol::Gen(0));
    relator.push(RuntimeSymbol::Gen(0));
    let mut relators: Vec<Vec<RuntimeSymbol>> = Vec::new();
    relators.push(relator);
    let rules = build_initial_rules_exec(1, &relators);
    assert(rules@.len() <= 3);
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

//  ---- Property 7: build_initial_rules is universally length-decreasing ----

fn test_initial_rules_universal(n: usize, relators: &Vec<Vec<RuntimeSymbol>>)
    requires
        n < 10000,
        relators@.len() < 10000,
        forall|i: int| 0 <= i < relators@.len() ==> (#[trigger] relators@[i])@.len() > 0,
{
    let rules = build_initial_rules_exec(n, relators);
    //  This is directly from the ensures of build_initial_rules_exec
    assert(forall|i: int| 0 <= i < rules@.len() ==>
        (#[trigger] rules@[i]).lhs@.len() > 0
        && rules@[i].rhs@.len() < rules@[i].lhs@.len());
}

} //  verus!
