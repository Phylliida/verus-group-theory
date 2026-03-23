use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::rewrite::*;

verus! {

// ============================================================
// Generalized Newman's Lemma
// ============================================================
//
// A terminating, locally confluent rewriting system is confluent.
//
// Termination: every rule strictly decreases word length (system_length_decreasing).
// This is stronger than general shortlex but sufficient for most group presentations
// and simpler to prove (decreases on w.len() directly).
//
// Generalizes the free-reduction confluence proof in reduction.rs.

/// Newman's lemma: length-decreasing + locally confluent → confluent.
pub proof fn lemma_newman(
    sys: RewriteSystem, w: Word, w1: Word, w2: Word,
)
    requires
        system_length_decreasing(sys),
        locally_confluent(sys),
        rewrites_to(sys, w, w1),
        rewrites_to(sys, w, w2),
    ensures
        joinable(sys, w1, w2),
    decreases w.len(),
{
    let n1 = choose|n: nat| rewrites_in_steps(sys, w, w1, n);
    let n2 = choose|n: nat| rewrites_in_steps(sys, w, w2, n);
    lemma_newman_aux(sys, w, w1, w2, n1, n2);
}

proof fn lemma_newman_aux(
    sys: RewriteSystem, w: Word, w1: Word, w2: Word, n1: nat, n2: nat,
)
    requires
        system_length_decreasing(sys),
        locally_confluent(sys),
        rewrites_in_steps(sys, w, w1, n1),
        rewrites_in_steps(sys, w, w2, n2),
    ensures
        joinable(sys, w1, w2),
    decreases w.len(),
{
    if n1 == 0 || w =~= w1 {
        lemma_rewrites_to_refl(sys, w2);
        if w =~= w1 {
            assert(rewrites_in_steps(sys, w1, w2, n2));
            assert(rewrites_to(sys, w1, w2));
        }
    } else if n2 == 0 || w =~= w2 {
        lemma_rewrites_to_refl(sys, w1);
        if w =~= w2 {
            assert(rewrites_in_steps(sys, w2, w1, n1));
            assert(rewrites_to(sys, w2, w1));
        }
    } else {
        // w →¹ wa →* w1  and  w →¹ wb →* w2
        let wa = choose|wa: Word|
            rewrites_one_step(sys, w, wa)
            && rewrites_in_steps(sys, wa, w1, (n1 - 1) as nat);
        let wb = choose|wb: Word|
            rewrites_one_step(sys, w, wb)
            && rewrites_in_steps(sys, wb, w2, (n2 - 1) as nat);

        // Strict length decrease: wa.len() < w.len(), wb.len() < w.len()
        lemma_one_step_strictly_decreases_len(sys, w, wa);
        lemma_one_step_strictly_decreases_len(sys, w, wb);

        // Local confluence: ∃ wc. wa →* wc ∧ wb →* wc
        assert(joinable(sys, wa, wb));
        let wc = choose|wc: Word| rewrites_to(sys, wa, wc) && rewrites_to(sys, wb, wc);

        // IH on wa: wa →* w1 and wa →* wc are joinable
        lemma_newman_aux(sys, wa, w1, wc,
            (n1 - 1) as nat,
            choose|n: nat| rewrites_in_steps(sys, wa, wc, n));
        let d = choose|d: Word| rewrites_to(sys, w1, d) && rewrites_to(sys, wc, d);

        // IH on wb: wb →* w2 and wb →* wc are joinable
        lemma_newman_aux(sys, wb, w2, wc,
            (n2 - 1) as nat,
            choose|n: nat| rewrites_in_steps(sys, wb, wc, n));
        let e = choose|e: Word| rewrites_to(sys, w2, e) && rewrites_to(sys, wc, e);

        // wc.len() <= wa.len() < w.len() (rewriting can't increase length)
        lemma_length_decreasing_implies_wf(sys);
        let nc = choose|n: nat| rewrites_in_steps(sys, wa, wc, n);
        lemma_rewrites_to_len(sys, wa, wc, nc);

        // IH on wc: wc →* d and wc →* e are joinable
        let nd = choose|n: nat| rewrites_in_steps(sys, wc, d, n);
        let ne = choose|n: nat| rewrites_in_steps(sys, wc, e, n);
        lemma_newman_aux(sys, wc, d, e, nd, ne);
        let f = choose|f: Word| rewrites_to(sys, d, f) && rewrites_to(sys, e, f);

        // Chain: w1 →* d →* f  and  w2 →* e →* f
        lemma_rewrites_to_transitive(sys, w1, d, f);
        lemma_rewrites_to_transitive(sys, w2, e, f);
    }
}

/// Main theorem: length-decreasing + locally confluent → confluent.
pub proof fn lemma_length_decreasing_locally_confluent_implies_confluent(
    sys: RewriteSystem,
)
    requires
        system_length_decreasing(sys),
        locally_confluent(sys),
    ensures
        confluent(sys),
{
    assert forall|w: Word, w1: Word, w2: Word|
        rewrites_to(sys, w, w1) && rewrites_to(sys, w, w2)
        implies joinable(sys, w1, w2)
    by {
        lemma_newman(sys, w, w1, w2);
    }
}

} // verus!
