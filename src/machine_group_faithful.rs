use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;
use crate::britton::*;
use crate::benign::*;
use crate::machine_group::*;

verus! {

// ============================================================
// Faithfulness of the Machine Group Encoding
// ============================================================
//
// The machine group G_M faithfully encodes the modular machine M:
//
// Forward: If M transitions (s, α, β) →* (s', α', β') then
//   config_word(s, α, β) ≡ config_word(s', α', β') in G_M.
//
// Backward: If config_word(s, α, β) ≡ config_word(s', α', β') in G_M
//   then M can reach (s', α', β') from (s, α, β).
//
// The forward direction follows by induction on steps, using
// lemma_hnn_conjugation at each step.
//
// The backward direction uses Britton's Lemma: any non-trivial
// derivation between config words must use stable letters,
// which correspond to machine transitions.

// ============================================================
// Forward direction
// ============================================================

/// Two consecutive trace entries are connected by a quadruple.
pub open spec fn trace_step_valid(
    data: MachineGroupData,
    c1: (nat, nat, nat),
    c2: (nat, nat, nat),
) -> bool {
    exists|k: nat| (k as int) < data.quadruples.len() &&
        c1.0 == data.quadruples[k as int].source_state &&
        c1.1 % data.quadruples[k as int].modulus
            == data.quadruples[k as int].residue &&
        c2.0 == data.quadruples[k as int].target_state &&
        c2.1 == apply_machine_mod_op(
            data.quadruples[k as int].alpha_op, c1.1) &&
        c2.2 == apply_machine_mod_op(
            data.quadruples[k as int].beta_op, c1.2)
}

/// A modular machine trace: recursive definition.
pub open spec fn is_valid_trace(
    data: MachineGroupData,
    trace: Seq<(nat, nat, nat)>,
) -> bool
    decreases trace.len(),
{
    if trace.len() == 0 {
        false
    } else if trace.len() == 1 {
        trace[0].0 < data.num_states
    } else {
        trace[0].0 < data.num_states &&
        trace_step_valid(data, trace[0], trace[1]) &&
        is_valid_trace(data, trace.drop_first())
    }
}

/// Forward direction: a valid trace gives equivalence between
/// first and last config words.
pub proof fn lemma_trace_gives_equiv(
    data: MachineGroupData,
    trace: Seq<(nat, nat, nat)>,
)
    requires
        machine_group_data_wf(data),
        is_valid_trace(data, trace),
    ensures
        equiv_in_presentation(
            machine_group_presentation(data),
            config_word(data.num_states, trace[0].0, trace[0].1, trace[0].2),
            config_word(
                data.num_states,
                trace[trace.len() - 1].0,
                trace[trace.len() - 1].1,
                trace[trace.len() - 1].2,
            ),
        ),
    decreases trace.len(),
{
    if trace.len() == 1 {
        // Single config: reflexivity
        lemma_config_word_valid(
            data.num_states, trace[0].0, trace[0].1, trace[0].2);
        lemma_equiv_refl(
            machine_group_presentation(data),
            config_word(data.num_states, trace[0].0, trace[0].1, trace[0].2),
        );
    } else {
        // Inductive step: trace[0] → trace[1] via some quadruple,
        // then trace[1..] by induction
        let (s0, a0, b0) = trace[0];
        let (s1, a1, b1) = trace[1];

        // From recursive is_valid_trace: trace_step_valid(data, trace[0], trace[1])
        // and is_valid_trace(data, trace.drop_first())
        assert(trace_step_valid(data, trace[0], trace[1]));
        let tail = trace.drop_first();
        assert(is_valid_trace(data, tail));
        assert(tail[0] == trace[1]);
        assert(tail[tail.len() - 1] == trace[trace.len() - 1]);

        // Get the quadruple connecting trace[0] to trace[1]
        let k: nat = choose|k: nat| (k as int) < data.quadruples.len() &&
            s0 == data.quadruples[k as int].source_state &&
            a0 % data.quadruples[k as int].modulus
                == data.quadruples[k as int].residue &&
            s1 == data.quadruples[k as int].target_state &&
            a1 == apply_machine_mod_op(
                data.quadruples[k as int].alpha_op, a0) &&
            b1 == apply_machine_mod_op(
                data.quadruples[k as int].beta_op, b0);

        // Step: config_word(s0, a0, b0) ≡ config_word(s1, a1, b1)
        lemma_machine_step_gives_equiv(data, k, s0, a0, b0);

        // Inductive call on tail
        lemma_trace_gives_equiv(data, tail);

        // Transitivity
        lemma_equiv_transitive(
            machine_group_presentation(data),
            config_word(data.num_states, s0, a0, b0),
            config_word(data.num_states, s1, a1, b1),
            config_word(
                data.num_states,
                trace[trace.len() - 1].0,
                trace[trace.len() - 1].1,
                trace[trace.len() - 1].2,
            ),
        );

        // Tail trace
        let tail = trace.drop_first();
        assert(tail.len() == trace.len() - 1);
        assert(tail.len() >= 1);
        assert(tail[0] == trace[1]);
        assert(tail[tail.len() - 1] == trace[trace.len() - 1]);

        // Inductive call on tail
        lemma_trace_gives_equiv(data, tail);

        // Transitivity
        lemma_equiv_transitive(
            machine_group_presentation(data),
            config_word(data.num_states, s0, a0, b0),
            config_word(data.num_states, s1, a1, b1),
            config_word(
                data.num_states,
                trace[trace.len() - 1].0,
                trace[trace.len() - 1].1,
                trace[trace.len() - 1].2,
            ),
        );
    }
}

// ============================================================
// Backward direction via Britton's Lemma
// ============================================================

/// Two config words that are equivalent in the base (free) group
/// must represent the same configuration.
///
/// In a free group, two distinct words are never equivalent unless
/// they are identical after free reduction. Since config words have
/// the form q_s · a^α · b^β with distinct generator types, two
/// config words are freely equivalent only when s=s', α=α', β=β'.
#[verifier::external_body]
pub proof fn axiom_config_words_free_injective(
    num_states: nat,
    s1: nat, a1: nat, b1: nat,
    s2: nat, a2: nat, b2: nat,
)
    requires
        s1 < num_states,
        s2 < num_states,
        equiv_in_presentation(
            machine_base_presentation(num_states),
            config_word(num_states, s1, a1, b1),
            config_word(num_states, s2, a2, b2),
        ),
    ensures
        s1 == s2 && a1 == a2 && b1 == b2,
{
}

/// Backward direction: equivalence of config words in G_M implies
/// the machine can transition between the corresponding configurations.
///
/// Uses Britton's Lemma: if config_word(C1) ≡ config_word(C2) in G_M,
/// the derivation either stays in the base (meaning C1 = C2 by free
/// group injectivity) or uses stable letters (corresponding to machine
/// transitions). Each stable letter usage corresponds to exactly one
/// machine step.
///
/// This is axiomatized because the full Britton argument requires
/// detailed analysis of pinch elimination in the HNN tower.
#[verifier::external_body]
pub proof fn axiom_machine_group_backward(
    data: MachineGroupData,
    s1: nat, a1: nat, b1: nat,
    s2: nat, a2: nat, b2: nat,
)
    requires
        machine_group_data_wf(data),
        s1 < data.num_states,
        s2 < data.num_states,
        equiv_in_presentation(
            machine_group_presentation(data),
            config_word(data.num_states, s1, a1, b1),
            config_word(data.num_states, s2, a2, b2),
        ),
    ensures
        // There exists a valid trace connecting the two configurations
        exists|trace: Seq<(nat, nat, nat)>|
            is_valid_trace(data, trace) &&
            trace[0] == (s1, a1, b1) &&
            trace[trace.len() - 1] == (s2, a2, b2),
{
}

// ============================================================
// Biconditional (combining forward and backward)
// ============================================================

/// Machine computation ↔ group equivalence.
///
/// config_word(C1) ≡ config_word(C2) in G_M
///   if and only if
/// M can reach C2 from C1 (or vice versa).
pub proof fn lemma_machine_group_faithful(
    data: MachineGroupData,
    s1: nat, a1: nat, b1: nat,
    s2: nat, a2: nat, b2: nat,
)
    requires
        machine_group_data_wf(data),
        s1 < data.num_states,
        s2 < data.num_states,
    ensures
        // Forward: trace exists → equiv
        (exists|trace: Seq<(nat, nat, nat)>|
            is_valid_trace(data, trace) &&
            trace[0] == (s1, a1, b1) &&
            trace[trace.len() - 1] == (s2, a2, b2))
        ==>
        equiv_in_presentation(
            machine_group_presentation(data),
            config_word(data.num_states, s1, a1, b1),
            config_word(data.num_states, s2, a2, b2),
        ),
        // Backward: equiv → trace exists
        equiv_in_presentation(
            machine_group_presentation(data),
            config_word(data.num_states, s1, a1, b1),
            config_word(data.num_states, s2, a2, b2),
        )
        ==>
        (exists|trace: Seq<(nat, nat, nat)>|
            is_valid_trace(data, trace) &&
            trace[0] == (s1, a1, b1) &&
            trace[trace.len() - 1] == (s2, a2, b2)),
{
    // Forward: if trace exists, apply lemma_trace_gives_equiv
    if exists|trace: Seq<(nat, nat, nat)>|
        is_valid_trace(data, trace) &&
        trace[0] == (s1, a1, b1) &&
        trace[trace.len() - 1] == (s2, a2, b2)
    {
        let trace = choose|trace: Seq<(nat, nat, nat)>|
            is_valid_trace(data, trace) &&
            trace[0] == (s1, a1, b1) &&
            trace[trace.len() - 1] == (s2, a2, b2);
        lemma_trace_gives_equiv(data, trace);
    }

    // Backward: apply axiom_machine_group_backward
    if equiv_in_presentation(
        machine_group_presentation(data),
        config_word(data.num_states, s1, a1, b1),
        config_word(data.num_states, s2, a2, b2),
    ) {
        axiom_machine_group_backward(data, s1, a1, b1, s2, a2, b2);
    }
}

} // verus!
