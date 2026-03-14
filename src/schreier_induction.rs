use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::todd_coxeter::*;
use crate::finite::coset_table_complete;
use crate::coset_group::*;
use crate::schreier_proofs::*;

verus! {

/// All non-tree edges up to `bound` are trivial (strong induction).
/// Isolated in its own module so Z3 doesn't see bodies of the ~18 other
/// proof functions in schreier_proofs.rs.
pub proof fn lemma_all_non_tree_trivial(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable, p: Presentation,
    non_tree_edges: Seq<(nat, Symbol)>,
    certificates: Seq<(int, nat, int)>,
    bound: int,
)
    requires
        tree_wf(t, parent, depth),
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        presentation_valid(p),
        t.num_gens == p.num_generators,
        t.num_cosets > 0,
        certificate_wf(t, p, parent, non_tree_edges, certificates),
        0 <= bound <= non_tree_edges.len(),
        // All tree edges trivial
        forall|c: nat, s: Symbol|
            c < t.num_cosets && symbol_valid(s, t.num_gens) &&
            symbol_to_column(s) < 2 * t.num_gens &&
            t.table[c as int][symbol_to_column(s) as int] is Some &&
            #[trigger] is_tree_edge(parent, c, s, t.table[c as int][symbol_to_column(s) as int].unwrap())
            ==> schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), c, s),
    ensures
        forall|m: int| #![trigger non_tree_edges[m]] 0 <= m < bound ==>
            schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), non_tree_edges[m].0, non_tree_edges[m].1),
    decreases bound
{
    if bound <= 0 {
    } else {
        lemma_all_non_tree_trivial(parent, depth, t, p, non_tree_edges, certificates, bound - 1);
        lemma_non_tree_edge_trivial(parent, depth, t, p, non_tree_edges, certificates, bound - 1);
    }
}

} // verus!
