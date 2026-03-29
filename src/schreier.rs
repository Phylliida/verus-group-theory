use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::todd_coxeter::*;
use crate::finite::coset_table_complete;
use crate::coset_group::*;
use crate::schreier_proofs::*;

verus! {

///  All cosets are reachable from coset 0 via some word.
pub open spec fn all_cosets_reachable(t: CosetTable) -> bool {
    forall|c: nat| c < t.num_cosets ==> coset_reachable(t, c)
}

///  Schreier representative for coset c: empty word for coset 0,
///  chosen representative for others (from coset_rep).
pub open spec fn schreier_rep(t: CosetTable, c: nat) -> Word {
    if c == 0 { empty_word() } else { coset_rep(t, c) }
}

///  Construct a Schreier system for a complete coset table from a spanning
///  tree witness. The witness provides a BFS tree of the coset graph with
///  certificates proving each non-tree Schreier generator is trivial via
///  relator traces.
pub proof fn lemma_construct_schreier_system(
    t: CosetTable, p: Presentation,
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    non_tree_edges: Seq<(nat, Symbol)>,
    certificates: Seq<(int, nat, int)>,
)
    requires
        coset_table_wf(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        t.num_cosets > 0,
        tree_wf(t, parent, depth),
        certificate_wf(t, p, parent, non_tree_edges, certificates),
    ensures
        has_schreier_system(t, p),
{
    lemma_schreier_trivial_from_witness(t, p, parent, depth, non_tree_edges, certificates);
}

} //  verus!
