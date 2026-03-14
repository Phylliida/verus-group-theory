use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::todd_coxeter::*;
use crate::finite::coset_table_complete;
use crate::coset_group::*;
use crate::completeness::*;
use crate::schreier_induction::lemma_all_non_tree_trivial;

verus! {

// ========================================================================
// Part 1: Spanning tree specs
// ========================================================================

/// Whether edge (c, s) -> d is a tree edge in the spanning tree.
pub open spec fn is_tree_edge(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    c: nat, s: Symbol, d: nat,
) -> bool {
    parent(d) == Some((c, s))
}

/// Tree-path representative for coset d: path from root 0 to d in the spanning tree.
pub open spec fn tree_rep(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    d: nat,
) -> Word
    decreases depth(d)
{
    if d == 0 { empty_word() }
    else {
        match parent(d) {
            Some((c, s)) => {
                if depth(c) < depth(d) {
                    concat(tree_rep(parent, depth, c), Seq::new(1, |_j: int| s))
                } else {
                    empty_word()
                }
            }
            None => empty_word()
        }
    }
}

/// Well-formedness of the spanning tree structure.
pub open spec fn tree_wf(
    t: CosetTable,
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
) -> bool {
    &&& depth(0nat) == 0nat
    &&& !(parent(0nat) is Some)
    &&& forall|d: nat| #![trigger parent(d)] 0 < d < t.num_cosets ==>
        parent(d) is Some && ({
            let (c, s) = parent(d).unwrap();
            &&& c < t.num_cosets
            &&& symbol_valid(s, t.num_gens)
            &&& symbol_to_column(s) < 2 * t.num_gens
            &&& t.table[c as int][symbol_to_column(s) as int] == Some(d)
            &&& depth(c) < depth(d)
        })
}

/// Whether edge at position j in relator trace is a tree edge or earlier non-tree edge.
pub open spec fn edge_at_pos_handled(
    t: CosetTable,
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    non_tree_edges: Seq<(nat, Symbol)>,
    start: nat, r: Word, j: int, k: int,
) -> bool {
    let c_j = trace_word(t, start, r.subrange(0, j)).unwrap();
    let s_j = r[j];
    let col_j = symbol_to_column(s_j);
    let d_j = t.table[c_j as int][col_j as int].unwrap();
    is_tree_edge(parent, c_j, s_j, d_j)
    || exists|m: int| 0 <= m < k && non_tree_edges[m] == (c_j, s_j)
}

/// Certificate well-formedness for non-tree edges.
#[verifier::opaque]
pub open spec fn certificate_wf(
    t: CosetTable, p: Presentation,
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    non_tree_edges: Seq<(nat, Symbol)>,
    certificates: Seq<(int, nat, int)>,
) -> bool {
    &&& non_tree_edges.len() == certificates.len()
    // Each non-tree edge is valid
    &&& forall|k: int| #![trigger non_tree_edges[k]] 0 <= k < non_tree_edges.len() ==> ({
        let (c, s) = non_tree_edges[k];
        let col = symbol_to_column(s);
        &&& c < t.num_cosets
        &&& symbol_valid(s, t.num_gens)
        &&& col < 2 * t.num_gens
        &&& t.table[c as int][col as int] is Some
        &&& !is_tree_edge(parent, c, s, t.table[c as int][col as int].unwrap())
    })
    // Each certificate: relator trace contains the non-tree edge, all others are handled
    &&& forall|k: int| #![trigger certificates[k]] 0 <= k < certificates.len() ==> ({
        let (c_k, s_k) = non_tree_edges[k];
        let (r_idx, start, pos) = certificates[k];
        let r = p.relators[r_idx];
        &&& 0 <= r_idx < p.relators.len()
        &&& start < t.num_cosets
        &&& 0 <= pos < r.len()
        &&& trace_word(t, start, r.subrange(0, pos)) == Some(c_k)
        &&& r[pos] == s_k
        &&& forall|j: int| #![trigger r[j]] 0 <= j < r.len() && j != pos ==>
            edge_at_pos_handled(t, parent, non_tree_edges, start, r, j, k)
    })
    // Coverage: every non-tree edge appears in the list
    &&& forall|c: nat, s: Symbol|
        c < t.num_cosets && symbol_valid(s, t.num_gens) &&
        symbol_to_column(s) < 2 * t.num_gens &&
        t.table[c as int][symbol_to_column(s) as int] is Some &&
        !is_tree_edge(parent, c, s, t.table[c as int][symbol_to_column(s) as int].unwrap())
        ==> exists|k: int| 0 <= k < non_tree_edges.len() && #[trigger] non_tree_edges[k] == (c, s)
}

/// Schreier product: product of Schreier generators along trace of w from c.
pub open spec fn schreier_product(
    t: CosetTable,
    reps: spec_fn(nat) -> Word,
    c: nat,
    w: Word,
) -> Word
    decreases w.len()
{
    if w.len() == 0 { empty_word() }
    else {
        let s = w.first();
        let col = symbol_to_column(s);
        let d = t.table[c as int][col as int].unwrap();
        let s_word: Word = Seq::new(1, |_j: int| s);
        let gen = concat(concat(reps(c), s_word), inverse_word(reps(d)));
        concat(gen, schreier_product(t, reps, d, w.drop_first()))
    }
}

/// All Schreier generators along a trace are trivial (recursive, matching sp structure).
pub open spec fn all_gens_trivial_in_trace(
    t: CosetTable, p: Presentation,
    reps: spec_fn(nat) -> Word,
    c: nat, w: Word,
) -> bool
    decreases w.len()
{
    if w.len() == 0 { true }
    else {
        let s = w.first();
        let col = symbol_to_column(s);
        let d = t.table[c as int][col as int].unwrap();
        schreier_gen_equiv(t, p, reps, c, s)
        && all_gens_trivial_in_trace(t, p, reps, d, w.drop_first())
    }
}

// ========================================================================
// Part 2: Tree rep is a valid coset rep system
// ========================================================================

/// Tree rep: traces correctly, word_valid, columns valid.
pub proof fn lemma_tree_rep_properties(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable,
    d: nat,
)
    requires
        tree_wf(t, parent, depth),
        coset_table_wf(t),
        coset_table_complete(t),
        d < t.num_cosets,
    ensures
        trace_word(t, 0 as nat, tree_rep(parent, depth, d)) == Some(d),
        word_valid(tree_rep(parent, depth, d), t.num_gens),
        forall|k: int| 0 <= k < tree_rep(parent, depth, d).len()
            ==> #[trigger] symbol_to_column(tree_rep(parent, depth, d)[k]) < 2 * t.num_gens,
    decreases depth(d)
{
    let rep = tree_rep(parent, depth, d);
    if d == 0 {
        // tree_rep(parent, depth, 0) = empty_word() by definition
        assert(rep =~= empty_word());
        lemma_trace_empty(t, 0);
        // trace(0, empty_word()) == Some(0), which is Some(d) since d == 0
        assert(trace_word(t, 0 as nat, rep) == Some(d));
    } else {
        let (c, s) = parent(d).unwrap();
        lemma_tree_rep_properties(parent, depth, t, c);

        let rep_c = tree_rep(parent, depth, c);
        let s_word: Word = Seq::new(1, |_j: int| s);
        assert(rep =~= concat(rep_c, s_word));

        // word_valid and columns for [s]
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(s_word[k], t.num_gens) by { assert(s_word[k] == s); }
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_to_column(s_word[k]) < 2 * t.num_gens by { assert(s_word[k] == s); }

        crate::word::lemma_concat_word_valid(rep_c, s_word, t.num_gens);

        // columns for concat
        assert forall|k: int| 0 <= k < rep.len()
            implies symbol_to_column(rep[k]) < 2 * t.num_gens by {
            if k < rep_c.len() as int {
                assert(rep[k] == rep_c[k]);
            } else {
                assert(rep[k] == s_word[(k - rep_c.len() as int)]);
            }
        }

        // trace: trace(0, concat(rep_c, [s])) = trace(trace(0, rep_c), [s]) = trace(c, [s]) = Some(d)
        lemma_trace_complete(t, c, s_word);
        lemma_trace_single(t, c, s);
        assert(s_word =~= seq![s]);
        assert(trace_word(t, c, s_word) == Some(d));
        lemma_trace_word_concat(t, 0 as nat, rep_c, s_word);
        assert(trace_word(t, 0 as nat, rep) == Some(d));
    }
}

/// Tree reps form a valid coset rep system.
pub proof fn lemma_tree_rep_is_rep_system(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable,
)
    requires
        tree_wf(t, parent, depth),
        coset_table_wf(t),
        coset_table_complete(t),
        t.num_cosets > 0,
    ensures
        is_coset_rep_system(t, |d: nat| tree_rep(parent, depth, d)),
{
    let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
    assert(reps(0nat) =~= empty_word());
    assert forall|c: nat| c < t.num_cosets implies (
        #[trigger] trace_word(t, 0 as nat, reps(c)) == Some(c)
        && word_valid(reps(c), t.num_gens)
        && (forall|k: int| 0 <= k < reps(c).len()
            ==> #[trigger] symbol_to_column(reps(c)[k]) < 2 * t.num_gens)
    ) by {
        lemma_tree_rep_properties(parent, depth, t, c);
    }
}

// ========================================================================
// Part 3: Tree edge triviality
// ========================================================================

/// Tree edges have trivial Schreier generators: gen = w . w^{-1} = e.
pub proof fn lemma_tree_edge_trivial(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable, p: Presentation,
    c: nat, s: Symbol,
)
    requires
        tree_wf(t, parent, depth),
        coset_table_wf(t),
        coset_table_complete(t),
        c < t.num_cosets,
        symbol_valid(s, t.num_gens),
        symbol_to_column(s) < 2 * t.num_gens,
        t.table[c as int][symbol_to_column(s) as int] is Some,
        is_tree_edge(parent, c, s, t.table[c as int][symbol_to_column(s) as int].unwrap()),
    ensures
        schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), c, s),
{
    let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
    let col = symbol_to_column(s);
    let d = t.table[c as int][col as int].unwrap();
    let s_word: Word = Seq::new(1, |_j: int| s);

    // parent(d) = Some((c, s)), d > 0, so tree_rep(d) = concat(tree_rep(c), [s])
    let w = concat(reps(c), s_word);
    assert(reps(d) =~= w);

    // gen = concat(w, inv(w)) which is w . w^{-1} = e
    lemma_word_inverse_right(p, w);
}

// ========================================================================
// Part 4: Telescoping
// ========================================================================

/// Schreier product equals conjugated trace:
/// sp(c, w) ≡ reps(c) . w . reps(trace(c,w))^{-1}
pub proof fn lemma_telescoping(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable, p: Presentation,
    c: nat, w: Word,
)
    requires
        tree_wf(t, parent, depth),
        coset_table_wf(t),
        coset_table_complete(t),
        presentation_valid(p),
        t.num_gens == p.num_generators,
        t.num_cosets > 0,
        c < t.num_cosets,
        word_valid(w, t.num_gens),
    ensures
        ({
            let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
            let e = trace_word(t, c, w).unwrap();
            equiv_in_presentation(p,
                schreier_product(t, reps, c, w),
                concat(reps(c), concat(w, inverse_word(reps(e)))))
        }),
    decreases w.len()
{
    let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
    lemma_valid_word_columns(w, t.num_gens);
    lemma_trace_complete(t, c, w);
    let e = trace_word(t, c, w).unwrap();

    if w.len() == 0 {
        // sp(c, ε) = ε, target = concat(reps(c), concat(ε, inv(reps(c)))) =~= concat(reps(c), inv(reps(c)))
        assert(concat(empty_word(), inverse_word(reps(c))) =~= inverse_word(reps(c)));
        // word_inverse_right: concat(reps(c), inv(reps(c))) ≡ ε
        lemma_word_inverse_right(p, reps(c));
        // Need symmetric: ε ≡ concat(reps(c), inv(reps(c)))
        lemma_tree_rep_properties(parent, depth, t, c);
        lemma_inverse_word_valid(reps(c), t.num_gens);
        crate::word::lemma_concat_word_valid(reps(c), inverse_word(reps(c)), p.num_generators);
        lemma_equiv_symmetric(p,
            concat(reps(c), inverse_word(reps(c))),
            empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let s_word: Word = Seq::new(1, |_j: int| s);
        let col = symbol_to_column(s);
        assert(symbol_valid(s, t.num_gens)) by { assert(s == w[0]); }
        let d = t.table[c as int][col as int].unwrap();

        // word_valid for rest
        assert(word_valid(rest, t.num_gens)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], t.num_gens) by { assert(rest[k] == w[k + 1]); }
        }

        // trace: need trace(c, [s]) is Some BEFORE calling trace_word_concat
        lemma_trace_complete(t, c, s_word);
        // Now trace_word_concat: trace(c, w) = trace(d, rest) since w = [s] ++ rest
        assert(w =~= concat(s_word, rest));
        lemma_trace_word_concat(t, c, s_word, rest);

        // IH: equiv(sp(d, rest), concat(reps(d), concat(rest, inv(reps(e)))))
        lemma_telescoping(parent, depth, t, p, d, rest);

        let rep_c = reps(c);
        let rep_d = reps(d);
        let rep_e = reps(e);
        let inv_rep_d = inverse_word(rep_d);
        let inv_rep_e = inverse_word(rep_e);
        let gen = concat(concat(rep_c, s_word), inv_rep_d);
        let B = concat(rest, inv_rep_e);
        let A = concat(rep_c, s_word);
        let sp_rest = schreier_product(t, reps, d, rest);

        // Step 1: equiv(concat(gen, sp_rest), concat(gen, concat(rep_d, B))) from IH
        lemma_equiv_concat_right(p, gen, sp_rest, concat(rep_d, B));

        // Step 2: Show concat(gen, concat(rep_d, B)) ≡ concat(A, B)
        // 2a: inv(rep_d) . rep_d ≡ ε
        lemma_word_inverse_left(p, rep_d);
        // 2b: concat(concat(inv_rep_d, rep_d), B) ≡ concat(ε, B)
        lemma_equiv_concat_left(p, concat(inv_rep_d, rep_d), empty_word(), B);
        // 2c: concat(ε, B) ≡ B
        lemma_concat_identity_left(p, B);
        // 2d: transitive: concat(concat(inv_rep_d, rep_d), B) ≡ B
        lemma_equiv_transitive(p,
            concat(concat(inv_rep_d, rep_d), B),
            concat(empty_word(), B), B);
        // 2e: assoc
        lemma_concat_assoc(inv_rep_d, rep_d, B);
        // 2f: equiv_concat_right(A, ...)
        lemma_equiv_concat_right(p, A, concat(inv_rep_d, concat(rep_d, B)), B);
        // 2g: assoc for gen
        lemma_concat_assoc(A, inv_rep_d, concat(rep_d, B));

        // Step 3: concat(A, B) =~= target
        lemma_concat_assoc(rep_c, s_word, B);
        lemma_concat_assoc(s_word, rest, inv_rep_e);

        // Step 4: chain
        lemma_equiv_transitive(p,
            concat(gen, sp_rest),
            concat(gen, concat(rep_d, B)),
            concat(A, B));
    }
}

// ========================================================================
// Part 5: Trivial product + extraction
// ========================================================================

/// Helper: trigger is_coset_rep_system for a specific coset.
proof fn lemma_rep_system_trigger(
    t: CosetTable,
    reps: spec_fn(nat) -> Word,
    c: nat,
)
    requires
        coset_table_wf(t),
        is_coset_rep_system(t, reps),
        c < t.num_cosets,
    ensures
        word_valid(reps(c), t.num_gens),
        trace_word(t, 0 as nat, reps(c)) == Some(c),
        forall|k: int| 0 <= k < reps(c).len()
            ==> #[trigger] symbol_to_column(reps(c)[k]) < 2 * t.num_gens,
{
    assert(trace_word(t, 0 as nat, reps(c)) == Some(c));
}

/// Schreier product is word_valid.
proof fn lemma_schreier_product_word_valid(
    t: CosetTable,
    reps: spec_fn(nat) -> Word,
    c: nat, w: Word, n: nat,
)
    requires
        coset_table_wf(t),
        coset_table_complete(t),
        c < t.num_cosets,
        t.num_gens == n,
        is_coset_rep_system(t, reps),
        word_valid(w, n),
    ensures
        word_valid(schreier_product(t, reps, c, w), n),
    decreases w.len()
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let s_word: Word = Seq::new(1, |_j: int| s);
        let col = symbol_to_column(s);
        assert(symbol_valid(s, n)) by { assert(s == w[0]); }
        lemma_valid_word_columns(w, n);
        let d = t.table[c as int][col as int].unwrap();
        lemma_trace_complete(t, c, s_word);

        // Trigger rep system for c and d
        lemma_rep_system_trigger(t, reps, c);
        lemma_rep_system_trigger(t, reps, d);

        // word_valid(gen, n)
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(s_word[k], n) by { assert(s_word[k] == s); }
        crate::word::lemma_concat_word_valid(reps(c), s_word, n);
        lemma_inverse_word_valid(reps(d), n);
        let gen = concat(concat(reps(c), s_word), inverse_word(reps(d)));
        crate::word::lemma_concat_word_valid(concat(reps(c), s_word), inverse_word(reps(d)), n);

        // IH
        assert(word_valid(rest, n)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], n) by { assert(rest[k] == w[k + 1]); }
        }
        lemma_schreier_product_word_valid(t, reps, d, rest, n);

        crate::word::lemma_concat_word_valid(gen, schreier_product(t, reps, d, rest), n);
    }
}

/// If all Schreier gens along a trace are trivial, the product is trivial.
pub proof fn lemma_trivial_product(
    t: CosetTable, p: Presentation,
    reps: spec_fn(nat) -> Word,
    c: nat, w: Word,
)
    requires
        coset_table_wf(t),
        coset_table_complete(t),
        presentation_valid(p),
        t.num_gens == p.num_generators,
        t.num_cosets > 0,
        c < t.num_cosets,
        word_valid(w, t.num_gens),
        is_coset_rep_system(t, reps),
        all_gens_trivial_in_trace(t, p, reps, c, w),
    ensures
        equiv_in_presentation(p, schreier_product(t, reps, c, w), empty_word()),
    decreases w.len()
{
    if w.len() == 0 {
        lemma_equiv_refl(p, empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let s_word: Word = Seq::new(1, |_j: int| s);
        let col = symbol_to_column(s);
        assert(symbol_valid(s, t.num_gens)) by { assert(s == w[0]); }
        lemma_valid_word_columns(w, t.num_gens);
        let d = t.table[c as int][col as int].unwrap();
        lemma_trace_complete(t, c, s_word);

        let gen = concat(concat(reps(c), s_word), inverse_word(reps(d)));

        // word_valid for rest
        assert(word_valid(rest, t.num_gens)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], t.num_gens) by { assert(rest[k] == w[k + 1]); }
        }

        // gen_0 is trivial (from all_gens_trivial_in_trace unfolding)
        // all_gens_trivial gives: schreier_gen_equiv(c, s) && all_gens_trivial(d, rest)
        // sp(d, rest) is trivial by IH
        lemma_trivial_product(t, p, reps, d, rest);

        // concat(gen, sp(d, rest)) ≡ concat(ε, ε) = ε
        lemma_equiv_concat(p, gen, empty_word(),
            schreier_product(t, reps, d, rest), empty_word());
        assert(concat(empty_word(), empty_word()) =~= empty_word());
    }
}

/// Extract a single non-trivial gen from a product where all other gens are trivial.
pub proof fn lemma_extract_nontrivial_gen(
    t: CosetTable, p: Presentation,
    reps: spec_fn(nat) -> Word,
    c: nat, w: Word, pos: int,
)
    requires
        coset_table_wf(t),
        coset_table_complete(t),
        presentation_valid(p),
        t.num_gens == p.num_generators,
        t.num_cosets > 0,
        c < t.num_cosets,
        word_valid(w, t.num_gens),
        is_coset_rep_system(t, reps),
        0 <= pos < w.len(),
        // prefix gens are trivial
        all_gens_trivial_in_trace(t, p, reps, c, w.subrange(0, pos)),
        // suffix gens (after pos) are trivial
        ({
            let c_after = trace_word(t, c, w.subrange(0, pos + 1)).unwrap();
            all_gens_trivial_in_trace(t, p, reps, c_after, w.subrange(pos + 1, w.len() as int))
        }),
    ensures
        ({
            let c_pos = trace_word(t, c, w.subrange(0, pos)).unwrap();
            let s_pos = w[pos];
            let col_pos = symbol_to_column(s_pos);
            let d_pos = t.table[c_pos as int][col_pos as int].unwrap();
            let s_word: Word = Seq::new(1, |_j: int| s_pos);
            let gen_pos = concat(concat(reps(c_pos), s_word), inverse_word(reps(d_pos)));
            equiv_in_presentation(p, schreier_product(t, reps, c, w), gen_pos)
        }),
    decreases pos
{
    lemma_valid_word_columns(w, t.num_gens);
    // Trace of prefix is defined
    assert(word_valid(w.subrange(0, pos), t.num_gens)) by {
        assert forall|k: int| 0 <= k < w.subrange(0, pos).len()
            implies symbol_valid(w.subrange(0, pos)[k], t.num_gens) by {
            assert(w.subrange(0, pos)[k] == w[k]);
        }
    }
    lemma_valid_word_columns(w.subrange(0, pos), t.num_gens);
    lemma_trace_complete(t, c, w.subrange(0, pos));
    let c_pos = trace_word(t, c, w.subrange(0, pos)).unwrap();

    // Trace of prefix+1 is defined
    assert(word_valid(w.subrange(0, pos + 1), t.num_gens)) by {
        assert forall|k: int| 0 <= k < w.subrange(0, pos + 1).len()
            implies #[trigger] symbol_valid(w.subrange(0, pos + 1)[k], t.num_gens) by {
            assert(w.subrange(0, pos + 1)[k] == w[k]);
        }
    }
    lemma_valid_word_columns(w.subrange(0, pos + 1), t.num_gens);
    lemma_trace_complete(t, c, w.subrange(0, pos + 1));
    let c_after = trace_word(t, c, w.subrange(0, pos + 1)).unwrap();

    if pos == 0 {
        // sp(c, w) = concat(gen_0, sp(d, rest))
        let s = w.first();
        let rest = w.drop_first();
        let s_word: Word = Seq::new(1, |_j: int| s);
        let col = symbol_to_column(s);
        let d = t.table[c as int][col as int].unwrap();
        let gen = concat(concat(reps(c), s_word), inverse_word(reps(d)));
        let sp_rest = schreier_product(t, reps, d, rest);

        // c_pos = c (trace of empty prefix)
        assert(w.subrange(0, 0int) =~= Seq::<Symbol>::empty());
        lemma_trace_empty(t, c);
        assert(c_pos == c);

        // c_after = d (trace of [s])
        assert(s_word =~= seq![s]);
        lemma_trace_single(t, c, s);
        assert(trace_word(t, c, s_word) == Some(d));
        assert(w.subrange(0, 1) =~= s_word);
        assert(c_after == d);

        // suffix = w[1..] = rest, starting from d
        assert(w.subrange(1, w.len() as int) =~= rest);
        assert(w.subrange(pos + 1, w.len() as int) =~= rest);

        // word_valid for rest
        assert(word_valid(rest, t.num_gens)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], t.num_gens) by { assert(rest[k] == w[k + 1]); }
        }

        // sp(d, rest) ≡ ε by trivial_product (suffix gens all trivial)
        lemma_trivial_product(t, p, reps, d, rest);

        // concat(gen, sp_rest) ≡ concat(gen, ε) ≡ gen
        lemma_equiv_concat_right(p, gen, sp_rest, empty_word());
        assert(concat(gen, empty_word()) =~= gen);
    } else {
        // pos > 0: gen_0 is trivial, peel it off
        let s = w.first();
        let rest = w.drop_first();
        let s_word: Word = Seq::new(1, |_j: int| s);
        let col = symbol_to_column(s);
        assert forall|k3: int| 0 <= k3 < s_word.len()
            implies symbol_to_column(s_word[k3]) < 2 * t.num_gens by { assert(s_word[k3] == s); }
        lemma_trace_complete(t, c, s_word);
        lemma_trace_single(t, c, s);
        assert(s_word =~= seq![s]);
        let d = t.table[c as int][col as int].unwrap();
        assert(trace_word(t, c, s_word) == Some(d));
        let gen = concat(concat(reps(c), s_word), inverse_word(reps(d)));
        let sp_rest = schreier_product(t, reps, d, rest);

        assert(word_valid(rest, t.num_gens)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], t.num_gens) by { assert(rest[k] == w[k + 1]); }
        }

        // gen_0 is trivial: from all_gens_trivial(c, w[0..pos]) with pos > 0
        assert(w.subrange(0, pos).len() > 0) by { assert(pos > 0); }
        assert(w.subrange(0, pos).first() == w[0]) by {
            assert(w.subrange(0, pos)[0] == w[0]);
        }
        assert(w.subrange(0, pos).first() == s);

        // Peel: sp(c, w) = concat(gen, sp_rest), gen ≡ ε
        lemma_equiv_concat_left(p, gen, empty_word(), sp_rest);
        assert(concat(empty_word(), sp_rest) =~= sp_rest);

        // IH setup: prefix gens for rest[0..pos-1] are trivial
        assert(rest.subrange(0, pos - 1) =~= w.subrange(1, pos));
        assert(w.subrange(0, pos).drop_first() =~= w.subrange(1, pos));

        // Suffix trace: rest[0..pos] = w[1..pos+1]
        assert(rest.subrange(0, pos) =~= w.subrange(1, pos + 1));
        assert(w.subrange(0, pos + 1) =~= concat(s_word, w.subrange(1, pos + 1)));
        lemma_trace_word_concat(t, c, s_word, w.subrange(1, pos + 1));
        assert(rest.subrange(0, (pos - 1) + 1) =~= w.subrange(1, pos + 1));

        // Suffix gens: rest[pos..] = w[pos+1..]
        assert(rest.subrange(pos, rest.len() as int) =~= w.subrange(pos + 1, w.len() as int));

        lemma_extract_nontrivial_gen(t, p, reps, d, rest, pos - 1);

        // gen_at_pos in rest = gen_at_pos in w
        assert(w.subrange(0, pos) =~= concat(s_word, w.subrange(1, pos)));
        lemma_trace_word_concat(t, c, s_word, w.subrange(1, pos));
        assert(rest.subrange(0, pos - 1) =~= w.subrange(1, pos));
        assert(rest[pos - 1] == w[pos]);

        // Transitive: equiv(sp(c, w), sp(d, rest)) + equiv(sp(d, rest), gen_pos)
        let s_pos = w[pos];
        let col_pos = symbol_to_column(s_pos);
        let d_pos = t.table[c_pos as int][col_pos as int].unwrap();
        let s_pos_word: Word = Seq::new(1, |_j: int| s_pos);
        let gen_pos = concat(concat(reps(c_pos), s_pos_word), inverse_word(reps(d_pos)));

        lemma_equiv_transitive(p,
            schreier_product(t, reps, c, w),
            sp_rest,
            gen_pos);
    }
}

// ========================================================================
// Part 6: Non-tree edge induction
// ========================================================================

/// Prove all_gens_trivial_in_trace for a subword r[from..to] of a relator,
/// using edge_at_pos_handled from certificate_wf directly.
proof fn lemma_relator_subword_trivial(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable, p: Presentation,
    non_tree_edges: Seq<(nat, Symbol)>,
    start: nat, r: Word, from: int, to: int, k: int,
)
    requires
        tree_wf(t, parent, depth),
        coset_table_wf(t),
        coset_table_complete(t),
        presentation_valid(p),
        t.num_gens == p.num_generators,
        t.num_cosets > 0,
        start < t.num_cosets,
        word_valid(r, t.num_gens),
        is_coset_rep_system(t, |d: nat| tree_rep(parent, depth, d)),
        0 <= from <= to <= r.len(),
        k <= non_tree_edges.len() as int,
        // Each position in [from, to) has its edge handled
        forall|j: int| from <= j < to ==> #[trigger]
            edge_at_pos_handled(t, parent, non_tree_edges, start, r, j, k),
        // All tree edges trivial
        forall|c2: nat, s2: Symbol|
            c2 < t.num_cosets && symbol_valid(s2, t.num_gens) &&
            symbol_to_column(s2) < 2 * t.num_gens &&
            t.table[c2 as int][symbol_to_column(s2) as int] is Some &&
            #[trigger] is_tree_edge(parent, c2, s2, t.table[c2 as int][symbol_to_column(s2) as int].unwrap())
            ==> schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), c2, s2),
        // All non-tree < k trivial
        forall|m: int| #![trigger non_tree_edges[m]] 0 <= m < k && m < non_tree_edges.len() ==>
            schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), non_tree_edges[m].0, non_tree_edges[m].1),
    ensures
        ({
            let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
            let subword = r.subrange(from, to);
            let c_from = trace_word(t, start, r.subrange(0, from)).unwrap();
            all_gens_trivial_in_trace(t, p, reps, c_from, subword)
        }),
    decreases to - from
{
    let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
    lemma_valid_word_columns(r, t.num_gens);

    // Establish trace(start, r[0..from]) is defined
    assert(word_valid(r.subrange(0, from), t.num_gens)) by {
        assert forall|j2: int| 0 <= j2 < r.subrange(0, from).len()
            implies symbol_valid(r.subrange(0, from)[j2], t.num_gens) by {
            assert(r.subrange(0, from)[j2] == r[j2]);
        }
    }
    lemma_valid_word_columns(r.subrange(0, from), t.num_gens);
    lemma_trace_complete(t, start, r.subrange(0, from));
    let c_from = trace_word(t, start, r.subrange(0, from)).unwrap();

    let subword = r.subrange(from, to);

    if from >= to {
        // Empty subword: all_gens_trivial unfolds to true
        assert(subword =~= Seq::<Symbol>::empty());
    } else {
        // Head symbol
        let s = r[from];
        assert(subword.first() == s) by { assert(subword[0] == r[from]); }
        assert(subword.drop_first() =~= r.subrange(from + 1, to));

        let col = symbol_to_column(s);
        assert(symbol_valid(s, t.num_gens)) by { assert(s == r[from]); }
        assert(col < 2 * t.num_gens);

        let s_word: Word = Seq::new(1, |_j: int| s);
        assert forall|k2: int| 0 <= k2 < s_word.len()
            implies symbol_to_column(s_word[k2]) < 2 * t.num_gens by { assert(s_word[k2] == s); }
        lemma_trace_complete(t, c_from, s_word);
        let d = t.table[c_from as int][col as int].unwrap();
        assert(d < t.num_cosets);

        // edge_at_pos_handled(t, parent, non_tree_edges, start, r, from, k) holds
        // This unfolds: c_j = trace(start, r[0..from]) = c_from, s_j = r[from] = s
        assert(edge_at_pos_handled(t, parent, non_tree_edges, start, r, from, k));

        // Get schreier_gen_equiv(t, p, reps, c_from, s)
        if is_tree_edge(parent, c_from, s, d) {
            // Tree edge: use tree_trivial precondition
        } else {
            // Non-tree: exists m < k with non_tree_edges[m] == (c_from, s)
            let m = choose|m: int| 0 <= m < k && non_tree_edges[m] == (c_from, s);
            assert(non_tree_edges[m].0 == c_from);
            assert(non_tree_edges[m].1 == s);
        }
        assert(schreier_gen_equiv(t, p, reps, c_from, s));

        // trace(start, r[0..from+1]) = trace(c_from, [s]) = d
        assert(r.subrange(0, from + 1) =~= concat(r.subrange(0, from), s_word));
        assert(s_word =~= seq![s]);
        lemma_trace_single(t, c_from, s);
        assert(trace_word(t, c_from, s_word) == Some(d));
        lemma_trace_word_concat(t, start, r.subrange(0, from), s_word);

        // IH: all_gens_trivial_in_trace(reps, d, r[from+1..to])
        lemma_relator_subword_trivial(parent, depth, t, p, non_tree_edges, start, r, from + 1, to, k);
    }
}

/// Single non-tree edge at index k is trivial, given all prior are trivial.
pub proof fn lemma_non_tree_edge_trivial(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable, p: Presentation,
    non_tree_edges: Seq<(nat, Symbol)>,
    certificates: Seq<(int, nat, int)>,
    k: int,
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
        0 <= k < non_tree_edges.len() as int,
        // All tree edges trivial
        forall|c: nat, s: Symbol|
            c < t.num_cosets && symbol_valid(s, t.num_gens) &&
            symbol_to_column(s) < 2 * t.num_gens &&
            t.table[c as int][symbol_to_column(s) as int] is Some &&
            #[trigger] is_tree_edge(parent, c, s, t.table[c as int][symbol_to_column(s) as int].unwrap())
            ==> schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), c, s),
        // All non-tree edges with index < k trivial
        forall|m: int| #![trigger non_tree_edges[m]] 0 <= m < k ==>
            schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), non_tree_edges[m].0, non_tree_edges[m].1),
    ensures
        schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), non_tree_edges[k].0, non_tree_edges[k].1),
{
    reveal(certificate_wf);
    let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
    let ck = non_tree_edges[k].0;
    let sk = non_tree_edges[k].1;
    let (r_idx, start, pos) = certificates[k];
    let r = p.relators[r_idx];

    lemma_tree_rep_is_rep_system(parent, depth, t);

    // r is word_valid
    assert(word_valid(r, t.num_gens)) by {
        assert(word_valid(r, p.num_generators));
    }
    lemma_valid_word_columns(r, t.num_gens);

    // Step 1: sp(start, r) ≡ ε
    lemma_non_tree_step1_sp_trivial(parent, depth, t, p, non_tree_edges, certificates, k);

    // Step 2: build prefix/suffix triviality and extract gen
    lemma_non_tree_step2_extract_gen(parent, depth, t, p, non_tree_edges, certificates, k);

    // Step 3: sp ≡ ε and sp ≡ gen_pos => gen_pos ≡ ε
    let sp = schreier_product(t, reps, start, r);
    let c_pos = trace_word(t, start, r.subrange(0, pos)).unwrap();
    let s_pos = r[pos];
    let s_pos_word: Word = Seq::new(1, |_j: int| s_pos);
    let col_pos = symbol_to_column(s_pos);
    let d_pos = t.table[c_pos as int][col_pos as int].unwrap();
    let gen_pos = concat(concat(reps(c_pos), s_pos_word), inverse_word(reps(d_pos)));

    // equiv(sp, ε) + equiv(sp, gen_pos) => equiv(gen_pos, ε)
    lemma_schreier_product_word_valid(t, reps, start, r, t.num_gens);
    lemma_equiv_symmetric(p, sp, empty_word());
    lemma_equiv_transitive(p, empty_word(), sp, gen_pos);
    lemma_equiv_symmetric(p, empty_word(), gen_pos);

    // gen_pos corresponds to (ck, sk) since certificate says trace(start, r[0..pos]) = ck, r[pos] = sk
    assert(c_pos == ck);
    assert(s_pos == sk);
}

/// Step 1 helper: sp(start, r) ≡ ε via telescoping + conjugate relator.
proof fn lemma_non_tree_step1_sp_trivial(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable, p: Presentation,
    non_tree_edges: Seq<(nat, Symbol)>,
    certificates: Seq<(int, nat, int)>,
    k: int,
)
    requires
        tree_wf(t, parent, depth),
        coset_table_wf(t),
        coset_table_complete(t),
        relator_closed(t, p),
        presentation_valid(p),
        t.num_gens == p.num_generators,
        t.num_cosets > 0,
        certificate_wf(t, p, parent, non_tree_edges, certificates),
        0 <= k < non_tree_edges.len() as int,
    ensures
        ({
            let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
            let (r_idx, start, pos) = certificates[k];
            let r = p.relators[r_idx];
            equiv_in_presentation(p, schreier_product(t, reps, start, r), empty_word())
        }),
{
    reveal(certificate_wf);
    let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
    let (r_idx, start, pos) = certificates[k];
    let r = p.relators[r_idx];

    assert(word_valid(r, t.num_gens)) by {
        assert(word_valid(r, p.num_generators));
    }

    // Telescoping: sp(start, r) ≡ concat(reps(start), concat(r, inv(reps(start))))
    lemma_telescoping(parent, depth, t, p, start, r);

    // trace(start, r) = Some(start) by relator_closed
    assert(trace_word(t, start, r) == Some(start));

    let big_expr = concat(reps(start), concat(r, inverse_word(reps(start))));

    // conjugate_relator: concat(concat(reps(start), r), inv(reps(start))) ≡ ε
    lemma_conjugate_relator_is_identity(p, reps(start), r_idx);
    // assoc: these are =~=
    lemma_concat_assoc(reps(start), r, inverse_word(reps(start)));

    // Transitive: sp ≡ big_expr ≡ ε
    lemma_equiv_transitive(p,
        schreier_product(t, reps, start, r),
        big_expr,
        empty_word());
}

/// Step 2a: build prefix triviality for certificate k's relator.
proof fn lemma_step2_prefix_trivial(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable, p: Presentation,
    non_tree_edges: Seq<(nat, Symbol)>,
    certificates: Seq<(int, nat, int)>,
    k: int,
)
    requires
        tree_wf(t, parent, depth),
        coset_table_wf(t),
        coset_table_complete(t),
        presentation_valid(p),
        t.num_gens == p.num_generators,
        t.num_cosets > 0,
        certificate_wf(t, p, parent, non_tree_edges, certificates),
        0 <= k < non_tree_edges.len() as int,
        is_coset_rep_system(t, |d: nat| tree_rep(parent, depth, d)),
        forall|c: nat, s: Symbol|
            c < t.num_cosets && symbol_valid(s, t.num_gens) &&
            symbol_to_column(s) < 2 * t.num_gens &&
            t.table[c as int][symbol_to_column(s) as int] is Some &&
            #[trigger] is_tree_edge(parent, c, s, t.table[c as int][symbol_to_column(s) as int].unwrap())
            ==> schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), c, s),
        forall|m: int| #![trigger non_tree_edges[m]] 0 <= m < k && m < non_tree_edges.len() ==>
            schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), non_tree_edges[m].0, non_tree_edges[m].1),
    ensures
        ({
            let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
            let (r_idx, start, pos) = certificates[k];
            let r = p.relators[r_idx];
            let prefix = r.subrange(0, pos);
            all_gens_trivial_in_trace(t, p, reps, start, prefix)
        }),
{
    reveal(certificate_wf);
    let (r_idx, start, pos) = certificates[k];
    let r = p.relators[r_idx];

    assert(word_valid(r, t.num_gens)) by { assert(word_valid(r, p.num_generators)); }

    // From certificate_wf: positions j != pos have edge_at_pos_handled
    // For prefix positions [0, pos), all j != pos, so all handled
    assert forall|j: int| 0 <= j < pos implies #[trigger]
        edge_at_pos_handled(t, parent, non_tree_edges, start, r, j, k) by {
        assert(r[j] == r[j]); // trigger certificate_wf forall
    }

    // r.subrange(0, 0) =~= empty, trace(start, empty) = Some(start)
    assert(r.subrange(0, 0int) =~= Seq::<Symbol>::empty());
    lemma_trace_empty(t, start);

    lemma_relator_subword_trivial(parent, depth, t, p, non_tree_edges, start, r, 0, pos, k);

    // Connect: c_from with from=0 is trace(start, r[0..0]) = start
    assert(r.subrange(0, pos) =~= r.subrange(0, pos));
}

/// Step 2b: build suffix triviality for certificate k's relator.
proof fn lemma_step2_suffix_trivial(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable, p: Presentation,
    non_tree_edges: Seq<(nat, Symbol)>,
    certificates: Seq<(int, nat, int)>,
    k: int,
)
    requires
        tree_wf(t, parent, depth),
        coset_table_wf(t),
        coset_table_complete(t),
        presentation_valid(p),
        t.num_gens == p.num_generators,
        t.num_cosets > 0,
        certificate_wf(t, p, parent, non_tree_edges, certificates),
        0 <= k < non_tree_edges.len() as int,
        is_coset_rep_system(t, |d: nat| tree_rep(parent, depth, d)),
        forall|c: nat, s: Symbol|
            c < t.num_cosets && symbol_valid(s, t.num_gens) &&
            symbol_to_column(s) < 2 * t.num_gens &&
            t.table[c as int][symbol_to_column(s) as int] is Some &&
            #[trigger] is_tree_edge(parent, c, s, t.table[c as int][symbol_to_column(s) as int].unwrap())
            ==> schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), c, s),
        forall|m: int| #![trigger non_tree_edges[m]] 0 <= m < k && m < non_tree_edges.len() ==>
            schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), non_tree_edges[m].0, non_tree_edges[m].1),
    ensures
        ({
            let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
            let (r_idx, start, pos) = certificates[k];
            let r = p.relators[r_idx];
            let suffix = r.subrange(pos + 1, r.len() as int);
            let c_after = trace_word(t, start, r.subrange(0, pos + 1)).unwrap();
            all_gens_trivial_in_trace(t, p, reps, c_after, suffix)
        }),
{
    reveal(certificate_wf);
    let (r_idx, start, pos) = certificates[k];
    let r = p.relators[r_idx];

    assert(word_valid(r, t.num_gens)) by { assert(word_valid(r, p.num_generators)); }

    // Suffix positions: j in [pos+1, r.len()), all j != pos
    assert forall|j: int| pos + 1 <= j < r.len() implies #[trigger]
        edge_at_pos_handled(t, parent, non_tree_edges, start, r, j, k) by {
        assert(r[j] == r[j]); // trigger
    }

    lemma_relator_subword_trivial(parent, depth, t, p, non_tree_edges, start, r, pos + 1, r.len() as int, k);
}

/// Step 2: extract gen_pos from sp using prefix/suffix triviality.
proof fn lemma_non_tree_step2_extract_gen(
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    t: CosetTable, p: Presentation,
    non_tree_edges: Seq<(nat, Symbol)>,
    certificates: Seq<(int, nat, int)>,
    k: int,
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
        0 <= k < non_tree_edges.len() as int,
        forall|c: nat, s: Symbol|
            c < t.num_cosets && symbol_valid(s, t.num_gens) &&
            symbol_to_column(s) < 2 * t.num_gens &&
            t.table[c as int][symbol_to_column(s) as int] is Some &&
            #[trigger] is_tree_edge(parent, c, s, t.table[c as int][symbol_to_column(s) as int].unwrap())
            ==> schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), c, s),
        forall|m: int| #![trigger non_tree_edges[m]] 0 <= m < k ==>
            schreier_gen_equiv(t, p, |d: nat| tree_rep(parent, depth, d), non_tree_edges[m].0, non_tree_edges[m].1),
    ensures
        ({
            let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
            let (r_idx, start, pos) = certificates[k];
            let r = p.relators[r_idx];
            let c_pos = trace_word(t, start, r.subrange(0, pos)).unwrap();
            let s_pos = r[pos];
            let col_pos = symbol_to_column(s_pos);
            let d_pos = t.table[c_pos as int][col_pos as int].unwrap();
            let s_word: Word = Seq::new(1, |_j: int| s_pos);
            let gen_pos = concat(concat(reps(c_pos), s_word), inverse_word(reps(d_pos)));
            equiv_in_presentation(p, schreier_product(t, reps, start, r), gen_pos)
        }),
{
    reveal(certificate_wf);
    let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };
    let (r_idx, start, pos) = certificates[k];
    let r = p.relators[r_idx];

    lemma_tree_rep_is_rep_system(parent, depth, t);

    assert(word_valid(r, t.num_gens)) by { assert(word_valid(r, p.num_generators)); }

    // Prefix and suffix triviality from extracted helpers
    lemma_step2_prefix_trivial(parent, depth, t, p, non_tree_edges, certificates, k);
    lemma_step2_suffix_trivial(parent, depth, t, p, non_tree_edges, certificates, k);

    // Extract gen_pos
    lemma_extract_nontrivial_gen(t, p, reps, start, r, pos);
}

// lemma_all_non_tree_trivial is in schreier_induction.rs (separate module for rlimit isolation)

// ========================================================================
// Part 7: Main theorem
// ========================================================================

/// Main theorem: a spanning tree witness proves has_schreier_system.
pub proof fn lemma_schreier_trivial_from_witness(
    t: CosetTable, p: Presentation,
    parent: spec_fn(nat) -> Option<(nat, Symbol)>,
    depth: spec_fn(nat) -> nat,
    non_tree_edges: Seq<(nat, Symbol)>,
    certificates: Seq<(int, nat, int)>,
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
    ensures
        has_schreier_system(t, p),
{
    reveal(certificate_wf);
    let reps = |d: nat| -> Word { tree_rep(parent, depth, d) };

    // Rep system validity
    lemma_tree_rep_is_rep_system(parent, depth, t);

    // Tree edge triviality
    assert forall|c: nat, s: Symbol|
        c < t.num_cosets && symbol_valid(s, t.num_gens) &&
        symbol_to_column(s) < 2 * t.num_gens &&
        t.table[c as int][symbol_to_column(s) as int] is Some &&
        #[trigger] is_tree_edge(parent, c, s, t.table[c as int][symbol_to_column(s) as int].unwrap())
        implies schreier_gen_equiv(t, p, reps, c, s)
    by {
        lemma_tree_edge_trivial(parent, depth, t, p, c, s);
    }

    // Non-tree edge triviality (induction)
    lemma_all_non_tree_trivial(parent, depth, t, p, non_tree_edges, certificates,
        non_tree_edges.len() as int);

    // Prove full schreier_trivial
    assert forall|c: nat, s: Symbol|
        c < t.num_cosets && symbol_valid(s, t.num_gens)
        implies #[trigger] schreier_gen_equiv(t, p, reps, c, s)
    by {
        // symbol_to_column(s) < 2 * t.num_gens from symbol_valid
        let col = symbol_to_column(s);
        assert(col < 2 * t.num_gens) by {
            match s {
                Symbol::Gen(i) => { assert(col == 2 * i); }
                Symbol::Inv(i) => { assert(col == 2 * i + 1); }
            }
        }
        let s_word: Word = Seq::new(1, |_j: int| s);
        lemma_trace_complete(t, c, s_word);
        let d = t.table[c as int][col as int].unwrap();
        if is_tree_edge(parent, c, s, d) {
            // Already proved
        } else {
            // Must be in non_tree_edges by coverage
            let idx = choose|idx: int| 0 <= idx < non_tree_edges.len() && non_tree_edges[idx] == (c, s);
            assert(non_tree_edges[idx].0 == c);
            assert(non_tree_edges[idx].1 == s);
        }
    }

    assert(schreier_trivial(t, p, reps));
    assert(is_coset_rep_system(t, reps) && schreier_trivial(t, p, reps));
}

} // verus!
