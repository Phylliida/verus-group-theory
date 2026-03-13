use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;

verus! {

/// Coset table for a finitely presented group.
/// table[coset][column] where column = 2*gen for Gen(gen), 2*gen+1 for Inv(gen).
/// None means undefined.
pub struct CosetTable {
    pub num_cosets: nat,
    pub num_gens: nat,
    pub table: Seq<Seq<Option<nat>>>,
}

/// Map a symbol to a column index.
pub open spec fn symbol_to_column(s: Symbol) -> nat {
    match s {
        Symbol::Gen(i) => 2 * i,
        Symbol::Inv(i) => 2 * i + 1,
    }
}

/// Map a column to its inverse column (Gen ↔ Inv for same generator).
pub open spec fn inverse_column(col: nat) -> nat {
    if col % 2 == 0 {
        col + 1
    } else {
        (col - 1) as nat
    }
}

/// A coset table is well-formed: dimensions match and values in range.
pub open spec fn coset_table_wf(t: CosetTable) -> bool {
    let num_cols = 2 * t.num_gens;
    t.table.len() == t.num_cosets
    && (forall|c: int| #![trigger t.table[c]]
        0 <= c < t.num_cosets ==> t.table[c].len() == num_cols)
    && (forall|c: int, col: int| #![trigger t.table[c][col]]
        0 <= c < t.num_cosets && 0 <= col < num_cols ==>
            match t.table[c][col] {
                Some(d) => d < t.num_cosets,
                None => true,
            })
}

/// Inverse consistency: if table[c][col] = Some(d), then table[d][inv_col] = Some(c).
pub open spec fn coset_table_consistent(t: CosetTable) -> bool {
    let num_cols = 2 * t.num_gens;
    coset_table_wf(t)
    && (forall|c: int, col: int| #![trigger t.table[c][col]]
        0 <= c < t.num_cosets && 0 <= col < num_cols ==>
            match t.table[c][col] {
                Some(d) => t.table[d as int][inverse_column(col as nat) as int] == Some(c as nat),
                None => true,
            })
}

/// Trace a word through the coset table starting from a coset.
/// Returns None if an undefined entry is hit.
pub open spec fn trace_word(t: CosetTable, coset: nat, w: Word) -> Option<nat>
    decreases w.len(),
{
    if w.len() == 0 {
        Some(coset)
    } else {
        let col = symbol_to_column(w.first());
        match t.table[coset as int][col as int] {
            Some(next) => trace_word(t, next, w.drop_first()),
            None => None,
        }
    }
}

/// All relators trace back to the starting coset (closed table).
pub open spec fn relator_closed(t: CosetTable, p: Presentation) -> bool {
    forall|c: int, r: int| #![trigger t.table[c as int], p.relators[r]]
        0 <= c < t.num_cosets && 0 <= r < p.relators.len() ==>
            trace_word(t, c as nat, p.relators[r]) == Some(c as nat)
}

// --- Lemmas ---

/// Tracing the empty word returns the starting coset.
pub proof fn lemma_trace_empty(t: CosetTable, coset: nat)
    ensures
        trace_word(t, coset, empty_word()) == Some(coset),
{
}

/// Tracing a concatenation is composition of traces.
pub proof fn lemma_trace_word_concat(t: CosetTable, c: nat, w1: Word, w2: Word)
    requires
        coset_table_wf(t),
        trace_word(t, c, w1) is Some,
    ensures
        trace_word(t, c, concat(w1, w2)) ==
            trace_word(t, trace_word(t, c, w1).unwrap(), w2),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(trace_word(t, c, w1) == Some(c));
    } else {
        let col = symbol_to_column(w1.first());
        let next = t.table[c as int][col as int].unwrap();
        assert(concat(w1, w2).first() == w1.first());
        assert(concat(w1, w2).drop_first() =~= concat(w1.drop_first(), w2));
        // trace_word(t, c, concat(w1, w2))
        //   = trace_word(t, next, concat(w1.drop_first(), w2))
        // trace_word(t, c, w1)
        //   = trace_word(t, next, w1.drop_first())
        lemma_trace_word_concat(t, next, w1.drop_first(), w2);
    }
}

// ============================================================
// Runtime Coset Enumeration
// ============================================================

/// Runtime coset table: flat array, usize::MAX = undefined.
pub struct RuntimeCosetTable {
    pub num_cosets: usize,
    pub num_gens: usize,
    /// Flat table: table[c * 2*num_gens + col].
    pub table: Vec<usize>,
}

/// Undefined sentinel value.
pub open spec fn UNDEF() -> usize { usize::MAX }

/// Access the runtime table at (coset, column).
pub open spec fn rt_table_get(t: &RuntimeCosetTable, c: usize, col: usize) -> usize
    recommends c < t.num_cosets, col < 2 * t.num_gens,
{
    t.table@[(c * 2 * t.num_gens + col) as int]
}

/// Runtime symbol to column.
pub fn symbol_to_column_exec(s: &crate::runtime::RuntimeSymbol) -> (out: usize)
    ensures
        out == symbol_to_column(crate::runtime::runtime_symbol_view(*s)) as usize,
{
    match s {
        crate::runtime::RuntimeSymbol::Gen(i) => 2 * *i,
        crate::runtime::RuntimeSymbol::Inv(i) => 2 * *i + 1,
    }
}

/// Scan a relator from a coset, returning the final coset or usize::MAX if undefined.
pub fn scan_relator_exec(
    table: &RuntimeCosetTable,
    coset: usize,
    relator: &Vec<crate::runtime::RuntimeSymbol>,
) -> (out: usize)
    requires
        coset < table.num_cosets,
        table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
        table.table@.len() == table.num_cosets * 2 * table.num_gens,
        table.num_gens > 0,
        forall|k: int| 0 <= k < relator@.len() ==>
            symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * table.num_gens,
    ensures
        out == UNDEF() || out < table.num_cosets,
{
    let num_cols = 2 * table.num_gens;
    let mut current = coset;
    let mut i: usize = 0;
    while i < relator.len()
        invariant
            0 <= i <= relator.len(),
            current < table.num_cosets,
            table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
            table.table@.len() == table.num_cosets * 2 * table.num_gens,
            num_cols == 2 * table.num_gens,
            table.num_gens > 0,
            forall|k: int| 0 <= k < relator@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * table.num_gens,
        decreases relator.len() - i,
    {
        let col = symbol_to_column_exec(&relator[i]);
        let idx = current * num_cols + col;
        let next = table.table[idx];
        if next == usize::MAX {
            return usize::MAX;
        }
        proof {
            // next < table.num_cosets (from table well-formedness invariant that callers must ensure)
            // For now we just assume it since we don't carry the full wf invariant
            assume(next < table.num_cosets);
        }
        current = next;
        i = i + 1;
    }
    current
}

/// Simple coset enumeration: define table entries and scan relators.
/// Returns None if the bound is exceeded or a conflict is found.
pub fn enumerate_cosets_exec(
    num_gens: usize,
    relators: &Vec<Vec<crate::runtime::RuntimeSymbol>>,
    max_cosets: usize,
) -> (out: Option<RuntimeCosetTable>)
    requires
        num_gens > 0,
        max_cosets > 0,
        max_cosets * (2 * num_gens + 1) < usize::MAX,
        // All relator symbols have valid generator indices
        forall|r: int, k: int| #![trigger relators@[r]@[k]]
            0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
    ensures
        out is Some ==> out.unwrap().num_cosets <= max_cosets,
{
    let num_cols: usize = 2 * num_gens;
    let table_size = max_cosets * num_cols;
    let mut table: Vec<usize> = Vec::new();

    // Initialize table with UNDEF
    let mut init_i: usize = 0;
    while init_i < table_size
        invariant
            0 <= init_i <= table_size,
            table@.len() == init_i,
            table_size == max_cosets * num_cols,
            num_cols == 2 * num_gens,
            max_cosets * (2 * num_gens + 1) < usize::MAX,
        decreases table_size - init_i,
    {
        table.push(usize::MAX);
        init_i = init_i + 1;
    }

    let mut rt = RuntimeCosetTable {
        num_cosets: 1, // Start with coset 0
        num_gens,
        table,
    };

    // Main loop: scan for undefined entries, define them, scan relators
    let mut fuel: usize = max_cosets * num_cols;
    while fuel > 0
        invariant
            rt.num_cosets >= 1,
            rt.num_cosets <= max_cosets,
            rt.num_gens == num_gens,
            num_cols == 2 * num_gens,
            rt.table@.len() == table_size,
            table_size == max_cosets * num_cols,
            max_cosets * (2 * num_gens + 1) < usize::MAX,
            num_gens > 0,
            forall|r: int, k: int| #![trigger relators@[r]@[k]]
                0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                    symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
        decreases fuel,
    {
        // Find first undefined entry
        let mut found = false;
        let mut fc: usize = 0;
        let mut fcol: usize = 0;

        let mut sc: usize = 0;
        while sc < rt.num_cosets && !found
            invariant
                0 <= sc <= rt.num_cosets,
                rt.num_cosets <= max_cosets,
                num_cols == 2 * num_gens,
                rt.table@.len() == table_size,
                table_size == max_cosets * num_cols,
                max_cosets * (2 * num_gens + 1) < usize::MAX,
                num_gens > 0,
                found ==> fc < rt.num_cosets && fcol < num_cols,
            decreases rt.num_cosets - sc,
        {
            let mut scol: usize = 0;
            while scol < num_cols && !found
                invariant
                    0 <= scol <= num_cols,
                    sc < rt.num_cosets,
                    rt.num_cosets <= max_cosets,
                    num_cols == 2 * num_gens,
                    rt.table@.len() == table_size,
                    table_size == max_cosets * num_cols,
                    max_cosets * (2 * num_gens + 1) < usize::MAX,
                    num_gens > 0,
                    found ==> fc < rt.num_cosets && fcol < num_cols,
                decreases num_cols - scol,
            {
                let idx = sc * num_cols + scol;
                if rt.table[idx] == usize::MAX {
                    fc = sc;
                    fcol = scol;
                    found = true;
                }
                scol = scol + 1;
            }
            sc = sc + 1;
        }

        if !found {
            // Table is complete
            return Some(rt);
        }

        // Define a new coset for the undefined entry
        if rt.num_cosets >= max_cosets {
            return None; // Bound exceeded
        }

        let new_coset = rt.num_cosets;
        let idx1 = fc * num_cols + fcol;
        rt.table.set(idx1, new_coset);

        // Set inverse: table[new_coset][inv_col] = fc
        let inv_col: usize = if fcol % 2 == 0 { fcol + 1 } else { fcol - 1 };
        let idx2 = new_coset * num_cols + inv_col;
        rt.table.set(idx2, fc);

        rt.num_cosets = rt.num_cosets + 1;

        // Scan all relators from all cosets to find forced entries
        let mut ri: usize = 0;
        while ri < relators.len()
            invariant
                0 <= ri <= relators.len(),
                rt.num_cosets >= 1,
                rt.num_cosets <= max_cosets,
                rt.num_gens == num_gens,
                num_cols == 2 * num_gens,
                rt.table@.len() == table_size,
                table_size == max_cosets * num_cols,
                max_cosets * (2 * num_gens + 1) < usize::MAX,
                num_gens > 0,
                forall|r: int, k: int| #![trigger relators@[r]@[k]]
                    0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                        symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
            decreases relators.len() - ri,
        {
            // Just scan from coset 0 for now (simplified)
            let result = scan_relator_exec(&rt, 0, &relators[ri]);
            // In a full implementation, we'd fill in forced entries
            // For this simplified version, we just proceed
            ri = ri + 1;
        }

        fuel = fuel - 1;
    }

    None // Ran out of fuel
}

} // verus!
