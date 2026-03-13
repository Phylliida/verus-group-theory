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
    requires
        symbol_to_column(crate::runtime::runtime_symbol_view(*s)) < usize::MAX,
    ensures
        out == symbol_to_column(crate::runtime::runtime_symbol_view(*s)) as usize,
{
    match s {
        crate::runtime::RuntimeSymbol::Gen(i) => 2 * *i,
        crate::runtime::RuntimeSymbol::Inv(i) => 2 * *i + 1,
    }
}

/// Helper: derive overflow bounds from the multiplication guard.
proof fn lemma_overflow_bounds(num_cosets: usize, num_gens: usize)
    requires
        num_cosets >= 1,
        num_cosets * (2 * num_gens + 1) < usize::MAX,
    ensures
        2 * num_gens < usize::MAX,
        num_cosets * 2 * num_gens < usize::MAX,
{
    assert(2 * num_gens + 1 <= num_cosets * (2 * num_gens + 1)) by(nonlinear_arith)
        requires num_cosets >= 1int, num_gens >= 0int;
    assert(num_cosets * 2 * num_gens <= num_cosets * (2 * num_gens + 1)) by(nonlinear_arith)
        requires num_cosets >= 0int, num_gens >= 0int;
}

/// Scan a relator from a coset, returning the final coset or usize::MAX if undefined.
pub fn scan_relator_exec(
    table: &RuntimeCosetTable,
    coset: usize,
    relator: &Vec<crate::runtime::RuntimeSymbol>,
) -> (out: usize)
    requires
        coset < table.num_cosets,
        table.num_cosets >= 1,
        table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
        table.table@.len() >= table.num_cosets * 2 * table.num_gens,
        table.num_gens > 0,
        forall|k: int| 0 <= k < relator@.len() ==>
            symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * table.num_gens,
    ensures
        out == UNDEF() || out < table.num_cosets,
{
    proof { lemma_overflow_bounds(table.num_cosets, table.num_gens); }
    let num_cols: usize = 2 * table.num_gens;
    let mut current = coset;
    let mut i: usize = 0;
    while i < relator.len()
        invariant
            0 <= i <= relator.len(),
            current < table.num_cosets,
            table.num_cosets >= 1,
            table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
            table.table@.len() >= table.num_cosets * 2 * table.num_gens,
            num_cols == 2 * table.num_gens,
            table.num_gens > 0,
            2 * table.num_gens < usize::MAX,
            table.num_cosets * 2 * table.num_gens < usize::MAX,
            forall|k: int| 0 <= k < relator@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * table.num_gens,
        decreases relator.len() - i,
    {
        proof {
            assert(symbol_to_column(crate::runtime::runtime_symbol_view(relator@[i as int])) < 2 * table.num_gens);
        }
        let col = symbol_to_column_exec(&relator[i]);
        proof {
            assert(current * num_cols + col < table.num_cosets * num_cols) by(nonlinear_arith)
                requires current < table.num_cosets, col < num_cols, num_cols == 2 * table.num_gens,
                    table.num_gens > 0int;
            assert(table.num_cosets * num_cols <= table.num_cosets * 2 * table.num_gens) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int, table.num_cosets >= 0int;
        }
        let idx = current * num_cols + col;
        let next = table.table[idx];
        if next == usize::MAX || next >= table.num_cosets {
            return usize::MAX;
        }
        current = next;
        i = i + 1;
    }
    current
}

/// Result of scanning a relator through the coset table.
pub enum ScanResult {
    /// Relator traces back correctly, no changes needed.
    Closed,
    /// Exactly one gap found and filled (+ inverse entry).
    Deduction,
    /// Multiple gaps remain, no deduction possible.
    Incomplete,
    /// Conflict detected: two different cosets forced equal.
    Coincidence,
}

/// Compute the inverse column index (exec version).
pub fn inverse_column_exec(col: usize) -> (out: usize)
    requires col < usize::MAX,
    ensures out == inverse_column(col as nat) as usize,
{
    if col % 2 == 0 { col + 1 } else { col - 1 }
}

/// Scan a relator from a coset with forward+backward scanning, filling single-gap deductions.
///
/// Forward scans from `coset` through relator symbols until hitting UNDEF.
/// Backward scans from `coset` through inverse symbols until meeting the forward scan.
/// If exactly one gap remains, fills it (deduction). If the endpoints disagree, returns Coincidence.
pub fn scan_and_fill_exec(
    table: &mut RuntimeCosetTable,
    coset: usize,
    relator: &Vec<crate::runtime::RuntimeSymbol>,
) -> (out: ScanResult)
    requires
        coset < old(table).num_cosets,
        old(table).num_cosets >= 1,
        old(table).num_cosets * (2 * old(table).num_gens + 1) < usize::MAX,
        old(table).table@.len() >= old(table).num_cosets * 2 * old(table).num_gens,
        old(table).num_gens > 0,
        forall|k: int| 0 <= k < relator@.len() ==>
            symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * old(table).num_gens,
        // Entry validity (flat array): all entries are UNDEF or < num_cosets
        forall|i: int| #![trigger old(table).table@[i]]
            0 <= i < old(table).table@.len() ==>
            old(table).table@[i] == UNDEF() || old(table).table@[i] < old(table).num_cosets,
    ensures
        table.num_cosets == old(table).num_cosets,
        table.num_gens == old(table).num_gens,
        table.table@.len() == old(table).table@.len(),
        // Entry validity preserved (flat array)
        forall|i: int| #![trigger table.table@[i]]
            0 <= i < table.table@.len() ==>
            table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets,
{
    proof { lemma_overflow_bounds(table.num_cosets, table.num_gens); }
    let num_cols: usize = 2 * table.num_gens;
    let rlen = relator.len();

    if rlen == 0 {
        return ScanResult::Closed;
    }

    // --- Forward scan ---
    let mut f_coset: usize = coset;
    let mut f_pos: usize = 0;
    while f_pos < rlen
        invariant
            0 <= f_pos <= rlen,
            f_coset < table.num_cosets,
            table.num_cosets >= 1,
            table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
            table.table@.len() >= table.num_cosets * 2 * table.num_gens,
            num_cols == 2 * table.num_gens,
            table.num_gens > 0,
            2 * table.num_gens < usize::MAX,
            table.num_cosets * 2 * table.num_gens < usize::MAX,
            rlen == relator@.len(),
            forall|k: int| 0 <= k < relator@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * table.num_gens,
            forall|i: int| #![trigger table.table@[i]]
                0 <= i < table.table@.len() ==>
                table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets,
        decreases rlen - f_pos,
    {
        proof {
            assert(symbol_to_column(crate::runtime::runtime_symbol_view(relator@[f_pos as int])) < 2 * table.num_gens);
        }
        let col = symbol_to_column_exec(&relator[f_pos]);
        proof {
            assert(f_coset * num_cols + col < table.num_cosets * num_cols) by(nonlinear_arith)
                requires f_coset < table.num_cosets, col < num_cols, num_cols == 2 * table.num_gens, table.num_gens > 0int;
            assert(table.num_cosets * num_cols <= table.num_cosets * 2 * table.num_gens) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int, table.num_cosets >= 0int;
        }
        let idx = f_coset * num_cols + col;
        let val = table.table[idx];
        if val == usize::MAX {
            break;
        }
        if val >= table.num_cosets {
            break;
        }
        f_coset = val;
        f_pos = f_pos + 1;
    }

    // If forward scan completed all symbols
    if f_pos == rlen {
        if f_coset == coset {
            return ScanResult::Closed;
        } else {
            return ScanResult::Coincidence;
        }
    }

    // --- Backward scan ---
    let mut b_coset: usize = coset;
    let mut b_pos: usize = rlen;
    while b_pos > f_pos + 1
        invariant
            f_pos < b_pos,
            b_pos <= rlen,
            b_coset < table.num_cosets,
            table.num_cosets >= 1,
            table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
            table.table@.len() >= table.num_cosets * 2 * table.num_gens,
            num_cols == 2 * table.num_gens,
            table.num_gens > 0,
            2 * table.num_gens < usize::MAX,
            table.num_cosets * 2 * table.num_gens < usize::MAX,
            rlen == relator@.len(),
            forall|k: int| 0 <= k < relator@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * table.num_gens,
            forall|i: int| #![trigger table.table@[i]]
                0 <= i < table.table@.len() ==>
                table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets,
        decreases b_pos - f_pos,
    {
        let sym_pos = b_pos - 1;
        proof {
            assert(symbol_to_column(crate::runtime::runtime_symbol_view(relator@[sym_pos as int])) < 2 * table.num_gens);
        }
        let col = symbol_to_column_exec(&relator[sym_pos]);
        let inv_col = inverse_column_exec(col);
        proof {
            assert(inv_col < num_cols) by {
                if col % 2 == 0 {
                    assert(inv_col == col + 1);
                } else {
                    assert(inv_col == col - 1);
                }
            }
            assert(b_coset * num_cols + inv_col < table.num_cosets * num_cols) by(nonlinear_arith)
                requires b_coset < table.num_cosets, inv_col < num_cols, num_cols == 2 * table.num_gens, table.num_gens > 0int;
            assert(table.num_cosets * num_cols <= table.num_cosets * 2 * table.num_gens) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int, table.num_cosets >= 0int;
        }
        let idx = b_coset * num_cols + inv_col;
        let val = table.table[idx];
        if val == usize::MAX {
            break;
        }
        if val >= table.num_cosets {
            break;
        }
        b_coset = val;
        b_pos = b_pos - 1;
    }

    // --- Gap analysis ---
    if b_pos == f_pos + 1 {
        // Exactly one gap at position f_pos: fill table[f_coset][col_f] = b_coset
        proof {
            assert(symbol_to_column(crate::runtime::runtime_symbol_view(relator@[f_pos as int])) < 2 * table.num_gens);
        }
        let col_f = symbol_to_column_exec(&relator[f_pos]);
        let inv_col_f = inverse_column_exec(col_f);
        proof {
            assert(inv_col_f < num_cols) by {
                if col_f % 2 == 0 {
                    assert(inv_col_f == col_f + 1);
                } else {
                    assert(inv_col_f == col_f - 1);
                }
            }
        }

        // Check for coincidence
        proof {
            assert(f_coset * num_cols + col_f < table.num_cosets * num_cols) by(nonlinear_arith)
                requires f_coset < table.num_cosets, col_f < num_cols, num_cols == 2 * table.num_gens, table.num_gens > 0int;
            assert(table.num_cosets * num_cols <= table.num_cosets * 2 * table.num_gens) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int, table.num_cosets >= 0int;
        }
        let idx_fwd = f_coset * num_cols + col_f;
        let existing_fwd = table.table[idx_fwd];
        if existing_fwd != usize::MAX && existing_fwd != b_coset {
            return ScanResult::Coincidence;
        }

        proof {
            assert(b_coset * num_cols + inv_col_f < table.num_cosets * num_cols) by(nonlinear_arith)
                requires b_coset < table.num_cosets, inv_col_f < num_cols, num_cols == 2 * table.num_gens, table.num_gens > 0int;
            assert(table.num_cosets * num_cols <= table.num_cosets * 2 * table.num_gens) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int, table.num_cosets >= 0int;
        }
        let idx_bwd = b_coset * num_cols + inv_col_f;
        let existing_bwd = table.table[idx_bwd];
        if existing_bwd != usize::MAX && existing_bwd != f_coset {
            return ScanResult::Coincidence;
        }

        // Fill the deduction
        table.table.set(idx_fwd, b_coset);
        table.table.set(idx_bwd, f_coset);

        // Flat array validity preserved: both written values < num_cosets,
        // and all other entries unchanged from the old valid state.
        proof {
            assert forall|i: int| #![trigger table.table@[i]]
                0 <= i < table.table@.len() implies
                table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets
            by {
                if i == idx_bwd as int {
                    // f_coset < num_cosets
                } else if i == idx_fwd as int {
                    // b_coset < num_cosets
                } else {
                    // unchanged
                }
            }
        }

        return ScanResult::Deduction;
    }

    // Multiple gaps
    ScanResult::Incomplete
}

/// Todd-Coxeter coset enumeration.
///
/// Algorithm:
///   Outer loop (≤ max_cosets iterations, each adds one coset):
///     Phase 1: Saturate deductions by scanning all relators from all cosets.
///     Phase 2: Check completeness — if no UNDEF entries, return the table.
///     Phase 3: Define new coset at first UNDEF entry.
///
/// Returns None if max_cosets exceeded or a coincidence is found.
pub fn enumerate_cosets_exec(
    num_gens: usize,
    relators: &Vec<Vec<crate::runtime::RuntimeSymbol>>,
    max_cosets: usize,
) -> (out: Option<RuntimeCosetTable>)
    requires
        num_gens > 0,
        max_cosets > 0,
        max_cosets * (2 * num_gens + 1) < usize::MAX,
        forall|r: int, k: int| #![trigger relators@[r]@[k]]
            0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
    ensures
        out is Some ==> out.unwrap().num_cosets <= max_cosets,
{
    proof { lemma_overflow_bounds(max_cosets, num_gens); }
    let num_cols: usize = 2 * num_gens;
    proof {
        assert(max_cosets * num_cols < usize::MAX) by(nonlinear_arith)
            requires num_cols == 2 * num_gens, max_cosets * 2 * num_gens < usize::MAX,
                num_gens >= 0int, max_cosets >= 0int;
    }
    let table_size: usize = max_cosets * num_cols;
    let mut table: Vec<usize> = Vec::new();

    // Initialize table with UNDEF
    let mut init_i: usize = 0;
    while init_i < table_size
        invariant
            0 <= init_i <= table_size,
            table@.len() == init_i,
            table_size == max_cosets * num_cols,
            num_cols == 2 * num_gens,
            forall|j: int| #![trigger table@[j]]
                0 <= j < init_i ==> table@[j] == UNDEF(),
        decreases table_size - init_i,
    {
        table.push(usize::MAX);
        init_i = init_i + 1;
    }

    let mut rt = RuntimeCosetTable {
        num_cosets: 1,
        num_gens,
        table,
    };

    // --- Outer loop: each iteration potentially adds one coset ---
    let mut outer_fuel: usize = max_cosets;
    while outer_fuel > 0
        invariant
            rt.num_cosets >= 1,
            rt.num_cosets <= max_cosets,
            rt.num_gens == num_gens,
            num_cols == 2 * num_gens,
            rt.table@.len() == table_size,
            table_size == max_cosets * num_cols,
            max_cosets * (2 * num_gens + 1) < usize::MAX,
            2 * num_gens < usize::MAX,
            max_cosets * 2 * num_gens < usize::MAX,
            num_gens > 0,
            forall|r: int, k: int| #![trigger relators@[r]@[k]]
                0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                    symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
            // Flat array validity
            forall|j: int| #![trigger rt.table@[j]]
                0 <= j < rt.table@.len() ==>
                rt.table@[j] == UNDEF() || rt.table@[j] < rt.num_cosets,
        decreases outer_fuel,
    {
        // === Phase 1: Saturate deductions ===
        let mut deduction_fuel: usize = max_cosets * num_cols;
        let mut any_progress = true;
        while any_progress && deduction_fuel > 0
            invariant
                rt.num_cosets >= 1,
                rt.num_cosets <= max_cosets,
                rt.num_gens == num_gens,
                num_cols == 2 * num_gens,
                rt.table@.len() == table_size,
                table_size == max_cosets * num_cols,
                max_cosets * (2 * num_gens + 1) < usize::MAX,
                2 * num_gens < usize::MAX,
                max_cosets * 2 * num_gens < usize::MAX,
                num_gens > 0,
                forall|r: int, k: int| #![trigger relators@[r]@[k]]
                    0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                        symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
                forall|j: int| #![trigger rt.table@[j]]
                    0 <= j < rt.table@.len() ==>
                    rt.table@[j] == UNDEF() || rt.table@[j] < rt.num_cosets,
            decreases deduction_fuel,
        {
            any_progress = false;
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
                    2 * num_gens < usize::MAX,
                    max_cosets * 2 * num_gens < usize::MAX,
                    num_gens > 0,
                    forall|r: int, k: int| #![trigger relators@[r]@[k]]
                        0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                            symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
                    forall|j: int| #![trigger rt.table@[j]]
                        0 <= j < rt.table@.len() ==>
                        rt.table@[j] == UNDEF() || rt.table@[j] < rt.num_cosets,
                decreases relators.len() - ri,
            {
                let mut ci: usize = 0;
                while ci < rt.num_cosets
                    invariant
                        0 <= ci <= rt.num_cosets,
                        0 <= ri < relators.len(),
                        rt.num_cosets >= 1,
                        rt.num_cosets <= max_cosets,
                        rt.num_gens == num_gens,
                        num_cols == 2 * num_gens,
                        rt.table@.len() == table_size,
                        table_size == max_cosets * num_cols,
                        max_cosets * (2 * num_gens + 1) < usize::MAX,
                        2 * num_gens < usize::MAX,
                        max_cosets * 2 * num_gens < usize::MAX,
                        num_gens > 0,
                        forall|r: int, k: int| #![trigger relators@[r]@[k]]
                            0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                                symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
                        forall|j: int| #![trigger rt.table@[j]]
                            0 <= j < rt.table@.len() ==>
                            rt.table@[j] == UNDEF() || rt.table@[j] < rt.num_cosets,
                    decreases rt.num_cosets - ci,
                {
                    proof {
                        assert(rt.num_cosets * (2 * rt.num_gens + 1) <= max_cosets * (2 * num_gens + 1)) by(nonlinear_arith)
                            requires rt.num_cosets <= max_cosets, rt.num_gens == num_gens, num_gens > 0int;
                        assert(rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens) by(nonlinear_arith)
                            requires
                                rt.table@.len() == table_size,
                                table_size == max_cosets * num_cols,
                                num_cols == 2 * num_gens,
                                rt.num_gens == num_gens,
                                rt.num_cosets <= max_cosets,
                                num_gens > 0int;
                    }
                    let result = scan_and_fill_exec(&mut rt, ci, &relators[ri]);
                    match result {
                        ScanResult::Deduction => { any_progress = true; },
                        ScanResult::Coincidence => { return None; },
                        _ => {},
                    }
                    ci = ci + 1;
                }
                ri = ri + 1;
            }
            deduction_fuel = deduction_fuel - 1;
        }

        // === Phase 2: Check completeness ===
        let mut complete = true;
        let mut fc: usize = 0;
        let mut fcol: usize = 0;

        let mut sc: usize = 0;
        while sc < rt.num_cosets
            invariant
                0 <= sc <= rt.num_cosets,
                rt.num_cosets <= max_cosets,
                num_cols == 2 * num_gens,
                rt.table@.len() == table_size,
                table_size == max_cosets * num_cols,
                max_cosets * (2 * num_gens + 1) < usize::MAX,
                max_cosets * 2 * num_gens < usize::MAX,
                num_gens > 0,
                complete ==> true,
                !complete ==> fc < rt.num_cosets && fcol < num_cols,
            decreases rt.num_cosets - sc,
        {
            if !complete { break; }
            let mut scol: usize = 0;
            while scol < num_cols
                invariant
                    0 <= scol <= num_cols,
                    sc < rt.num_cosets,
                    rt.num_cosets <= max_cosets,
                    num_cols == 2 * num_gens,
                    rt.table@.len() == table_size,
                    table_size == max_cosets * num_cols,
                    max_cosets * (2 * num_gens + 1) < usize::MAX,
                    max_cosets * 2 * num_gens < usize::MAX,
                    num_gens > 0,
                    complete ==> true,
                    !complete ==> fc < rt.num_cosets && fcol < num_cols,
                decreases num_cols - scol,
            {
                if !complete { break; }
                proof {
                    assert(sc * num_cols + scol < max_cosets * num_cols) by(nonlinear_arith)
                        requires sc < max_cosets, scol < num_cols, num_cols > 0int;
                }
                let idx = sc * num_cols + scol;
                if rt.table[idx] == usize::MAX {
                    fc = sc;
                    fcol = scol;
                    complete = false;
                }
                scol = scol + 1;
            }
            sc = sc + 1;
        }

        if complete {
            // Table is complete — enumeration done!
            return Some(rt);
        }

        // === Phase 3: Define new coset ===
        if rt.num_cosets >= max_cosets {
            return None;
        }

        let new_coset = rt.num_cosets;
        proof {
            assert(fc * num_cols + fcol < max_cosets * num_cols) by(nonlinear_arith)
                requires fc < max_cosets, fcol < num_cols, num_cols > 0int;
        }
        let idx1 = fc * num_cols + fcol;
        rt.table.set(idx1, new_coset);

        // Set inverse: table[new_coset][inv_col] = fc
        let inv_col: usize = if fcol % 2 == 0 { fcol + 1 } else { fcol - 1 };
        proof {
            assert(new_coset * num_cols + inv_col < max_cosets * num_cols) by(nonlinear_arith)
                requires new_coset < max_cosets, inv_col < num_cols, num_cols > 0int;
        }
        let idx2 = new_coset * num_cols + inv_col;
        rt.table.set(idx2, fc);

        rt.num_cosets = rt.num_cosets + 1;

        // Prove flat array validity after adding new coset
        proof {
            // new_coset == old num_cosets, so new_coset < new num_cosets
            // fc < old num_cosets < new num_cosets
            assert forall|j: int| #![trigger rt.table@[j]]
                0 <= j < rt.table@.len() implies
                rt.table@[j] == UNDEF() || rt.table@[j] < rt.num_cosets
            by {
                if j == idx2 as int {
                    // fc < old num_cosets < new num_cosets
                } else if j == idx1 as int {
                    // new_coset == old num_cosets == new num_cosets - 1 < new num_cosets
                } else {
                    // unchanged: was UNDEF or < old num_cosets <= new num_cosets
                }
            }
        }

        outer_fuel = outer_fuel - 1;
    }

    None
}

} // verus!
