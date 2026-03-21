use vstd::prelude::*;
use crate::word::*;
use crate::symbol::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;
use crate::britton::*;
use crate::britton_proof::*;

verus! {

/// Helper: 3-way tail-shift equivalence. Given tail = u1 ++ w_right,
/// w =~= left ++ w_right, w_end =~= left ++ tail[|u2|..],
/// and u2 ≡ u1 in G, prove w ≡ w_end.
///
/// Used by rr_nn (u1=inv_b_j1, u2=inv_b_j2).
/// Isolated in helper module to avoid trigger pollution on other britton_proof functions.
pub proof fn lemma_tail_shift_equiv(
    p: Presentation, n: nat,
    w: Word, w_left: Word, w_right: Word, w_end: Word,
    u1: Word, u2: Word, tail: Word,
)
    requires
        presentation_valid(p),
        p.num_generators == n,
        word_valid(u1, n),
        word_valid(u2, n),
        word_valid(w_left, n),
        word_valid(w_right, n),
        tail =~= concat(u1, w_right),
        // Word-level overlap: u2 characters match the tail prefix
        u2.len() <= tail.len(),
        u2 =~= tail.subrange(0, u2.len() as int),
        w =~= concat(w_left, w_right),
        w_end =~= concat(w_left, tail.subrange(u2.len() as int, tail.len() as int)),
        equiv_in_presentation(p, u2, u1),
    ensures
        equiv_in_presentation(p, w, w_end),
{
    if u1.len() == u2.len() {
        // tail[|u2|..] = tail[|u1|..] = w_right, so w_end =~= w
        assert(tail.subrange(u2.len() as int, tail.len() as int) =~= w_right);
        assert(w_end =~= w);
        lemma_equiv_refl(p, w);
    } else if u1.len() > u2.len() {
        // extra = tail[|u2|..|u1|] = u1[|u2|..|u1|]
        let extra = tail.subrange(u2.len() as int, u1.len() as int);
        assert(tail.subrange(u2.len() as int, tail.len() as int) =~= extra + w_right);
        assert(w_end =~= w_left + (extra + w_right));
        // u1 = u1[0..|u2|] + u1[|u2|..] = u2 + extra
        assert(u1 =~= u1.subrange(0, u2.len() as int) + extra);
        assert(u1 =~= concat(u2, extra));
        lemma_subrange_word_valid(u1, u2.len() as int, u1.len() as int, n);
        // We have equiv(p, u2, u1). Flip to get equiv(p, u1, u2),
        // i.e., equiv(p, concat(u2, extra), u2). Then right_cancel gives extra ≡ ε.
        lemma_equiv_symmetric(p, u2, u1);
        lemma_right_cancel(p, u2, extra);
        lemma_insert_trivial_equiv(p, w_left, w_right, extra);
    } else {
        // u2.len() > u1.len()
        // Work with w_right subranges directly (avoids subrange-of-concat issues)
        let diff: int = u2.len() as int - u1.len() as int;

        // Bounds: diff <= w_right.len() (from u2 fits in tail, tail = u1 + w_right)
        assert(tail.len() == u1.len() + w_right.len());
        assert(u2.len() <= tail.len());
        assert(diff <= w_right.len() as int);

        let extra = w_right.subrange(0, diff);
        let rest = w_right.subrange(diff, w_right.len() as int);

        // w_right = extra + rest (standard Seq split)
        assert(w_right =~= extra + rest);

        // w = w_left + w_right = w_left + (extra + rest)
        assert(w =~= concat(w_left, concat(extra, rest)));

        // tail[|u2|..] = w_right[diff..] = rest
        // Need element-wise bridge: tail[u2_len + k] = w_right[diff + k] = rest[k]
        assert forall|k: int| 0 <= k < rest.len()
            implies tail[(u2.len() as int + k) as int] == rest[k]
        by {}
        assert(tail.subrange(u2.len() as int, tail.len() as int) =~= rest);
        assert(w_end =~= concat(w_left, rest));

        // u2 = tail[0..|u2|] and concat(u1, extra) has the same elements:
        // for i < |u1|: u2[i] = tail[i] = u1[i] = concat(u1, extra)[i]
        // for |u1| <= i < |u2|: u2[i] = tail[i] = w_right[i-|u1|] = extra[i-|u1|] = concat(u1, extra)[i]
        assert(u2 =~= concat(u1, extra));

        // word_valid for extra
        lemma_subrange_word_valid(w_right, 0, diff, n);

        // right_cancel: equiv(p, u2, u1) and u2 =~= concat(u1, extra) give
        // equiv(p, concat(u1, extra), u1), so extra ≡ ε
        lemma_right_cancel(p, u1, extra);
        lemma_remove_trivial_equiv(p, w_left, rest, extra);
    }
}

/// Helper for rr_ii: 3-way word equivalence based on b_j1/b_j2 length comparison.
/// Extracted from lemma_k2_rr_ii to avoid path explosion with the preamble.
///
/// Given equiv(p, b_j2, b_j1) and w1 containing overlapping r1 (starting with b_j1)
/// and r2 (starting with b_j2), prove w ≡ w_end in G.
pub proof fn lemma_ii_word_shift(
    p: Presentation, n: nat,
    w: Word, w_left: Word, w_right: Word, w_end: Word,
    w1: Word, r1: Word, r2: Word,
    b_j1: Word, b_j2: Word,
    pos0: int,
)
    requires
        presentation_valid(p),
        p.num_generators == n,
        word_valid(b_j1, n), word_valid(b_j2, n),
        word_valid(w_left, n), word_valid(w_right, n),
        w =~= concat(w_left, w_right),
        equiv_in_presentation(p, b_j2, b_j1),
        // w1 structure
        w1 =~= w_left + (r1 + w_right),
        pos0 as int == w_left.len() as int,
        pos0 >= 0,
        // r1 starts with b_j1
        r1.len() >= b_j1.len(),
        forall|i: int| 0 <= i < b_j1.len() ==> r1[i] == b_j1[i],
        // r2 starts with b_j2
        r2.len() >= b_j2.len(),
        forall|i: int| 0 <= i < b_j2.len() ==> r2[i] == b_j2[i],
        // r2 position in w1
        ({
            let pos1 = pos0 + b_j1.len() as int - b_j2.len() as int;
            &&& pos1 >= 0
            &&& pos1 + r2.len() <= w1.len()
            &&& w1.subrange(pos1, pos1 + r2.len() as int) =~= r2
        }),
        // r1/r2 end at same position
        ({
            let pos1 = pos0 + b_j1.len() as int - b_j2.len() as int;
            pos1 + r2.len() as int == pos0 + r1.len() as int
        }),
        // w_end definition
        ({
            let pos1 = pos0 + b_j1.len() as int - b_j2.len() as int;
            &&& w1.subrange(pos0 + r1.len() as int, w1.len() as int) =~= w_right
            &&& w_end =~= w1.subrange(0, pos1) + w_right
        }),
    ensures
        equiv_in_presentation(p, w, w_end),
{
    let pos1 = pos0 + b_j1.len() as int - b_j2.len() as int;
    if b_j1.len() == b_j2.len() {
        assert(pos1 == pos0);
        assert(w1.subrange(0, pos1) =~= w_left);
        assert(w_end =~= w);
        lemma_equiv_refl(p, w);
    } else if b_j1.len() > b_j2.len() {
        let delta = (b_j1.len() - b_j2.len()) as int;
        let extra = b_j1.subrange(0, delta);
        assert(w1.subrange(0, pos0) =~= w_left);
        assert(w1.subrange(pos0, pos1) =~= b_j1.subrange(0, delta));
        assert(w1.subrange(0, pos1) =~= w_left + extra);
        assert(w_end =~= w_left + (extra + w_right));
        // Bridge: b_j1[delta..] = b_j2 via r1/r2 alignment in w1
        assert forall|i_idx: int| 0 <= i_idx < b_j2.len()
            implies b_j1[(delta + i_idx) as int] == #[trigger] b_j2[i_idx]
        by {
            assert(w1[(pos1 + i_idx) as int] == r2[i_idx]);
            assert(r2[i_idx] == b_j2[i_idx]);
            assert(w1[(pos0 + delta + i_idx) as int] == r1[(delta + i_idx) as int]);
            assert(r1[(delta + i_idx) as int] == b_j1[(delta + i_idx) as int]);
        }
        assert(b_j1.subrange(delta, b_j1.len() as int) =~= b_j2);
        assert(b_j1 =~= extra + b_j2);
        // b_j2 ≡ b_j1 = extra ++ b_j2, need concat(extra, b_j2) ≡ b_j2
        lemma_equiv_symmetric(p, b_j2, b_j1);
        lemma_subrange_word_valid(b_j1, 0, delta, n);
        lemma_left_cancel(p, extra, b_j2);
        lemma_insert_trivial_equiv(p, w_left, w_right, extra);
    } else {
        let delta = (b_j2.len() - b_j1.len()) as int;
        let left_trim = w_left.subrange(0, pos0 - delta);
        assert(w1.subrange(0, pos1) =~= left_trim);
        assert(w_end =~= left_trim + w_right);
        let extra = w_left.subrange(pos0 - delta, pos0);
        assert(w_left =~= left_trim + extra);
        assert(w =~= left_trim + (extra + w_right));
        // Bridge: b_j2 = extra + b_j1 via r1/r2 alignment in w1
        assert forall|i: int| 0 <= i < b_j2.len()
            implies (extra + b_j1)[i] == #[trigger] b_j2[i]
        by {
            if i < delta {
                assert((extra + b_j1)[i] == extra[i]);
                assert(w1[(pos1 + i) as int] == r2[i]);
                assert(r2[i] == b_j2[i]);
                assert(w1[(pos1 + i) as int] == w_left[(pos1 + i) as int]);
            } else {
                let k = (i - delta) as int;
                assert((extra + b_j1)[i] == b_j1[k]);
                assert(w1[(pos0 + k) as int] == r1[k]);
                assert(r1[k] == b_j1[k]);
                assert(w1[(pos1 + i) as int] == r2[i]);
                assert(r2[i] == b_j2[i]);
            }
        }
        assert(b_j2 =~= extra + b_j1);
        lemma_subrange_word_valid(w_left, pos0 - delta, pos0, n);
        lemma_left_cancel(p, extra, b_j1);
        lemma_remove_trivial_equiv(p, left_trim, w_right, extra);
    }
}

/// FreeExpand with base symbol preserves baseness.
pub proof fn lemma_base_expand_preserves_base(
    w: Word, p: int, sym: Symbol, n: nat,
)
    requires
        is_base_word(w, n),
        word_valid(w, n + 1),
        generator_index(sym) < n,
        0 <= p <= w.len(),
    ensures ({
        let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
        let w_prime = w.subrange(0, p) + pair + w.subrange(p, w.len() as int);
        is_base_word(w_prime, n)
    }),
{
    // Match the ensures exactly: use Seq::new form
    let pair = Seq::new(1, |_i: int| sym) + Seq::new(1, |_i: int| inverse_symbol(sym));
    let w_prime = w.subrange(0, p) + pair + w.subrange(p, w.len() as int);
    // Connect to seq![] form for lemma_stable_count_pair
    let pair_seq: Seq<Symbol> = seq![sym, inverse_symbol(sym)];
    assert(pair =~= pair_seq);
    lemma_stable_count_pair(sym, inverse_symbol(sym), n);
    // pair_seq has count 0, and pair =~= pair_seq, so pair has count 0
    assert(stable_letter_count(pair_seq, n) == 0nat);
    assert(stable_letter_count(pair, n) == 0nat);
    lemma_stable_letter_count_concat(w.subrange(0, p), pair, n);
    lemma_stable_letter_count_concat(w.subrange(0, p) + pair, w.subrange(p, w.len() as int), n);
    lemma_stable_letter_count_concat(w.subrange(0, p), w.subrange(p, w.len() as int), n);
    let left = w.subrange(0, p);
    let right = w.subrange(p, w.len() as int);
    assert(w =~= left + right);
    assert(stable_letter_count(w, n) == 0nat);
    // from concat lemma: count(left) + count(right) == count(left + right) == count(w) == 0
    assert(stable_letter_count(left + right, n) == 0nat);
    assert(stable_letter_count(left, n) + stable_letter_count(right, n) == 0nat);
    assert(stable_letter_count(left, n) + stable_letter_count(pair, n) ==
        stable_letter_count(left + pair, n));
    assert(stable_letter_count(left + pair, n) + stable_letter_count(right, n) ==
        stable_letter_count(w_prime, n));
    assert(stable_letter_count(w_prime, n) == 0nat);
}

} // verus!
