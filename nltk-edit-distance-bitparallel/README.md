# nltk-edit-distance-bitparallel

Lean 4 proof for the `edit_distance` unit-cost fast path in
[nltk/nltk#4017](https://github.com/nltk/nltk/pull/4017). The old path is
NLTK's DP table (`_edit_dist_init` + `_edit_dist_step` with
`substitution_cost=1`, `transpositions=False`). The new path,
`_edit_distance_bitparallel`, is the Myers (1999) / Hyyrö (2003) bit-parallel
loop on Python's unbounded integers.

**The equivalence is unconditional.** For every element type with decidable
equality, every nonempty `s1` and every `s2`, the transcribed Python loop
returns exactly the DP table's `lev[len(s1)][len(s2)]`. No hypotheses, no
`sorry`, no new axioms.

## What is proved

Main results:

- `bitparallel_eq_dp`: `bitparallel xs ys = some (dp xs ys)` whenever
  `xs ≠ []`.
- `dispatch_eq_dp`: the `edit_distance` dispatch returns the DP value whether
  the helper is skipped (the guard is off), returns `None`, or returns its
  result. `dispatch_fallback` covers the first two cases.

Steps along the way:

- `column_step`: one loop iteration takes masks that encode DP column `j` to
  masks that encode column `j+1`. The distance moves from the last cell of one
  column to the last cell of the next. This is the Myers/Hyyrö column lemma,
  built from these pieces:
  - `cell`: Myers' cell lemma. Given vertical and horizontal deltas in
    {-1, 0, +1} and the `min` recurrence, Hyyrö's `Ph`, `Mh`, `Pv'` and
    `Mv'` formulas give the outgoing deltas, and those stay in {-1, 0, +1}.
  - `testBit_add`, `carry_succ`: bit `i` of `a + b` is
    `a_i xor b_i xor carry_i`, and the carry propagates by majority.
  - `horizontal_bit`, `carry_mh`: bit `i` of
    `(((Eq & Pv) + Pv) ^ Pv) | Eq` is `Eq_i | carry_i`, and the carry into bit
    `i` is the shifted `Mh` bit. This is the sequential `Xh` recurrence that
    the addition computes all at once.
  - `step_positive_bit`, `step_negative_bit`, `step_distance`: the bits of
    the masks after one step, including `(Ph << 1) | 1` and the high-bit
    distance update.
- `initial_invariant`, `run_invariant`: `Pv = ~0`, `Mv = 0`,
  `distance = len(s1)` encode column 0. By induction over `s2`, the final state
  encodes the last column.
- `step_low`, `run_low`: the transcribed Python loop on `Int` (`pyStep`,
  `pyRun`) agrees with its low-`len(s1)+1`-bit image (`step`, `run`) after
  every iteration. Supporting lemmas: `low_and`, `low_or`, `low_xor`,
  `low_not`, `low_add`, `low_shift_one`, and `and_high_ne_zero` (Python's
  `if x & high_bit:` tests two's-complement bit `len(s1)-1`). Negative
  operands are included; `~0` is `-1`.
- `peq_bit`: each equality-mask bit is set exactly at an equal source token.

## What is modelled by hand

- **Python's loop.** `pyStep` is a line-by-line transcription of the loop
  body, in the PR's order: `vertical`, `horizontal`, `positive_shift`,
  `negative_shift`, the two high-bit distance updates,
  `(positive_shift << 1) | 1`, `negative_shift <<= 1`, then the new `positive`
  and `negative`. `pyInit` is `positive = ~0`, `negative = 0`,
  `distance = width`. `bitparallel` returns `None` for empty `s1` and the final
  distance otherwise. (`matches` is a Lean keyword, so the Lean name is
  `eqMask`.)
- **Python's `&`, `|`, `^` on `int`.** Lean core has `~~~`, `<<<` and `+` on
  `Int` but not `&`, `|`, `^`. `iand`, `ior` and `ixor` use the standard
  two's-complement case split (the same as Mathlib's `Int.land`, `Int.lor`,
  `Int.xor`). `ibit_and`, `ibit_or`, `ibit_xor` and `ibit_not` prove that they
  act bit by bit on the infinite two's-complement expansion. `ibit_inj` proves
  that this expansion determines the integer, so these operations are the only
  ones with that behaviour, which is Python's.
- **The DP.** `lev xs ys i j` is NLTK's `lev[i][j]`. Row 0 and column 0 hold
  their index, and every other cell is `min(a, b, c)` in
  `_edit_dist_step`'s order. The transposition candidate `d = c + 1` is never
  the minimum when `transpositions=False`, so it is left out. `dp` is
  `lev[len1][len2]`. The model covers the table's values, not its list-of-lists
  storage.
- **Tokens and equality.** Sequences are `List α` with `DecidableEq α`. The
  same equality drives `peq` (Python's dict lookup) and the DP's `c1 != c2`.
  The model leaves out Python hashing, the `TypeError`/NaN checks that return
  `None`, and the substitution-cost/transposition guard. In `dispatch`, the
  guard is the Boolean `enabled` and the helper's result is an `Option`
  argument. `dispatch_eq_dp` takes that argument to be either `none` or
  `bitparallel xs ys`.

## Check

From the repository root:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lean nltk-edit-distance-bitparallel/NltkMyersProof.lean
./check.sh
```

The `#print axioms` lines at the end of the file report only `propext`,
`Classical.choice` and `Quot.sound`.
