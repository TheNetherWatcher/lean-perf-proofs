# natural-levenshtein

Lean 4 proofs for the plain Levenshtein and spellcheck loop changes in
[NaturalNode/natural PR #798](https://github.com/NaturalNode/natural/pull/798).

Check it (Lean core only, no Mathlib):

```sh
export PATH="$HOME/.elan/bin:$PATH"
lean natural-levenshtein/NaturalLevenshteinProof.lean
```

## What is proved

Strings are lists of character elements. `initialRow` builds row zero by repeated
addition of the insertion cost. `oldCells` builds each matrix row from the row
above and the current row's left cell. `fullMatrix` retains every row;
`twoRows` retains only the latest row. The three candidates are passed to the
same `min3` function in insertion, deletion, substitution order. No order,
associativity, or commutativity law is required of `min3` or addition.

- `row_equal`: each new row equals the corresponding old row for any costs and
  any `min3`.
- `rows_equal`: the final retained row equals the final row of the full matrix.
- `levenshtein_exact`: the final cell is identical for all source and target
  lists.
- `spellcheck_dedupe_exact`: filtering at positions where `indexOf` returns the
  current index equals insertion-order Set deduplication for every input list.
- `spellcheck_concat_exact`: folding `concat` over edit batches yields the same
  list as pushing each element of each batch, for every starting list and batch
  list. The order and duplicates are preserved.

No algebraic law is needed for `min3` or addition: both versions compute the
same candidate values with the same operations and pass them to `min3` in the
same order; only which rows are kept differs. So for the PR's guarded fast path
(string inputs, finite numeric costs) the distances are bit-identical, given
that `Math.min` and lodash's `_.min` return the same value for three finite
numbers.

No `sorry` or new axioms; `#print axioms` for each main theorem shows only
`propext`, `Classical.choice`, and `Quot.sound` or fewer.

## What is modelled by hand

The Lean lists correspond to JS string index elements (UTF-16 code units in
the implementation). The original matrix's parent pointers, search, and
Damerau branches are excluded because the fast path handles plain Levenshtein
distance only. `getD` supplies a fallback for malformed rows; the constructed
rows have the expected lengths, so the normal recurrence reads populated cells.

`min3` represents both the old `_.min` selection and new `Math.min` on the
three costs. Their behavior differs for NaN, so the theorem does not equate
those JS functions for arbitrary values. The PR's fast-path guard requires
string inputs, disables search and Damerau, requires numeric costs, and bounds
their absolute values by `Number.MAX_VALUE / (sourceLength + targetLength + 1)`.
The numeric bound rejects NaN and infinities and keeps accumulated costs finite.
The Lean proof does not verify the JS guard or IEEE-754 rules.

For spellcheck, `indexOf`, `indexFilter`, `setDedupe`, `concatEdits`, and
`pushEdits` transcribe the relevant list operations. The proof assumes equality
on list elements matches JS string equality; it does not model edit generation,
dictionary lookups, or timing.
