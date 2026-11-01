# pyteomics-coverage-mask

Lean 4 proof that the faster `parser.coverage_mask` in
[pyteomics](https://github.com/levitsky/pyteomics) returns exactly the mask the
original returns.

Check it (Lean core only, no Mathlib):

```sh
lean pyteomics-coverage-mask/CoverageProof.lean
```

## The change

`coverage_mask` found each peptide with `re.finditer(f'(?={peptide})', protein)`.
A lookahead pattern cannot use the regex engine's literal prefix search, so each
peptide cost a full regex scan of the protein. Each occurrence then added 1 over
its slice of the mask.

The new code finds the same overlapping occurrences with
`protein.find(peptide, i + 1)`, records +1 where an occurrence starts and -1 where
it ends, and takes the running sum (`np.cumsum`). On a 35,000-residue protein:

| Peptides | Before | After |
|---|---|---|
| 2,000 | 0.42 s | 0.023 s |
| 4,606 | 0.98 s | 0.054 s |

## What is proved

Sequences are lists of characters. The original lookahead is modelled as trying
every position from 0 to `len(protein)` and keeping those where the peptide occurs
(`occOld`). Python's `str.find` is modelled as returning the first occurrence at or
after a start (`find`).

- `occ_exact`: for any non-empty peptide, the `find` loop yields exactly the
  lookahead positions, in the same order.
- `mask_exact`: for any protein, any list of peptides (empty ones included) and
  any residue `k`, the running sum of the new +1/-1 array at `k` equals the
  original mask at `k`: the number of occurrences covering `k`.

No `sorry`; `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound`.

## What is not covered

The lookahead model holds for peptides of plain letters, which is what the
function documents (`fast=True` assumes one-letter uppercase sequences;
`fast=False` strips them to that). A peptide holding regex metacharacters was
matched as a pattern before and is matched literally now.

The Lean model is transcribed by hand from the Python. The ties to the real code
are a 200,000-case old-vs-new comparison (random proteins over 2-, 3- and 20-letter
alphabets, overlapping, repeated, missing and empty peptides; identical values and
dtype, and an injected bug is caught) and the regression tests in the PR.
