# pyannote-core-sweep

Lean 4 proof that the sweep-line rewrites of `pyannote.core`'s
`Timeline.co_iter` and `Timeline.segmentation` return exactly what the
original nested loops return: same pairs, same order.

Check it (Lean core only, no Mathlib):

```sh
lean pyannote-core-sweep/SweepProof.lean
```

## What is proved

- `sweep_eq_naive`: generic. If `other` is sorted, `bound s` is closed
  downwards under that order, and a candidate that neither intersects `s`
  nor starts at or after it can never intersect a later segment, then the
  sweep equals the nested loop.
- `drop_ok`: that last property holds for pyannote's real
  `Segment.intersects`, for *any* value of `end - SEGMENT_PRECISION`
  (so float rounding cannot break it).
- `co_iter_exact`: the two combined, with Python's tuple ordering for
  `Segment.__le__`.
- `segmentation_exact`: the running-maximum sweep in `segmentation`
  answers exactly what `support.overlapping(middle)` answers.

## Modelling assumptions

- Times compare like non-NaN Python floats: `<=` is a total preorder,
  `a < b` is `not (b <= a)`, `a == b` is `a <= b and b <= a`.
- `SortedList` contents are sorted by `Segment.__le__`.
- `Segment(t, t)` (with optional rounding) is monotone in `t`, and
  segment middles are visited in nondecreasing order.
- `-math.inf` is modelled as "no maximum yet".

`#print axioms` reports only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); there is no `sorry`.
