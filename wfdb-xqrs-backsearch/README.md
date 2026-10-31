# wfdb-xqrs-backsearch

Lean 4 proof that skipping already-rejected peaks in the XQRS backsearch of
[wfdb-python](https://github.com/MIT-LCP/wfdb-python) leaves the detector in exactly
the same state after every peak as the original code.

Check it (Lean core only, no Mathlib):

```sh
lean wfdb-xqrs-backsearch/BacksearchProof.lean
```

## The change

The original `_backsearch` rescans `range(last_qrs_peak_num + 1, peak_num + 1)` every
time it runs. If it finds nothing, `last_qrs_peak_num` does not move, so a long
stretch without QRS complexes is rescanned at every peak (quadratic). The new code
remembers the last peak a backsearch checked and starts after
`max(last_qrs_peak_num, last_checked)`.

## What is proved

The detector state is an abstract type. `run_exact` says that for any number of peaks,
the new loop and the old loop end in the same state, assuming three facts about the
code:

1. `_update_qrs` sets `last_qrs_peak_num` to the current peak (`upd_last`).
2. `_update_noise` does not change `last_qrs_peak_num` (`noise_last`).
3. `_update_noise` does not change the backsearch check (`noise_bs`). The check reads
   `qrs_thr`, `last_qrs_ind`, the configuration and the signal, none of which
   `_update_noise` touches.

The main and backsearch checks, `_require_backsearch` and the updates are otherwise
arbitrary functions, so nothing depends on the float arithmetic.

Helper results: `scan_false` (scanning rejected peaks changes nothing), `scan_cases`
(a scan either changes nothing or ends with `last_qrs_peak_num` at the current peak),
`step_exact` (one peak, with the invariant that every peak between the last QRS and
the skip point was rejected).

No `sorry`; `#print axioms run_exact` shows only `propext`, `Classical.choice` and
`Quot.sound`.

## What is not covered

The model is written by hand from the Python code, so the three facts above are
checked by reading the code, and the tie to the real implementation is the test and
the old-vs-new comparison in the PR.
