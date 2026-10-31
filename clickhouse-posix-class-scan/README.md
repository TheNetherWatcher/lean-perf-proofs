# clickhouse-posix-class-scan

Lean 4 proof that the faster `skipPosixNamedClass` in
[ClickHouse](https://github.com/ClickHouse/ClickHouse)'s regexp analyzer
(`src/Common/OptimizedRegularExpression.cpp`) returns exactly what the original
returns.

Check it (Lean core only, no Mathlib):

```sh
lean clickhouse-posix-class-scan/PosixClassProof.lean
```

## The change

Before building re2, ClickHouse analyzes each regexp to find a required
substring. Inside a character class, every `[:` might start a POSIX named class
like `[:alpha:]`, so the analyzer searched the rest of the pattern for `:]`.
When there is none, the search runs to the end every time, so a pattern with
many `[:` and no `:]` took quadratic time: 250,000 of them took 34 s
([#119581](https://github.com/ClickHouse/ClickHouse/issues/119581)).

The new code finds the last `:]` once (`rfind`) and skips the search for any
`[:` after it. The issue's pattern now takes 0.0002 s to analyze.

## What is proved

The regexp is a list of characters and pointers are indices.

- `skip_exact`: for any regexp and any position, the new function returns the
  same position as the old one, given any `last_close` that is the last `:]`.
- `skip_exact_rfind`: the same, as an equality of functions, with `last_close`
  computed by a recursive `rfind` (`lastClose_spec`). The analyzer only sees the
  regexp through these calls, so its result is unchanged.
- `scan_only_on_hit`: the new code runs the search only when it finds a `:]`
  at or before the last one. The analyzer then continues after that `:]`, so
  each character is searched at most once and analysis is linear.

No `sorry`; `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound`.

## What is not covered

The Lean model is transcribed by hand from the C++. The ties to the real code
are a 300,000-pattern old-vs-new comparison of the two C++ functions (0
mismatches) and a SQL test in the PR whose expected answers were checked
against re2.
