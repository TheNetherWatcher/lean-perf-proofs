# utf8h-ascii-fast-path

Lean 4 proof that the ASCII fast paths added to
[utf8.h](https://github.com/sheredom/utf8.h) return exactly what the original
functions return.

Check it (Lean core only, no Mathlib):

```sh
lean utf8h-ascii-fast-path/Utf8AsciiProof.lean
```

## The change

utf8.h decoded every byte as a full codepoint, even plain ASCII. ASCII bytes are
always whole codepoints, and the case mappings only change `A-Z` and `a-z` among
them. So runs of ASCII can skip decoding. On 16 MB of ASCII text (`-O2`, Apple M4 Pro):

| Function | Before | After |
|---|---|---|
| `utf8casestr` (no match) | 0.13 GB/s | 2.98 GB/s |
| `utf8casecmp` (equal) | 0.09 GB/s | 1.69 GB/s |
| `utf8lwr` / `utf8upr` | 0.25 GB/s | 3.7 GB/s |
| `utf8str` / `utf8chr` (no match) | 0.53 GB/s | 4.1 GB/s |
| `utf8valid` | 1.02 GB/s | 3.86 GB/s |
| `utf8len` | 1.28 GB/s | 4.02 GB/s |

## What is proved

Strings are lists of bytes; reading past the end reads the NUL terminator.
`utf8codepoint` is modelled exactly (`dec`), and `dec_ascii` shows an ASCII byte
decodes to itself and advances by one.

- `utf8str_exact`: the new `utf8str` returns the same index (or no match) for
  every haystack and needle. `utf8chr` builds a needle and calls `utf8str`.
- `utf8casestr_exact`: the same for `utf8casestr`.
- `utf8casecmp_exact`: the new loop returns the same value as the old one, pass
  for pass.
- `utf8nlen_exact`: the same count for every string and byte limit `n`
  (`utf8len` is `utf8nlen` with `SIZE_MAX`).
- `ascii_not_lead`: `utf8nvalid` now tests for ASCII first; no ASCII byte
  passes a multi-byte lead test, so each byte takes the same branch as before.
- `utf8lwr_exact` / `utf8upr_exact`: the same buffer after the call.
  `lower_fast_form` / `upper_fast_form` show the C's `c + 32` / `c - 32` writes are
  the same as writing the mapped codepoint.

No `sorry`; `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound`.

## What is assumed

`utf8lwrcodepoint` and `utf8uprcodepoint` are parameters. The only fact used is
how they treat ASCII: `A-Z` and `a-z` swap and everything else stays the same.
The PR adds a test that checks this for all 128 values. `utf8catcodepoint` is a
parameter too, assumed to write one byte for an ASCII codepoint.

## What is not covered

The Lean model is transcribed by hand from the C. The ties to the real code are
a 1.5M-case old-vs-new differential fuzz per function group (random strings with
invalid UTF-8, truncated sequences, NULs and byte limits; 0 mismatches, and
injected bugs are caught) and the repo's test suite.
