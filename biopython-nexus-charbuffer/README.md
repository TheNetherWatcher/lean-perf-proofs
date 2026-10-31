# biopython-nexus-charbuffer

Lean 4 proof that the faster `CharBuffer` in
[Biopython](https://github.com/biopython/biopython)'s `Bio.Nexus.Nexus` returns
exactly the same results as the original.

Check it (Lean core only, no Mathlib):

```sh
lean biopython-nexus-charbuffer/CharBufferProof.lean
```

## The change

`CharBuffer` tokenizes NEXUS commands. The original kept the unread input as a
list of characters and read by `buffer.pop(0)`; `peek_nonwhitespace` also
rebuilt the whole remaining string with `"".join(...).strip()` on every call.
Each read cost O(n), so a command of length n took O(n²). The new version keeps
the text and an integer read position.

For a 16,000-entry charset, parsing drops from 1.9 s to 0.018 s; a 16,000-entry
`TRANSLATE` block from 4.4 s to 0.041 s.

## What is proved

The invariant is `old buffer = text.drop pos`. For each primitive
(`peek`, `__next__`, `peek_nonwhitespace`, `skip_whitespace`, `next_until`,
`peek_word`, `rest`) the new code returns the same value as the old one and
keeps the invariant, including the `IndexError` of `skip_whitespace` on an
empty buffer. `next_word` and `next_nonwhitespace` are unchanged and only call
these primitives.

- `run_exact`: any sequence of calls gives the same outputs on both versions.
- `strip_head`: the first character of `str.strip()` is the first
  non-whitespace character, so the new scan matches `"".join(buf).strip()[0]`.
- `findFrom_spec`, `until_exact`: `str.find(c, pos)` plus a slice matches
  `list.index` plus a split.

Characters are an arbitrary type and the whitespace tests are arbitrary
predicates, so the result does not depend on which characters count as
whitespace. Python strings are modelled as lists of characters.
