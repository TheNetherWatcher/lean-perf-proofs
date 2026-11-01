# pretty-midi-instrument

Lean 4 proof that the faster `Instrument.remove_invalid_notes` and
`Instrument.synthesize` in [pretty-midi](https://github.com/craffel/pretty-midi)
give exactly what the originals gave.

Check it (Lean core only, no Mathlib):

```sh
lean pretty-midi-instrument/InstrumentProof.lean
```

## The change

`remove_invalid_notes` collected the notes with `end <= start` and then called
`self.notes.remove(note)` for each one. Every `remove` scans the list from the
front, so cleaning up many short notes was quadratic. It now keeps the valid
notes in one pass and assigns them back into the same list object.

`synthesize` checked every pitch bend against every note to find the bends that
fall inside the note. It now builds the sorted list of bend positions once and
picks each note's bends with `bisect`.

| Case | Before | After |
|---|---|---|
| `remove_invalid_notes`, 20,000 notes (half invalid) | 0.22 s | 0.0005 s |
| `remove_invalid_notes`, 80,000 notes (half invalid) | 3.49 s | 0.0018 s |
| `synthesize`, 2,000 notes, 5,000 bends, fs 8 kHz | 0.45 s | 0.11 s |
| `synthesize`, 5,000 notes, 20,000 bends, fs 8 kHz | 4.10 s | 0.75 s |

## What is proved

- `remove_exact`: for any list and any invalid-note test, erasing each invalid
  element in turn (as `list.remove` does, by identity, first match) gives the
  list of valid elements in their original order. This includes a note object
  that appears in the list more than once.
- `synth_bends_exact`: for a sorted list of bend sample positions and any note
  `start`/`end`, the slice between `bisect_right(start)` and
  `bisect_left(end)` is exactly the list of positions with
  `start < b < end`, in the same order, including when `end <= start`. The
  loop body is unchanged, so the same positions in the same order give the same
  waveform.

No `sorry`; `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound`.

## What is modelled

Python's `bisect_right`/`bisect_left` are modelled by what they return on a
sorted list: the number of leading elements `<= x` or `< x`. The bend
positions are `int(bend.time * fs)` over bends already sorted by time; that
map never decreases, so the list is sorted, which is the proof's hypothesis.

The Lean model is transcribed by hand from the Python. The ties to the real
code are a 20,000-case old-vs-new comparison (random notes including zero and
negative durations and repeated note objects, random bends including ones
exactly at note boundaries, several sample rates; identical arrays and dtype,
same exceptions) that catches injected bugs, and the tests in the PR.
