# torchao-da8w4-vnni

Lean 4 proof that the AVX512-VNNI micro-kernel for torchao's DA8W4 linear
(int8 activations, int4 weights) on x86 CPUs without AMX produces exactly
the integer the scalar reference loop produces, including the int32
wrap-around of the hardware.

Check it (Lean core only, no Mathlib):

```sh
lean torchao-da8w4-vnni/VnniProof.lean
```

## What is proved

Machine values are Lean `BitVec`s, which wrap exactly like the hardware:
bytes are `BitVec 8`, int32 lanes are `BitVec 32`.

- `xor_flip`: for any int8 byte `a`, `a ^ 0x80` read as uint8 is `a + 128`.
  This lets `vpdpbusd` (uint8 x int8 only) handle signed activations.
- `dequant_exact`: unpacking an int4 nibble and subtracting an int4 zero
  point in wrapping int8 arithmetic is exact and lands in `[-15, 15]`.
- `kloop_toInt`: a chain of `vpdpbusd` steps over any grouping of the k
  axis equals the exact dot product modulo 2^32.
- `asym_exact`: uint8 activations with zero point `zp`:
  `acc - zp * comp` in wrapping int32 equals the exact `Σ (a - zp) * b`.
- `sym_exact`: int8 activations fed as `a ^ 0x80`:
  `acc - 128 * comp` in wrapping int32 equals the exact `Σ a * b`.

Both main theorems need `|b| <= 15` and at most 2^15 terms along k
(the kernel uses at most 128 per call), so the true value fits in int32 and
the wrapped result is the true value.

## Modelling assumptions

- `vpdpbusd` adds the sum of its four uint8 x int8 products to each lane
  modulo 2^32 (Intel SDM). The products fit in 16 bits, so the order of the
  four additions does not matter.
- `comp` is the prepacked compensation `Σ_k b[k]`, computed in int32 by
  the prepack step.
- Only the integer part is proved. The float epilogue
  (`cvt(int32) * scale_a * scale_b + C`) is the same sequence of IEEE
  operations as the reference, so it receives the same integer.

Axioms: `propext`, `Classical.choice`, `Quot.sound` (Lean's standard ones);
no `sorry`.
