/-
  Exactness of the AVX512-VNNI micro-kernel for torchao's DA8W4 linear
  (int8 activations x int4 weights) on x86 CPUs without AMX.

  Machine values are modelled with Lean's `BitVec`, which has exactly the
  wrap-around semantics of the hardware:
  * a byte is `BitVec 8`; its unsigned value is `toNat`, signed is `toInt`
  * an int32 lane is `BitVec 32`; `+`, `-`, `*` wrap modulo 2^32

  `vpdpbusd acc, u, s` adds to each int32 lane the sum of four products
  (unsigned byte of u) * (signed byte of s), wrapping modulo 2^32.

  Main results
  * `asym_exact`: for uint8 activations a with zero point zp,
        acc - zp * comp   (int32, wrapping)
    equals the exact integer  Σ (a - zp) * b.
  * `sym_exact`: for int8 activations a fed to vpdpbusd as a ^ 0x80,
        acc - 128 * comp  (int32, wrapping)
    equals the exact integer  Σ a * b.
  Both need only |b| ≤ 15 (true for int4 weights minus an int4 zero point,
  `dequant_exact`) and K ≤ 2^15 terms (the kernel uses K ≤ 128 per call).
  So the int32 result handed to the float epilogue is the same integer the
  scalar reference loop computes.

  Core Lean 4 only, no Mathlib.
-/

namespace Vnni

/-! ## Bytes -/

/-- Flipping the sign bit of an int8 gives a uint8 equal to a + 128. -/
theorem xor_flip (a : BitVec 8) : ((a ^^^ 0x80#8).toNat : Int) = a.toInt + 128 := by
  revert a; decide

/-- Unpacking an int4 weight nibble w and subtracting an int4 zero point zp
    in wrapping int8 arithmetic (`_mm256_sub_epi8`) is exact. -/
theorem dequant_exact (w zp : BitVec 8) (hw : w.toNat < 16)
    (hz0 : 0 ≤ zp.toInt) (hz1 : zp.toInt < 16) :
    (w - zp).toInt = (w.toNat : Int) - zp.toInt ∧
    -15 ≤ (w - zp).toInt ∧ (w - zp).toInt ≤ 15 := by
  have hwi : w.toInt = (w.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have h : (w - zp).toInt = (w.toNat - zp.toInt : Int) := by
    rw [BitVec.toInt_sub, hwi]
    apply Int.bmod_eq_of_le <;> simp <;> omega
  refine ⟨h, ?_, ?_⟩ <;> omega

/-! ## int32 lanes -/

/-- Adding an exact integer into a wrapping int32 accumulator. -/
theorem toInt_add_ofInt (acc : BitVec 32) (x : Int) :
    (acc + BitVec.ofInt 32 x).toInt = (acc.toInt + x).bmod (2 ^ 32) := by
  rw [BitVec.toInt_add, BitVec.toInt_ofInt, Int.add_bmod_bmod]

/-- One vpdpbusd lane step: four (uint8 * int8) products, added with wrap. -/
def dpbusd (acc : BitVec 32) (q : List (Int × Int)) : BitVec 32 :=
  acc + BitVec.ofInt 32 (q.foldr (fun p s => p.1 * p.2 + s) 0)

def dot (l : List (Int × Int)) : Int := l.foldr (fun p s => p.1 * p.2 + s) 0

theorem dot_append (l m : List (Int × Int)) : dot (l ++ m) = dot l + dot m := by
  induction l with
  | nil => simp [dot]
  | cons p l ih => simp only [dot, List.cons_append, List.foldr_cons] at *; rw [ih]; omega

/-- The k-loop: one vpdpbusd per group of four k, starting from zero.
    `qs` is the list of 4-element groups; groups may be any length, the
    result only depends on the flattened list. -/
def kloop (qs : List (List (Int × Int))) : BitVec 32 :=
  qs.foldl dpbusd 0#32

theorem kloop_aux (qs : List (List (Int × Int))) (acc : BitVec 32) :
    (qs.foldl dpbusd acc).toInt = (acc.toInt + dot qs.flatten).bmod (2 ^ 32) := by
  induction qs generalizing acc with
  | nil =>
    simp only [List.foldl_nil, List.flatten_nil]
    rw [show dot [] = 0 from rfl, Int.add_zero]
    exact (BitVec.toInt_bmod_cancel acc).symm
  | cons q qs ih =>
    simp only [List.foldl_cons, List.flatten_cons]
    rw [ih, dpbusd, toInt_add_ofInt, Int.bmod_add_bmod, dot_append]
    simp only [dot]; rw [Int.add_assoc]

theorem kloop_toInt (qs : List (List (Int × Int))) :
    (kloop qs).toInt = (dot qs.flatten).bmod (2 ^ 32) := by
  rw [kloop, kloop_aux]; simp

/-- Epilogue: acc - zp * comp in wrapping int32 (`_mm512_mullo_epi32`,
    `_mm512_sub_epi32`). -/
def epilogue (acc : BitVec 32) (zp comp : BitVec 32) : BitVec 32 :=
  acc - zp * comp

theorem epilogue_toInt (qs : List (List (Int × Int))) (zp comp : BitVec 32) :
    (epilogue (kloop qs) zp comp).toInt
      = (dot qs.flatten - zp.toInt * comp.toInt).bmod (2 ^ 32) := by
  rw [epilogue, BitVec.toInt_sub, BitVec.toInt_mul, kloop_toInt,
    Int.sub_bmod_bmod, Int.bmod_sub_bmod]

/-! ## Bounds -/

/-- |x * y| ≤ X * Y from |x| ≤ X, |y| ≤ Y. -/
theorem natAbs_mul_le {x y : Int} {X Y : Nat} (hx : x.natAbs ≤ X) (hy : y.natAbs ≤ Y) :
    (x * y).natAbs ≤ X * Y := by
  rw [Int.natAbs_mul]; exact Nat.mul_le_mul hx hy

/-- A sum of n terms each of absolute value ≤ c has absolute value ≤ n * c. -/
theorem natAbs_sum_le (l : List Int) (c : Nat) (h : ∀ x ∈ l, x.natAbs ≤ c) :
    (l.foldr (· + ·) 0).natAbs ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldr_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    have := Int.natAbs_add_le x (l.foldr (· + ·) 0)
    rw [Nat.succ_mul]; omega

theorem dot_eq_sum (l : List (Int × Int)) :
    dot l = (l.map (fun p => p.1 * p.2)).foldr (· + ·) 0 := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [dot, List.foldr_cons, List.map_cons] at *; rw [ih]

theorem bmod_exact (x : Int) (h : x.natAbs < 2 ^ 31) : x.bmod (2 ^ 32) = x := by
  apply Int.bmod_eq_of_le <;> simp <;> omega

/-! ## Main theorems

  A row of A and a column of dequantized B are lists `a`, `b` of bytes
  (same length K). The kernel groups k by four; `qs` is any grouping
  whose flattening pairs a[k] with b[k] (as fed to vpdpbusd).
-/

/-- Exact Σ (x - z) * y over a zipped list. -/
def dotZ (z : Int) (l : List (Int × Int)) : Int := dot (l.map fun p => (p.1 - z, p.2))

/-- Σ (x - z) * y = Σ x * y - z * Σ y. -/
theorem dotZ_eq (z : Int) (l : List (Int × Int)) :
    dotZ z l = dot l - z * (l.map Prod.snd).foldr (· + ·) 0 := by
  induction l with
  | nil => simp [dotZ, dot]
  | cons p l ih =>
    simp only [dotZ, dot, List.map_cons, List.foldr_cons] at *
    rw [ih, Int.sub_mul, Int.mul_add]; omega

/-- Asymmetric (uint8) activations.
    `pairs` lists (a[k] as uint8, b[k] as int8) in k order; the kernel's
    groups `qs` flatten to it. `comp` holds Σ b (the prepacked
    compensation), `zp` the activation zero point. -/
theorem asym_exact (pairs : List (Int × Int)) (qs : List (List (Int × Int)))
    (hqs : qs.flatten = pairs)
    (zp comp : BitVec 32)
    (hcomp : comp.toInt = (pairs.map Prod.snd).foldr (· + ·) 0)
    (ha : ∀ p ∈ pairs, 0 ≤ p.1 ∧ p.1 ≤ 255)
    (hb : ∀ p ∈ pairs, -15 ≤ p.2 ∧ p.2 ≤ 15)
    (hz : 0 ≤ zp.toInt ∧ zp.toInt ≤ 255)
    (hK : pairs.length ≤ 2 ^ 15) :
    (epilogue (kloop qs) zp comp).toInt = dotZ zp.toInt pairs := by
  rw [epilogue_toInt, hqs, hcomp, ← dotZ_eq]
  apply bmod_exact
  have hbound := natAbs_sum_le
    ((pairs.map fun p => (p.1 - zp.toInt, p.2)).map fun p => p.1 * p.2) (255 * 15)
    (by
      intro x hx
      simp only [List.map_map, List.mem_map, Function.comp] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      have := ha p hp; have := hb p hp
      exact natAbs_mul_le (by omega) (by omega))
  rw [dotZ, dot_eq_sum]
  simp only [List.length_map] at hbound
  have : pairs.length * (255 * 15) < 2 ^ 31 := by omega
  omega

/-- Symmetric (int8) activations: the kernel feeds a ^ 0x80 (= a + 128 as
    uint8) to vpdpbusd and subtracts 128 * comp.
    `acts`/`ws` are the int8 activation bytes and int8 dequantized weights. -/
theorem sym_exact (acts ws : List (BitVec 8)) (hlen : acts.length = ws.length)
    (qs : List (List (Int × Int)))
    (hqs : qs.flatten =
      (acts.zip ws).map fun p => (((p.1 ^^^ 0x80#8).toNat : Int), p.2.toInt))
    (comp : BitVec 32)
    (hcomp : comp.toInt = (ws.map BitVec.toInt).foldr (· + ·) 0)
    (hb : ∀ w ∈ ws, -15 ≤ w.toInt ∧ w.toInt ≤ 15)
    (hK : acts.length ≤ 2 ^ 15) :
    (epilogue (kloop qs) 128#32 comp).toInt
      = dot ((acts.zip ws).map fun p => (p.1.toInt, p.2.toInt)) := by
  -- the kernel's pairs are the true pairs shifted by +128 in the first slot
  have hshift : (acts.zip ws).map (fun p => (((p.1 ^^^ 0x80#8).toNat : Int), p.2.toInt))
      = ((acts.zip ws).map fun p => (p.1.toInt + 128, p.2.toInt)) := by
    apply List.map_congr_left; intro p _; rw [xor_flip]
  have hsnd : (((acts.zip ws).map fun p => (p.1.toInt + 128, p.2.toInt)).map Prod.snd)
      = ws.map BitVec.toInt := by
    rw [List.map_map]
    have : (Prod.snd ∘ fun p : BitVec 8 × BitVec 8 => (p.1.toInt + 128, p.2.toInt))
        = BitVec.toInt ∘ Prod.snd := rfl
    rw [this, ← List.map_map, List.map_snd_zip (Nat.le_of_eq hlen.symm)]
  have h128 : (128#32).toInt = 128 := by decide
  have key := asym_exact
    ((acts.zip ws).map fun p => (p.1.toInt + 128, p.2.toInt)) qs
    (by rw [hqs, hshift]) 128#32 comp
    (by rw [hcomp, hsnd])
    (by
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨q, _, rfl⟩ := hp
      have := BitVec.toInt_le (x := q.1); have := BitVec.le_toInt q.1
      simp only at *; omega)
    (by
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact hb q.2 (List.of_mem_zip hq).2)
    (by rw [h128]; decide)
    (by simp only [List.length_map, List.length_zip]; omega)
  rw [key, h128, dotZ, List.map_map]
  congr 1
  apply List.map_congr_left; intro p _; simp

end Vnni

#print axioms Vnni.asym_exact
#print axioms Vnni.sym_exact
#print axioms Vnni.dequant_exact
