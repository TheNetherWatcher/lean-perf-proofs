/-!
# NLTK unit-cost edit distance: Myers bit-parallel loop

Proof that `_edit_distance_bitparallel` from nltk/nltk#4017 returns the
unit-cost Levenshtein table value `lev[len(s1)][len(s2)]` for every nonempty
`s1`. `pyStep` transcribes the Python loop body on unbounded `Int`s; `step`
is its image on the low `len(s1)+1` bits, and `column_step` is the Myers /
Hyyrö column lemma. No premises, no `sorry`.
-/

namespace NltkMyers

/-! ## The DP table (`_edit_dist_init` + `_edit_dist_step`, unit cost, no
transpositions) -/

/-- `lev xs ys i j` is `lev[i][j]`: row 0 and column 0 are initialised to the
index, every other cell is `min(a, b, c)` as in `_edit_dist_step`. -/
def lev [DecidableEq α] (xs ys : List α) : Nat → Nat → Nat
  | 0, j => j
  | i + 1, 0 => i + 1
  | i + 1, j + 1 =>
      min (min (lev xs ys i (j + 1) + 1) (lev xs ys (i + 1) j + 1))
        (lev xs ys i j + if xs[i]? = ys[j]? then 0 else 1)

/-- The DP result `lev[len1][len2]`. -/
def dp [DecidableEq α] (xs ys : List α) : Nat := lev xs ys xs.length ys.length

theorem lev_zero_left [DecidableEq α] (xs ys : List α) (j : Nat) :
    lev xs ys 0 j = j := by
  simp [lev]

theorem lev_zero_right [DecidableEq α] (xs ys : List α) (i : Nat) :
    lev xs ys i 0 = i := by
  cases i <;> simp [lev]

theorem lev_succ_succ [DecidableEq α] (xs ys : List α) (i j : Nat) :
    lev xs ys (i + 1) (j + 1) =
      min (min (lev xs ys i (j + 1) + 1) (lev xs ys (i + 1) j + 1))
        (lev xs ys i j + if xs[i]? = ys[j]? then 0 else 1) := by
  simp [lev]

/-! ## Equality masks -/

/-- Python `peq.get(element, 0)`: a bit is set at every equal source token. -/
def peqFrom [DecidableEq α] : List α → Nat → α → Nat
  | [], _, _ => 0
  | x :: xs, i, c => (if x = c then 2^i else 0) ||| peqFrom xs (i + 1) c

def peq [DecidableEq α] (xs : List α) (c : α) : Nat := peqFrom xs 0 c

/-- Every bit below the starting offset is clear. -/
theorem peqFrom_below [DecidableEq α] (xs : List α) (base j : Nat)
    (h : j < base) (c : α) : (peqFrom xs base c).testBit j = false := by
  induction xs generalizing base with
  | nil => simp [peqFrom]
  | cons x xs ih =>
      simp only [peqFrom, Nat.testBit_or]
      have hne : base ≠ j := by omega
      rw [ih (base + 1) (by omega)]
      split <;> simp [hne]

/-- `peq` has the same low-bit membership test as Python's dictionary mask. -/
theorem peqFrom_bit [DecidableEq α] (xs : List α) (base j : Nat)
    (c : α) :
    (peqFrom xs base c).testBit (base + j) =
      decide (xs[j]? = some c) := by
  induction xs generalizing base j with
  | nil => simp [peqFrom]
  | cons x xs ih =>
      cases j with
      | zero =>
          simp only [peqFrom, Nat.testBit_or, Nat.add_zero]
          rw [peqFrom_below xs (base + 1) base (by omega) c]
          split <;> simp [*]
      | succ j =>
          simp only [peqFrom, Nat.testBit_or]
          have hne : base ≠ base + (j + 1) := by omega
          have heq : base + (j + 1) = base + 1 + j := by omega
          rw [heq, ih (base + 1) j]
          split <;> simp [show base ≠ base + 1 + j by omega]

theorem peq_bit [DecidableEq α] (xs : List α) (j : Nat) (c : α) :
    (peq xs c).testBit j = decide (xs[j]? = some c) := by
  simpa [peq] using peqFrom_bit xs 0 j c

/-! ## Python integers

Lean core has `~~~`, `<<<` and `+` on `Int` but no `&`, `|`, `^`. The three
definitions below are the usual two's-complement ones (Mathlib's `Int.land`,
`Int.lor`, `Int.xor`). `low w x` is `x mod 2^w`, i.e. the low `w` bits. -/

/-- The low `width` bits of a Python integer. -/
def low (width : Nat) (x : Int) : Nat := (x % (2^width : Nat)).toNat

/-- Python's `&` on unbounded integers (two's complement); same case split
as Mathlib's `Int.land`, with `ldiff m n` written `m ^^^ (m &&& n)`. -/
def iand : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .ofNat m, .negSucc n => .ofNat (m ^^^ (m &&& n))
  | .negSucc m, .ofNat n => .ofNat (n ^^^ (n &&& m))
  | .negSucc m, .negSucc n => .negSucc (m ||| n)

def ior : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ||| n)
  | .ofNat m, .negSucc n => .negSucc (n ^^^ (n &&& m))
  | .negSucc m, .ofNat n => .negSucc (m ^^^ (m &&& n))
  | .negSucc m, .negSucc n => .negSucc (m &&& n)

def ixor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ^^^ n)
  | .ofNat m, .negSucc n => .negSucc (m ^^^ n)
  | .negSucc m, .ofNat n => .negSucc (m ^^^ n)
  | .negSucc m, .negSucc n => .ofNat (m ^^^ n)

instance : AndOp Int := ⟨iand⟩
instance : OrOp Int := ⟨ior⟩
instance : XorOp Int := ⟨ixor⟩

/-- Bit `i` of an unbounded two's-complement integer. -/
def ibit : Int → Nat → Bool
  | .ofNat n, i => n.testBit i
  | .negSucc n, i => !n.testBit i

/-- Two's complement is faithful: an `Int` is determined by its bits, so the
`ibit_*` lemmas below pin `&`, `|`, `^` down uniquely. -/
theorem ibit_inj (x y : Int) (h : ∀ i, ibit x i = ibit y i) : x = y := by
  have big : ∀ m n : Nat, ¬ ∀ i, m.testBit i = !n.testBit i := by
    intro m n hmn
    have h1 := hmn (m + n)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right
      (by decide) (Nat.le_add_right m n))), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
      (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) (Nat.le_add_left n m)))] at h1
    simp at h1
  cases x <;> cases y <;> simp only [ibit] at h
  · exact congrArg _ (Nat.eq_of_testBit_eq h)
  · exact absurd h (big _ _)
  · exact absurd (fun i => (h i).symm) (big _ _)
  · exact congrArg _ (Nat.eq_of_testBit_eq (fun i => by simpa using h i))

theorem low_ofNat (width n : Nat) : low width (.ofNat n) = n % 2^width := rfl

theorem low_negSucc (width n : Nat) :
    low width (.negSucc n) = 2^width - 1 - n % 2^width := by
  have hp : 0 < 2^width := Nat.pow_pos (by decide)
  unfold low
  rw [Int.negSucc_emod n (by exact_mod_cast hp)]
  have := Nat.mod_lt n hp
  omega

theorem low_testBit (width i : Nat) (x : Int) :
    (low width x).testBit i = (decide (i < width) && ibit x i) := by
  cases x with
  | ofNat n => rw [low_ofNat, Nat.testBit_mod_two_pow]; rfl
  | negSucc n =>
    have key : 2^width - 1 - n % 2^width = (~~~(BitVec.ofNat width n)).toNat := by
      simp [BitVec.toNat_not]
    rw [low_negSucc, key, BitVec.testBit_toNat, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, ibit]
    cases decide (i < width) <;> rfl

theorem low_testBit_lt (width i : Nat) (x : Int) (hi : i < width) :
    (low width x).testBit i = ibit x i := by
  rw [low_testBit]; simp [hi]

theorem ibit_and (x y : Int) (i : Nat) : ibit (x &&& y) i = (ibit x i && ibit y i) := by
  change ibit (iand x y) i = _
  cases x <;> cases y <;>
    simp only [iand, ibit, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or] <;>
    cases Nat.testBit _ i <;> cases Nat.testBit _ i <;> rfl

theorem ibit_or (x y : Int) (i : Nat) : ibit (x ||| y) i = (ibit x i || ibit y i) := by
  change ibit (ior x y) i = _
  cases x <;> cases y <;>
    simp only [ior, ibit, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or] <;>
    cases Nat.testBit _ i <;> cases Nat.testBit _ i <;> rfl

theorem ibit_xor (x y : Int) (i : Nat) : ibit (x ^^^ y) i = (ibit x i ^^ ibit y i) := by
  change ibit (ixor x y) i = _
  cases x <;> cases y <;> simp only [ixor, ibit, Nat.testBit_xor] <;>
    cases Nat.testBit _ i <;> cases Nat.testBit _ i <;> rfl

theorem ibit_not (x : Int) (i : Nat) : ibit (~~~x) i = !ibit x i := by
  cases x <;> simp [ibit, Complement.complement, Int.not]

/-- `~x` on the retained bits. -/
def bnot (width x : Nat) : Nat := (2^width - 1) ^^^ x

theorem bnot_bit (width x i : Nat) (hi : i < width) :
    (bnot width x).testBit i = !(x.testBit i) := by
  simp [bnot, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hi]

theorem low_and (w : Nat) (x y : Int) : low w (x &&& y) = low w x &&& low w y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [low_testBit, Nat.testBit_and, ibit_and]
  cases decide (i < w) <;> simp

theorem low_or (w : Nat) (x y : Int) : low w (x ||| y) = low w x ||| low w y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [low_testBit, Nat.testBit_or, ibit_or]
  cases decide (i < w) <;> simp

theorem low_xor (w : Nat) (x y : Int) : low w (x ^^^ y) = low w x ^^^ low w y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [low_testBit, Nat.testBit_xor, ibit_xor]
  cases decide (i < w) <;> simp

theorem low_not (w : Nat) (x : Int) : low w (~~~x) = bnot w (low w x) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [bnot, low_testBit, Nat.testBit_xor, ibit_not, Nat.testBit_two_pow_sub_one]
  cases decide (i < w) <;> simp

theorem low_natCast (w n : Nat) : low w (n : Int) = n % 2^w := rfl

theorem low_one (w : Nat) : low w (1 : Int) = 1 % 2^w := rfl

theorem ne_zero_iff_of_bits (v k : Nat) (b : Bool)
    (h : ∀ i, v.testBit i = (b && decide (k = i))) : v ≠ 0 ↔ b = true := by
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hv
    rw [h] at hi
    simp at hi; exact hi.1
  · intro hb hv
    have := h k
    rw [hv, hb] at this
    simp at this

/-- Python's `if x & (1 << k):` tests two's-complement bit `k`. -/
theorem and_high_ne_zero (x : Int) (k : Nat) :
    (x &&& ((1 : Int) <<< k) ≠ 0) ↔ ibit x k = true := by
  have h1 : ((1 : Int) <<< k) = .ofNat (2^k) := by
    change Int.ofNat (1 <<< k) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hz : ∀ v : Nat, (Int.ofNat v ≠ 0 ↔ v ≠ 0) := fun v => by
    rw [show Int.ofNat v = (v : Int) from rfl]; omega
  rw [h1]
  change iand x _ ≠ 0 ↔ _
  cases x with
  | ofNat n =>
    rw [iand, ibit, hz]
    refine ne_zero_iff_of_bits _ k _ (fun i => ?_)
    simp only [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hk : k = i <;> simp [hk]
  | negSucc n =>
    rw [iand, ibit, hz]
    refine ne_zero_iff_of_bits _ k _ (fun i => ?_)
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hk : k = i <;> simp [hk]

theorem low_not_zero (width : Nat) : low width (~~~(0 : Int)) = 2^width - 1 := by
  have hp : 0 < 2^width := Nat.pow_pos (by decide)
  change ((-1 : Int) % (2^width : Nat)).toNat = 2^width - 1
  rw [show (-1 : Int) = Int.negSucc 0 by rfl,
    Int.negSucc_emod 0 (by exact_mod_cast hp)]
  simp [-Int.natCast_pow]

/-- Reduction after addition retains exactly the low bits of Python's
unbounded integer addition, including when either operand is negative. -/
theorem low_add (width : Nat) (x y : Int) :
    low width (x + y) = (low width x + low width y) % 2^width := by
  have hp : 0 < ((2^width : Nat) : Int) := by
    exact_mod_cast Nat.pow_pos (by decide : 0 < (2 : Nat))
  have hx : 0 ≤ x % ((2^width : Nat) : Int) := Int.emod_nonneg x (by omega)
  have hy : 0 ≤ y % ((2^width : Nat) : Int) := Int.emod_nonneg y (by omega)
  unfold low
  rw [Int.add_emod, Int.toNat_emod (by omega) (by omega)]
  rw [Int.toNat_add hx hy]
  simp [-Int.natCast_pow]

theorem low_mul (width : Nat) (x y : Int) :
    low width (x * y) = (low width x * low width y) % 2^width := by
  have hp : 0 < ((2^width : Nat) : Int) := by
    exact_mod_cast Nat.pow_pos (by decide : 0 < (2 : Nat))
  have hx : 0 ≤ x % ((2^width : Nat) : Int) := Int.emod_nonneg x (by omega)
  have hy : 0 ≤ y % ((2^width : Nat) : Int) := Int.emod_nonneg y (by omega)
  have hxy : 0 ≤ (x % ((2^width : Nat) : Int)) * (y % ((2^width : Nat) : Int)) :=
    Int.mul_nonneg hx hy
  unfold low
  rw [Int.mul_emod, Int.toNat_emod (by omega) (by omega)]
  rw [Int.toNat_mul hx hy]
  simp [-Int.natCast_pow]

theorem low_shift_one (width : Nat) (x : Int) :
    low width (x <<< 1) = ((low width x <<< 1) % 2^width) := by
  rw [show x <<< 1 = x * 2 by simp [Int.shiftLeft_eq]]
  rw [low_mul]
  have htwo : low width (2 : Int) = 2 % 2^width := by
    simp [low, Int.toNat_emod, -Int.natCast_pow]
  rw [htwo]
  simp [Nat.shiftLeft_eq, Nat.mul_mod]

/-! ## The Python loop, transcribed -/

structure PyState where
  positive : Int
  negative : Int
  distance : Int

/-- One iteration of `for element in s2:` (lines in the same order as the
PR). `peq.get(element, 0)` is `peq xs c`; `high_bit = 1 << (width - 1)`. -/
def pyStep [DecidableEq α] (xs : List α) (c : α) (s : PyState) : PyState :=
  let highBit : Int := (1 : Int) <<< (xs.length - 1)
  let eqMask : Int := (peq xs c : Nat)
  let vertical := eqMask ||| s.negative
  let horizontal := (((eqMask &&& s.positive) + s.positive) ^^^ s.positive) ||| eqMask
  let positiveShift := s.negative ||| ~~~(horizontal ||| s.positive)
  let negativeShift := s.positive &&& horizontal
  let distance := s.distance + (if positiveShift &&& highBit ≠ 0 then 1 else 0)
  let distance := distance - (if negativeShift &&& highBit ≠ 0 then 1 else 0)
  let positiveShift := (positiveShift <<< 1) ||| 1
  let negativeShift := negativeShift <<< 1
  let positive := negativeShift ||| ~~~(vertical ||| positiveShift)
  let negative := positiveShift &&& vertical
  ⟨positive, negative, distance⟩

/-- `positive = ~0`, `negative = 0`, `distance = width`. -/
def pyInit [DecidableEq α] (xs : List α) : PyState := ⟨~~~0, 0, xs.length⟩

def pyRun [DecidableEq α] (xs ys : List α) : PyState :=
  ys.foldl (fun s c => pyStep xs c s) (pyInit xs)

/-- `_edit_distance_bitparallel(s1, s2)`; `None` for empty `s1`. The Python
`None` returns for unhashable or non-reflexive tokens are not modelled. -/
def bitparallel [DecidableEq α] (xs ys : List α) : Option Int :=
  if xs.length = 0 then none else some (pyRun xs ys).distance

/-! ## The same loop on the low `len(s1)+1` bits -/

structure State where
  positive : Nat
  negative : Nat
  distance : Int

/-- `matches`, `horizontal`, `positive_shift` and `negative_shift` (before
the shifts), on the low `width = len(s1)+1` bits. -/
def eqLow [DecidableEq α] (xs : List α) (c : α) : Nat := peq xs c % 2^(xs.length + 1)

def hMask [DecidableEq α] (xs : List α) (c : α) (s : State) : Nat :=
  ((((eqLow xs c &&& s.positive) + s.positive) % 2^(xs.length + 1)) ^^^ s.positive) |||
    eqLow xs c

def phMask [DecidableEq α] (xs : List α) (c : α) (s : State) : Nat :=
  s.negative ||| bnot (xs.length + 1) (hMask xs c s ||| s.positive)

def mhMask [DecidableEq α] (xs : List α) (c : α) (s : State) : Nat :=
  s.positive &&& hMask xs c s

/-- `pyStep` with every value replaced by its low `width` bits; `step_low`
proves the two agree. -/
def step [DecidableEq α] (xs : List α) (c : α) (s : State) : State :=
  let width := xs.length + 1
  let vertical := eqLow xs c ||| s.negative
  let distance := s.distance + (if (phMask xs c s).testBit (xs.length - 1) then 1 else 0)
  let distance := distance - (if (mhMask xs c s).testBit (xs.length - 1) then 1 else 0)
  let positiveShift := ((phMask xs c s <<< 1) % 2^width) ||| (1 % 2^width)
  let negativeShift := (mhMask xs c s <<< 1) % 2^width
  let positive := negativeShift ||| bnot width (vertical ||| positiveShift)
  let negative := positiveShift &&& vertical
  ⟨positive, negative, distance⟩

def lowState (width : Nat) (s : PyState) : State :=
  ⟨low width s.positive, low width s.negative, s.distance⟩

theorem step_low [DecidableEq α] (xs : List α) (c : α) (s : PyState) :
    step xs c (lowState (xs.length + 1) s) = lowState (xs.length + 1) (pyStep xs c s) := by
  have hk : xs.length - 1 < xs.length + 1 := by omega
  simp only [step, eqLow, hMask, phMask, mhMask, pyStep, lowState, low_or, low_and, low_xor,
    low_not, low_add, low_shift_one, low_one, low_natCast, and_high_ne_zero,
    ← low_testBit_lt _ _ _ hk]
  rfl

def initial (width : Nat) : State := ⟨2^(width+1) - 1, 0, width⟩

theorem initial_low [DecidableEq α] (xs : List α) :
    lowState (xs.length + 1) (pyInit xs) = initial xs.length := by
  simp only [lowState, pyInit, initial, low_not_zero]
  rfl

def run [DecidableEq α] (xs ys : List α) : State :=
  ys.foldl (fun s c => step xs c s) (initial xs.length)

theorem run_low [DecidableEq α] (xs ys : List α) :
    run xs ys = lowState (xs.length + 1) (pyRun xs ys) := by
  have loop (s : PyState) (rest : List α) :
      rest.foldl (fun st c => step xs c st) (lowState (xs.length + 1) s) =
        lowState (xs.length + 1) (rest.foldl (fun st c => pyStep xs c st) s) := by
    induction rest generalizing s with
    | nil => rfl
    | cons c cs ih => simp only [List.foldl_cons, step_low, ih]
  rw [run, pyRun, ← initial_low, loop]

/-! ## Carry propagation -/

def carry (a b i : Nat) : Bool := decide (2^i ≤ a % 2^i + b % 2^i)

theorem bv_carry (a b i w : Nat) (h : i ≤ w) :
    BitVec.carry i (BitVec.ofNat w a) (BitVec.ofNat w b) false = carry a b i := by
  simp only [BitVec.carry, BitVec.toNat_ofNat, carry, Bool.toNat_false, Nat.add_zero]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h), Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]

theorem testBit_add (a b i : Nat) :
    (a + b).testBit i = (a.testBit i ^^ (b.testBit i ^^ carry a b i)) := by
  have h := BitVec.getLsbD_add (w := i+1) (i := i) (by omega) (BitVec.ofNat _ a) (BitVec.ofNat _ b)
  rw [bv_carry a b i (i+1) (by omega)] at h
  rw [← BitVec.ofNat_add] at h
  simp only [BitVec.getLsbD_ofNat] at h
  simpa using h

theorem carry_zero (a b : Nat) : carry a b 0 = false := by
  simp [carry, Nat.mod_one]

theorem carry_succ (a b i : Nat) :
    carry a b (i+1) = Bool.atLeastTwo (a.testBit i) (b.testBit i) (carry a b i) := by
  have h := BitVec.carry_succ (w := i+1) i (BitVec.ofNat _ a) (BitVec.ofNat _ b) false
  rw [bv_carry a b i (i+1) (by omega), bv_carry a b (i+1) (i+1) (by omega)] at h
  simp only [BitVec.getLsbD_ofNat] at h
  simpa using h

theorem testBit_one (i : Nat) : (1 : Nat).testBit i = decide (i = 0) := by
  rw [show (1 : Nat) = 2^0 from rfl, Nat.testBit_two_pow]; simp [eq_comm]

/-! ## Bits of one `step` -/

section
variable [DecidableEq α] (xs : List α) (c : α) (s : State)

/-- Bit `i` of `Xh`: the add-and-xor term collapses to `Eq | carry`. -/
def xh (i : Nat) : Bool :=
  (eqLow xs c).testBit i || carry (eqLow xs c &&& s.positive) s.positive i
/-- Bit `i` of `Ph` (row `i+1` gains one). -/
def ph (i : Nat) : Bool :=
  s.negative.testBit i || !(xh xs c s i || s.positive.testBit i)
/-- Bit `i` of `Mh` (row `i+1` loses one). -/
def mh (i : Nat) : Bool := s.positive.testBit i && xh xs c s i
/-- `(Ph << 1) | 1` at bit `i`. -/
def phs : Nat → Bool
  | 0 => true
  | k + 1 => ph xs c s k
/-- `Mh << 1` at bit `i`. -/
def mhs : Nat → Bool
  | 0 => false
  | k + 1 => mh xs c s k

theorem low_peq_bit (i : Nat) (hi : i < xs.length + 1) :
    (eqLow xs c).testBit i = decide (xs[i]? = some c) := by
  rw [eqLow, Nat.testBit_mod_two_pow, peq_bit]; simp [hi]

theorem horizontal_bit (E P W i : Nat) (hi : i < W) :
    ((((E &&& P) + P) % 2^W ^^^ P) ||| E).testBit i =
      (E.testBit i || carry (E &&& P) P i) := by
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_xor, testBit_add,
    Nat.testBit_and, hi, decide_true, Bool.true_and]
  cases E.testBit i <;> cases P.testBit i <;> cases carry (E &&& P) P i <;> rfl

theorem ph_bit (i : Nat) (hi : i < xs.length + 1) :
    (phMask xs c s).testBit i = ph xs c s i := by
  rw [phMask, Nat.testBit_or, bnot_bit _ _ _ hi, Nat.testBit_or, hMask,
    horizontal_bit _ _ _ _ hi]; rfl

theorem mh_bit (i : Nat) (hi : i < xs.length + 1) :
    (mhMask xs c s).testBit i = mh xs c s i := by
  rw [mhMask, Nat.testBit_and, hMask, horizontal_bit _ _ _ _ hi]; rfl

theorem step_distance :
    (step xs c s).distance = s.distance + (if ph xs c s (xs.length - 1) then 1 else 0)
      - (if mh xs c s (xs.length - 1) then 1 else 0) := by
  simp only [step]
  rw [ph_bit _ _ _ _ (by omega), mh_bit _ _ _ _ (by omega)]

theorem phs_bit (i : Nat) (hi : i < xs.length + 1) :
    ((phMask xs c s <<< 1) % 2^(xs.length + 1) ||| 1 % 2^(xs.length + 1)).testBit i =
      phs xs c s i := by
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    testBit_one]
  cases i with
  | zero => simp [phs, hi]
  | succ k => rw [ph_bit _ _ _ _ (by omega)]; simp [phs, hi]

theorem mhs_bit (i : Nat) (hi : i < xs.length + 1) :
    ((mhMask xs c s <<< 1) % 2^(xs.length + 1)).testBit i = mhs xs c s i := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  cases i with
  | zero => simp [mhs]
  | succ k => rw [mh_bit _ _ _ _ (by omega)]; simp [mhs, hi]

theorem step_positive_bit (i : Nat) (hi : i < xs.length + 1) :
    (step xs c s).positive.testBit i =
      (mhs xs c s i ||
        !(((eqLow xs c).testBit i || s.negative.testBit i) || phs xs c s i)) := by
  simp only [step]
  rw [Nat.testBit_or, bnot_bit _ _ _ hi, mhs_bit _ _ _ _ hi, Nat.testBit_or,
    phs_bit _ _ _ _ hi, Nat.testBit_or]

theorem step_negative_bit (i : Nat) (hi : i < xs.length + 1) :
    (step xs c s).negative.testBit i =
      (phs xs c s i && ((eqLow xs c).testBit i || s.negative.testBit i)) := by
  simp only [step]
  rw [Nat.testBit_and, phs_bit _ _ _ _ hi, Nat.testBit_or]

/-- The carry into bit `i` of `(Eq & Pv) + Pv` is `Mh` shifted left. -/
theorem carry_mh (i : Nat) :
    carry (eqLow xs c &&& s.positive) s.positive i = mhs xs c s i := by
  cases i with
  | zero => simp [carry, mhs, Nat.mod_one]
  | succ k =>
    rw [carry_succ, Nat.testBit_and]
    simp only [mhs, mh, xh]
    cases (eqLow xs c).testBit k <;> cases s.positive.testBit k <;>
      cases carry (eqLow xs c &&& s.positive) s.positive k <;> rfl
end

/-! ## One DP column -/

/-- Myers' cell lemma: vertical delta `b - a`, horizontal delta `a' - a`, and
`b' = min(...)`, give the outgoing deltas by the Hyyrö bit formulas. -/
theorem cell (a b a' b' : Nat) (e : Bool)
    (hb' : b' = min (min (a' + 1) (b + 1)) (a + if e then 0 else 1))
    (h1 : b ≤ a + 1) (h2 : a ≤ b + 1) (h3 : a' ≤ a + 1) (h4 : a ≤ a' + 1) :
    (decide (a = b + 1) || !((e || decide (a' + 1 = a)) || decide (b = a + 1))) =
      decide (b' = b + 1) ∧
    (decide (b = a + 1) && (e || decide (a' + 1 = a))) = decide (b' + 1 = b) ∧
    b' ≤ b + 1 ∧ b ≤ b' + 1 ∧
    (decide (a' + 1 = a) || !((e || decide (a = b + 1)) || decide (a' = a + 1))) =
      decide (b' = a' + 1) ∧
    (decide (a' = a + 1) && (e || decide (a = b + 1))) = decide (a' = b' + 1) ∧
    b' ≤ a' + 1 ∧ a' ≤ b' + 1 := by
  subst hb'
  cases e <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try apply Bool.eq_iff_iff.mpr) <;>
    simp <;> omega

/-- `p`/`n` encode the vertical delta `b - a ∈ {+1, -1, 0}`. -/
def Enc (p n : Bool) (a b : Nat) : Prop :=
  p = decide (b = a + 1) ∧ n = decide (a = b + 1) ∧ b ≤ a + 1 ∧ a ≤ b + 1

/-- After `j` target tokens, the masks encode column `j` of the table and the
distance is its last cell. -/
def Invariant [DecidableEq α] (xs ys : List α) (j : Nat) (s : State) : Prop :=
  s.distance = lev xs ys xs.length j ∧
  ∀ i, i < xs.length →
    Enc (s.positive.testBit i) (s.negative.testBit i) (lev xs ys i j) (lev xs ys (i + 1) j)

theorem column_step [DecidableEq α] (xs ys : List α) (j : Nat) (c : α)
    (hc : ys[j]? = some c) (s : State) (hne : xs ≠ []) (hinv : Invariant xs ys j s) :
    Invariant xs ys (j + 1) (step xs c s) := by
  -- `cell` at row `k`, rewritten in terms of the step's bits
  have cellAt : ∀ k, k < xs.length →
      mhs xs c s k = decide (lev xs ys k (j + 1) + 1 = lev xs ys k j) →
      lev xs ys k (j + 1) ≤ lev xs ys k j + 1 → lev xs ys k j ≤ lev xs ys k (j + 1) + 1 →
      let a := lev xs ys k j
      let b := lev xs ys (k + 1) j
      let a' := lev xs ys k (j + 1)
      let b' := lev xs ys (k + 1) (j + 1)
      let e := decide (xs[k]? = some c)
      ph xs c s k = decide (b' = b + 1) ∧ mh xs c s k = decide (b' + 1 = b) ∧
      b' ≤ b + 1 ∧ b ≤ b' + 1 ∧
      (decide (a' + 1 = a) || !((e || decide (a = b + 1)) || decide (a' = a + 1))) =
        decide (b' = a' + 1) ∧
      (decide (a' = a + 1) && (e || decide (a = b + 1))) = decide (a' = b' + 1) ∧
      b' ≤ a' + 1 ∧ a' ≤ b' + 1 := by
    intro k hk hm h3 h4
    obtain ⟨hp, hn, h1, h2⟩ := hinv.2 k hk
    have hb' := lev_succ_succ xs ys k j
    rw [hc] at hb'
    have hcell := cell (lev xs ys k j) (lev xs ys (k + 1) j) (lev xs ys k (j + 1))
      (lev xs ys (k + 1) (j + 1)) (decide (xs[k]? = some c)) (by rw [hb']; simp) h1 h2 h3 h4
    simp only [ph, mh, xh, carry_mh, low_peq_bit xs c k (by omega), hp, hn, hm]
    exact hcell
  -- scan the column upward: the horizontal delta at every row is in {-1,0,1}
  -- and is what `(Ph << 1) | 1` / `Mh << 1` (= the carry) report
  have rows : ∀ i, i ≤ xs.length →
      (lev xs ys i (j + 1) ≤ lev xs ys i j + 1 ∧ lev xs ys i j ≤ lev xs ys i (j + 1) + 1) ∧
      mhs xs c s i = decide (lev xs ys i (j + 1) + 1 = lev xs ys i j) ∧
      phs xs c s i = decide (lev xs ys i (j + 1) = lev xs ys i j + 1) := by
    intro i
    induction i with
    | zero => intro _; simp [lev_zero_left, mhs, phs]; omega
    | succ k ih =>
      intro hk
      obtain ⟨⟨h3, h4⟩, hm, _⟩ := ih (by omega)
      obtain ⟨hph, hmh, h5, h6, -⟩ := cellAt k (by omega) hm h3 h4
      exact ⟨⟨h5, h6⟩, hmh, hph⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, xs.length = k + 1 :=
      ⟨xs.length - 1, by cases xs <;> simp_all⟩
    obtain ⟨⟨h3, h4⟩, hm, hp⟩ := rows (k + 1) (by omega)
    rw [step_distance, hinv.1, hk, show k + 1 - 1 = k by omega]
    simp only [mhs, phs] at hm hp
    rw [hm, hp]
    by_cases h₁ : lev xs ys (k + 1) (j + 1) = lev xs ys (k + 1) j + 1 <;>
    by_cases h₂ : lev xs ys (k + 1) (j + 1) + 1 = lev xs ys (k + 1) j <;>
      simp [h₁, h₂] <;> omega
  · intro i hi
    obtain ⟨⟨h3, h4⟩, hm, hp⟩ := rows i (by omega)
    obtain ⟨-, -, -, -, hP, hN, h7, h8⟩ := cellAt i hi hm h3 h4
    obtain ⟨-, hn, -, -⟩ := hinv.2 i hi
    refine ⟨?_, ?_, h7, h8⟩
    · rw [step_positive_bit xs c s i (by omega), hm, hp, low_peq_bit xs c i (by omega), hn]
      exact hP
    · rw [step_negative_bit xs c s i (by omega), hp, low_peq_bit xs c i (by omega), hn]; exact hN

theorem initial_invariant [DecidableEq α] (xs ys : List α) :
    Invariant xs ys 0 (initial xs.length) := by
  refine ⟨by simp [initial, lev_zero_right], fun i hi => ?_⟩
  simp only [Enc, initial, Nat.testBit_two_pow_sub_one, Nat.zero_testBit, lev_zero_right]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try simp) <;> omega

theorem run_invariant [DecidableEq α] (xs ys : List α) (hne : xs ≠ []) :
    Invariant xs ys ys.length (run xs ys) := by
  have h : ∀ j, j ≤ ys.length →
      Invariant xs ys j ((ys.take j).foldl (fun s c => step xs c s) (initial xs.length)) := by
    intro j
    induction j with
    | zero => intro _; simpa using initial_invariant xs ys
    | succ j ih =>
      intro hj
      have hc : ys[j]? = some ys[j] := List.getElem?_eq_getElem (by omega)
      rw [List.take_add_one, hc, Option.toList_some, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      exact column_step xs ys j _ hc _ hne (ih (by omega))
  simpa [run] using h ys.length (Nat.le_refl _)

/-- Main theorem: the bit-parallel helper equals the DP for every nonempty
`s1` and every `s2`. -/
theorem bitparallel_eq_dp [DecidableEq α] (xs ys : List α) (hne : xs ≠ []) :
    bitparallel xs ys = some (dp xs ys : Int) := by
  have h := (run_invariant xs ys hne).1
  rw [run_low] at h
  have hl : xs.length ≠ 0 := by cases xs <;> simp_all
  simp [bitparallel, hl, dp, ← h, lowState]

/-- `result` is the helper's result: `none` covers empty input and the
Python hash/equality failures. `enabled` is the unit-cost/no-transpositions
guard. -/
def dispatch [DecidableEq α] (xs ys : List α) (enabled : Bool)
    (result : Option Int) : Int :=
  if enabled then result.getD (dp xs ys) else dp xs ys

theorem dispatch_fallback [DecidableEq α] (xs ys : List α)
    (enabled : Bool) (result : Option Int)
    (h : enabled = false ∨ result = none) :
    dispatch xs ys enabled result = dp xs ys := by
  rcases h with h | h
  · simp [dispatch, h]
  · cases enabled <;> simp [dispatch, h]

theorem dispatch_eq_dp [DecidableEq α] (xs ys : List α) (enabled : Bool)
    (result : Option Int) (hresult : result = none ∨ result = bitparallel xs ys) :
    dispatch xs ys enabled result = dp xs ys := by
  rcases hresult with h | h
  · exact dispatch_fallback xs ys enabled result (Or.inr h)
  · subst result
    by_cases hne : xs = []
    · subst xs; simp [dispatch, bitparallel]
    · cases enabled
      · simp [dispatch]
      · simp [dispatch, bitparallel_eq_dp xs ys hne]

#print axioms peq_bit
#print axioms ibit_inj
#print axioms ibit_and
#print axioms ibit_or
#print axioms ibit_xor
#print axioms ibit_not
#print axioms low_testBit
#print axioms low_and
#print axioms low_or
#print axioms low_xor
#print axioms low_not
#print axioms low_add
#print axioms low_shift_one
#print axioms and_high_ne_zero
#print axioms step_low
#print axioms run_low
#print axioms testBit_add
#print axioms carry_succ
#print axioms cell
#print axioms column_step
#print axioms initial_invariant
#print axioms run_invariant
#print axioms bitparallel_eq_dp
#print axioms dispatch_fallback
#print axioms dispatch_eq_dp

end NltkMyers
