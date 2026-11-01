/-!
pyteomics `parser.coverage_mask`: finding peptides with `str.find` and summing a difference array
gives exactly the mask of the original lookahead-regex version.

Sequences are `List Char`. The original runs `re.finditer(f'(?={peptide})', protein)`: for a
peptide of letters the lookahead is tried at every position `0..len(protein)` and succeeds where
the peptide occurs (`occOld`). It then adds 1 over `mask[i:i + len(peptide)]` for each start `i`.
-/

set_option linter.unusedVariables false

theorem ite_t {α} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
theorem ite_f {α} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by simp [h]

/-- The peptide occurs at index `i`. -/
def isAt (s p : List Char) (i : Nat) : Bool := ((s.drop i).take p.length) == p

theorem isAt_past (s p : List Char) (i : Nat) (hp : p ≠ []) (h : s.length < i + p.length) :
    isAt s p i = false := by
  unfold isAt
  have hl : ((s.drop i).take p.length).length ≤ s.length - i := by
    rw [List.length_take, List.length_drop]; exact Nat.min_le_right _ _
  cases hq : ((s.drop i).take p.length) == p with
  | false => rfl
  | true =>
    have e := congrArg List.length (beq_iff_eq.mp hq)
    have : p.length ≠ 0 := fun e => hp (List.eq_nil_of_length_eq_zero e)
    omega

/-- The original: every position from `i` to the end where the lookahead succeeds. -/
def occOld (s p : List Char) (i : Nat) : List Nat :=
  if i ≤ s.length then (if isAt s p i then i :: occOld s p (i + 1) else occOld s p (i + 1)) else []
termination_by s.length + 1 - i

/-- Python's `protein.find(peptide, i)`: the first occurrence at or after `i`. -/
def find (s p : List Char) (i : Nat) : Option Nat :=
  if i + p.length ≤ s.length then (if isAt s p i then some i else find s p (i + 1)) else none
termination_by s.length + 1 - i

theorem find_some (s p : List Char) : ∀ k i j, s.length + 1 - i = k → find s p i = some j →
    i ≤ j ∧ j ≤ s.length ∧ isAt s p j = true ∧ ∀ m, i ≤ m → m < j → isAt s p m = false := by
  intro k; induction k with
  | zero =>
    intro i j hk h; rw [find] at h; split at h
    · rename_i hc; have : 0 < p.length ∨ p.length = 0 := by omega
      omega
    · cases h
  | succ k ih =>
    intro i j hk h
    rw [find] at h
    split at h
    · split at h
      · rename_i hi; cases h; exact ⟨Nat.le_refl _, by omega, hi, fun m h1 h2 => by omega⟩
      · rename_i hi
        obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) j (by omega) h
        refine ⟨by omega, h2, h3, fun m hm1 hm2 => ?_⟩
        by_cases e : m = i
        · subst e; simpa using hi
        · exact h4 m (by omega) hm2
    · cases h

theorem find_none (s p : List Char) (hp : p ≠ []) : ∀ k i, s.length + 1 - i = k → find s p i = none →
    ∀ m, i ≤ m → isAt s p m = false := by
  intro k; induction k with
  | zero => intro i hk h m hm; exact isAt_past s p m hp (by have : p.length ≠ 0 := fun e => hp (List.eq_nil_of_length_eq_zero e); omega)
  | succ k ih =>
    intro i hk h m hm
    rw [find] at h
    split at h
    · split at h
      · cases h
      · rename_i hi
        by_cases e : m = i
        · subst e; simpa using hi
        · exact ih (i + 1) (by omega) h m (by omega)
    · exact isAt_past s p m hp (by omega)

/-- The new loop: `i = protein.find(peptide)` then `protein.find(peptide, i + 1)` until -1. -/
def occNew (s p : List Char) (i : Nat) : List Nat :=
  match h : find s p i with
  | none => []
  | some j => j :: occNew s p (j + 1)
termination_by s.length + 1 - i
decreasing_by have := find_some s p _ i j rfl h; omega

theorem occOld_skip (s p : List Char) : ∀ k i j, s.length + 1 - i = k → i ≤ j → j ≤ s.length + 1 →
    (∀ m, i ≤ m → m < j → isAt s p m = false) → occOld s p i = occOld s p j := by
  intro k; induction k with
  | zero => intro i j hk hij hj h; rw [occOld.eq_1 s p i, occOld.eq_1 s p j, ite_f (by omega), ite_f (by omega)]
  | succ k ih =>
    intro i j hk hij hj h
    by_cases e : i = j
    · rw [e]
    · rw [occOld, ite_t (by omega), ite_f (by simp [h i (Nat.le_refl _) (by omega)])]
      exact ih (i + 1) j (by omega) (by omega) hj (fun m h1 h2 => h m (by omega) h2)

theorem occOld_nil (s p : List Char) : ∀ k i, s.length + 1 - i = k →
    (∀ m, i ≤ m → isAt s p m = false) → occOld s p i = [] := by
  intro k; induction k with
  | zero => intro i hk h; rw [occOld, ite_f (by omega)]
  | succ k ih =>
    intro i hk h
    rw [occOld, ite_t (by omega), ite_f (by simp [h i (Nat.le_refl _)])]
    exact ih (i + 1) (by omega) (fun m hm => h m (by omega))

/-- The `str.find` loop yields exactly the lookahead matches, in the same order. -/
theorem occ_exact (s p : List Char) (hp : p ≠ []) :
    ∀ k i, s.length + 1 - i = k → occNew s p i = occOld s p i := by
  intro k; induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i hk
    rw [occNew]
    split
    · rename_i h; exact (occOld_nil s p _ i rfl (find_none s p hp _ i rfl h)).symm
    · rename_i j h
      obtain ⟨h1, h2, h3, h4⟩ := find_some s p _ i j rfl h
      rw [occOld_skip s p _ i j rfl h1 (by omega) h4, occOld.eq_1 s p j, ite_t h2, ite_t h3,
        ih _ (by omega) (j + 1) rfl]

/-! ## The difference array -/

/-- `np.cumsum(delta)[k]`. -/
def prefixSum (f : Nat → Int) : Nat → Int
  | 0 => f 0
  | k + 1 => prefixSum f k + f (k + 1)

theorem prefixSum_add (f g : Nat → Int) : ∀ k, prefixSum (fun j => f j + g j) k = prefixSum f k + prefixSum g k := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp only [prefixSum, ih]; omega

theorem prefixSum_zero : ∀ k, prefixSum (fun _ => (0 : Int)) k = 0 := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp only [prefixSum, ih]; rfl

/-- The running sum commutes with summing over a list. -/
theorem prefixSum_sum {α} (L : List α) (f : α → Nat → Int) (k : Nat) :
    prefixSum (fun j => (L.map fun x => f x j).sum) k = (L.map fun x => prefixSum (f x) k).sum := by
  induction L with
  | nil => simpa using prefixSum_zero k
  | cons x L ih => simp only [List.map_cons, List.sum_cons]; rw [prefixSum_add, ih]

/-- One occurrence: +1 at `i`, -1 at `i + n`. Its running sum at `k` is 1 exactly on `[i, i + n)`. -/
theorem prefixSum_one (i n : Nat) : ∀ k,
    prefixSum (fun j => (if i = j then 1 else 0) - (if i + n = j then 1 else 0)) k =
    (if i ≤ k ∧ k < i + n then 1 else 0) := by
  intro k; induction k with
  | zero => simp only [prefixSum]; by_cases a : i = 0 <;> by_cases b : i + n = 0 <;> simp [a, b] <;> omega
  | succ k ih =>
    simp only [prefixSum, ih]
    by_cases a : i = k + 1 <;> by_cases b : i + n = k + 1 <;>
      by_cases c : i ≤ k ∧ k < i + n <;> by_cases d : i ≤ k + 1 ∧ k + 1 < i + n <;> simp [a, b, c, d] <;> omega

/-- The original mask at residue `k`: one per occurrence covering it, over all peptides. -/
def maskOld (s : List Char) (peps : List (List Char)) (k : Nat) : Int :=
  (peps.map fun p => ((occOld s p 0).map fun i => if i ≤ k ∧ k < i + p.length then (1 : Int) else 0).sum).sum

/-- The new `delta[j]`; empty peptides are skipped. -/
def delta (s : List Char) (peps : List (List Char)) (j : Nat) : Int :=
  (peps.map fun p => if p = [] then 0 else
    ((occNew s p 0).map fun i => ((if i = j then 1 else 0) - (if i + p.length = j then 1 else 0) : Int)).sum).sum

/-- `np.cumsum(delta[:-1])` is the original mask at every residue. -/
theorem mask_exact (s : List Char) (peps : List (List Char)) (k : Nat) :
    prefixSum (delta s peps) k = maskOld s peps k := by
  unfold delta maskOld
  rw [prefixSum_sum]
  congr 1; apply List.map_congr_left; intro p _
  by_cases hp : p = []
  · subst hp
    have h0 : ∀ i, ¬ (i ≤ k ∧ k < i + 0) := fun i => by omega
    have hz : ∀ (L : List Nat), (L.map fun _ => (0 : Int)).sum = 0 := by
      intro L; induction L <;> simp_all
    simp only [List.length_nil, h0, ite_false, ite_true]
    rw [prefixSum_zero, hz]
  · simp only [ite_f hp]
    rw [prefixSum_sum, occ_exact s p hp _ 0 rfl]
    congr 1; apply List.map_congr_left; intro i _
    exact prefixSum_one i p.length k

#print axioms occ_exact
#print axioms mask_exact
