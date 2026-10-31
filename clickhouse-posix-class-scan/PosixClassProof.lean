/-!
ClickHouse `skipPosixNamedClass`: skipping the `:]` scan when no `:]` is left in the regexp
returns exactly what the original scan returns.

The regexp is a list of characters and pointers are indices into it, so `end` is `s.length`.
-/

theorem ite_t {α} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
theorem ite_f {α} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by simp [h]

/-- A `:]` starts at index `j`. -/
def isClose (s : List Char) (j : Nat) : Bool :=
  s[j]? == some ':' && s[j + 1]? == some ']'

theorem isClose_lt {s : List Char} {j : Nat} (h : isClose s j = true) : j + 1 < s.length := by
  apply Classical.byContradiction
  intro hc
  have : s[j + 1]? = none := List.getElem?_eq_none (by omega)
  simp [isClose, this] at h

/-- The original loop: `for (name_end = pos + 2; name_end <= end - 2; ++name_end)`, started at
`i = pos + 2`. It returns the first `:]` at or after `i`. -/
def scan (s : List Char) (i : Nat) : Option Nat :=
  if i + 1 < s.length then (if isClose s i then some i else scan s (i + 1)) else none
termination_by s.length - i

/-- The original `skipPosixNamedClass(pos, end)`. -/
def skipOld (s : List Char) (p : Nat) : Nat :=
  if s.length - p ≤ 2 ∨ s[p + 1]? ≠ some ':' then p + 1
  else match scan s (p + 2) with
    | some j => j + 2
    | none => p + 1

/-- The new `skipPosixNamedClass(pos, end, last_close)`. -/
def skipNew (s : List Char) (lc : Option Nat) (p : Nat) : Nat :=
  if s.length - p ≤ 2 ∨ s[p + 1]? ≠ some ':' then p + 1
  else match lc with
    | none => p + 1
    | some l =>
      if l < p + 2 then p + 1
      else match scan s (p + 2) with
        | some j => j + 2
        | none => p + 1

/-- What `regexp.rfind(":]")` returns: the last `:]`, or nothing if there is none. -/
def IsLastClose (s : List Char) : Option Nat → Prop
  | none => ∀ j, isClose s j = false
  | some l => isClose s l = true ∧ ∀ j, l < j → isClose s j = false

theorem scan_none (s : List Char) :
    ∀ k i, s.length - i = k → (∀ j, i ≤ j → isClose s j = false) → scan s i = none := by
  intro k
  induction k with
  | zero =>
    intro i hk _
    rw [scan, ite_f (by omega)]
  | succ k ih =>
    intro i hk h
    rw [scan]
    split
    · rw [h i (Nat.le_refl _)]
      exact ih (i + 1) (by omega) (fun j hj => h j (by omega))
    · rfl

theorem scan_hit (s : List Char) (l : Nat) (hl : isClose s l = true) :
    ∀ k i, s.length - i = k → i ≤ l → ∃ j, scan s i = some j ∧ isClose s j = true ∧ j ≤ l := by
  have hlt := isClose_lt hl
  intro k
  induction k with
  | zero => intro i hk hi; omega
  | succ k ih =>
    intro i hk hi
    rw [scan, ite_t (by omega)]
    by_cases hc : isClose s i = true
    · exact ⟨i, by simp [hc], hc, hi⟩
    · rw [ite_f hc]
      have hne : i ≠ l := fun e => hc (e ▸ hl)
      exact ih (i + 1) (by omega) (by omega)

/-- The new code gives the same position for every `[` in every regexp. -/
theorem skip_exact (s : List Char) (lc : Option Nat) (h : IsLastClose s lc) (p : Nat) :
    skipNew s lc p = skipOld s p := by
  unfold skipNew skipOld
  split
  · rfl
  · cases lc with
    | none =>
      rw [scan_none s _ (p + 2) rfl (fun j _ => h j)]
    | some l =>
      simp only
      split
      · rename_i hlp
        rw [scan_none s _ (p + 2) rfl (fun j hj => h.2 j (by omega))]
      · rfl

/-- So the analyzer, which only sees `regexp` through these calls, cannot tell the two apart. -/
theorem skip_funext (s : List Char) (lc : Option Nat) (h : IsLastClose s lc) :
    skipNew s lc = skipOld s :=
  funext (skip_exact s lc h)

/-- Why the new code is linear: it only runs the scan when the scan finds a `:]`, and then the
analyzer continues after it, so no character is scanned twice. -/
theorem scan_only_on_hit (s : List Char) (l p : Nat) (h : IsLastClose s (some l)) (hp : ¬ l < p + 2) :
    ∃ j, scan s (p + 2) = some j ∧ p + 2 ≤ j ∧ j ≤ l := by
  obtain ⟨j, hj, _, hjl⟩ := scan_hit s l h.1 _ (p + 2) rfl (by omega)
  refine ⟨j, hj, ?_, hjl⟩
  -- the scan starts at p + 2, so whatever it returns is at least that
  have key : ∀ k i, s.length - i = k → ∀ j, scan s i = some j → i ≤ j := by
    intro k
    induction k with
    | zero => intro i hk j hs; rw [scan, ite_f (by omega)] at hs; cases hs
    | succ k ih =>
      intro i hk j hs
      rw [scan] at hs
      split at hs
      · split at hs
        · cases hs; omega
        · have := ih (i + 1) (by omega) j hs; omega
      · cases hs
  exact key _ _ rfl j hj

/-! `regexp.rfind(":]")`, written as a recursion, satisfies `IsLastClose`. -/

/-- The last `:]` at index `i` or later. -/
def lastFrom (s : List Char) (i : Nat) : Option Nat :=
  if i < s.length then
    match lastFrom s (i + 1) with
    | some l => some l
    | none => if isClose s i then some i else none
  else none
termination_by s.length - i

theorem lastFrom_spec (s : List Char) : ∀ k i, s.length - i = k →
    (lastFrom s i = none → ∀ j, i ≤ j → isClose s j = false) ∧
    (∀ l, lastFrom s i = some l → isClose s l = true ∧ ∀ j, l < j → isClose s j = false) := by
  intro k
  induction k with
  | zero =>
    intro i hk
    have hnone : lastFrom s i = none := by rw [lastFrom, ite_f (by omega)]
    refine ⟨fun _ j hj => ?_, fun l hl => by rw [hnone] at hl; cases hl⟩
    cases hc : isClose s j
    · rfl
    · have := isClose_lt hc; omega
  | succ k ih =>
    intro i hk
    obtain ⟨ihn, ihs⟩ := ih (i + 1) (by omega)
    rw [lastFrom, ite_t (by omega)]
    cases hr : lastFrom s (i + 1) with
    | some l =>
      simp only
      refine ⟨fun h => ?_, fun l' hl' => ?_⟩
      · cases h
      · cases hl'; exact ihs l hr
    | none =>
      have rest := ihn hr
      simp only
      by_cases hc : isClose s i = true
      · rw [ite_t hc]
        refine ⟨fun h => ?_, fun l hl => ?_⟩
        · cases h
        · cases hl; exact ⟨hc, fun j hj => rest j (by omega)⟩
      · rw [ite_f hc]
        refine ⟨fun _ j hj => ?_, fun l hl => ?_⟩
        · by_cases e : j = i
          · subst e; simpa using hc
          · exact rest j (by omega)
        · cases hl

theorem lastClose_spec (s : List Char) : IsLastClose s (lastFrom s 0) := by
  obtain ⟨hn, hs⟩ := lastFrom_spec s _ 0 rfl
  cases h : lastFrom s 0 with
  | none => exact fun j => hn h j (Nat.zero_le _)
  | some l => exact hs l h

/-- End to end: with `last_close` computed as `rfind(":]")`, the new function is the old one. -/
theorem skip_exact_rfind (s : List Char) : skipNew s (lastFrom s 0) = skipOld s :=
  skip_funext s _ (lastClose_spec s)

#print axioms skip_exact_rfind
#print axioms scan_only_on_hit
