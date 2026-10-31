/-
Skipping already-rejected peaks in XQRS backsearch gives the same detector state.

Model of `XQRS._run_detection` (wfdb-python, `src/wfdb/processing/qrs.py`).
The detector state `S` is abstract. What the proof needs from the code:

* `upd s j p`  : `_update_qrs` for peak `j` while the loop is at peak `p`.
                 It sets `last_qrs_peak_num := p` (`upd_last`).
* `noise s j`  : `_update_noise`. It changes neither `last_qrs_peak_num` nor
                 the backsearch check (`noise_last`, `noise_bs`); that check
                 reads `qrs_thr`, `last_qrs_ind` and the signal only.
* `isQ`, `req`, `bs` : `_is_qrs`, `_require_backsearch`,
                 `_is_qrs(backsearch=True)`. Arbitrary functions of the state.

`lastPeak s = none` models `last_qrs_peak_num is None`.
-/

section
variable {S : Type}
variable (lastPeak : S → Option Nat) (bs : S → Nat → Bool)
variable (upd : S → Nat → Nat → S) (noise : S → Nat → S)
variable (isQ : S → Nat → Bool) (req : S → Nat → Bool)

/-- `for j in js: if bs(j): upd(j)` with the loop at peak `p`. -/
def scan (p : Nat) : S → List Nat → S
  | s, [] => s
  | s, j :: js => scan p (if bs s j then upd s j p else s) js

/-- Main-loop body for peak `p`, before the backsearch. -/
def mainStep (s : S) (p : Nat) : S :=
  if isQ s p then upd s p p else noise s p

/-- Original: backsearch rescans `range(last + 1, p + 1)`. -/
def oldStep (s : S) (p : Nat) : S :=
  let s1 := mainStep upd noise isQ s p
  if req s1 p then
    match lastPeak s1 with
    | none => s1
    | some l => scan bs upd p s1 (List.range' (l + 1) (p - l))
  else s1

/-- New: start at `max(last, w) + 1` with `nxt = w + 1`, then set `w := p`. -/
def newStep (st : S × Nat) (p : Nat) : S × Nat :=
  let s1 := mainStep upd noise isQ st.1 p
  if req s1 p then
    match lastPeak s1 with
    | none => (s1, st.2)
    | some l =>
      let a := max (l + 1) st.2
      (scan bs upd p s1 (List.range' a (p + 1 - a)), p + 1)
  else (s1, st.2)

/-- Run peaks `0 .. n-1`. -/
def oldRun (s : S) : Nat → S
  | 0 => s
  | n + 1 => oldStep lastPeak bs upd noise isQ req (oldRun s n) n

def newRun (s : S) : Nat → S × Nat
  | 0 => (s, 0)
  | n + 1 => newStep lastPeak bs upd noise isQ req (newRun s n) n

/-- Peaks between the last QRS and `nxt` were rejected by backsearch. -/
def BsInv (s : S) (nxt : Nat) : Prop :=
  ∀ l, lastPeak s = some l → ∀ j, l < j → j < nxt → bs s j = false

/-- Scanning peaks that all fail the check changes nothing. -/
theorem scan_false (p : Nat) (s : S) (xs ys : List Nat)
    (h : ∀ j ∈ xs, bs s j = false) :
    scan bs upd p s (xs ++ ys) = scan bs upd p s ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, scan, h x (by simp)]
    exact ih (fun j hj => h j (by simp [hj]))

/-- A scan either finds nothing (state unchanged, all rejected) or ends with
`last_qrs_peak_num = p`. -/
theorem scan_cases (upd_last : ∀ s j p, lastPeak (upd s j p) = some p)
    (p : Nat) (s : S) (xs : List Nat) :
    (scan bs upd p s xs = s ∧ ∀ j ∈ xs, bs s j = false) ∨
    lastPeak (scan bs upd p s xs) = some p := by
  induction xs generalizing s with
  | nil => left; simp [scan]
  | cons x xs ih =>
    simp only [scan]
    by_cases hb : bs s x = true
    · simp only [hb, ↓reduceIte]
      rcases ih (upd s x p) with ⟨he, _⟩ | h
      · right; rw [he]; exact upd_last s x p
      · right; exact h
    · have hb' : bs s x = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, ↓reduceIte]
      rcases ih s with ⟨he, hall⟩ | h
      · left
        refine ⟨he, fun j hj => ?_⟩
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hb'
        · exact hall j hj
      · right; exact h

theorem mainStep_inv
    (upd_last : ∀ s j p, lastPeak (upd s j p) = some p)
    (noise_last : ∀ s j, lastPeak (noise s j) = lastPeak s)
    (noise_bs : ∀ s j, bs (noise s j) = bs s)
    (s : S) (p nxt : Nat) (hn : nxt ≤ p) (hi : BsInv lastPeak bs s nxt) :
    BsInv lastPeak bs (mainStep upd noise isQ s p) nxt := by
  intro l hl j hlj hj
  unfold mainStep at hl ⊢
  by_cases hq : isQ s p = true
  · simp only [hq, ↓reduceIte, upd_last] at hl
    cases hl; omega
  · have hq' : isQ s p = false := by simpa using hq
    simp only [hq', Bool.false_eq_true, ↓reduceIte, noise_last, noise_bs] at hl ⊢
    exact hi l hl j hlj hj

/-- One step: same state, invariant kept, `nxt ≤ p + 1`. -/
theorem step_exact
    (upd_last : ∀ s j p, lastPeak (upd s j p) = some p)
    (noise_last : ∀ s j, lastPeak (noise s j) = lastPeak s)
    (noise_bs : ∀ s j, bs (noise s j) = bs s)
    (s : S) (p nxt : Nat) (hn : nxt ≤ p) (hi : BsInv lastPeak bs s nxt) :
    let r := newStep lastPeak bs upd noise isQ req (s, nxt) p
    r.1 = oldStep lastPeak bs upd noise isQ req s p ∧ r.2 ≤ p + 1 ∧
      BsInv lastPeak bs r.1 r.2 := by
  have h1 := mainStep_inv lastPeak bs upd noise isQ upd_last noise_last noise_bs
    s p nxt hn hi
  simp only [newStep, oldStep]
  generalize mainStep upd noise isQ s p = s1 at h1 ⊢
  by_cases hr : req s1 p = true
  · simp only [hr, ↓reduceIte]
    cases hl : lastPeak s1 with
    | none =>
      simp only
      exact ⟨trivial, by omega, h1⟩
    | some l =>
      simp only
      -- split old range at a = max (l + 1) nxt
      have hsplit : List.range' (l + 1) (p - l) =
          List.range' (l + 1) (max (l + 1) nxt - (l + 1)) ++
            List.range' (max (l + 1) nxt) (p + 1 - max (l + 1) nxt) := by
        by_cases hlp : l ≤ p
        · obtain ⟨d, hd⟩ : ∃ d, max (l + 1) nxt = l + 1 + d :=
            ⟨max (l + 1) nxt - (l + 1), by omega⟩
          rw [hd, show l + 1 + d - (l + 1) = d by omega]
          have := @List.range'_append (l + 1) d (p + 1 - (l + 1 + d)) 1
          rw [Nat.one_mul] at this
          rw [this]; congr 1; omega
        · rw [show p - l = 0 by omega, show max (l + 1) nxt = l + 1 by omega,
            show p + 1 - (l + 1) = 0 by omega]
          simp
      have hpre : ∀ j ∈ List.range' (l + 1) (max (l + 1) nxt - (l + 1)),
          bs s1 j = false := by
        intro j hj
        rw [List.mem_range'_1] at hj
        exact h1 l hl j (by omega) (by omega)
      rw [hsplit, scan_false bs upd p s1 _ _ hpre]
      refine ⟨rfl, by omega, ?_⟩
      intro l' hl' j hlj hj
      rcases scan_cases lastPeak bs upd upd_last p s1
          (List.range' (max (l + 1) nxt) (p + 1 - max (l + 1) nxt)) with
        ⟨he, hall⟩ | hp
      · rw [he] at hl' ⊢
        rw [hl] at hl'; cases hl'
        by_cases hjn : j < max (l + 1) nxt
        · exact h1 l hl j hlj (by omega)
        · exact hall j (by rw [List.mem_range'_1]; omega)
      · rw [hp] at hl'; cases hl'; omega
  · have hr' : req s1 p = false := by simpa using hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte]
    exact ⟨by simp, by omega, h1⟩

/-- Main theorem: after every peak, the new detector state equals the old one. -/
theorem run_exact
    (upd_last : ∀ s j p, lastPeak (upd s j p) = some p)
    (noise_last : ∀ s j, lastPeak (noise s j) = lastPeak s)
    (noise_bs : ∀ s j, bs (noise s j) = bs s)
    (s : S) (n : Nat) :
    (newRun lastPeak bs upd noise isQ req s n).1 =
      oldRun lastPeak bs upd noise isQ req s n := by
  have key : ∀ n, (newRun lastPeak bs upd noise isQ req s n).1 =
        oldRun lastPeak bs upd noise isQ req s n ∧
      (newRun lastPeak bs upd noise isQ req s n).2 ≤ n ∧
      BsInv lastPeak bs (newRun lastPeak bs upd noise isQ req s n).1
        (newRun lastPeak bs upd noise isQ req s n).2 := by
    intro n
    induction n with
    | zero =>
      refine ⟨rfl, Nat.le_refl 0, ?_⟩
      intro l _ j _ hj; simp [newRun] at hj
    | succ k ih =>
      obtain ⟨he, hle, hi⟩ := ih
      have := step_exact lastPeak bs upd noise isQ req upd_last noise_last noise_bs
        _ k _ hle hi
      simp only [newRun, oldRun]
      rw [← he]
      exact this
  exact (key n).1

end
