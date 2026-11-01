/-
pretty-midi `Instrument.remove_invalid_notes` and `Instrument.synthesize`.

1. `remove_invalid_notes` used to collect the invalid notes and then call
   `list.remove` on each one. It now keeps the valid notes with one filter.
   Notes compare by identity, so a note is an element of a type with decidable
   equality and `bad` says whether it is invalid (`end <= start`).

2. `synthesize` used to scan every pitch bend for every note and keep the ones
   with `start < bend_sample < end`. It now slices the sorted list of bend
   samples between `bisect_right(start)` and `bisect_left(end)`. The loop body
   is unchanged, so it is enough to show both visit the same samples in the
   same order.
-/

/-! ## 1. remove_invalid_notes -/

/-- Old code: `for note in [n for n in notes if bad n]: notes.remove(note)`. -/
def removeOld {α : Type} [DecidableEq α] (bad : α → Bool) (l : List α) : List α :=
  (l.filter bad).foldl (fun acc d => acc.erase d) l

/-- New code: `notes[:] = [n for n in notes if not bad n]`. -/
def removeNew {α : Type} (bad : α → Bool) (l : List α) : List α :=
  l.filter (fun x => !bad x)

theorem foldl_erase_cons {α : Type} [DecidableEq α] (a : α) :
    ∀ (ds t : List α), a ∉ ds →
      ds.foldl (fun acc d => acc.erase d) (a :: t)
        = a :: ds.foldl (fun acc d => acc.erase d) t
  | [], _, _ => rfl
  | d :: ds, t, h => by
    have had : a ≠ d := fun e => h (e ▸ List.mem_cons_self)
    have hds : a ∉ ds := fun m => h (List.mem_cons_of_mem _ m)
    simp only [List.foldl_cons]
    rw [List.erase_cons_tail (by simpa using had)]
    exact foldl_erase_cons a ds _ hds

/-- Removing the invalid notes one by one gives the filtered list, including
    when the same note object appears more than once. -/
theorem remove_exact {α : Type} [DecidableEq α] (bad : α → Bool) :
    ∀ l : List α, removeOld bad l = removeNew bad l
  | [] => rfl
  | a :: t => by
    have ih := remove_exact bad t
    unfold removeOld removeNew at *
    cases h : bad a
    · have hn : a ∉ t.filter bad := by
        intro m; rw [List.mem_filter] at m; rw [h] at m; exact absurd m.2 (by decide)
      simp only [List.filter_cons, h, Bool.not_false, ite_true]
      simp only [Bool.false_eq_true, ite_false]
      rw [foldl_erase_cons a _ t hn, ih]
    · simp only [List.filter_cons, h, ite_true, List.foldl_cons, List.erase_cons_head,
        Bool.not_true, Bool.false_eq_true, ite_false]
      exact ih

/-! ## 2. synthesize: bend selection -/

/-- Python `bisect_right(xs, s)` on a sorted list: number of leading `≤ s`. -/
def bisectRight (xs : List Int) (s : Int) : Nat := (xs.takeWhile (fun x => decide (x ≤ s))).length

/-- Python `bisect_left(xs, e)` on a sorted list: number of leading `< e`. -/
def bisectLeft (xs : List Int) (e : Int) : Nat := (xs.takeWhile (fun x => decide (x < e))).length

/-- Python `xs[lo:hi]` for `0 ≤ lo, hi ≤ len(xs)`; empty when `hi < lo`. -/
def slice (xs : List Int) (lo hi : Nat) : List Int := (xs.drop lo).take (hi - lo)

/-- Old code: every bend sample with `start < b < end`, in list order. -/
def bendsOld (xs : List Int) (s e : Int) : List Int :=
  xs.filter (fun b => decide (b > s) && decide (b < e))

/-- New code: the bisected slice. -/
def bendsNew (xs : List Int) (s e : Int) : List Int :=
  slice xs (bisectRight xs s) (bisectLeft xs e)

def Sorted (xs : List Int) : Prop := xs.Pairwise (· ≤ ·)

theorem filter_nil_of_ge (e a : Int) (hae : ¬ a < e) (p : Int → Bool)
    (t : List Int) (ht : ∀ x ∈ t, a ≤ x) :
    t.filter (fun b => p b && decide (b < e)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  have : ¬ x < e := fun h => hae (Int.lt_of_le_of_lt (ht x hx) h)
  simp [this]

/-- Taking the leading `< e` run of a sorted list = filtering by `< e`,
    and adding a condition that holds on every element changes nothing. -/
theorem take_lt (s e : Int) :
    ∀ xs : List Int, Sorted xs → (∀ x ∈ xs, s < x) →
      xs.take (bisectLeft xs e) = bendsOld xs s e
  | [], _, _ => rfl
  | a :: t, hs, hpos => by
    have hst : Sorted t := (List.pairwise_cons.mp hs).2
    have hat : ∀ x ∈ t, a ≤ x := (List.pairwise_cons.mp hs).1
    have hsa : s < a := hpos a List.mem_cons_self
    have ht : ∀ x ∈ t, s < x := fun x m => hpos x (List.mem_cons_of_mem _ m)
    unfold bisectLeft bendsOld
    by_cases hae : a < e
    · have ih := take_lt s e t hst ht
      unfold bisectLeft bendsOld at ih
      simp [hae, hsa, ih]
    · have hnil := filter_nil_of_ge e a hae (fun b => decide (b > s)) t hat
      simp [hae, hnil]

theorem bends_exact (s e : Int) :
    ∀ xs : List Int, Sorted xs → bendsNew xs s e = bendsOld xs s e
  | [], _ => rfl
  | a :: t, hs => by
    have hst : Sorted t := (List.pairwise_cons.mp hs).2
    have hat : ∀ x ∈ t, a ≤ x := (List.pairwise_cons.mp hs).1
    by_cases has : a ≤ s
    · have ih := bends_exact s e t hst
      unfold bendsNew slice bisectRight bisectLeft bendsOld at *
      by_cases hae : a < e
      · have hns : ¬ a > s := Int.not_lt.mpr has
        simp [has, hae, hns, ih, Nat.add_sub_add_right]
      · have hnil := filter_nil_of_ge e a hae (fun b => decide (b > s)) t hat
        have hns : ¬ a > s := Int.not_lt.mpr has
        simp [has, hae, hns, hnil]
    · have hsa : s < a := Int.lt_of_not_ge has
      have hpos : ∀ x ∈ a :: t, s < x := by
        intro x m
        cases List.mem_cons.mp m with
        | inl h => exact h ▸ hsa
        | inr h => exact Int.lt_of_lt_of_le hsa (hat x h)
      have key := take_lt s e (a :: t) hs hpos
      unfold bendsNew slice bisectRight
      simp only [List.takeWhile_cons, has, decide_false]
      exact key

/-- `int(t * fs)` of times sorted ascending is sorted, so the hypothesis holds
    for the list the new code builds. The loop body runs once per element of
    the selected list, so equal lists give equal output. -/
theorem synth_bends_exact (xs : List Int) (hs : Sorted xs) (s e : Int) :
    bendsNew xs s e = bendsOld xs s e := bends_exact s e xs hs

#print axioms remove_exact
#print axioms synth_bends_exact
