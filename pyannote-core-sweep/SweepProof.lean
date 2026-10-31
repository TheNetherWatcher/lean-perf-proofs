/-!
# Sweep-line `Timeline.co_iter` and `Timeline.segmentation` are exact

This file proves that the sweep-line versions of `pyannote.core`'s
`Timeline.co_iter` and `Timeline.segmentation` return *exactly* the same
result as the original nested-loop versions.

Times are modelled as an arbitrary type `α` with Boolean comparisons
`le`, `lt`, `eq` behaving like Python's `<=`, `<`, `==` on non-NaN floats
(a total preorder). Float subtraction `end - SEGMENT_PRECISION` is an
*arbitrary* function, so rounding errors cannot break the proof.

Only Lean core is used (no Mathlib).
-/

namespace Sweep

/-! ## Generic list lemmas -/

/-- On a list sorted by `R`, filtering by a predicate that is closed
downwards under `R` is the same as taking its longest satisfying prefix. -/
theorem filter_eq_takeWhile {α : Type} (R : α → α → Prop) (p : α → Bool)
    (hdown : ∀ a b, R a b → p b = true → p a = true) :
    ∀ l : List α, l.Pairwise R → l.filter p = l.takeWhile p
  | [], _ => rfl
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    cases ha : p a with
    | true => simp [ha,
        filter_eq_takeWhile R p hdown l h.2]
    | false =>
      have hnil : l.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hpb
        have := hdown a b (h.1 b hb) hpb
        rw [ha] at this
        exact Bool.false_ne_true this
      simp [ha, hnil]

theorem takeWhile_idem {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.takeWhile p).takeWhile p = l.takeWhile p
  | [] => rfl
  | a :: l => by
    cases ha : p a with
    | true => simp [ha, takeWhile_idem p l]
    | false => simp [ha]

theorem takeWhile_append_takeWhile {α : Type} (p : α → Bool) :
    ∀ l₁ l₂ : List α,
      (l₁ ++ l₂.takeWhile p).takeWhile p = (l₁ ++ l₂).takeWhile p
  | [], l₂ => by simp [takeWhile_idem]
  | a :: l₁, l₂ => by
    cases ha : p a with
    | true => simp [ha, takeWhile_append_takeWhile p l₁ l₂]
    | false => simp [ha]

theorem takeWhile_append_of_all {α : Type} (p : α → Bool) :
    ∀ l₁ l₂ : List α, (∀ a ∈ l₁, p a = true) →
      (l₁ ++ l₂).takeWhile p = l₁ ++ l₂.takeWhile p
  | [], _, _ => rfl
  | a :: l₁, l₂, h => by
    have ha : p a = true := h a (List.mem_cons_self ..)
    have := takeWhile_append_of_all p l₁ l₂
      (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp [ha, this]

theorem mem_takeWhile_imp {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), a ∈ l.takeWhile p → p a = true
  | [], _, h => by simp at h
  | b :: l, a, h => by
    cases hb : p b with
    | true =>
      simp [hb] at h
      rcases h with rfl | h
      · exact hb
      · exact mem_takeWhile_imp p l a h
    | false => simp [hb] at h

/-! ## Part 1: `co_iter`, generic version

`inter s o` is `segment.intersects(other_segment)`,
`bound s o` is `other_segment <= Segment(segment.end, segment.end)`,
`keep s o` is `other_segment.start >= segment.start`.
-/

section CoIter

variable {σ τ : Type} (inter bound keep : σ → τ → Bool)

/-- Original implementation: for every `segment`, scan every segment of
`other` sorted before `Segment(segment.end, segment.end)` and keep the
intersecting ones. -/
def naive (xs : List σ) (ys : List τ) : List (σ × τ) :=
  xs.flatMap fun s => (ys.filter fun o => bound s o && inter s o).map (s, ·)

/-- Sweep-line implementation. `pending` is `others[pointer:]`.
For each `segment`:
* move segments of `pending` that are `<= temp` to the end of `active`;
* scan the prefix of `active` that is `<= temp` (`break` at the first one
  that is not), yield intersecting ones, and drop the ones that neither
  intersect nor start at or after `segment.start`. -/
def sweep : List σ → List τ → List τ → List (σ × τ)
  | [], _, _ => []
  | s :: xs, active, pending =>
    let act := active ++ pending.takeWhile (bound s)
    let scan := act.takeWhile (bound s)
    let rest := act.dropWhile (bound s)
    (scan.filter (inter s)).map (s, ·) ++
      sweep xs (scan.filter (fun o => inter s o || keep s o) ++ rest)
        (pending.dropWhile (bound s))

theorem sweep_eq_naive_aux (R : τ → τ → Prop) (Q : σ → σ → Prop)
    (hbound : ∀ s a b, R a b → bound s b = true → bound s a = true)
    (hdrop : ∀ s s' o, Q s s' → inter s o = false → keep s o = false →
      inter s' o = false) :
    ∀ (xs : List σ) (ys active pending : List τ),
      xs.Pairwise Q → (active ++ pending).Pairwise R →
      (∀ s ∈ xs, ys.filter (fun o => bound s o && inter s o) =
        (active ++ pending).filter (fun o => bound s o && inter s o)) →
      sweep inter bound keep xs active pending = naive inter bound xs ys
  | [], _, _, _, _, _, _ => by simp [sweep, naive]
  | s :: xs, ys, active, pending, hQ, hR, hF => by
    -- names for the pieces of the state
    have hsplit : (active ++ pending.takeWhile (bound s)) ++
        pending.dropWhile (bound s) = active ++ pending := by
      rw [List.append_assoc, List.takeWhile_append_dropWhile]
    have hparts : (active ++ pending.takeWhile (bound s)).takeWhile (bound s) ++
        (active ++ pending.takeWhile (bound s)).dropWhile (bound s) ++
        pending.dropWhile (bound s) = active ++ pending := by
      rw [List.takeWhile_append_dropWhile, hsplit]
    -- what is yielded for `s` is what the original yields
    have hout : ((active ++ pending.takeWhile (bound s)).takeWhile (bound s)).filter
        (inter s) = ys.filter (fun o => bound s o && inter s o) := by
      have hff : (active ++ pending).filter (fun o => bound s o && inter s o) =
          ((active ++ pending).filter (bound s)).filter (inter s) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro o _
        exact Bool.and_comm ..
      rw [hF s (List.mem_cons_self ..), hff,
        filter_eq_takeWhile R (bound s) (hbound s) _ hR,
        takeWhile_append_takeWhile]
    simp only [sweep, naive, List.flatMap_cons] at *
    rw [hout]
    congr 1
    apply sweep_eq_naive_aux R Q hbound hdrop xs ys
    · exact (List.pairwise_cons.mp hQ).2
    · -- the new state is a sublist of the old one, hence still sorted
      apply List.Pairwise.sublist _ hR
      rw [← hparts, List.append_assoc, List.append_assoc]
      exact (List.filter_sublist).append (List.Sublist.refl _)
    · -- dropped segments can not intersect any later `s'`
      intro s' hs'
      have hQss' : Q s s' := (List.pairwise_cons.mp hQ).1 s' hs'
      rw [hF s' (List.mem_cons_of_mem _ hs'), ← hparts]
      simp only [List.filter_append, List.filter_filter]
      congr 2
      apply List.filter_congr
      intro o _
      cases hi : inter s o <;> cases hk : keep s o
      · simp [hdrop s s' o hQss' hi hk]
      all_goals simp

/-- **Main generic theorem.** If `other` is sorted by `R`, `self` is sorted
by `Q`, `bound s` is closed downwards under `R`, and a segment that neither
intersects `s` nor is kept can not intersect any later segment, then the
sweep returns exactly what the nested loop returns. -/
theorem sweep_eq_naive (R : τ → τ → Prop) (Q : σ → σ → Prop)
    (hbound : ∀ s a b, R a b → bound s b = true → bound s a = true)
    (hdrop : ∀ s s' o, Q s s' → inter s o = false → keep s o = false →
      inter s' o = false)
    (xs : List σ) (ys : List τ) (hQ : xs.Pairwise Q) (hR : ys.Pairwise R) :
    sweep inter bound keep xs [] ys = naive inter bound xs ys :=
  sweep_eq_naive_aux inter bound keep R Q hbound hdrop xs ys [] ys hQ
    (by simpa using hR) (by simp)

end CoIter

/-! ## Part 2: `segmentation`, generic version

For each (nondecreasing) query time `t` (a segment middle), the original
asks whether some support segment `o` with `p t o` (sorted before
`Segment(t, t)` and starting at or before `t`) ends at or after `t`.
The sweep keeps a running maximum of end times instead. -/

section Segmentation

variable {α τ : Type} (le lt : α → α → Bool) (stop : τ → α)
  (p : α → τ → Bool)

/-- Python's `max(m, x)`; `none` plays the role of `-math.inf`. -/
def omax : Option α → α → Option α
  | none, x => some x
  | some m, x => if lt m x then some x else some m

/-- `max_end >= t`. -/
def oge : Option α → α → Bool
  | none, _ => false
  | some m, t => le t m

def segNaive (ts : List α) (ys : List τ) : List Bool :=
  ts.map fun t => ys.any fun o => p t o && le t (stop o)

def segSweep : List α → Option α → List τ → List Bool
  | [], _, _ => []
  | t :: ts, m, pending =>
    let m' := (pending.takeWhile (p t)).foldl (fun acc o => omax lt acc (stop o)) m
    oge le m' t :: segSweep ts m' (pending.dropWhile (p t))

variable (le_trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
  (le_total : ∀ a b, le a b = true ∨ le b a = true)
  (lt_iff : ∀ a b, lt a b = !(le b a))

include le_trans le_total lt_iff in
theorem oge_omax (m : Option α) (x t : α) :
    oge le (omax lt m x) t = (oge le m t || le t x) := by
  cases m with
  | none => simp [omax, oge]
  | some m =>
    simp only [omax]
    cases hl : lt m x with
    | true =>
      have hmx : le m x = true := by
        rw [lt_iff] at hl
        cases le_total m x with
        | inl h => exact h
        | inr h => simp [h] at hl
      simp only [ite_true, oge]
      cases htm : le t m with
      | true => simp [le_trans _ _ _ htm hmx]
      | false => simp
    | false =>
      have hxm : le x m = true := by simpa [lt_iff] using hl
      simp only [Bool.false_eq_true, ite_false, oge]
      cases htx : le t x with
      | true => simp [le_trans _ _ _ htx hxm]
      | false => simp

include le_trans le_total lt_iff in
theorem oge_foldl (t : α) :
    ∀ (l : List τ) (m : Option α),
      oge le (l.foldl (fun acc o => omax lt acc (stop o)) m) t =
        (oge le m t || l.any fun o => le t (stop o))
  | [], m => by simp
  | o :: l, m => by
    simp only [List.foldl_cons, List.any_cons]
    rw [oge_foldl t l, oge_omax le lt le_trans le_total lt_iff, Bool.or_assoc]

include le_trans le_total lt_iff in
theorem segSweep_eq_aux (R : τ → τ → Prop)
    (hdown : ∀ t a b, R a b → p t b = true → p t a = true) :
    ∀ (ts : List α) (consumed pending : List τ) (m : Option α),
      ts.Pairwise (fun t t' => ∀ o, p t o = true → p t' o = true) →
      (consumed ++ pending).Pairwise R →
      (∀ t ∈ ts, ∀ o ∈ consumed, p t o = true) →
      (∀ t, oge le m t = consumed.any fun o => le t (stop o)) →
      segSweep le lt stop p ts m pending =
        segNaive le stop p ts (consumed ++ pending)
  | [], _, _, _, _, _, _, _ => by simp [segSweep, segNaive]
  | t :: ts, consumed, pending, m, hmono, hR, hcons, hm => by
    have hcons_t : ∀ o ∈ consumed, p t o = true := hcons t (List.mem_cons_self ..)
    simp only [segSweep, segNaive, List.map_cons]
    congr 1
    · -- the answer for `t`
      rw [oge_foldl le lt stop le_trans le_total lt_iff, hm]
      have hany : ((consumed ++ pending).any fun o => p t o && le t (stop o)) =
          ((consumed ++ pending).filter (p t)).any fun o => le t (stop o) := by
        rw [List.any_filter]
      rw [hany, filter_eq_takeWhile R (p t) (hdown t) _ hR,
        takeWhile_append_of_all _ _ _ hcons_t, List.any_append]
    · -- the remaining answers
      have := segSweep_eq_aux R hdown ts (consumed ++ pending.takeWhile (p t))
        (pending.dropWhile (p t))
        ((pending.takeWhile (p t)).foldl (fun acc o => omax lt acc (stop o)) m)
        (List.pairwise_cons.mp hmono).2
        (by rw [List.append_assoc, List.takeWhile_append_dropWhile]; exact hR)
        (by
          intro t' ht' o ho
          have hmono_t := (List.pairwise_cons.mp hmono).1 t' ht'
          rcases List.mem_append.mp ho with ho | ho
          · exact hcons t' (List.mem_cons_of_mem _ ht') o ho
          · exact hmono_t o (mem_takeWhile_imp _ _ _ ho))
        (by
          intro t'
          rw [oge_foldl le lt stop le_trans le_total lt_iff, hm, List.any_append])
      rw [this, List.append_assoc, List.takeWhile_append_dropWhile]
      rfl

include le_trans le_total lt_iff in
/-- **Main generic theorem for `segmentation`.** -/
theorem segSweep_eq_segNaive (R : τ → τ → Prop)
    (hdown : ∀ t a b, R a b → p t b = true → p t a = true)
    (ts : List α) (ys : List τ)
    (hmono : ts.Pairwise (fun t t' => ∀ o, p t o = true → p t' o = true))
    (hR : ys.Pairwise R) :
    segSweep le lt stop p ts none ys = segNaive le stop p ts ys := by
  have := segSweep_eq_aux le lt stop p le_trans le_total lt_iff R hdown ts [] ys none
    hmono (by simpa using hR) (by simp) (by simp [oge])
  simpa using this

end Segmentation

/-! ## Part 3: the concrete pyannote definitions -/

/-- Comparisons on times, as Python's `<=`, `<`, `==` on non-NaN floats. -/
structure TimeOrder (α : Type) where
  le : α → α → Bool
  lt : α → α → Bool
  eq : α → α → Bool
  le_refl : ∀ a, le a a = true
  le_trans : ∀ a b c, le a b = true → le b c = true → le a c = true
  le_total : ∀ a b, le a b = true ∨ le b a = true
  lt_iff : ∀ a b, lt a b = !(le b a)
  eq_iff : ∀ a b, eq a b = (le a b && le b a)

structure Seg (α : Type) where
  start : α
  stop : α

namespace TimeOrder

variable {α : Type} (O : TimeOrder α)

/-- `Segment.__le__` from `@dataclass(order=True)`: Python compares the
tuples `(start, end)`, i.e. finds the first field that is not `==` and
compares it with `<=`. -/
def segLe (a b : Seg α) : Bool :=
  if O.eq a.start b.start then O.le a.stop b.stop else O.le a.start b.start

/-- `Segment.intersects`, with `sub x` standing for the float
computation `x - SEGMENT_PRECISION` (any function at all). -/
def intersects (sub : α → α) (s o : Seg α) : Bool :=
  (O.lt s.start o.start && O.lt o.start (sub s.stop)) ||
    (O.lt o.start s.start && O.lt s.start (sub o.stop)) ||
    O.eq s.start o.start

theorem le_of_eq {a b : α} (h : O.eq a b = true) : O.le a b = true := by
  rw [O.eq_iff] at h; simp at h; exact h.1

theorem ge_of_eq {a b : α} (h : O.eq a b = true) : O.le b a = true := by
  rw [O.eq_iff] at h; simp at h; exact h.2

theorem eq_of_le_le {a b : α} (h1 : O.le a b = true) (h2 : O.le b a = true) :
    O.eq a b = true := by
  rw [O.eq_iff]; simp [h1, h2]

theorem start_le_of_segLe {a b : Seg α} (h : O.segLe a b = true) :
    O.le a.start b.start = true := by
  unfold segLe at h
  split at h
  · exact O.le_of_eq (by assumption)
  · exact h

theorem segLe_trans {a b c : Seg α} (hab : O.segLe a b = true)
    (hbc : O.segLe b c = true) : O.segLe a c = true := by
  have hab' := O.start_le_of_segLe hab
  have hbc' := O.start_le_of_segLe hbc
  have hac' := O.le_trans _ _ _ hab' hbc'
  unfold segLe at hab hbc ⊢
  by_cases e1 : O.eq a.start b.start = true <;>
    by_cases e2 : O.eq b.start c.start = true <;>
    by_cases e3 : O.eq a.start c.start = true <;>
    simp only [e1, e2, e3, ite_true, ite_false, Bool.false_eq_true] at hab hbc ⊢
  · exact O.le_trans _ _ _ hab hbc
  · exact absurd (O.eq_of_le_le hac' (O.le_trans _ _ _ (O.ge_of_eq e2)
      (O.ge_of_eq e1))) e3
  · exact absurd (O.eq_of_le_le hbc' (O.le_trans _ _ _ (O.ge_of_eq e3)
      (O.le_of_eq e1))) e2
  · exact hac'
  · exact absurd (O.eq_of_le_le hab' (O.le_trans _ _ _ (O.le_of_eq e2)
      (O.ge_of_eq e3))) e1
  · exact hac'
  · exact absurd (O.eq_of_le_le hab' (O.le_trans _ _ _ hbc' (O.ge_of_eq e3))) e1
  · exact hac'

/-- The key fact behind dropping candidates: a segment `o` of `other`
that starts before `s` and does not intersect `s` can not intersect any
later segment `s'` of `self`. Holds for *any* `sub`, i.e. regardless of
how `end - SEGMENT_PRECISION` is rounded. -/
theorem drop_ok (sub : α → α) (s s' o : Seg α)
    (hss' : O.segLe s s' = true)
    (hi : O.intersects sub s o = false)
    (hk : O.le s.start o.start = false) :
    O.intersects sub s' o = false := by
  have h1 : O.le s.start s'.start = true := O.start_le_of_segLe hss'
  have hlt : O.lt o.start s.start = true := by rw [O.lt_iff, hk]; rfl
  -- from `¬ intersects s o`: `sub o.stop <= s.start`
  have h2 : O.le (sub o.stop) s.start = true := by
    unfold intersects at hi
    simp only [hlt, Bool.true_and, Bool.or_eq_false_iff] at hi
    have := hi.1.2
    rw [O.lt_iff] at this
    simpa using this
  have hos : O.le o.start s.start = true := by
    cases O.le_total o.start s.start with
    | inl h => exact h
    | inr h => rw [hk] at h; exact absurd h Bool.false_ne_true
  unfold intersects
  -- case A: `s'.start < o.start` is impossible
  have hA : O.lt s'.start o.start = false := by
    rw [O.lt_iff]; simp [O.le_trans _ _ _ hos h1]
  -- case B: `s'.start < o.end - P` is impossible
  have hB : O.lt s'.start (sub o.stop) = false := by
    rw [O.lt_iff]; simp [O.le_trans _ _ _ h2 h1]
  -- case C: `s'.start == o.start` is impossible
  have hC : O.eq s'.start o.start = false := by
    cases he : O.eq s'.start o.start with
    | false => rfl
    | true =>
      have := O.le_trans _ _ _ h1 (O.le_of_eq he)
      rw [hk] at this
      exact absurd this Bool.false_ne_true
  simp [hA, hB, hC]

/-- **`co_iter` is exact.** For timelines sorted as `SortedList`s of
segments, the sweep returns exactly what the original nested loop
returns — same pairs, same order. `temp s` is whatever
`Segment(segment.end, segment.end)` evaluates to (rounding included). -/
theorem co_iter_exact (sub : α → α) (temp : Seg α → Seg α)
    (xs ys : List (Seg α))
    (hxs : xs.Pairwise fun a b => O.segLe a b = true)
    (hys : ys.Pairwise fun a b => O.segLe a b = true) :
    sweep (O.intersects sub) (fun s o => O.segLe o (temp s))
        (fun s o => O.le s.start o.start) xs [] ys =
      naive (O.intersects sub) (fun s o => O.segLe o (temp s)) xs ys :=
  sweep_eq_naive (O.intersects sub) (fun s o => O.segLe o (temp s))
    (fun s o => O.le s.start o.start) (fun a b => O.segLe a b = true)
    (fun a b => O.segLe a b = true)
    (fun _ _ _ hab hb => O.segLe_trans hab hb)
    (fun s s' o hss' hi hk => O.drop_ok sub s s' o hss' hi hk)
    xs ys hxs hys

/-- **`segmentation` is exact.** For each nondecreasing segment middle
`t`, the running-maximum sweep answers exactly what the original
`support.overlapping(t)` check answers. `boundary t` is whatever
`Segment(t, t)` evaluates to, assumed monotone in `t` (rounding is). -/
theorem segmentation_exact (boundary : α → Seg α)
    (hboundary : ∀ t t', O.le t t' = true →
      O.segLe (boundary t) (boundary t') = true)
    (ts : List α) (support : List (Seg α))
    (hts : ts.Pairwise fun t t' => O.le t t' = true)
    (hsupport : support.Pairwise fun a b => O.segLe a b = true) :
    segSweep O.le O.lt Seg.stop
        (fun t o => O.segLe o (boundary t) && O.le o.start t) ts none support =
      ts.map fun t => support.any fun o =>
        O.segLe o (boundary t) && (O.le o.start t && O.le t o.stop) := by
  have := segSweep_eq_segNaive O.le O.lt Seg.stop
    (fun t o => O.segLe o (boundary t) && O.le o.start t)
    O.le_trans O.le_total O.lt_iff (fun a b => O.segLe a b = true)
    (by
      intro t a b hab hb
      simp only [Bool.and_eq_true] at hb ⊢
      exact ⟨O.segLe_trans hab hb.1,
        O.le_trans _ _ _ (O.start_le_of_segLe hab) hb.2⟩)
    ts support
    (by
      apply List.Pairwise.imp _ hts
      intro t t' htt' o ho
      simp only [Bool.and_eq_true] at ho ⊢
      exact ⟨O.segLe_trans ho.1 (hboundary t t' htt'),
        O.le_trans _ _ _ ho.2 htt'⟩)
    hsupport
  rw [this]
  simp [segNaive, Bool.and_assoc]

end TimeOrder

end Sweep
