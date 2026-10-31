/-!
# Biopython `Bio.Nexus.Nexus.CharBuffer`: list buffer vs text + cursor

Old: the unread input is a list `l`; reads pop from its front.
New: the whole text `t` plus an index `p`; reads advance `p`.

Invariant: `l = t.drop p`. Every primitive returns the same value on both
sides and keeps the invariant, so any sequence of calls (which is all
`next_word` and `next_nonwhitespace` are) behaves identically: `run_exact`.

Characters are an arbitrary type with decidable equality; whitespace tests
are arbitrary predicates, so nothing depends on which characters count.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CharBuffer

variable {α : Type} [DecidableEq α]

/-- Python slice `t[a:b]`. -/
def slice (t : List α) (a b : Nat) : List α := (t.take b).drop a

/-! ## Primitives, old (list) and new (text + cursor) -/

def oldNext : List α → Option α × List α
  | [] => (none, [])
  | c :: r => (some c, r)

def newNext (t : List α) (p : Nat) : Option α × Nat :=
  if h : p < t.length then (some t[p], p + 1) else (none, p)

/-- `str.strip()` with whitespace predicate `ws`. -/
def strip (ws : α → Bool) (l : List α) : List α :=
  ((l.dropWhile ws).reverse.dropWhile ws).reverse

def oldPeekNW (ws : α → Bool) (l : List α) : Option α := (strip ws l).head?

/-- `while pos < len(text) and text[pos].isspace(): pos += 1` -/
def scanWs (ws : α → Bool) (t : List α) (p : Nat) : Nat :=
  if h : p < t.length then
    if ws t[p] then scanWs ws t (p + 1) else p
  else p
termination_by t.length - p

def newPeekNW (ws : α → Bool) (t : List α) (p : Nat) : Option α := t[scanWs ws t p]?

/-- `while self.buffer[0] in WHITESPACE: self.buffer = self.buffer[1:]`;
    `error` is the `IndexError` on an exhausted buffer. -/
def oldSkip (ws : α → Bool) : List α → Except Unit (List α)
  | [] => .error ()
  | c :: r => if ws c then oldSkip ws r else .ok (c :: r)

def newSkip (ws : α → Bool) (t : List α) (p : Nat) : Except Unit Nat :=
  if h : p < t.length then
    if ws t[p] then newSkip ws t (p + 1) else .ok p
  else .error ()
termination_by t.length - p

/-- One target character of `next_until`: `list.index` + split. -/
def oldUntil (c : α) (l : List α) : Option (List α × List α) :=
  if c ∈ l then some (l.take (l.idxOf c), l.drop (l.idxOf c)) else none

/-- `str.find(c, p)`. -/
def findFrom (c : α) (t : List α) (p : Nat) : Option Nat :=
  if h : p < t.length then
    if t[p] = c then some p else findFrom c t (p + 1)
  else none
termination_by t.length - p

def newUntil (c : α) (t : List α) (p : Nat) : Option (List α × Nat) :=
  match findFrom c t p with
  | some q => some (slice t p q, q)
  | none => none

/-! ## Per-primitive lemmas -/

theorem drop_eq_cons {t : List α} {p : Nat} (h : p < t.length) :
    t.drop p = t[p] :: t.drop (p + 1) := by
  rw [List.drop_eq_getElem_cons h]

theorem drop_eq_nil {t : List α} {p : Nat} (h : ¬ p < t.length) : t.drop p = [] := by
  simp; omega

theorem peek_exact (t : List α) (p : Nat) : (t.drop p).head? = t[p]? := by
  by_cases h : p < t.length
  · rw [drop_eq_cons h]; simp [h]
  · rw [drop_eq_nil h]; simp; omega

theorem next_exact (t : List α) (p : Nat) :
    oldNext (t.drop p) = ((newNext t p).1, t.drop (newNext t p).2) := by
  unfold newNext
  by_cases h : p < t.length
  · rw [drop_eq_cons h]; simp [h, oldNext]
  · rw [drop_eq_nil h]; simp [h, oldNext, Nat.not_lt.mp h]

theorem rest_exact (t : List α) (p : Nat) : t.drop p = slice t p t.length := by
  simp [slice]

theorem peekWord_exact (t w : List α) (p : Nat) :
    (t.drop p).take w.length = slice t p (p + w.length) := by
  simp [slice, List.drop_take]

theorem scanWs_spec (ws : α → Bool) (t : List α) (p : Nat) :
    (t.drop p).dropWhile ws = t.drop (scanWs ws t p) := by
  unfold scanWs
  by_cases h : p < t.length
  · simp only [h, dite_true]
    rw [drop_eq_cons h]
    by_cases hw : ws t[p]
    · simp [List.dropWhile, hw, scanWs_spec ws t (p + 1)]
    · simp only [List.dropWhile, hw]; rw [← drop_eq_cons h]; simp [hw]
  · rw [drop_eq_nil h]; simp [h, Nat.not_lt.mp h]
termination_by t.length - p

theorem dropWhile_head (ws : α → Bool) :
    ∀ (l r : List α) (c : α), l.dropWhile ws = c :: r → ws c = false
  | [], r, c, hd => by simp at hd
  | x :: l, r, c, hd => by
    by_cases hx : ws x
    · simp [List.dropWhile, hx] at hd; exact dropWhile_head ws l r c hd
    · simp [List.dropWhile, hx] at hd; obtain ⟨rfl, -⟩ := hd; simpa using hx

/-- The head of `strip l` is the head of `dropWhile ws l`: trailing strip
    never removes the first non-whitespace character. -/
theorem strip_head (ws : α → Bool) (l : List α) :
    (strip ws l).head? = (l.dropWhile ws).head? := by
  unfold strip
  generalize hd : l.dropWhile ws = d
  cases d with
  | nil => simp
  | cons c r =>
    have hc : ws c = false := dropWhile_head ws l r c hd
    -- reverse of (c :: r) ends with c, and c survives dropWhile ws
    have key : ∀ m : List α, ∃ m', (m ++ [c]).dropWhile ws = m' ++ [c] := by
      intro m
      induction m with
      | nil => exact ⟨[], by simp [List.dropWhile, hc]⟩
      | cons x m ih =>
        by_cases hx : ws x
        · simpa [List.dropWhile, hx] using ih
        · exact ⟨x :: m, by simp [List.dropWhile, hx]⟩
    obtain ⟨m', hm'⟩ := key r.reverse
    simp [List.reverse_cons, hm']

theorem peekNW_exact (ws : α → Bool) (t : List α) (p : Nat) :
    oldPeekNW ws (t.drop p) = newPeekNW ws t p := by
  simp [oldPeekNW, newPeekNW, strip_head, scanWs_spec, peek_exact]

theorem skip_exact (ws : α → Bool) (t : List α) (p : Nat) :
    oldSkip ws (t.drop p) = (newSkip ws t p).map (t.drop ·) := by
  unfold newSkip
  by_cases h : p < t.length
  · simp only [h, dite_true]
    rw [drop_eq_cons h]
    by_cases hw : ws t[p]
    · simp [oldSkip, hw, skip_exact ws t (p + 1)]
    · simp only [oldSkip, hw]; rw [← drop_eq_cons h]; simp [hw, Except.map]
  · rw [drop_eq_nil h]; simp [h, oldSkip, Except.map]
termination_by t.length - p

theorem findFrom_spec (c : α) (t : List α) (p : Nat) :
    findFrom c t p =
      if c ∈ t.drop p then some (p + (t.drop p).idxOf c) else none := by
  unfold findFrom
  by_cases h : p < t.length
  · simp only [h, dite_true]
    rw [drop_eq_cons h]
    by_cases hc : t[p] = c
    · simp [hc, List.idxOf_cons_self]
    · rw [findFrom_spec c t (p + 1)]
      have hne : (t[p] == c) = false := by simpa using hc
      by_cases hm : c ∈ t.drop (p + 1)
      · simp only [hm, ite_true, List.mem_cons, or_true, List.idxOf_cons, hne,
          Bool.cond_false]
        simp [hc]; omega
      · simp only [hm, ite_false, List.mem_cons, or_false]
        have hc' : ¬ c = t[p] := fun e => hc e.symm
        simp [hc, hc']
  · rw [drop_eq_nil h]; simp [h, Nat.not_lt.mp h]
termination_by t.length - p

theorem until_exact (c : α) (t : List α) (p : Nat) :
    oldUntil c (t.drop p) =
      (newUntil c t p).map (fun r => (r.1, t.drop r.2)) := by
  unfold oldUntil newUntil
  rw [findFrom_spec]
  by_cases hm : c ∈ t.drop p
  · simp [hm, slice, List.drop_take, List.drop_drop]
  · simp [hm]

/-! ## Any sequence of calls -/

inductive Op (α : Type)
  | peek | next | rest
  | peekNW (ws : α → Bool)
  | skip (ws : α → Bool)
  | untilC (c : α)
  | peekWord (w : List α)

inductive Out (α : Type)
  | ch (c : Option α)
  | str (s : List α)
  | bool (b : Bool)
  | found (s : Option (List α))
  | err

def stepOld : Op α → List α → Out α × List α
  | .peek, l => (.ch l.head?, l)
  | .next, l => ((Out.ch (oldNext l).1), (oldNext l).2)
  | .rest, l => (.str l, l)
  | .peekNW ws, l => (.ch (oldPeekNW ws l), l)
  | .skip ws, l =>
    match oldSkip ws l with
    | .ok l' => (.bool true, l')
    | .error _ => (.err, l)
  | .untilC c, l =>
    match oldUntil c l with
    | some (s, l') => (.found (some s), l')
    | none => (.found none, l)
  | .peekWord w, l => (.bool (l.take w.length == w), l)

def stepNew (t : List α) : Op α → Nat → Out α × Nat
  | .peek, p => (.ch t[p]?, p)
  | .next, p => (.ch (newNext t p).1, (newNext t p).2)
  | .rest, p => (.str (slice t p t.length), p)
  | .peekNW ws, p => (.ch (newPeekNW ws t p), p)
  | .skip ws, p =>
    match newSkip ws t p with
    | .ok p' => (.bool true, p')
    | .error _ => (.err, p)
  | .untilC c, p =>
    match newUntil c t p with
    | some (s, p') => (.found (some s), p')
    | none => (.found none, p)
  | .peekWord w, p => (.bool (slice t p (p + w.length) == w), p)

theorem step_exact (t : List α) (p : Nat) (op : Op α) :
    stepOld op (t.drop p) =
      ((stepNew t op p).1, t.drop (stepNew t op p).2) := by
  cases op with
  | peek => simp [stepOld, stepNew, peek_exact]
  | next => simp [stepOld, stepNew, next_exact]
  | rest => simp [stepOld, stepNew, rest_exact]
  | peekNW ws => simp [stepOld, stepNew, peekNW_exact]
  | skip ws =>
    simp only [stepOld, stepNew, skip_exact]
    cases newSkip ws t p <;> rfl
  | untilC c =>
    simp only [stepOld, stepNew, until_exact]
    cases newUntil c t p with
    | none => rfl
    | some r => rfl
  | peekWord w => simp [stepOld, stepNew, peekWord_exact]

def runOld : List (Op α) → List α → List (Out α)
  | [], _ => []
  | op :: ops, l => (stepOld op l).1 :: runOld ops (stepOld op l).2

def runNew (t : List α) : List (Op α) → Nat → List (Out α)
  | [], _ => []
  | op :: ops, p => (stepNew t op p).1 :: runNew t ops (stepNew t op p).2

/-- Main result: starting from the same text, any sequence of buffer calls
    returns the same values in the old and new implementation. -/
theorem run_exact (t : List α) (ops : List (Op α)) (p : Nat) :
    runOld ops (t.drop p) = runNew t ops p := by
  induction ops generalizing p with
  | nil => rfl
  | cons op ops ih =>
    simp only [runOld, runNew, step_exact, ih]

theorem run_exact_init (t : List α) (ops : List (Op α)) :
    runOld ops t = runNew t ops 0 := by
  simpa using run_exact t ops 0

end CharBuffer
