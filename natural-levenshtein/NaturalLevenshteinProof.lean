/-!
NaturalNode/natural PR #798: storage and spellcheck loop equivalences.
The distance proof assumes only a right identity for addition; `min3` is arbitrary.
-/

namespace NaturalLevenshteinProof

/-! ## Plain Levenshtein distance -/

variable {α β : Type} [DecidableEq β] [Zero α] [Add α]

/-- The old and new code both build row zero by repeated addition. -/
def initialRow (ins : α) : List β → α → List α
  | [], value => [value]
  | _ :: rest, value => value :: initialRow ins rest (value + ins)

/-- One old matrix row, retaining the old conditional substitution operation. -/
def oldCells (min3 : α → α → α → α) (ins del sub : α) (source : β)
    (target : List β) (previous : List α) (column : Nat) (current : List α) : List α :=
  match target with
  | [] => current
  | char :: rest =>
    let insertion := current.getD column 0 + ins
    let deletion := previous.getD (column + 1) 0 + del
    let diagonal := previous.getD column 0
    let substitution := if source = char then diagonal else diagonal + sub
    let cell := min3 insertion deletion substitution
    oldCells min3 ins del sub source rest previous (column + 1) (current ++ [cell])

/-- One new two-row update: same cell arithmetic, but reads only the previous row. -/
def newCells (min3 : α → α → α → α) (ins del sub : α) (source : β)
    (target : List β) (previous : List α) (column : Nat) (current : List α) : List α :=
  match target with
  | [] => current
  | char :: rest =>
    let insertion := current.getD column 0 + ins
    let deletion := previous.getD (column + 1) 0 + del
    let diagonal := previous.getD column 0
    let substitution := if source = char then diagonal else diagonal + sub
    let cell := min3 insertion deletion substitution
    newCells min3 ins del sub source rest previous (column + 1) (current ++ [cell])

def oldRow (min3 : α → α → α → α) (ins del sub : α) (source : β)
    (target : List β) (previous : List α) : List α :=
  oldCells min3 ins del sub source target previous 0 [previous.getD 0 0 + del]

def newRow (min3 : α → α → α → α) (ins del sub : α) (source : β)
    (target : List β) (previous : List α) : List α :=
  newCells min3 ins del sub source target previous 0 [previous.getD 0 0 + del]

omit [DecidableEq β] [Zero α] in
theorem initialRow_length (ins : α) (target : List β) (value : α) :
    (initialRow ins target value).length = target.length + 1 := by
  induction target generalizing value with
  | nil => rfl
  | cons _ rest ih => simp [initialRow, ih]

theorem oldCells_length (min3 : α → α → α → α) (ins del sub : α) (source : β)
    (target : List β) (previous : List α) (column : Nat) (current : List α) :
    (oldCells min3 ins del sub source target previous column current).length =
      current.length + target.length := by
  induction target generalizing column current with
  | nil => simp [oldCells]
  | cons _ rest ih =>
    simp only [oldCells]
    rw [ih]
    simp [List.length_append] <;> omega

theorem newCells_length (min3 : α → α → α → α) (ins del sub : α) (source : β)
    (target : List β) (previous : List α) (column : Nat) (current : List α) :
    (newCells min3 ins del sub source target previous column current).length =
      current.length + target.length := by
  induction target generalizing column current with
  | nil => simp [newCells]
  | cons _ rest ih =>
    simp only [newCells]
    rw [ih]
    simp [List.length_append] <;> omega

theorem oldRow_length (min3 : α → α → α → α) (ins del sub : α) (source : β)
    (target : List β) (previous : List α) :
    (oldRow min3 ins del sub source target previous).length = target.length + 1 := by
  simp [oldRow, oldCells_length]
  omega

theorem newRow_length (min3 : α → α → α → α) (ins del sub : α) (source : β)
    (target : List β) (previous : List α) :
    (newRow min3 ins del sub source target previous).length = target.length + 1 := by
  simp [newRow, newCells_length]
  omega

theorem cells_equal (min3 : α → α → α → α) (ins del sub : α) (source : β)
    (target : List β) (previous : List α) (column : Nat) (current : List α) :
    newCells min3 ins del sub source target previous column current =
      oldCells min3 ins del sub source target previous column current := by
  induction target generalizing column current with
  | nil => rfl
  | cons char rest ih =>
    simp only [newCells, oldCells]
    by_cases h : source = char
    · simp [h] at *
      exact ih _ _
    · simp [h] at *
      exact ih _ _

theorem row_equal (min3 : α → α → α → α) (ins del sub : α) (source : β)
    (target : List β) (previous : List α) :
    newRow min3 ins del sub source target previous =
      oldRow min3 ins del sub source target previous := by
  exact cells_equal min3 ins del sub source target previous 0 _

/-- All rows of the original matrix, in order. -/
def fullMatrix (min3 : α → α → α → α) (ins del sub : α)
    (source target : List β) : List (List α) :=
  source.foldl (fun matrix char =>
    matrix ++ [oldRow min3 ins del sub char target (matrix.getLast?.getD [])])
    [initialRow ins target 0]

/-- The new implementation retains only the row needed by the next iteration. -/
def twoRows (min3 : α → α → α → α) (ins del sub : α)
    (source target : List β) : List α :=
  source.foldl (fun previous char => newRow min3 ins del sub char target previous)
    (initialRow ins target 0)

theorem fold_rows_equal (min3 : α → α → α → α) (ins del sub : α)
    (source target : List β) (matrix : List (List α)) (previous : List α)
    (h : matrix.getLast?.getD [] = previous) :
    (source.foldl (fun rows char =>
      rows ++ [oldRow min3 ins del sub char target (rows.getLast?.getD [])]) matrix).getLast?.getD [] =
    source.foldl (fun row char => newRow min3 ins del sub char target row) previous := by
  induction source generalizing matrix previous with
  | nil => exact h
  | cons char rest ih =>
    simp only [List.foldl_cons]
    apply ih
    simp [h, row_equal min3 ins del sub char target previous]

theorem rows_equal (min3 : α → α → α → α) (ins del sub : α)
    (source target : List β) :
    (fullMatrix min3 ins del sub source target).getLast?.getD [] =
      twoRows min3 ins del sub source target := by
  exact fold_rows_equal min3 ins del sub source target
    [initialRow ins target 0] (initialRow ins target 0) rfl

/-- The final matrix cell equals the last cell in the new retained row. -/
theorem levenshtein_exact (min3 : α → α → α → α) (ins del sub : α)
    (source target : List β) :
    ((fullMatrix min3 ins del sub source target).getLast?.getD []).getD target.length 0 =
      (twoRows min3 ins del sub source target).getD target.length 0 := by
  rw [rows_equal min3 ins del sub source target]

/-! ## Spellcheck list operations -/

def indexOf [DecidableEq γ] (value : γ) : List γ → Option Nat
  | [] => none
  | x :: xs => if value = x then some 0 else (indexOf value xs).map Nat.succ

def indexFilterAux [DecidableEq γ] (whole : List γ) (position : Nat) : List γ → List γ
  | [] => []
  | x :: xs =>
    let tail := indexFilterAux whole (position + 1) xs
    if indexOf x whole = some position then x :: tail else tail

def indexFilter [DecidableEq γ] (xs : List γ) : List γ := indexFilterAux xs 0 xs

/-- The insertion order of a Set: emit a value only on its first insertion. -/
def setDedupeFrom [DecidableEq γ] (seen : List γ) : List γ → List γ
  | [] => []
  | x :: xs => if x ∈ seen then setDedupeFrom (seen ++ [x]) xs
                 else x :: setDedupeFrom (seen ++ [x]) xs

def setDedupe [DecidableEq γ] (xs : List γ) : List γ := setDedupeFrom [] xs

theorem indexOf_at_iff_not_mem [DecidableEq γ] (x : γ) (prior suffix : List γ) :
    indexOf x (prior ++ x :: suffix) = some prior.length ↔ x ∉ prior := by
  induction prior with
  | nil => simp [indexOf]
  | cons y ys ih =>
    by_cases h : x = y
    · simp [indexOf, h]
    · simp [indexOf, h, ih]

theorem dedupe_aux_equal [DecidableEq γ] (prior rest : List γ) :
    indexFilterAux (prior ++ rest) prior.length rest = setDedupeFrom prior rest := by
  induction rest generalizing prior with
  | nil => rfl
  | cons x xs ih =>
    simp only [indexFilterAux, setDedupeFrom]
    have htail := ih (prior ++ [x])
    simp only [List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton] at htail
    rw [htail]
    by_cases hm : x ∈ prior
    · have hc : indexOf x (prior ++ x :: xs) ≠ some prior.length :=
        fun he => ((indexOf_at_iff_not_mem x prior xs).mp he) hm
      simp [hm, hc]
    · have hc : indexOf x (prior ++ x :: xs) = some prior.length :=
        (indexOf_at_iff_not_mem x prior xs).mpr hm
      simp [hm, hc]

theorem spellcheck_dedupe_exact [DecidableEq γ] (xs : List γ) :
    indexFilter xs = setDedupe xs := by
  simpa [indexFilter, setDedupe] using dedupe_aux_equal ([] : List γ) xs

def concatEdits (initial : List γ) (batches : List (List γ)) : List γ :=
  batches.foldl (fun acc xs => acc ++ xs) initial

def pushEach (acc : List γ) (xs : List γ) : List γ :=
  xs.foldl (fun acc x => acc ++ [x]) acc

def pushEdits (initial : List γ) (batches : List (List γ)) : List γ :=
  batches.foldl pushEach initial

theorem pushEach_eq_append (acc xs : List γ) : pushEach acc xs = acc ++ xs := by
  induction xs generalizing acc with
  | nil => simp [pushEach]
  | cons x xs ih =>
    simp only [pushEach, List.foldl_cons]
    rw [← pushEach, ih, List.append_assoc]
    rfl

theorem spellcheck_concat_exact (initial : List γ) (batches : List (List γ)) :
    concatEdits initial batches = pushEdits initial batches := by
  induction batches generalizing initial with
  | nil => rfl
  | cons xs rest ih =>
    simp only [concatEdits, pushEdits, List.foldl_cons]
    rw [← concatEdits, ← pushEdits, pushEach_eq_append, ih]

end NaturalLevenshteinProof

#print axioms NaturalLevenshteinProof.row_equal
#print axioms NaturalLevenshteinProof.rows_equal
#print axioms NaturalLevenshteinProof.levenshtein_exact
#print axioms NaturalLevenshteinProof.spellcheck_dedupe_exact
#print axioms NaturalLevenshteinProof.spellcheck_concat_exact
