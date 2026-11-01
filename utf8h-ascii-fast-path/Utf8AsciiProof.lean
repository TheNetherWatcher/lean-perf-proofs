/-!
utf8.h ASCII fast paths: each new function returns exactly what the original returns.

Strings are `List Nat`; `byte s i` reads a byte, and reading past the end reads the NUL
terminator. Positions are indices. `utf8codepoint` is modelled exactly (`dec`). The case
mappings `utf8lwrcodepoint`/`utf8uprcodepoint` are parameters; the only fact used about them is
what they do on ASCII (`A-Z` <-> `a-z`, all else unchanged), which the PR checks for all 128 values.
-/

set_option linter.unusedVariables false

theorem ite_t {α} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
theorem ite_f {α} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by simp [h]

/-- The byte at index `i`; past the end of the buffer reads the NUL terminator. -/
def byte (s : List Nat) (i : Nat) : Nat := s.getD i 0 % 256

theorem byte_lt (s : List Nat) (i : Nat) : byte s i < 256 := Nat.mod_lt _ (by decide)

theorem byte_past (s : List Nat) (i : Nat) (h : s.length ≤ i) : byte s i = 0 := by
  simp [byte, List.getD, List.getElem?_eq_none h]

theorem lt_of_byte_ne (s : List Nat) (i : Nat) (h : byte s i ≠ 0) : i < s.length := by
  apply Classical.byContradiction; intro hc; exact h (byte_past s i (by omega))

/-- C tests `0 == (0x80 & c)`; on a byte that is `c < 128`. -/
theorem ascii_iff : ∀ b, b < 256 → ((b &&& 0x80 = 0) ↔ b < 128) := by decide +kernel

/-- Lead-byte length used by `utf8codepoint`. -/
def leadLen (c : Nat) : Nat :=
  if c &&& 0xf8 = 0xf0 then 4 else if c &&& 0xf0 = 0xe0 then 3
  else if c &&& 0xe0 = 0xc0 then 2 else 1

theorem leadLen_ascii : ∀ c, c < 128 → leadLen c = 1 := by decide +kernel

/-- The continuation loop of `utf8codepoint`: `for (i = 1; i < n && '\0' != str[i]; i++)`. -/
def accum (s : List Nat) (p n : Nat) (i cp : Nat) : Nat × Nat :=
  if i < n ∧ byte s (p + i) ≠ 0 then accum s p n (i + 1) ((cp <<< 6) ||| (byte s (p + i) &&& 0x3f))
  else (cp, i)
termination_by n - i

theorem accum_ge (s : List Nat) (p n : Nat) : ∀ k i cp, n - i = k → i ≤ (accum s p n i cp).2 := by
  intro k
  induction k with
  | zero => intro i cp hk; rw [accum, ite_f (by omega)]; exact Nat.le_refl _
  | succ k ih =>
    intro i cp hk
    rw [accum]; split
    · have := ih (i + 1) ((cp <<< 6) ||| (byte s (p + i) &&& 0x3f)) (by omega); omega
    · exact Nat.le_refl _

/-- `utf8codepoint(str + p, &cp)`: the codepoint and the index after it.
Lead bytes are read unsigned; the fast paths only ever take bytes below 128. -/
def dec (s : List Nat) (p : Nat) : Nat × Nat :=
  let c := byte s p
  let n := leadLen c
  let cp0 := if n = 4 then c &&& 0x07 else if n = 3 then c &&& 0x0f
    else if n = 2 then c &&& 0x1f else c
  let r := accum s p n 1 cp0
  (r.1, p + r.2)

theorem dec_next (s : List Nat) (p : Nat) : p + 1 ≤ (dec s p).2 := by
  have := accum_ge s p (leadLen (byte s p)) _ 1
    (if leadLen (byte s p) = 4 then byte s p &&& 0x07 else if leadLen (byte s p) = 3 then byte s p &&& 0x0f
      else if leadLen (byte s p) = 2 then byte s p &&& 0x1f else byte s p) rfl
  simp only [dec]; omega

/-- An ASCII byte decodes to itself and advances by one. -/
theorem dec_ascii (s : List Nat) (p : Nat) (h : byte s p < 128) : dec s p = (byte s p, p + 1) := by
  simp only [dec, leadLen_ascii _ h]
  rw [accum, ite_f (by omega)]
  simp

theorem dec_zero (s : List Nat) (p : Nat) (h : byte s p = 0) : (dec s p).1 = 0 := by
  have := dec_ascii s p (by omega); rw [this]; exact h

theorem dec_fst_ne (s : List Nat) (p : Nat) (h : (dec s p).1 ≠ 0) : byte s p ≠ 0 :=
  fun hz => h (dec_zero s p hz)

/-! ## `utf8str` (and `utf8chr`, which calls it) -/

/-- The byte compare loop: `while (*haystack == *n && *haystack != '\0' && *n != '\0')`,
returning how far it got into the needle. -/
def matchLen (s nd : List Nat) (h k : Nat) : Nat :=
  if byte s (h + k) = byte nd k ∧ byte s (h + k) ≠ 0 ∧ byte nd k ≠ 0 then matchLen s nd h (k + 1) else k
termination_by nd.length - k
decreasing_by have := lt_of_byte_ne nd k (by omega); omega

/-- The original `utf8str` loop from haystack index `h`. -/
def strOld (s nd : List Nat) (h : Nat) : Option Nat :=
  if hb : byte s h = 0 then none
  else if byte nd (matchLen s nd h 0) = 0 then some h
  else strOld s nd (dec s h).2
termination_by s.length - h
decreasing_by have := lt_of_byte_ne s h hb; have := dec_next s h; omega

/-- The new skip: `while (ascii && *haystack != '\0' && *haystack != *needle) haystack++`. -/
def skipStr (s nd : List Nat) (h : Nat) : Nat :=
  if hc : byte s h < 128 ∧ byte s h ≠ 0 ∧ byte s h ≠ byte nd 0 then skipStr s nd (h + 1) else h
termination_by s.length - h
decreasing_by have := lt_of_byte_ne s h hc.2.1; omega

theorem skipStr_ge (s nd : List Nat) : ∀ k h, s.length - h = k → h ≤ skipStr s nd h := by
  intro k; induction k with
  | zero =>
    intro h hk; rw [skipStr]; split
    · rename_i hc; have := lt_of_byte_ne s h hc.2.1; omega
    · exact Nat.le_refl _
  | succ k ih =>
    intro h hk; rw [skipStr]; split
    · have := ih (h + 1) (by omega); omega
    · exact Nat.le_refl _

/-- The new `utf8str` loop. -/
def strNew (s nd : List Nat) (h : Nat) : Option Nat :=
  if hb : byte s (skipStr s nd h) = 0 then none
  else if byte nd (matchLen s nd (skipStr s nd h) 0) = 0 then some (skipStr s nd h)
  else strNew s nd (dec s (skipStr s nd h)).2
termination_by s.length - h
decreasing_by
  have := lt_of_byte_ne s _ hb; have := dec_next s (skipStr s nd h)
  have : h ≤ skipStr s nd h := skipStr_ge s nd _ h rfl
  omega

/-- At a skipped byte the original loop fails on the first byte and moves on by one. -/
theorem strOld_skip (s nd : List Nat) (h : Nat) (hn : byte nd 0 ≠ 0)
    (hc : byte s h < 128 ∧ byte s h ≠ 0 ∧ byte s h ≠ byte nd 0) :
    strOld s nd h = strOld s nd (h + 1) := by
  have hm : matchLen s nd h 0 = 0 := by
    rw [matchLen, ite_f (by simp only [Nat.add_zero]; omega)]
  rw [strOld]; simp only [hc.2.1, ↓reduceDIte, hm, hn, ite_false, dec_ascii s h hc.1]

theorem strOld_skipStr (s nd : List Nat) (hn : byte nd 0 ≠ 0) :
    ∀ k h, s.length - h = k → strOld s nd (skipStr s nd h) = strOld s nd h := by
  intro k; induction k with
  | zero =>
    intro h hk; rw [skipStr]; split
    · rename_i hc; have := lt_of_byte_ne s h hc.2.1; omega
    · rfl
  | succ k ih =>
    intro h hk; rw [skipStr]; split
    · rename_i hc; rw [ih (h + 1) (by omega), strOld_skip s nd h hn hc]
    · rfl

/-- The new loop returns what the old loop returns, from any start, for any non-empty needle. -/
theorem strLoop_exact (s nd : List Nat) (hn : byte nd 0 ≠ 0) :
    ∀ k h, s.length - h = k → strNew s nd h = strOld s nd h := by
  intro k; induction k using Nat.strongRecOn with
  | _ k ih =>
    intro h hk
    rw [← strOld_skipStr s nd hn _ h rfl, strNew, strOld.eq_1 s nd (skipStr s nd h)]
    have hge := skipStr_ge s nd _ h rfl
    split
    · rfl
    · rename_i hb
      split
      · rfl
      · have := lt_of_byte_ne s _ hb; have := dec_next s (skipStr s nd h)
        exact ih _ (by omega) _ rfl

/-- `utf8str` as a whole: an empty needle returns the haystack, otherwise the loop runs. -/
def utf8strOld (s nd : List Nat) : Option Nat := if byte nd 0 = 0 then some 0 else strOld s nd 0
def utf8strNew (s nd : List Nat) : Option Nat := if byte nd 0 = 0 then some 0 else strNew s nd 0

theorem utf8str_exact (s nd : List Nat) : utf8strNew s nd = utf8strOld s nd := by
  unfold utf8strNew utf8strOld; split
  · rfl
  · rename_i hn; exact strLoop_exact s nd hn _ 0 rfl

/-! ## `utf8casestr`

`utf8lwrcodepoint` is a parameter `lwr`. The only fact used about it is `lwr_ascii`: on ASCII it
lowers `A-Z` and leaves everything else alone (checked for all 128 values against the C). -/

def asciiLower (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c
def asciiUpper (c : Nat) : Nat := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

theorem asciiLower_zero (c : Nat) : asciiLower c = 0 ↔ c = 0 := by
  unfold asciiLower; split <;> omega

/-- The codepoint compare loop of `utf8casestr`, with fuel standing in for the needle running out
(old and new use the same function, so the fuel does not affect the comparison). -/
def ci (lwr : Nat → Nat) (s nd : List Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, _, hc, nc => (hc, nc)
  | f + 1, h, n, hc, nc =>
    if hc ≠ 0 ∧ nc ≠ 0 then
      if lwr hc ≠ lwr nc then (lwr hc, lwr nc)
      else ci lwr s nd f (dec s h).2 (dec nd n).2 (dec s h).1 (dec nd n).1
    else (hc, nc)

theorem ci_zero (lwr : Nat → Nat) (s nd : List Nat) (f h n nc : Nat) : (ci lwr s nd f h n 0 nc).1 = 0 := by
  cases f <;> simp [ci]

/-- One try at haystack index `h`: the final `(h_cp, n_cp)` of the compare loop. -/
def csTry (lwr : Nat → Nat) (s nd : List Nat) (h : Nat) : Nat × Nat :=
  ci lwr s nd (nd.length + 1) (dec s h).2 (dec nd 0).2 (dec s h).1 (dec nd 0).1

theorem csTry_lt (lwr : Nat → Nat) (s nd : List Nat) (h : Nat) (hr : (csTry lwr s nd h).1 ≠ 0) :
    h < s.length := by
  apply lt_of_byte_ne; intro hb
  exact hr (by unfold csTry; rw [show (dec s h).1 = 0 from dec_zero s h hb]; exact ci_zero ..)

/-- The original `utf8casestr` loop. -/
def csOld (lwr : Nat → Nat) (s nd : List Nat) (h : Nat) : Option Nat :=
  if (csTry lwr s nd h).2 = 0 then some h
  else if hr : (csTry lwr s nd h).1 = 0 then none
  else csOld lwr s nd (dec s h).2
termination_by s.length - h
decreasing_by have := csTry_lt lwr s nd h hr; have := dec_next s h; omega

/-- `first`: the needle's first byte lowered if it is ASCII, else 0. -/
def firstOf (nd : List Nat) : Nat := if byte nd 0 < 128 then asciiLower (byte nd 0) else 0

def skipCs (s : List Nat) (f h : Nat) : Nat :=
  if hc : f ≠ 0 ∧ byte s h < 128 ∧ byte s h ≠ 0 ∧ asciiLower (byte s h) ≠ f then skipCs s f (h + 1) else h
termination_by s.length - h
decreasing_by have := lt_of_byte_ne s h hc.2.2.1; omega

theorem skipCs_ge (s : List Nat) (f : Nat) : ∀ k h, s.length - h = k → h ≤ skipCs s f h := by
  intro k; induction k with
  | zero =>
    intro h hk; rw [skipCs]; split
    · rename_i hc; have := lt_of_byte_ne s h hc.2.2.1; omega
    · exact Nat.le_refl _
  | succ k ih =>
    intro h hk; rw [skipCs]; split
    · have := ih (h + 1) (by omega); omega
    · exact Nat.le_refl _

/-- The new `utf8casestr` loop. -/
def csNew (lwr : Nat → Nat) (s nd : List Nat) (h : Nat) : Option Nat :=
  if (csTry lwr s nd (skipCs s (firstOf nd) h)).2 = 0 then some (skipCs s (firstOf nd) h)
  else if hr : (csTry lwr s nd (skipCs s (firstOf nd) h)).1 = 0 then none
  else csNew lwr s nd (dec s (skipCs s (firstOf nd) h)).2
termination_by s.length - h
decreasing_by
  have := csTry_lt lwr s nd _ hr; have := dec_next s (skipCs s (firstOf nd) h)
  have := skipCs_ge s (firstOf nd) _ h rfl; omega

section
variable (lwr : Nat → Nat) (lwr_ascii : ∀ c, c < 128 → lwr c = asciiLower c)
include lwr_ascii

theorem csOld_skip (s nd : List Nat) (h : Nat)
    (hc : firstOf nd ≠ 0 ∧ byte s h < 128 ∧ byte s h ≠ 0 ∧ asciiLower (byte s h) ≠ firstOf nd) :
    csOld lwr s nd h = csOld lwr s nd (h + 1) := by
  obtain ⟨hf, hb, hz, hne⟩ := hc
  have hn : byte nd 0 < 128 := by
    unfold firstOf at hf hne; split at hf
    · assumption
    · exact absurd rfl hf
  have hfe : firstOf nd = asciiLower (byte nd 0) := by simp [firstOf, hn]
  have hn0 : byte nd 0 ≠ 0 := fun e => hf (by rw [hfe, e]; rfl)
  have ht : csTry lwr s nd h = (asciiLower (byte s h), asciiLower (byte nd 0)) := by
    unfold csTry
    rw [dec_ascii s h hb, dec_ascii nd 0 hn]
    simp only [ci, lwr_ascii _ hb, lwr_ascii _ hn]
    rw [hfe] at hne
    simp [hz, hn0, hne]
  have h1 : asciiLower (byte nd 0) ≠ 0 := fun e => hn0 ((asciiLower_zero _).mp e)
  have h2 : asciiLower (byte s h) ≠ 0 := fun e => hz ((asciiLower_zero _).mp e)
  rw [csOld]
  simp only [ht, h1, h2, ite_false, ↓reduceDIte, dec_ascii s h hb]

theorem csOld_skipCs (s nd : List Nat) :
    ∀ k h, s.length - h = k → csOld lwr s nd (skipCs s (firstOf nd) h) = csOld lwr s nd h := by
  intro k; induction k with
  | zero =>
    intro h hk; rw [skipCs]; split
    · rename_i hc; have := lt_of_byte_ne s h hc.2.2.1; omega
    · rfl
  | succ k ih =>
    intro h hk; rw [skipCs]; split
    · rename_i hc; rw [ih (h + 1) (by omega), csOld_skip lwr lwr_ascii s nd h hc]
    · rfl

theorem csLoop_exact (s nd : List Nat) :
    ∀ k h, s.length - h = k → csNew lwr s nd h = csOld lwr s nd h := by
  intro k; induction k using Nat.strongRecOn with
  | _ k ih =>
    intro h hk
    rw [← csOld_skipCs lwr lwr_ascii s nd _ h rfl, csNew, csOld.eq_1 lwr s nd (skipCs s (firstOf nd) h)]
    have hge := skipCs_ge s (firstOf nd) _ h rfl
    split
    · rfl
    · split
      · rfl
      · rename_i hr
        have := csTry_lt lwr s nd _ hr; have := dec_next s (skipCs s (firstOf nd) h)
        exact ih _ (by omega) _ rfl

def utf8casestrOld (s nd : List Nat) : Option Nat := if byte nd 0 = 0 then some 0 else csOld lwr s nd 0
def utf8casestrNew (s nd : List Nat) : Option Nat := if byte nd 0 = 0 then some 0 else csNew lwr s nd 0

theorem utf8casestr_exact (s nd : List Nat) : utf8casestrNew lwr s nd = utf8casestrOld lwr s nd := by
  unfold utf8casestrNew utf8casestrOld; split
  · rfl
  · exact csLoop_exact lwr lwr_ascii s nd _ 0 rfl
end

/-! ## `utf8casecmp`

`lwr`/`upr` stand for `utf8lwrcodepoint`/`utf8uprcodepoint`. Every pass of the new `for (;;)` is one
pass of the old one, so the loops are compared pass for pass with the same fuel. -/

def ccOld (lwr upr : Nat → Nat) (a b : List Nat) : Nat → Nat → Nat → Int
  | 0, _, _ => 0
  | f + 1, i, j =>
    if (dec a i).1 = 0 ∧ (dec b j).1 = 0 then 0
    else if lwr (dec a i).1 = lwr (dec b j).1 ∨ upr (dec a i).1 = upr (dec b j).1 then
      ccOld lwr upr a b f (dec a i).2 (dec b j).2
    else (lwr (dec a i).1 : Int) - lwr (dec b j).1

def ccNew (lwr upr : Nat → Nat) (a b : List Nat) : Nat → Nat → Nat → Int
  | 0, _, _ => 0
  | f + 1, i, j =>
    if byte a i < 128 ∧ byte b j < 128 then
      if byte a i = 0 ∧ byte b j = 0 then 0
      else if asciiLower (byte a i) = asciiLower (byte b j) ∨
          asciiUpper (byte a i) = asciiUpper (byte b j) then
        ccNew lwr upr a b f (i + 1) (j + 1)
      else (asciiLower (byte a i) : Int) - asciiLower (byte b j)
    else if (dec a i).1 = 0 ∧ (dec b j).1 = 0 then 0
    else if lwr (dec a i).1 = lwr (dec b j).1 ∨ upr (dec a i).1 = upr (dec b j).1 then
      ccNew lwr upr a b f (dec a i).2 (dec b j).2
    else (lwr (dec a i).1 : Int) - lwr (dec b j).1

theorem utf8casecmp_exact (lwr upr : Nat → Nat)
    (lwr_ascii : ∀ c, c < 128 → lwr c = asciiLower c) (upr_ascii : ∀ c, c < 128 → upr c = asciiUpper c)
    (a b : List Nat) : ∀ f i j, ccNew lwr upr a b f i j = ccOld lwr upr a b f i j := by
  intro f; induction f with
  | zero => intro i j; rfl
  | succ f ih =>
    intro i j
    simp only [ccNew, ccOld, ih]
    split
    · rename_i h
      rw [dec_ascii a i h.1, dec_ascii b j h.2]
      simp only [lwr_ascii _ h.1, lwr_ascii _ h.2, upr_ascii _ h.1, upr_ascii _ h.2]
    · rfl

/-! ## `utf8nlen` (and `utf8len`) -/

/-- `do { str += 1; } while (--cp_len && str < n && '\0' != *str)`, after the first `str += 1`. -/
def adv (s : List Nat) (n p k : Nat) : Nat × Nat :=
  if k ≠ 0 ∧ p < n ∧ byte s p ≠ 0 then adv s n (p + 1) (k - 1) else (p, k)
termination_by k

theorem adv_ge (s : List Nat) (n : Nat) : ∀ k p, p ≤ (adv s n p k).1 := by
  intro k; induction k with
  | zero => intro p; rw [adv, ite_f (by omega)]; exact Nat.le_refl _
  | succ k ih => intro p; rw [adv]; split
                 · have := ih (p + 1); simp only [Nat.add_sub_cancel]; omega
                 · exact Nat.le_refl _

def lenOld (s : List Nat) (n p len : Nat) : Nat :=
  if hc : p < n ∧ byte s p ≠ 0 then
    if (adv s n (p + 1) (leadLen (byte s p) - 1)).2 ≠ 0 ∧ (adv s n (p + 1) (leadLen (byte s p) - 1)).1 = n
    then len
    else lenOld s n (adv s n (p + 1) (leadLen (byte s p) - 1)).1 (len + 1)
  else len
termination_by s.length - p
decreasing_by have := lt_of_byte_ne s p hc.2; have := adv_ge s n (leadLen (byte s p) - 1) (p + 1); omega

/-- The new ASCII run: `do { str++; length++; } while (str < n && '\0' != *str && ascii)`. -/
def run (s : List Nat) (n p len : Nat) : Nat × Nat :=
  if hc : p + 1 < n ∧ byte s (p + 1) ≠ 0 ∧ byte s (p + 1) < 128 then run s n (p + 1) (len + 1)
  else (p + 1, len + 1)
termination_by s.length - p
decreasing_by have := lt_of_byte_ne s (p + 1) hc.2.1; omega

theorem run_ge (s : List Nat) (n : Nat) : ∀ k p len, s.length - p = k → p + 1 ≤ (run s n p len).1 := by
  intro k; induction k with
  | zero =>
    intro p len hk; rw [run]; split
    · rename_i hc; have := lt_of_byte_ne s (p + 1) hc.2.1; omega
    · exact Nat.le_refl _
  | succ k ih =>
    intro p len hk; rw [run]; split
    · rename_i hc; have := lt_of_byte_ne s (p + 1) hc.2.1; have := ih (p + 1) (len + 1) (by omega); omega
    · exact Nat.le_refl _

def lenNew (s : List Nat) (n p len : Nat) : Nat :=
  if hc : p < n ∧ byte s p ≠ 0 then
    if byte s p < 128 then lenNew s n (run s n p len).1 (run s n p len).2
    else if (adv s n (p + 1) (leadLen (byte s p) - 1)).2 ≠ 0 ∧ (adv s n (p + 1) (leadLen (byte s p) - 1)).1 = n
    then len
    else lenNew s n (adv s n (p + 1) (leadLen (byte s p) - 1)).1 (len + 1)
  else len
termination_by s.length - p
decreasing_by
  · have := lt_of_byte_ne s p hc.2; have := run_ge s n _ p len rfl; omega
  · have := lt_of_byte_ne s p hc.2; have := adv_ge s n (leadLen (byte s p) - 1) (p + 1); omega

theorem lenOld_ascii (s : List Nat) (n p len : Nat) (hc : p < n ∧ byte s p ≠ 0) (ha : byte s p < 128) :
    lenOld s n p len = lenOld s n (p + 1) (len + 1) := by
  rw [lenOld, dite_eq_left_of_eq_true (eq_true hc), leadLen_ascii _ ha]
  simp [adv]

theorem lenOld_run (s : List Nat) (n : Nat) : ∀ k p len, s.length - p = k →
    p < n ∧ byte s p ≠ 0 ∧ byte s p < 128 →
    lenOld s n p len = lenOld s n (run s n p len).1 (run s n p len).2 := by
  intro k; induction k with
  | zero => intro p len hk hc; have := lt_of_byte_ne s p hc.2.1; omega
  | succ k ih =>
    intro p len hk hc
    rw [lenOld_ascii s n p len ⟨hc.1, hc.2.1⟩ hc.2.2, run]
    split
    · rename_i h1; exact ih (p + 1) (len + 1) (by omega) h1
    · rfl

theorem utf8nlen_exact (s : List Nat) (n : Nat) :
    ∀ k p len, s.length - p = k → lenNew s n p len = lenOld s n p len := by
  intro k; induction k using Nat.strongRecOn with
  | _ k ih =>
    intro p len hk
    rw [lenNew]
    split
    · rename_i hc
      split
      · rename_i ha
        have := lt_of_byte_ne s p hc.2; have := run_ge s n _ p len rfl
        rw [ih _ (by omega) _ _ rfl, ← lenOld_run s n _ p len rfl ⟨hc.1, hc.2, ha⟩]
      · rw [lenOld.eq_1 s n p len, dite_eq_left_of_eq_true (eq_true hc)]
        split
        · rfl
        · have := lt_of_byte_ne s p hc.2; have := adv_ge s n (leadLen (byte s p) - 1) (p + 1)
          exact ih _ (by omega) _ _ rfl
    · rename_i hc; rw [lenOld, dite_eq_right_of_eq_false (eq_false hc)]

/-! ## `utf8nvalid` (and `utf8valid`)

The ASCII test moved from the last branch to the first. An ASCII byte matches none of the
multi-byte lead tests, so every byte still takes the same branch. -/

theorem ascii_not_lead : ∀ b, b < 256 → b &&& 0x80 = 0 →
    ¬ (b &&& 0xf8 = 0xf0) ∧ ¬ (b &&& 0xf0 = 0xe0) ∧ ¬ (b &&& 0xe0 = 0xc0) := by decide +kernel

/-! ## `utf8lwr` and `utf8upr`

Both are one loop over a mapping `m` (`utf8lwrcodepoint` or `utf8uprcodepoint`) whose ASCII part is
`am`, writing through `enc` (`utf8catcodepoint`), which writes one byte for an ASCII codepoint. -/

def writeAt : List Nat → Nat → List Nat → List Nat
  | s, _, [] => s
  | s, p, x :: xs => writeAt (s.set p x) (p + 1) xs

theorem writeAt_length : ∀ (xs : List Nat) (s : List Nat) (p : Nat), (writeAt s p xs).length = s.length
  | [], _, _ => rfl
  | x :: xs, s, p => by simp [writeAt, writeAt_length xs]

/-- One general step: write the mapped codepoint back if it differs. -/
def put (m : Nat → Nat) (enc : Nat → List Nat) (s : List Nat) (p : Nat) : List Nat :=
  if m (dec s p).1 ≠ (dec s p).1 then writeAt s p (enc (m (dec s p).1)) else s

/-- One ASCII fast step: overwrite the byte if its case changes. -/
def fput (am : Nat → Nat) (s : List Nat) (p : Nat) : List Nat :=
  if am (byte s p) ≠ byte s p then s.set p (am (byte s p)) else s

theorem put_length (m : Nat → Nat) (enc : Nat → List Nat) (s : List Nat) (p : Nat) :
    (put m enc s p).length = s.length := by
  unfold put; split
  · exact writeAt_length ..
  · rfl

theorem fput_length (am : Nat → Nat) (s : List Nat) (p : Nat) : (fput am s p).length = s.length := by
  unfold fput; split
  · exact List.length_set ..
  · rfl

def mapOld (m : Nat → Nat) (enc : Nat → List Nat) (s : List Nat) (p : Nat) : List Nat :=
  if hc : (dec s p).1 = 0 then s
  else mapOld m enc (put m enc s p) (dec s p).2
termination_by s.length - p
decreasing_by
  have := lt_of_byte_ne s p (dec_fst_ne s p hc); have := dec_next s p
  rw [put_length]; omega

def mapNew (m am : Nat → Nat) (enc : Nat → List Nat) (s : List Nat) (p : Nat) : List Nat :=
  if hc : byte s p < 128 ∧ byte s p ≠ 0 then mapNew m am enc (fput am s p) (p + 1)
  else if hd : (dec s p).1 = 0 then s
  else mapNew m am enc (put m enc s p) (dec s p).2
termination_by s.length - p
decreasing_by
  · have := lt_of_byte_ne s p hc.2; rw [fput_length]; omega
  · have := lt_of_byte_ne s p (dec_fst_ne s p hd); have := dec_next s p
    rw [put_length]; omega

theorem map_exact (m am : Nat → Nat) (enc : Nat → List Nat)
    (m_ascii : ∀ c, c < 128 → m c = am c) (enc_ascii : ∀ c, c < 128 → enc c = [c])
    (am_ascii : ∀ c, c < 128 → am c < 128) :
    ∀ k s p, s.length - p = k → mapNew m am enc s p = mapOld m enc s p := by
  intro k; induction k using Nat.strongRecOn with
  | _ k ih =>
    intro s p hk
    rw [mapNew]
    split
    · rename_i hc
      have hlt := lt_of_byte_ne s p hc.2
      have hstep : mapOld m enc s p = mapOld m enc (fput am s p) (p + 1) := by
        have hz : (dec s p).1 ≠ 0 := by rw [dec_ascii s p hc.1]; exact hc.2
        have hp : put m enc s p = fput am s p := by
          unfold put fput
          rw [dec_ascii s p hc.1]
          simp only [m_ascii _ hc.1, enc_ascii _ (am_ascii _ hc.1), writeAt]
        rw [mapOld.eq_1 m enc s p, dite_eq_right_of_eq_false (eq_false hz), hp, dec_ascii s p hc.1]
      rw [hstep]
      exact ih _ (by rw [fput_length]; omega) _ _ rfl
    · split
      · rename_i hd; rw [mapOld, dite_eq_left_of_eq_true (eq_true hd)]
      · rename_i hd
        rw [mapOld.eq_1 m enc s p, dite_eq_right_of_eq_false (eq_false hd)]
        have := lt_of_byte_ne s p (dec_fst_ne s p hd); have := dec_next s p
        exact ih _ (by rw [put_length]; omega) _ _ rfl

/-- The C fast path writes `c + 32` for `A-Z`: that is `asciiLower`. -/
theorem lower_fast_form (s : List Nat) (p c : Nat) :
    (if 65 ≤ c ∧ c ≤ 90 then s.set p (c + 32) else s) =
    (if asciiLower c ≠ c then s.set p (asciiLower c) else s) := by
  unfold asciiLower; by_cases h : 65 ≤ c ∧ c ≤ 90 <;> simp [h]

/-- The C fast path writes `c - 32` for `a-z`: that is `asciiUpper`. -/
theorem upper_fast_form (s : List Nat) (p c : Nat) :
    (if 97 ≤ c ∧ c ≤ 122 then s.set p (c - 32) else s) =
    (if asciiUpper c ≠ c then s.set p (asciiUpper c) else s) := by
  unfold asciiUpper; by_cases h : 97 ≤ c ∧ c ≤ 122 <;> simp [h] <;> omega

theorem asciiLower_lt : ∀ c, c < 128 → asciiLower c < 128 := by
  intro c h; unfold asciiLower; split <;> omega
theorem asciiUpper_lt : ∀ c, c < 128 → asciiUpper c < 128 := by
  intro c h; unfold asciiUpper; split <;> omega


theorem utf8lwr_exact (lwr : Nat → Nat) (enc : Nat → List Nat)
    (lwr_ascii : ∀ c, c < 128 → lwr c = asciiLower c) (enc_ascii : ∀ c, c < 128 → enc c = [c])
    (s : List Nat) : mapNew lwr asciiLower enc s 0 = mapOld lwr enc s 0 :=
  map_exact lwr asciiLower enc lwr_ascii enc_ascii asciiLower_lt _ s 0 rfl

theorem utf8upr_exact (upr : Nat → Nat) (enc : Nat → List Nat)
    (upr_ascii : ∀ c, c < 128 → upr c = asciiUpper c) (enc_ascii : ∀ c, c < 128 → enc c = [c])
    (s : List Nat) : mapNew upr asciiUpper enc s 0 = mapOld upr enc s 0 :=
  map_exact upr asciiUpper enc upr_ascii enc_ascii asciiUpper_lt _ s 0 rfl

#print axioms utf8str_exact
#print axioms utf8casestr_exact
#print axioms utf8casecmp_exact
#print axioms utf8nlen_exact
#print axioms ascii_not_lead
#print axioms utf8lwr_exact
#print axioms utf8upr_exact
