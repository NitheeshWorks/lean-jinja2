/-!
# Character classes and small list helpers

Python's `str.isspace`, regex `\s` and `\w`, digit values, and the newline
handling upstream applies to template source.
-/

namespace LeanJinja2

/-- Python's `str.isspace` / regex `\s` (ASCII whitespace plus the Unicode
space separators). -/
def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c' ||
  c == '\x1c' || c == '\x1d' || c == '\x1e' || c == '\x1f' || c == '\x85' || c == '\xa0' ||
  c == ' ' || (c.val ≥ 0x2000 && c.val ≤ 0x200a) || c == ' ' || c == ' ' ||
  c == ' ' || c == ' ' || c == '　'

/-- A line break character (`\n` or `\r`). -/
def isNewline (c : Char) : Bool := c == '\n' || c == '\r'

/-- Non-ASCII ranges that are punctuation, symbols or emoji rather than
letters (an approximation of Unicode's categories; Lean has no tables). -/
def isSymbolRange (v : UInt32) : Bool :=
  (v ≥ 0x80 && v ≤ 0xbf && v != 0xaa && v != 0xb5 && v != 0xba && v != 0xb7) ||
  v == 0xd7 || v == 0xf7 || (v ≥ 0x2000 && v ≤ 0x206f) || (v ≥ 0x20a0 && v ≤ 0x20cf) ||
  (v ≥ 0x2190 && v ≤ 0x2bff) || (v ≥ 0x3000 && v ≤ 0x303f) || (v ≥ 0xe000 && v ≤ 0xf8ff) ||
  (v ≥ 0xfe00 && v ≤ 0xfe0f) || (v ≥ 0x1f000 && v ≤ 0x1faff)

/-- A character of an identifier (`\w` plus upstream's extra identifier
characters): ASCII letters, digits, `_`, and non-ASCII letters. -/
def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || (c.val ≥ 128 && !isSpace c && !isSymbolRange c.val)

def isDigit (c : Char) : Bool := c.isDigit

/-- The value of a digit in base 2, 8, 10 or 16 (`none` if not a digit of that base). -/
def digitVal (base : Nat) (c : Char) : Option Nat :=
  let v :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  match v with
  | some d => if d < base then some d else none
  | none => none

/-- Fold digits (ignoring `_`) into a number. Non-digits count as zero; the
callers only pass characters a scanner has accepted. -/
def digitsValue (base : Nat) (l : List Char) : Nat :=
  l.foldl (fun acc c => if c == '_' then acc else acc * base + (digitVal base c).getD 0) 0

/-- Length of the newline sequence at the head (`\r\n`, `\r`, `\n`), or 0
(it reads two characters: the match is on `l.take 2`). -/
def newlineLen (l : List Char) : Nat :=
  match l.take 2 with
  | '\r' :: '\n' :: _ => 2
  | '\r' :: _ => 1
  | '\n' :: _ => 1
  | _ => 0

/-- Replace every newline sequence by `nl` (upstream `_normalize_newlines`). -/
def normalizeNewlines (nl : List Char) : List Char → List Char
  | [] => []
  | '\r' :: '\n' :: l => nl ++ normalizeNewlines nl l
  | '\r' :: l => nl ++ normalizeNewlines nl l
  | '\n' :: l => nl ++ normalizeNewlines nl l
  | c :: l => c :: normalizeNewlines nl l

/-- Newline normalisation as a fold: (text so far, last was `\r`). It builds
the text in a `String`, in one pass and constant stack. -/
def normStep (nl : String) : String × Bool → Char → String × Bool
  | (acc, cr), c =>
    if c == '\r' then (acc ++ nl, true)
    else if c == '\n' then (if cr then (acc, false) else (acc ++ nl, false))
    else (acc.push c, false)

/-- Drop a leading `\n` (the half of `\r\n` already normalised). -/
def dropLF (l : List Char) : List Char := if l.head? = some '\n' then l.tail else l

theorem norm_fold (nl : String) (l : List Char) :
    ∀ acc : String,
      (l.foldl (normStep nl) (acc, false)).1.toList = acc.toList ++ normalizeNewlines nl.toList l ∧
      (l.foldl (normStep nl) (acc, true)).1.toList =
        acc.toList ++ normalizeNewlines nl.toList (dropLF l) := by
  induction l with
  | nil => intro acc; simp [dropLF, normalizeNewlines]
  | cons c t ih =>
    intro acc
    have first : (List.foldl (normStep nl) (acc, false) (c :: t)).1.toList =
        acc.toList ++ normalizeNewlines nl.toList (c :: t) := by
      simp only [List.foldl_cons, normStep]
      by_cases hr : c = '\r'
      · subst hr
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [(ih _).2, String.toList_append, List.append_assoc]
        congr 1
        cases t with
        | nil => simp [dropLF, normalizeNewlines]
        | cons d u =>
          by_cases hd : d = '\n'
          · subst hd; simp [dropLF, normalizeNewlines.eq_2]
          · rw [normalizeNewlines.eq_3 _ _ (by intro _ h; simp at h; exact hd h.1)]
            simp [dropLF, hd]
      · have hr' : (c == '\r') = false := by simpa using hr
        simp only [hr', Bool.false_eq_true, ↓reduceIte]
        by_cases hn : c = '\n'
        · subst hn
          simp only [beq_self_eq_true, ↓reduceIte]
          rw [(ih _).1, String.toList_append, normalizeNewlines.eq_4, List.append_assoc]
        · have hn' : (c == '\n') = false := by simpa using hn
          simp only [hn', Bool.false_eq_true, ↓reduceIte]
          rw [(ih _).1, String.toList_push,
            normalizeNewlines.eq_5 _ _ _ (fun _ h _ => hr h) hr hn]
          simp
    refine ⟨first, ?_⟩
    by_cases hn : c = '\n'
    · subst hn
      simp only [List.foldl_cons, normStep, dropLF, List.head?_cons, List.tail_cons]
      simp [(ih _).1]
    · have hd : dropLF (c :: t) = c :: t := by simp [dropLF, hn]
      rw [hd, ← first]
      have hstep : normStep nl (acc, true) c = normStep nl (acc, false) c := by
        simp [normStep, hn]
      simp only [List.foldl_cons, hstep]

theorem normStep_fold (nl : String) (l : List Char) :
    (l.foldl (normStep nl) ("", false)).1 = String.ofList (normalizeNewlines nl.toList l) := by
  apply String.ext
  rw [(norm_fold nl l "").1, String.toList_ofList]; simp

/-- `normalizeNewlines` as it runs: the fold above (tail recursive). -/
def normalizeNewlinesTR (nl l : List Char) : List Char :=
  (l.foldl (normStep (String.ofList nl)) ("", false)).1.toList

@[csimp] theorem normalizeNewlines_eq_TR : @normalizeNewlines = @normalizeNewlinesTR := by
  funext nl l
  rw [normalizeNewlinesTR, (norm_fold (String.ofList nl) l "").1, String.toList_ofList]
  simp

/-- Python's `rstrip()`: drop trailing whitespace. -/
def rstripList (l : List Char) : List Char := (l.reverse.dropWhile isSpace).reverse

/-- Python's `strip()` on whitespace. -/
def stripList (l : List Char) : List Char := rstripList (l.dropWhile isSpace)

/-- Index just after the last line break of `l` (0 if there is none),
upstream `text.rfind("\n") + 1`. -/
def afterLastNewline (l : List Char) : Nat :=
  let rec go : List Char → Nat → Nat → Nat
    | [], _, acc => acc
    | c :: cs, i, acc => go cs (i + 1) (if isNewline c then i + 1 else acc)
  go l 0 0

/-- Decimal digits of a natural number, most significant first. -/
def natDigits (n : Nat) : List Char :=
  if h : n < 10 then [Char.ofNat (48 + n)]
  else natDigits (n / 10) ++ [Char.ofNat (48 + n % 10)]
termination_by n
decreasing_by omega

/-- `natDigits n ++ acc`, consing each digit onto the accumulator (no
appends): `natDigits_eq_acc` makes compiled code use it. -/
def natDigitsAcc (n : Nat) (acc : List Char) : List Char :=
  if h : n < 10 then Char.ofNat (48 + n) :: acc
  else natDigitsAcc (n / 10) (Char.ofNat (48 + n % 10) :: acc)
termination_by n
decreasing_by omega

theorem natDigitsAcc_eq (n : Nat) (acc : List Char) : natDigitsAcc n acc = natDigits n ++ acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    rw [natDigitsAcc, natDigits]
    split
    · rfl
    · rw [ih (n / 10) (by omega)]; simp

/-- `natDigits`, through `natDigitsAcc`. -/
def natDigitsFast (n : Nat) : List Char := natDigitsAcc n []

@[csimp] theorem natDigits_eq_acc : @natDigits = @natDigitsFast := by
  funext n; simp [natDigitsFast, natDigitsAcc_eq]

/-- Decimal text of an integer. -/
def intDigits (i : Int) : List Char :=
  if i < 0 then '-' :: natDigits i.natAbs else natDigits i.natAbs

end LeanJinja2
