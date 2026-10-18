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

/-- A character of an identifier (`\w`): ASCII letters, digits, `_`, and any
non-ASCII character that is not whitespace. -/
def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || (c.val ≥ 128 && !isSpace c)

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

/-- Length of the newline sequence at the head (`\r\n`, `\r`, `\n`), or 0. -/
def newlineLen : List Char → Nat
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

/-- Decimal text of an integer. -/
def intDigits (i : Int) : List Char :=
  if i < 0 then '-' :: natDigits i.natAbs else natDigits i.natAbs

end LeanJinja2
