/-!
# A cursor over a string slice

The lexer's specification (`Lexer.lean`) reads its input as a `List Char`.
That is the right shape for proofs and the wrong one for a 20 MB template: a
list costs 24 bytes a character. The fast lexer (`LexFast.lean`) reads the
same input in place, through positions of a `String.Slice`; this file is its
vocabulary. `rest p` is the list the specification would see at `p`; it is
used only in proofs and in termination measures, never computed at run time.

Every walker here is tail recursive (constant stack) and allocates nothing
per character, except `takeL`, which materialises a short prefix.
-/

namespace LeanJinja2

open String

namespace Cursor

variable {s : Slice}

/-- The characters from `p` to the end of the slice (the specification's
view of the input at `p`). -/
def rest (p : s.Pos) : List Char := (s.sliceFrom p).copy.toList

theorem rest_endPos : rest s.endPos = [] := by
  have h := Slice.Pos.splits s.endPos
  have h3 := h.eq_right (Slice.splits_endPos s)
  simp [rest, h3]

theorem rest_next (p : s.Pos) (h : p ≠ s.endPos) : rest p = p.get h :: rest (p.next h) := by
  have h1 := Slice.Pos.splits_next_right p h
  have h2 := h1.eq_right (Slice.Pos.splits p)
  simp [rest, ← h2]

theorem rest_startPos : rest s.startPos = s.copy.toList := by
  simp [rest]

theorem rest_next_length (p : s.Pos) (h : p ≠ s.endPos) :
    (rest (p.next h)).length < (rest p).length := by
  rw [rest_next p h]; simp

theorem rest_eq_nil_iff (p : s.Pos) : rest p = [] ↔ p = s.endPos := by
  constructor
  · intro hp
    by_cases h : p = s.endPos
    · exact h
    · rw [rest_next p h] at hp; cases hp
  · rintro rfl; exact rest_endPos

/-- The character at `p`, if any. -/
def peek (p : s.Pos) : Option Char := if h : p = s.endPos then none else some (p.get h)

/-- One character on (stays put at the end). -/
def adv (p : s.Pos) : s.Pos := if h : p = s.endPos then p else p.next h

/-- `n` characters on (stops at the end). -/
def advN (p : s.Pos) : Nat → s.Pos
  | 0 => p
  | n + 1 => advN (adv p) n

/-- `d` is a prefix of the text at `p`. -/
def preW (p : s.Pos) : List Char → Bool
  | [] => true
  | c :: cs => peek p == some c && preW (adv p) cs

/-- Add to `acc` the length of the run at `p` satisfying `P`. -/
def countWhile (P : Char → Bool) (p : s.Pos) (acc : Nat) : Nat :=
  if h : p = s.endPos then acc
  else if P (p.get h) then countWhile P (p.next h) (acc + 1) else acc
termination_by (rest p).length
decreasing_by exact rest_next_length p h

/-- Fold `f` over the first `n` characters at `p`. -/
def foldTake {β : Type} (f : β → Char → β) (b : β) (p : s.Pos) : Nat → β
  | 0 => b
  | n + 1 => if h : p = s.endPos then b else foldTake f (f b (p.get h)) (p.next h) n

/-- The first `n` characters at `p`, as a list (for short prefixes). -/
def takeL (p : s.Pos) (n : Nat) : List Char := (foldTake (fun l c => c :: l) [] p n).reverse

/-- The first `n` characters at `p`, as a string (copied in one piece). -/
def copyTake (p : s.Pos) (n : Nat) : String := ((s.sliceFrom p).take n).copy

/-! ## The walkers agree with the list view -/

theorem peek_eq (p : s.Pos) : peek p = (rest p).head? := by
  unfold peek
  split
  · subst_vars; simp [rest_endPos]
  · rename_i h; rw [rest_next p h]; rfl

theorem rest_adv (p : s.Pos) : rest (adv p) = (rest p).tail := by
  unfold adv
  split
  · subst_vars; simp [rest_endPos]
  · rename_i h; rw [rest_next p h]; rfl

theorem rest_advN (p : s.Pos) (n : Nat) : rest (advN p n) = (rest p).drop n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [advN, ih, rest_adv]; cases rest p <;> simp

theorem preW_eq (p : s.Pos) (d : List Char) : preW p d = d.isPrefixOf (rest p) := by
  induction d generalizing p with
  | nil => simp [preW]
  | cons c cs ih =>
    simp only [preW, ih, peek_eq, rest_adv]
    cases rest p <;> simp [List.isPrefixOf, Bool.beq_comm]

theorem countWhile_eq (P : Char → Bool) (p : s.Pos) (acc : Nat) :
    countWhile P p acc = acc + ((rest p).takeWhile P).length := by
  induction h : (rest p).length generalizing p acc with
  | zero =>
    rw [List.length_eq_zero_iff, rest_eq_nil_iff] at h
    subst h; unfold countWhile; simp [rest_endPos]
  | succ n ih =>
    have hp : p ≠ s.endPos := by
      intro he; subst he; simp [rest_endPos] at h
    unfold countWhile
    simp only [hp, ↓reduceDIte]; rw [rest_next p hp]
    have hl : (rest (p.next hp)).length = n := by rw [rest_next p hp] at h; simpa using h
    split
    · rename_i hP; rw [ih _ _ hl]; simp [hP]; omega
    · rename_i hP; simp [hP]

theorem foldTake_eq {β : Type} (f : β → Char → β) (b : β) (p : s.Pos) (n : Nat) :
    foldTake f b p n = ((rest p).take n).foldl f b := by
  induction n generalizing p b with
  | zero => rfl
  | succ n ih =>
    unfold foldTake
    split
    · subst_vars; simp [rest_endPos]
    · rename_i h; rw [ih, rest_next p h]; rfl

theorem takeL_eq (p : s.Pos) (n : Nat) : takeL p n = (rest p).take n := by
  have : ∀ (l acc : List Char), l.foldl (fun l c => c :: l) acc = l.reverse ++ acc := by
    intro l; induction l with
    | nil => simp
    | cons c cs ih => intro acc; simp [ih]
  simp [takeL, foldTake_eq, this]

theorem copyTake_toList (p : s.Pos) (n : Nat) : (copyTake p n).toList = (rest p).take n := by
  simp [copyTake, rest, Slice.toList_copy_take]

end Cursor

end LeanJinja2
