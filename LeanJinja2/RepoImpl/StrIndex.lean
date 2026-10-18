import LeanJinja2.RepoImpl.Runtime

/-!
# A position-indexed view of a string

Python's `s[i]` counts characters; a Lean `String` is UTF-8, so finding the
`i`-th character walks `i` characters, and a negative `i` needs the length,
a walk over the whole string. A template loop that indexes every position
of a long string is then quadratic.

The view records the character count and the byte offset of every 8th
character (`strView`, built in one pass, under four bytes per character, none for
ASCII); with it `s[i]` walks at most 7 characters (`strViewIndex`). The renderer
keeps the view of the last string it indexed in heap cell 1
(`Render.getitemM`), so a loop over one string builds it once and each index
is then constant time. `strIndexCached` agrees with `strIndex` whatever the
cell holds (`strViewProp` in `tests/Props.lean`).
-/

namespace LeanJinja2

/-- The checkpoint spacing, in characters. -/
def strViewStep : Nat := 8

/-- Walk the characters of `s` from byte offset `p`, counting them and
recording the offset of every `strViewStep`-th. `fuel` bounds the walk (each
step advances at least one byte). -/
def strViewGo (s : String) : Nat → String.Pos.Raw → Nat → Array Value → Nat × Array Value
  | 0, _, k, acc => (k, acc)
  | fuel + 1, p, k, acc =>
    if p.byteIdx < s.utf8ByteSize then
      strViewGo s fuel (String.Pos.Raw.next s p) (k + 1)
        (if k % strViewStep == 0 then acc.push (.int p.byteIdx) else acc)
    else (k, acc)

/-- `s`'s character count and the byte offset of every `strViewStep`-th
character (as `Value.int`s, so the view can live in the heap). An ASCII
string needs no offsets (character `j` is byte `j`), so its view keeps none. -/
def strView (s : String) : Nat × Array Value :=
  let (n, cps) := strViewGo s (s.utf8ByteSize + 1) 0 0 #[]
  (n, if n = s.utf8ByteSize then #[] else cps)

/-- `n` characters on from byte offset `p`. -/
def strAdvance (s : String) : Nat → String.Pos.Raw → String.Pos.Raw
  | 0, p => p
  | n + 1, p => strAdvance s n (String.Pos.Raw.next s p)

/-- `n` characters back from byte offset `p`. -/
def strRetreat (s : String) : Nat → String.Pos.Raw → String.Pos.Raw
  | 0, p => p
  | n + 1, p => strRetreat s n (String.Pos.Raw.prev s p)

/-- Python `s[i]` through a view `(n, cps)` of `s`: the character. -/
def strViewIndex (s : String) (n : Nat) (cps : Array Value) (i : Int) : Option Char :=
  let j := if i < 0 then i + n else i
  if j < 0 || j ≥ n then none else
  let j := j.toNat
  if n = s.utf8ByteSize then some (String.Pos.Raw.get s ⟨j⟩) else
  let k := j % strViewStep
  -- walk from the nearer checkpoint: back from the next one (or the end)
  -- when that is closer
  if 2 * k > strViewStep && j - k + strViewStep ≤ n then
    let e := if j - k + strViewStep = n then s.utf8ByteSize else
      match cps[j / strViewStep + 1]? with | some (.int b) => b.toNat | _ => 0
    some (String.Pos.Raw.get s (strRetreat s (strViewStep - k) ⟨e⟩))
  else
  let b := match cps[j / strViewStep]? with | some (.int b) => b.toNat | _ => 0
  some (String.Pos.Raw.get s (strAdvance s k ⟨b⟩))

/-- Python `s[i]` for `0 ≤ i`, walking from the start: the character. -/
def strIndexNear (s : String) (i : Nat) : Option Char :=
  let p := strAdvance s i 0
  if p.byteIdx < s.utf8ByteSize then some (String.Pos.Raw.get s p) else none

/-- The heap cell holding the view of `s`. -/
def strViewCell (s : String) : List (String × Value) :=
  let (n, cps) := strView s
  [("s", .str s), ("n", .int n), ("cp", .list cps)]

/-- Python `s[i]`, reusing the view in `cell` when it is the view of `s`, or
building it: the character, and the new cell if it changed. Indexes
`0 ≤ i < strViewStep` walk from the start and leave the cell alone. Only
`strViewCell` writes the cell, so its keys are not compared. -/
def strIndexCached (cell : List (String × Value)) (s : String) (i : Int) :
    Option Char × Option (List (String × Value)) :=
  if 0 ≤ i && i < strViewStep then (strIndexNear s i.toNat, none) else
  match cell with
  | [(_, .str t), (_, .int n), (_, .list cps)] =>
    if t == s then (strViewIndex s n.toNat cps i, none)
    else let (n, cps) := strView s; (strViewIndex s n cps i, some (strViewCell s))
  | _ => let (n, cps) := strView s; (strViewIndex s n cps i, some (strViewCell s))

/-- The one-character strings of the Latin-1 characters, made once: `s[i]`
on one of them allocates nothing (as CPython's cached one-character
strings). -/
def asciiCharValues : Array Value :=
  (Array.range 256).map (fun i => .str (String.singleton (Char.ofNat i)))

/-- The string of one character, as a value (`charValue_eq`). -/
def charValue (c : Char) : Value :=
  if h : c.toNat < asciiCharValues.size then asciiCharValues[c.toNat] else .str (String.singleton c)

theorem charValue_eq (c : Char) : charValue c = .str (String.singleton c) := by
  unfold charValue asciiCharValues
  split
  · simp
  · rfl

end LeanJinja2
