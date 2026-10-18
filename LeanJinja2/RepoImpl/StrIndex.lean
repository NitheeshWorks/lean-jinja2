import LeanJinja2.RepoImpl.Runtime

/-!
# A position-indexed view of a string

Python's `s[i]` counts characters; a Lean `String` is UTF-8, so finding the
`i`-th character walks `i` characters, and a negative `i` needs the length,
a walk over the whole string. A template loop that indexes every position
of a long string is then quadratic.

The view records the character count and the byte offset of every 64th
character (`strView`, built in one pass, under half a byte per character);
with it `s[i]` walks at most 63 characters (`strViewIndex`). The renderer
keeps the view of the last string it indexed in heap cell 1
(`Render.getitemM`), so a loop over one string builds it once and each index
is then constant time. `strIndexCached` agrees with `strIndex` whatever the
cell holds (`strViewProp` in `tests/Props.lean`).
-/

namespace LeanJinja2

/-- The checkpoint spacing, in characters. -/
def strViewStep : Nat := 64

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
character (as `Value.int`s, so the view can live in the heap). -/
def strView (s : String) : Nat × Array Value := strViewGo s (s.utf8ByteSize + 1) 0 0 #[]

/-- `n` characters on from byte offset `p`. -/
def strAdvance (s : String) : Nat → String.Pos.Raw → String.Pos.Raw
  | 0, p => p
  | n + 1, p => strAdvance s n (String.Pos.Raw.next s p)

/-- Python `s[i]` through a view `(n, cps)` of `s`. -/
def strViewIndex (s : String) (n : Nat) (cps : Array Value) (i : Int) : Option String :=
  let j := if i < 0 then i + n else i
  if j < 0 || j ≥ n then none else
  let j := j.toNat
  let b := match cps[j / strViewStep]? with | some (.int b) => b.toNat | _ => 0
  some (String.singleton (String.Pos.Raw.get s (strAdvance s (j % strViewStep) ⟨b⟩)))

/-- Python `s[i]` for `0 ≤ i`, walking from the start. -/
def strIndexNear (s : String) (i : Nat) : Option String :=
  let p := strAdvance s i 0
  if p.byteIdx < s.utf8ByteSize then some (String.singleton (String.Pos.Raw.get s p)) else none

/-- The heap cell holding the view of `s`. -/
def strViewCell (s : String) : List (String × Value) :=
  let (n, cps) := strView s
  [("s", .str s), ("n", .int n), ("cp", .list cps)]

/-- Python `s[i]`, reusing the view in `cell` when it is the view of `s`, or
building it: the result and the cell to keep. Indexes `0 ≤ i < strViewStep`
walk from the start and leave the cell alone. -/
def strIndexCached (cell : List (String × Value)) (s : String) (i : Int) :
    Option String × List (String × Value) :=
  if 0 ≤ i && i < strViewStep then (strIndexNear s i.toNat, cell) else
  match cell with
  | [("s", .str t), ("n", .int n), ("cp", .list cps)] =>
    if t == s then (strViewIndex s n.toNat cps i, cell)
    else let (n, cps) := strView s; (strViewIndex s n cps i, strViewCell s)
  | _ => let (n, cps) := strView s; (strViewIndex s n cps i, strViewCell s)

end LeanJinja2
