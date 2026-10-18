import LeanJinja2.RepoImpl.Runtime

/-!
# The random source of `random` and `lipsum`

Upstream's `random` filter and `lipsum` global draw from Python's
process-wide `random` module. Here they draw from an explicit generator:
SplitMix64, seeded by `Environment.randomSeed`, its state kept in the
render's heap (cell `0`, see `Render`). A render is a function of its
template, its variables and that seed. The draws are not CPython's Mersenne
Twister, so a seeded upstream render and ours pick different items.
-/

namespace LeanJinja2

open LeanMarkupsafe

/-- One SplitMix64 step: the output and the next state. -/
def SplitMix.next (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9E3779B97F4A7C15
  let z := (s' ^^^ (s' >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s')

/-- A draw in `[0, n)` (`0` when `n = 0`). -/
def SplitMix.below (s : UInt64) (n : Nat) : Nat × UInt64 :=
  let (z, s') := SplitMix.next s
  (if n = 0 then 0 else z.toNat % n, s')

theorem SplitMix.below_lt (s : UInt64) {n : Nat} (h : 0 < n) : (SplitMix.below s n).1 < n := by
  simp only [SplitMix.below]
  split <;> simp_all [Nat.mod_lt]

/-- Python `randrange(a, b)`. -/
def SplitMix.range (s : UInt64) (a b : Int) : Except ValueError (Int × UInt64) :=
  if a < b then
    let (k, s') := SplitMix.below s (b - a).toNat
    .ok (a + k, s')
  else .error (.typeError s!"empty range in randrange({a}, {b})")

/-- The generator state a heap holds (cell `0`), or the seed. -/
def rngOf (seed : Nat) (heap : Heap) : UInt64 :=
  match (((heap[0]?).getD []).lookup "state" : Option Value) with
  | some (.int i) => UInt64.ofNat i.toNat
  | _ => UInt64.ofNat seed

/-- The heap a render starts from: cell `0` is the generator, cell `1` the
view of the last string indexed (`StrIndex`). -/
def initHeap (seed : Nat) : Heap := [[("state", .int (UInt64.ofNat seed).toNat)], []]

/-- Upstream `do_random(seq)`: `random.choice(seq)`, or an undefined value
for an empty sequence. -/
def randomChoice (pol : UndefinedPolicy) (heap : Heap) (s : UInt64) (v : Value) :
    Except ValueError (Value × UInt64) := do
  let n ← lenOf pol v
  if n = 0 then pure (.undef (.hint "No random item, sequence was empty."), s)
  else
    let (i, s') := SplitMix.below s n
    match pyItem heap v (.int i) with
    | some x => pure (x, s')
    | none => match v with
      | .dict _ => .error (.typeError s!"KeyError: {i}")
      | _ => .error (.typeError s!"'{v.typeName}' object is not subscriptable")

/-- The words of `lipsum` (a Latin vocabulary of our own). -/
def lipsumWords : Array String := #[
  "a", "aliquam", "amet", "animus", "aqua", "ars", "bellum", "caelum", "canis", "causa",
  "civis", "corpus", "cura", "deus", "dies", "domus", "dux", "est", "et", "fama", "fides",
  "flumen", "gloria", "homo", "ignis", "imperium", "iter", "lex", "liber", "locus", "lux",
  "magnus", "manus", "mare", "mens", "miles", "mons", "mors", "mundus", "natura", "navis",
  "nihil", "nomen", "nox", "numerus", "opus", "orbis", "pater", "pax", "populus", "porta",
  "rex", "sapientia", "semper", "silva", "sol", "spes", "tempus", "terra", "urbs", "verbum",
  "via", "vita", "vox"]

/-- Python `str.capitalize` on a lower-case word. -/
def capitalizeWord (w : String) : String :=
  match w.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => w

/-- A paragraph ends with a full stop (upstream replaces a final comma). -/
def lipsumFinish (p : String) : String :=
  if p.endsWith "," then String.ofList p.toList.dropLast ++ "."
  else if p.endsWith "." then p else p ++ "."

/-- Upstream's paragraph loop: `count` words, none repeating the one before,
a comma when `idx - randrange(3, 8) > last_comma`, a full stop when
`idx - randrange(10, 20) > last_fullstop`, and a capital after a full stop. -/
def lipsumPara (idx : Nat) : Nat → UInt64 → Option Nat → Bool → Int → Int → String →
    String × UInt64
  | 0, s, _, _, _, _, p => (lipsumFinish p, s)
  | k + 1, s, last, cap, lc, lf, p =>
    let (j, s) := match last with
      | none => SplitMix.below s lipsumWords.size
      | some l =>
        let (j, s) := SplitMix.below s (lipsumWords.size - 1)
        (if j ≥ l then j + 1 else j, s)
    let w := lipsumWords.getD j ""
    let w := if cap then capitalizeWord w else w
    let (r1, s) := SplitMix.below s 5
    let (w, lc, lf) :=
      if (idx : Int) - (3 + r1 : Nat) > lc then (w ++ ",", (idx : Int), lf + 2) else (w, lc, lf)
    let (r2, s) := SplitMix.below s 10
    let (w, lc, lf, cap) :=
      if (idx : Int) - (10 + r2 : Nat) > lf then (w ++ ".", (idx : Int), (idx : Int), true)
      else (w, lc, lf, false)
    lipsumPara (idx + 1) k s (some j) cap lc lf (if idx = 0 then w else p ++ " " ++ w)

/-- The paragraphs of `lipsum`. -/
def lipsumParas (lo hi : Int) : Nat → UInt64 → List String →
    Except ValueError (List String × UInt64)
  | 0, s, acc => .ok (acc.reverse, s)
  | k + 1, s, acc => do
    let (c, s) ← SplitMix.range s lo hi
    let (p, s) := lipsumPara 0 c.toNat s none true 0 0 ""
    lipsumParas lo hi k s (p :: acc)

/-- Upstream `generate_lorem_ipsum(n, html, min, max)`: `n` paragraphs of
`randrange(min, max)` words, as `<p>` markup or blank-line separated text. -/
def lipsum (n : Int) (html : Bool) (lo hi : Int) (s : UInt64) : Except ValueError (Value × UInt64) := do
  let (ps, s) ← lipsumParas lo hi n.toNat s []
  if html then
    pure (.markup (Markup.markSafe ("\n".intercalate (ps.map fun p => "<p>" ++ (escape p).str ++ "</p>"))), s)
  else pure (.str ("\n\n".intercalate ps), s)

/-- An integer argument of `lipsum` (Python `range`/`randrange`). -/
def lipsumInt (v : Value) : Except ValueError Int :=
  match v with
  | .int i => .ok i
  | .bool b => .ok (if b then 1 else 0)
  | _ => .error (.typeError s!"'{v.typeName}' object cannot be interpreted as an integer")

/-- `lipsum(n=5, html=True, min=20, max=100)` called with these arguments. -/
def lipsumCall (pol : UndefinedPolicy) (s : UInt64) (args : List Value) (kw : List (String × Value)) :
    Except ValueError (Value × UInt64) := do
  let names := ["n", "html", "min", "max"]
  if args.length > 4 then
    .error (.typeError s!"generate_lorem_ipsum() takes from 0 to 4 positional arguments but {args.length} were given")
  else
  match kw.find? (fun p => !names.contains p.1) with
  | some (k, _) => .error (.typeError s!"generate_lorem_ipsum() got an unexpected keyword argument '{k}'")
  | none =>
  let arg := fun (i : Nat) => match args[i]? with
    | some v => some v
    | none => match names[i]? with
      | some k => kw.lookup k
      | none => none
  let n ← match arg 0 with | some v => lipsumInt v | none => pure 5
  let html ← match arg 1 with | some v => truthyOf pol v | none => pure true
  let lo ← match arg 2 with | some v => lipsumInt v | none => pure 20
  let hi ← match arg 3 with | some v => lipsumInt v | none => pure 100
  lipsum n html lo hi s

end LeanJinja2
