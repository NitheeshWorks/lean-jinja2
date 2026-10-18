import LeanJinja2

/-!
# Property tests: fast feedback where there is no proof

Generates values with a seeded generator and checks the properties that are
tested rather than proved. Not a substitute for the theorems; the check that
runs in under a second so a mistake surfaces while the change is still in
your head.

Run with `lake exe props`, or a different seed with `lake exe props 12345`.
A failure prints the seed and the value, so it reproduces exactly.
-/

/-- xorshift64*: four lines, no dependency, deterministic from the seed. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { s := x })

def Rng.nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if bound == 0 then 0 else v.toNat % bound, r)

/-- A property: a name and a check that, given a generator, either passes or
returns a description of the failing value. -/
structure Property where
  name : String
  check : Rng → Option String × Rng


open LeanJinja2

def Rng.pick {α : Type} [Inhabited α] (r : Rng) (xs : List α) : α × Rng :=
  let (i, r) := r.nat xs.length
  (xs[i]!, r)

/-! ## Generated templates -/

/-- A short text with markup characters but no tag start. -/
def genText (r : Rng) : String × Rng := Id.run do
  let (n, r) := r.nat 6
  let mut r := r
  let mut out : List Char := ['x']
  for _ in [0:n] do
    let (c, r') := r.pick ['a', 'b', ' ', '<', '>', '&', '\n', '}', '%']
    r := r'
    out := out ++ [c]
  return (String.ofList out, r)

def genExpr (r : Rng) : Expr × Rng :=
  let (k, r) := r.nat 6
  match k with
  | 0 => (.const (.int 3), r)
  | 1 => (.const (.str "<q>"), r)
  | 2 => (.name "s", r)
  | 3 => (.filter (.name "s") "upper" [] [], r)
  | 4 => (.filter (.name "xs") "length" [] [], r)
  | _ => (.binop .add (.name "n") (.const (.int 1)), r)

/-- One node; `sub` generates the nested bodies. -/
def genNode (sub : Rng → List Node × Rng) (textOK : Bool) (r : Rng) : Node × Rng :=
  let (k, r) := r.nat 8
  match k with
  | 0 => if textOK then let (t, r) := genText r; (.text t, r) else let (e, r) := genExpr r; (.output e, r)
  | 1 => let (e, r) := genExpr r; (.output e, r)
  | 2 => let (b, r) := sub r; let (e, r) := sub r; (.if_ [(.name "s", b)] e, r)
  | 3 => let (b, r) := sub r; (.for_ (.name "n") (.name "xs") none false b [], r)
  | 4 => let (e, r) := genExpr r; (.set (.name "t") e, r)
  | 5 => let (b, r) := sub r; (.with_ [(.name "s", .const (.str "w"))] b, r)
  | 6 => let (b, r) := sub r; (.filterBlock [⟨"upper", [], []⟩] b, r)
  | _ => let (b, r) := sub r; (.autoescape (.const (.bool true)) b, r)

/-- `k` nodes, never two texts in a row (the parser would merge them). -/
def genSeq (g : Bool → Rng → Node × Rng) : Nat → Bool → Rng → List Node × Rng
  | 0, _, r => ([], r)
  | k + 1, textOK, r =>
    let (nd, r) := g textOK r
    let (rest, r) := genSeq g k (!nd.isText) r
    (nd :: rest, r)

/-- A body nested at most `d` deep. -/
def genBody : Nat → Rng → List Node × Rng
  | 0, r => ([], r)
  | d + 1, r =>
    let (len, r) := r.nat 4
    genSeq (genNode (genBody d)) len true r

def vars : List (String × Value) := [("s", "a<b"), ("xs", .list [1, 2, 3]), ("n", 0)]

def renderTotal : Property where
  name := "render_total on generated templates (executable cross-check)"
  check r :=
    let (body, r) := genBody 6 r
    let t : Template := ⟨{}, none, body⟩
    match t.render vars with
    | .error .fuelExhausted => (some s!"ran out of fuel: {pretty body}", r)
    | _ => (none, r)

def printParse : Property where
  name := "parse_pretty_roundtrip on generated templates (executable cross-check)"
  check r :=
    let (body, r) := genBody 5 r
    let src := pretty body
    match parse {} src with
    | .ok t' => if pretty t' == src then (none, r) else (some s!"reprinted differently: {src}", r)
    | .error e => (some s!"did not parse: {src}: {e.msg}", r)

/-! ## Filters tested rather than proved -/

def genInts (r : Rng) : List Int × Rng := Id.run do
  let (n, r) := r.nat 8
  let mut r := r
  let mut out : List Int := []
  for _ in [0:n] do
    let (v, r') := r.nat 6
    r := r'
    out := out ++ [(v : Int) - 2]
  return (out, r)

def intsOf : Value → Option (List Int)
  | .list xs => xs.mapM (fun | .int i => some i | _ => none)
  | _ => none

def isSorted : List Int → Bool
  | a :: b :: rest => a ≤ b && isSorted (b :: rest)
  | _ => true

def countIn (x : Int) (xs : List Int) : Nat := (xs.filter (· == x)).length

def sortProp : Property where
  name := "sort returns a sorted permutation"
  check r :=
    let (xs, r) := genInts r
    match applyFilter {} "sort" (.list (xs.map Value.int)) [] [] with
    | .ok v =>
      match intsOf v with
      | some ys => if isSorted ys && xs.all (fun x => countIn x xs == countIn x ys) && ys.length == xs.length
          then (none, r) else (some s!"{xs} -> {ys}", r)
      | none => (some "not a list of ints", r)
    | .error _ => (some s!"error on {xs}", r)

def uniqueProp : Property where
  name := "unique keeps the first occurrence of each item, in order"
  check r :=
    let (xs, r) := genInts r
    let expected := xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
    match applyFilter {} "unique" (.list (xs.map Value.int)) [] [] >>= (fun v => .ok (intsOf v)) with
    | .ok (some ys) => if ys == expected then (none, r) else (some s!"{xs} -> {ys}", r)
    | _ => (some s!"failed on {xs}", r)

def genSpacey (r : Rng) : String × Rng := Id.run do
  let (n, r) := r.nat 10
  let mut r := r
  let mut out : List Char := []
  for _ in [0:n] do
    let (c, r') := r.pick ['a', 'b', ' ', '\t', '\n', 'c']
    r := r'
    out := out ++ [c]
  return (String.ofList out, r)

def trimProp : Property where
  name := "trim leaves no surrounding whitespace and keeps the middle"
  check r :=
    let (s, r) := genSpacey r
    match applyFilter {} "trim" (.str s) [] [] with
    | .ok (.str t) =>
      let ws := fun (c : Char) => c == ' ' || c == '\t' || c == '\n'
      let cs := s.toList
      let expected := ((cs.dropWhile ws).reverse.dropWhile ws).reverse
      if t.toList == expected then (none, r) else (some s!"{repr s} -> {repr t}", r)
    | _ => (some s!"failed on {repr s}", r)

def wordcountProp : Property where
  name := "wordcount counts whitespace-separated words"
  check r :=
    let (s, r) := genSpacey r
    let words := (s.toList.splitBy (fun a b => (a == ' ' || a == '\t' || a == '\n') == (b == ' ' || b == '\t' || b == '\n'))).filter
      (fun g => g.all (fun c => c == 'a' || c == 'b' || c == 'c'))
    match applyFilter {} "wordcount" (.str s) [] [] with
    | .ok (.int k) => if k == words.length then (none, r) else (some s!"{repr s} -> {k}, expected {words.length}", r)
    | _ => (some s!"failed on {repr s}", r)

def centerProp : Property where
  name := "center pads with spaces to the width, the sides differing by at most one"
  check r :=
    let (s, r) := genSpacey r
    let (w, r) := r.nat 20
    match applyFilter {} "center" (.str s) [.int w] [] with
    | .ok (.str t) =>
      let marg := t.length - s.length
      let centred := fun (left : Nat) =>
        (t.toList.drop left).take s.length == s.toList &&
        (t.toList.take left ++ t.toList.drop (left + s.length)).all (· == ' ')
      if t.length == max w s.length && (centred (marg / 2) || centred (marg / 2 + 1))
      then (none, r) else (some s!"{repr s} width {w} -> {repr t}", r)
    | _ => (some s!"failed on {repr s}", r)

def properties : List Property := [renderTotal, printParse, sortProp, uniqueProp, trimProp, wordcountProp, centerProp]

def main (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 88172645463325252
  let cases := 200
  let mut rng : Rng := { s := UInt64.ofNat seed }
  let mut failures := 0
  for p in properties do
    let mut failed : Option String := none
    for _ in [0:cases] do
      if failed.isSome then break
      let (res, rng') := p.check rng
      rng := rng'
      failed := res
    match failed with
    | none => IO.println s!"ok    {p.name} ({cases} cases)"
    | some why =>
      failures := failures + 1
      IO.println s!"FAIL  {p.name}: {why}  (seed {seed})"
  IO.println s!"{properties.length} properties, {failures} failing (seed {seed})"
  return if failures == 0 then 0 else 1
