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

def vars : List (String × Value) := [("s", "a<b"), ("xs", .list #[1, 2, 3]), ("n", 0)]

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
  | .list xs => xs.toList.mapM (fun | .int i => some i | _ => none)
  | _ => none

def isSorted : List Int → Bool
  | a :: b :: rest => a ≤ b && isSorted (b :: rest)
  | _ => true

def countIn (x : Int) (xs : List Int) : Nat := (xs.filter (· == x)).length

def sortProp : Property where
  name := "sort returns a sorted permutation"
  check r :=
    let (xs, r) := genInts r
    match applyFilter {} "sort" (.list (xs.map Value.int).toArray) [] [] with
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
    match applyFilter {} "unique" (.list (xs.map Value.int).toArray) [] [] >>= (fun v => .ok (intsOf v)) with
    | .ok (some ys) => if ys == expected then (none, r) else (some s!"{xs} -> {ys}", r)
    | _ => (some s!"failed on {xs}", r)

/-- An optional slice bound in `-15 .. 15`. -/
def genBound (r : Rng) : Option Int × Rng :=
  let (k, r) := r.nat 32
  (if k == 31 then none else some ((k : Int) - 15), r)

/-- The slice as indexes into the list (the definition before the one-pass
`sliceV`). -/
def sliceRef (xs : List Value) (a b c : Option Int) : Option (List Value) :=
  match sliceIndices xs.length a b c with
  | .ok is => some (is.filterMap (fun i => xs[i]?))
  | .error _ => none

def sliceProp : Property where
  name := "one-pass slicing of lists and strings equals indexing the indices"
  check r :=
    let (xs, r) := genInts r
    let (a, r) := genBound r
    let (b, r) := genBound r
    let (c, r) := genBound r
    let c := if c == some 0 then some 1 else c
    let opt := fun (o : Option Int) => o.map Value.int
    let vs := xs.map Value.int
    let str := String.ofList (xs.map (fun i => Char.ofNat (97 + (i.toNat % 26))))
    let gotL := sliceV .default (.list vs.toArray) (opt a) (opt b) (opt c)
    let gotS := sliceV .default (.str str) (opt a) (opt b) (opt c)
    let refS := (sliceRef (str.toList.map (fun ch => Value.str (String.singleton ch))) a b c).map
      (fun l => String.join (l.map Value.toStr))
    match gotL, sliceRef vs a b c, gotS, refS with
    | .ok (.list ys), some zs, .ok (.str t), some u =>
      if ys.toList.map Value.repr == zs.map Value.repr && t == u then (none, r)
      else (some s!"{xs}[{a}:{b}:{c}]", r)
    | _, _, _, _ => (some s!"failed on {xs}[{a}:{b}:{c}]", r)

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

/-- Occurrences of a character. -/
def countChar (c : Char) (s : String) : Nat := s.toList.count c

def lipsumProp : Property where
  name := "lipsum: n paragraphs of randrange(min, max) words, no word twice in a row (test_utils.py::TestLoremIpsum)"
  check r :=
    let (seed, r) := r.nat 1000000
    let (n, r) := r.nat 6
    let (lo, r) := r.nat 40
    let (w, r) := r.nat 60
    let lo : Int := lo + 1
    let hi : Int := lo + w + 1
    match lipsum n false lo hi (UInt64.ofNat seed), lipsum n true lo hi (UInt64.ofNat seed) with
    | .ok (.str t, _), .ok (.markup m, _) =>
      let paras := if n = 0 then [] else t.splitOn "\n\n"
      let words := fun (p : String) => (p.splitOn " ").map (fun x =>
        String.ofList ((x.toList.filter (fun c => c != ',' && c != '.')).map Char.toLower))
      let noRepeat := fun (ws : List String) => (ws.zip (ws.drop 1)).all (fun (a, b) => a != b)
      let ok := (if n = 0 then t == "" else countChar '\n' t == 2 * (n - 1)) &&
        paras.length == n &&
        paras.all (fun p => countChar ' ' p ≥ (lo - 1).toNat && (countChar ' ' p : Int) < hi - 1 &&
          p.endsWith "." && noRepeat (words p)) &&
        m.str == "\n".intercalate (paras.map (fun p => "<p>" ++ p ++ "</p>"))
      if ok then (none, r) else (some s!"lipsum({n}, min={lo}, max={hi}) seed {seed}: {repr t}", r)
    | _, _ => (some s!"lipsum({n}, min={lo}, max={hi}) failed", r)

def randomProp : Property where
  name := "random picks an item of the sequence; an empty one gives undefined"
  check r :=
    let (seed, r) := r.nat 1000000
    let (xs, r) := genInts r
    let vs := xs.map Value.int
    match randomChoice .default [] (UInt64.ofNat seed) (.list vs.toArray) with
    | .ok (.int i, _) => if xs.contains i then (none, r) else (some s!"{xs} gave {i}", r)
    | .ok (.undef _, _) => if xs.isEmpty then (none, r) else (some s!"{xs} gave undefined", r)
    | _ => (some s!"{xs} failed", r)

/-- A string of up to 300 characters of 1 to 4 UTF-8 bytes. -/
def genUnicode (r : Rng) : String × Rng := Id.run do
  let (n, r) := r.nat 300
  let mut r := r
  let mut out : String := ""
  for _ in [0:n] do
    let (c, r') := r.pick ['a', 'é', '€', '😀', ' ', 'z', 'ß']
    r := r'
    out := out.push c
  return (out, r)

/-- Python `x[i]` by the definition: normalise, then the `j`-th item. -/
def indexRef {α : Type} (xs : List α) (i : Int) : Option α :=
  let j := if i < 0 then i + xs.length else i
  if j < 0 then none else xs[j.toNat]?

def strViewProp : Property where
  name := "s[i] through the cached view and x[i] on an array equal indexing by definition"
  check r :=
    let (s, r) := genUnicode r
    let (t, r) := genUnicode r
    let (k, r) := r.nat 4
    let (i, r) := r.nat 700
    let i : Int := (i : Int) - 350
    let cell := match k with
      | 0 => []
      | 1 => strViewCell s
      | 2 => strViewCell t
      | _ => [("s", .str s), ("n", .int 0), ("cp", .list #[])]
    let cell := if k == 3 then [("junk", Value.none)] else cell
    let want := (indexRef s.toList i).map String.singleton
    let (got, cell') := strIndexCached cell s i
    let got := got.map String.singleton
    let (again, _) := strIndexCached (cell'.getD cell) s i
    let again := again.map String.singleton
    let xs := s.toList.map (fun c => Value.str (String.singleton c))
    let gotL := (indexList xs.toArray i).map Value.toStr
    if got == want && again == want && strIndex s i == want &&
        gotL == (indexRef xs i).map Value.toStr then (none, r)
    else (some s!"{repr s}[{i}] cell {k}: {got} {again}, want {want}", r)

/-- Pearson's statistic, times the expected count, of 10000 draws of
`random` over 10 items seeded by `seed`: `Σ (count - 1000)²`. -/
def chiSquare1000 (seed : UInt64) : Nat := Id.run do
  let xs : Array Value := (Array.range 10).map (fun (i : Nat) => Value.int (i : Int))
  let mut s := seed
  let mut c := Array.replicate 10 (0 : Nat)
  for _ in [0:10000] do
    match randomChoice .default [] s (.list xs) with
    | .ok (.int i, s') => s := s'; c := c.modify i.toNat (· + 1)
    | _ => pure ()
  return c.foldl (fun (acc n : Nat) => acc + ((n : Int) - 1000).natAbs ^ 2) 0

/-- Chi-square goodness of fit: 10 bins, 10000 draws, `X² < 27.88`, the 0.999
quantile of chi-square with 9 degrees of freedom (`X² = Σ (n - 1000)² / 1000`,
so `Σ (n - 1000)² < 27880`). Each case draws five seeds; a fair source exceeds
the bound once in a thousand seeds, so one of the five may (two or more: about
1e-5 per case, 0.2% per run of 200 cases), while a source biased by 2% on one
item exceeds it on most seeds. -/
def randomUniformProp : Property where
  name := "random is uniform: chi-square of 10000 draws over 10 items below 27.88 (p = 0.001, 9 df)"
  check r := Id.run do
    let mut r := r
    let mut over : List (Nat × Nat) := []
    for _ in [0:5] do
      let (seed, r') := r.nat 1000000000
      r := r'
      let x := chiSquare1000 (UInt64.ofNat seed)
      if x ≥ 27880 then over := (seed, x) :: over
    return (if over.length ≤ 1 then none else some s!"seeds with X² × 1000 ≥ 27880: {over}", r)

/-- Text built from pieces of links, brackets, entities and whitespace. -/
def genUrlText (r : Rng) : String × Rng := Id.run do
  let (n, r) := r.nat 12
  let mut r := r
  let mut out : String := ""
  for _ in [0:n] do
    let (p, r') := r.pick ["a", "é", " ", "\n", "\t", ".", ":", "@", "(", ")", "&lt;", "&gt;", "<",
      ">", ",", "www.", "http://", "https://", "x.com", "b.org", "/p?q#f", "mailto:", "ftp:", "1.2.3.4",
      "[::1]", "xn--ab", "\u00a0", "\u2003"]
    r := r'
    out := out ++ p
  return (out, r)

def urlizeTextProp : Property where
  name := "urlize in place equals urlize over the character list (urlizeSpec)"
  check r :=
    let (s, r) := genUrlText r
    let (k, r) := r.nat 4
    let o : UrlizeOpts := match k with
      | 0 => {}
      | 1 => { trim := some 5, relAttr := " rel=\"x\"" }
      | 2 => { extraSchemes := ["ftp:", "a"] }
      | _ => { extraSchemes := ["mailto:"], targetAttr := " target=\"_b\"" }
    let got := urlizeText o s
    let want := urlizeSpec o s
    if got == want then (none, r) else (some s!"opts {k} {repr s}: {repr got}, want {repr want}", r)

def properties : List Property := [renderTotal, printParse, sortProp, uniqueProp, sliceProp, trimProp, wordcountProp,
  centerProp, lipsumProp, randomProp, randomUniformProp, strViewProp, urlizeTextProp]

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
