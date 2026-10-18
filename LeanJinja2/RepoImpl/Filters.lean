import LeanJinja2.RepoImpl.Format
import LeanJinja2.RepoImpl.Unique
import LeanJinja2.RepoImpl.Random
import LeanJinja2.RepoImpl.Urlize

/-!
# Builtin filters and tests

Upstream `jinja2.filters.FILTERS` and `jinja2.tests.TESTS`, as total
functions of the value and the arguments. `FCtx` carries what upstream reads
from the environment and evaluation context: the autoescape flag, the
undefined policy, the namespace heap, `truncate.leeway`, and the host's
custom filters and tests.

`random` draws from the explicit source of `Random`. Not provided:
`wordwrap`'s hyphen rules; see `docs/traceability.toml`.
-/

namespace LeanJinja2

set_option linter.unusedVariables false

open LeanMarkupsafe

/-- What filters and tests read from the environment. -/
structure FCtx where
  autoescape : Bool := false
  pol : UndefinedPolicy := .default
  heap : Heap := []
  leeway : Nat := 5
  filters : List (String × NativeFn) := []
  tests : List (String × NativeFn) := []
  vars : List (String × Value) := []
  /-- The state of the random source (see `Random`). -/
  rng : UInt64 := 0
  /-- `policies["urlize.rel"]`, `["urlize.target"]`, `["urlize.extra_schemes"]`. -/
  urlizeRel : Option String := some "noopener"
  urlizeTarget : Option String := none
  urlizeExtraSchemes : List String := []

instance : Inhabited FCtx := ⟨{}⟩

/-- Positional argument `i` or keyword `name`. -/
def argAt (args : List Value) (kwargs : List (String × Value)) (i : Nat) (name : String) :
    Option Value :=
  match args[i]? with
  | some v => some v
  | none => kwargs.lookup name

def Value.asInt? : Value → Option Int
  | .int i => some i
  | .bool b => some (if b then 1 else 0)
  | _ => Option.none

def typeErr {α : Type} (msg : String) : Except ValueError α := .error (.typeError msg)

/-- An integer argument, or a `TypeError`. -/
def intArg (v : Value) (what : String) : Except ValueError Int :=
  match v.asInt? with
  | some i => .ok i
  | none => typeErr s!"{what} must be an integer, not {v.typeName}"

/-- Upstream `ignore_case`: strings are lowered, other values unchanged. -/
def ignoreCase : Value → Value
  | .str s => .str (strLower s)
  | .markup m => .markup ⟨strLower m.str⟩
  | v => v

/-- Upstream `_prepare_attribute_parts`. -/
def attrParts : Value → List Value
  | .none => []
  | .str s => (s.splitOn ".").map fun p =>
      if !p.isEmpty && p.toList.all Char.isDigit then .int (digitsValue 10 p.toList) else .str p
  | v => [v]

/-- Upstream `make_attrgetter(attribute, default=default)`. -/
def attrGet (fc : FCtx) (attr : Value) (default : Option Value) (item : Value) :
    Except ValueError Value :=
  (attrParts attr).foldlM (fun it part => do
    let r ← getitemV fc.pol fc.heap it part
    match default, r with
    | some d, .undef _ => pure d
    | _, _ => pure r) item

/-- A stable insertion sort with a fallible order. -/
def sortBy {α : Type} (le : α → α → Except ValueError Bool) (xs : List α) :
    Except ValueError (List α) :=
  let rec ins (x : α) : List α → Except ValueError (List α)
    | [] => .ok [x]
    | y :: ys => do
      if ← le y x then do let r ← ins x ys; pure (y :: r) else pure (x :: y :: ys)
  xs.foldlM (fun acc x => ins x acc) []

/-- `a ≤ b` in Python's order. -/
def pyLe (a b : Value) : Except ValueError Bool :=
  match Value.pyCmp a b with
  | .ok o => .ok (o != .gt)
  | .error m => typeErr m

/-- Python `str.strip(chars)`. -/
def stripChars (chars : Option (List Char)) (l : List Char) : List Char :=
  match chars with
  | none => stripList l
  | some cs => ((l.dropWhile (cs.contains ·)).reverse.dropWhile (cs.contains ·)).reverse

/-- Wrap a text result as markup when the input was markup (MarkupSafe's
string methods return `Markup`). -/
def keepKind (v : Value) (s : String) : Value :=
  match v with
  | .markup _ => .markup (Markup.markSafe s)
  | _ => .str s

/-- Python `str.title` as upstream's `do_title` computes it: words begin after
runs of `-`, whitespace, `(`, `{`, `[`, `<`. -/
def titleList (l : List Char) : List Char :=
  let isSep := fun (c : Char) => c == '-' || isSpace c || c == '(' || c == '{' || c == '[' || c == '<'
  let rec go : List Char → Bool → List Char
    | [], _ => []
    | c :: cs, start =>
      if isSep c then c :: go cs true
      else (if start then charUpper c else charLower c) :: go cs false
  go l true

/-- `\w+` word count. -/
def wordCount (l : List Char) : Nat :=
  let isW := fun (c : Char) => c.isAlphanum || c == '_' || (c.val ≥ 128 && !isSpace c)
  let rec go : List Char → Bool → Nat
    | [], _ => 0
    | c :: cs, inWord => if isW c then (if inWord then go cs true else 1 + go cs true) else go cs false
  go l false

/-- Python `float(s)` for a string: decimal, exponent, sign, surrounding
whitespace. -/
def parseFloatStr (s : String) : Option (Int × Nat) :=
  let l := stripList s.toList
  let (neg, l) := match l with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ip := l.takeWhile (fun (c : Char) => c.isDigit || c == '_')
  let r := l.drop ip.length
  let (fp, r) := match r with
    | '.' :: r' => let f := r'.takeWhile (fun (c : Char) => c.isDigit || c == '_'); (f, r'.drop f.length)
    | _ => ([], r)
  if ip.isEmpty && fp.isEmpty then none else
  let (e, r) : Int × List Char := match r with
    | c :: r' =>
      if c == 'e' || c == 'E' then
        let (en, r'') := match r' with
          | '-' :: x => (true, x) | '+' :: x => (false, x) | x => (false, x)
        let ed := r''.takeWhile Char.isDigit
        if ed.isEmpty then (0, c :: r') else
        ((if en then -1 else 1) * (digitsValue 10 ed : Int), r''.drop ed.length)
      else (0, c :: r')
    | [] => (0, [])
  if !r.isEmpty then none else
  let fd := fp.filter (· != '_')
  let m : Int := digitsValue 10 (ip.filter (· != '_') ++ fd)
  let m := if neg then -m else m
  let sc : Int := (fd.length : Int) - e
  if sc ≥ 0 then some (decNorm m sc.toNat) else some (m * 10 ^ (-sc).toNat, 0)

/-- Python `int(s, base)` for a string. -/
def parseIntStr (s : String) (base : Nat) : Option Int :=
  let l := stripList s.toList
  let (neg, l) := match l with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let (base, l) :=
    match base, l with
    | 16, '0' :: c :: r => if c == 'x' || c == 'X' then (16, r) else (16, '0' :: c :: r)
    | 8, '0' :: c :: r => if c == 'o' || c == 'O' then (8, r) else (8, '0' :: c :: r)
    | 2, '0' :: c :: r => if c == 'b' || c == 'B' then (2, r) else (2, '0' :: c :: r)
    | b, r => (b, r)
  if l.isEmpty || l.head? == some '_' || l.getLast? == some '_' then none
  else if l.all (fun c => c == '_' || (digitVal base c).isSome) then
    let v : Int := digitsValue base l
    some (if neg then -v else v)
  else none

/-- Upstream `url_quote`: UTF-8 percent-encoding; `/` stays unless `forQs`,
where a space becomes `+`. -/
def urlQuote (s : String) (forQs : Bool) : String :=
  let hex := fun (b : UInt8) =>
    let h := (Nat.toDigits 16 b.toNat).map Char.toUpper
    "%" ++ String.ofList (if h.length < 2 then '0' :: h else h)
  let bytes := s.toUTF8.toList
  String.join (bytes.map fun b =>
    let c := Char.ofNat b.toNat
    if b < 128 && (c.isAlphanum || c == '_' || c == '.' || c == '-' || c == '~') then String.singleton c
    else if b == 47 && !forQs then "/"
    else if b == 32 && forQs then "+"
    else hex b)

/-- The names of the builtin filters. -/
def builtinFilters : List String :=
  ["abs", "attr", "batch", "capitalize", "center", "count", "d", "default", "dictsort", "e",
   "escape", "filesizeformat", "first", "float", "forceescape", "format", "groupby", "indent",
   "int", "join", "last", "length", "list", "lower", "items", "map", "min", "max", "pprint", "random",
   "reject", "rejectattr", "replace", "reverse", "round", "safe", "select", "selectattr",
   "slice", "sort", "string", "striptags", "sum", "title", "trim", "truncate", "unique",
   "upper", "urlencode", "urlize", "wordcount", "wordwrap", "xmlattr", "tojson"]

/-- The names of the builtin tests. -/
def builtinTests : List String :=
  ["odd", "even", "divisibleby", "defined", "undefined", "filter", "test", "none", "boolean",
   "false", "true", "integer", "float", "lower", "upper", "string", "mapping", "number",
   "sequence", "iterable", "callable", "sameas", "escaped", "in", "==", "eq", "equalto", "!=",
   "ne", ">", "gt", "greaterthan", "ge", ">=", "<", "lt", "lessthan", "<=", "le"]

def FCtx.hasFilter (fc : FCtx) (n : String) : Bool :=
  builtinFilters.contains n || (fc.filters.lookup n).isSome

def FCtx.hasTest (fc : FCtx) (n : String) : Bool :=
  builtinTests.contains n || (fc.tests.lookup n).isSome

/-- A native function's error is a `TypeError`. -/
def liftNative (r : Except String Value) : Except ValueError Value :=
  match r with
  | .ok v => .ok v
  | .error m => .error (.typeError m)

/-- Comparison tests. -/
def cmpTest (op : String) (a b : Value) : Except ValueError Bool :=
  match op with
  | "==" | "eq" | "equalto" => .ok (Value.pyEq a b)
  | "!=" | "ne" => .ok (!Value.pyEq a b)
  | _ =>
    match Value.pyCmp a b with
    | .error m => typeErr m
    | .ok o =>
      match op with
      | ">" | "gt" | "greaterthan" => .ok (o == .gt)
      | ">=" | "ge" => .ok (o != .lt)
      | "<" | "lt" | "lessthan" => .ok (o == .lt)
      | _ => .ok (o != .gt)

/-- Whether a value is callable. -/
def Value.isCallable : Value → Bool
  | .macro .. | .native _ | .method .. | .superRef .. | .joiner _ => true
  | .loop _ _ _ _ _ (some _) _ => true
  | _ => false

/-- Apply a test (upstream `Environment.call_test`). -/
def applyTest (fc : FCtx) (name : String) (v : Value) (args : List Value)
    (kwargs : List (String × Value)) : Except ValueError Bool := do
  let a0 := argAt args kwargs 0
  let undefOp := fun (k : Except ValueError Bool) =>
    match v with
    | .undef i => failUndef i
    | _ => k
  match name with
  | "odd" => undefOp do let r ← arith .mod v (.int 2); pure (Value.pyEq r (.int 1))
  | "even" => undefOp do let r ← arith .mod v (.int 2); pure (Value.pyEq r (.int 0))
  | "divisibleby" =>
    match a0 "num" with
    | some n => undefOp do let r ← arith .mod v n; pure (Value.pyEq r (.int 0))
    | none => typeErr "test_divisibleby() missing 1 required positional argument: 'num'"
  | "defined" => pure !v.isUndef
  | "undefined" => pure v.isUndef
  | "filter" => pure (match v with | .str s => fc.hasFilter s | _ => false)
  | "test" => pure (match v with | .str s => fc.hasTest s | _ => false)
  | "none" => pure (match v with | .none => true | _ => false)
  | "boolean" => pure (match v with | .bool _ => true | _ => false)
  | "false" => pure (match v with | .bool false => true | _ => false)
  | "true" => pure (match v with | .bool true => true | _ => false)
  | "integer" => pure (match v with | .int _ => true | _ => false)
  | "float" => pure (match v with | .float .. => true | _ => false)
  | "lower" => do
    let s ← strOf fc.pol v
    let l := s.toList
    pure (l.any Char.isLower && !l.any Char.isUpper)
  | "upper" => do
    let s ← strOf fc.pol v
    let l := s.toList
    pure (l.any Char.isUpper && !l.any Char.isLower)
  | "string" => pure (v.text?.isSome)
  | "mapping" => pure (match v with | .dict _ => true | _ => false)
  | "number" => pure (v.num?.isSome)
  | "sequence" => pure (match v with
      | .list _ | .tuple _ | .namedTuple .. | .str _ | .markup _ | .dict _ => true
      | .undef _ => fc.pol != .strict
      | _ => false)
  | "iterable" => pure (match v with
      | .list _ | .tuple _ | .namedTuple .. | .str _ | .markup _ | .dict _ | .ns _ => true
      | .undef _ => fc.pol != .strict
      | _ => false)
  | "callable" => pure v.isCallable
  | "sameas" =>
    match a0 "other" with
    | some o => pure (match v, o with
        | .none, .none => true | .bool a, .bool b => a == b
        | .ns a, .ns b | .cycler a, .cycler b | .joiner a, .joiner b => a == b
        | .undef _, .undef _ => false
        | .int a, .int b => a == b && a ≥ -5 && a ≤ 256
        | _, _ => false)
    | none => typeErr "test_sameas() missing 1 required positional argument: 'other'"
  | "escaped" => pure (match v with | .markup _ => true | _ => false)
  | "in" =>
    match a0 "seq" with
    | some s => containsV fc.pol fc.heap v s
    | none => typeErr "test_in() missing 1 required positional argument: 'seq'"
  | "==" | "eq" | "equalto" | "!=" | "ne" | ">" | "gt" | "greaterthan" | "ge" | ">=" | "<"
  | "lt" | "lessthan" | "<=" | "le" =>
    match a0 "b" with
    | some b =>
      match v, b with
      | .undef i, _ => if i.policy fc.pol == .strict || !(name == "==" || name == "eq" || name == "equalto" ||
          name == "!=" || name == "ne") then failUndef i else cmpTest name v b
      | _, .undef i => if i.policy fc.pol == .strict then failUndef i else cmpTest name v b
      | _, _ => cmpTest name v b
    | none => typeErr s!"{name} test requires an argument"
  | _ =>
    match fc.tests.lookup name with
    | some f => do
      let r ← liftNative (f fc.vars (v :: args) kwargs)
      truthyOf fc.pol r
    | none => .error (.runtime s!"No test named '{name}'.")

/-- Upstream `do_join` (`d`, `attribute`). -/
def joinFilter (fc : FCtx) (items : List Value) (d : Value) : Except ValueError Value := do
  if !fc.autoescape then
    let ss ← items.mapM (strOf fc.pol)
    let sep ← strOf fc.pol d
    pure (.str (sep.intercalate ss))
  else
    match d with
    | .markup m => do
      let ms ← items.mapM (escapeOf fc.pol)
      pure (.markup (Markup.joinMarkup m ms))
    | _ =>
      if items.any Value.hasHtml then do
        let sep ← strOf fc.pol d
        let ms ← items.mapM (escapeOf fc.pol)
        pure (.markup (Markup.joinMarkup (escape sep) ms))
      else do
        let ss ← items.mapM (strOf fc.pol)
        let sep ← strOf fc.pol d
        pure (.str (sep.intercalate ss))

/-- `truncate` on characters (upstream `do_truncate`). -/
def truncateList (l : List Char) (length : Nat) (killwords : Bool) (endS : List Char)
    (leeway : Nat) : List Char :=
  if l.length ≤ length + leeway then l
  else
    let cut := l.take (length - endS.length)
    if killwords then cut ++ endS
    else
      -- `rsplit(" ", 1)[0]`: drop the last space and everything after it
      let r := cut.reverse
      let kept := match r.dropWhile (· != ' ') with
        | ' ' :: rest => rest.reverse
        | _ => cut
      kept ++ endS

/-- Upstream `do_indent`. -/
def indentText (s : String) (ind : String) (first blank : Bool) : String :=
  let lines := (splitLines (s.toList ++ ['\n'])).map String.ofList
  let body :=
    if blank then ("\n" ++ ind).intercalate lines
    else match lines with
      | [] => ""
      | l0 :: rest =>
        if rest.isEmpty then l0
        else l0 ++ "\n" ++ "\n".intercalate (rest.map (fun l => if l.isEmpty then l else ind ++ l))
  if first then ind ++ body else body

/-- Upstream `do_filesizeformat`. -/
def fileSizeFormat (x : Int × Nat) (binary : Bool) : String :=
  let base : Nat := if binary then 1024 else 1000
  let prefixes := if binary then ["KiB", "MiB", "GiB", "TiB", "PiB", "EiB", "ZiB", "YiB"]
    else ["kB", "MB", "GB", "TB", "PB", "EB", "ZB", "YB"]
  if decCmp x (1, 0) == .eq then "1 Byte"
  else if decCmp x ((base : Int), 0) == .lt then
    s!"{String.ofList (intDigits (x.1.tdiv (10 ^ x.2)))} Bytes"
  else
    let rec go : List String → Nat → String
      | [], _ => ""
      | [p], i =>
        let unit : Int := (base : Int) ^ (i + 2)
        let (m, s) := decDiv (decMul ((base : Int), 0) x) (unit, 0)
        fixedText m s 1 ++ " " ++ p
      | p :: ps, i =>
        let unit : Int := (base : Int) ^ (i + 2)
        if decCmp x (unit, 0) == .lt then
          let (m, s) := decDiv (decMul ((base : Int), 0) x) (unit, 0)
          fixedText m s 1 ++ " " ++ p
        else go ps (i + 1)
    go prefixes 0

/-- Upstream `do_round`. -/
def roundFilter (x : Int × Nat) (precision : Int) (method : String) : Except ValueError Value :=
  if precision < 0 then
    -- round x / 10^k to an integer, then scale back
    let k := precision.natAbs
    let y := (x.1, x.2 + k)
    match roundFilterAux y 0 method with
    | .ok (m, s) => .ok (mkFloat (decMul (m, s) ((10 : Int) ^ k, 0)))
    | .error e => .error e
  else match roundFilterAux x precision.toNat method with
    | .ok d => .ok (mkFloat d)
    | .error e => .error e
where
  roundFilterAux (x : Int × Nat) (p : Nat) (method : String) : Except ValueError (Int × Nat) :=
  match method with
  | "common" => .ok (roundHalfEven x.1 x.2 p, p)
  | "floor" =>
    let d : Int := 10 ^ (x.2 - min x.2 p)
    .ok (Int.fdiv (x.1 * 10 ^ (p - min x.2 p)) d, p)
  | "ceil" =>
    let d : Int := 10 ^ (x.2 - min x.2 p)
    .ok (-(Int.fdiv (-(x.1 * 10 ^ (p - min x.2 p))) d), p)
  | _ => .error (.runtime "method must be common, ceil or floor")

/-- Upstream `do_xmlattr`. -/
def xmlAttr (fc : FCtx) (kvs : List (Value × Value)) (autospace : Bool) : Except ValueError Value := do
  let items ← kvs.filterMapM fun (k, v) => do
    match v with
    | .none | .undef _ => pure none
    | _ =>
      let key ← strOf fc.pol k
      if key.toList.any (fun c => isSpace c || c == '/' || c == '>' || c == '=') then
        .error (.typeError s!"Invalid character in attribute name: {pyStrRepr key}")
      else do
        let ev ← escapeOf fc.pol v
        pure (some ((escape key).str ++ "=\"" ++ ev.str ++ "\""))
  let rv := " ".intercalate items
  let rv := if autospace && !rv.isEmpty then " " ++ rv else rv
  pure (if fc.autoescape then .markup (Markup.markSafe rv) else .str rv)

/-- Upstream `do_wordwrap` without hyphen breaking: greedy wrapping of each
line at `width`, breaking long words when asked. -/
def wordWrap (s : String) (width : Nat) (breakLong : Bool) (wrap : String) : String :=
  let wrapLine := fun (line : List Char) =>
    let words := splitWs line
    let rec go : Nat → List (List Char) → List Char → List (List Char)
      | 0, _, cur => if cur.isEmpty then [] else [cur]
      | _ + 1, [], cur => if cur.isEmpty then [] else [cur]
      | fuel + 1, w :: ws, cur =>
        if cur.isEmpty then
          if w.length > width && breakLong && width > 0 then
            w.take width :: go fuel (w.drop width :: ws) []
          else go fuel ws w
        else if cur.length + 1 + w.length ≤ width then go fuel ws (cur ++ ' ' :: w)
        else cur :: go fuel (w :: ws) []
    (go (words.foldl (fun n w => n + w.length + 2) 2) words []).map String.ofList
  wrap.intercalate ((splitLines s.toList).map (fun l => wrap.intercalate (wrapLine l)))

/-- A filter implementation: environment context, value, arguments. -/
abbrev FilterFn := FCtx → Value → List Value → List (String × Value) → Except ValueError Value

/-- Upstream filter `abs`. -/
def Filters.abs (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  match v with
  | .int i => pure (.int i.natAbs)
  | .float m s => pure (.float m.natAbs s)
  | .bool b => pure (.int (if b then 1 else 0))
  | .undef i => failUndef i
  | _ => typeErr s!"bad operand type for abs(): '{v.typeName}'"

/-- Upstream filter `attr`. -/
def Filters.attr (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let pol := fc.pol
  match a 0 "name" with
  | some (.str n) =>
    match v with
    | .undef i => if i.policy pol == .chainable then pure v else failUndef i
    | _ => pure ((pyAttr fc.heap v n).getD (.undef (.attr v.objectTypeRepr n)))
  | _ => typeErr "attr requires a string name"

/-- Upstream filter `batch`. -/
def Filters.batch (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let a := argAt args kwargs
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let n ← intArg ((a 0 "linecount").getD .none) "linecount"
  if n ≤ 0 then typeErr "batch linecount must be positive" else
  let fill := a 1 "fill_with"
  let xs ← iter v
  let k := n.toNat
  let rec chunks : Nat → List Value → List Value
    | 0, _ => []
    | _ + 1, [] => []
    | fuel + 1, ys =>
      let c := ys.take k
      let c := match fill with
        | some f => if c.length < k && (match f with | .none => false | _ => true)
            then c ++ List.replicate (k - c.length) f else c
        | none => c
      .list c :: chunks fuel (ys.drop k)
  pure (.list (chunks (xs.length + 1) xs))

/-- Upstream filter `capitalize`. -/
def Filters.capitalize (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  do let s ← strOf pol v; pure (keepKind v (strCapitalize s))

/-- Upstream filter `center`. -/
def Filters.center (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let pol := fc.pol
  do
  let s ← strOf pol v
  let w ← intArg ((a 0 "width").getD (.int 80)) "width"
  let n := s.length
  if w.toNat ≤ n then pure (keepKind v s) else
  let marg := w.toNat - n
  let left := marg / 2 + (marg % 2 * (w.toNat % 2))
  pure (keepKind v (String.ofList (List.replicate left ' ') ++ s ++
    String.ofList (List.replicate (marg - left) ' ')))

/-- Upstream filter `count`, `length`. -/
def Filters.length (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  do let n ← lenOf pol v; pure (.int n)

/-- Upstream filter `d`, `default`. -/
def Filters.default (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let pol := fc.pol
  do
  let dv := (a 0 "default_value").getD (.str "")
  let boolean := ((a 1 "boolean").map Value.truthy).getD false
  if v.isUndef then pure dv
  else if boolean then do
    let t ← truthyOf pol v
    pure (if t then v else dv)
  else pure v

/-- Upstream filter `dictsort`. -/
def Filters.dictsort (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  do
  let cs := ((a 0 "case_sensitive").map Value.truthy).getD false
  let by_ := (a 1 "by").getD (.str "key")
  let rev := ((a 2 "reverse").map Value.truthy).getD false
  let pos ← match by_ with
    | .str "key" => pure 0 | .str "value" => pure 1
    | _ => .error (.runtime "You can only sort by either \"key\" or \"value\"")
  match v with
  | .dict kvs => do
    let key := fun (p : Value × Value) => let x := if pos == 0 then p.1 else p.2
      if cs then x else ignoreCase x
    let sorted ← sortBy (fun p q => if rev then pyLe (key q) (key p) else pyLe (key p) (key q)) kvs
    pure (.list (sorted.map (fun p => .tuple [p.1, p.2])))
  | .undef i => failUndef i
  | _ => typeErr "dictsort requires a mapping"

/-- Upstream filter `e`, `escape`. -/
def Filters.e (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  do let m ← escapeOf pol v; pure (.markup m)

/-- Upstream filter `filesizeformat`. -/
def Filters.filesizeformat (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let binary := ((a 0 "binary").map Value.truthy).getD false
  match v.num?, v with
  | some x, _ => pure (.str (fileSizeFormat x binary))
  | none, .str s =>
    match parseFloatStr s with
    | some x => pure (.str (fileSizeFormat x binary))
    | none => typeErr s!"could not convert string to float: {pyStrRepr s}"
  | _, _ => typeErr "filesizeformat requires a number"

/-- Upstream filter `first`. -/
def Filters.first (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let xs ← iter v
  pure (xs.head?.getD (.undef (.hint "No first item, sequence was empty.")))

/-- Upstream filter `float`. -/
def Filters.float (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let dflt := (a 0 "default").getD (.float 0 0)
  match v with
  | .int i => pure (.float i 0)
  | .bool b => pure (.float (if b then 1 else 0) 0)
  | .float .. => pure v
  | .str s | .markup ⟨s⟩ => pure ((parseFloatStr s).map mkFloat |>.getD dflt)
  | _ => pure dflt

/-- Upstream filter `forceescape`. -/
def Filters.forceescape (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  match v with
  | .markup m => pure (.markup (escape m.str))
  | _ => do let s ← strOf pol v; pure (.markup (escape s))

/-- Upstream filter `format`. -/
def Filters.format (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  do
  if !args.isEmpty && !kwargs.isEmpty then
    .error (.runtime "can't handle positional and keyword arguments at the same time")
  else
    let packed : Value := if !kwargs.isEmpty then .dict (kwargs.map (fun p => (.str p.1, p.2)))
      else .tuple args
    match v with
    | .markup m => do let r ← pctFormat pol true m.str packed; pure (.markup (Markup.markSafe r))
    | _ => do let s ← strOf pol v; let r ← pctFormat pol false s packed; pure (.str r)

/-- Upstream filter `groupby`. -/
def Filters.groupby (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let a := argAt args kwargs
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let attr ← match a 0 "attribute" with
    | some x => pure x
    | none => typeErr "groupby() missing 1 required positional argument: 'attribute'"
  let dflt := a 1 "default"
  let cs := ((a 2 "case_sensitive").map Value.truthy).getD false
  let xs ← iter v
  let keyed ← xs.mapM (fun x => do
    let k ← attrGet fc attr dflt x
    pure ((if cs then k else ignoreCase k), x))
  let sorted ← sortBy (fun p q => pyLe p.1 q.1) keyed
  let rec groups : Nat → List (Value × Value) → Except ValueError (List Value)
    | 0, _ => pure []
    | _ + 1, [] => pure []
    | fuel + 1, (k, x) :: rest =>
      let same := rest.takeWhile (fun p => Value.pyEq p.1 k)
      let others := rest.drop same.length
      let members := x :: same.map Prod.snd
      do
        let shown ← if cs then pure k else attrGet fc attr dflt x
        let more ← groups fuel others
        pure (.namedTuple "_GroupTuple" ["grouper", "list"] [shown, .list members] :: more)
  pure (.list (← groups (sorted.length + 1) sorted))

/-- Upstream filter `indent`. -/
def Filters.indent (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let pol := fc.pol
  do
  let s ← strOf pol v
  let w := (a 0 "width").getD (.int 4)
  let ind ← match w with
    | .str t => pure t
    | x => do let k ← intArg x "width"; pure (String.ofList (List.replicate k.toNat ' '))
  let first := ((a 1 "first").map Value.truthy).getD false
  let blank := ((a 2 "blank").map Value.truthy).getD false
  pure (keepKind v (indentText s ind first blank))

/-- Upstream filter `int`. -/
def Filters.int (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  do
  let dflt := (a 0 "default").getD (.int 0)
  let base ← intArg ((a 1 "base").getD (.int 10)) "base"
  match v with
  | .int _ => pure v
  | .bool b => pure (.int (if b then 1 else 0))
  | .float m s => pure (.int (m.tdiv (10 ^ s)))
  | .str s | .markup ⟨s⟩ =>
    match parseIntStr s base.toNat with
    | some i => pure (.int i)
    | none =>
      match parseFloatStr s with
      | some (m, sc) => pure (.int (m.tdiv (10 ^ sc)))
      | none => pure dflt
  | _ => pure dflt

/-- Upstream filter `items`. -/
def Filters.items (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  match v with
  | .undef _ => pure (.list [])
  | .dict kvs => pure (.list (kvs.map (fun p => .tuple [p.1, p.2])))
  | _ => typeErr "Can only get item pairs from a mapping."

/-- Upstream filter `join`. -/
def Filters.join (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let a := argAt args kwargs
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let xs ← iter v
  let xs ← match a 1 "attribute" with
    | some at_ => xs.mapM (attrGet fc at_ none)
    | none => pure xs
  joinFilter fc xs ((a 0 "d").getD (.str ""))

/-- Upstream filter `last`. -/
def Filters.last (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let xs ← iter v
  pure (xs.getLast?.getD (.undef (.hint "No last item, sequence was empty.")))

/-- Upstream filter `list`. -/
def Filters.list (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do let xs ← iter v; pure (.list xs)

/-- Upstream filter `lower`. -/
def Filters.lower (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  do let s ← strOf pol v; pure (keepKind v (strLower s))

/-- Upstream filter `upper`. -/
def Filters.upper (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  do let s ← strOf pol v; pure (keepKind v (strUpper s))

/-- Upstream filter `map`. -/
def Filters.map (apply : String → Value → List Value → List (String × Value) → Except ValueError Value) (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let pol := fc.pol
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let t0 ← truthyOf pol v
  let xs ← if t0 then iter v else pure []
  if args.isEmpty && (kwargs.lookup "attribute").isSome then
    let at_ := (kwargs.lookup "attribute").getD .none
    let dflt := kwargs.lookup "default"
    match (kwargs.filter (fun p => p.1 != "attribute" && p.1 != "default")).head? with
    | some (k, _) => .error (.runtime s!"Unexpected keyword argument {pyStrRepr k}")
    | none => do let ys ← xs.mapM (attrGet fc at_ dflt); pure (.list ys)
  else
    match args with
    | .str fname :: rest => do
      let ys ← xs.mapM (fun x => apply fname x rest kwargs)
      pure (.list ys)
    | _ => .error (.runtime "map requires a filter argument")

/-- Upstream filter `min`, `max`. -/
def Filters.min (isMin : Bool) (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let a := argAt args kwargs
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let cs := ((a 0 "case_sensitive").map Value.truthy).getD false
  let at_ := (a 1 "attribute").getD .none
  let xs ← iter v
  match xs with
  | [] => pure (.undef (.hint "No aggregated item, sequence was empty."))
  | x :: rest => do
    let key := fun (y : Value) => do
      let k ← attrGet fc at_ none y
      pure (if cs then k else ignoreCase k)
    let best ← rest.foldlM (fun (b : Value) (y : Value) => do
      let kb ← key b
      let ky ← key y
      let le ← pyLe ky kb
      if isMin then (if le && !(Value.pyEq ky kb) then pure y else pure b)
      else (if !le then pure y else pure b)) x
    pure best

/-- Upstream filter `pprint`. -/
def Filters.pprint (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  pure (.str v.repr)

/-- Upstream filter `select`, `reject`, `selectattr`, `rejectattr`. -/
def Filters.select (lookupAttr keep : Bool) (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let t0 ← truthyOf pol v
  if !t0 then pure (.list []) else
  let xs ← iter v
  let (attr, rest) := if lookupAttr then (args.head?, args.drop 1) else (none, args)
  if lookupAttr && attr.isNone then .error (.runtime "Missing parameter for attribute name") else
  let ys ← xs.filterM (fun x => do
    let y ← match attr with
      | some at_ => attrGet fc at_ none x
      | none => pure x
    let r ← match rest with
      | .str tname :: targs => applyTest fc tname y targs kwargs
      | _ => truthyOf pol y
    pure (r == keep))
  pure (.list ys)

/-- Upstream filter `replace`. -/
def Filters.replace (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let pol := fc.pol
  do
  let old ← match a 0 "old" with | some x => pure x | none => typeErr "replace() missing 'old'"
  let new ← match a 1 "new" with | some x => pure x | none => typeErr "replace() missing 'new'"
  let count ← match a 2 "count" with
    | none | some .none => pure (-1 : Int)
    | some c => intArg c "count"
  if !fc.autoescape then do
    let s ← strOf pol v
    let o ← strOf pol old
    let n ← strOf pol new
    pure (.str (String.ofList (replaceList s.toList o.toList n.toList count)))
  else
    let escS := (old.isMarkup || new.isMarkup) && !v.isMarkup
    if escS || v.isMarkup then do
      let sm ← escapeOf pol v
      let om ← escapeOf pol old
      let nm ← escapeOf pol new
      pure (.markup (Markup.markSafe (String.ofList
        (replaceList sm.str.toList om.str.toList nm.str.toList count))))
    else do
      let s ← strOf pol v
      let o ← strOf pol old
      let n ← strOf pol new
      pure (.str (String.ofList (replaceList s.toList o.toList n.toList count)))

/-- Upstream filter `reverse`. -/
def Filters.reverse (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let iter := fun (x : Value) => iterOf pol fc.heap x
  match v with
  | .str s => pure (.str (String.ofList s.toList.reverse))
  | .markup m => pure (.markup (Markup.markSafe (String.ofList m.str.toList.reverse)))
  | _ => do let xs ← iter v; pure (.list xs.reverse)

/-- Upstream filter `round`. -/
def Filters.round (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  do
  let p ← intArg ((a 0 "precision").getD (.int 0)) "precision"
  let meth ← match (a 1 "method").getD (.str "common") with
    | .str m => pure m
    | _ => .error (.runtime "method must be common, ceil or floor")
  match v.num? with
  | some x => roundFilter x p meth
  | none => match v with
    | .undef i => failUndef i
    | _ => typeErr s!"type {v.typeName} doesn't define __round__ method"

/-- Upstream filter `safe`. -/
def Filters.safe (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  match v with
  | .markup _ => pure v
  | _ => do let s ← strOf pol v; pure (.markup (Markup.markSafe s))

/-- Upstream filter `slice`. -/
def Filters.slice (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let a := argAt args kwargs
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let n ← intArg ((a 0 "slices").getD .none) "slices"
  if n ≤ 0 then typeErr "slice count must be positive" else
  let fill := a 1 "fill_with"
  let seq ← iter v
  let len := seq.length
  let k := n.toNat
  let per := len / k
  let extra := len % k
  -- the slices are consecutive, so each takes its items off the rest (a
  -- `drop` from the start per slice would be quadratic in the slice count)
  let rec build : Nat → Nat → Nat → List Value → List Value → List Value
    | 0, _, _, _, acc => acc.reverse
    | fuel + 1, i, off, rest, acc =>
      if i ≥ k then acc.reverse else
      let start := off + i * per
      let off' := if i < extra then off + 1 else off
      let stop := off' + (i + 1) * per
      let tmp := rest.take (stop - start)
      let tmp := match fill with
        | some f => if i ≥ extra && (match f with | .none => false | _ => true)
            then tmp ++ [f] else tmp
        | none => tmp
      build fuel (i + 1) off' (rest.drop (stop - start)) (.list tmp :: acc)
  pure (.list (build (k + 1) 0 0 seq []))

/-- Upstream filter `sort`. -/
def Filters.sort (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let a := argAt args kwargs
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let rev := ((a 0 "reverse").map Value.truthy).getD false
  let cs := ((a 1 "case_sensitive").map Value.truthy).getD false
  let attr := (a 2 "attribute").getD .none
  let xs ← iter v
  let attrs : List Value := match attr with
    | .str s => (s.splitOn ",").map Value.str
    | .none => [.none]
    | x => [x]
  let keyed ← xs.mapM (fun x => do
    let ks ← attrs.mapM (fun at_ => attrGet fc at_ none x)
    pure (Value.list (if cs then ks else ks.map ignoreCase), x))
  let sorted ← sortBy (fun p q => if rev then pyLe q.1 p.1 else pyLe p.1 q.1) keyed
  pure (.list (sorted.map Prod.snd))

/-- Upstream filter `string`. -/
def Filters.string (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  match v with
  | .markup _ => pure v
  | _ => do let s ← strOf pol v; pure (.str s)

/-- Upstream filter `striptags`. -/
def Filters.striptags (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  match v with
  | .markup m => pure (.str m.striptags)
  | _ => do let s ← strOf pol v; pure (.str (Markup.markSafe s).striptags)

/-- Upstream filter `sum`. -/
def Filters.sum (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let a := argAt args kwargs
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let attr := (a 0 "attribute").getD .none
  let start := (a 1 "start").getD (.int 0)
  let xs ← iter v
  xs.foldlM (fun acc x => do
    let y ← attrGet fc attr none x
    match acc, y with
    | .undef i, _ => failUndef i
    | _, .undef i => failUndef i
    | _, _ => arith .add acc y) start

/-- Upstream filter `title`. -/
def Filters.title (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  do let s ← strOf pol v; pure (.str (String.ofList (titleList s.toList)))

/-- Upstream filter `tojson`. -/
def Filters.tojson (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  do
  let ind ← match a 0 "indent" with
    | none | some .none => pure none
    | some x => do let k ← intArg x "indent"; pure (some k.toNat)
  let j ← jsonDump ind 0 v
  pure (.markup (Markup.markSafe (htmlsafeJson j)))

/-- Upstream filter `trim`. -/
def Filters.trim (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let pol := fc.pol
  do
  let s ← strOf pol v
  let chars ← match a 0 "chars" with
    | none | some .none => pure none
    | some c => do let t ← strOf pol c; pure (some t.toList)
  pure (keepKind v (String.ofList (stripChars chars s.toList)))

/-- Upstream filter `truncate`. -/
def Filters.truncate (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let pol := fc.pol
  do
  let s ← strOf pol v
  let length ← intArg ((a 0 "length").getD (.int 255)) "length"
  let kill := ((a 1 "killwords").map Value.truthy).getD false
  let endS ← strOf pol ((a 2 "end").getD (.str "..."))
  let leeway ← match a 3 "leeway" with
    | none | some .none => pure (fc.leeway : Int)
    | some x => intArg x "leeway"
  if length < endS.length then .error (.runtime s!"expected length >= {endS.length}, got {length}")
  else if leeway < 0 then .error (.runtime s!"expected leeway >= 0, got {leeway}")
  else
    let r := truncateList s.toList length.toNat kill endS.toList leeway.toNat
    if r.length == s.length && r == s.toList then pure v
    else match v with
      | .markup _ =>
        let base := r.take (r.length - endS.length)
        pure (.markup (Markup.markSafe (String.ofList base ++ (escape endS).str)))
      | _ => pure (.str (String.ofList r))

/-- Upstream filter `unique`. -/
def Filters.unique (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  let a := argAt args kwargs
  let iter := fun (x : Value) => iterOf pol fc.heap x
  do
  let cs := ((a 0 "case_sensitive").map Value.truthy).getD false
  let attr := (a 1 "attribute").getD .none
  let xs ← iter v
  let out ← uniqueSpec (fun x => do
    let k ← attrGet fc attr none x
    pure (if cs then k else ignoreCase k)) xs
  pure (.list out)

/-- Upstream filter `urlencode`. -/
def Filters.urlencode (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  match v with
  | .dict kvs => do
    let parts ← kvs.mapM (fun p => do
      let k ← strOf pol p.1
      let x ← strOf pol p.2
      pure (urlQuote k true ++ "=" ++ urlQuote x true))
    pure (.str ("&".intercalate parts))
  | .list xs | .tuple xs | .namedTuple _ _ xs => do
    let parts ← xs.mapM (fun p => do
      match p with
      | .tuple [k, x] | .list [k, x] | .namedTuple _ _ [k, x] => do
        let k ← strOf pol k
        let x ← strOf pol x
        pure (urlQuote k true ++ "=" ++ urlQuote x true)
      | _ => typeErr "urlencode requires (key, value) pairs")
    pure (.str ("&".intercalate parts))
  | _ => do let s ← strOf pol v; pure (.str (urlQuote s false))

/-- Upstream filter `wordcount`. -/
def Filters.wordcount (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let pol := fc.pol
  do let s ← strOf pol v; pure (.int (wordCount s.toList))

/-- Upstream filter `wordwrap`. -/
def Filters.wordwrap (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let pol := fc.pol
  do
  let s ← strOf pol v
  let w ← intArg ((a 0 "width").getD (.int 79)) "width"
  let bl := ((a 1 "break_long_words").map Value.truthy).getD true
  let ws ← match a 2 "wrapstring" with
    | none | some .none => pure "\n"
    | some x => strOf pol x
  pure (.str (wordWrap s w.toNat bl ws))

/-- Upstream filter `xmlattr`. -/
def Filters.xmlattr (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let autospace := ((a 0 "autospace").map Value.truthy).getD true
  match v with
  | .dict kvs => xmlAttr fc kvs autospace
  | _ => typeErr "xmlattr requires a mapping"

/-- Python `str.split()`: the runs of non-space characters. -/
def splitWords (s : String) : List String :=
  let rec go : List Char → List Char → List String → List String
    | [], cur, acc => (if cur.isEmpty then acc else String.ofList cur.reverse :: acc).reverse
    | c :: r, cur, acc =>
      if isSpace c then go r [] (if cur.isEmpty then acc else String.ofList cur.reverse :: acc)
      else go r (c :: cur) acc
  go s.toList [] []

/-- Sorted and without duplicates (Python `sorted(set(xs))`). -/
def sortedSet (xs : List String) : List String :=
  let rec dedup : List String → List String
    | a :: b :: r => if a == b then dedup (b :: r) else a :: dedup (b :: r)
    | r => r
  dedup (xs.mergeSort (fun a b => compare a b != .gt))

/-- Upstream filter `urlize` (`do_urlize`): the `rel` words, `nofollow` and
the `urlize.rel` policy are merged, sorted; `target` and `extra_schemes`
default to their policies; each extra scheme must match `_uri_scheme_re`. -/
def Filters.urlize (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value := do
  let a := argAt args kwargs
  let pol := fc.pol
  let trim ← match a 0 "trim_url_limit" with
    | none | some .none => pure none
    | some x => match x.asInt? with
      | some i => pure (some i)
      | none => typeErr s!"'>' not supported between instances of 'int' and '{x.typeName}'"
  let nofollow := ((a 1 "nofollow").map Value.truthy).getD false
  let relWords ← match a 3 "rel" with
    | some x =>
      if !x.truthy then pure [] else
      match x.text? with
      | some t => pure (splitWords t)
      | none => typeErr s!"'{x.typeName}' object has no attribute 'split'"
    | none => pure []
  let rel := " ".intercalate (sortedSet (relWords ++ (if nofollow then ["nofollow"] else []) ++
    splitWords (fc.urlizeRel.getD "")))
  let target : Value := match a 2 "target" with
    | none | some .none => (fc.urlizeTarget.map Value.str).getD .none
    | some x => x
  let targetAttr ← if target.truthy then do
      let m ← escapeOf pol target
      pure s!" target=\"{m.str}\""
    else pure ""
  let schemes ← match a 4 "extra_schemes" with
    | none | some .none => pure fc.urlizeExtraSchemes
    | some x => do
      let xs ← iterOf pol fc.heap x
      xs.mapM (fun s => match s.text? with
        | some t => pure t
        | none => typeErr s!"expected string or bytes-like object, got '{s.typeName}'")
  match schemes.find? (fun s => !uriSchemeOk s) with
  | some s => .error (.runtime s!"{pyStrRepr s} is not a valid URI scheme prefix.")
  | none =>
  let relAttr := if rel.isEmpty then "" else s!" rel=\"{(escape rel).str}\""
  let text ← escapeOf pol v
  let out := urlizeText { trim, relAttr, targetAttr, extraSchemes := schemes } text.str
  pure (if fc.autoescape then .markup (Markup.markSafe out) else .str out)

/-- Upstream filter `random`, drawing from the source state `fc.rng`. A
direct `|random` advances the render's source (`Render.applyFilterM`); one
`map('random')` reads it once. -/
def Filters.random (fc : FCtx) (v : Value) (args : List Value) (kwargs : List (String × Value)) :
    Except ValueError Value :=
  match args, kwargs with
  | [], [] => (randomChoice fc.pol fc.heap fc.rng v).map Prod.fst
  | _, (k, _) :: _ => typeErr s!"do_random() got an unexpected keyword argument '{k}'"
  | _, [] => typeErr s!"do_random() takes 2 positional arguments but {args.length + 2} were given"

/-- The builtin filters by name (upstream `FILTERS`); `apply` is the filter
lookup `map` calls by name. -/
def builtinFilterTable (apply : String → Value → List Value → List (String × Value) →
    Except ValueError Value) : List (String × FilterFn) := [
  ("abs", Filters.abs),
  ("attr", Filters.attr),
  ("batch", Filters.batch),
  ("capitalize", Filters.capitalize),
  ("center", Filters.center),
  ("count", Filters.length),
  ("length", Filters.length),
  ("d", Filters.default),
  ("default", Filters.default),
  ("dictsort", Filters.dictsort),
  ("e", Filters.e),
  ("escape", Filters.e),
  ("filesizeformat", Filters.filesizeformat),
  ("first", Filters.first),
  ("float", Filters.float),
  ("forceescape", Filters.forceescape),
  ("format", Filters.format),
  ("groupby", Filters.groupby),
  ("indent", Filters.indent),
  ("int", Filters.int),
  ("items", Filters.items),
  ("join", Filters.join),
  ("last", Filters.last),
  ("list", Filters.list),
  ("lower", Filters.lower),
  ("upper", Filters.upper),
  ("map", Filters.map apply),
  ("min", Filters.min true),
  ("max", Filters.min false),
  ("pprint", Filters.pprint),
  ("random", Filters.random),
  ("select", Filters.select false true),
  ("reject", Filters.select false false),
  ("selectattr", Filters.select true true),
  ("rejectattr", Filters.select true false),
  ("replace", Filters.replace),
  ("reverse", Filters.reverse),
  ("round", Filters.round),
  ("safe", Filters.safe),
  ("slice", Filters.slice),
  ("sort", Filters.sort),
  ("string", Filters.string),
  ("striptags", Filters.striptags),
  ("sum", Filters.sum),
  ("title", Filters.title),
  ("tojson", Filters.tojson),
  ("trim", Filters.trim),
  ("truncate", Filters.truncate),
  ("unique", Filters.unique),
  ("urlencode", Filters.urlencode),
  ("urlize", Filters.urlize),
  ("wordcount", Filters.wordcount),
  ("wordwrap", Filters.wordwrap),
  ("xmlattr", Filters.xmlattr)]

/-- Apply a filter (upstream `Environment.call_filter`). `depth` bounds the
nesting of `map` calling filters by name. Each level of that nesting consumes
one argument, so the `args.length + 2` that `applyFilter` gives is never
exhausted. -/
def applyFilterD (fc : FCtx) : Nat → String → Value → List Value → List (String × Value) →
    Except ValueError Value
  | 0, _, _, _, _ => .error (.runtime "filter nesting exceeds its arguments")
  | d + 1, name, v, args, kwargs =>
    match (builtinFilterTable (applyFilterD fc d)).lookup name with
    | some f => f fc v args kwargs
    | none =>
      match fc.filters.lookup name with
      | some f => liftNative (f fc.vars (v :: args) kwargs)
      | none => .error (.runtime s!"No filter named '{name}'.")

/-- Apply a filter by name. -/
def applyFilter (fc : FCtx) (name : String) (v : Value) (args : List Value)
    (kwargs : List (String × Value)) : Except ValueError Value :=
  applyFilterD fc (args.length + 2) name v args kwargs

end LeanJinja2
