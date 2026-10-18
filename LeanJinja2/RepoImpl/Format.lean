import LeanJinja2.RepoImpl.Runtime

/-!
# `%`-formatting and JSON

Python's `str % args` (the `%` operator on strings and the `format` filter)
and `json.dumps(..., sort_keys=True)` with upstream's HTML-safe replacements
(the `tojson` filter).
-/

namespace LeanJinja2

set_option linter.unusedVariables false

open LeanMarkupsafe

/-- Round a decimal half-to-even to `p` fractional digits: the scaled integer. -/
def roundHalfEven (m : Int) (s : Nat) (p : Nat) : Int :=
  if s ≤ p then m * 10 ^ (p - s)
  else
    let d : Int := 10 ^ (s - p)
    let q := Int.fdiv m d
    let r := m - q * d
    if 2 * r > d then q + 1
    else if 2 * r < d then q
    else if q % 2 = 0 then q else q + 1

/-- Fixed-point text of a decimal with exactly `p` fractional digits. -/
def fixedText (m : Int) (s : Nat) (p : Nat) : String :=
  let q := roundHalfEven m s p
  let sign := if q < 0 then "-" else ""
  let a := q.natAbs
  if p = 0 then sign ++ String.ofList (natDigits a)
  else
    let ip := a / 10 ^ p
    let fp := a % 10 ^ p
    let fd := natDigits fp
    sign ++ String.ofList (natDigits ip) ++ "." ++
      String.ofList (List.replicate (p - fd.length) '0' ++ fd)

/-- One `%` conversion spec. -/
structure PctSpec where
  key : Option String
  flags : List Char
  width : Option Nat
  prec : Option Nat
  conv : Char

/-- Parse the conversion spec after `%`: the spec and the rest. -/
def parsePct (l : List Char) : Option (PctSpec × List Char) :=
  let (key, l) : Option String × List Char :=
    match l with
    | '(' :: r =>
      let k := r.takeWhile (· != ')')
      (some (String.ofList k), (r.drop (k.length + 1)))
    | _ => (none, l)
  let flags := l.takeWhile (fun c => c == '-' || c == '+' || c == ' ' || c == '#' || c == '0')
  let l := l.drop flags.length
  let wd := l.takeWhile Char.isDigit
  let l := l.drop wd.length
  let (prec, l) := match l with
    | '.' :: r => let pd := r.takeWhile Char.isDigit; (some (digitsValue 10 pd), r.drop pd.length)
    | _ => (none, l)
  match l with
  | c :: r => some (⟨key, flags, if wd.isEmpty then none else some (digitsValue 10 wd), prec, c⟩, r)
  | [] => none

/-- Pad to the width of a spec. -/
def pctPad (sp : PctSpec) (body : String) (numeric : Bool) : String :=
  match sp.width with
  | none => body
  | some w =>
    if body.length ≥ w then body
    else
      let pad := w - body.length
      if sp.flags.contains '-' then body ++ String.ofList (List.replicate pad ' ')
      else if numeric && sp.flags.contains '0' then
        match body.toList with
        | '-' :: r => "-" ++ String.ofList (List.replicate pad '0') ++ String.ofList r
        | r => String.ofList (List.replicate pad '0') ++ String.ofList r
      else String.ofList (List.replicate pad ' ') ++ body

/-- Render one argument under a spec. -/
def pctOne (pol : UndefinedPolicy) (sp : PctSpec) (v : Value) : Except ValueError String := do
  let sgn := fun (neg : Bool) => if neg then "-" else if sp.flags.contains '+' then "+"
    else if sp.flags.contains ' ' then " " else ""
  match sp.conv with
  | 's' => let s ← strOf pol v; pure (pctPad sp (match sp.prec with | some p => s.take p |>.toString | none => s) false)
  | 'r' | 'a' => pure (pctPad sp v.repr false)
  | 'd' | 'i' | 'u' =>
    match v.num? with
    | some (m, s) =>
      let q := m.tdiv (10 ^ s)
      pure (pctPad sp (sgn (q < 0) ++ String.ofList (natDigits q.natAbs)) true)
    | none => .error (.typeError s!"%{sp.conv} format: a real number is required, not {v.typeName}")
  | 'f' | 'F' =>
    match v.num? with
    | some (m, s) =>
      let t := fixedText m.natAbs s (sp.prec.getD 6)
      pure (pctPad sp (sgn (m < 0) ++ t) true)
    | none => .error (.typeError s!"must be real number, not {v.typeName}")
  | 'x' | 'X' | 'o' =>
    match v with
    | .int i =>
      let base := if sp.conv == 'o' then 8 else 16
      let ds := Nat.toDigits base i.natAbs
      let ds := if sp.conv == 'X' then ds.map Char.toUpper else ds
      pure (pctPad sp (sgn (i < 0) ++ String.ofList ds) true)
    | _ => .error (.typeError s!"%{sp.conv} format: an integer is required, not {v.typeName}")
  | 'c' =>
    match v with
    | .int i => pure (pctPad sp (String.singleton (Char.ofNat i.toNat)) false)
    | .str s =>
      if s.length == 1 then pure (pctPad sp s false) else .error (.typeError "%c requires int or char")
    | _ => .error (.typeError "%c requires int or char")
  | c => .error (.typeError s!"unsupported format character '{c}'")

/-- Python `template % args`: `args` is a tuple of positional values, a
mapping for `%(key)s`, or a single value. `esc` escapes every interpolated
non-markup value (the `Markup.__mod__` case). -/
def pctFormat (pol : UndefinedPolicy) (esc : Bool) (tmpl : String) (args : Value) :
    Except ValueError String := do
  let positional : List Value := match args with
    | .tuple xs => xs
    | v => [v]
  let mapping : Option (List (Value × Value)) := match args with
    | .dict kvs => some kvs
    | _ => none
  let conv := fun (sp : PctSpec) (v : Value) =>
    if esc then match v with
      | .markup m => pctOne pol sp (.str m.str)
      | _ => do let s ← pctOne pol sp v; pure (escape s).str
    else pctOne pol sp v
  let rec go : Nat → List Char → List Value → Bool → Except ValueError (List Char × List Value × Bool)
    | 0, _, rest, used => .ok ([], rest, used)
    | _ + 1, [], rest, used => .ok ([], rest, used)
    | fuel + 1, '%' :: '%' :: r, rest, used => do
      let (o, rest, used) ← go fuel r rest used
      pure ('%' :: o, rest, used)
    | fuel + 1, '%' :: r, rest, used =>
      match parsePct r with
      | none => .error (.typeError "incomplete format")
      | some (sp, r) => do
        let (v, rest) ← match sp.key with
          | some k =>
            match mapping with
            | some kvs => match Value.lookupIn kvs (.str k) with
              | some v => pure (v, rest)
              | none => .error (.typeError s!"KeyError: '{k}'")
            | none => .error (.typeError "format requires a mapping")
          | none =>
            match mapping with
            | some _ => pure (args, rest)
            | none =>
              match rest with
              | v :: vs => pure (v, vs)
              | [] => .error (.typeError "not enough arguments for format string")
        let s ← conv sp v
        let (o, rest, _) ← go fuel r rest true
        pure (s.toList ++ o, rest, true)
    | fuel + 1, c :: r, rest, used => do
      let (o, rest, used') ← go fuel r rest used
      pure (c :: o, rest, used')
  let (out, rest, _) ← go (tmpl.length + 1) tmpl.toList positional false
  if mapping.isNone && !rest.isEmpty then
    .error (.typeError "not all arguments converted during string formatting")
  else .ok (String.ofList out)

/-! ## JSON -/

/-- `json.dumps` string escaping with `ensure_ascii=True`. -/
def jsonStr (s : String) : String :=
  let hex4 := fun (n : Nat) =>
    let h := Nat.toDigits 16 n
    "\\u" ++ String.ofList (List.replicate (4 - h.length) '0' ++ h)
  let esc := fun (c : Char) =>
    match c with
    | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
    | '\x08' => "\\b" | '\x0c' => "\\f"
    | c =>
      if c.val < 0x20 then hex4 c.val.toNat
      else if c.val < 0x7f then String.singleton c
      else if c.val < 0x10000 then hex4 c.val.toNat
      else
        let v := c.val.toNat - 0x10000
        hex4 (0xd800 + v / 0x400) ++ hex4 (0xdc00 + v % 0x400)
  "\"" ++ String.join (s.toList.map esc) ++ "\""

/-- A JSON object key (`json.dumps` converts scalar keys to strings). -/
def jsonKey : Value → Except ValueError String
  | .str s => .ok s
  | .markup m => .ok m.str
  | .int i => .ok (String.ofList (intDigits i))
  | .float m s => .ok (decRepr m s)
  | .bool b => .ok (if b then "true" else "false")
  | .none => .ok "null"
  | v => .error (.typeError s!"keys must be str, int, float, bool or None, not {v.typeName}")

/-- Insertion of a key-sorted entry. -/
def insertSorted (p : String × String) : List (String × String) → List (String × String)
  | [] => [p]
  | q :: qs => if p.1 < q.1 then p :: q :: qs else q :: insertSorted p qs

/-- `json.dumps(v, sort_keys=True, indent=indent)`. -/
def jsonDump (indent : Option Nat) (level : Nat) : Value → Except ValueError String
  | .none => .ok "null"
  | .bool b => .ok (if b then "true" else "false")
  | .int i => .ok (String.ofList (intDigits i))
  | .float m s => .ok (decRepr m s)
  | .str s => .ok (jsonStr s)
  | .markup m => .ok (jsonStr m.str)
  | .list xs | .tuple xs => do
    let items ← jsonDumpList indent (level + 1) xs
    pure (jsonWrap indent level "[" "]" items)
  | .dict kvs => do
    let items ← jsonDumpPairs indent (level + 1) kvs
    let sorted := items.foldl (fun acc p => insertSorted p acc) []
    pure (jsonWrap indent level "{" "}" (sorted.map (fun p => jsonStr p.1 ++ ": " ++ p.2)))
  | v => .error (.typeError s!"Object of type {v.typeName} is not JSON serializable")
where
  jsonWrap (indent : Option Nat) (level : Nat) (o c : String) (items : List String) : String :=
    if items.isEmpty then o ++ c else
    match indent with
    | none => o ++ ", ".intercalate items ++ c
    | some k =>
      let pad := fun (n : Nat) => String.ofList (List.replicate (k * n) ' ')
      o ++ "\n" ++ (",\n".intercalate (items.map (pad (level + 1) ++ ·))) ++ "\n" ++ pad level ++ c
  jsonDumpList (indent : Option Nat) (level : Nat) : List Value → Except ValueError (List String)
    | [] => .ok []
    | x :: xs => do
      let a ← jsonDump indent level x
      let b ← jsonDumpList indent level xs
      pure (a :: b)
  jsonDumpPairs (indent : Option Nat) (level : Nat) :
      List (Value × Value) → Except ValueError (List (String × String))
    | [] => .ok []
    | (k, v) :: rest => do
      let ks ← jsonKey k
      let vs ← jsonDump indent level v
      let more ← jsonDumpPairs indent level rest
      pure ((ks, vs) :: more)

/-- Upstream `htmlsafe_json_dumps`: `<`, `>`, `&`, `'` become `\u` escapes,
and the result is marked safe. -/
def htmlsafeChar : Char → String
  | '<' => "\\u003c" | '>' => "\\u003e" | '&' => "\\u0026" | '\'' => "\\u0027"
  | c => String.singleton c

def htmlsafeJson (s : String) : String := String.join (s.toList.map htmlsafeChar)

end LeanJinja2
