import LeanJinja2.DataTypes.Value
import LeanJinja2.RepoImpl.Chars

/-!
# Operations on values

Python's semantics for the operations templates perform: `str()` and
`repr()`, truthiness, `==`, ordering, arithmetic, `in`, iteration, length.
Numbers are exact (`Int`, and decimals `m / 10^s` for floats); division keeps
16 significant digits (see the deviation rows).
-/

namespace LeanJinja2

open LeanMarkupsafe

/-! ## Decimals -/

/-- Strip trailing zeros of a decimal `m / 10^s`. -/
def decNorm : Int → Nat → Int × Nat
  | m, 0 => (m, 0)
  | m, s + 1 => if m % 10 = 0 then decNorm (m / 10) s else (m, s + 1)

/-- Bring two decimals to a common scale. -/
def decAlign (a : Int × Nat) (b : Int × Nat) : Int × Int × Nat :=
  let s := max a.2 b.2
  (a.1 * 10 ^ (s - a.2), b.1 * 10 ^ (s - b.2), s)

def decAdd (a b : Int × Nat) : Int × Nat := let (x, y, s) := decAlign a b; decNorm (x + y) s
def decSub (a b : Int × Nat) : Int × Nat := let (x, y, s) := decAlign a b; decNorm (x - y) s
def decMul (a b : Int × Nat) : Int × Nat := decNorm (a.1 * b.1) (a.2 + b.2)

/-- Compare two decimals. -/
def decCmp (a b : Int × Nat) : Ordering := let (x, y, _) := decAlign a b; compare x y

/-- Number of decimal digits of a natural number (at least 1). -/
def numDigits (n : Nat) : Nat := (natDigits n).length

/-- `a / b` as a decimal truncated to 16 significant digits (`b ≠ 0`). -/
def decDiv (a b : Int × Nat) : Int × Nat :=
  -- a.1 / 10^a.2 ÷ b.1 / 10^b.2 = (a.1 * 10^b.2) / (b.1 * 10^a.2)
  let num := a.1 * 10 ^ b.2
  let den := b.1 * 10 ^ a.2
  if den = 0 then (0, 0) else
  let neg := (num < 0) != (den < 0)
  let n := num.natAbs
  let d := den.natAbs
  -- choose a scale k so that n * 10^k / d has at least 16 digits
  let ip := n / d
  let k := if ip = 0 then
      -- leading zeros after the point
      let rec lead (r : Nat) (fuel : Nat) (z : Nat) : Nat :=
        match fuel with
        | 0 => z
        | f + 1 => if r * 10 ≥ d then z else lead (r * 10) f (z + 1)
      15 + 1 + lead n 400 0
    else if numDigits ip ≥ 16 then 0 else 16 - numDigits ip
  let q := (n * 10 ^ k) / d
  decNorm (if neg then -(q : Int) else (q : Int)) k

/-- `floor(a / b)` for decimals (`b ≠ 0`). -/
def decFloorDiv (a b : Int × Nat) : Int :=
  let num := a.1 * 10 ^ b.2
  let den := b.1 * 10 ^ a.2
  if den = 0 then 0 else Int.fdiv num den

/-- Python's `repr(float)` for an exact decimal: shortest digits, fixed
notation for exponents in `[-4, 16)`, scientific otherwise. -/
def decRepr (m : Int) (s : Nat) : String :=
  let (m, s) := decNorm m s
  let sign := if m < 0 then "-" else ""
  let a := m.natAbs
  if a = 0 then sign ++ "0.0" else
  let ds := natDigits a
  let e : Int := (ds.length : Int) - 1 - s
  if e ≥ 16 || e < -4 then
    -- strip trailing zeros of the digit string
    let digits := (ds.reverse.dropWhile (· == '0')).reverse
    let mant := match digits with
      | [d] => String.ofList [d]
      | d :: rest => String.ofList (d :: '.' :: rest)
      | [] => "0"
    let ex := if e < 0 then "-" else "+"
    let ed := natDigits e.natAbs
    let ed := if ed.length < 2 then '0' :: ed else ed
    sign ++ mant ++ "e" ++ ex ++ String.ofList ed
  else if s = 0 then sign ++ String.ofList ds ++ ".0"
  else
    let ip := a / 10 ^ s
    let fp := a % 10 ^ s
    let fd := natDigits fp
    let fd := List.replicate (s - fd.length) '0' ++ fd
    sign ++ String.ofList (natDigits ip) ++ "." ++ String.ofList fd

/-! ## Strings -/

/-- Python `repr(str)`. -/
def pyStrRepr (s : String) : String :=
  let l := s.toList
  let q := if l.contains '\'' && !l.contains '"' then '"' else '\''
  let hex2 := fun (n : Nat) =>
    let h := Nat.toDigits 16 n
    String.ofList (if h.length < 2 then '0' :: h else h)
  let esc := fun (c : Char) =>
    if c == q || c == '\\' then String.ofList ['\\', c]
    else if c == '\n' then "\\n" else if c == '\r' then "\\r" else if c == '\t' then "\\t"
    else if c.val < 32 || c.val == 127 then "\\x" ++ hex2 c.val.toNat
    else String.singleton c
  String.singleton q ++ String.join (l.map esc) ++ String.singleton q

/-- ASCII and Latin-1 case mapping (Python's is full Unicode). -/
def charUpper (c : Char) : Char :=
  if c.val ≥ 0xe0 && c.val ≤ 0xfe && c.val != 0xf7 then Char.ofNat (c.val.toNat - 32)
  else c.toUpper

def charLower (c : Char) : Char :=
  if c.val ≥ 0xc0 && c.val ≤ 0xde && c.val != 0xd7 then Char.ofNat (c.val.toNat + 32)
  else c.toLower

def strUpper (s : String) : String := String.ofList (s.toList.map charUpper)
def strLower (s : String) : String := String.ofList (s.toList.map charLower)

/-- Python `str.capitalize`. -/
def strCapitalize (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: cs => String.ofList (charUpper c :: cs.map charLower)

/-- Whether `p` occurs in `l` at position 0. -/
def listStartsWith (l p : List Char) : Bool := p.isPrefixOf l

/-- Python `str.replace(old, new, count)` (`count < 0`: all). -/
def replaceList (l old new : List Char) (count : Int) : List Char :=
  if old.isEmpty then
    -- Python inserts `new` between every character (and at both ends)
    let rec ins : List Char → Int → List Char
      | [], c => if c == 0 then [] else new
      | x :: xs, c => if c == 0 then x :: xs else new ++ x :: ins xs (c - 1)
    ins l count
  else
    let rec go : Nat → List Char → Int → List Char
      | 0, l, _ => l
      | fuel + 1, l, c =>
        if c == 0 then l
        else if listStartsWith l old then new ++ go fuel (l.drop old.length) (c - 1)
        else match l with
          | [] => []
          | x :: xs => x :: go fuel xs c
    go (l.length + 1) l count

/-- Find the first occurrence of `p` in `l`. -/
def findSub (l p : List Char) : Option Nat :=
  let rec go : List Char → Nat → Option Nat
    | [], i => if p.isEmpty then some i else none
    | x :: xs, i => if listStartsWith (x :: xs) p then some i else go xs (i + 1)
  go l 0

/-- Whether `p` is a substring of `l`. -/
def containsSub (l p : List Char) : Bool := (findSub l p).isSome

/-- Split on a non-empty separator (Python `str.split(sep)`). -/
def splitOn (l sep : List Char) : List (List Char) :=
  let rec go : Nat → List Char → List Char → List (List Char)
    | 0, l, acc => [acc.reverse ++ l]
    | fuel + 1, l, acc =>
      if !sep.isEmpty && listStartsWith l sep then acc.reverse :: go fuel (l.drop sep.length) []
      else match l with
        | [] => [acc.reverse]
        | x :: xs => go fuel xs (x :: acc)
  go (l.length + 1) l []

/-- Python `str.split()` (on runs of whitespace, dropping empties). -/
def splitWs (l : List Char) : List (List Char) :=
  let rec go : Nat → List Char → List (List Char)
    | 0, _ => []
    | fuel + 1, l =>
      let l := l.dropWhile isSpace
      if l.isEmpty then [] else
      let w := l.takeWhile (fun c => !isSpace c)
      w :: go fuel (l.drop w.length)
  go (l.length + 1) l

/-- Python `str.splitlines()`. -/
def splitLines (l : List Char) : List (List Char) :=
  let rec go : Nat → List Char → List Char → List (List Char)
    | 0, _, acc => if acc.isEmpty then [] else [acc.reverse]
    | _ + 1, [], acc => if acc.isEmpty then [] else [acc.reverse]
    | fuel + 1, '\r' :: '\n' :: r, acc => acc.reverse :: go fuel r []
    | fuel + 1, c :: r, acc =>
      if c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c' || c == '\x1c' || c == '\x1d' ||
        c == '\x1e' || c == '\x85' || c == ' ' || c == ' '
      then acc.reverse :: go fuel r []
      else go fuel r (c :: acc)
  go (l.length + 1) l []

/-! ## Type names, as upstream's messages print them -/

/-- Python `type(x).__name__`. -/
def Value.typeName : Value → String
  | .none => "NoneType" | .undef _ => "Undefined" | .bool _ => "bool" | .int _ => "int"
  | .float .. => "float" | .str _ => "str" | .markup _ => "Markup" | .list _ => "list"
  | .tuple _ => "tuple" | .dict _ => "dict" | .macro .. => "Macro" | .native _ => "function"
  | .method .. => "builtin_function_or_method" | .loop .. => "LoopContext"
  | .superRef .. => "BlockReference" | .ns _ => "Namespace" | .module .. => "TemplateModule"

/-- Upstream `object_type_repr`. -/
def Value.objectTypeRepr : Value → String
  | .none => "None"
  | .markup _ => "markupsafe.Markup object"
  | .macro .. => "jinja2.runtime.Macro object"
  | .loop .. => "jinja2.runtime.LoopContext object"
  | .ns _ => "jinja2.utils.Namespace object"
  | .module .. => "jinja2.environment.TemplateModule object"
  | v => s!"{v.typeName} object"

/-- The message of an undefined value (upstream `_undefined_message`). -/
def UndefInfo.message : UndefInfo → String
  | .name n => s!"'{n}' is undefined"
  | .attr o n => s!"'{o}' has no attribute '{n}'"
  | .hint h | .plain h => h

/-! ## `str()` and `repr()` -/

mutual
/-- Python `repr()` of a value. Undefined values print as `Undefined`. -/
def Value.repr : Value → String
  | .none => "None"
  | .undef _ => "Undefined"
  | .bool b => if b then "True" else "False"
  | .int i => String.ofList (intDigits i)
  | .float m s => decRepr m s
  | .str s => pyStrRepr s
  | .markup m => "Markup(" ++ pyStrRepr m.str ++ ")"
  | .list xs => "[" ++ Value.reprList xs ++ "]"
  | .tuple [x] => "(" ++ x.repr ++ ",)"
  | .tuple xs => "(" ++ Value.reprList xs ++ ")"
  | .dict kvs => "{" ++ Value.reprPairs kvs ++ "}"
  | .macro n .. => s!"<Macro '{n}'>"
  | .native n => s!"<function {n}>"
  | .method _ n => s!"<built-in method {n}>"
  | .loop i len .. => s!"<LoopContext {i + 1}/{len}>"
  | .superRef n _ => s!"<BlockReference '{n}'>"
  | .ns a => s!"<Namespace {a}>"
  | .module n .. => s!"<TemplateModule {pyStrRepr n}>"

def Value.reprList : List Value → String
  | [] => ""
  | [x] => x.repr
  | x :: xs => x.repr ++ ", " ++ Value.reprList xs

def Value.reprPairs : List (Value × Value) → String
  | [] => ""
  | [(k, v)] => k.repr ++ ": " ++ v.repr
  | (k, v) :: kvs => k.repr ++ ": " ++ v.repr ++ ", " ++ Value.reprPairs kvs
end

/-! `repr` in one pass. `Value.reprList` appends each item's text to the text
of the rest, which copies the rest once per item (quadratic on a long list).
The `Acc` versions append to an accumulator instead, and `repr_eq_acc` (a
`@[csimp]` lemma) makes compiled code use them. -/

mutual
def Value.reprAcc (acc : String) : Value → String
  | .list xs => Value.reprListAcc (acc ++ "[") xs ++ "]"
  | .tuple [x] => Value.reprAcc (acc ++ "(") x ++ ",)"
  | .tuple xs => Value.reprListAcc (acc ++ "(") xs ++ ")"
  | .dict kvs => Value.reprPairsAcc (acc ++ "{") kvs ++ "}"
  | v => acc ++ v.repr

def Value.reprListAcc (acc : String) : List Value → String
  | [] => acc
  | [x] => Value.reprAcc acc x
  | x :: xs => Value.reprListAcc (Value.reprAcc acc x ++ ", ") xs

def Value.reprPairsAcc (acc : String) : List (Value × Value) → String
  | [] => acc
  | [(k, v)] => Value.reprAcc (Value.reprAcc acc k ++ ": ") v
  | (k, v) :: kvs => Value.reprPairsAcc (Value.reprAcc (Value.reprAcc acc k ++ ": ") v ++ ", ") kvs
end

mutual
theorem Value.reprAcc_eq : ∀ (acc : String) (v : Value), Value.reprAcc acc v = acc ++ v.repr
  | acc, .list xs => by
    rw [Value.reprAcc, Value.reprListAcc_eq]; simp [Value.repr, String.append_assoc]
  | acc, .tuple [] => by simp [Value.reprAcc, Value.reprListAcc, Value.repr, Value.reprList, String.append_assoc]
  | acc, .tuple [x] => by
    rw [Value.reprAcc, Value.reprAcc_eq]; simp [Value.repr, String.append_assoc]
  | acc, .tuple (x :: y :: ys) => by
    rw [Value.reprAcc, Value.reprListAcc_eq]
    · simp [Value.repr, String.append_assoc]
    · intro z h; simp at h
  | acc, .dict kvs => by
    rw [Value.reprAcc, Value.reprPairsAcc_eq]; simp [Value.repr, String.append_assoc]
  | acc, .none => by simp [Value.reprAcc]
  | acc, .undef _ => by simp [Value.reprAcc]
  | acc, .bool _ => by simp [Value.reprAcc]
  | acc, .int _ => by simp [Value.reprAcc]
  | acc, .float .. => by simp [Value.reprAcc]
  | acc, .str _ => by simp [Value.reprAcc]
  | acc, .markup _ => by simp [Value.reprAcc]
  | acc, .macro .. => by simp [Value.reprAcc]
  | acc, .native _ => by simp [Value.reprAcc]
  | acc, .method .. => by simp [Value.reprAcc]
  | acc, .loop .. => by simp [Value.reprAcc]
  | acc, .superRef .. => by simp [Value.reprAcc]
  | acc, .ns _ => by simp [Value.reprAcc]
  | acc, .module .. => by simp [Value.reprAcc]

theorem Value.reprListAcc_eq : ∀ (acc : String) (xs : List Value),
    Value.reprListAcc acc xs = acc ++ Value.reprList xs
  | acc, [] => by simp [Value.reprListAcc, Value.reprList]
  | acc, [x] => by rw [Value.reprListAcc, Value.reprAcc_eq]; simp [Value.reprList]
  | acc, x :: y :: ys => by
    rw [Value.reprListAcc, Value.reprListAcc_eq, Value.reprAcc_eq]
    · simp [Value.reprList, String.append_assoc]
    · simp_all

theorem Value.reprPairsAcc_eq : ∀ (acc : String) (kvs : List (Value × Value)),
    Value.reprPairsAcc acc kvs = acc ++ Value.reprPairs kvs
  | acc, [] => by simp [Value.reprPairsAcc, Value.reprPairs]
  | acc, [(k, v)] => by
    rw [Value.reprPairsAcc, Value.reprAcc_eq, Value.reprAcc_eq]; simp [Value.reprPairs, String.append_assoc]
  | acc, (k, v) :: q :: kvs => by
    rw [Value.reprPairsAcc, Value.reprPairsAcc_eq, Value.reprAcc_eq, Value.reprAcc_eq]
    · simp [Value.reprPairs, String.append_assoc]
    · simp_all
end

/-- `repr` through the accumulator. -/
def Value.reprFast (v : Value) : String := Value.reprAcc "" v

@[csimp] theorem repr_eq_acc : @Value.repr = @Value.reprFast := by
  funext v; rw [Value.reprFast, Value.reprAcc_eq]; simp

/-- Python `str()` of a defined value (undefined values are handled by the
policy, see `Render`). -/
def Value.toStr : Value → String
  | .str s => s
  | .markup m => m.str
  | .module _ _ out => out
  | .undef _ => ""
  | v => v.repr

/-- Python truthiness of a defined value. -/
def Value.truthy : Value → Bool
  | .none => false
  | .undef _ => false
  | .bool b => b
  | .int i => i != 0
  | .float m _ => m != 0
  | .str s => !s.isEmpty
  | .markup m => !m.str.isEmpty
  | .list xs => !xs.isEmpty
  | .tuple xs => !xs.isEmpty
  | .dict kvs => !kvs.isEmpty
  | _ => true

/-- A number as a decimal (bools are ints, as in Python). -/
def Value.num? : Value → Option (Int × Nat)
  | .bool b => some (if b then 1 else 0, 0)
  | .int i => some (i, 0)
  | .float m s => some (m, s)
  | _ => Option.none

def Value.isFloat : Value → Bool
  | .float .. => true
  | _ => false

/-- The text of a string or markup value. -/
def Value.text? : Value → Option String
  | .str s => some s
  | .markup m => some m.str
  | _ => Option.none

def Value.isUndef : Value → Bool
  | .undef _ => true
  | _ => false

def Value.isMarkup : Value → Bool
  | .markup _ => true
  | _ => false

/-- Whether a value has `__html__` (markup, and an imported template module),
so `escape` takes its own text. -/
def Value.hasHtml : Value → Bool
  | .markup _ | .module .. => true
  | _ => false

/-- A float result, normalised. -/
def mkFloat (d : Int × Nat) : Value := let (m, s) := decNorm d.1 d.2; .float m s

mutual
/-- Python `==` on defined values. -/
def Value.pyEq : Value → Value → Bool
  | .none, .none => true
  | .list xs, .list ys => Value.pyEqList xs ys
  | .tuple xs, .tuple ys => Value.pyEqList xs ys
  | .dict a, .dict b => a.length == b.length && Value.pyDictSub a b
  | .undef _, .undef _ => true
  | .ns a, .ns b => a == b
  | .native a, .native b => a == b
  | a, b =>
    match a.num?, b.num? with
    | some x, some y => decCmp x y == .eq
    | _, _ =>
      match a.text?, b.text? with
      | some x, some y => x == y
      | _, _ => false
termination_by a b => sizeOf a + sizeOf b

def Value.pyEqList : List Value → List Value → Bool
  | [], [] => true
  | x :: xs, y :: ys => Value.pyEq x y && Value.pyEqList xs ys
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b

/-- Every entry of `a` is in `b` with an equal value. -/
def Value.pyDictSub : List (Value × Value) → List (Value × Value) → Bool
  | [], _ => true
  | (k, v) :: rest, b => Value.pyDictFind b k v && Value.pyDictSub rest b
termination_by a b => sizeOf a + sizeOf b

/-- The first entry of `b` with key `k` has value `v`. -/
def Value.pyDictFind : List (Value × Value) → Value → Value → Bool
  | [], _, _ => false
  | (k', v') :: rest, k, v => if Value.pyEq k' k then Value.pyEq v' v else Value.pyDictFind rest k v
termination_by b k v => sizeOf b + sizeOf k + sizeOf v
end

/-- Look a key up in a mapping. -/
def Value.lookupIn : List (Value × Value) → Value → Option Value
  | [], _ => Option.none
  | (k, v) :: rest, key => if Value.pyEq k key then some v else Value.lookupIn rest key

mutual
/-- Python ordering, or a `TypeError` message. -/
def Value.pyCmp : Value → Value → Except String Ordering
  | .list xs, .list ys => Value.pyCmpList xs ys
  | .tuple xs, .tuple ys => Value.pyCmpList xs ys
  | a, b =>
    match a.num?, b.num? with
    | some x, some y => .ok (decCmp x y)
    | _, _ =>
      match a.text?, b.text? with
      | some x, some y => .ok (compare x y)
      | _, _ => .error s!"'<' not supported between instances of '{a.typeName}' and '{b.typeName}'"

def Value.pyCmpList : List Value → List Value → Except String Ordering
  | [], [] => .ok .eq
  | [], _ :: _ => .ok .lt
  | _ :: _, [] => .ok .gt
  | x :: xs, y :: ys => if Value.pyEq x y then Value.pyCmpList xs ys else Value.pyCmp x y
end

end LeanJinja2
