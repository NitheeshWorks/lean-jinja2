import LeanJinja2.RepoImpl.Values
import LeanJinja2.RepoImpl.AstWalk

/-!
# Runtime primitives

What upstream's runtime does with a value, under an undefined policy:
printing (`str`), truth, iteration, length, autoescaping, attribute and item
access (`Environment.getattr`/`getitem`), slicing, arithmetic and the bound
methods of builtin types.

The namespace heap (`namespace()` objects) is passed in where an operation
can read it.
-/

namespace LeanJinja2

open LeanMarkupsafe

/-- The namespace heap: the attributes of each `namespace()` object. -/
abbrev Heap := List (List (String × Value))

def undefinedError (i : UndefInfo) : ValueError := .undefined i.message

/-- The policy an undefined value follows: the environment's, except for the
plain undefined of a conditional expression without `else`. -/
def UndefInfo.policy (pol : UndefinedPolicy) : UndefInfo → UndefinedPolicy
  | .plain _ => .default
  | _ => pol

/-- Python `str(v)` under the undefined policy. -/
def strOf (pol : UndefinedPolicy) : Value → Except ValueError String
  | .undef i =>
    match i.policy pol with
    | .strict => .error (undefinedError i)
    | .debug =>
      .ok (match i with
        | .name n => "{{ " ++ n ++ " }}"
        | .attr o n => "{{ no such element: " ++ o ++ "[" ++ pyStrRepr n ++ "] }}"
        | .hint h | .plain h => "{{ undefined value printed: " ++ h ++ " }}")
    | _ => .ok ""
  | v => .ok v.toStr

/-- Python truthiness under the undefined policy. -/
def truthyOf (pol : UndefinedPolicy) : Value → Except ValueError Bool
  | .undef i => if i.policy pol == .strict then .error (undefinedError i) else .ok false
  | v => .ok v.truthy

/-- The characters of a string, as one-character strings. -/
def charValues (s : String) : List Value := s.toList.map (fun c => .str (String.singleton c))

/-- Python `iter(v)` under the undefined policy: the items a `for` loop sees. -/
def iterOf (pol : UndefinedPolicy) (heap : Heap) : Value → Except ValueError (List Value)
  | .list xs => .ok xs
  | .tuple xs => .ok xs
  | .dict kvs => .ok (kvs.map Prod.fst)
  | .str s => .ok (charValues s)
  | .markup m => .ok (charValues m.str)
  | .undef i => if i.policy pol == .strict then .error (undefinedError i) else .ok []
  | .ns a => .ok (((heap[a]?).getD []).map (fun p => Value.str p.1))
  | v => .error (.typeError s!"'{v.typeName}' object is not iterable")

/-- Python `len(v)` under the undefined policy. -/
def lenOf (pol : UndefinedPolicy) : Value → Except ValueError Nat
  | .list xs => .ok xs.length
  | .tuple xs => .ok xs.length
  | .dict kvs => .ok kvs.length
  | .str s => .ok s.length
  | .markup m => .ok m.str.length
  | .loop _ len .. => .ok len
  | .undef i => if i.policy pol == .strict then .error (undefinedError i) else .ok 0
  | v => .error (.typeError s!"object of type '{v.typeName}' has no len()")

/-- Upstream `escape(v)`: markup passes through, anything else is converted
with `str()` and escaped. -/
def escapeOf (pol : UndefinedPolicy) : Value → Except ValueError Markup
  | .markup m => .ok m
  | .module _ _ out => .ok (LeanMarkupsafe.Markup.markSafe out)
  | v => do let s ← strOf pol v; pure (escape s)

/-- Spread a call's `*args` and `**kwargs` (the parser keeps them as keyword
entries named `*` and `**`, which no identifier can be): the iterable's items
follow the positional arguments, the mapping's entries follow the keywords. -/
def spreadArgs (pol : UndefinedPolicy) (heap : Heap) (av : List Value) (kv : List (String × Value)) :
    Except ValueError (List Value × List (String × Value)) := do
  if kv.any (fun p => p.1 == "*" || p.1 == "**") then
    let star ← (kv.filter (·.1 == "*")).mapM (fun p => iterOf pol heap p.2)
    let dstar ← (kv.filter (·.1 == "**")).mapM (fun p => match p.2 with
      | .dict kvs => kvs.mapM (fun q => match q.1 with
        | .str k => .ok (k, q.2)
        | _ => .error (.typeError "keywords must be strings"))
      | v => .error (.typeError s!"argument after ** must be a mapping, not {v.typeName}"))
    pure (av ++ star.flatten, kv.filter (fun p => p.1 != "*" && p.1 != "**") ++ dstar.flatten)
  else pure (av, kv)

/-- Upstream `soft_str`: markup stays markup, anything else becomes text. -/
def softOf (pol : UndefinedPolicy) : Value → Except ValueError SoftString
  | .markup m => .ok (.markup m)
  | v => do let s ← strOf pol v; pure (.plain s)

/-- An operation on an undefined value fails (upstream
`_fail_with_undefined_error`). -/
def failUndef {α : Type} (i : UndefInfo) : Except ValueError α := .error (undefinedError i)

/-! ## Attribute and item access -/

/-- Methods of each builtin type that attribute access returns bound. -/
def dictMethods : List String := ["items", "keys", "values", "get"]
def strMethods : List String :=
  ["upper", "lower", "strip", "lstrip", "rstrip", "split", "startswith", "endswith", "replace",
   "title", "capitalize", "join", "count", "find", "isdigit", "isalpha", "isalnum", "isspace",
   "islower", "isupper", "splitlines", "format", "center", "zfill"]
def listMethods : List String := ["index", "count"]

/-- Python list indexing with negative indices. -/
def indexList (xs : List Value) (i : Int) : Option Value :=
  let n : Int := xs.length
  let j := if i < 0 then i + n else i
  if j < 0 || j ≥ n then none else xs[j.toNat]?

/-- Python `s[i]` on a string: the character as a string, without a value
per character (`indexList (charValues s) i`). -/
def strIndex (s : String) (i : Int) : Option String :=
  let n : Int := s.length
  let j := if i < 0 then i + n else i
  if j < 0 || j ≥ n then none else (s.drop j.toNat).front?.map String.singleton

/-- Loop attributes (upstream `LoopContext`). -/
def loopAttr (index0 length depth0 : Nat) (prev next : Option Value) (recur : Option LoopRec)
    (cell : Nat) (a : String) : Option Value :=
  match a with
  | "index" => some (.int (index0 + 1))
  | "index0" => some (.int index0)
  | "revindex" => some (.int ((length : Int) - index0))
  | "revindex0" => some (.int ((length : Int) - index0 - 1))
  | "first" => some (.bool (index0 == 0))
  | "last" => some (.bool (index0 + 1 == length))
  | "length" => some (.int length)
  | "depth" => some (.int (depth0 + 1))
  | "depth0" => some (.int depth0)
  | "previtem" => some (prev.getD (.undef (.hint "there is no previous item")))
  | "nextitem" => some (next.getD (.undef (.hint "there is no next item")))
  | "cycle" => some (.method (.loop index0 length depth0 prev next recur cell) "cycle")
  | "changed" => some (.method (.loop index0 length depth0 prev next recur cell) "changed")
  | _ => none

/-- The number attributes of Python's `int`. -/
def intAttr (n : Int) : String → Option Value
  | "real" | "numerator" => some (.int n)
  | "imag" => some (.int 0)
  | "denominator" => some (.int 1)
  | _ => none

/-- Python attribute lookup only (no item fallback); `none` if missing. -/
def pyAttr (heap : Heap) (v : Value) (a : String) : Option Value :=
  match v with
  | .dict _ => if dictMethods.contains a then some (.method v a) else none
  | .str _ | .markup _ => if strMethods.contains a then some (.method v a) else none
  | .list _ => if listMethods.contains a then some (.method v a) else none
  | .tuple _ => if a == "index" || a == "count" then some (.method v a) else none
  -- the number attributes of Python's `int` (and `bool`) and `float`
  | .int n => intAttr n a
  | .bool b => intAttr (if b then 1 else 0) a
  | .float .. =>
    match a with
    | "real" => some v
    | "imag" => some (.float 0 1)
    | _ => none
  | .loop i len d p nx r c => loopAttr i len d p nx r c a
  | .ns addr => ((heap[addr]?).getD []).lookup a
  | .macro n ps body uc .. =>
    match a with
    | "name" => some (.str n)
    | "arguments" => some (.tuple (ps.map (fun p => .str p.1)))
    | "caller" => some (.bool uc)
    | "catch_kwargs" => some (.bool (mentionsName "kwargs" body))
    | "catch_varargs" => some (.bool (mentionsName "varargs" body))
    | _ => none
  | .module _ exports _ => exports.lookup a
  | _ => none

/-- Python `obj[key]` only (no attribute fallback); `none` if missing. -/
def pyItem (heap : Heap) (v : Value) (k : Value) : Option Value :=
  match v, k with
  | .dict kvs, _ => Value.lookupIn kvs k
  | .list xs, .int i => indexList xs i
  | .list xs, .bool b => indexList xs (if b then 1 else 0)
  | .tuple xs, .int i => indexList xs i
  | .str s, .int i => (strIndex s i).map Value.str
  | .markup m, .int i => (strIndex m.str i).map (fun t => .markup (Markup.markSafe t))
  | .ns addr, .str a => ((heap[addr]?).getD []).lookup a
  | _, _ => none

/-- Upstream `Environment.getattr(obj, attr)`: attribute, then item, then
undefined. Attribute access on an undefined value fails, except under the
chainable policy. -/
def getattrV (pol : UndefinedPolicy) (heap : Heap) (v : Value) (a : String) :
    Except ValueError Value :=
  match v with
  | .undef i => if i.policy pol == .chainable then .ok v else failUndef i
  | _ =>
    match pyAttr heap v a with
    | some r => .ok r
    | none =>
      match pyItem heap v (.str a) with
      | some r => .ok r
      | none => .ok (.undef (.attr v.objectTypeRepr a))

/-- Upstream `Environment.getitem(obj, key)`: item, then (for a string key)
attribute, then undefined. -/
def getitemV (pol : UndefinedPolicy) (heap : Heap) (v : Value) (k : Value) :
    Except ValueError Value :=
  match v with
  | .undef i => if i.policy pol == .chainable then .ok v else failUndef i
  | _ =>
    match pyItem heap v k with
    | some r => .ok r
    | none =>
      match k with
      | .str a =>
        match pyAttr heap v a with
        | some r => .ok r
        | none => .ok (.undef (.attr v.objectTypeRepr a))
      | _ => .ok (.undef (.hint s!"{v.objectTypeRepr} has no element {k.repr}"))

/-- Python slice bounds for a sequence of length `n`. -/
def sliceRange (n : Nat) (start stop step : Option Int) : Except ValueError (Int × Int × Nat) :=
  let st := step.getD 1
  if st == 0 then .error (.typeError "slice step cannot be zero") else
  let n' : Int := n
  let clamp := fun (lo hi : Int) (x : Int) => if x < lo then lo else if x > hi then hi else x
  let norm := fun (x : Int) => if x < 0 then x + n' else x
  if st > 0 then
    let a := clamp 0 n' (norm (start.getD 0))
    let b := clamp 0 n' (norm (stop.getD n'))
    let count := if b > a then ((b - a + st - 1) / st).toNat else 0
    .ok (a, st, count)
  else
    let a := clamp (-1) (n' - 1) (norm (start.getD (n' - 1)))
    let b := clamp (-1) (n' - 1) (match stop with | some x => norm x | none => -1)
    let count := if a > b then ((a - b + (-st) - 1) / (-st)).toNat else 0
    .ok (a, st, count)

/-- The indices of a slice: `count` of them from `a` in steps of `st`. -/
def sliceIndices (n : Nat) (start stop step : Option Int) : Except ValueError (List Nat) := do
  let (a, st, count) ← sliceRange n start stop step
  pure ((List.range count).map (fun (k : Nat) => (a + (k : Int) * st).toNat))

/-- Fold over the indices `a, a + st, ...` (`count` of them), without a list
of them. -/
def idxFold {β : Type} (f : β → Nat → β) (a st : Int) : Nat → β → β
  | 0, b => b
  | k + 1, b => idxFold f (a + st) st k (f b a.toNat)

/-- The items of `arr` at a slice's indices, in one pass. -/
def slicePick {α : Type} (arr : Array α) (a st : Int) (count : Nat) : Array α :=
  idxFold (fun acc i => match arr[i]? with | some x => acc.push x | none => acc) a st count
    (Array.mkEmpty count)

/-- An optional slice bound as an integer. -/
def sliceBound : Option Value → Except ValueError (Option Int)
  | none => .ok none
  | some .none => .ok none
  | some (.int i) => .ok (some i)
  | some (.bool b) => .ok (some (if b then 1 else 0))
  | some v => .error (.typeError s!"slice indices must be integers or None, not {v.typeName}")

/-- Python `v[start:stop:step]`. -/
def sliceV (pol : UndefinedPolicy) (v : Value) (start stop step : Option Value) :
    Except ValueError Value := do
  let a ← sliceBound start
  let b ← sliceBound stop
  let c ← sliceBound step
  -- one pass over an array of the items (a list indexed per item is quadratic)
  let pick := fun (xs : List Value) => do
    let arr := xs.toArray
    let (i, st, count) ← sliceRange arr.size a b c
    pure (slicePick arr i st count).toList
  let pickStr := fun (s : String) => do
    let arr : Array Char := s.foldl (·.push ·) #[]
    let (i, st, count) ← sliceRange arr.size a b c
    pure ((slicePick arr i st count).foldl (·.push ·) "")
  match v with
  | .list xs => return .list (← pick xs)
  | .tuple xs => return .tuple (← pick xs)
  | .str s => return .str (← pickStr s)
  | .markup m => return .markup (Markup.markSafe (← pickStr m.str))
  | .undef i => if i.policy pol == .chainable then pure v else failUndef i
  | _ => .error (.typeError s!"'{v.typeName}' object is not subscriptable")

/-! ## Arithmetic -/

/-- The result of a binary arithmetic operator on defined values. -/
def arith (op : BinOp) (a b : Value) : Except ValueError Value :=
  let tyErr := fun (sym : String) =>
    Except.error (ValueError.typeError
      s!"unsupported operand type(s) for {sym}: '{a.typeName}' and '{b.typeName}'")
  match op with
  | .add =>
    match a, b with
    | .markup m, .str s => .ok (.markup (m ++ s))
    | .str s, .markup m => .ok (.markup (s ++ m))
    | .markup m, .markup n => .ok (.markup (m ++ n))
    | .str s, .str t => .ok (.str (s ++ t))
    | .list xs, .list ys => .ok (.list (xs ++ ys))
    | .tuple xs, .tuple ys => .ok (.tuple (xs ++ ys))
    | _, _ =>
      match a.num?, b.num? with
      | some x, some y => if a.isFloat || b.isFloat then .ok (mkFloat (decAdd x y))
        else .ok (.int (x.1 + y.1))
      | _, _ => tyErr "+"
  | .sub =>
    match a.num?, b.num? with
    | some x, some y => if a.isFloat || b.isFloat then .ok (mkFloat (decSub x y))
      else .ok (.int (x.1 - y.1))
    | _, _ => tyErr "-"
  | .mul =>
    match a, b with
    | .str s, .int k | .int k, .str s => .ok (.str (String.join (List.replicate k.toNat s)))
    | .markup m, .int k | .int k, .markup m => .ok (.markup (Markup.times m k.toNat))
    | .list xs, .int k | .int k, .list xs => .ok (.list (List.replicate k.toNat xs).flatten)
    | .tuple xs, .int k | .int k, .tuple xs => .ok (.tuple (List.replicate k.toNat xs).flatten)
    | _, _ =>
      match a.num?, b.num? with
      | some x, some y => if a.isFloat || b.isFloat then .ok (mkFloat (decMul x y))
        else .ok (.int (x.1 * y.1))
      | _, _ => tyErr "*"
  | .div =>
    match a.num?, b.num? with
    | some x, some y => if y.1 == 0 then .error (.typeError "division by zero")
      else .ok (mkFloat (decDiv x y))
    | _, _ => tyErr "/"
  | .floordiv =>
    match a.num?, b.num? with
    | some x, some y =>
      if y.1 == 0 then .error (.typeError "integer division or modulo by zero")
      else if a.isFloat || b.isFloat then .ok (mkFloat (decFloorDiv x y, 0))
      else .ok (.int (Int.fdiv x.1 y.1))
    | _, _ => tyErr "//"
  | .mod =>
    match a.num?, b.num? with
    | some x, some y =>
      if y.1 == 0 then .error (.typeError "integer division or modulo by zero")
      else if a.isFloat || b.isFloat then
        let q := decFloorDiv x y
        .ok (mkFloat (decSub x (decMul y (q, 0))))
      else .ok (.int (Int.fmod x.1 y.1))
    | _, _ => tyErr "%"
  | .pow =>
    match a.num?, b.num? with
    | some x, some (e, 0) =>
      if e ≥ 0 then
        if a.isFloat then .ok (mkFloat (decNorm (x.1 ^ e.toNat) (x.2 * e.toNat)))
        else .ok (.int (x.1 ^ e.toNat))
      else if x.1 == 0 then .error (.typeError "0.0 cannot be raised to a negative power")
      else .ok (mkFloat (decDiv (1, 0) (decNorm (x.1 ^ e.natAbs) (x.2 * e.natAbs))))
    | some _, some _ => .error (.typeError "fractional powers are not supported by lean-jinja2")
    | _, _ => tyErr "** or pow()"
  | .and | .or => .error (.typeError "internal: logical operator in arith")

/-- `x in container` (Python `in`). -/
def containsV (pol : UndefinedPolicy) (heap : Heap) (x container : Value) :
    Except ValueError Bool :=
  match container with
  | .str s | .markup ⟨s⟩ =>
    match x.text? with
    | some t => .ok (containsSub s.toList t.toList)
    | none => .error (.typeError s!"'in <string>' requires string as left operand, not {x.typeName}")
  | .list xs | .tuple xs => .ok (xs.any (fun y => Value.pyEq x y))
  | .dict kvs => .ok (kvs.any (fun p => Value.pyEq x p.1))
  | .undef i => if i.policy pol == .strict then failUndef i else .ok false
  | .ns addr => .ok ((((heap[addr]?).getD []).map Prod.fst).any (fun k => Value.pyEq x (.str k)))
  | v => .error (.typeError s!"argument of type '{v.typeName}' is not iterable")

end LeanJinja2
