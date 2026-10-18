import LeanJinja2.RepoImpl.Filters

/-!
# Methods of builtin values

The bound methods attribute access returns (`d.items()`, `s.upper()`,
`loop.cycle(...)`): Python's behaviour for the common ones. Markup receivers
return markup and escape plain arguments, as MarkupSafe's methods do.
-/

namespace LeanJinja2

open LeanMarkupsafe

/-- Python `str.split(sep, maxsplit)`. -/
def splitMax (l : List Char) (sep : Option (List Char)) (maxsplit : Int) : List (List Char) :=
  match sep with
  | none =>
    if maxsplit < 0 then splitWs l
    else
      -- whitespace split with a limit: the remainder keeps its inner spacing
      let rec go : Nat → List Char → Int → List (List Char)
        | 0, _, _ => []
        | fuel + 1, l, k =>
          let l := l.dropWhile isSpace
          if l.isEmpty then [] else
          if k == 0 then [rstripList l] else
          let w := l.takeWhile (fun c => !isSpace c)
          w :: go fuel (l.drop w.length) (k - 1)
      go (l.length + 1) l maxsplit
  | some s =>
    if maxsplit < 0 then splitOn l s
    else
      let rec go2 : Nat → List Char → Int → List (List Char)
        | 0, l, _ => [l]
        | fuel + 1, l, k =>
          if k == 0 then [l] else
          match findSub l s with
          | some i => l.take i :: go2 fuel (l.drop (i + s.length)) (k - 1)
          | none => [l]
      go2 (l.length + 1) l maxsplit

/-- Python `str.format` with `{}`, `{0}` and `{name}` fields (no format
specs or conversions). -/
def strFormat (pol : UndefinedPolicy) (esc : Bool) (tmpl : String) (args : List Value)
    (kwargs : List (String × Value)) : Except RenderError String := do
  let conv := fun (v : Value) => if esc then (do let m ← escapeOf pol v; pure m.str) else strOf pol v
  let rec go : Nat → List Char → Nat → Except RenderError (List Char)
    | 0, _, _ => .ok []
    | _ + 1, [], _ => .ok []
    | fuel + 1, '{' :: '{' :: r, k => do let o ← go fuel r k; pure ('{' :: o)
    | fuel + 1, '}' :: '}' :: r, k => do let o ← go fuel r k; pure ('}' :: o)
    | fuel + 1, '{' :: r, k => do
      let field := r.takeWhile (· != '}')
      let rest := r.drop (field.length + 1)
      let fname := (field.takeWhile (fun c => c != ':' && c != '!'))
      let (v, k') ←
        if fname.isEmpty then
          match args[k]? with
          | some v => pure (v, k + 1)
          | none => .error (.typeError s!"Replacement index {k} out of range for positional args tuple")
        else if fname.all Char.isDigit then
          let i := digitsValue 10 fname
          match args[i]? with
          | some v => pure (v, k)
          | none => .error (.typeError s!"Replacement index {i} out of range for positional args tuple")
        else
          match kwargs.lookup (String.ofList fname) with
          | some v => pure (v, k)
          | none => .error (.typeError s!"KeyError: '{String.ofList fname}'")
      let s ← conv v
      let o ← go fuel rest k'
      pure (s.toList ++ o)
    | fuel + 1, c :: r, k => do let o ← go fuel r k; pure (c :: o)
  let out ← go (tmpl.length + 1) tmpl.toList 0
  pure (String.ofList out)

/-- Call a bound method. -/
def callMethod (fc : FCtx) (recv : Value) (name : String) (args : List Value)
    (kwargs : List (String × Value)) : Except RenderError Value := do
  let pol := fc.pol
  let a := argAt args kwargs
  let textArg := fun (i : Nat) (n : String) => do
    match a i n with
    | some v => strOf pol v
    | none => typeErr s!"{name}() missing required argument '{n}'"
  match recv with
  | .dict kvs =>
    match name with
    | "items" => pure (.list (kvs.map (fun p => .tuple [p.1, p.2])))
    | "keys" => pure (.list (kvs.map Prod.fst))
    | "values" => pure (.list (kvs.map Prod.snd))
    | "get" =>
      match args with
      | k :: rest => pure ((Value.lookupIn kvs k).getD (rest.head?.getD .none))
      | [] => typeErr "get expected at least 1 argument, got 0"
    | _ => typeErr s!"'dict' object has no attribute '{name}'"
  | .str _ | .markup _ =>
    let s := recv.toStr
    let l := s.toList
    let isM := recv.isMarkup
    -- markup methods escape plain string arguments
    let argText := fun (v : Value) => if isM then (do let m ← escapeOf pol v; pure m.str) else strOf pol v
    match name with
    | "upper" => pure (keepKind recv (strUpper s))
    | "lower" => pure (keepKind recv (strLower s))
    | "capitalize" => pure (keepKind recv (strCapitalize s))
    | "title" => pure (keepKind recv (String.ofList (titleList l)))
    | "strip" | "lstrip" | "rstrip" => do
      let chars ← match a 0 "chars" with
        | none | some .none => pure none
        | some c => do let t ← strOf pol c; pure (some t.toList)
      let isC := fun (c : Char) => match chars with | some cs => cs.contains c | none => isSpace c
      let r := if name == "rstrip" then l else l.dropWhile isC
      let r := if name == "lstrip" then r else (r.reverse.dropWhile isC).reverse
      pure (keepKind recv (String.ofList r))
    | "split" => do
      let sep ← match a 0 "sep" with
        | none | some .none => pure none
        | some v => do let t ← strOf pol v; pure (some t.toList)
      if sep == some [] then typeErr "empty separator" else
      let mx ← match a 1 "maxsplit" with
        | none => pure (-1 : Int)
        | some v => intArg v "maxsplit"
      pure (.list ((splitMax l sep mx).map (fun p => keepKind recv (String.ofList p))))
    | "splitlines" => pure (.list ((splitLines l).map (fun p => keepKind recv (String.ofList p))))
    | "startswith" | "endswith" => do
      let ps ← match a 0 "prefix" with
        | some (.tuple xs) => xs.mapM (strOf pol)
        | some v => do let t ← strOf pol v; pure [t]
        | none => typeErr s!"{name}() takes at least 1 argument (0 given)"
      pure (.bool (ps.any (fun p => if name == "startswith" then s.startsWith p else s.endsWith p)))
    | "replace" => do
      let o ← match a 0 "old" with | some v => argText v | none => typeErr "replace() missing 'old'"
      let n ← match a 1 "new" with | some v => argText v | none => typeErr "replace() missing 'new'"
      let c ← match a 2 "count" with | some v => intArg v "count" | none => pure (-1 : Int)
      pure (keepKind recv (String.ofList (replaceList l o.toList n.toList c)))
    | "join" => do
      let xs ← match a 0 "iterable" with
        | some v => iterOf pol fc.heap v
        | none => typeErr "join() takes exactly one argument (0 given)"
      let parts ← xs.mapM argText
      pure (keepKind recv (s.intercalate parts))
    | "count" => do
      let sub ← textArg 0 "sub"
      if sub.isEmpty then pure (.int (l.length + 1)) else
      pure (.int ((splitOn l sub.toList).length - 1))
    | "find" => do
      let sub ← textArg 0 "sub"
      pure (.int (match findSub l sub.toList with | some i => (i : Int) | none => -1))
    | "isdigit" => pure (.bool (!l.isEmpty && l.all Char.isDigit))
    | "isalpha" => pure (.bool (!l.isEmpty && l.all Char.isAlpha))
    | "isalnum" => pure (.bool (!l.isEmpty && l.all Char.isAlphanum))
    | "isspace" => pure (.bool (!l.isEmpty && l.all isSpace))
    | "islower" => pure (.bool (l.any Char.isLower && !l.any Char.isUpper))
    | "isupper" => pure (.bool (l.any Char.isUpper && !l.any Char.isLower))
    | "format" => do
      let r ← strFormat pol isM s args kwargs
      pure (keepKind recv r)
    | "center" => applyFilter fc "center" recv args kwargs
    | "zfill" => do
      let w ← intArg ((a 0 "width").getD (.int 0)) "width"
      if w.toNat ≤ l.length then pure recv else
      let pad := List.replicate (w.toNat - l.length) '0'
      let r := match l with
        | c :: cs => if c == '-' || c == '+' then c :: pad ++ cs else pad ++ l
        | [] => pad
      pure (keepKind recv (String.ofList r))
    | _ => typeErr s!"'str' object has no attribute '{name}'"
  | .list xs | .tuple xs =>
    match name, args with
    | "index", [x] =>
      match xs.findIdx? (fun y => Value.pyEq y x) with
      | some i => pure (.int i)
      | none => .error (.typeError s!"{x.repr} is not in list")
    | "count", [x] => pure (.int (xs.countP (fun y => Value.pyEq y x)))
    | _, _ => typeErr s!"'{recv.typeName}' object has no attribute '{name}'"
  | .loop i _ _ _ _ _ =>
    match name with
    | "cycle" =>
      if args.isEmpty then typeErr "no items for cycling given"
      else pure (args[i % args.length]?.getD .none)
    | _ => .error (.runtime "loop.changed() is not supported by lean-jinja2")
  | v => typeErr s!"'{v.typeName}' object has no attribute '{name}'"

end LeanJinja2
