import LeanJinja2.DataTypes.Environment
import LeanJinja2.RepoImpl.LexFast
import LeanJinja2.RepoImpl.Parser
import LeanJinja2.RepoImpl.AstWalk
import LeanJinja2.RepoImpl.Depth
import LeanJinja2.RepoImpl.Methods
import LeanJinja2.RepoImpl.StrIndex

/-!
# The renderer

A total interpreter of the AST, standing in for upstream's compiler plus the
generated Python code. Rendering a node list produces a *trace*: the pieces
of output in order, each either literal template text (`Piece.lit`) or an
interpolated value with the autoescape flag in force where it was
interpolated (`Piece.value`). The output string is the trace flattened
(`Piece.flatten`): literal text as is, each value through `escape` when the
flag is set and through `str` otherwise. That separation is what
`autoescape_sound` is stated over.

Every function takes a depth budget (`fuel`) and passes one less to what it
calls, so rendering is total by structural recursion; running out is a
`RecursionError` (`RenderError.fuelExhausted`), as upstream raises one for
unbounded recursion through macros, includes and inheritance.

Scoping follows upstream: `for`, `with`, macro bodies, `{% filter %}`,
`{% set %}` blocks and non-scoped blocks have their own locals; `{% set %}` at
template top level writes the template context, which `extends` passes on to
the parent. After `{% extends %}` runs, the rest of the child's top-level
output is discarded, and the parent renders with the child's blocks first in
each block chain.
-/

namespace LeanJinja2

open LeanMarkupsafe

instance : Coe Bool AutoescapePolicy := ⟨.const⟩

/-- A piece of output. -/
inductive Piece where
  /-- Literal template text. -/
  | lit (s : String)
  /-- An interpolated value, and whether autoescaping was on there. -/
  | value (v : Value) (esc : Bool)
  deriving Inhabited

/-- The text of one piece: literal text as is, a value escaped when `esc`
(upstream `escape`, which leaves markup alone) and converted with `str`
otherwise. -/
def Piece.text (pol : UndefinedPolicy) : Piece → Except ValueError String
  | .lit s => .ok s
  | .value v true => do let m ← escapeOf pol v; pure m.str
  | .value v false => strOf pol v

/-- The output a trace stands for. -/
def Piece.flatten (pol : UndefinedPolicy) (ps : List Piece) : Except ValueError String := do
  let ss ← ps.mapM (Piece.text pol)
  pure (String.join ss)

/-- A block body in a block chain, with the settings of the template it came
from. -/
structure BlockEntry where
  body : List Node
  autoescape : Bool
  required : Bool
  deriving Inhabited

/-- The rendering frame (upstream's `Context` plus the compiler's frame). -/
structure Frame where
  /-- The template context: globals, render arguments, exported top-level sets. -/
  ctx : List (String × Value)
  /-- Local variables (loop variables, macro arguments, `with`, nested sets). -/
  locals : List (String × Value) := []
  /-- At template top level, where `set` exports to the context. -/
  top : Bool := true
  /-- Autoescaping in force. -/
  autoescape : Bool := false
  /-- Block bodies from extending templates, child first. -/
  overrides : List (String × List BlockEntry) := []
  /-- The blocks of the template being rendered. -/
  own : List (String × BlockEntry) := []
  /-- The block being rendered and its position in the chain (for `super()`). -/
  curBlock : Option (String × Nat) := none
  /-- The template this one extends, once `{% extends %}` has run. -/
  parent : Option String := none
  /-- The template's name. -/
  name : Option String := none
  deriving Inhabited

/-- Variable lookup: locals, then the template context. -/
def Frame.lookup? (fr : Frame) (n : String) : Option Value :=
  match fr.locals.lookup n with
  | some v => some v
  | none => fr.ctx.lookup n

/-- The block chain of a name: the overrides, then the template's own. -/
def Frame.chain (fr : Frame) (n : String) : List BlockEntry :=
  (fr.overrides.lookup n).getD [] ++ (fr.own.lookup n).toList

/-- The renderer's monad: the namespace heap and render errors. -/
abbrev RenderM := StateT Heap (Except RenderError)

/-- Run a value operation: its error becomes a render error. -/
def liftR {α : Type} (x : Except ValueError α) : RenderM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e.toRenderError

/-- Run a loading step (`getSource`, `compile`). -/
def liftE {α : Type} (x : Except RenderError α) : RenderM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-- The value of a constant. -/
def Const.toValue : Const → Value
  | .none => .none
  | .bool b => .bool b
  | .int i => .int i
  | .float m s => mkFloat (m, s)
  | .str s => .str s

/-- What filters and tests read, for a frame. -/
def Environment.fctx (env : Environment) (fr : Frame) (heap : Heap) : FCtx :=
  { autoescape := fr.autoescape, pol := env.undefined, heap, leeway := env.truncateLeeway,
    filters := env.filters, tests := env.tests, vars := fr.locals ++ fr.ctx,
    rng := rngOf env.randomSeed heap, urlizeRel := env.urlizeRel,
    urlizeTarget := env.urlizeTarget, urlizeExtraSchemes := env.urlizeExtraSchemes }

/-- The bindings an assignment target makes (tuple unpacking as Python). -/
def bindTarget (pol : UndefinedPolicy) (heap : Heap) (t : Target) (v : Value) :
    Except ValueError (List (String × Value)) :=
  match t with
  | .name n => .ok [(n, v)]
  | .nsAttr _ _ => .error (.assertion "namespace attributes can only be assigned with set")
  | .tuple ts => do
    let xs ← iterOf pol heap v
    if xs.length < ts.length then
      .error (.typeError s!"not enough values to unpack (expected {ts.length}, got {xs.length})")
    else if xs.length > ts.length then
      .error (.typeError s!"too many values to unpack (expected {ts.length})")
    else
      let parts ← (ts.attach.zip xs).mapM (fun (⟨t, _⟩, x) => bindTarget pol heap t x)
      pure parts.flatten
termination_by sizeOf t
decreasing_by simp_wf; have := List.sizeOf_lt_of_mem ‹_›; omega

/-- Update one attribute of a namespace object. -/
def heapSet (heap : Heap) (addr : Nat) (k : String) (v : Value) : Heap :=
  heap.set addr ((k, v) :: ((heap[addr]?).getD []).filter (·.1 != k))

/-- `v[k]` (`getitemV`); indexing a string goes through the view of heap
cell 1 (`StrIndex`), so a loop indexing one string is linear. -/
def getitemM (pol : UndefinedPolicy) (v k : Value) : RenderM Value := do
  let h ← get
  match v, k with
  | .str s, .int i => do
    let (r, cell) := strIndexCached ((h[1]?).getD []) s i
    set (h.set 1 cell)
    pure (itemOr h v k (r.map Value.str))
  | .markup m, .int i => do
    let (r, cell) := strIndexCached ((h[1]?).getD []) m.str i
    set (h.set 1 cell)
    pure (itemOr h v k (r.map (fun t => .markup (Markup.markSafe t))))
  | _, _ => liftR (getitemV pol h v k)

/-- Store the random source's state (heap cell `0`). -/
def setRng (heap : Heap) (s : UInt64) : Heap := heapSet heap 0 "state" (.int s.toNat)

/-- Apply a filter; `random` advances the render's random source. -/
def applyFilterM (env : Environment) (fr : Frame) (name : String) (v : Value) (args : List Value)
    (kwargs : List (String × Value)) : RenderM Value := do
  let h ← get
  if name == "random" && args.isEmpty && kwargs.isEmpty then do
    let (r, s) ← liftR (randomChoice env.undefined h (rngOf env.randomSeed h) v)
    set (setRng h s)
    pure r
  else liftR (applyFilter (env.fctx fr h) name v args kwargs)

/-- Wrap rendered text as the value a macro call, block call or filter block
returns: markup under autoescape (upstream `Markup(rv)`), text otherwise. -/
def wrapText (autoescape : Bool) (s : String) : Value :=
  if autoescape then .markup (Markup.markSafe s) else .str s

/-- Merge a template's blocks behind the existing overrides (upstream appends
the parent's block to each chain). -/
def mergeOverrides (old : List (String × List BlockEntry)) (own : List (String × BlockEntry)) :
    List (String × List BlockEntry) :=
  own.foldl (fun acc (n, be) =>
    match acc.lookup n with
    | some l => acc.map (fun p => if p.1 == n then (n, l ++ [be]) else p)
    | none => acc ++ [(n, [be])]) old

/-! ## Loading and compiling -/

/-- Line number of a character offset: one plus the line breaks before it
(counted in place, without a list of the source). -/
def lineOf (src : String) (pos : Nat) : Nat :=
  1 + Cursor.foldTake (fun n c => if c == '\n' then n + 1 else n) 0 src.toSlice.startPos pos

/-- Upstream `split_template_path`: `/`-separated pieces, `..` rejected. -/
def splitTemplatePath (name : String) : Option (List String) :=
  let pieces := (name.splitOn "/").filter (fun p => !p.isEmpty && p != ".")
  if pieces.contains ".." then none else some pieces

/-- The source of a template (upstream `loader.get_source`). -/
def Environment.getSource (env : Environment) (name : String) : Except RenderError String :=
  match env.loader with
  | .dict m =>
    match m.lookup name with
    | some s => .ok s
    | none => .error (.notFound name)
  | .fileSystem _ files =>
    match splitTemplatePath name with
    | none => .error (.notFound name)
    | some pieces =>
      match files.lookup ("/".intercalate pieces) with
      | some s => .ok s
      | none => .error (.notFound name)

/-- Whether two names in a list repeat; the first repeated one. -/
def firstDuplicate : List String → Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDuplicate xs

/-- The depth budget a body needs: three levels of the renderer's recursion
per level of nesting (node, node list, loop), plus the template and the
list it starts with. `render_total` shows it suffices for templates that do
not recurse. -/
def renderBudget (body : List Node) : Nat := 3 * nodesDepth body + 2

/-- Lex, parse and check a template source (upstream `Environment.compile`):
syntax errors carry their line; unknown filters and duplicate blocks are
`TemplateAssertionError`s. -/
def Environment.compile (env : Environment) (src : String) : Except RenderError (List Node) :=
  match lexFast env.toLexConfig src with
  | .error e => .error (.syntax e.msg (lineOf src e.pos))
  | .ok toks =>
    let sig := significantL toks
    match parseTokens sig with
    | .error e =>
      -- the offset of the significant token the parser stopped at
      let idx := sig.length - e.remaining
      let rec posOf : List TokL → Nat → Nat → Nat
        | [], _, p => p
        | t :: ts, k, p =>
          if t.kind.ignored then posOf ts k (p + t.len)
          else if k == 0 then p else posOf ts (k - 1) (p + t.len)
      .error (.syntax e.msg (lineOf src (posOf toks idx 0)))
    | .ok body =>
      -- too deep for the depth budget: upstream's RecursionError, raised here
      -- before any walk over the tree (see `render_total` for the bound)
      if env.maxDepth < renderBudget body then .error .fuelExhausted else
      let fc : FCtx := { filters := env.filters, tests := env.tests }
      match (hardFilterTestNames body).find? (fun p => !(if p.1 then fc.hasFilter p.2 else fc.hasTest p.2)) with
      | some (isF, f) => .error (.assertion s!"No {if isF then "filter" else "test"} named '{f}'.")
      | none =>
        if (forTargets body).any (fun t => t.names.contains "loop") then
          .error (.assertion "Can't assign to special loop variable in for-loop target.")
        else
        match firstDuplicate ((blockDefs body).map (·.1)) with
        | some b => .error (.assertion s!"block '{b}' defined twice")
        | none => .ok body

/-- The variables a render starts from: the arguments over the globals. -/
def Environment.startContext (env : Environment) (vars : List (String × Value)) :
    List (String × Value) :=
  vars ++ env.globals ++ builtinGlobals

/-- The template names an `{% include %}` expression names: one string, or a
list of candidates. -/
def includeNames (pol : UndefinedPolicy) (heap : Heap) : Value → Except ValueError (List String)
  | .str s => .ok [s]
  | .undef i => failUndef i
  | v => do
    let xs ← iterOf pol heap v
    xs.mapM (strOf pol)

/-- An exported value: a macro defined without a closure context gets the
module's final context `ctx`, anything else is itself. -/
def exportValue (ctx : List (String × Value)) : Value → Value
  | .macro nm ps body uc clo none => .macro nm ps body uc clo (some ctx)
  | v => v

/-- What an imported template exports (upstream `Context.get_exported`): the
names its top level assigned, newest first, without the ones starting with
`_`. `ctx` is its final context and `start` the length of the one it began
with; assignments at top level are prepended. Exported macros keep that
context, so they see the module's variables wherever they are called. -/
def moduleExports (start : Nat) (ctx : List (String × Value)) : List (String × Value) :=
  let fresh := (ctx.take (ctx.length - start)).filter (fun p => !p.1.startsWith "_")
  let names := fresh.map Prod.fst |>.eraseDups
  names.filterMap fun k => (fresh.lookup k).map fun v => (k, exportValue ctx v)

/-- The `loop` variable of iteration `i` over `items` (upstream
`LoopContext`): position, length, neighbours, recursion depth. -/
def loopValue (items : List Value) (i depth0 : Nat) (recur : Option LoopRec) (cell : Nat) : Value :=
  .loop i items.length depth0 (if i = 0 then none else items[i - 1]?) items[i + 1]? recur cell

/-- Each item with its `loop` value, in one pass: the same values as
`loopValue items i ..` for each index (`loopValues_eq`), without indexing
the list once per iteration. -/
def loopValues (items : List Value) (depth0 : Nat) (recur : Option LoopRec) (cell : Nat) :
    List (Value × Value) :=
  let len := items.length
  let rec go : Option Value → Nat → List Value → List (Value × Value)
    | _, _, [] => []
    | prev, i, x :: xs => (x, .loop i len depth0 prev xs.head? recur cell) :: go (some x) (i + 1) xs
  go none 0 items

/-! ## Builtin functions -/

/-- The most items a `range` may produce (upstream `jinja2.sandbox.MAX_RANGE`):
the renderer is sandboxed, so `range` is upstream's `safe_range`. -/
def maxRange : Nat := 100000

/-- `range(stop)`, `range(start, stop[, step])`, refusing more than
`maxRange` items (upstream `safe_range`). -/
def rangeFn (args : List Value) : Except ValueError Value := do
  let is ← args.mapM (fun a => intArg a "range argument")
  let (a, b, c) ← match is with
    | [b] => pure (0, b, 1)
    | [a, b] => pure (a, b, 1)
    | [a, b, c] => pure (a, b, c)
    | _ => typeErr s!"range expected at most 3 arguments, got {is.length}"
  if c == 0 then typeErr "range() arg 3 must not be zero" else
  let count : Nat :=
    if c > 0 then (if b > a then ((b - a + c - 1) / c).toNat else 0)
    else (if a > b then ((a - b + (-c) - 1) / (-c)).toNat else 0)
  if count > maxRange then
    .error (.overflow s!"Range too big. The sandbox blocks ranges larger than MAX_RANGE ({maxRange}).")
  else
  pure (.list ((Array.range count).map (fun (k : Nat) => Value.int (a + (k : Int) * c))))

/-- A mapping argument's entries (`dict(m)`, `namespace(m)`). -/
def mappingEntries (pol : UndefinedPolicy) (heap : Heap) : Value → Except ValueError (List (Value × Value))
  | .dict kvs => .ok kvs
  | v => do
    let xs ← iterOf pol heap v
    xs.mapM fun x => match x with
      | .tuple ⟨[k, y]⟩ | .list ⟨[k, y]⟩ | .namedTuple _ _ ⟨[k, y]⟩ => .ok (k, y)
      | _ => .error (.typeError "dictionary update sequence element has wrong length")

/-- One comparison of a chain. -/
def compareOp (pol : UndefinedPolicy) (heap : Heap) (op : CmpOp) (a b : Value) :
    Except ValueError Bool :=
  match op with
  | .eq | .ne =>
    match a, b with
    | .undef i, _ | _, .undef i =>
      if i.policy pol == .strict then failUndef i
      else .ok (if op == .eq then Value.pyEq a b else !Value.pyEq a b)
    | _, _ => .ok (if op == .eq then Value.pyEq a b else !Value.pyEq a b)
  | .in => containsV pol heap a b
  | .notin => do let r ← containsV pol heap a b; pure !r
  | _ =>
    match a, b with
    | .undef i, _ | _, .undef i => failUndef i
    | _, _ =>
      match Value.pyCmp a b with
      | .error m => .error (.typeError m)
      | .ok o => .ok (match op with
        | .lt => o == .lt | .lteq => o != .gt | .gt => o == .gt | _ => o != .lt)


mutual

/-- Evaluate an expression. -/
def evalE (env : Environment) : Nat → Frame → Expr → RenderM Value
  | 0, _, _ => throw .fuelExhausted
  | n + 1, fr, e =>
    let pol := env.undefined
    match e with
    | .const c => pure c.toValue
    | .name x =>
      match fr.lookup? x with
      | some v => pure v
      | none =>
        match x, fr.curBlock with
        | "super", some (b, i) =>
          if i + 1 < (fr.chain b).length then pure (.superRef b (i + 1))
          else pure (.undef (.hint s!"there is no parent block called '{b}'."))
        | _, _ => pure (.undef (.name x))
    | .tuple xs => do let vs ← xs.mapM (evalE env n fr); pure (.tuple vs.toArray)
    | .list xs => do let vs ← xs.mapM (evalE env n fr); pure (.list vs.toArray)
    | .dict ps => do
      let vs ← ps.mapM (fun p => do
        let k ← evalE env n fr p.1
        let v ← evalE env n fr p.2
        pure (k, v))
      pure (.dict vs)
    | .getattr (.name "self") a =>
      match fr.lookup? "self" with
      | none => pure (if (fr.chain a).isEmpty then .undef (.attr "jinja2.runtime.TemplateReference object" a)
          else .superRef a 0)
      | some v => do let h ← get; liftR (getattrV pol h v a)
    | .getattr x a => do
      let v ← evalE env n fr x
      let h ← get
      liftR (getattrV pol h v a)
    | .getitem x (.slice a b c) => do
      let v ← evalE env n fr x
      let a ← a.mapM (evalE env n fr)
      let b ← b.mapM (evalE env n fr)
      let c ← c.mapM (evalE env n fr)
      liftR (sliceV pol v a b c)
    | .getitem x i => do
      let v ← evalE env n fr x
      let k ← evalE env n fr i
      getitemM pol v k
    | .slice .. => throw (.typeError "a slice is only valid in a subscript")
    | .call f args kw => do
      let fv ← evalE env n fr f
      let av ← args.mapM (evalE env n fr)
      let kv ← kw.mapM (fun p => do let v ← evalE env n fr p.2; pure (p.1, v))
      let h ← get
      let (av, kv) ← liftR (spreadArgs pol h av kv)
      callV env n fr fv av kv
    | .filter x nm args kw => do
      let v ← evalE env n fr x
      let av ← args.mapM (evalE env n fr)
      let kv ← kw.mapM (fun p => do let v ← evalE env n fr p.2; pure (p.1, v))
      let h ← get
      let (av, kv) ← liftR (spreadArgs pol h av kv)
      applyFilterM env fr nm v av kv
    | .test x nm args kw => do
      let v ← evalE env n fr x
      let av ← args.mapM (evalE env n fr)
      let kv ← kw.mapM (fun p => do let v ← evalE env n fr p.2; pure (p.1, v))
      let h ← get
      let (av, kv) ← liftR (spreadArgs pol h av kv)
      let b ← liftR (applyTest (env.fctx fr h) nm v av kv)
      pure (.bool b)
    | .unop op x => do
      let v ← evalE env n fr x
      match op, v with
      | .not, _ => do let t ← liftR (truthyOf pol v); pure (.bool !t)
      | _, .undef i => liftR (failUndef i)
      | .neg, .int i => pure (.int (-i))
      | .neg, .bool b => pure (.int (if b then -1 else 0))
      | .neg, .float m s => pure (.float (-m) s)
      | .pos, .int _ | .pos, .float .. => pure v
      | .pos, .bool b => pure (.int (if b then 1 else 0))
      | .neg, _ => throw (.typeError s!"bad operand type for unary -: '{v.typeName}'")
      | .pos, _ => throw (.typeError s!"bad operand type for unary +: '{v.typeName}'")
    | .binop .and l r => do
      let lv ← evalE env n fr l
      let t ← liftR (truthyOf pol lv)
      if t then evalE env n fr r else pure lv
    | .binop .or l r => do
      let lv ← evalE env n fr l
      let t ← liftR (truthyOf pol lv)
      if t then pure lv else evalE env n fr r
    | .binop op l r => do
      let lv ← evalE env n fr l
      let rv ← evalE env n fr r
      match lv, rv with
      | .undef i, _ => liftR (failUndef i)
      | _, .undef i => liftR (failUndef i)
      | _, _ => liftR (arith op lv rv)
    | .compare x ops => do
      let lv ← evalE env n fr x
      let h ← get
      let r ← ops.foldlM (fun (st : Option Value) (p : CmpOp × Expr) => do
        match st with
        | none => pure none
        | some cur => do
          let rv ← evalE env n fr p.2
          let ok ← liftR (compareOp pol h p.1 cur rv)
          pure (if ok then some rv else none)) (some lv)
      pure (.bool r.isSome)
    | .concat xs => do
      let vs ← xs.mapM (evalE env n fr)
      if fr.autoescape && vs.any Value.hasHtml then do
        let ms ← liftR (vs.mapM (escapeOf pol))
        pure (.markup (Markup.joinMarkup Markup.empty ms))
      else do
        let ss ← liftR (vs.mapM (strOf pol))
        pure (.str (String.join ss))
    | .cond t b els => do
      let tv ← evalE env n fr t
      let ok ← liftR (truthyOf pol tv)
      if ok then evalE env n fr b
      else match els with
        | some x => evalE env n fr x
        | none => pure (.undef (.plain
            "the inline if-expression evaluated to false and no else section was defined."))

/-- Call a value. -/
def callV (env : Environment) : Nat → Frame → Value → List Value → List (String × Value) →
    RenderM Value
  | 0, _, _, _, _ => throw .fuelExhausted
  | n + 1, fr, f, args, kw => do
    let pol := env.undefined
    match f with
    | .macro nm ps body uc clo mctx => callMacro env n { fr with ctx := mctx.getD fr.ctx } nm ps body uc clo args kw
    | .native "range" => liftR (rangeFn args)
    | .native "dict" => do
      let h ← get
      let base ← match args with
        | [] => pure []
        | [m] => liftR (mappingEntries pol h m)
        | _ => throw (.typeError "dict expected at most 1 argument")
      pure (.dict (base ++ kw.map (fun p => (Value.str p.1, p.2))))
    | .native "namespace" => do
      let h ← get
      let base ← match args with
        | [] => pure []
        | [m] => liftR (mappingEntries pol h m)
        | _ => throw (.typeError "namespace expected at most 1 argument")
      let attrs := (base.filterMap (fun p => match p.1 with
        | .str k => some (k, p.2) | _ => none)) ++ kw
      set (h ++ [attrs.reverse])
      pure (.ns h.length)
    | .native "cycler" =>
      match kw, args with
      | (k, _) :: _, _ => throw (.typeError s!"Cycler.__init__() got an unexpected keyword argument '{k}'")
      | [], [] => throw (.python "RuntimeError" "at least one item has to be provided")
      | [], _ => do
        let h ← get
        set (h ++ [[("items", .tuple args.toArray), ("pos", .int 0)]])
        pure (.cycler h.length)
    | .native "joiner" => do
      let sep ← match args, kw with
        | [], [] => pure (.str ", ")
        | [s], [] | [], [("sep", s)] => pure s
        | _, (k, _) :: _ =>
          if k == "sep" then throw (.typeError "Joiner.__init__() got multiple values for argument 'sep'")
          else throw (.typeError s!"Joiner.__init__() got an unexpected keyword argument '{k}'")
        | _, [] => throw (.typeError
            s!"Joiner.__init__() takes from 1 to 2 positional arguments but {args.length + 1} were given")
      let h ← get
      set (h ++ [[("sep", sep), ("used", .bool false)]])
      pure (.joiner h.length)
    | .native "lipsum" => do
      let h ← get
      let (v, s) ← liftR (lipsumCall pol (rngOf env.randomSeed h) args kw)
      set (setRng h s)
      pure v
    | .native nm =>
      match env.functions.lookup nm with
      | some g => liftR (liftNative (g (fr.locals ++ fr.ctx) args kw))
      | none => throw (.typeError s!"'{nm}' is not callable")
    | .method (.loop _ _ _ _ _ _ cell) "changed" => do
      let h ← get
      let cur := Value.tuple args.toArray
      let last := ((h[cell]?).getD []).lookup "last"
      match last with
      | some l => if Value.pyEq l cur then pure (.bool false) else do
          set (heapSet h cell "last" cur); pure (.bool true)
      | none => do set (heapSet h cell "last" cur); pure (.bool true)
    | .method (.cycler a) m => do
      if !(args.isEmpty && kw.isEmpty) then
        throw (.typeError s!"Cycler.{m}() takes 1 positional argument but {args.length + 1} were given")
      let h ← get
      let cell := (h[a]?).getD []
      match m, cell.lookup "items", cell.lookup "pos" with
      | "next", some (.tuple xs), some (.int p) => do
        set (heapSet h a "pos" (.int ((p + 1) % xs.size)))
        pure (xs[p.toNat]?.getD .none)
      | "reset", _, _ => do set (heapSet h a "pos" (.int 0)); pure .none
      | _, _, _ => throw (.typeError s!"'Cycler' object has no attribute '{m}'")
    | .joiner a => do
      if !(args.isEmpty && kw.isEmpty) then
        throw (.typeError s!"Joiner.__call__() takes 1 positional argument but {args.length + 1} were given")
      let h ← get
      let cell := (h[a]?).getD []
      match cell.lookup "used" with
      | some (.bool true) => pure ((cell.lookup "sep").getD (.str ""))
      | _ => do set (heapSet h a "used" (.bool true)); pure (.str "")
    | .method recv nm => do
      let h ← get
      liftR (callMethod (env.fctx fr h) recv nm args kw)
    | .loop _ _ d _ _ (some rec) _ => do
      let items ← match args with
        | [x] => do let h ← get; liftR (iterOf pol h x)
        | _ => throw (.typeError "loop() takes exactly one argument")
      let ps ← renderLoop env n fr rec true items (d + 1)
      let s ← liftR (Piece.flatten pol ps)
      pure (wrapText fr.autoescape s)
    | .superRef b i => do
      let ps ← renderBlockAt env n fr b i (if i = 0 then [] else fr.locals)
      let s ← liftR (Piece.flatten pol ps)
      pure (wrapText fr.autoescape s)
    | .undef i => liftR (failUndef i)
    | v => throw (.typeError s!"'{v.typeName}' object is not callable")

/-- Call a macro (upstream `Macro.__call__`): positional arguments fill the
parameters in order, then keywords, then defaults; `caller`, `varargs` and
`kwargs` are bound when the body mentions them. -/
def callMacro (env : Environment) : Nat → Frame → String → List Param → List Node → Bool →
    List (String × Value) → List Value → List (String × Value) → RenderM Value
  | 0, _, _, _, _, _, _, _, _ => throw .fuelExhausted
  | n + 1, fr, nm, ps, body, usesCaller, clo, args, kw => do
    let pol := env.undefined
    let base : Frame := { fr with locals := clo, top := false, curBlock := none }
    -- the values passed for each parameter (positionally, then by keyword)
    let passed : List (String × Option Value) := (ps.zipIdx).map (fun (p : Param × Nat) =>
      (p.1.1, match args[p.2]? with | some v => some v | none => kw.lookup p.1.1))
    let kwLeft := kw.filter (fun k => !((ps.drop args.length).map Prod.fst).contains k.1)
    let missing := fun (pn : String) => Value.undef (.hint s!"parameter '{pn}' was not provided")
    let init : List (String × Value) := passed.map (fun p => (p.1, p.2.getD (missing p.1)))
    -- defaults, in order, each seeing the parameters as bound so far
    let bound ← (ps.zip passed).foldlM (fun (cur : List (String × Value)) (q : Param × (String × Option Value)) => do
      match q.2.2, q.1.2 with
      | none, some e => do
        let v ← evalE env n { base with locals := cur ++ clo } e
        pure (cur.map (fun p => if p.1 == q.1.1 then (p.1, v) else p))
      | _, _ => pure cur) init
    let declared := ps.map Prod.fst
    let (bound, kwLeft) :=
      if usesCaller && !declared.contains "caller" then
        ((("caller", (kwLeft.lookup "caller").getD (.undef (.hint "No caller defined"))) :: bound),
          kwLeft.filter (·.1 != "caller"))
      else (bound, kwLeft)
    let extra := args.drop ps.length
    let bound ←
      if mentionsName "kwargs" body then
        pure (("kwargs", .dict (kwLeft.map (fun p => (.str p.1, p.2)))) :: bound)
      else match kwLeft with
        | [] => pure bound
        | (k, _) :: _ =>
          if k == "caller" then
            throw (.typeError s!"macro '{nm}' was invoked with two values for the special caller argument. This is most likely a bug.")
          else throw (.typeError s!"macro '{nm}' takes no keyword argument '{k}'")
    let bound ←
      if mentionsName "varargs" body then pure (("varargs", .tuple extra.toArray) :: bound)
      else if extra.isEmpty then pure bound
      else throw (.typeError s!"macro '{nm}' takes not more than {ps.length} argument(s)")
    let (pieces, _) ← renderNodes env n { base with locals := bound ++ clo } body
    let s ← liftR (Piece.flatten pol pieces)
    pure (wrapText fr.autoescape s)

/-- Render a node list, threading the frame. After `{% extends %}` has run at
top level, further output is discarded. Each node's pieces are kept as one
chunk, newest first, and joined once at the end, so a long list renders in
linear time. -/
def renderNodes (env : Environment) : Nat → Frame → List Node → RenderM (List Piece × Frame)
  | 0, _, _ => throw .fuelExhausted
  | n + 1, fr, nodes => do
    let (chunks, fr') ← nodes.foldlM (fun (st : List (List Piece) × Frame) (node : Node) => do
      let (acc, fr) := st
      let (ps, fr') ← renderNode env n fr node
      pure (if fr.top && fr.parent.isSome then acc else ps :: acc, fr')) ([], fr)
    pure (chunks.reverse.flatten, fr')

/-- Render one node. -/
def renderNode (env : Environment) : Nat → Frame → Node → RenderM (List Piece × Frame)
  | 0, _, _ => throw .fuelExhausted
  | n + 1, fr, node => do
    let pol := env.undefined
    match node with
    | .text s => pure ([.lit s], fr)
    | .output e => do
      let v ← evalE env n fr e
      pure ([.value v fr.autoescape], fr)
    | .if_ branches els => do
      let chosen ← branches.findM? (fun b => do
        let v ← evalE env n fr b.1
        liftR (truthyOf pol v))
      renderNodes env n fr ((chosen.map Prod.snd).getD els)
    | .for_ target iter filt recursive body els => do
      let v ← evalE env n fr iter
      let h ← get
      let items ← liftR (iterOf pol h v)
      let ps ← renderLoop env n fr ⟨target, filt, body, els⟩ recursive items 0
      pure (ps, fr)
    | .set target e => do
      let v ← evalE env n fr e
      let fr' ← assignTo env n fr target v
      pure ([], fr')
    | .setBlock target fs body => do
      let (ps, _) ← renderNodes env n { fr with top := false } body
      let s ← liftR (Piece.flatten pol ps)
      let v ← applyChain env n fr fs (wrapText fr.autoescape s)
      let fr' ← assignTo env n fr target v
      pure ([], fr')
    | .macro nm ps body => do
      let fr' ← assignTo env n fr (.name nm) (.macro nm ps body (mentionsName "caller" body) fr.locals none)
      pure ([], fr')
    | .callBlock ps c body =>
      match c with
      | .call f args kw => do
        let fv ← evalE env n fr f
        let av ← args.mapM (evalE env n fr)
        let kv ← kw.mapM (fun p => do let v ← evalE env n fr p.2; pure (p.1, v))
        let h ← get
        let (av, kv) ← liftR (spreadArgs pol h av kv)
        let caller := Value.macro "caller" ps body (mentionsName "caller" body) fr.locals (some fr.ctx)
        let r ← callV env n fr fv av (kv ++ [("caller", caller)])
        pure ([.value r fr.autoescape], fr)
      | _ => throw (.assertion "expected call")
    | .include e ignoreMissing withContext => do
      let v ← evalE env n fr e
      let h ← get
      let names ← liftR (includeNames pol h v)
      match names.findSome? (fun nm => (env.getSource nm).toOption.map (nm, ·)) with
      | none =>
        if ignoreMissing then pure ([], fr)
        else match names with
          | [nm] => throw (.notFound nm)
          | _ => throw (.notFound s!"none of the templates given were found: {names}")
      | some (nm, src) => do
        let body ← liftE (env.compile src)
        let base : Frame :=
          { ctx := if withContext then fr.locals ++ fr.ctx else env.startContext [] }
        let (ps, _) ← renderTemplate env n base (some nm) body
        pure (ps, fr)
    | .import_ e _ wc | .fromImport e _ wc => do
      let v ← evalE env n fr e
      let nm ← liftR (strOf pol v)
      let src ← liftE (env.getSource nm)
      let body ← liftE (env.compile src)
      let base : Frame := { ctx := if wc then fr.locals ++ fr.ctx else env.startContext [] }
      let (ps, ctx') ← renderTemplate env n base (some nm) body
      let out ← liftR (Piece.flatten pol ps)
      let exports := moduleExports base.ctx.length ctx'
      match node with
      | .fromImport _ names _ => do
        let fr' ← names.foldlM (fun (f : Frame) (p : String × Option String) =>
          assignTo env n f (.name (p.2.getD p.1)) ((exports.lookup p.1).getD (.undef (.hint
            s!"the template {pyStrRepr nm} does not export the requested name {pyStrRepr p.1}")))) fr
        pure ([], fr')
      | _ => do
        let target := match node with | .import_ _ t _ => t | _ => ""
        let fr' ← assignTo env n fr (.name target) (.module nm exports out)
        pure ([], fr')
    | .extends e => do
      if fr.parent.isSome then throw (.runtime "extended multiple times") else
      let v ← evalE env n fr e
      let nm ← liftR (strOf pol v)
      pure ([], { fr with parent := some nm })
    | .block nm sc req body =>
      if fr.top && fr.parent.isSome then pure ([], fr)
      else if ((fr.overrides.lookup nm).getD []).isEmpty then
        if req then throw (.runtime s!"Required block '{nm}' not found.") else do
        let (ps, _) ← renderNodes env n
          { fr with locals := if sc then fr.locals else [], top := false, curBlock := some (nm, 0) } body
        pure (ps, fr)
      else do
        let ps ← renderBlockAt env n fr nm 0 (if sc then fr.locals else [])
        pure (ps, fr)
    | .with_ assigns body => do
      let binds ← assigns.mapM (fun a => do
        let v ← evalE env n fr a.2
        let h ← get
        liftR (bindTarget pol h a.1 v))
      let (ps, _) ← renderNodes env n { fr with locals := binds.flatten ++ fr.locals, top := false } body
      pure (ps, fr)
    | .filterBlock fs body => do
      let (ps, _) ← renderNodes env n { fr with top := false } body
      let s ← liftR (Piece.flatten pol ps)
      let v ← applyChain env n fr fs (wrapText fr.autoescape s)
      pure ([.value v fr.autoescape], fr)
    | .autoescape e body => do
      let v ← evalE env n fr e
      let b ← liftR (truthyOf pol v)
      let (ps, _) ← renderNodes env n { fr with autoescape := b, top := false } body
      pure (ps, fr)

/-- Apply a filter chain (`{% filter %}` and `{% set %}` blocks). -/
def applyChain (env : Environment) : Nat → Frame → List FilterCall → Value → RenderM Value
  | 0, _, _, _ => throw .fuelExhausted
  | n + 1, fr, fs, v =>
    fs.foldlM (fun (acc : Value) (f : FilterCall) => do
      let av ← f.args.mapM (evalE env n fr)
      let kv ← f.kwargs.mapM (fun p => do let v ← evalE env n fr p.2; pure (p.1, v))
      let h ← get
      let (av, kv) ← liftR (spreadArgs env.undefined h av kv)
      applyFilterM env fr f.name acc av kv) v

/-- Assign to a target (`{% set %}`, `{% macro %}`): at top level the
template context, otherwise the locals; `ns.attr` writes the namespace. -/
def assignTo (env : Environment) : Nat → Frame → Target → Value → RenderM Frame
  | 0, _, _, _ => throw .fuelExhausted
  | n + 1, fr, target, v => do
    match target with
    | .nsAttr ns a =>
      match fr.lookup? ns with
      | some (.ns addr) => do
        modify (fun h => heapSet h addr a v)
        pure fr
      | _ => throw (.runtime "cannot assign attribute on non-namespace object")
    | .name x =>
      if fr.top then pure { fr with ctx := (x, v) :: fr.ctx }
      else pure { fr with locals := (x, v) :: fr.locals }
    | .tuple ts => do
      let h ← get
      let xs ← liftR (iterOf env.undefined h v)
      if xs.length < ts.length then
        throw (.typeError s!"not enough values to unpack (expected {ts.length}, got {xs.length})")
      else if xs.length > ts.length then
        throw (.typeError s!"too many values to unpack (expected {ts.length})")
      else (ts.zip xs).foldlM (fun (f : Frame) (p : Target × Value) => assignTo env n f p.1 p.2) fr

/-- Render a `for` loop over its items (the filter applied first); the body
sees the loop variables and `loop`. -/
def renderLoop (env : Environment) : Nat → Frame → LoopRec → Bool → List Value → Nat →
    RenderM (List Piece)
  | 0, _, _, _, _, _ => throw .fuelExhausted
  | n + 1, fr, rec, recursive, items, depth0 => do
    let pol := env.undefined
    let inner : Frame := { fr with top := false }
    let items ← loopItems env n inner rec items
    if items.isEmpty then do
      let (ps, _) ← renderNodes env n inner rec.else_
      pure ps
    else
      let cell := (← get).length
      modify (· ++ [[]])
      let chunks ← (loopValues items depth0 (if recursive then some rec else none) cell).foldlM
          (fun (acc : List (List Piece)) (p : Value × Value) => do
        let (x, loopV) := p
        let h ← get
        let binds ← liftR (bindTarget pol h rec.target x)
        let (ps, _) ← renderNodes env n { inner with locals := binds ++ ("loop", loopV) :: fr.locals }
          rec.body
        pure (ps :: acc)) []
      pure chunks.reverse.flatten

/-- The items a loop iterates: those its `if` filter keeps, the filter seeing
each item bound to the loop target. -/
def loopItems (env : Environment) : Nat → Frame → LoopRec → List Value → RenderM (List Value)
  | 0, _, _, _ => throw .fuelExhausted
  | n + 1, fr, rec, items =>
    match rec.filter with
    | none => pure items
    | some f => items.filterM (fun x => do
      let h ← get
      let binds ← liftR (bindTarget env.undefined h rec.target x)
      let v ← evalE env n { fr with locals := binds ++ fr.locals } f
      liftR (truthyOf env.undefined v))

/-- Render entry `i` of a block chain with the given locals (the caller's when
the block tag is `scoped`, and for `super()`). -/
def renderBlockAt (env : Environment) : Nat → Frame → String → Nat → List (String × Value) →
    RenderM (List Piece)
  | 0, _, _, _, _ => throw .fuelExhausted
  | n + 1, fr, b, i, locals =>
    match (fr.chain b)[i]? with
    | none => throw (.undefined s!"there is no parent block called '{b}'.")
    | some be =>
      if be.required then throw (.runtime s!"Required block '{b}' not found.") else do
      let (ps, _) ← renderNodes env n
        { fr with locals := locals, top := false,
                  curBlock := some (b, i), autoescape := be.autoescape } be.body
      pure ps

/-- Render a template from its top level (upstream `root_render_func`):
its blocks join the chains, and when it extends a parent, the parent renders
next with this template's context and blocks. -/
def renderTemplate (env : Environment) : Nat → Frame → Option String → List Node →
    RenderM (List Piece × List (String × Value))
  | 0, _, _, _ => throw .fuelExhausted
  | n + 1, base, name, body => do
    let ae := env.autoescape.enabledFor name
    let own := (blockDefs body).map (fun (b, _, req, bb) => (b, BlockEntry.mk bb ae req))
    let fr : Frame :=
      { base with own := own, top := true, parent := none, name := name, autoescape := ae, curBlock := none, locals := [] }
    let (ps, fr') ← renderNodes env n fr body
    match fr'.parent with
    | none => pure (ps, fr'.ctx)
    | some pn => do
      let src ← liftE (env.getSource pn)
      let pbody ← liftE (env.compile src)
      let (pps, ctx') ← renderTemplate env n
        { base with ctx := fr'.ctx, overrides := mergeOverrides base.overrides own } (some pn) pbody
      pure (ps ++ pps, ctx')

end

end LeanJinja2
