import LeanJinja2.DataTypes.Ast
import LeanMarkupsafe

/-!
# Runtime values

`Value` is the closed universe a template computes over, standing in for the
Python objects upstream renders. Numbers are exact: `int` is `Int`, `float`
is a decimal `m / 10^s` (upstream uses binary floats; see the deviation rows
in `docs/traceability.toml`). Callables are data, never Lean closures, so
`Value` stays a plain inductive:

* `macro` carries the macro's parameters, body and the variables it closed
  over; calling it renders the body.
* `native` names a function in the environment's table (`range`, `dict`,
  `namespace`, Starlette's `url_for`, user globals).
* `method` is a bound method of a builtin type (`d.items`, `s.upper`).
* `loop` is the loop object of a `for` (index, length, neighbours).
* `superRef` is `super()` inside a block.
* `ns` is a `namespace()` object, a reference into the renderer's heap.
-/

namespace LeanJinja2

open LeanMarkupsafe

/-- The data a recursive loop needs to render its body again (`loop(xs)`). -/
structure LoopRec where
  target : Target
  filter : Option Expr
  body : List Node
  else_ : List Node
  deriving Inhabited

/-- What an undefined value knows about how it came to be (upstream
`Undefined(hint, obj, name)`); used for the error message. -/
inductive UndefInfo where
  /-- A name that is not defined: `'x' is undefined`. -/
  | name (n : String)
  /-- A missing attribute or item of an object: `'dict object' has no attribute 'x'`. -/
  | attr (objType : String) (n : String)
  /-- A free-form hint, e.g. `there is no next item`. -/
  | hint (h : String)
  /-- The value of `a if c` when `c` is false: always upstream's plain
  `Undefined`, whatever the environment's policy (upstream
  `cond_expr_undefined = Undefined`). -/
  | plain (h : String)
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Runtime values. -/
inductive Value where
  | none
  | undef (info : UndefInfo)
  | bool (b : Bool)
  | int (i : Int)
  /-- `m / 10^s`. -/
  | float (m : Int) (s : Nat)
  | str (s : String)
  | markup (m : Markup)
  | list (items : List Value)
  | tuple (items : List Value)
  /-- An insertion-ordered mapping. -/
  | dict (items : List (Value × Value))
  /-- A macro: name, parameters, body, whether it uses `caller`, the
  variables it closed over, and the template context it was exported with
  (`none` while it is used in the template that defines it, which then
  supplies its context; an imported macro keeps its module's). -/
  | macro (name : String) (params : List Param) (body : List Node) (usesCaller : Bool)
      (closure : List (String × Value)) (context : Option (List (String × Value)))
  /-- A function provided by the environment, by name. -/
  | native (name : String)
  /-- A bound method of a builtin value. -/
  | method (recv : Value) (name : String)
  /-- The `loop` variable of a `for` loop; `cell` is the heap cell `loop.changed` uses. -/
  | loop (index0 length depth0 : Nat) (prev next : Option Value) (recur : Option LoopRec)
      (cell : Nat)
  /-- `super()` of block `name`, rendering entry `depth` of the block chain. -/
  | superRef (name : String) (depth : Nat)
  /-- A `namespace()` object, by heap address. -/
  | ns (addr : Nat)
  /-- An imported template (upstream `TemplateModule`): its name, the names it
  exports (top-level macros and `set`s) and its rendered output. -/
  | module (name : String) (exports : List (String × Value)) (output : String)
  deriving Inhabited

/-- A function the host provides (a global, a custom filter or test): it
receives the template's variables, the positional and the keyword arguments.
A filter receives the filtered value as its first positional argument. -/
abbrev NativeFn := List (String × Value) → List Value → List (String × Value) → Except String Value

/-- How undefined values behave (upstream `Undefined` subclasses). -/
inductive UndefinedPolicy where
  /-- `Undefined`: prints as empty, iterates as empty, is false; anything else fails. -/
  | default
  /-- `StrictUndefined`: only `is defined` and `default` may touch it. -/
  | strict
  /-- `ChainableUndefined`: attribute and item access return undefined again. -/
  | chainable
  /-- `DebugUndefined`: prints as `{{ name }}`. -/
  | debug
  deriving DecidableEq, Repr, Inhabited, BEq

/-- When output is HTML-escaped (upstream `autoescape=` and
`select_autoescape`). -/
inductive AutoescapePolicy where
  /-- Always on, or always off. -/
  | const (on : Bool)
  /-- `select_autoescape(enabled_extensions, disabled_extensions,
  default_for_string, default)`: decided by the template name's extension. -/
  | select (enabled disabled : List String) (defaultForString default : Bool)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Upstream `select_autoescape()` with its defaults. -/
def AutoescapePolicy.selectDefault : AutoescapePolicy :=
  .select ["html", "htm", "xml"] [] true false

/-- Errors the value operations raise: filters, tests, methods, attribute and
item access, arithmetic. There is no constructor for running out of the depth
budget, because these operations take none, so a `RecursionError` can only
come from the renderer's own recursion (see `render_total`). -/
inductive ValueError where
  /-- `UndefinedError`. -/
  | undefined (msg : String)
  /-- `TypeError`/`ValueError`/`ZeroDivisionError`... raised by an operation. -/
  | typeError (msg : String)
  /-- `OverflowError` (the sandbox's `MAX_RANGE`). -/
  | overflow (msg : String)
  /-- `TemplateAssertionError`. -/
  | assertion (msg : String)
  /-- `TemplateRuntimeError`, `FilterArgumentError`. -/
  | runtime (msg : String)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Errors raised while rendering (upstream exception classes). -/
inductive RenderError where
  /-- `UndefinedError`. -/
  | undefined (msg : String)
  /-- `TypeError`/`ValueError`/`ZeroDivisionError`... raised by an operation. -/
  | typeError (msg : String)
  /-- `OverflowError` (the sandbox's `MAX_RANGE`). -/
  | overflow (msg : String)
  /-- `TemplateNotFound`. -/
  | notFound (name : String)
  /-- `TemplateSyntaxError`, from a template loaded during rendering. -/
  | syntax (msg : String) (line : Nat)
  /-- `TemplateAssertionError`: unknown filter, bad structure. -/
  | assertion (msg : String)
  /-- `TemplateRuntimeError`: required block not overridden, unknown test, ... -/
  | runtime (msg : String)
  /-- The recursion-depth bound was reached (upstream `RecursionError`). -/
  | fuelExhausted
  deriving DecidableEq, Repr, Inhabited, BEq

instance : ToString RenderError where
  toString
    | .undefined m => s!"UndefinedError: {m}"
    | .typeError m => s!"TypeError: {m}"
    | .overflow m => s!"OverflowError: {m}"
    | .notFound n => s!"TemplateNotFound: {n}"
    | .syntax m l => s!"TemplateSyntaxError: {m} (line {l})"
    | .assertion m => s!"TemplateAssertionError: {m}"
    | .runtime m => s!"TemplateRuntimeError: {m}"
    | .fuelExhausted => "RecursionError: maximum recursion depth exceeded"

/-- A value error as a render error (same exception class). -/
def ValueError.toRenderError : ValueError → RenderError
  | .undefined m => .undefined m
  | .typeError m => .typeError m
  | .overflow m => .overflow m
  | .assertion m => .assertion m
  | .runtime m => .runtime m

instance : Coe ValueError RenderError := ⟨ValueError.toRenderError⟩

instance : ToString ValueError := ⟨fun e => toString e.toRenderError⟩

end LeanJinja2
