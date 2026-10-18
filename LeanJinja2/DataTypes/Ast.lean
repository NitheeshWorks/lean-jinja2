/-!
# The template AST

Mirrors upstream `jinja2.nodes` for the supported language. Differences in
shape, not meaning:

* A template body is a flat `List Node`; upstream groups adjacent template
  data and `{{ }}` expressions into `Output` nodes, which carries no meaning.
* `if`/`elif`/`else` is one node with a list of `(test, body)` branches.
* A filter applied to an expression is `Expr.filter e f`; the filter chains of
  `{% filter %}` and `{% set x | f %}` blocks are `List FilterCall`.
* Constant literals are `Const`; a float literal is an exact decimal.
-/

namespace LeanJinja2

/-- A literal constant (upstream `nodes.Const`). -/
inductive Const where
  | none
  | bool (b : Bool)
  | int (n : Int)
  /-- `m / 10^s`. -/
  | float (m : Int) (s : Nat)
  | str (s : String)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Arithmetic and logic binary operators. -/
inductive BinOp where
  | add | sub | mul | div | floordiv | mod | pow | and | or
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Unary operators: `-x`, `+x`, `not x`. -/
inductive UnOp where
  | neg | pos | not
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Comparison operators of a `Compare` chain. -/
inductive CmpOp where
  | eq | ne | lt | lteq | gt | gteq | «in» | notin
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Expressions (upstream `nodes.Expr` subclasses). -/
inductive Expr where
  | const (c : Const)
  | name (n : String)
  | tuple (items : List Expr)
  | list (items : List Expr)
  | dict (items : List (Expr × Expr))
  | getattr (e : Expr) (attr : String)
  | getitem (e : Expr) (index : Expr)
  /-- `a:b:c` inside a subscript. -/
  | slice (start stop step : Option Expr)
  | call (f : Expr) (args : List Expr) (kwargs : List (String × Expr))
  /-- `e | name(args, kwargs)`. -/
  | filter (e : Expr) (name : String) (args : List Expr) (kwargs : List (String × Expr))
  | test (e : Expr) (name : String) (args : List Expr) (kwargs : List (String × Expr))
  | unop (op : UnOp) (e : Expr)
  | binop (op : BinOp) (l r : Expr)
  /-- `a < b <= c`: the first operand and the chain. -/
  | compare (e : Expr) (ops : List (CmpOp × Expr))
  /-- `a ~ b ~ c`. -/
  | concat (items : List Expr)
  /-- `body if test else else_`; a missing `else` is `none`. -/
  | cond (test body : Expr) (else_ : Option Expr)
  deriving Repr, Inhabited

/-- One filter application in a filter chain: name, positional and keyword
arguments. -/
structure FilterCall where
  name : String
  args : List Expr
  kwargs : List (String × Expr)
  deriving Repr, Inhabited

/-- Assignment targets: a name, a namespace attribute `ns.attr`, or a tuple of
targets (upstream `Name`/`NSRef`/`Tuple` in store context). -/
inductive Target where
  | name (n : String)
  | nsAttr (ns attr : String)
  | tuple (items : List Target)
  deriving Repr, Inhabited

/-- A macro or call-block parameter: name and optional default. -/
abbrev Param := String × Option Expr

/-- Template nodes (upstream `nodes.Stmt` subclasses and template data). -/
inductive Node where
  /-- Literal template text. -/
  | text (s : String)
  /-- `{{ e }}`. -/
  | output (e : Expr)
  /-- `{% if %}...{% elif %}...{% else %}...{% endif %}`. -/
  | if_ (branches : List (Expr × List Node)) (else_ : List Node)
  /-- `{% for target in iter if filter recursive %}body{% else %}else_{% endfor %}`. -/
  | for_ (target : Target) (iter : Expr) (filter : Option Expr) (recursive : Bool)
      (body : List Node) (else_ : List Node)
  /-- `{% set target = e %}`. -/
  | set (target : Target) (e : Expr)
  /-- `{% set target | filters %}body{% endset %}`. -/
  | setBlock (target : Target) (filters : List FilterCall) (body : List Node)
  /-- `{% macro name(params) %}body{% endmacro %}`. -/
  | macro (name : String) (params : List Param) (body : List Node)
  /-- `{% call(params) e %}body{% endcall %}`; `e` is a call expression. -/
  | callBlock (params : List Param) (call : Expr) (body : List Node)
  /-- `{% include e ignore missing with context %}`. -/
  | include (template : Expr) (ignoreMissing : Bool) (withContext : Bool)
  /-- `{% extends e %}`. -/
  | extends (template : Expr)
  /-- `{% block name scoped required %}body{% endblock %}`. -/
  | block (name : String) (isScoped : Bool) (required : Bool) (body : List Node)
  /-- `{% with t1 = e1, t2 = e2 %}body{% endwith %}`. -/
  | with_ (assigns : List (Target × Expr)) (body : List Node)
  /-- `{% filter f | g %}body{% endfilter %}`. -/
  | filterBlock (filters : List FilterCall) (body : List Node)
  /-- `{% autoescape e %}body{% endautoescape %}`. -/
  | autoescape (e : Expr) (body : List Node)
  deriving Repr, Inhabited

/-- A parsed template body. -/
abbrev Template := List Node

end LeanJinja2
