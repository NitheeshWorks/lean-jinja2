import LeanJinja2.DataTypes.Ast

/-!
# Nesting depth

How deeply a template nests: tags inside tags, expressions inside
expressions, and tuple targets inside tuple targets, each level counting one.
`Environment.compile` refuses a template too deep for the renderer's budget
(upstream raises `RecursionError` or Python's "too many levels of
indentation" on deep templates), and `render_total` is stated in terms of
`nodesDepth`.

The functions recurse structurally through the AST's nested lists, so each
equation holds by `rfl`.
-/

namespace LeanJinja2

mutual

/-- The nesting depth of an expression (a leaf is 1). -/
def Expr.depth : Expr → Nat
  | .const _ | .name _ => 1
  | .tuple xs | .list xs | .concat xs => exprsDepth xs + 1
  | .dict ps => pairsDepth ps + 1
  | .getattr x _ => x.depth + 1
  | .getitem x i => max x.depth i.depth + 1
  | .slice a b c => max (optDepth a) (max (optDepth b) (optDepth c)) + 1
  | .call f args kw | .filter f _ args kw | .test f _ args kw =>
    max f.depth (max (exprsDepth args) (kwDepth kw)) + 1
  | .unop _ x => x.depth + 1
  | .binop _ l r => max l.depth r.depth + 1
  | .compare x ops => max x.depth (opsDepth ops) + 1
  | .cond a b c => max a.depth (max b.depth (optDepth c)) + 1

/-- The deepest of a list of expressions (0 when empty). -/
def exprsDepth : List Expr → Nat
  | [] => 0
  | x :: xs => max x.depth (exprsDepth xs)

def pairsDepth : List (Expr × Expr) → Nat
  | [] => 0
  | (a, b) :: ps => max (max a.depth b.depth) (pairsDepth ps)

def kwDepth : List (String × Expr) → Nat
  | [] => 0
  | (_, x) :: ps => max x.depth (kwDepth ps)

def opsDepth : List (CmpOp × Expr) → Nat
  | [] => 0
  | (_, x) :: ps => max x.depth (opsDepth ps)

def optDepth : Option Expr → Nat
  | none => 0
  | some x => x.depth

end

mutual

/-- The nesting depth of an assignment target. -/
def Target.depth : Target → Nat
  | .name _ | .nsAttr _ _ => 1
  | .tuple ts => targetsDepth ts + 1

def targetsDepth : List Target → Nat
  | [] => 0
  | t :: ts => max t.depth (targetsDepth ts)

end

/-- The deepest expression of a filter chain. -/
def chainDepth : List FilterCall → Nat
  | [] => 0
  | f :: fs => max (max (exprsDepth f.args) (kwDepth f.kwargs)) (chainDepth fs)

/-- The deepest default of a parameter list. -/
def paramsDepth : List Param → Nat
  | [] => 0
  | (_, d) :: ps => max (optDepth d) (paramsDepth ps)

/-- The deepest assignment of a `with`. -/
def assignsDepth : List (Target × Expr) → Nat
  | [] => 0
  | (t, e) :: ps => max (max t.depth e.depth) (assignsDepth ps)

mutual

/-- The nesting depth of a node: one more than the deepest expression,
target or body node in it. -/
def Node.depth : Node → Nat
  | .text _ => 1
  | .output e => e.depth + 1
  | .if_ bs els => max (branchesDepth bs) (nodesDepth els) + 1
  | .for_ t it f _ body els =>
    max (max t.depth (max it.depth (optDepth f))) (max (nodesDepth body) (nodesDepth els)) + 1
  | .set t e => max t.depth e.depth + 1
  | .setBlock t fs body => max (max t.depth (chainDepth fs)) (nodesDepth body) + 1
  | .macro _ ps body => max (paramsDepth ps) (nodesDepth body) + 1
  | .callBlock ps c body => max (max (paramsDepth ps) c.depth) (nodesDepth body) + 1
  | .include e _ _ | .extends e => e.depth + 1
  | .block _ _ _ body => nodesDepth body + 1
  | .with_ as body => max (assignsDepth as) (nodesDepth body) + 1
  | .filterBlock fs body => max (chainDepth fs) (nodesDepth body) + 1
  | .autoescape e body => max e.depth (nodesDepth body) + 1

/-- The deepest node of a list (0 when empty). -/
def nodesDepth : List Node → Nat
  | [] => 0
  | n :: ns => max n.depth (nodesDepth ns)

def branchesDepth : List (Expr × List Node) → Nat
  | [] => 0
  | (e, b) :: bs => max (max e.depth (nodesDepth b)) (branchesDepth bs)

end

end LeanJinja2
