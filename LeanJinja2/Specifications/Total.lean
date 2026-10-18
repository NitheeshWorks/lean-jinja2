import LeanJinja2.RepoImpl.Template

/-!
# When rendering cannot run out of depth

The renderer is total by construction, and running out of its depth budget
is upstream's `RecursionError`. In Jinja, unbounded recursion only comes from
calling back into template code: a macro (or `caller`), `super()` or
`self.block()`, a recursive `loop(...)`, `include` and `extends`. A template
that does none of that, here `nodesNonrec`, renders within a budget linear in
its nesting depth (`renderBudget`), and that is `render_total`.

`nodesNonrec` allows every tag except `include`, `extends`, `macro` and
`call`, and allows calls only to the builtin globals `range`, `dict` and
`namespace`, by name, which the template never rebinds. Filters, tests and
attribute access are unrestricted: the value layer has no way to raise
`RecursionError` (`ValueError` has no such constructor), so they need no
argument of their own.
-/

namespace LeanJinja2

/-- The globals a non-recursive template may call: builtins that compute a
value and never re-enter template code. -/
def callableGlobals : List String := ["range", "dict", "namespace"]

/-- Values whose call re-enters template code: macros, block references
(`super()`, `self.b`) and the loop object of a recursive loop. -/
def Value.reenters : Value → Bool
  | .macro .. | .superRef .. => true
  | .loop _ _ _ _ _ (some _) _ => true
  | _ => false

mutual

/-- An expression that calls only `callableGlobals`, by name. -/
def Expr.nonrec : Expr → Bool
  | .const _ | .name _ => true
  | .tuple xs | .list xs | .concat xs => exprsNonrec xs
  | .dict ps => pairsNonrec ps
  | .getattr x _ => x.nonrec
  | .getitem x i => x.nonrec && i.nonrec
  | .slice a b c => optNonrec a && optNonrec b && optNonrec c
  | .call f args kw =>
    (match f with | .name g => callableGlobals.contains g | _ => false) &&
      exprsNonrec args && kwNonrec kw
  | .filter f _ args kw | .test f _ args kw => f.nonrec && exprsNonrec args && kwNonrec kw
  | .unop _ x => x.nonrec
  | .binop _ l r => l.nonrec && r.nonrec
  | .compare x ops => x.nonrec && opsNonrec ops
  | .cond a b c => a.nonrec && b.nonrec && optNonrec c

def exprsNonrec : List Expr → Bool
  | [] => true
  | x :: xs => x.nonrec && exprsNonrec xs

def pairsNonrec : List (Expr × Expr) → Bool
  | [] => true
  | (a, b) :: ps => a.nonrec && b.nonrec && pairsNonrec ps

def kwNonrec : List (String × Expr) → Bool
  | [] => true
  | (_, x) :: ps => x.nonrec && kwNonrec ps

def opsNonrec : List (CmpOp × Expr) → Bool
  | [] => true
  | (_, x) :: ps => x.nonrec && opsNonrec ps

def optNonrec : Option Expr → Bool
  | none => true
  | some x => x.nonrec

end

mutual

/-- A target that does not rebind a callable global. -/
def Target.nonrec : Target → Bool
  | .name x => !callableGlobals.contains x
  | .nsAttr _ _ => true
  | .tuple ts => targetsNonrec ts

def targetsNonrec : List Target → Bool
  | [] => true
  | t :: ts => t.nonrec && targetsNonrec ts

end

def chainNonrec : List FilterCall → Bool
  | [] => true
  | f :: fs => exprsNonrec f.args && kwNonrec f.kwargs && chainNonrec fs

def assignsNonrec : List (Target × Expr) → Bool
  | [] => true
  | (t, e) :: ps => t.nonrec && e.nonrec && assignsNonrec ps

mutual

/-- A node that does not recurse: no `include`, `extends`, `macro` or
`call` tag, and non-recursive expressions and targets throughout. -/
def Node.nonrec : Node → Bool
  | .text _ => true
  | .output e => e.nonrec
  | .if_ bs els => branchesNonrec bs && nodesNonrec els
  | .for_ t it f _ body els =>
    t.nonrec && it.nonrec && optNonrec f && nodesNonrec body && nodesNonrec els
  | .set t e => t.nonrec && e.nonrec
  | .setBlock t fs body => t.nonrec && chainNonrec fs && nodesNonrec body
  | .macro .. | .callBlock .. | .include .. | .extends _ => false
  | .block _ _ _ body => nodesNonrec body
  | .with_ as body => assignsNonrec as && nodesNonrec body
  | .filterBlock fs body => chainNonrec fs && nodesNonrec body
  | .autoescape e body => e.nonrec && nodesNonrec body

def nodesNonrec : List Node → Bool
  | [] => true
  | n :: ns => n.nonrec && nodesNonrec ns

def branchesNonrec : List (Expr × List Node) → Bool
  | [] => true
  | (e, b) :: bs => e.nonrec && nodesNonrec b && branchesNonrec bs

end

namespace Spec

/-- `render_total`: a template that does not recurse, rendered with variables
that do not bind a callable global to template code, never raises
`RecursionError` when the depth budget covers its nesting. -/
def renderTotal : Prop :=
  ∀ (t : Template) (vars : List (String × Value)),
    nodesNonrec t.body = true →
    (∀ g ∈ callableGlobals, ∀ v, (g, v) ∈ vars ++ t.env.globals → v.reenters = false) →
    renderBudget t.body ≤ t.env.maxDepth →
    t.render vars ≠ .error .fuelExhausted

end Spec

end LeanJinja2
