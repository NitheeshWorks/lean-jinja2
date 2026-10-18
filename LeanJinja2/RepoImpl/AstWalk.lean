import LeanJinja2.DataTypes.Ast

/-!
# Walking the AST

A generic pre-order collector over expressions and nodes, and the facts the
compiler and renderer need from it: the names a macro body mentions
(`caller`, `varargs`, `kwargs`, upstream's `find_undeclared`), the filters a
template uses (checked at load time, upstream `TemplateAssertionError`), and
the blocks it defines.
-/

namespace LeanJinja2

theorem sizeOf_fst_lt_of_mem {α β : Type} [SizeOf α] [SizeOf β] {p : α × β} {l : List (α × β)}
    (h : p ∈ l) : sizeOf p.1 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h
  cases p; simp at *; omega

theorem sizeOf_snd_lt_of_mem {α β : Type} [SizeOf α] [SizeOf β] {p : α × β} {l : List (α × β)}
    (h : p ∈ l) : sizeOf p.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h
  cases p; simp at *; omega

/-- Decreasing proofs for recursion through the AST's nested lists. -/
macro "ast_decr" : tactic =>
  `(tactic| (simp_wf; first
    | omega
    | (have := sizeOf_fst_lt_of_mem ‹_›; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_›; omega)
    | (have := List.sizeOf_lt_of_mem ‹_›; omega)
    | (have := sizeOf_fst_lt_of_mem ‹_›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_›; simp_all; omega)))

/-- Collect `f e'` over every subexpression `e'` of `e`, pre-order. -/
def Expr.collect {α : Type} (f : Expr → List α) (e : Expr) : List α :=
  f e ++ match e with
  | .const _ | .name _ => []
  | .tuple xs | .list xs | .concat xs => xs.attach.flatMap (fun ⟨x, _⟩ => Expr.collect f x)
  | .dict ps => ps.attach.flatMap (fun ⟨p, _⟩ => Expr.collect f p.1 ++ Expr.collect f p.2)
  | .getattr x _ => Expr.collect f x
  | .getitem x i => Expr.collect f x ++ Expr.collect f i
  | .slice a b c =>
    (match a with | some x => Expr.collect f x | none => []) ++
    (match b with | some x => Expr.collect f x | none => []) ++
    (match c with | some x => Expr.collect f x | none => [])
  | .call g args kw | .filter g _ args kw | .test g _ args kw =>
    Expr.collect f g ++ args.attach.flatMap (fun ⟨x, _⟩ => Expr.collect f x) ++
      kw.attach.flatMap (fun ⟨p, _⟩ => Expr.collect f p.2)
  | .unop _ x => Expr.collect f x
  | .binop _ l r => Expr.collect f l ++ Expr.collect f r
  | .compare x ops => Expr.collect f x ++ ops.attach.flatMap (fun ⟨p, _⟩ => Expr.collect f p.2)
  | .cond a b c => Expr.collect f a ++ Expr.collect f b ++
    (match c with | some x => Expr.collect f x | none => [])
termination_by sizeOf e
decreasing_by all_goals ast_decr

/-- The expressions of a filter chain. -/
def FilterCall.exprs (fc : FilterCall) : List Expr := fc.args ++ fc.kwargs.map Prod.snd

/-- The expressions directly in a target (none; targets hold names). -/
def paramExprs (ps : List Param) : List Expr := ps.filterMap Prod.snd

/-- Collect over every node (pre-order), with `g` applied to each node and
`f` to every expression in it. -/
def Node.collect {α : Type} (f : Expr → List α) (g : Node → List α) (n : Node) : List α :=
  let ex := fun (e : Expr) => Expr.collect f e
  g n ++ match n with
  | .text _ => []
  | .output e => ex e
  | .if_ branches els =>
    branches.attach.flatMap (fun ⟨b, hb⟩ =>
      have : sizeOf b.2 < sizeOf branches := sizeOf_snd_lt_of_mem hb
      ex b.1 ++ b.2.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x)) ++
    els.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x)
  | .for_ _ iter filt _ body els =>
    ex iter ++ (match filt with | some e => ex e | none => []) ++
    body.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x) ++
    els.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x)
  | .set _ e => ex e
  | .setBlock _ fs body =>
    fs.flatMap (fun fc => fc.exprs.flatMap ex) ++ body.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x)
  | .macro _ ps body =>
    (paramExprs ps).flatMap ex ++ body.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x)
  | .callBlock ps c body =>
    (paramExprs ps).flatMap ex ++ ex c ++ body.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x)
  | .include e _ _ => ex e
  | .extends e => ex e
  | .block _ _ _ body => body.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x)
  | .with_ assigns body =>
    assigns.flatMap (fun a => ex a.2) ++ body.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x)
  | .filterBlock fs body =>
    fs.flatMap (fun fc => fc.exprs.flatMap ex) ++ body.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x)
  | .autoescape e body => ex e ++ body.attach.flatMap (fun ⟨x, _⟩ => Node.collect f g x)
termination_by sizeOf n
decreasing_by all_goals (simp_wf; first
  | omega
  | (have := List.sizeOf_lt_of_mem ‹_›; omega)
  | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))

/-- Collect over a node list. -/
def nodesCollect {α : Type} (f : Expr → List α) (g : Node → List α) (ns : List Node) : List α :=
  ns.flatMap (Node.collect f g)

/-- Whether a name occurs in a node list (upstream `find_undeclared`,
without shadowing analysis). -/
def mentionsName (n : String) (ns : List Node) : Bool :=
  (nodesCollect (fun e => match e with | .name x => if x == n then [()] else [] | _ => [])
    (fun _ => []) ns).length > 0

/-- The filter names used in a template. -/
def filterNames (ns : List Node) : List String :=
  nodesCollect (fun e => match e with | .filter _ nm _ _ => [nm] | _ => [])
    (fun nd => match nd with
      | .setBlock _ fs _ | .filterBlock fs _ => fs.map FilterCall.name
      | _ => []) ns

/-- The blocks a template defines, at any depth: name, scoped, required,
body. -/
def blockDefs (ns : List Node) : List (String × Bool × Bool × List Node) :=
  nodesCollect (fun _ => []) (fun nd => match nd with
    | .block nm sc req body => [(nm, sc, req, body)]
    | _ => []) ns

end LeanJinja2
