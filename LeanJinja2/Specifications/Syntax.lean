import LeanJinja2.RepoImpl.Pretty

/-!
# Well-formed templates and the round-trip property

`WellFormed t` says `t` is in the parser's image as the canonical printer
prints it: names are identifiers other than the keywords the expression
grammar reserves, literals are non-negative (a minus sign is the `-`
operator), slices occur only as subscripts, comparison chains and `~`
concatenations have their operators, template text is non-empty, contains no
delimiter and no carriage return (the lexer normalises newlines), and two
text nodes are never adjacent (the parser merges them). The round-trip
theorem says the parser reads the printed template back exactly.
-/

namespace LeanJinja2

/-- Names the expression grammar treats as keywords or constants. -/
def reservedNames : List String :=
  ["and", "or", "not", "in", "is", "if", "else", "true", "false", "none", "True", "False", "None",
   "recursive"]

/-- An identifier the lexer reads as one name token. -/
def IsIdent (s : String) : Prop :=
  ∃ c cs, s.toList = c :: cs ∧ isIdentChar c = true ∧ c.isDigit = false ∧ c ≠ '\xb7' ∧
    ∀ d ∈ cs, isIdentChar d = true

/-- A name usable as a variable, attribute, filter, test or parameter. -/
def VarName (s : String) : Prop := IsIdent s ∧ s ∉ reservedNames

def Const.WF : Const → Prop
  | .int i => 0 ≤ i
  | .float m _ => 0 ≤ m
  | _ => True

mutual
def Expr.WF : Expr → Prop
  | .const c => c.WF
  | .name n => VarName n
  | .tuple xs | .list xs => Expr.WFs xs
  | .concat xs => 2 ≤ xs.length ∧ Expr.WFs xs
  | .dict ps => Expr.WFPairs ps
  | .getattr e a => e.WF ∧ VarName a
  | .getitem e i => e.WF ∧ Expr.SubWF i
  | .slice .. => False
  | .call f args kw => f.WF ∧ Expr.WFs args ∧ Expr.WFKw kw
  | .filter e n args kw | .test e n args kw => e.WF ∧ VarName n ∧ Expr.WFs args ∧ Expr.WFKw kw
  | .unop _ e => e.WF
  | .binop _ l r => l.WF ∧ r.WF
  | .compare e ops => e.WF ∧ ops ≠ [] ∧ Expr.WFCmps ops
  | .cond t b e => t.WF ∧ b.WF ∧ Expr.WFOpt e

/-- A subscript: a slice of well-formed bounds, or a well-formed expression. -/
def Expr.SubWF : Expr → Prop
  | .slice a b c => Expr.WFOpt a ∧ Expr.WFOpt b ∧ Expr.WFOpt c
  | e => e.WF

def Expr.WFs : List Expr → Prop
  | [] => True
  | x :: xs => x.WF ∧ Expr.WFs xs

def Expr.WFPairs : List (Expr × Expr) → Prop
  | [] => True
  | (k, v) :: ps => k.WF ∧ v.WF ∧ Expr.WFPairs ps

def Expr.WFKw : List (String × Expr) → Prop
  | [] => True
  | (k, v) :: kw => VarName k ∧ v.WF ∧ Expr.WFKw kw

def Expr.WFCmps : List (CmpOp × Expr) → Prop
  | [] => True
  | (_, e) :: ops => e.WF ∧ Expr.WFCmps ops

def Expr.WFOpt : Option Expr → Prop
  | none => True
  | some e => e.WF
end

/-- A target of `for` and `with`: names and tuples of them. -/
def Target.Plain : Target → Prop
  | .name n => VarName n
  | .nsAttr .. => False
  | .tuple ts => Plains ts
where
  Plains : List Target → Prop
    | [] => True
    | t :: ts => t.Plain ∧ Plains ts

/-- A target of `set`: also `ns.attr` at the top. -/
def Target.Settable : Target → Prop
  | .nsAttr n a => VarName n ∧ VarName a
  | t => t.Plain

def FilterCall.WF (f : FilterCall) : Prop := VarName f.name ∧ Expr.WFs f.args ∧ Expr.WFKw f.kwargs

/-- Parameters: names, defaults well-formed, no parameter without a default
after one with. -/
def ParamsWF : Bool → List Param → Prop
  | _, [] => True
  | hadDefault, (n, d) :: ps =>
    VarName n ∧ Expr.WFOpt d ∧ (hadDefault = true → d.isSome) ∧ ParamsWF (hadDefault || d.isSome) ps

/-- Template text the lexer reads back as one data token. -/
def TextOK (s : String) : Prop :=
  s.toList ≠ [] ∧ '\r' ∉ s.toList ∧
    ∀ i, s.toList[i]? = some '{' → ∃ c, s.toList[i + 1]? = some c ∧ c ≠ '{' ∧ c ≠ '%' ∧ c ≠ '#'

def Node.isText : Node → Bool
  | .text _ => true
  | _ => false

mutual
def Node.WF : Node → Prop
  | .text s => TextOK s
  | .output e => e.WF
  | .if_ bs els => bs ≠ [] ∧ Node.BranchesWF bs ∧ Node.BodyWF els
  | .for_ t it fl _ body els => t.Plain ∧ it.WF ∧ Expr.WFOpt fl ∧ Node.BodyWF body ∧ Node.BodyWF els
  | .set t e => t.Settable ∧ e.WF
  | .setBlock t fs body => t.Settable ∧ (∀ f ∈ fs, f.WF) ∧ Node.BodyWF body
  | .macro n ps body => VarName n ∧ ParamsWF false ps ∧ Node.BodyWF body
  | .callBlock ps c body =>
    ParamsWF false ps ∧ (∃ f args kw, c = .call f args kw) ∧ c.WF ∧ Node.BodyWF body
  | .include e _ _ => e.WF
  | .extends e => e.WF
  | .block n _ req body => VarName n ∧ Node.BodyWF body ∧ (req = true → Parse.onlyWhitespace body = true)
  | .with_ as body => Node.AssignsWF as ∧ Node.BodyWF body
  | .filterBlock fs body => fs ≠ [] ∧ (∀ f ∈ fs, f.WF) ∧ Node.BodyWF body
  | .autoescape e body => e.WF ∧ Node.BodyWF body

/-- A body: well-formed nodes, no two text nodes in a row. -/
def Node.BodyWF : List Node → Prop
  | [] => True
  | n :: ns => n.WF ∧ Node.BodyWF ns ∧ (n.isText = true → (ns.head?.map Node.isText) ≠ some true)

def Node.BranchesWF : List (Expr × List Node) → Prop
  | [] => True
  | (t, b) :: bs => t.WF ∧ Node.BodyWF b ∧ Node.BranchesWF bs

def Node.AssignsWF : List (Target × Expr) → Prop
  | [] => True
  | (t, e) :: as => t.Plain ∧ e.WF ∧ Node.AssignsWF as
end

/-- A template the canonical printer prints and the parser reads back. -/
def WellFormed (t : List Node) : Prop := Node.BodyWF t

namespace Spec

/-- `lex_print_roundtrip`: lexing loses nothing. -/
def lexPrintRoundtrip : Prop :=
  ∀ (cfg : LexConfig) (s : String) (ts : List Token), lex cfg s = .ok ts → Token.print ts = s

/-- `parse_pretty_roundtrip`: the parser reads a well-formed template's
canonical print back to the same template. -/
def parsePrettyRoundtrip : Prop := ∀ t : List Node, WellFormed t → parse {} (pretty t) = .ok t

/-- `lexFast_eq`: the lexer the compiler runs (in place over the source) is
the specification lexer `lex`, seen through `Token.light`: the same tokens'
kinds and lengths, or the same error. -/
def lexFastEq : Prop :=
  ∀ (cfg : LexConfig) (s : String), lexFast cfg s = (lex cfg s).map (·.map Token.light)

end Spec

end LeanJinja2
