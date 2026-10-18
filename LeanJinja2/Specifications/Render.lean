import LeanJinja2.RepoImpl.Template

/-!
# What rendering guarantees

The renderer's output is the flattening of a trace of pieces (literal text and
interpolated values). The specifications here say where literal text comes
from, and what the output is when autoescaping is on.
-/

namespace LeanJinja2

open LeanMarkupsafe

/-! ## Facts about a template body -/

/-- What a node contributes to the facts `autoescape_sound` needs: its
literal text, and whether it is an `{% autoescape %}` tag. -/
inductive Fact where
  | text (s : String)
  | autoescapeTag
  deriving DecidableEq

/-- The facts of one node (not of its children). -/
def Node.fact : Node → List Fact
  | .text s => [.text s]
  | .autoescape .. => [.autoescapeTag]
  | _ => []

/-- The facts of a body, at every depth. -/
def factsOf (body : List Node) : List Fact := nodesCollect (fun _ => []) Node.fact body

/-- The literal text of a body: its text nodes, at every depth. -/
def textsOf (body : List Node) : List String :=
  (factsOf body).filterMap fun | .text s => some s | _ => none

/-- `s` is literal template text: a text node of `root`, or of a template
the environment's loader holds. -/
def Literal (env : Environment) (root : List Node) (s : String) : Prop :=
  s ∈ textsOf root ∨
    ∃ name src body, env.getSource name = .ok src ∧ env.compile src = .ok body ∧ s ∈ textsOf body

/-- Autoescaping is on throughout: the environment escapes every template,
and neither the template nor any template its loader holds contains an
`{% autoescape %}` tag that could switch it off. -/
def AutoescapeAlways (env : Environment) (root : List Node) : Prop :=
  env.autoescape = .const true ∧ Fact.autoescapeTag ∉ factsOf root ∧
    ∀ name src body, env.getSource name = .ok src → env.compile src = .ok body →
      Fact.autoescapeTag ∉ factsOf body

/-! ## The escaped reading of a trace -/

/-- How a value prints, under the undefined policy (total: a strict undefined
value, which `str` rejects, displays as empty). -/
def Value.display (pol : UndefinedPolicy) (v : Value) : String :=
  match strOf pol v with
  | .ok s => s
  | .error _ => ""

/-- The text a piece contributes when autoescaping: literal text as is; a
markup value as its own text; any other value as the escape of its text. -/
def Piece.escaped (pol : UndefinedPolicy) : Piece → String
  | .lit s => s
  | .value (.markup m) _ => m.str
  | .value v _ => (escape (v.display pol)).str

/-- An interpolated piece whose value is not markup. -/
def Piece.IsPlainValue : Piece → Prop
  | .value (.markup _) _ => False
  | .value _ _ => True
  | .lit _ => False

namespace Spec

/-- `render_literals`: every literal piece of a rendered trace is literal
template text, of the template or of one its loader holds. -/
def renderLiterals : Prop :=
  ∀ (t : Template) (vars : List (String × Value)) (ps : List Piece) (s : String),
    t.renderTrace vars = .ok ps → Piece.lit s ∈ ps → Literal t.env t.body s

/-- `autoescape_sound`: with autoescaping on throughout, the output is the
trace's literal text with each interpolated value replaced by its escape
(markup values unchanged). -/
def autoescapeSound : Prop :=
  ∀ (t : Template) (vars : List (String × Value)) (out : String),
    AutoescapeAlways t.env t.body → t.render vars = .ok out →
      ∃ ps, t.renderTrace vars = .ok ps ∧ out = String.join (ps.map (Piece.escaped t.env.undefined))

/-- `autoescape_escaped`: under autoescaping, what an interpolated non-markup
value contributes is escaped text (composing lean-markupsafe's
`escape_sound`). -/
def autoescapeEscaped : Prop :=
  ∀ (pol : UndefinedPolicy) (p : Piece), p.IsPlainValue → IsEscaped (p.escaped pol)

/-- `markup_passthrough`: an interpolated markup value contributes its own
text, whether or not autoescaping is on. -/
def markupPassthrough : Prop :=
  ∀ (pol : UndefinedPolicy) (m : Markup) (esc : Bool), Piece.text pol (.value (.markup m) esc) = .ok m.str

end Spec

end LeanJinja2
