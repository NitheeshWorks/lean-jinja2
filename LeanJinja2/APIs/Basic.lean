import LeanJinja2.Proofs

/-!
# APIs

The public surface is upstream's: `Environment`, `Environment.getTemplate`,
`Environment.fromString`, `Template.render` (in `RepoImpl/Template.lean`), and
`FileSystemLoader` (in `Loader.lean`). Here are the refined variants whose
results carry their guarantees.
-/

namespace LeanJinja2

namespace API

/-- Tokenize; the tokens print back to the source. -/
def lex (cfg : LexConfig) (s : String) : Except LexError {ts : List Token // Token.print ts = s} :=
  match h : LeanJinja2.lex cfg s with
  | .ok ts => .ok ⟨ts, lex_print_roundtrip cfg s ts h⟩
  | .error e => .error e

/-- Print a well-formed template in canonical form; the parser reads it back. -/
def pretty (t : List Node) (h : WellFormed t) : {s : String // parse {} s = .ok t} :=
  ⟨LeanJinja2.pretty t, parse_pretty_roundtrip t h⟩

/-- Render a template; when autoescaping is on throughout, the output is the
trace's literal text with every interpolated value escaped. -/
def render (t : Template) (vars : List (String × Value) := []) :
    Except TemplateError {out : String // AutoescapeAlways t.env t.body →
      ∃ ps, t.renderTrace vars = .ok ps ∧ out = String.join (ps.map (Piece.escaped t.env.undefined))} :=
  match h : t.render vars with
  | .ok out => .ok ⟨out, fun hae => autoescape_sound t vars out hae h⟩
  | .error e => .error e

end API

end LeanJinja2
