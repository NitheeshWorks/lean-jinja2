import LeanJinja2.Proofs.Lexer
import LeanJinja2.Proofs.Roundtrip
import LeanJinja2.Proofs.Render
import LeanJinja2.Proofs.Semantics
import LeanJinja2.Proofs.Total
import LeanJinja2.Specifications

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` bundles a layer's implementation with a proof term for
every `Specifications/<Layer>.lean` property it claims. A specification with
no proof is a compile error the moment it needs a field here: you cannot
construct a `Verified<Layer>` value without every proof in hand. If a stated
specification turns out false, its slot's type flips to a refutation rather
than being dropped, so this file stays an honest map of what is verified.

`render_total` sits with the rendering properties: a template that does not
recurse cannot exhaust the depth budget that `Environment.compile` checks.
-/

namespace LeanJinja2

set_option linter.unusedSimpArgs false

/-- Lexing and parsing (`RepoImpl/Lexer.lean`, `RepoImpl/Parser.lean`, `RepoImpl/Pretty.lean`). -/
structure VerifiedSyntax where
  /-- `lex_print_roundtrip`. -/
  lexPrintRoundtrip : Spec.lexPrintRoundtrip
  /-- `parse_pretty_roundtrip`. -/
  parsePrettyRoundtrip : Spec.parsePrettyRoundtrip

theorem theVerifiedSyntax : VerifiedSyntax where
  lexPrintRoundtrip := lex_print_roundtrip
  parsePrettyRoundtrip := parse_pretty_roundtrip

/-- Rendering and autoescaping (`RepoImpl/Render.lean`, `RepoImpl/Template.lean`). -/
structure VerifiedRender where
  /-- `render_literals`. -/
  renderLiterals : Spec.renderLiterals
  /-- `autoescape_sound`. -/
  autoescapeSound : Spec.autoescapeSound
  /-- `autoescape_escaped`. -/
  autoescapeEscaped : Spec.autoescapeEscaped
  /-- `markup_passthrough`. -/
  markupPassthrough : Spec.markupPassthrough
  /-- `render_total`. -/
  renderTotal : Spec.renderTotal

theorem theVerifiedRender : VerifiedRender where
  renderLiterals := render_literals
  autoescapeSound := autoescape_sound
  autoescapeEscaped := autoescape_escaped
  markupPassthrough := markup_passthrough
  renderTotal := render_total

/-- Loop variables, undefined values, inheritance and filters. -/
structure VerifiedSemantics where
  /-- `for_loop_vars`. -/
  forLoopVars : Spec.forLoopVars
  /-- `undefined_policy`. -/
  undefinedPolicy : Spec.undefinedPolicy
  /-- `extends_block_override`. -/
  extendsBlockOverride : Spec.extendsBlockOverride
  /-- The builtin filters' equations (`filter_upper`, ...). -/
  filterLaws : Spec.filterLaws
  /-- `filter_tojson_htmlsafe`. -/
  tojsonHtmlsafe : Spec.tojsonHtmlsafe

theorem theVerifiedSemantics : VerifiedSemantics where
  forLoopVars := for_loop_vars
  undefinedPolicy := undefined_policy
  extendsBlockOverride := fun env n fr b sc body be rest s h1 h2 h3 =>
    extends_block_override env n fr b sc body be rest s h1 h2 h3
  filterLaws := fun fc => ⟨filter_upper fc, filter_lower fc, filter_length fc, filter_default_undefined fc,
    filter_default_defined fc, filter_escape fc, filter_escape_markup fc, filter_safe fc, filter_first fc,
    filter_last fc, filter_reverse fc⟩
  tojsonHtmlsafe := filter_tojson_htmlsafe

end LeanJinja2
