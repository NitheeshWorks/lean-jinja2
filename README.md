# lean-jinja2

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [Jinja2](https://github.com/pallets/jinja) to Lean 4: a template lexer, parser and total renderer with proved autoescape soundness.

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo with its proofs. This one
depends on: [lean-markupsafe](https://github.com/NitheeshWorks/lean-markupsafe).

## Quickstart

Upstream's first example, in Lean:

```lean
import LeanJinja2
open LeanJinja2

def main : IO Unit := do
  let env : Environment := { loader := ← FileSystemLoader "templates", autoescape := selectAutoescape }
  let template ← IO.ofExcept (env.getTemplate "mytemplate.html")
  IO.println (← IO.ofExcept (template.render [("the", "variables"), ("go", "here")]))
```

`FileSystemLoader` accepts a `String`, a `System.FilePath` or a list of
either, as upstream does. It is the only part that does IO. Everything after
it is a pure function returning `Except TemplateError`, so templates can be
evaluated directly:

```lean
def hello : Except TemplateError String := do
  let env : Environment :=
    { loader := DictLoader [("hello.html", "Hello {{ name }}!")], autoescape := selectAutoescape }
  (← env.getTemplate "hello.html").render [("name", "<World>")]

#eval hello   -- Except.ok "Hello &lt;World&gt;!"
```

`Environment.fromString` compiles a template from a string. The template
language is upstream's: `{{ }}`, `{% %}`, `{# #}`, filters and tests,
`for`/`if`/`set`/`with`/`macro`/`call`/`filter`/`autoescape`/`raw`,
`extends`/`block`/`include`, the whitespace controls `-` and `+`, and the
`Undefined`, `StrictUndefined`, `ChainableUndefined` and `DebugUndefined`
policies. The differences are listed in
[CONTRIBUTING.md](CONTRIBUTING.md#deviations-from-upstream).

## What is proved

All of these are machine-checked. `Proofs/Verified.lean` bundles them into
`theVerifiedSyntax`, `theVerifiedRender` and `theVerifiedSemantics`.

| Theorem | Statement |
|---|---|
| `lex_print_roundtrip` | `lex cfg s = .ok ts → Token.print ts = s`: lexing loses nothing, for every configuration |
| `parse_pretty_roundtrip` | `WellFormed t → parse {} (pretty t) = .ok t`: the canonical print parses back to the same tree |
| `lexFast_eq` | `lexFast cfg s = (lex cfg s).map (·.map Token.light)`: the in-place lexer the compiler runs (linear, constant stack, a few bytes a character) gives exactly `lex`'s tokens |
| `autoescape_sound` | with autoescaping on throughout, `t.render vars = .ok out` implies `out` is the trace's literal text with every interpolated value escaped (markup unchanged) |
| `autoescape_escaped` | each such escaped value satisfies lean-markupsafe's `IsEscaped` |
| `render_literals` | every literal piece of the output is text from the template or one its loader holds |
| `render_total` | a template without `include`, `extends`, `macro` or `call`, calling only `range`/`dict`/`namespace`, never raises `RecursionError` when `3 * nodesDepth body + 2 ≤ maxDepth`, which `compile` checks (`render_total_fromString`) |
| `markup_passthrough` | an interpolated `Markup` value contributes its own text, with or without autoescaping |
| `for_loop_vars` | in iteration `i`, `loop.index = i + 1`, `loop.first ↔ i = 0`, `loop.last ↔ i + 1 = length` (and `index0`, `revindex`, `depth`, `previtem`, `nextitem`) |
| `undefined_policy` | how an undefined name prints under each of the four policies |
| `extends_block_override` | a block renders the most-derived body in its `extends` chain, with that template's autoescape setting |
| `filter_upper`, `filter_lower`, `filter_length`, `filter_default_*`, `filter_escape*`, `filter_safe`, `filter_first`, `filter_last`, `filter_list`, `filter_reverse`, `filter_join` | the filters' defining equations |
| `filter_tojson_htmlsafe` | `tojson` returns markup with no raw `<`, `>`, `&` or `'` |

The refined entry points carry these results in their types:
`API.lex cfg s : Except LexError {ts // Token.print ts = s}`,
`API.pretty t h : {s // parse {} s = .ok t}`, and `API.render t vars`, whose
output comes with the `autoescape_sound` statement.

Tested rather than proved: the `sort`, `unique`, `trim`, `wordcount` and
`center` filters, and the time and memory bounds on hostile and large
templates (`lake exe bench`).
See [CONTRIBUTING.md](CONTRIBUTING.md#tested-not-proved).

## What "verified" means here

* Public functions take the weakest precondition they need and return the
  strongest postcondition, as a refinement type `{r // Post r}` or an
  `Except` of one. Invariants live in types, not comments.
* Every theorem is machine-checked. CI fails on `sorry` and on any axiom
  beyond Lean's own `propext`, `Quot.sound` and `Classical.choice`.
* What is tested rather than proved is listed, with the reason, in
  [CONTRIBUTING.md](CONTRIBUTING.md#verification) and in
  `docs/traceability.toml`.

## Getting started

```
lake build            # library, proofs, and both test executables
lake exe props        # property tests (seeded; `lake exe props 42`)
lake exe conformance  # cases re-expressed from the upstream test suite
lake exe bench        # time and memory bounds on hostile and large templates
scripts/check.sh      # the whole CI gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`; `elan` installs it).

## Status

Core slice complete: lexer, parser, renderer, 52 builtin filters, the
builtin tests, inheritance, macros, and the dictionary and file system
loaders, import and from-import, line statements and line comments.
`tests/Conformance.lean` re-expresses 512 cases from the upstream suite and
all of them pass. `tests/Props.lean` holds 8 seeded properties.

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
