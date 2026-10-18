# Contributing to lean-jinja2

`README.md` covers usage. This file covers the architecture, the verification
rules, the repository layout and the conventions, and is the document to keep
current when the code changes.

## Architecture

`LeanJinja2/` is layered bottom-up; each layer imports only the ones below it, so a
proof at one layer rewrites with lemmas from beneath it instead of unfolding
to bytes:

| Directory | Holds | Proved? |
|---|---|---|
| `DataTypes/` | structures and inductives; invariants are fields | n/a |
| `RepoImpl/` | executable definitions; total, structural recursion | subject of proofs |
| `Specifications/` | the properties, in `Prop` | the contract |
| `Proofs/` | theorems; `Proofs/Verified.lean` bundles one `Verified<Layer>` per layer | yes |
| `APIs/` | the public surface, returning refinements | by construction |
| `Loader.lean` | the only effectful module: `FileSystemLoader` reads a search path into the pure `Loader` | no; tested |

Everything except `Loader.lean` is a pure function: a file system loader
reads its directory once, up front, and the environment holds the result. This is
load-bearing: a round-trip property of a function is an equation that
`omega` and `simp` attack directly; the same property of a procedure would
be a Hoare triple over a heap.

## Verification <a name="verification"></a>

* **Weak preconditions, strong postconditions.** A public function takes the
  minimal hypothesis its body needs (usually none; the refinement lives in the
  input type) and returns the strongest useful statement, typically a round
  trip or a membership, as `{r // Post r}` or `Except Err {r // Post r}`.
* **Refinement types are subtypes with `Decidable` predicates**, so the same
  predicate is checked at runtime (`if h : P x`) and used in proofs.
* **Totality.** No `partial def` or `unsafe` under `LeanJinja2/`. The lexer
  recurses on the remaining input. The parser takes fuel `parse.fuelFor ts =
  40 * (ts.length + 2)`, and `Proofs/Parser/` shows that this is always enough
  for the canonical print of a well-formed template, because fuel is monotone
  (`Reads`) and a node of size `n` needs at most `40 n + 40`. The renderer
  takes `Environment.maxDepth` (default 1000) as its recursion budget.
  `Environment.compile` refuses a template whose nesting needs more
  (`renderBudget body = 3 * nodesDepth body + 2`) with `RecursionError`, and
  `render_total` shows that a template that passes, and does not recurse
  through macros, `include`, `extends`, `super()` or `loop()`, never runs out.
* **Errors by layer.** The value layer (filters, tests, methods, attribute
  access, arithmetic) returns `ValueError`, which has no `RecursionError`
  constructor, so no filter can exhaust the budget and `render_total` needs
  no argument per filter. Only the renderer (`RenderError`) has
  `fuelExhausted`.
* **Linear time on hostile input.** The lexer loop is tail recursive and
  tracks the position from each step's tokens. Node lists and loops collect
  their output as chunks and join them once, and loop values are computed in
  one pass (`loopValues_eq` ties them to `loopValue`). `range` is
  upstream's sandboxed `safe_range` (`MAX_RANGE = 100000`). `lake exe bench`
  bounds the time at `10^4` and `10^5` nesting; complexity is tested, not
  stated in Lean.
* **Two lexers, one proved equal to the other.** `RepoImpl/Lexer.lean` is
  the specification: a state machine over `List Char`, which the round-trip
  proofs are about. A list costs 24 bytes a character, so the compiler and
  `parse` run `lexFast` (`RepoImpl/LexFast.lean`) instead: the same machine
  over `String.Slice` positions (`RepoImpl/Cursor.lean`), template data and
  string literals built straight into a `String`, tokens kept as kind and
  length (`TokL`). Each of its helpers mirrors the specification helper of
  the same name, and `lexFast_eq` proves
  `lexFast cfg s = (lex cfg s).map (·.map Token.light)`; `parse_eq` restates
  `parse` through `lex`. A helper that reads a bounded prefix matches on
  `l.take k` in the specification, so its twin reads only `k` characters.
  To add a lexer feature, change both and extend the step proofs in
  `Proofs/LexFast.lean`.
* **Constant stack.** Every loop over input or output is tail recursive.
  The specification's non-tail `normalizeNewlines` and `unescapeStr` run
  through proved `@[csimp]` replacements (`normalizeNewlines_eq_TR`,
  `unescapeStr_eq_TR`), so even `lex` does not overflow on long data.
  lean-markupsafe's `escape` works on a `List Char` (non-tail
  `escapeList`); `RepoImpl/Escape.lean` replaces it, for the code this
  package compiles, by the one-pass `escapeFast` (`escape_eq_fast`,
  `@[csimp]`), so the proofs about `escape` stand as they are.
* **`_ext` lemmas.** A decoder lemma holds on any continuation of the buffer and
  reports the final position, so field lemmas compose. Do not add a lemma that
  only holds at the end of a buffer; it is unusable one field later.
* **Numbers.** `Nat`/`Int`/decimal-as-rational in proofs. `Float` only at the
  boundary via `Float.toBits`. Never `bv_decide` or `native_decide`.
* **The gate.** `scripts/check.sh` runs what CI runs: build, `sorry` grep,
  `scripts/Axioms.lean` (every theorem under `LeanJinja2` reaches only `propext`,
  `Quot.sound`, `Classical.choice`), `lake exe props`, `lake exe conformance`,
  `lake exe bench`, the traceability check. Run heavy commands through
  `stack-tools/capped` (see the workspace AGENT-BRIEF).

### Tested, not proved

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`.

* **Time and memory bounds** (`tests/Bench.lean`): linear lexing, parsing
  and rendering on deeply nested and long templates, the `range` cap, and
  10 MB / 20 MB of plain text, `{{ x }}` with a 20 MB value (plain and
  autoescaped) and a 10 MB string literal within 2 s and 300 MB of peak
  resident memory.
* **`sort`, `unique`, `trim`, `wordcount`, `center`** are covered by property
  tests and by the upstream cases in `tests/Conformance.lean`. The properties
  are: a sorted permutation, first occurrences in order, no surrounding
  whitespace, the word count, and the text centred in the width. The other
  filters without an equation in `Proofs/Filters.lean` are covered by
  conformance cases only.
* **`parse_pretty_roundtrip`** and **`render_total`** are proved.
  `printParse` and `renderTotal` in `tests/Props.lean` are executable
  cross-checks of the same statements on generated templates.

### Deviations from upstream

Each one has a `docs/traceability.toml` row (`deviation` or `excluded`).

* **Numbers.** Float literals are exact decimals (rationals), not binary
  doubles. Arithmetic on them is exact, so a printed result can differ from
  Python's in the last digits.
* **Not implemented:** `import` and `from ... import`, macro `*varargs` and
  `**kwargs`, line statements and line comments, the globals `cycler`,
  `joiner` and `lipsum`, and the `random` and `urlize` filters.
* **Autoescape** is `.const b` or `selectAutoescape ...` (the
  `AutoescapePolicy` data type), not an arbitrary callable.
* **Unicode.** Case mapping (`upper`, `lower`, `title`, `capitalize`) covers
  ASCII and Latin-1. Identifiers approximate Python's `str.isidentifier`: they
  accept alphanumerics, `_`, and non-ASCII characters outside the whitespace
  and symbol ranges. String literals reject `\N{...}` escapes.
* **Unknown escapes** (UP-047). `'\q'` and `'\é'` both keep the backslash.
  Upstream keeps it before an ASCII character but turns `'\é'` into the text
  `\xe9`.
* **Deep templates.** `compile` raises `RecursionError` for nesting beyond
  `(maxDepth - 2) / 3` levels (332 by default). Upstream fails on deep
  templates too, but at limits set by Python: past about 100 nested blocks
  ("too many levels of indentation") or 69 nested parentheses.
* **Sandboxed `range`.** As upstream's `SandboxedEnvironment`, `range` refuses
  more than 100000 items with `OverflowError`.
* **`title` on markup** (UP-048) follows upstream: the result is a plain
  string, so it is escaped again under autoescape.

## Tests

* `tests/Props.lean`: seeded property tests, no dependencies, under a second.
* `tests/Conformance.lean`: cases re-expressed from the upstream suite; each
  names the upstream test (`tests/test_x.py::test_y`).
* `tests/pbt/`: a separate Lake package, the one place an external dependency
  (`plausible`) is taken.

## Traceability

`docs/traceability.toml` links upstream behaviour to the Lean symbol, theorem
and test that realise it. Add a row when behaviour is newly implemented,
tested-only, excluded, or deviates. CI fails if a registered symbol does not
resolve.

## Conventions

* Lean 4 `leanprover/lean4:v4.35.0`; no Mathlib; the core library depends only on Lean
  core and the sibling `lean-*` repos listed in `lakefile.toml`, pinned by
  commit in `lake-manifest.json`.
* Choose the definition that suits the automation over a prettier one with a
  harder proof.
* No upstream code is copied; the upstream test suite and docs are the spec.
