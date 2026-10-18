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
* **`_ext` lemmas.** A decoder lemma holds on any continuation of the buffer and
  reports the final position, so field lemmas compose. Do not add a lemma that
  only holds at the end of a buffer; it is unusable one field later.
* **Numbers.** `Nat`/`Int`/decimal-as-rational in proofs. `Float` only at the
  boundary via `Float.toBits`. Never `bv_decide` or `native_decide`.
* **The gate.** `scripts/check.sh` runs what CI runs: build, `sorry` grep,
  `scripts/Axioms.lean` (every theorem under `LeanJinja2` reaches only `propext`,
  `Quot.sound`, `Classical.choice`), `lake exe props`, `lake exe conformance`,
  the traceability check.

### Tested, not proved

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`.

* **`render_total`**: rendering terminates, and the default `maxDepth` is
  enough for any template without runaway recursion. Termination holds by
  construction, since there is no `partial`. Proving that the budget suffices
  would need a fuel argument for each of the 52 builtin filters. Instead,
  `tests/Props.lean` (`renderTotal`) renders generated templates with nested
  `if`, `for`, `with`, filter blocks and autoescape blocks, and checks that
  none returns `fuelExhausted`. `Proofs/Verified.lean` has no slot for it.
* **`sort`, `unique`, `trim`, `wordcount`, `center`** are covered by property
  tests and by the upstream cases in `tests/Conformance.lean`. The properties
  are: a sorted permutation, first occurrences in order, no surrounding
  whitespace, the word count, and the text centred in the width. The other
  filters without an equation in `Proofs/Filters.lean` are covered by
  conformance cases only.
* **`parse_pretty_roundtrip`** is proved. `printParse` in `tests/Props.lean`
  is an executable cross-check of the same statement on generated templates.

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
