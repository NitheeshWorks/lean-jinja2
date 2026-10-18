import LeanJinja2

/-!
# Hostile-template bench: time and memory bounds

Templates an attacker controls must not cost more than linear time, nor more
than a small multiple of their size in memory. Each case below renders (or
compiles) a template, checks the outcome, and fails if it took longer than its
time bound or, where it has one, if the process's peak resident memory during
the case exceeded its memory bound (Linux `VmHWM`, reset before each case).

* plain text of 10 MB and 20 MB, and `{{ x }}` with a 20 MB string value,
  plain and autoescaped: linear and in place (before the in-place lexer, 6 MB
  took 3.5 s and 830 MB, and 24 MB overflowed the stack);
* a 10 MB string literal (escapes decoded in place, constant stack);
* with line statement and line comment prefixes set: 20 MB of plain text,
  10 MB of commented lines, a 10 MB run of blanks (scanned once, not once
  per position) and 2 MB of line statements;
* value operations on `10^5`-`10^6` items and a 10 MB string: slicing,
  `unique`, printing a list, the `slice` filter and string indexing;
* templates nested `10^4` and `10^5` deep (before the linear rewrite, `10^4`
  nested `if`s took 62 s), and a huge `range`.

The bounds are generous (a slow CI machine passes) but far below what a
quadratic or list-based implementation takes. Run with `lake exe bench`;
`scripts/check.sh` runs it. `lake exe bench probe <phase> <bytes>` times one
workload for profiling.
-/

open LeanJinja2

-- Inputs are built when their case runs, not when the program starts (a
-- hoisted 20 MB constant would count in every case's memory).
set_option compiler.extract_closed false

def repGo (s : String) : Nat → String → String
  | 0, acc => acc
  | k + 1, acc => repGo s k (acc ++ s)

/-- `k` copies of `s`, appended in place (no list of copies). -/
def rep (k : Nat) (s : String) : String := repGo s k ""

def nestedIf (k : Nat) : String := rep k "{% if true %}" ++ "x" ++ rep k "{% endif %}"
def unclosedIf (k : Nat) : String := rep k "{% if true %}" ++ "x"
def nestedFor (k : Nat) : String := rep k "{% for x in [1] %}" ++ "x" ++ rep k "{% endfor %}"
def nestedParens (k : Nat) : String := "{{ " ++ rep k "(" ++ "1" ++ rep k ")" ++ " }}"
def siblings (k : Nat) : String := rep k "{{ x }}{% if x %}y{% endif %}"

/-- One bench case: what to run, what the outcome must satisfy, the time
bound in milliseconds and the peak-memory bound in MB (0: none). -/
structure Bench where
  name : String
  run : Unit → Except TemplateError String
  ok : Except TemplateError String → Bool
  boundMs : Nat
  boundMB : Nat := 0

def line : String := "lorem ipsum dolor sit amet, consectetur adipiscing elit\n"

/-- About `n` bytes of plain text in lines. -/
def plain (n : Nat) : String := rep (n / line.length) line

def plainLen (n : Nat) : Nat := n / line.length * line.length

/-- A string literal of about `n` characters. -/
def strLit (n : Nat) : String := "{{ '" ++ rep (n / 56) "lorem ipsum dolor sit amet, consectetur adipiscing elit" ++ "' }}"

def render (src : String) (vars : List (String × Value) := []) : Unit → Except TemplateError String :=
  fun _ => ({} : Environment).fromString src >>= (·.render vars)

/-- Line statements `#` and line comments `##`. -/
def lineEnv : Environment := { lineStatementPrefix := some "#", lineCommentPrefix := some "##" }

def renderL (src : String) (vars : List (String × Value) := []) : Unit → Except TemplateError String :=
  fun _ => lineEnv.fromString src >>= (·.render vars)

def commentLine : String := "lorem ipsum dolor sit amet ## consectetur adipiscing\n"

/-- About `n` bytes of text whose lines end in line comments. -/
def commented (n : Nat) : String := rep (n / commentLine.length) commentLine

/-- About `n` bytes of line statements. -/
def lineStmts (n : Nat) : String := rep (n / 20) "# if true\nx\n# endif\n"

def isRecursion : Except TemplateError String → Bool
  | .error .fuelExhausted => true
  | _ => false

def isSyntax : Except TemplateError String → Bool
  | .error (.syntax ..) => true
  | _ => false

def isOverflow : Except TemplateError String → Bool
  | .error (.overflow _) => true
  | _ => false

def rendersLen (n : Nat) : Except TemplateError String → Bool
  | .ok s => s.length == n
  | _ => false

def sized (k bound : Nat) : List Bench := [
  { name := s!"{k} nested if", run := render (nestedIf k), ok := isRecursion, boundMs := bound },
  { name := s!"{k} nested for", run := render (nestedFor k), ok := isRecursion, boundMs := bound },
  { name := s!"{k} unclosed if", run := render (unclosedIf k), ok := isSyntax, boundMs := bound },
  { name := s!"{k} nested parentheses", run := render (nestedParens k), ok := rendersLen 1, boundMs := bound },
  { name := s!"{k} sibling tags", run := render (siblings k) [("x", 1)], ok := rendersLen (2 * k),
    boundMs := bound } ]

/-- Big inputs: time and memory linear in the size. These run first, while
the process is small. -/
def big : List Bench := [
  { name := "plain text 10 MB", run := render (plain 10000000), ok := rendersLen (plainLen 10000000 - 1),
    boundMs := 1000, boundMB := 200 },
  { name := "plain text 20 MB", run := render (plain 20000000), ok := rendersLen (plainLen 20000000 - 1),
    boundMs := 2000, boundMB := 300 },
  { name := "{{ x }}, x a 20 MB string", run := fun u => render "{{ x }}" [("x", .str (plain 20000000))] u,
    ok := rendersLen (plainLen 20000000), boundMs := 2000, boundMB := 300 },
  { name := "{{ x }} autoescaped, x a 20 MB string",
    run := fun _ => ({ autoescape := .const true } : Environment).fromString "{{ x }}" >>=
      (·.render [("x", .str (plain 20000000))]),
    ok := rendersLen (plainLen 20000000), boundMs := 2000, boundMB := 300 },
  { name := "string literal 10 MB", run := render (strLit 10000000),
    ok := rendersLen (10000000 / 56 * 55), boundMs := 2000, boundMB := 300 },
  { name := "plain text 20 MB, line prefixes set", run := renderL (plain 20000000),
    ok := rendersLen (plainLen 20000000 - 1), boundMs := 2000, boundMB := 300 },
  { name := "line comments 10 MB", run := renderL (commented 10000000),
    ok := rendersLen (10000000 / commentLine.length * 27 - 1), boundMs := 2000, boundMB := 300 },
  { name := "a 10 MB blank run, line prefixes set", run := renderL ("x" ++ rep 10000000 " " ++ "y"),
    ok := rendersLen 10000002, boundMs := 2000, boundMB := 300 },
  { name := "line statements 2 MB", run := renderL (lineStmts 2000000),
    ok := rendersLen (2000000 / 20 * 2), boundMs := 5000 } ]

/-- `0, 1, ..., n - 1` as a list value. -/
def intsV (n : Nat) (m : Nat := n) : Value := .list ((Array.range n).map (fun i => Value.int ((i % m : Nat) : Int)))

def rendersText (t : String) : Except TemplateError String → Bool
  | .ok s => s == t
  | _ => false

/-- Value operations on request-sized data: one pass each (slicing indexed a
list per item, `unique` scanned every key seen, `repr` of a list copied the
rest per item, the `slice` filter dropped from the start per slice, and
`s[i]` built a value per character). -/
def valueOps : List Bench := [
  { name := "x[1:] on 10^6 items", run := fun u => render "{{ x[1:]|length }}" [("x", intsV 1000000)] u,
    ok := rendersText "999999", boundMs := 500 },
  { name := "x[::-1] on 10^6 items", run := fun u => render "{{ x[::-1]|first }}" [("x", intsV 1000000)] u,
    ok := rendersText "999999", boundMs := 500 },
  { name := "x[::2] on 10^6 items", run := fun u => render "{{ x[::2]|length }}" [("x", intsV 1000000)] u,
    ok := rendersText "500000", boundMs := 500 },
  { name := "s[1:] on a 10 MB string", run := fun u => render "{{ s[1:]|length }}" [("s", .str (plain 10000000))] u,
    ok := rendersText (toString (plainLen 10000000 - 1)), boundMs := 500 },
  { name := "s[::-1] on a 10 MB string", run := fun u => render "{{ s[::-1]|length }}" [("s", .str (plain 10000000))] u,
    ok := rendersText (toString (plainLen 10000000)), boundMs := 500 },
  { name := "s[::2] on a 10 MB string", run := fun u => render "{{ s[::2]|length }}" [("s", .str (plain 10000000))] u,
    ok := rendersText (toString ((plainLen 10000000 + 1) / 2)), boundMs := 500 },
  { name := "unique of 10^5 ints", run := fun u => render "{{ x|unique|list|length }}" [("x", intsV 100000 50000)] u,
    ok := rendersText "50000", boundMs := 200 },
  { name := "{{ x }} of 10^6 ints", run := fun u => render "{{ x }}" [("x", intsV 1000000)] u,
    ok := fun r => match r with | .ok s => s.length == 7888890 | _ => false, boundMs := 1000 },
  { name := "x|pprint of 10^6 ints", run := fun u => render "{{ x|pprint|length }}" [("x", intsV 1000000)] u,
    ok := rendersText "7888890", boundMs := 1000 },
  { name := "x|slice(10^5) of 10^5 items", run := fun u => render "{{ x|slice(100000)|list|length }}" [("x", intsV 100000)] u,
    ok := rendersText "100000", boundMs := 500 },
  { name := "10^4 indexes into a 10^4-char string",
    run := fun u => render "{% for i in range(10000) %}{{ s[i] }}{% endfor %}" [("s", .str (rep 1000 "abcdefghij"))] u,
    ok := rendersLen 10000, boundMs := 1000 } ]

/-- The globals and filters of `5zga4vtt22ic`: linear in the input. -/
def globalOps : List Bench := [
  { name := "urlize of 1 MB of text with links",
    run := fun u => render "{{ s|urlize|length }}" [("s", .str (rep 20000 "see http://example.org/a?b=1 mail me@x.org, "))] u,
    ok := fun r => match r with | .ok _ => true | _ => false, boundMs := 500 },
  { name := "urlize of a 1 MB word",
    run := fun u => render "{{ s|urlize|length }}" [("s", .str (rep 100000 "www.ab.cd/"))] u,
    ok := fun r => match r with | .ok _ => true | _ => false, boundMs := 300 },
  { name := "urlize of 10^5 brackets around a link",
    run := fun u => render "{{ s|urlize|length }}" [("s", .str (rep 100000 "(" ++ "http://x.org" ++ rep 100000 ")"))] u,
    ok := fun r => match r with | .ok _ => true | _ => false, boundMs := 200 },
  { name := "lipsum(2000)", run := render "{{ lipsum(2000)|length > 0 }}", ok := rendersText "True",
    boundMs := 300 },
  { name := "10^5 cycler.next()",
    run := render "{% set c = cycler(1, 2, 3) %}{% for i in range(100000) %}{{ c.next() }}{% endfor %}",
    ok := rendersLen 100000, boundMs := 500 },
  { name := "10^5 joiner()",
    run := render "{% set j = joiner('') %}{% for i in range(100000) %}{{ j() }}.{% endfor %}",
    ok := rendersLen 100000, boundMs := 500 },
  { name := "10^5 |random", run := fun u =>
      render "{% for i in range(100000) %}{{ x|random }}{% endfor %}" [("x", intsV 10)] u,
    ok := rendersLen 100000, boundMs := 700 } ]

/-- `x[i]` in a loop over every position: constant time per index. -/
def indexOps : List Bench := [
  { name := "x[i] for every i of 10^5 items",
    run := fun u => render "{% for i in range(100000) %}{% if x[i] == i %}.{% endif %}{% endfor %}"
      [("x", intsV 100000)] u,
    ok := rendersLen 100000, boundMs := 300 },
  { name := "s[i] for every i of a 10^5-char string",
    run := fun u => render "{% for i in range(100000) %}{{ s[i] }}{% endfor %}"
      [("s", .str (rep 10000 "abcdefghij"))] u,
    ok := rendersLen 100000, boundMs := 300 },
  { name := "s[-i - 1] for every i of a 10^5-char non-ASCII string",
    run := fun u => render "{% for i in range(100000) %}{{ s[-i - 1] }}{% endfor %}"
      [("s", .str (rep 10000 "abcdéfghi€"))] u,
    ok := rendersLen 100000, boundMs := 300 } ]

def benches : List Bench :=
  big ++ valueOps ++ globalOps ++ indexOps ++ sized 10000 2000 ++ sized 100000 20000 ++ [
  { name := "range(100000000)", run := render "{{ range(100000000)|length }}", ok := isOverflow,
    boundMs := 100 },
  { name := "range(100000) loop", run := render "{% for i in range(100000) %}.{% endfor %}",
    ok := rendersLen 100000, boundMs := 5000 } ]

def resetPeak : IO Unit :=
  try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()

/-- Peak resident memory in MB since the last reset (Linux `VmHWM`). -/
def peakMB : IO (Option Nat) := do
  try
    let st ← IO.FS.readFile "/proc/self/status"
    let ln := (st.splitOn "\n").find? (·.startsWith "VmHWM:")
    pure <| ln.bind fun l => ((l.drop 6).trimAscii.copy.takeWhile Char.isDigit).copy.toNat?.map (· / 1024)
  catch _ => pure none

/-- `lake exe bench probe <phase> <bytes>`: one workload of about that size,
for profiling: `lex` (the specification lexer), `lexf` (the in-place one),
`parse`, `render` (plain text), `tags`, `blocks`, `strlit`, `comment`, `raw`,
`var`, `varesc`, `gen` (the input only), `dcomments`, and with line prefixes
`lineplain`, `linecomment`, `linestmt`. -/
def probe (phase : String) (n : Nat) : IO UInt32 := do
  let src := plain n
  let t0 ← IO.monoMsNow
  let r := match phase with
    | "lex" => match lex {} src with | .ok ts => s!"{ts.length} tokens" | .error e => e.msg
    | "parse" => match parse {} src with | .ok b => s!"{b.length} nodes" | .error e => e.msg
    | "lexf" => match lexFast {} src with | .ok ts => s!"{ts.length} tokens" | .error e => e.msg
    | "tags" => match render (rep (n / 8) "a{{ x }}") [("x", .str "b")] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "blocks" => match render (rep (n / 26) "a{% if x %}b{% endif %}") [("x", .bool true)] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "strlit" => match render (strLit n) [] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "comment" => match render ("{# " ++ src ++ " #}x") [] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "raw" => match render ("{% raw %}" ++ src ++ "{% endraw %}") [] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "var" => match render "{{ x }}" [("x", .str src)] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "gen" => s!"{src.length} chars"
    | "loop" => match render s!"\{% for i in range({n}) %}.\{% endfor %}" [] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "xi" => match render s!"\{% for i in range({n}) %}\{% if x[i] == i %}.\{% endif %}\{% endfor %}"
          [("x", intsV n)] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "si" => match render s!"\{% for i in range({n}) %}\{\{ s[i] }}\{% endfor %}"
          [("s", .str (rep (n / 10) "abcdefghij"))] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "linecomment" => match renderL (commented n) [] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "linestmt" => match renderL (lineStmts n) [] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "dcomments" => match render (rep (n / 50) "lorem ipsum dolor sit amet {# consectetur adi #}\n") [] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "lineplain" => match renderL src [] () with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | "varesc" => match (({ autoescape := .const true } : Environment).fromString "{{ x }}" >>=
          (·.render [("x", .str src)])) with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | _ => match render src [] () with | .ok s => s!"{s.length} chars" | .error e => toString e
  IO.println s!"{phase} {src.length} bytes: {r} in {(← IO.monoMsNow) - t0} ms, peak {(← peakMB).getD 0} MB"
  return 0

/-- Reset the peak resident memory (Linux; does nothing elsewhere). -/
def main (args : List String) : IO UInt32 := do
  if let "probe" :: "tpl" :: src :: _ := args then
    -- an ad-hoc template, with `x` 10^5 ints and `s` a 10^5-char string
    let t0 ← IO.monoMsNow
    let r := render src [("x", intsV 100000), ("s", .str (rep 10000 "abcdefghij"))] ()
    let what := match r with | .ok s => s!"{s.length} chars" | .error e => toString e
    IO.println s!"{what} in {(← IO.monoMsNow) - t0} ms"
    return 0
  if let "probe" :: phase :: n :: _ := args then
    return ← probe phase (n.toNat?.getD 1000000)
  let mut failures := 0
  for b in benches do
    resetPeak
    let t0 ← IO.monoMsNow
    let r := b.run ()
    let good := b.ok r
    let t1 ← IO.monoMsNow
    let ms := t1 - t0
    let mb ← peakMB
    let memOK := b.boundMB == 0 || (mb.map (decide <| · ≤ b.boundMB)).getD true
    let mem := if b.boundMB == 0 then "" else
      s!", {(mb.map toString).getD "?"} MB (bound {b.boundMB})"
    let what := match r with | .ok s => s!"ok, {s.length} chars" | .error e => toString e
    if good && ms ≤ b.boundMs && memOK then
      IO.println s!"ok    {b.name}: {ms} ms (bound {b.boundMs}){mem}  {what.take 60}"
    else
      failures := failures + 1
      IO.println s!"FAIL  {b.name}: {ms} ms (bound {b.boundMs}){mem}  {what.take 60}"
    (← IO.getStdout).flush
  IO.println s!"{benches.length} benches, {failures} failing"
  return if failures == 0 then 0 else 1
