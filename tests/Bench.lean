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
* templates nested `10^4` and `10^5` deep (before the linear rewrite, `10^4`
  nested `if`s took 62 s), and a huge `range`.

The bounds are generous (a slow CI machine passes) but far below what a
quadratic or list-based implementation takes. Run with `lake exe bench`;
`scripts/check.sh` runs it. `lake exe bench probe <phase> <bytes>` times one
workload for profiling.
-/

open LeanJinja2

def rep (k : Nat) (s : String) : String := String.join (List.replicate k s)

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

/-- A string literal of about `n` characters. -/
def strLit (n : Nat) : String := "{{ '" ++ rep (n / 56) "lorem ipsum dolor sit amet, consectetur adipiscing elit" ++ "' }}"

def render (src : String) (vars : List (String × Value) := []) : Unit → Except TemplateError String :=
  fun _ => ({} : Environment).fromString src >>= (·.render vars)

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
  { name := "plain text 10 MB", run := render (plain 10000000), ok := rendersLen ((plain 10000000).length - 1),
    boundMs := 1000, boundMB := 200 },
  { name := "plain text 20 MB", run := render (plain 20000000), ok := rendersLen ((plain 20000000).length - 1),
    boundMs := 2000, boundMB := 300 },
  { name := "{{ x }}, x a 20 MB string", run := render "{{ x }}" [("x", .str (plain 20000000))],
    ok := rendersLen (plain 20000000).length, boundMs := 2000, boundMB := 300 },
  { name := "{{ x }} autoescaped, x a 20 MB string",
    run := fun _ => ({ autoescape := .const true } : Environment).fromString "{{ x }}" >>=
      (·.render [("x", .str (plain 20000000))]),
    ok := rendersLen (plain 20000000).length, boundMs := 2000, boundMB := 300 },
  { name := "string literal 10 MB", run := render (strLit 10000000),
    ok := rendersLen ((strLit 10000000).length - 8), boundMs := 2000, boundMB := 300 } ]

def benches : List Bench :=
  big ++ sized 10000 2000 ++ sized 100000 20000 ++ [
  { name := "range(100000000)", run := render "{{ range(100000000)|length }}", ok := isOverflow,
    boundMs := 100 },
  { name := "range(100000) loop", run := render "{% for i in range(100000) %}.{% endfor %}",
    ok := rendersLen 100000, boundMs := 5000 } ]

/-- `lake exe bench probe <phase> <bytes>`: one workload of about that size,
for profiling: `lex` (the specification lexer), `lexf` (the in-place one),
`parse`, `render` (plain text), `tags`, `blocks`, `strlit`, `comment`, `raw`,
`var`, `varesc`. -/
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
    | "varesc" => match (({ autoescape := .const true } : Environment).fromString "{{ x }}" >>=
          (·.render [("x", .str src)])) with
      | .ok s => s!"{s.length} chars" | .error e => toString e
    | _ => match render src [] () with | .ok s => s!"{s.length} chars" | .error e => toString e
  IO.println s!"{phase} {src.length} bytes: {r} in {(← IO.monoMsNow) - t0} ms"
  return 0

/-- Reset the peak resident memory (Linux; does nothing elsewhere). -/
def resetPeak : IO Unit :=
  try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()

/-- Peak resident memory in MB since the last reset (Linux `VmHWM`). -/
def peakMB : IO (Option Nat) := do
  try
    let st ← IO.FS.readFile "/proc/self/status"
    let ln := (st.splitOn "\n").find? (·.startsWith "VmHWM:")
    pure <| ln.bind fun l => ((l.drop 6).trimAscii.copy.takeWhile Char.isDigit).copy.toNat?.map (· / 1024)
  catch _ => pure none

def main (args : List String) : IO UInt32 := do
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
