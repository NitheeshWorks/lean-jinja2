import LeanJinja2

/-!
# Hostile-template bench: time bounds

Templates an attacker controls must not cost more than linear time. Each case
below renders (or compiles) a template nested `10^4` and `10^5` deep, or asks
for a huge `range`, checks the outcome, and fails if it took longer than its
bound. The bounds are generous (a slow CI machine passes) but far below what a
quadratic lexer, parser or renderer would take: before the linear rewrite,
`10^4` nested `if`s took 62 s.

Run with `lake exe bench`; `scripts/check.sh` runs it.
-/

open LeanJinja2

def rep (k : Nat) (s : String) : String := String.join (List.replicate k s)

def nestedIf (k : Nat) : String := rep k "{% if true %}" ++ "x" ++ rep k "{% endif %}"
def unclosedIf (k : Nat) : String := rep k "{% if true %}" ++ "x"
def nestedFor (k : Nat) : String := rep k "{% for x in [1] %}" ++ "x" ++ rep k "{% endfor %}"
def nestedParens (k : Nat) : String := "{{ " ++ rep k "(" ++ "1" ++ rep k ")" ++ " }}"
def siblings (k : Nat) : String := rep k "{{ x }}{% if x %}y{% endif %}"

/-- One bench case: what to run, what the outcome must satisfy, and the time
bound in milliseconds. -/
structure Bench where
  name : String
  run : Unit → Except TemplateError String
  ok : Except TemplateError String → Bool
  boundMs : Nat

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

def benches : List Bench :=
  sized 10000 2000 ++ sized 100000 20000 ++ [
  { name := "range(100000000)", run := render "{{ range(100000000)|length }}", ok := isOverflow,
    boundMs := 100 },
  { name := "range(100000) loop", run := render "{% for i in range(100000) %}.{% endfor %}",
    ok := rendersLen 100000, boundMs := 5000 } ]

def main : IO UInt32 := do
  let mut failures := 0
  for b in benches do
    let t0 ← IO.monoMsNow
    let r := b.run ()
    let good := b.ok r
    let t1 ← IO.monoMsNow
    let ms := t1 - t0
    let what := match r with | .ok s => s!"ok, {s.length} chars" | .error e => toString e
    if good && ms ≤ b.boundMs then
      IO.println s!"ok    {b.name}: {ms} ms (bound {b.boundMs})  {what.take 60}"
    else
      failures := failures + 1
      IO.println s!"FAIL  {b.name}: {ms} ms (bound {b.boundMs})  {what.take 60}"
    (← IO.getStdout).flush
  IO.println s!"{benches.length} benches, {failures} failing"
  return if failures == 0 then 0 else 1
