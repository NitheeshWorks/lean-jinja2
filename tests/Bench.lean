import LeanJinja2
open LeanJinja2

def nestedIf (k : Nat) (close : Bool) : String :=
  String.join (List.replicate k "{% if true %}") ++ "x" ++ (if close then String.join (List.replicate k "{% endif %}") else "")

def nestedFor (k : Nat) : String :=
  String.join (List.replicate k "{% for x in [1] %}") ++ "x" ++ String.join (List.replicate k "{% endfor %}")

def siblings (k : Nat) : String := String.join (List.replicate k "{{ x }}{% if x %}y{% endif %}")

def timeIt {α : Type} (label : String) (f : Unit → α) (show_ : α → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  let s := show_ r
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1 - t0} ms  {s.take 80}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 3000
  let src := nestedIf k true
  timeIt s!"lex {k}" (fun _ => lex {} src) (fun | .ok ts => s!"{ts.length} tokens" | .error e => e.msg)
  timeIt s!"significant {k}" (fun _ => match lex {} src with | .ok ts => (significant ts).length | _ => 0) toString
  timeIt s!"parse {k}" (fun _ => parse {} src) (fun | .ok b => s!"{b.length} nodes" | .error e => e.msg)
  timeIt s!"parse unclosed {k}" (fun _ => parse {} (nestedIf k false)) (fun | .ok b => s!"{b.length} nodes" | .error e => e.msg)
  timeIt s!"parse for {k}" (fun _ => parse {} (nestedFor k)) (fun | .ok b => s!"{b.length} nodes" | .error e => e.msg)
  timeIt s!"parse siblings {k}" (fun _ => parse {} (siblings k)) (fun | .ok b => s!"{b.length} nodes" | .error e => e.msg)
  timeIt s!"render for {k}" (fun _ => (({} : Environment).fromString (nestedFor k) >>= (·.render))) (fun | .ok s => s | .error e => toString e)
  timeIt s!"render siblings {k}" (fun _ => (({} : Environment).fromString (siblings k) >>= (·.render [("x", 1)]))) (fun | .ok s => s!"{s.length} chars" | .error e => toString e)
  timeIt s!"render {k}" (fun _ => (({} : Environment).fromString src >>= (·.render))) (fun | .ok s => s | .error e => toString e)
