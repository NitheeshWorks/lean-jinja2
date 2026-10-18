import LeanJinja2.RepoImpl.Render

/-!
# Templates: loading and rendering

Upstream's surface, in Lean spelling:

```lean
let env : Environment := { loader := DictLoader [("hello.html", "Hello {{ name }}!")],
                           autoescape := selectAutoescape }
let t ← env.getTemplate "hello.html"
t.render [("name", "World")]          -- .ok "Hello World!"
```

`Environment.getTemplate` and `Environment.fromString` load and compile;
`Template.render` renders with keyword-style variables. Plain Lean values
coerce to `Value` (`"World"`, `42`, `true`, `[..]`, `Markup`).
-/

namespace LeanJinja2

open LeanMarkupsafe

/-- Errors a template raises (upstream `TemplateError` and subclasses). -/
abbrev TemplateError := RenderError

/-- A compiled template (upstream `jinja2.Template`). -/
structure Template where
  env : Environment
  /-- The name it was loaded by (`none` for `from_string`). -/
  name : Option String
  /-- The parsed body. -/
  body : List Node

/-- Load and compile a template by name (upstream `Environment.get_template`). -/
def Environment.getTemplate (env : Environment) (name : String) : Except TemplateError Template := do
  let src ← env.getSource name
  let body ← env.compile src
  pure ⟨env, some name, body⟩

/-- The first template that exists (upstream `Environment.select_template`). -/
def Environment.selectTemplate (env : Environment) (names : List String) :
    Except TemplateError Template :=
  match names.find? (fun n => (env.getSource n).toOption.isSome) with
  | some n => env.getTemplate n
  | none => .error (.notFound s!"none of the templates given were found: {names}")

/-- Compile a template from source (upstream `Environment.from_string`). -/
def Environment.fromString (env : Environment) (source : String)
    (globals : List (String × Value) := []) : Except TemplateError Template := do
  let env := { env with globals := globals ++ env.globals }
  let body ← env.compile source
  pure ⟨env, none, body⟩

/-- The trace a render produces, before flattening (see `Piece`). -/
def Template.renderTrace (t : Template) (vars : List (String × Value) := []) :
    Except TemplateError (List Piece) :=
  match (renderTemplate t.env t.env.maxDepth { ctx := t.env.startContext vars } t.name t.body).run [] with
  | .ok ((ps, _), _) => .ok ps
  | .error e => .error e

/-- Render the template with the given variables (upstream
`Template.render(**vars)`). -/
def Template.render (t : Template) (vars : List (String × Value) := []) :
    Except TemplateError String := do
  let ps ← t.renderTrace vars
  (Piece.flatten t.env.undefined ps).mapError ValueError.toRenderError

/-! ## Values from Lean values -/

instance : Coe String Value := ⟨.str⟩
instance : Coe Bool Value := ⟨.bool⟩
instance : Coe Int Value := ⟨.int⟩
instance : Coe Markup Value := ⟨.markup⟩
instance : OfNat Value n := ⟨.int n⟩

/-- Lean values that render as template values. -/
class ToValue (α : Type) where
  toValue : α → Value

instance : ToValue Value := ⟨id⟩
instance : ToValue String := ⟨.str⟩
instance : ToValue Bool := ⟨.bool⟩
instance : ToValue Int := ⟨.int⟩
instance : ToValue Nat := ⟨fun n => .int n⟩
instance : ToValue Markup := ⟨.markup⟩
instance {α : Type} [ToValue α] : ToValue (List α) := ⟨fun xs => .list (xs.map ToValue.toValue)⟩
instance {α : Type} [ToValue α] : ToValue (Option α) := ⟨fun o => (o.map ToValue.toValue).getD .none⟩
instance {α : Type} [ToValue α] : ToValue (List (String × α)) :=
  ⟨fun kvs => .dict (kvs.map (fun p => (.str p.1, ToValue.toValue p.2)))⟩

/-- A mapping value from string keys. -/
def Value.ofDict (kvs : List (String × Value)) : Value := .dict (kvs.map (fun p => (.str p.1, p.2)))

instance : Repr Value := ⟨fun v _ => v.repr⟩
instance : ToString Value := ⟨Value.repr⟩

end LeanJinja2
