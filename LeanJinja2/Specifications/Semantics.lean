import LeanJinja2.RepoImpl.Template

/-!
# Loop variables, undefined values, inheritance, filters

The equations the renderer's building blocks satisfy: the `loop` object, how
an undefined value prints under each policy, which body a block tag renders
under inheritance, and the builtin filters' defining equations.
-/

namespace LeanJinja2

open LeanMarkupsafe

/-- The characters `tojson` must never emit raw inside a `<script>` tag or
an HTML document. -/
def htmlUnsafe (c : Char) : Bool := c == '<' || c == '>' || c == '&' || c == '\''

namespace Spec

/-- `for_loop_vars`: in iteration `i`, `loop.index` is `i + 1`, `loop.first`
holds exactly when `i = 0`, and `loop.last` exactly when `i + 1` is the
number of items. -/
def forLoopVars : Prop :=
  ∀ (pol : UndefinedPolicy) (heap : Heap) (items : List Value) (i d : Nat) (recur : Option LoopRec) (cell : Nat),
    getattrV pol heap (loopValue items i d recur cell) "index" = .ok (.int (i + 1)) ∧
    getattrV pol heap (loopValue items i d recur cell) "first" = .ok (.bool (i == 0)) ∧
    getattrV pol heap (loopValue items i d recur cell) "last" = .ok (.bool (i + 1 == items.length))

/-- `undefined_policy`: how an undefined name prints under each policy. -/
def undefinedPolicy : Prop :=
  ∀ (pol : UndefinedPolicy) (n : String),
    strOf pol (.undef (.name n)) =
      match pol with
      | .strict => .error (.undefined s!"'{n}' is undefined")
      | .debug => .ok ("{{ " ++ n ++ " }}")
      | .default | .chainable => .ok ""

/-- `extends_block_override`: a block tag renders the most-derived body in
its chain, with that template's autoescape setting. -/
def extendsBlockOverride : Prop :=
  ∀ (env : Environment) (n : Nat) (fr : Frame) (b : String) (sc : Bool) (body : List Node) (be : BlockEntry)
    (rest : List BlockEntry) (s : Heap),
    fr.overrides.lookup b = some (be :: rest) → (fr.top && fr.parent.isSome) = false → be.required = false →
    renderNode env (n + 2) fr (.block b sc false body) s =
      (renderNodes env n
          { fr with locals := if sc then fr.locals else [], top := false,
                    curBlock := some (b, 0), autoescape := be.autoescape } be.body s).map
        (fun r => ((r.1.1, fr), r.2))

/-- The builtin filters' defining equations (upstream `filters.py`). -/
def filterLaws : Prop :=
  ∀ (fc : FCtx),
    (∀ s, applyFilter fc "upper" (.str s) [] [] = .ok (.str (strUpper s))) ∧
    (∀ s, applyFilter fc "lower" (.str s) [] [] = .ok (.str (strLower s))) ∧
    (∀ xs : List Value, applyFilter fc "length" (.list xs.toArray) [] [] = .ok (.int xs.length)) ∧
    (∀ i d, applyFilter fc "default" (.undef i) [d] [] = .ok d) ∧
    (∀ v d, v.isUndef = false → applyFilter fc "default" v [d] [] = .ok v) ∧
    (∀ s, applyFilter fc "escape" (.str s) [] [] = .ok (.markup (escape s))) ∧
    (∀ m, applyFilter fc "escape" (.markup m) [] [] = .ok (.markup m)) ∧
    (∀ s, applyFilter fc "safe" (.str s) [] [] = .ok (.markup (Markup.markSafe s))) ∧
    (∀ (x : Value) (xs : List Value), applyFilter fc "first" (.list (x :: xs).toArray) [] [] = .ok x) ∧
    (∀ (xs : List Value) x, applyFilter fc "last" (.list (xs ++ [x]).toArray) [] [] = .ok x) ∧
    (∀ xs : List Value, applyFilter fc "reverse" (.list xs.toArray) [] [] = .ok (.list xs.reverse.toArray))

/-- `tojson_htmlsafe`: `tojson` returns markup with no raw `<`, `>`, `&`, `'`. -/
def tojsonHtmlsafe : Prop :=
  ∀ (fc : FCtx) (v r : Value), applyFilter fc "tojson" v [] [] = .ok r →
    ∃ m : Markup, r = .markup m ∧ ∀ c ∈ m.str.toList, htmlUnsafe c = false

/-- `import_namespace`: the namespace an import binds (`moduleExports`, from
the module's final context `ctx` and the length `start` of the one it began
with) holds each name once, and looking a name up in it is looking it up in
the module's top-level assignments, except that names starting with `_` are
private and a macro carries the module's context. -/
def importNamespace : Prop :=
  ∀ (start : Nat) (ctx : List (String × Value)),
    ((moduleExports start ctx).map Prod.fst).Nodup ∧
    ∀ k, (moduleExports start ctx).lookup k =
      if k.startsWith "_" then none else ((ctx.take (ctx.length - start)).lookup k).map (exportValue ctx)

end Spec

end LeanJinja2
