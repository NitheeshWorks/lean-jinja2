import LeanJinja2.Proofs.Filters

/-!
# Loop variables, undefined values, template inheritance

Equations about the values the renderer binds and the rules it follows.
-/

namespace LeanJinja2

set_option linter.unusedSimpArgs false

open LeanMarkupsafe

/-! ## `for` loops -/

section Loop

variable (pol : UndefinedPolicy) (heap : Heap) (items : List Value) (i d : Nat)
  (recur : Option LoopRec) (cell : Nat)

/-- `for_loop_vars`: in iteration `i`, `loop.index` is `i + 1`, `loop.first`
holds exactly when `i = 0`, and `loop.last` exactly when `i + 1` is the
number of items. -/
theorem for_loop_vars :
    getattrV pol heap (loopValue items i d recur cell) "index" = .ok (.int (i + 1)) ∧
    getattrV pol heap (loopValue items i d recur cell) "first" = .ok (.bool (i == 0)) ∧
    getattrV pol heap (loopValue items i d recur cell) "last" = .ok (.bool (i + 1 == items.length)) :=
  ⟨rfl, rfl, rfl⟩

theorem loop_index0 : getattrV pol heap (loopValue items i d recur cell) "index0" = .ok (.int i) := rfl

theorem loop_length :
    getattrV pol heap (loopValue items i d recur cell) "length" = .ok (.int items.length) := rfl

theorem loop_revindex :
    getattrV pol heap (loopValue items i d recur cell) "revindex" = .ok (.int (items.length - i)) := rfl

theorem loop_revindex0 :
    getattrV pol heap (loopValue items i d recur cell) "revindex0" =
      .ok (.int (items.length - i - 1)) := rfl

theorem loop_depth : getattrV pol heap (loopValue items i d recur cell) "depth" = .ok (.int (d + 1)) :=
  rfl

theorem loop_previtem (h : 0 < i) (x : Value) (hx : items[i - 1]? = some x) :
    getattrV pol heap (loopValue items i d recur cell) "previtem" = .ok x := by
  simp [getattrV, pyAttr, loopAttr, loopValue, hx, Nat.pos_iff_ne_zero.mp h]

theorem loop_nextitem (x : Value) (hx : items[i + 1]? = some x) :
    getattrV pol heap (loopValue items i d recur cell) "nextitem" = .ok x := by
  simp [getattrV, pyAttr, loopAttr, loopValue, hx]

end Loop

/-- The loop body sees `loop` as the loop value: a `for` target never binds
`loop` (the compiler rejects it), so the lookup reaches the binding the
renderer adds. -/
theorem loop_lookup (fr : Frame) (binds : List (String × Value)) (L : Value)
    (hb : ∀ p ∈ binds, p.1 ≠ "loop") :
    Frame.lookup? { fr with locals := binds ++ ("loop", L) :: fr.locals } "loop" = some L := by
  simp only [Frame.lookup?]
  have : (binds ++ ("loop", L) :: fr.locals).lookup "loop" = some L := by
    induction binds with
    | nil => simp [List.lookup]
    | cons p ps ih =>
      have h1 := hb p List.mem_cons_self
      have : (("loop" == p.1) = false) := by
        simp only [beq_eq_false_iff_ne]; exact fun h => h1 h.symm
      simp only [List.cons_append, List.lookup, this]
      exact ih (fun q hq => hb q (List.mem_cons_of_mem _ hq))
  rw [this]

/-! ## Undefined values -/

/-- `undefined_policy`: how an undefined name prints under each policy
(upstream `Undefined`, `ChainableUndefined`, `DebugUndefined`,
`StrictUndefined`). -/
theorem undefined_policy (pol : UndefinedPolicy) (n : String) :
    strOf pol (.undef (.name n)) =
      match pol with
      | .strict => .error (.undefined s!"'{n}' is undefined")
      | .debug => .ok ("{{ " ++ n ++ " }}")
      | .default | .chainable => .ok "" := by
  cases pol <;> rfl

/-- Under every policy, `is defined` tells undefined values apart. -/
theorem test_defined (fc : FCtx) (v : Value) :
    applyTest fc "defined" v [] [] = .ok (!v.isUndef) := by
  simp [applyTest]; rfl

/-- Attribute access on an undefined value fails, except under the
chainable policy, where it is undefined again. -/
theorem undefined_getattr (pol : UndefinedPolicy) (heap : Heap) (n a : String) :
    getattrV pol heap (.undef (.name n)) a =
      if pol == .chainable then .ok (.undef (.name n)) else .error (.undefined s!"'{n}' is undefined") := by
  cases pol <;> rfl

/-! ## Inheritance -/

/-- `extends_block_override`: a block tag renders the most-derived body in
its chain (an extending template's block), not its own. -/
theorem extends_block_override (env : Environment) (n : Nat) (fr : Frame) (b : String) (sc : Bool)
    (body : List Node) (be : BlockEntry) (rest : List BlockEntry) (s : Heap)
    (hov : fr.overrides.lookup b = some (be :: rest)) (hshown : (fr.top && fr.parent.isSome) = false)
    (hreq : be.required = false) :
    renderNode env (n + 2) fr (.block b sc false body) s =
      (renderNodes env n
          { fr with locals := if sc then fr.locals else [], top := false,
                    curBlock := some (b, 0), autoescape := be.autoescape } be.body s).map
        (fun r => ((r.1.1, fr), r.2)) := by
  have hc : (fr.chain b)[0]? = some be := by simp [Frame.chain, hov]
  simp only [renderNode, hshown, hov, Option.getD_some, List.isEmpty_cons, Bool.false_eq_true,
    ↓reduceIte, bind, StateT.bind, renderBlockAt, hc, hreq, pure, StateT.pure]
  cases renderNodes env n _ be.body s <;> rfl

/-- After `{% extends %}`, the parent renders each of the child's blocks
first in its chain: merging into no prior overrides gives the child's entry. -/
theorem mergeOverrides_child (own : List (String × BlockEntry)) (b : String) (be : BlockEntry)
    (h : own = [(b, be)]) : (mergeOverrides [] own).lookup b = some [be] := by
  subst h; simp [mergeOverrides, List.lookup]

/-! ## The loop values the renderer binds -/

theorem loopValues_go (items : List Value) (d : Nat) (r : Option LoopRec) (c : Nat) :
    ∀ (xs pre : List Value), items = pre ++ xs →
      loopValues.go d r c items.length pre.getLast? pre.length xs =
        (xs.zipIdx pre.length).map (fun p => (p.1, loopValue items p.2 d r c))
  | [], _, _ => by simp [loopValues.go]
  | x :: xs, pre, h => by
    have ih := loopValues_go items d r c xs (pre ++ [x]) (by simp [h])
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, List.length_append,
      List.length_singleton] at ih
    simp only [loopValues.go, List.zipIdx_cons, List.map_cons, ih, loopValue, List.cons.injEq, and_true]
    subst h
    congr 2
    · rcases List.eq_nil_or_concat pre with rfl | ⟨p', y, rfl⟩
      · simp
      · simp
    · rw [List.getElem?_append_right (by omega)]
      cases xs <;> simp

/-- The renderer's loop values are `loopValue`'s, the ones `for_loop_vars`
describes. -/
theorem loopValues_eq (items : List Value) (d : Nat) (r : Option LoopRec) (c : Nat) :
    loopValues items d r c = items.zipIdx.map (fun p => (p.1, loopValue items p.2 d r c)) := by
  simpa [loopValues] using loopValues_go items d r c items [] rfl


end LeanJinja2
