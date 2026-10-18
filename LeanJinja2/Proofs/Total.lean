import LeanJinja2.Proofs.Monad
import LeanJinja2.Specifications.Total

/-!
# `render_total`

`Safe m P`: from every heap, `m` does not fail with `fuelExhausted`, and its
results satisfy `P`. The renderer's functions are `Safe` once the fuel covers
the nesting depth of what they render, proved for all of them at once by
induction on the fuel, like the autoescape invariant in `Proofs/Render.lean`.
-/

namespace LeanJinja2

set_option linter.unusedSimpArgs false

/-- `m` never runs out of fuel, and what it returns satisfies `P`. -/
def Safe {α : Type} (m : RenderM α) (P : α → Prop) : Prop :=
  ∀ s, m s ≠ .error .fuelExhausted ∧ ∀ a s', m s = .ok (a, s') → P a

namespace Safe

variable {α β : Type}

theorem pure' {a : α} {P : α → Prop} (h : P a) : Safe (pure a) P :=
  fun _ => ⟨by simp [pure, StateT.pure, Except.pure], fun a' s' h' => by
    simp [pure, StateT.pure, Except.pure] at h'; exact h'.1 ▸ h⟩

theorem bind' {m : RenderM α} {f : α → RenderM β} {P : α → Prop} {Q : β → Prop}
    (hm : Safe m P) (hf : ∀ a, P a → Safe (f a) Q) : Safe (m >>= f) Q := by
  intro s
  have h1 := hm s
  cases hms : m s with
  | error e =>
    refine ⟨?_, fun _ _ h => ?_⟩
    · have : (m >>= f) s = .error e := by
        simp only [bind, StateT.bind, hms]; rfl
      rw [this]; intro he; cases he; exact h1.1 hms
    · simp only [bind, StateT.bind, hms] at h; cases h
  | ok r =>
    obtain ⟨a, s1⟩ := r
    have hp := h1.2 a s1 hms
    have h2 := hf a hp s1
    have : (m >>= f) s = f a s1 := by simp only [bind, StateT.bind, hms]; rfl
    rw [this]; exact h2

theorem weaken {m : RenderM α} {P Q : α → Prop} (h : Safe m P) (hpq : ∀ a, P a → Q a) : Safe m Q :=
  fun s => ⟨(h s).1, fun a s' h' => hpq a ((h s).2 a s' h')⟩

theorem throw' {e : RenderError} (he : e ≠ .fuelExhausted) {P : α → Prop} : Safe (throw e) P :=
  fun _ => ⟨by simp [throw_run'] ; exact fun h => he (by cases h; rfl), fun _ _ h => by simp [throw_run'] at h⟩
where throw_run' : ∀ s, (throw e : RenderM α) s = .error e := fun _ => rfl

theorem toRenderError_ne (e : ValueError) : e.toRenderError ≠ .fuelExhausted := by
  cases e <;> simp [ValueError.toRenderError]

theorem liftR' {x : Except ValueError α} : Safe (liftR x) (fun a => x = .ok a) := by
  cases x with
  | error e => exact throw' (toRenderError_ne e)
  | ok a => exact pure' rfl

theorem get' : Safe (get : RenderM Heap) (fun _ => True) :=
  fun _ => ⟨by simp [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure], fun _ _ _ => trivial⟩

theorem set' (h : Heap) : Safe (set h : RenderM PUnit) (fun _ => True) :=
  fun _ => ⟨by simp [set, MonadStateOf.set, StateT.set, pure, Except.pure], fun _ _ _ => trivial⟩

theorem modify' (f : Heap → Heap) : Safe (modify f : RenderM PUnit) (fun _ => True) :=
  fun _ => ⟨by simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure],
    fun _ _ _ => trivial⟩

theorem mapM' {f : α → RenderM β} {P : β → Prop} :
    ∀ (xs : List α), (∀ x ∈ xs, Safe (f x) P) → Safe (xs.mapM f) (fun ys => ∀ y ∈ ys, P y)
  | [], _ => by simpa [List.mapM_nil] using pure' (P := fun ys : List β => ∀ y ∈ ys, P y) (by simp)
  | x :: xs, h => by
    rw [List.mapM_cons]
    refine bind' (h x List.mem_cons_self) fun y hy => ?_
    refine bind' (mapM' xs fun x hx => h x (List.mem_cons_of_mem _ hx)) fun ys hys => ?_
    exact pure' (by simp only [List.mem_cons]; rintro z (rfl | hz); exact hy; exact hys z hz)

theorem foldlM' {f : β → α → RenderM β} (I : β → Prop) :
    ∀ (xs : List α) (init : β), (∀ b x, x ∈ xs → I b → Safe (f b x) I) → I init →
      Safe (xs.foldlM f init) I
  | [], init, _, hi => by simpa using pure' hi
  | x :: xs, init, h, hi => by
    rw [List.foldlM_cons]
    exact bind' (h init x List.mem_cons_self hi) fun b hb =>
      foldlM' I xs b (fun b y hy => h b y (List.mem_cons_of_mem _ hy)) hb

theorem findM?' {p : α → RenderM Bool} :
    ∀ (xs : List α), (∀ x ∈ xs, Safe (p x) (fun _ => True)) →
      Safe (xs.findM? p) (fun r => ∀ x, r = some x → x ∈ xs)
  | [], _ => by simpa [List.findM?] using pure' (P := fun r : Option α => ∀ x, r = some x → x ∈ ([] : List α)) (by simp)
  | x :: xs, h => by
    simp only [List.findM?]
    refine bind' (h x List.mem_cons_self) fun b _ => ?_
    cases b
    · exact weaken (findM?' xs fun y hy => h y (List.mem_cons_of_mem _ hy))
        (fun r hr z hz => List.mem_cons_of_mem _ (hr z hz))
    · exact pure' (by intro z hz; cases hz; exact List.mem_cons_self)

theorem filterM' {p : α → RenderM Bool} (xs : List α) (h : ∀ x ∈ xs, Safe (p x) (fun _ => True)) :
    Safe (xs.filterM p) (fun _ => True) := by
  unfold List.filterM
  suffices ∀ (ys : List α) (acc : List α), (∀ x ∈ ys, Safe (p x) (fun _ => True)) →
      Safe (List.filterAuxM p ys acc) (fun _ => True) by
    exact bind' (this xs [] h) fun _ _ => pure' trivial
  intro ys
  induction ys with
  | nil => intro acc _; simpa [List.filterAuxM] using pure' (P := fun _ : List α => True) trivial
  | cons y ys ih =>
    intro acc hy
    simp only [List.filterAuxM]
    exact bind' (hy y List.mem_cons_self) fun b _ =>
      ih _ (fun x hx => hy x (List.mem_cons_of_mem _ hx))

end Safe


theorem Safe.bindT {α β : Type} {m : RenderM α} {f : α → RenderM β} {Q : β → Prop}
    (hm : Safe m (fun _ => True)) (hf : ∀ a, Safe (f a) Q) : Safe (m >>= f) Q :=
  Safe.bind' hm (fun a _ => hf a)

theorem Safe.liftT {α : Type} {x : Except ValueError α} : Safe (liftR x) (fun _ => True) :=
  Safe.liftR'.weaken (fun _ _ => trivial)

/-! ## What the predicates say about the parts of a node -/

section Parts

theorem Expr.depth_pos (e : Expr) : 1 ≤ e.depth := by cases e <;> simp [Expr.depth]

theorem Target.depth_pos (t : Target) : 1 ≤ t.depth := by cases t <;> simp [Target.depth]

theorem Node.depth_pos (n : Node) : 1 ≤ n.depth := by cases n <;> simp [Node.depth]

theorem exprs_mem {xs : List Expr} {x : Expr} (hx : x ∈ xs) :
    (exprsNonrec xs = true → x.nonrec = true) ∧ x.depth ≤ exprsDepth xs := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [exprsNonrec, exprsDepth, Bool.and_eq_true]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨fun h => h.1, by (try dsimp only); omega⟩
    · have := ih hx; exact ⟨fun h => this.1 h.2, by (try dsimp only); omega⟩

theorem kw_mem {kw : List (String × Expr)} {p : String × Expr} (hp : p ∈ kw) :
    (kwNonrec kw = true → p.2.nonrec = true) ∧ p.2.depth ≤ kwDepth kw := by
  induction kw with
  | nil => cases hp
  | cons q qs ih =>
    obtain ⟨k, y⟩ := q
    simp only [kwNonrec, kwDepth, Bool.and_eq_true]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨fun h => h.1, by (try dsimp only); omega⟩
    · have := ih hp; exact ⟨fun h => this.1 h.2, by (try dsimp only); omega⟩

theorem ops_mem {ops : List (CmpOp × Expr)} {p : CmpOp × Expr} (hp : p ∈ ops) :
    (opsNonrec ops = true → p.2.nonrec = true) ∧ p.2.depth ≤ opsDepth ops := by
  induction ops with
  | nil => cases hp
  | cons q qs ih =>
    obtain ⟨k, y⟩ := q
    simp only [opsNonrec, opsDepth, Bool.and_eq_true]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨fun h => h.1, by (try dsimp only); omega⟩
    · have := ih hp; exact ⟨fun h => this.1 h.2, by (try dsimp only); omega⟩

theorem pairs_mem {ps : List (Expr × Expr)} {p : Expr × Expr} (hp : p ∈ ps) :
    (pairsNonrec ps = true → p.1.nonrec = true ∧ p.2.nonrec = true) ∧
      p.1.depth ≤ pairsDepth ps ∧ p.2.depth ≤ pairsDepth ps := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
    obtain ⟨a, b⟩ := q
    simp only [pairsNonrec, pairsDepth, Bool.and_eq_true]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨fun h => ⟨h.1.1, h.1.2⟩, by (try dsimp only); omega, by (try dsimp only); omega⟩
    · have := ih hp; exact ⟨fun h => this.1 h.2, by (try dsimp only); omega, by (try dsimp only); omega⟩

theorem targets_mem {ts : List Target} {t : Target} (ht : t ∈ ts) :
    (targetsNonrec ts = true → t.nonrec = true) ∧ t.depth ≤ targetsDepth ts := by
  induction ts with
  | nil => cases ht
  | cons y ys ih =>
    simp only [targetsNonrec, targetsDepth, Bool.and_eq_true]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨fun h => h.1, by (try dsimp only); omega⟩
    · have := ih ht; exact ⟨fun h => this.1 h.2, by (try dsimp only); omega⟩

theorem nodes_mem {ns : List Node} {x : Node} (hx : x ∈ ns) :
    (nodesNonrec ns = true → x.nonrec = true) ∧ x.depth ≤ nodesDepth ns := by
  induction ns with
  | nil => cases hx
  | cons y ys ih =>
    simp only [nodesNonrec, nodesDepth, Bool.and_eq_true]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨fun h => h.1, by (try dsimp only); omega⟩
    · have := ih hx; exact ⟨fun h => this.1 h.2, by (try dsimp only); omega⟩

theorem branches_mem {bs : List (Expr × List Node)} {b : Expr × List Node} (hb : b ∈ bs) :
    (branchesNonrec bs = true → b.1.nonrec = true ∧ nodesNonrec b.2 = true) ∧
      b.1.depth ≤ branchesDepth bs ∧ nodesDepth b.2 ≤ branchesDepth bs := by
  induction bs with
  | nil => cases hb
  | cons q qs ih =>
    obtain ⟨e, body⟩ := q
    simp only [branchesNonrec, branchesDepth, Bool.and_eq_true]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨fun h => ⟨h.1.1, h.1.2⟩, by (try dsimp only); omega, by (try dsimp only); omega⟩
    · have := ih hb; exact ⟨fun h => this.1 h.2, by (try dsimp only); omega, by (try dsimp only); omega⟩

theorem chain_mem {fs : List FilterCall} {f : FilterCall} (hf : f ∈ fs) :
    (chainNonrec fs = true → exprsNonrec f.args = true ∧ kwNonrec f.kwargs = true) ∧
      exprsDepth f.args ≤ chainDepth fs ∧ kwDepth f.kwargs ≤ chainDepth fs := by
  induction fs with
  | nil => cases hf
  | cons q qs ih =>
    simp only [chainNonrec, chainDepth, Bool.and_eq_true]
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨fun h => ⟨h.1.1, h.1.2⟩, by (try dsimp only); omega, by (try dsimp only); omega⟩
    · have := ih hf; exact ⟨fun h => this.1 h.2, by (try dsimp only); omega, by (try dsimp only); omega⟩

theorem assigns_mem {as : List (Target × Expr)} {a : Target × Expr} (ha : a ∈ as) :
    (assignsNonrec as = true → a.1.nonrec = true ∧ a.2.nonrec = true) ∧
      a.1.depth ≤ assignsDepth as ∧ a.2.depth ≤ assignsDepth as := by
  induction as with
  | nil => cases ha
  | cons q qs ih =>
    obtain ⟨t, e⟩ := q
    simp only [assignsNonrec, assignsDepth, Bool.and_eq_true]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨fun h => ⟨h.1.1, h.1.2⟩, by (try dsimp only); omega, by (try dsimp only); omega⟩
    · have := ih ha; exact ⟨fun h => this.1 h.2, by (try dsimp only); omega, by (try dsimp only); omega⟩

end Parts

theorem Except.mapM_mem {ε α β : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; simp
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok y =>
      cases hxs : xs.mapM f with
      | error e => simp [hx, hxs, bind, Except.bind] at h
      | ok zs =>
        simp [hx, hxs, bind, Except.bind, pure, Except.pure] at h
        subst h
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨x', hx', he⟩ := Except.mapM_mem hxs w hw
          exact ⟨x', List.mem_cons_of_mem _ hx', he⟩

theorem bindTarget_keys (pol : UndefinedPolicy) (heap : Heap) :
    ∀ (t : Target) (v : Value) (bs : List (String × Value)), t.nonrec = true →
      bindTarget pol heap t v = .ok bs → ∀ p ∈ bs, callableGlobals.contains p.1 = false
  | .name n, v, bs, hn, h => by
    simp [bindTarget] at h; subst h; simpa [Target.nonrec] using hn
  | .nsAttr _ _, v, bs, hn, h => by simp [bindTarget] at h
  | .tuple ts, v, bs, hn, h => by
    rw [bindTarget] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i parts hparts
            simp [pure, Except.pure] at h
            subst h
            intro p hp
            simp only [List.mem_flatten] at hp
            obtain ⟨part, hpart, hp⟩ := hp
            obtain ⟨⟨⟨t', ht'⟩, x⟩, hmem, hbt⟩ := Except.mapM_mem hparts part hpart
            have hmt : t' ∈ ts := ht'
            have := List.sizeOf_lt_of_mem hmt
            exact bindTarget_keys pol heap t' x part ((targets_mem hmt).1 (by simpa [Target.nonrec] using hn)) hbt p hp
termination_by t => sizeOf t
decreasing_by simp_wf; omega


/-! ## The frame invariant -/

/-- What rendering a non-recursive template keeps true of the frame: no
block overrides and no parent (there is no `extends`), no local binds a
callable global, and the context binds them only to values that do not
re-enter template code. -/
def FrOK (fr : Frame) : Prop :=
  fr.overrides = [] ∧ fr.parent = none ∧ (∀ g ∈ callableGlobals, fr.locals.lookup g = none) ∧
    (∀ g ∈ callableGlobals, ∀ v, fr.ctx.lookup g = some v → v.reenters = false)

/-- Keys that are not callable globals. -/
def Plain (bs : List (String × Value)) : Prop := ∀ p ∈ bs, callableGlobals.contains p.1 = false

theorem lookup_plain_append {bs l : List (String × Value)} (hb : Plain bs) {g : String}
    (hg : g ∈ callableGlobals) : (bs ++ l).lookup g = l.lookup g := by
  induction bs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    have hk := hb (k, v) List.mem_cons_self
    have hne : (g == k) = false := by
      simp only [beq_eq_false_iff_ne]; rintro rfl; simp [List.contains_iff_mem, hg] at hk
    simp only [List.cons_append, List.lookup, hne]
    exact ih (fun q hq => hb q (List.mem_cons_of_mem _ hq))

theorem Plain.nil : Plain [] := fun _ h => by cases h

theorem Plain.append {a b : List (String × Value)} (ha : Plain a) (hb : Plain b) : Plain (a ++ b) :=
  fun p hp => (List.mem_append.mp hp).elim (ha p) (hb p)

theorem Plain.flatten {bss : List (List (String × Value))} (h : ∀ bs ∈ bss, Plain bs) : Plain bss.flatten :=
  fun p hp => by
    obtain ⟨bs, hbs, hp⟩ := List.mem_flatten.mp hp
    exact h bs hbs p hp

theorem Plain.loop (v : Value) : Plain [("loop", v)] := by
  intro p hp; simp at hp; subst hp; simp [callableGlobals]

/-- A frame with more plain locals, or fewer, and otherwise the same
invariant fields, keeps the invariant. -/
theorem FrOK.with_locals {fr fr' : Frame} (h : FrOK fr) (ho : fr'.overrides = fr.overrides)
    (hp : fr'.parent = fr.parent) (hc : fr'.ctx = fr.ctx)
    (hl : ∃ bs, Plain bs ∧ (fr'.locals = bs ++ fr.locals ∨ fr'.locals = bs)) : FrOK fr' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨bs, hbs, hl | hl⟩ := hl
  · refine ⟨ho ▸ h1, hp ▸ h2, fun g hg => ?_, hc ▸ h4⟩
    rw [hl, lookup_plain_append hbs hg]; exact h3 g hg
  · refine ⟨ho ▸ h1, hp ▸ h2, fun g hg => ?_, hc ▸ h4⟩
    rw [hl, ← List.append_nil bs, lookup_plain_append hbs hg]; rfl

theorem FrOK.same_locals {fr fr' : Frame} (h : FrOK fr) (ho : fr'.overrides = fr.overrides)
    (hp : fr'.parent = fr.parent) (hc : fr'.ctx = fr.ctx) (hl : fr'.locals = fr.locals) : FrOK fr' :=
  h.with_locals ho hp hc ⟨[], Plain.nil, Or.inl (by simpa using hl)⟩

theorem FrOK.lookup {fr : Frame} (h : FrOK fr) {g : String} (hg : g ∈ callableGlobals) {v : Value}
    (hv : fr.lookup? g = some v) : v.reenters = false := by
  simp only [Frame.lookup?, h.2.2.1 g hg] at hv
  exact h.2.2.2 g hg v hv

theorem evalE_global (env : Environment) (k : Nat) {fr : Frame} (h : FrOK fr) {g : String}
    (hg : g ∈ callableGlobals) : Safe (evalE env (k + 1) fr (.name g)) (fun v => v.reenters = false) := by
  have hs : g ≠ "super" := by rintro rfl; simp [callableGlobals] at hg
  simp only [evalE]
  cases hl : fr.lookup? g with
  | some v => exact Safe.pure' (h.lookup hg hl)
  | none =>
    simp only
    split
    · exact absurd rfl hs
    · exact Safe.pure' rfl


/-- Take a `Safe` goal apart: binds, leaves (`pure`, `liftR`, heap access,
non-fuel `throw`), and case splits. What is left are calls into the renderer. -/
macro "safe_steps" : tactic => `(tactic| repeat' (first
  | exact Safe.pure' trivial
  | exact Safe.liftT
  | exact Safe.get'
  | exact Safe.set' _
  | exact Safe.modify' _
  | (apply Safe.throw'; simp)
  | (refine Safe.bindT ?_ fun _ => ?_)
  | split))

/-- A filter application never runs out of fuel. -/
theorem Safe.applyFilterM' {env : Environment} {fr : Frame} {name : String} {v : Value}
    {args : List Value} {kw : List (String × Value)} :
    Safe (applyFilterM env fr name v args kw) (fun _ => True) := by
  unfold applyFilterM; safe_steps

/-- A comparison never runs out of fuel. -/
theorem Safe.compareM' {pol : UndefinedPolicy} {op : CmpOp} {a b : Value} :
    Safe (compareM pol op a b) (fun _ => True) := by
  intro s
  unfold compareM
  split
  · exact ⟨by simp, fun _ _ _ => trivial⟩
  · rename_i e _
    exact ⟨by simpa using toRenderError_ne e, fun _ _ h => by simp at h⟩

/-- Indexing never runs out of fuel. -/
theorem Safe.getitemM' {pol : UndefinedPolicy} {v k : Value} :
    Safe (getitemM pol v k) (fun _ => True) := by
  unfold getitemM; safe_steps

/-! ## The induction -/

/-- Every renderer function is `Safe` at fuel `n` on what fits in `n`. -/
structure Good (env : Environment) (n : Nat) : Prop where
  eval : ∀ fr e, FrOK fr → e.nonrec = true → e.depth < n → Safe (evalE env n fr e) (fun _ => True)
  call : ∀ fr f args kw, f.reenters = false → 0 < n → Safe (callV env n fr f args kw) (fun _ => True)
  assign : ∀ fr t v, FrOK fr → t.nonrec = true → t.depth ≤ n → Safe (assignTo env n fr t v) FrOK
  chain : ∀ fr fs v, FrOK fr → chainNonrec fs = true → chainDepth fs + 1 < n →
    Safe (applyChain env n fr fs v) (fun _ => True)
  items : ∀ fr rec items, FrOK fr → rec.target.nonrec = true → optNonrec rec.filter = true →
    optDepth rec.filter + 1 < n → Safe (loopItems env n fr rec items) (fun _ => True)
  nodes : ∀ fr ns, FrOK fr → nodesNonrec ns = true → 3 * nodesDepth ns + 1 ≤ n →
    Safe (renderNodes env n fr ns) (fun r => FrOK r.2)
  node : ∀ fr nd, FrOK fr → nd.nonrec = true → 3 * nd.depth ≤ n →
    Safe (renderNode env n fr nd) (fun r => FrOK r.2)
  loop : ∀ fr rec rc items d, FrOK fr → rec.target.nonrec = true → optNonrec rec.filter = true →
    nodesNonrec rec.body = true → nodesNonrec rec.else_ = true → optDepth rec.filter + 2 < n →
    3 * max (nodesDepth rec.body) (nodesDepth rec.else_) + 2 ≤ n →
    Safe (renderLoop env n fr rec rc items d) (fun _ => True)

theorem good_zero (env : Environment) : Good env 0 where
  eval _ _ _ _ h := absurd h (Nat.not_lt_zero _)
  call _ _ _ _ _ h := absurd h (Nat.lt_irrefl 0)
  assign _ t _ _ _ h := absurd h (by have := Target.depth_pos t; omega)
  chain _ _ _ _ _ h := absurd h (Nat.not_lt_zero _)
  items _ _ _ _ _ _ h := absurd h (Nat.not_lt_zero _)
  nodes _ _ _ _ h := absurd h (by omega)
  node _ nd _ _ h := absurd h (by have := Node.depth_pos nd; omega)
  loop _ _ _ _ _ _ _ _ _ _ h _ := absurd h (Nat.not_lt_zero _)

section Step

variable {env : Environment} {n : Nat} (ih : Good env n)
include ih

theorem Good.evals {fr : Frame} (h : FrOK fr) {xs : List Expr} (hn : exprsNonrec xs = true)
    (hd : exprsDepth xs < n) : Safe (xs.mapM (evalE env n fr)) (fun _ => True) :=
  (Safe.mapM' xs fun x hx => ih.eval fr x h ((exprs_mem hx).1 hn)
    (Nat.lt_of_le_of_lt (exprs_mem hx).2 hd)).weaken (fun _ _ => trivial)

theorem Good.evalKw {fr : Frame} (h : FrOK fr) {kw : List (String × Expr)} (hn : kwNonrec kw = true)
    (hd : kwDepth kw < n) :
    Safe (kw.mapM (fun p => do let v ← evalE env n fr p.2; pure (p.1, v))) (fun _ => True) :=
  (Safe.mapM' (P := fun _ => True) kw fun p hp => Safe.bindT (ih.eval fr p.2 h ((kw_mem hp).1 hn)
    (Nat.lt_of_le_of_lt (kw_mem hp).2 hd)) fun _ => Safe.pure' trivial).weaken (fun _ _ => trivial)

theorem Good.evalOpt {fr : Frame} (h : FrOK fr) {a : Option Expr} (hn : optNonrec a = true)
    (hd : optDepth a < n) : Safe (a.mapM (evalE env n fr)) (fun _ => True) := by
  cases a with
  | none => exact Safe.pure' trivial
  | some x =>
    simp only [Option.mapM_some]
    exact Safe.bindT (ih.eval fr x h hn hd) fun _ => Safe.pure' trivial

theorem Good.evalPairs {fr : Frame} (h : FrOK fr) {ps : List (Expr × Expr)} (hn : pairsNonrec ps = true)
    (hd : pairsDepth ps < n) :
    Safe (ps.mapM (fun p => do
      let k ← evalE env n fr p.1
      let v ← evalE env n fr p.2
      pure (k, v))) (fun _ => True) :=
  (Safe.mapM' (P := fun _ => True) ps fun p hp =>
    Safe.bindT (ih.eval fr p.1 h ((pairs_mem hp).1 hn).1 (by have := (pairs_mem hp).2.1; omega)) fun _ =>
    Safe.bindT (ih.eval fr p.2 h ((pairs_mem hp).1 hn).2 (by have := (pairs_mem hp).2.2; omega)) fun _ =>
    Safe.pure' trivial).weaken (fun _ _ => trivial)

theorem Good.eval_step : ∀ fr e, FrOK fr → e.nonrec = true → e.depth < n + 1 →
    Safe (evalE env (n + 1) fr e) (fun _ => True) := by
  intro fr e h hn hd
  simp only [evalE]
  split
  all_goals simp only [Expr.nonrec, Expr.depth, Bool.and_eq_true] at hn hd
  case h_11 f args kw =>
    obtain ⟨⟨hf, ha⟩, hk⟩ := hn
    cases f
    all_goals simp at hf
    rename_i g
    have hg : g ∈ callableGlobals := by simpa [List.contains_iff_mem] using hf
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.depth] at hd; omega⟩
    refine Safe.bind' (evalE_global env k h hg) fun fv hfv => ?_
    refine Safe.bindT (ih.evals h ha (by omega)) fun av => ?_
    refine Safe.bindT (ih.evalKw h hk (by omega)) fun kv => ?_
    exact Safe.bindT Safe.get' fun _ => Safe.bindT Safe.liftT fun p => ih.call fr fv p.1 p.2 hfv (by omega)
  case h_19 x op y =>
    simp only [opsNonrec, opsDepth, Bool.and_true] at hn hd
    refine Safe.bindT (ih.eval fr x h hn.1 (by omega)) fun _ => ?_
    split
    · exact Safe.compareM'
    refine Safe.bindT (ih.eval fr y h hn.2 (by omega)) fun _ => ?_
    exact Safe.bindT Safe.get' fun _ => Safe.bindT Safe.liftT fun _ => Safe.pure' trivial
  case h_20 x ops _ =>
    refine Safe.bindT (ih.eval fr x h hn.1 (by omega)) fun lv => ?_
    refine Safe.bindT Safe.get' fun hp => ?_
    refine Safe.bindT (Safe.foldlM' (fun _ => True) ops _ (fun b p hp _ => ?_) trivial) fun _ => Safe.pure' trivial
    split
    · exact Safe.pure' trivial
    · refine Safe.bindT (ih.eval fr p.2 h ((ops_mem hp).1 hn.2) (by have := (ops_mem hp).2; omega)) fun _ => ?_
      exact Safe.bindT Safe.liftT fun _ => Safe.pure' trivial
  all_goals safe_steps
  all_goals first
    | exact ih.evals h (by simp_all) (by omega)
    | exact ih.evalKw h (by simp_all) (by omega)
    | exact ih.evalPairs h (by simp_all) (by omega)
    | exact ih.evalOpt h (by simp_all) (by omega)
    | exact ih.eval fr _ h (by simp_all [optNonrec]) (by (try simp only [optDepth] at *); omega)


omit ih in
theorem Good.call_step : ∀ fr f args kw, f.reenters = false → 0 < n + 1 →
    Safe (callV env (n + 1) fr f args kw) (fun _ => True) := by
  intro fr f args kw hf _
  simp only [callV]
  split
  all_goals (try simp [Value.reenters] at hf)
  all_goals safe_steps


omit ih in
theorem FrOK.push_ctx {fr : Frame} (h : FrOK fr) {x : String} (hx : callableGlobals.contains x = false)
    (v : Value) : FrOK { fr with ctx := (x, v) :: fr.ctx } := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun g hg w hw => ?_⟩
  have hne : (g == x) = false := by
    simp only [beq_eq_false_iff_ne]; rintro rfl; simp [List.contains_iff_mem, hg] at hx
  simp only [List.lookup, hne] at hw
  exact h.2.2.2 g hg w hw

theorem Good.assign_step : ∀ fr t v, FrOK fr → t.nonrec = true → t.depth ≤ n + 1 →
    Safe (assignTo env (n + 1) fr t v) FrOK := by
  intro fr t v h hn hd
  cases t with
  | nsAttr ns a =>
    simp only [assignTo]
    split
    · exact Safe.bindT (Safe.modify' _) fun _ => Safe.pure' h
    · exact Safe.throw' (by simp)
  | name x =>
    simp only [Target.nonrec, Bool.not_eq_true'] at hn
    simp only [assignTo]
    split
    · exact Safe.pure' (h.push_ctx hn v)
    · exact Safe.pure' (h.with_locals rfl rfl rfl ⟨[(x, v)], fun p hp => by simp at hp; subst hp; exact hn,
        Or.inl rfl⟩)
  | tuple ts =>
    simp only [Target.nonrec, Target.depth] at hn hd
    simp only [assignTo]
    refine Safe.bindT Safe.get' fun hp => Safe.bindT Safe.liftT fun xs => ?_
    split
    · exact Safe.throw' (by simp)
    · split
      · exact Safe.throw' (by simp)
      · refine Safe.foldlM' FrOK _ _ (fun f p hp hf => ?_) h
        have hm : p.1 ∈ ts := (List.of_mem_zip hp).1
        exact ih.assign f p.1 p.2 hf ((targets_mem hm).1 hn) (by have := (targets_mem hm).2; omega)


theorem Good.chain_step : ∀ fr fs v, FrOK fr → chainNonrec fs = true → chainDepth fs + 1 < n + 1 →
    Safe (applyChain env (n + 1) fr fs v) (fun _ => True) := by
  intro fr fs v h hn hd
  simp only [applyChain]
  refine Safe.foldlM' (fun _ => True) fs v (fun acc f hf _ => ?_) trivial
  have hm := chain_mem hf
  refine Safe.bindT (ih.evals h (hm.1 hn).1 (by omega)) fun _ => ?_
  refine Safe.bindT (ih.evalKw h (hm.1 hn).2 (by omega)) fun _ => ?_
  exact Safe.bindT Safe.get' fun _ => Safe.bindT Safe.liftT fun _ => Safe.applyFilterM'

omit ih in
/-- Binding a non-recursive target makes plain locals. -/
theorem Safe.bindPlain {pol : UndefinedPolicy} {heap : Heap} {t : Target} {v : Value} (ht : t.nonrec = true) :
    Safe (liftR (bindTarget pol heap t v)) Plain :=
  Safe.liftR'.weaken fun bs hbs => bindTarget_keys pol heap t v bs ht hbs

theorem Good.items_step : ∀ fr rec items, FrOK fr → rec.target.nonrec = true → optNonrec rec.filter = true →
    optDepth rec.filter + 1 < n + 1 → Safe (loopItems env (n + 1) fr rec items) (fun _ => True) := by
  intro fr rec items h ht hn hd
  simp only [loopItems]
  split
  · exact Safe.pure' trivial
  · rename_i f hf
    rw [hf] at hn hd
    simp only [optNonrec, optDepth] at hn hd
    refine Safe.filterM' items fun x _ => ?_
    refine Safe.bindT Safe.get' fun heap => Safe.bind' (Safe.bindPlain ht) fun binds hb => ?_
    refine Safe.bindT (ih.eval _ f (h.with_locals rfl rfl rfl ⟨binds, hb, Or.inl rfl⟩) hn (by omega)) fun _ => ?_
    exact Safe.liftT

theorem Good.nodes_step : ∀ fr ns, FrOK fr → nodesNonrec ns = true → 3 * nodesDepth ns + 1 ≤ n + 1 →
    Safe (renderNodes env (n + 1) fr ns) (fun r => FrOK r.2) := by
  intro fr ns h hn hd
  rw [renderNodes_succ]
  refine Safe.bind' (Safe.foldlM' (fun st : List (List Piece) × Frame => FrOK st.2) ns ([], fr)
    (fun st nd hnd hst => ?_) h) fun st hst => ?_
  · obtain ⟨acc, f⟩ := st
    have hm := nodes_mem hnd
    refine Safe.bind' (ih.node f nd hst (hm.1 hn) (by omega)) fun r hr => ?_
    obtain ⟨ps, f'⟩ := r
    exact Safe.pure' hr
  · obtain ⟨cs, f'⟩ := st
    exact Safe.pure' hst

theorem Good.loop_step : ∀ fr rec rc items d, FrOK fr → rec.target.nonrec = true → optNonrec rec.filter = true →
    nodesNonrec rec.body = true → nodesNonrec rec.else_ = true → optDepth rec.filter + 2 < n + 1 →
    3 * max (nodesDepth rec.body) (nodesDepth rec.else_) + 2 ≤ n + 1 →
    Safe (renderLoop env (n + 1) fr rec rc items d) (fun _ => True) := by
  intro fr rec rc items d h ht hf hb he hfd hbd
  simp only [renderLoop]
  have hin : FrOK { fr with top := false } := h.same_locals rfl rfl rfl rfl
  refine Safe.bindT (ih.items _ rec items hin ht hf (by omega)) fun its => ?_
  split
  · refine Safe.bind' (ih.nodes _ rec.else_ hin he (by omega)) fun r _ => ?_
    obtain ⟨ps, _⟩ := r
    exact Safe.pure' trivial
  · refine Safe.bindT Safe.get' fun heap => Safe.bindT (Safe.modify' _) fun _ => ?_
    refine Safe.bindT (Safe.foldlM' (fun _ => True) _ [] (fun acc p _ _ => ?_) trivial) fun _ => Safe.pure' trivial
    obtain ⟨x, loopV⟩ := p
    simp only [bindTargetM_eq]
    refine Safe.bind' (Safe.bindT Safe.get' fun _ => Safe.bindPlain ht) fun binds hbs => ?_
    refine Safe.bind' (ih.nodes _ rec.body ?_ hb (by omega)) fun r _ => ?_
    · split
      · exact h.with_locals rfl rfl rfl ⟨binds ++ [("loop", loopV)], hbs.append (Plain.loop loopV), Or.inl (by simp)⟩
      · exact h.with_locals rfl rfl rfl ⟨binds, hbs, Or.inl (by simp)⟩
    obtain ⟨ps, _⟩ := r
    exact Safe.pure' trivial


theorem Good.node_step : ∀ fr nd, FrOK fr → nd.nonrec = true → 3 * nd.depth ≤ n + 1 →
    Safe (renderNode env (n + 1) fr nd) (fun r => FrOK r.2) := by
  intro fr nd h hn hd
  have hsame : ∀ fr' : Frame, fr'.overrides = fr.overrides → fr'.parent = fr.parent → fr'.ctx = fr.ctx →
      fr'.locals = fr.locals → FrOK fr' := fun fr' a b c d => h.same_locals a b c d
  cases nd with
  | text t => exact Safe.pure' h
  | output e =>
    simp only [Node.nonrec, Node.depth] at hn hd
    simp only [renderNode]
    exact Safe.bindT (ih.eval fr e h hn (by omega)) fun _ => Safe.pure' h
  | if_ bs els =>
    simp only [Node.nonrec, Node.depth, Bool.and_eq_true] at hn hd
    simp only [renderNode]
    refine Safe.bind' (Safe.findM?' bs fun b hb => ?_) fun c hc => ?_
    · have hm := branches_mem hb
      exact Safe.bindT (ih.eval fr b.1 h (hm.1 hn.1).1 (by omega)) fun _ => Safe.liftT
    · cases c with
      | none =>
        exact (ih.nodes fr els h hn.2 (by omega)).weaken fun r hr => hr
      | some b =>
        have hm := branches_mem (hc b rfl)
        exact (ih.nodes fr b.2 h (hm.1 hn.1).2 (by omega)).weaken fun r hr => hr
  | for_ t it f rc body els =>
    simp only [Node.nonrec, Node.depth, Bool.and_eq_true] at hn hd
    have := Target.depth_pos t
    simp only [renderNode]
    refine Safe.bindT (ih.eval fr it h hn.1.1.1.2 (by omega)) fun _ => ?_
    refine Safe.bindT Safe.get' fun _ => Safe.bindT Safe.liftT fun items => ?_
    refine Safe.bindT (ih.loop fr ⟨t, f, body, els⟩ rc items 0 h hn.1.1.1.1 hn.1.1.2 hn.1.2 hn.2
      (by simp only; omega) (by simp only; omega)) fun _ => Safe.pure' h
  | set t e =>
    simp only [Node.nonrec, Node.depth, Bool.and_eq_true] at hn hd
    simp only [renderNode]
    refine Safe.bindT (ih.eval fr e h hn.2 (by omega)) fun v => ?_
    exact Safe.bind' (ih.assign fr t v h hn.1 (by omega)) fun fr' hf' => Safe.pure' hf'
  | setBlock t fs body =>
    simp only [Node.nonrec, Node.depth, Bool.and_eq_true] at hn hd
    simp only [renderNode]
    refine Safe.bind' (ih.nodes _ body (hsame _ rfl rfl rfl rfl) hn.2 (by omega)) fun r _ => ?_
    obtain ⟨ps, _⟩ := r
    refine Safe.bindT Safe.liftT fun _ => ?_
    refine Safe.bindT (ih.chain fr fs _ h hn.1.2 (by omega)) fun v => ?_
    exact Safe.bind' (ih.assign fr t v h hn.1.1 (by omega)) fun fr' hf' => Safe.pure' hf'
  | «macro» => simp [Node.nonrec] at hn
  | callBlock => simp [Node.nonrec] at hn
  | «include» => simp [Node.nonrec] at hn
  | «extends» => simp [Node.nonrec] at hn
  | import_ => simp [Node.nonrec] at hn
  | fromImport => simp [Node.nonrec] at hn
  | block nm sc req body =>
    simp only [Node.nonrec, Node.depth] at hn hd
    simp only [renderNode]
    split
    · exact Safe.pure' h
    · split
      · split
        · exact Safe.throw' (by simp)
        · have hf' : FrOK { fr with locals := if sc then fr.locals else [], top := false, curBlock := some (nm, 0) } :=
            h.with_locals rfl rfl rfl ⟨[], Plain.nil, by cases sc <;> simp⟩
          refine Safe.bind' (ih.nodes _ body hf' hn (by omega)) fun r _ => ?_
          obtain ⟨ps, _⟩ := r
          exact Safe.pure' h
      · rename_i hne
        simp [h.1] at hne
  | with_ as body =>
    simp only [Node.nonrec, Node.depth, Bool.and_eq_true] at hn hd
    simp only [renderNode]
    refine Safe.bind' (Safe.mapM' (P := Plain) as fun a ha => ?_) fun bss hbss => ?_
    · have hm := assigns_mem ha
      refine Safe.bindT (ih.eval fr a.2 h (hm.1 hn.1).2 (by omega)) fun v => ?_
      exact Safe.bindT Safe.get' fun _ => Safe.bindPlain (hm.1 hn.1).1
    · have hf' : FrOK { fr with locals := bss.flatten ++ fr.locals, top := false } :=
        h.with_locals rfl rfl rfl ⟨bss.flatten, Plain.flatten hbss, Or.inl rfl⟩
      refine Safe.bind' (ih.nodes _ body hf' hn.2 (by omega)) fun r _ => ?_
      obtain ⟨ps, _⟩ := r
      exact Safe.pure' h
  | filterBlock fs body =>
    simp only [Node.nonrec, Node.depth, Bool.and_eq_true] at hn hd
    simp only [renderNode]
    refine Safe.bind' (ih.nodes _ body (hsame _ rfl rfl rfl rfl) hn.2 (by omega)) fun r _ => ?_
    obtain ⟨ps, _⟩ := r
    refine Safe.bindT Safe.liftT fun _ => ?_
    exact Safe.bindT (ih.chain fr fs _ h hn.1 (by omega)) fun _ => Safe.pure' h
  | autoescape e body =>
    simp only [Node.nonrec, Node.depth, Bool.and_eq_true] at hn hd
    simp only [renderNode]
    refine Safe.bindT (ih.eval fr e h hn.1 (by omega)) fun _ => Safe.bindT Safe.liftT fun b => ?_
    refine Safe.bind' (ih.nodes _ body (hsame _ rfl rfl rfl rfl) hn.2 (by omega)) fun r _ => ?_
    obtain ⟨ps, _⟩ := r
    exact Safe.pure' h

end Step


/-- The invariant at every fuel. -/
theorem good_all (env : Environment) : ∀ n, Good env n
  | 0 => good_zero env
  | n + 1 =>
    let ih := good_all env n
    { eval := ih.eval_step, call := Good.call_step, assign := ih.assign_step, chain := ih.chain_step,
      items := ih.items_step, nodes := ih.nodes_step, node := ih.node_step, loop := ih.loop_step }

theorem lookup_mem_self {l : List (String × Value)} {g : String} {v : Value} (h : l.lookup g = some v) :
    (g, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p ps ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk; cases h; simp at hk; subst hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem startContext_ok {env : Environment} {vars : List (String × Value)}
    (hctx : ∀ g ∈ callableGlobals, ∀ v, (g, v) ∈ vars ++ env.globals → v.reenters = false) :
    ∀ g ∈ callableGlobals, ∀ v, (env.startContext vars).lookup g = some v → v.reenters = false := by
  intro g hg v hv
  have hm := lookup_mem_self hv
  simp only [Environment.startContext, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact hctx g hg v (List.mem_append_left _ hm)
  · exact hctx g hg v (List.mem_append_right _ hm)
  · simp [builtinGlobals] at hm
    rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

theorem renderTemplate_safe {env : Environment} {base : Frame} (ho : base.overrides = [])
    (hc : ∀ g ∈ callableGlobals, ∀ v, base.ctx.lookup g = some v → v.reenters = false)
    {name : Option String} {body : List Node} (hn : nodesNonrec body = true) {m : Nat}
    (hm : renderBudget body ≤ m) : Safe (renderTemplate env m base name body) (fun _ => True) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by unfold renderBudget at hm; omega⟩
  simp only [renderTemplate]
  refine Safe.bind' ((good_all env k).nodes _ body ⟨ho, rfl, fun _ _ => rfl, hc⟩ hn
    (by unfold renderBudget at hm; omega)) fun r hr => ?_
  obtain ⟨ps, fr'⟩ := r
  simp only
  split
  · exact Safe.pure' trivial
  · rename_i pn hp; rw [hr.2.1] at hp; cases hp

/-- `render_total`: a template that does not recurse (`nodesNonrec`),
rendered with variables that do not bind a callable global to template code,
never raises `RecursionError` once the depth budget covers its nesting
(`renderBudget body = 3 * nodesDepth body + 2`; `Environment.compile`
refuses templates beyond the budget). -/
theorem render_total (t : Template) (vars : List (String × Value)) (hn : nodesNonrec t.body = true)
    (hctx : ∀ g ∈ callableGlobals, ∀ v, (g, v) ∈ vars ++ t.env.globals → v.reenters = false)
    (hb : renderBudget t.body ≤ t.env.maxDepth) : t.render vars ≠ .error .fuelExhausted := by
  have hs := renderTemplate_safe (env := t.env) (base := { ctx := t.env.startContext vars }) rfl
    (startContext_ok hctx) (name := t.name) hn hb (initHeap t.env.randomSeed)
  simp only [Template.render, Template.renderTrace]
  cases hr : (renderTemplate t.env t.env.maxDepth { ctx := t.env.startContext vars } t.name t.body).run (initHeap t.env.randomSeed) with
  | error e =>
    have : e ≠ .fuelExhausted := fun he => hs.1 (he ▸ hr)
    simpa [bind, Except.bind] using this
  | ok r =>
    cases hf : Piece.flatten t.env.undefined r.1.1 with
    | ok _ => simp [bind, Except.bind, hf, Except.mapError]
    | error e => simpa [bind, Except.bind, hf, Except.mapError] using Safe.toRenderError_ne e


/-- A compiled template fits its environment's depth budget. -/
theorem compile_budget {env : Environment} {src : String} {body : List Node}
    (h : env.compile src = .ok body) : renderBudget body ≤ env.maxDepth := by
  unfold Environment.compile at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i b _ hlt
        try dsimp only at h
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h; omega

/-- `render_total` for a template loaded the usual way (`fromString`,
`getTemplate`): compilation already checked the budget. -/
theorem render_total_fromString {env : Environment} {src : String} {t : Template}
    (h : env.fromString src = .ok t) (vars : List (String × Value)) (hn : nodesNonrec t.body = true)
    (hctx : ∀ g ∈ callableGlobals, ∀ v, (g, v) ∈ vars ++ env.globals → v.reenters = false) :
    t.render vars ≠ .error .fuelExhausted := by
  simp only [Environment.fromString, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i body hc
    cases h
    exact render_total _ vars hn hctx (compile_budget hc)

end LeanJinja2
