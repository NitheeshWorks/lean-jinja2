import LeanJinja2.Proofs.Monad
import LeanJinja2.Proofs.AstWalk

/-!
# What the renderer emits

One invariant, proved once for all the renderer's trace-producing functions
by induction on the depth budget: every literal piece of a trace is literal
text of the template set, and (when autoescaping is on throughout) every
interpolated piece carries the escape flag. `render_literals` and
`autoescape_sound` are its two readings.
-/

namespace LeanJinja2

set_option linter.unusedSimpArgs false

open LeanMarkupsafe

section Invariant

variable (env : Environment) (L : String → Prop) (ae : Bool)

/-- A body whose literal text satisfies `L`, without `{% autoescape %}` tags
when `ae`. -/
def BodyOK (body : List Node) : Prop :=
  ∀ f ∈ factsOf body, match f with
    | .text s => L s
    | .autoescapeTag => ae = false

def EntryOK (be : BlockEntry) : Prop := BodyOK L ae be.body ∧ (ae = true → be.autoescape = true)

def FrameOK (fr : Frame) : Prop :=
  (∀ p ∈ fr.overrides, ∀ be ∈ p.2, EntryOK L ae be) ∧ (∀ p ∈ fr.own, EntryOK L ae p.2) ∧
    (ae = true → fr.autoescape = true)

def TraceOK (ps : List Piece) : Prop :=
  ∀ p ∈ ps, match p with
    | .lit s => L s
    | .value _ esc => ae = true → esc = true

def EnvOK : Prop :=
  (∀ name src body, env.getSource name = .ok src → env.compile src = .ok body → BodyOK L ae body) ∧
    (ae = true → env.autoescape = .const true)

/-- Two frames that agree on what the invariant reads. -/
def Same (fr fr' : Frame) : Prop :=
  fr'.overrides = fr.overrides ∧ fr'.own = fr.own ∧ fr'.autoescape = fr.autoescape ∧ fr'.top = fr.top

end Invariant

theorem Same.refl (fr : Frame) : Same fr fr := ⟨rfl, rfl, rfl, rfl⟩

theorem Same.trans {a b c : Frame} (h1 : Same a b) (h2 : Same b c) : Same a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem FrameOK.of_same {L ae} {fr fr' : Frame} (h : FrameOK L ae fr) (hs : Same fr fr') :
    FrameOK L ae fr' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨e1, e2, e3, _⟩ := hs
  exact ⟨e1 ▸ h1, e2 ▸ h2, fun ha => e3 ▸ h3 ha⟩

theorem TraceOK.nil {L ae} : TraceOK L ae [] := fun _ h => by cases h

theorem TraceOK.append {L ae} {a b : List Piece} (ha : TraceOK L ae a) (hb : TraceOK L ae b) :
    TraceOK L ae (a ++ b) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact ha p h
  · exact hb p h

theorem BodyOK.node {L ae} {body : List Node} {n : Node} (h : BodyOK L ae body) (hn : n ∈ body) :
    BodyOK L ae [n] := fun f hf => h f (by
      simp only [factsOf, nodesCollect, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hf
      simp only [factsOf, nodesCollect, List.mem_flatMap]
      exact ⟨n, hn, hf⟩)

theorem BodyOK.sub {L ae} {n : Node} {sub : List Node} (h : BodyOK L ae [n])
    (hs : ∀ x ∈ sub, x ∈ n.children) : BodyOK L ae sub :=
  fun f hf => h f (factsOf_sub n List.mem_cons_self hs hf)

theorem BodyOK.text {L ae} {n : Node} {s : String} (h : BodyOK L ae [n]) (hf : Fact.text s ∈ n.fact) :
    L s :=
  h _ (factsOf_node List.mem_cons_self hf)

theorem BodyOK.tag {L ae} {n : Node} (h : BodyOK L ae [n]) (hf : Fact.autoescapeTag ∈ n.fact) :
    ae = false :=
  h _ (factsOf_node List.mem_cons_self hf)

@[simp] theorem throw_run {α : Type} (e : RenderError) (s : Heap) :
    (throw e : RenderM α) s = .error e := rfl

@[simp] theorem lift_error_run {α : Type} (e : RenderError) (s : Heap) :
    (StateT.lift (Except.error e) : RenderM α) s = .error e := rfl

theorem lookup_mem {α β : Type} [BEq α] {l : List (α × β)} {a : α} {b : β} (h : l.lookup a = some b) :
    ∃ k, (k, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.lookup] at h
    split at h
    · cases h; exact ⟨k, List.mem_cons_self⟩
    · obtain ⟨k', hk⟩ := ih h; exact ⟨k', List.mem_cons_of_mem _ hk⟩

theorem FrameOK.chain {L ae} {fr : Frame} (h : FrameOK L ae fr) {b : String} {be : BlockEntry}
    (hb : be ∈ fr.chain b) : EntryOK L ae be := by
  simp only [Frame.chain, List.mem_append] at hb
  rcases hb with hb | hb
  · cases hl : fr.overrides.lookup b with
    | none => simp [hl] at hb
    | some es =>
      simp [hl] at hb
      obtain ⟨k, hk⟩ := lookup_mem hl
      exact h.1 (k, es) hk be hb
  · cases hl : fr.own.lookup b with
    | none => simp [hl] at hb
    | some e =>
      simp [hl] at hb
      obtain ⟨k, hk⟩ := lookup_mem hl
      exact hb ▸ h.2.1 (k, e) hk

theorem assignTo_same (env : Environment) :
    ∀ n fr t v s fr' s', assignTo env n fr t v s = .ok (fr', s') → Same fr fr'
  | 0, fr, t, v, s, fr', s', h => by simp [assignTo] at h
  | n + 1, fr, t, v, s, fr', s', h => by
    cases t with
    | name x =>
      simp only [assignTo, StateT.run_pure_ok] at h
      split at h <;> (obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl, rfl⟩)
    | nsAttr ns a =>
      unfold assignTo at h
      simp only at h
      cases hl : fr.lookup? ns with
      | none => simp [hl] at h
      | some w =>
        cases w <;> simp [hl] at h
        simp only [StateT.run_bind_ok, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          StateT.run_pure_ok] at h
        obtain ⟨_, _, _, rfl, -⟩ := h
        exact Same.refl fr
    | tuple ts =>
      simp only [assignTo, StateT.run_bind_ok] at h
      obtain ⟨hp, s1, -, h⟩ := h
      obtain ⟨xs, s2, -, h⟩ := h
      split at h
      · simp at h
      · split at h
        · simp at h
        · exact foldlM_inv (fun f => Same fr f) _ _
            (fun b p s b' s' _ hb hstep => hb.trans (assignTo_same env n b p.1 p.2 s b' s' hstep))
            fr s2 fr' s' (Same.refl fr) h

end LeanJinja2

namespace LeanJinja2

theorem findSome_source {env : Environment} {names : List String} {nm src : String}
    (h : names.findSome? (fun nm => (env.getSource nm).toOption.map (nm, ·)) = some (nm, src)) :
    env.getSource nm = .ok src := by
  induction names with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.findSome?_cons] at h
    cases hx : env.getSource x with
    | error e => simp [hx, Except.toOption] at h; exact ih h
    | ok v => simp [hx, Except.toOption] at h; obtain ⟨rfl, rfl⟩ := h; exact hx

theorem mergeOverrides_mem {old : List (String × List BlockEntry)} {own : List (String × BlockEntry)}
    {p : String × List BlockEntry} (hp : p ∈ mergeOverrides old own) {be : BlockEntry} (hb : be ∈ p.2) :
    (∃ q ∈ old, be ∈ q.2) ∨ ∃ k, (k, be) ∈ own := by
  unfold mergeOverrides at hp
  induction own generalizing old with
  | nil => exact Or.inl ⟨p, hp, hb⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at hp
    rcases ih hp with ⟨q, hq, hbq⟩ | ⟨k, hk⟩
    · -- q is in the accumulator after inserting x
      split at hq
      · simp only [List.mem_map] at hq
        obtain ⟨q0, hq0, rfl⟩ := hq
        split at hbq
        · simp only [List.mem_append, List.mem_singleton] at hbq
          rcases hbq with hbq | rfl
          · rename_i l hl _
            obtain ⟨k, hk⟩ := lookup_mem hl
            exact Or.inl ⟨_, hk, hbq⟩
          · exact Or.inr ⟨x.1, List.mem_cons_self⟩
        · exact Or.inl ⟨q0, hq0, hbq⟩
      · simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact Or.inl ⟨q, hq, hbq⟩
        · simp at hbq; exact Or.inr ⟨x.1, hbq ▸ List.mem_cons_self⟩
    · exact Or.inr ⟨k, List.mem_cons_of_mem _ hk⟩

end LeanJinja2

namespace LeanJinja2

open LeanMarkupsafe


/-- The invariant at one depth budget. -/
def Inv (env : Environment) (L : String → Prop) (ae : Bool) (n : Nat) : Prop :=
  (∀ fr body s r s', FrameOK L ae fr → BodyOK L ae body →
     renderNodes env n fr body s = .ok (r, s') → TraceOK L ae r.1 ∧ Same fr r.2) ∧
  (∀ fr node s r s', FrameOK L ae fr → BodyOK L ae [node] →
     renderNode env n fr node s = .ok (r, s') → TraceOK L ae r.1 ∧ Same fr r.2) ∧
  (∀ fr rec rc items d s ps s', FrameOK L ae fr → BodyOK L ae rec.body → BodyOK L ae rec.else_ →
     renderLoop env n fr rec rc items d s = .ok (ps, s') → TraceOK L ae ps) ∧
  (∀ fr b i locals s ps s', FrameOK L ae fr →
     renderBlockAt env n fr b i locals s = .ok (ps, s') → TraceOK L ae ps) ∧
  (∀ base name body s ps s', (∀ p ∈ base.overrides, ∀ be ∈ p.2, EntryOK L ae be) → BodyOK L ae body →
     renderTemplate env n base name body s = .ok (ps, s') → TraceOK L ae ps)

theorem inv_nodes_step {env L ae n} (ih : Inv env L ae n) :
    ∀ fr body s r s', FrameOK L ae fr → BodyOK L ae body →
     renderNodes env (n + 1) fr body s = .ok (r, s') → TraceOK L ae r.1 ∧ Same fr r.2 := by
  intro fr body s r s' hf hb h
  simp only [renderNodes] at h
  exact foldlM_inv (fun (st : List Piece × Frame) => TraceOK L ae st.1 ∧ Same fr st.2) _ body
    (fun ⟨acc, f⟩ node s ⟨acc', f'⟩ s' hn ⟨ht, hs⟩ hstep => by
      simp only [StateT.run_bind_ok, StateT.run_pure_ok] at hstep
      obtain ⟨⟨ps, f2⟩, s2, h1, h2⟩ := hstep
      obtain ⟨hp, hs2⟩ := ih.2.1 f node s (ps, f2) s2 (hf.of_same hs) (hb.node hn) h1
      simp only [Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h2
      refine ⟨?_, hs.trans hs2⟩
      split
      · exact ht
      · exact ht.append hp)
    ([], fr) s r s' ⟨TraceOK.nil, Same.refl fr⟩ h

theorem inv_node_step {env L ae n} (hE : EnvOK env L ae) (ih : Inv env L ae n) :
    ∀ fr node s r s', FrameOK L ae fr → BodyOK L ae [node] →
     renderNode env (n + 1) fr node s = .ok (r, s') → TraceOK L ae r.1 ∧ Same fr r.2 := by
  intro fr node s r s' hf hb h
  cases node with
  | text t =>
    simp only [renderNode, StateT.run_pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨?_, Same.refl fr⟩
    intro p hp; simp at hp; subst hp; exact hb.text (by simp [Node.fact])
  | output e =>
    simp only [renderNode, StateT.run_bind_ok, StateT.run_pure_ok] at h
    obtain ⟨v, s1, -, rfl, -⟩ := h
    refine ⟨?_, Same.refl fr⟩
    intro p hp; simp at hp; subst hp; exact hf.2.2
  | if_ bs els =>
    simp only [renderNode, StateT.run_bind_ok] at h
    obtain ⟨c, s1, hc, h⟩ := h
    have hbody : BodyOK L ae ((Option.map Prod.snd c).getD els) := by
      apply hb.sub
      intro x hx
      cases c with
      | none => simp [Node.children] at hx ⊢; exact Or.inr hx
      | some b =>
        have := findM?_mem _ bs s s1 b hc
        simp [Node.children] at hx ⊢
        exact Or.inl ⟨b.1, b.2, this, hx⟩
    exact ih.1 fr _ s1 r s' hf hbody h
  | for_ t it fl rc body els =>
    simp only [renderNode, StateT.run_bind_ok, StateT.run_pure_ok, liftR_ok] at h
    obtain ⟨_, _, -, _, _, -, _, _, -, ps, _, hl, rfl, -⟩ := h
    refine ⟨ih.2.2.1 fr _ rc _ 0 _ ps _ hf (hb.sub ?_) (hb.sub ?_) hl, Same.refl fr⟩ <;>
      intro x hx <;> simp [Node.children, hx]
  | set t e =>
    simp only [renderNode, StateT.run_bind_ok, StateT.run_pure_ok] at h
    obtain ⟨_, _, -, f', _, ha, rfl, -⟩ := h
    exact ⟨TraceOK.nil, assignTo_same env n fr t _ _ f' _ ha⟩
  | setBlock t fs body =>
    simp only [renderNode, StateT.run_bind_ok, StateT.run_pure_ok, liftR_ok] at h
    obtain ⟨_, _, -, _, _, -, _, _, -, f', _, ha, rfl, -⟩ := h
    exact ⟨TraceOK.nil, assignTo_same env n fr t _ _ f' _ ha⟩
  | «macro» nm ps body =>
    simp only [renderNode, StateT.run_bind_ok, StateT.run_pure_ok] at h
    obtain ⟨f', _, ha, rfl, -⟩ := h
    exact ⟨TraceOK.nil, assignTo_same env n fr _ _ _ f' _ ha⟩
  | callBlock ps c body =>
    cases c
    case call f args kw =>
      simp only [renderNode, StateT.run_bind_ok, StateT.run_pure_ok] at h
      obtain ⟨_, _, -, _, _, -, _, _, -, _, _, -, rfl, -⟩ := h
      refine ⟨?_, Same.refl fr⟩
      intro p hp; simp at hp; subst hp; exact hf.2.2
    all_goals simp [renderNode] at h
  | «include» e ig wc =>
    simp only [renderNode, StateT.run_bind_ok, liftR_ok] at h
    obtain ⟨v, s1, -, _, s2, -, names, s3, -, h⟩ := h
    cases hfs : names.findSome? (fun nm => (env.getSource nm).toOption.map (nm, ·)) with
    | none =>
      simp only [hfs] at h
      split at h
      · simp only [StateT.run_pure_ok] at h; obtain ⟨rfl, -⟩ := h; exact ⟨TraceOK.nil, Same.refl fr⟩
      · split at h <;> simp at h
    | some p =>
      obtain ⟨nm, src⟩ := p
      simp only [hfs, StateT.run_bind_ok, StateT.run_pure_ok, liftR_ok] at h
      obtain ⟨body, _, ⟨hc, rfl⟩, ps, _, ht, rfl, -⟩ := h
      exact ⟨ih.2.2.2.2 _ _ body _ ps _ (by simp) (hE.1 nm src body (findSome_source hfs) hc) ht,
        Same.refl fr⟩
  | «extends» e =>
    simp only [renderNode] at h
    split at h
    · simp at h
    · simp only [StateT.run_bind_ok, StateT.run_pure_ok, liftR_ok] at h
      obtain ⟨_, _, -, _, _, -, rfl, -⟩ := h
      exact ⟨TraceOK.nil, rfl, rfl, rfl, rfl⟩
  | block nm sc req body =>
    simp only [renderNode] at h
    split at h
    · simp only [StateT.run_pure_ok] at h; obtain ⟨rfl, -⟩ := h; exact ⟨TraceOK.nil, Same.refl fr⟩
    · split at h
      · split at h
        · simp at h
        · simp only [StateT.run_bind_ok, StateT.run_pure_ok] at h
          obtain ⟨⟨ps, f2⟩, _, hr, rfl, -⟩ := h
          have hf' : FrameOK L ae { fr with locals := if sc then fr.locals else [], top := false, curBlock := some (nm, 0) } :=
            ⟨hf.1, hf.2.1, hf.2.2⟩
          exact ⟨(ih.1 _ body _ _ _ hf' (hb.sub (fun x hx => by simpa [Node.children] using hx)) hr).1,
            Same.refl fr⟩
      · simp only [StateT.run_bind_ok, StateT.run_pure_ok] at h
        obtain ⟨ps, _, hr, rfl, -⟩ := h
        exact ⟨ih.2.2.2.1 fr nm 0 _ _ ps _ hf hr, Same.refl fr⟩
  | with_ as body =>
    simp only [renderNode, StateT.run_bind_ok, StateT.run_pure_ok] at h
    obtain ⟨binds, _, -, ⟨ps, f2⟩, _, hr, rfl, -⟩ := h
    have hf' : FrameOK L ae { fr with locals := binds.flatten ++ fr.locals, top := false } :=
      ⟨hf.1, hf.2.1, hf.2.2⟩
    exact ⟨(ih.1 _ body _ _ _ hf' (hb.sub (fun x hx => by simpa [Node.children] using hx)) hr).1,
      Same.refl fr⟩
  | filterBlock fs body =>
    simp only [renderNode, StateT.run_bind_ok, StateT.run_pure_ok, liftR_ok] at h
    obtain ⟨_, _, -, _, _, -, _, _, -, rfl, -⟩ := h
    refine ⟨?_, Same.refl fr⟩
    intro p hp; simp at hp; subst hp; exact hf.2.2
  | autoescape e body =>
    simp only [renderNode, StateT.run_bind_ok, StateT.run_pure_ok, liftR_ok] at h
    obtain ⟨_, _, -, b, _, -, ⟨ps, f2⟩, _, hr, rfl, -⟩ := h
    have hae : ae = false := hb.tag (by simp [Node.fact])
    have hf' : FrameOK L ae { fr with autoescape := b, top := false } :=
      ⟨hf.1, hf.2.1, fun h => by simp [hae] at h⟩
    exact ⟨(ih.1 _ body _ _ _ hf' (hb.sub (fun x hx => by simpa [Node.children] using hx)) hr).1,
      Same.refl fr⟩
theorem inv_loop_step {env L ae n} (ih : Inv env L ae n) :
    ∀ fr rec rc items d s ps s', FrameOK L ae fr → BodyOK L ae rec.body → BodyOK L ae rec.else_ →
     renderLoop env (n + 1) fr rec rc items d s = .ok (ps, s') → TraceOK L ae ps := by
  intro fr rec rc items d s ps s' hf hb he h
  simp only [renderLoop, StateT.run_bind_ok] at h
  obtain ⟨its, s1, -, h⟩ := h
  have hin : FrameOK L ae { fr with top := false } := ⟨hf.1, hf.2.1, hf.2.2⟩
  split at h
  · simp only [StateT.run_bind_ok, StateT.run_pure_ok] at h
    obtain ⟨⟨ps', f2⟩, _, hr, rfl, -⟩ := h
    exact (ih.1 _ _ _ _ _ hin he hr).1
  · simp only [StateT.run_bind_ok, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      StateT.run_pure_ok] at h
    obtain ⟨_, _, -, _, _, -, h⟩ := h
    refine foldlM_inv (TraceOK L ae) _ _ (fun acc p s acc' s' _ hacc hstep => ?_) [] _ ps s' TraceOK.nil h
    simp only [StateT.run_bind_ok, StateT.run_pure_ok, liftR_ok] at hstep
    obtain ⟨_, _, -, binds, _, -, ⟨ps2, f2⟩, _, hr, rfl, -⟩ := hstep
    refine hacc.append (ih.1 _ _ _ _ _ ?_ hb hr).1
    exact ⟨hf.1, hf.2.1, hf.2.2⟩

theorem inv_block_step {env L ae n} (ih : Inv env L ae n) :
    ∀ fr b i locals s ps s', FrameOK L ae fr →
     renderBlockAt env (n + 1) fr b i locals s = .ok (ps, s') → TraceOK L ae ps := by
  intro fr b i locals s ps s' hf h
  simp only [renderBlockAt] at h
  cases hc : (fr.chain b)[i]? with
  | none => simp [hc] at h
  | some be =>
    simp only [hc] at h
    split at h
    · simp at h
    · simp only [StateT.run_bind_ok, StateT.run_pure_ok] at h
      obtain ⟨⟨ps', f2⟩, _, hr, rfl, -⟩ := h
      have he := hf.chain (List.mem_of_getElem? hc)
      refine (ih.1 _ _ _ _ _ ?_ he.1 hr).1
      exact ⟨hf.1, hf.2.1, he.2⟩

theorem inv_tmpl_step {env L ae n} (hE : EnvOK env L ae) (ih : Inv env L ae n) :
    ∀ base name body s ps s', (∀ p ∈ base.overrides, ∀ be ∈ p.2, EntryOK L ae be) → BodyOK L ae body →
     renderTemplate env (n + 1) base name body s = .ok (ps, s') → TraceOK L ae ps := by
  intro base name body s ps s' ho hb h
  simp only [renderTemplate, StateT.run_bind_ok] at h
  obtain ⟨⟨ps1, f1⟩, s1, hr, h⟩ := h
  have hae : ae = true → env.autoescape.enabledFor name = true := by
    intro ha; rw [hE.2 ha]; rfl
  have hown : ∀ p ∈ (blockDefs body).map (fun x => (x.1, BlockEntry.mk x.2.2.2 (env.autoescape.enabledFor name) x.2.2.1)),
      EntryOK L ae p.2 := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨⟨b, sc, req, bb⟩, hmem, rfl⟩ := hp
    exact ⟨fun f hf => hb f (blockDefs_facts hmem hf), hae⟩
  have hfr := ih.1 _ body _ _ _ ?_ hb hr
  rotate_left
  · exact ⟨ho, hown, hae⟩
  simp only at hfr
  cases hp : f1.parent with
  | none =>
    simp only [hp, StateT.run_pure_ok] at h
    obtain ⟨rfl, -⟩ := h
    exact hfr.1
  | some pn =>
    simp only [hp, StateT.run_bind_ok, StateT.run_pure_ok, liftR_ok] at h
    obtain ⟨src, _, ⟨hsrc, rfl⟩, pbody, _, ⟨hc, rfl⟩, pps, _, ht, rfl, -⟩ := h
    refine hfr.1.append (ih.2.2.2.2 _ _ pbody _ pps _ ?_ (hE.1 pn src pbody hsrc hc) ht)
    intro p hp' be hbe
    rcases mergeOverrides_mem hp' hbe with ⟨q, hq, hbq⟩ | ⟨k, hk⟩
    · exact ho q hq be hbq
    · exact hown (k, be) hk

theorem inv_zero (env L ae) : Inv env L ae 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [renderNodes, renderNode, renderLoop,
    renderBlockAt, renderTemplate]

/-- The invariant holds at every depth budget. -/
theorem inv_all {env L ae} (hE : EnvOK env L ae) : ∀ n, Inv env L ae n
  | 0 => inv_zero env L ae
  | n + 1 =>
    let ih := inv_all hE n
    ⟨inv_nodes_step ih, inv_node_step hE ih, inv_loop_step ih, inv_block_step ih, inv_tmpl_step hE ih⟩

theorem text_mem_textsOf {body : List Node} {s : String} (h : Fact.text s ∈ factsOf body) :
    s ∈ textsOf body := by
  simp only [textsOf, List.mem_filterMap]
  exact ⟨_, h, rfl⟩

/-- A template's trace satisfies the invariant. -/
theorem renderTrace_inv {t : Template} {vars : List (String × Value)} {ps : List Piece}
    {L : String → Prop} {ae : Bool} (hE : EnvOK t.env L ae) (hb : BodyOK L ae t.body)
    (h : t.renderTrace vars = .ok ps) : TraceOK L ae ps := by
  simp only [Template.renderTrace] at h
  split at h
  · rename_i r _ hr
    simp only [Except.ok.injEq] at h
    subst h
    exact (inv_all hE _).2.2.2.2 _ _ _ _ _ _ (by simp) hb hr
  · cases h

/-- `render_literals`: every literal piece of a rendered trace is literal
template text, of the template or of one its loader holds. -/
theorem render_literals (t : Template) (vars : List (String × Value)) (ps : List Piece) (s : String)
    (h : t.renderTrace vars = .ok ps) (hs : Piece.lit s ∈ ps) : Literal t.env t.body s := by
  have hE : EnvOK t.env (Literal t.env t.body) false :=
    ⟨fun name src body h1 h2 f hf => by
      cases f with
      | text s => exact Or.inr ⟨name, src, body, h1, h2, text_mem_textsOf hf⟩
      | autoescapeTag => rfl, fun h => by cases h⟩
  have hb : BodyOK (Literal t.env t.body) false t.body := fun f hf => by
    cases f with
    | text s => exact Or.inl (text_mem_textsOf hf)
    | autoescapeTag => rfl
  exact renderTrace_inv hE hb h _ hs

theorem escapeOf_nonmarkup {pol : UndefinedPolicy} {v : Value} (hv : v.isMarkup = false) :
    escapeOf pol v = (strOf pol v >>= fun s => pure (escape s)) := by
  cases v <;> simp_all [escapeOf, Value.isMarkup]

theorem escaped_nonmarkup {pol : UndefinedPolicy} {v : Value} {e : Bool} (hv : v.isMarkup = false) :
    Piece.escaped pol (.value v e) = (escape (v.display pol)).str := by
  cases v <;> simp_all [Piece.escaped, Value.isMarkup]

/-- An escaped piece's text is its escaped reading. -/
theorem Piece.text_escaped {pol : UndefinedPolicy} {p : Piece} {t : String}
    (hp : ∀ v esc, p = .value v esc → esc = true) (h : Piece.text pol p = .ok t) :
    t = p.escaped pol := by
  cases p with
  | lit s => simp [Piece.text] at h; simp [Piece.escaped, h]
  | value v esc =>
    have := hp v esc rfl
    subst this
    cases hm : v.isMarkup with
    | true =>
      cases v <;> simp [Value.isMarkup] at hm
      simp [Piece.text, escapeOf, Functor.map, Except.map] at h; simp [Piece.escaped, h]
    | false =>
      rw [escaped_nonmarkup hm]
      simp only [Piece.text, escapeOf_nonmarkup hm, bind, Except.bind] at h
      cases hs : strOf pol v with
      | error e => simp [hs] at h
      | ok s => simp [hs, pure, Except.pure] at h; simp [Value.display, hs, h]

theorem mapM_text_escaped {pol : UndefinedPolicy} :
    ∀ (ps : List Piece) (ts : List String), (∀ p ∈ ps, ∀ v esc, p = .value v esc → esc = true) →
      ps.mapM (Piece.text pol) = .ok ts → ts = ps.map (Piece.escaped pol)
  | [], ts, _, h => by
    rw [List.mapM_nil] at h; simp [pure, Except.pure] at h; simp [h]
  | p :: ps, ts, hp, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i t ht
      split at h
      · cases h
      · rename_i ts' hts
        simp [pure, Except.pure] at h
        subst h
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨Piece.text_escaped (hp p List.mem_cons_self) ht,
          mapM_text_escaped ps ts' (fun q hq => hp q (List.mem_cons_of_mem p hq)) hts⟩

/-- `autoescape_sound`: with autoescaping on throughout, the output of
`render` is the trace's literal text with each interpolated value replaced by
its escape (markup values unchanged). -/
theorem autoescape_sound (t : Template) (vars : List (String × Value)) (out : String)
    (hae : AutoescapeAlways t.env t.body) (h : t.render vars = .ok out) :
    ∃ ps, t.renderTrace vars = .ok ps ∧ out = String.join (ps.map (Piece.escaped t.env.undefined)) := by
  obtain ⟨hconst, hroot, hloaded⟩ := hae
  simp only [Template.render, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i ps hps
    refine ⟨ps, hps, ?_⟩
    have hE : EnvOK t.env (fun _ => True) true :=
      ⟨fun name src body h1 h2 f hf => by
        cases f with
        | text _ => trivial
        | autoescapeTag => exact absurd hf (hloaded name src body h1 h2), fun _ => hconst⟩
    have hb : BodyOK (fun _ => True) true t.body := fun f hf => by
      cases f with
      | text _ => trivial
      | autoescapeTag => exact absurd hf hroot
    have hinv := renderTrace_inv hE hb hps
    simp only [Piece.flatten, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i ts hts
      simp [pure, Except.pure] at h
      rw [← h, mapM_text_escaped ps ts (fun p hp v esc he => by
        have := hinv p hp; subst he; exact this rfl) hts]

/-- `autoescape_escaped`: what an interpolated non-markup value contributes
under autoescaping satisfies lean-markupsafe's `IsEscaped`. -/
theorem autoescape_escaped (pol : UndefinedPolicy) (p : Piece) (hp : p.IsPlainValue) :
    IsEscaped (p.escaped pol) := by
  cases p with
  | lit _ => cases hp
  | value v esc =>
    cases v with
    | markup _ => cases hp
    | _ => exact escape_sound _

/-- `markup_passthrough`: an interpolated markup value contributes its own
text, whether or not autoescaping is on. -/
theorem markup_passthrough (pol : UndefinedPolicy) (m : Markup) (esc : Bool) :
    Piece.text pol (.value (.markup m) esc) = .ok m.str := by
  cases esc <;> rfl

end LeanJinja2
