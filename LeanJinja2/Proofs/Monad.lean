import LeanJinja2.RepoImpl.Render

/-!
# Reasoning about the renderer's monad

`RenderM` is `StateT Heap (Except RenderError)`. These lemmas take a
successful run apart: a bind succeeded because both halves did; a fold
preserved an invariant because every step did.
-/

namespace LeanJinja2

theorem Except.bind_eq_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x.bind f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Except.bind]

theorem StateT.run_bind_ok {σ ε α β : Type} {x : StateT σ (Except ε) α} {f : α → StateT σ (Except ε) β}
    {s s'' : σ} {b : β} :
    (x >>= f) s = .ok (b, s'') ↔ ∃ a s', x s = .ok (a, s') ∧ f a s' = .ok (b, s'') := by
  simp only [bind, StateT.bind, Except.bind_eq_ok_iff]
  constructor
  · rintro ⟨⟨a, s'⟩, h1, h2⟩; exact ⟨a, s', h1, h2⟩
  · rintro ⟨a, s', h1, h2⟩; exact ⟨(a, s'), h1, h2⟩

theorem StateT.run_pure_ok {σ ε α : Type} {a b : α} {s s' : σ} :
    (pure a : StateT σ (Except ε) α) s = .ok (b, s') ↔ a = b ∧ s = s' := by
  simp [pure, StateT.pure, Except.pure]

theorem liftR_ok {α : Type} {x : Except RenderError α} {s s' : Heap} {a : α} :
    liftR x s = .ok (a, s') ↔ x = .ok a ∧ s = s' := by
  cases x <;> simp [liftR, pure, StateT.pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    StateT.lift, Except.bind, bind]

/-- A monadic left fold over a list preserves an invariant that every step
preserves. -/
theorem foldlM_inv {σ ε α β : Type} (P : β → Prop) (f : β → α → StateT σ (Except ε) β) :
    ∀ (xs : List α), (∀ b a s b' s', a ∈ xs → P b → f b a s = .ok (b', s') → P b') →
    ∀ init s r s', P init → xs.foldlM f init s = .ok (r, s') → P r
  | [], _, init, s, r, s', hp, h => by
    simp [List.foldlM, pure, StateT.pure, Except.pure] at h
    rw [← h.1]; exact hp
  | a :: as, hstep, init, s, r, s', hp, h => by
    simp only [List.foldlM, StateT.run_bind_ok] at h
    obtain ⟨b, s1, h1, h2⟩ := h
    exact foldlM_inv P f as (fun b x s b' s' hx => hstep b x s b' s' (List.mem_cons_of_mem a hx))
      b s1 r s' (hstep init a s b s1 List.mem_cons_self hp h1) h2

/-- `findM?` only finds members. -/
theorem findM?_mem {σ ε α : Type} (p : α → StateT σ (Except ε) Bool) :
    ∀ (xs : List α) (s s' : σ) (x : α), xs.findM? p s = .ok (some x, s') → x ∈ xs
  | [], s, s', x, h => by simp [List.findM?, pure, StateT.pure, Except.pure] at h
  | a :: as, s, s', x, h => by
    simp only [List.findM?, StateT.run_bind_ok] at h
    obtain ⟨b, s1, _, h2⟩ := h
    cases b with
    | true =>
      simp [pure, StateT.pure, Except.pure] at h2
      rw [← h2.1]; exact List.mem_cons_self
    | false =>
      exact List.mem_cons_of_mem a (findM?_mem p as s1 s' x h2)

end LeanJinja2
