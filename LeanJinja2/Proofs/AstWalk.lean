import LeanJinja2.Specifications.Render

/-!
# Lemmas about walking the AST

A node's children (the bodies nested in it) contribute their facts to the
node's own: one lemma, used by every case of the renderer proofs.
-/

namespace LeanJinja2

set_option linter.unusedSimpArgs false

/-- The nodes directly nested in a node: every body it holds. -/
def Node.children : Node → List Node
  | .if_ bs els => bs.flatMap (·.2) ++ els
  | .for_ _ _ _ _ body els => body ++ els
  | .setBlock _ _ body | .macro _ _ body | .callBlock _ _ body | .block _ _ _ body
  | .with_ _ body | .filterBlock _ body | .autoescape _ body => body
  | _ => []

theorem collect_child {α : Type} (f : Expr → List α) (g : Node → List α) {n x : Node}
    (hx : x ∈ n.children) {y : α} (hy : y ∈ Node.collect f g x) : y ∈ Node.collect f g n := by
  unfold Node.collect at *
  cases n with
  | if_ bs els =>
    rw [Node.collectS.eq_def]
    simp only [Node.children, List.mem_append, List.mem_flatMap] at hx
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_flatMap, List.mem_attach,
      true_and, Subtype.exists]
    rcases hx with ⟨b, hb, hxb⟩ | hx
    · exact Or.inr (Or.inl ⟨b, hb, Or.inr ⟨x, hxb, hy⟩⟩)
    · exact Or.inr (Or.inr ⟨x, hx, hy⟩)
  | for_ t it fl r body els =>
    rw [Node.collectS.eq_def]
    simp only [Node.children, List.mem_append] at hx
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_flatMap, List.mem_attach,
      true_and, Subtype.exists]
    rcases hx with hx | hx
    · exact Or.inr (Or.inl (Or.inr ⟨x, hx, hy⟩))
    · exact Or.inr (Or.inr ⟨x, hx, hy⟩)
  | setBlock _ _ body | «macro» _ _ body | callBlock _ _ body | block _ _ _ body | with_ _ body
  | filterBlock _ body | autoescape _ body =>
    rw [Node.collectS.eq_def]
    simp only [Node.children] at hx
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_flatMap, List.mem_attach,
      true_and, Subtype.exists]
    first
    | exact Or.inr (Or.inr ⟨x, hx, hy⟩)
    | exact Or.inr ⟨x, hx, hy⟩
  | _ => simp [Node.children] at hx

/-- The facts of a child body are facts of the parent body. -/
theorem factsOf_child {body : List Node} {n : Node} (hn : n ∈ body) {x : Node} (hx : x ∈ n.children)
    {fct : Fact} (h : fct ∈ factsOf [x]) : fct ∈ factsOf body := by
  simp only [factsOf, nodesCollect, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
  simp only [factsOf, nodesCollect, List.mem_flatMap]
  exact ⟨n, hn, collect_child _ _ hx h⟩

theorem factsOf_sub {body sub : List Node} (n : Node) (hn : n ∈ body) (hsub : ∀ x ∈ sub, x ∈ n.children)
    {fct : Fact} (h : fct ∈ factsOf sub) : fct ∈ factsOf body := by
  simp only [factsOf, nodesCollect, List.mem_flatMap] at h
  obtain ⟨x, hx, hf⟩ := h
  exact factsOf_child hn (hsub x hx) (by simpa [factsOf, nodesCollect] using hf)

theorem factsOf_node {body : List Node} {n : Node} (hn : n ∈ body) {fct : Fact}
    (h : fct ∈ n.fact) : fct ∈ factsOf body := by
  simp only [factsOf, nodesCollect, List.mem_flatMap]
  refine ⟨n, hn, ?_⟩
  unfold Node.collect; rw [Node.collectS.eq_def]
  simp [h]

end LeanJinja2

namespace LeanJinja2

theorem Expr.collectS_nil {α : Type} (e : Expr) :
    Expr.collectS (fun _ => false) (fun _ => ([] : List α)) e = [] := by
  rw [Expr.collectS.eq_def]
  match e with
  | .const _ | .name _ => simp
  | .tuple xs | .list xs | .concat xs =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.flatMap_eq_nil_iff,
      List.mem_attach, forall_const, Subtype.forall]
    intro x hx; exact Expr.collectS_nil x
  | .dict ps =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.flatMap_eq_nil_iff,
      List.mem_attach, forall_const, Subtype.forall, List.append_eq_nil_iff]
    intro p hp; exact ⟨Expr.collectS_nil p.1, Expr.collectS_nil p.2⟩
  | .getattr x _ | .unop _ x => simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]; exact Expr.collectS_nil x
  | .getitem x i | .binop _ x i =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_eq_nil_iff]
    exact ⟨Expr.collectS_nil x, Expr.collectS_nil i⟩
  | .slice a b c =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_eq_nil_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · match a with | some x => exact Expr.collectS_nil x | none => rfl
    · match b with | some x => exact Expr.collectS_nil x | none => rfl
    · match c with | some x => exact Expr.collectS_nil x | none => rfl
  | .call g args kw | .filter g _ args kw | .test g _ args kw =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_eq_nil_iff,
      List.flatMap_eq_nil_iff, List.mem_attach, forall_const, Subtype.forall]
    exact ⟨⟨Expr.collectS_nil g, fun x _ => Expr.collectS_nil x⟩, fun p _ => Expr.collectS_nil p.2⟩
  | .compare x ops =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_eq_nil_iff,
      List.flatMap_eq_nil_iff, List.mem_attach, forall_const, Subtype.forall]
    exact ⟨Expr.collectS_nil x, fun p _ => Expr.collectS_nil p.2⟩
  | .cond a b c =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_eq_nil_iff]
    refine ⟨⟨Expr.collectS_nil a, Expr.collectS_nil b⟩, ?_⟩
    match c with | some x => exact Expr.collectS_nil x | none => rfl
termination_by sizeOf e
decreasing_by all_goals ast_decr

theorem Expr.collect_nil {α : Type} (e : Expr) : Expr.collect (fun _ => ([] : List α)) e = [] :=
  Expr.collectS_nil e


theorem Node.sizeOf_child {n x : Node} (hx : x ∈ n.children) : sizeOf x < sizeOf n := by
  cases n with
  | if_ bs els =>
    simp only [Node.children, List.mem_append, List.mem_flatMap] at hx
    simp only [Node.if_.sizeOf_spec]
    rcases hx with ⟨b, hb, hxb⟩ | hx
    · have h1 := List.sizeOf_lt_of_mem hb
      have h2 := List.sizeOf_lt_of_mem hxb
      cases b; simp at h1 h2; omega
    · have := List.sizeOf_lt_of_mem hx; omega
  | for_ t it fl r body els =>
    simp only [Node.children, List.mem_append] at hx
    simp only [Node.for_.sizeOf_spec]
    rcases hx with hx | hx <;> (have := List.sizeOf_lt_of_mem hx; omega)
  | setBlock _ _ body | «macro» _ _ body | callBlock _ _ body | block _ _ _ body | with_ _ body
  | filterBlock _ body | autoescape _ body =>
    simp only [Node.children] at hx
    have := List.sizeOf_lt_of_mem hx
    simp; omega
  | _ => simp [Node.children] at hx

/-- Without expression facts, a node's facts are its own or its children's. -/
theorem collect_cases {β : Type} (g : Node → List β) {n : Node} {y : β}
    (hy : y ∈ Node.collect (fun _ => []) g n) :
    y ∈ g n ∨ ∃ x ∈ n.children, y ∈ Node.collect (fun _ => []) g x := by
  unfold Node.collect at *
  rw [Node.collectS.eq_def] at hy
  have hz : ∀ e : Expr, Expr.collectS (fun _ => false) (fun _ => ([] : List β)) e = [] :=
    Expr.collectS_nil
  cases n with
  | if_ bs els =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_flatMap, List.mem_attach,
      true_and, Subtype.exists, hz, List.not_mem_nil, false_or, exists_prop] at hy
    rcases hy with hy | ⟨b, hb, x, hx, h⟩ | ⟨x, hx, h⟩
    · exact Or.inl hy
    · exact Or.inr ⟨x, by simp only [Node.children, List.mem_append, List.mem_flatMap]; exact Or.inl ⟨b, hb, hx⟩, h⟩
    · exact Or.inr ⟨x, by simp only [Node.children, List.mem_append]; exact Or.inr hx, h⟩
  | for_ t it fl r body els =>
    cases fl <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_flatMap, List.mem_attach,
      true_and, Subtype.exists, hz, List.not_mem_nil, false_or, exists_prop] at hy <;>
    rcases hy with hy | ⟨x, hx, h⟩ | ⟨x, hx, h⟩
    all_goals first
      | exact Or.inl hy
      | exact Or.inr ⟨x, by simp only [Node.children, List.mem_append]; exact Or.inl hx, h⟩
      | exact Or.inr ⟨x, by simp only [Node.children, List.mem_append]; exact Or.inr hx, h⟩
  | setBlock _ _ body | «macro» _ _ body | callBlock _ _ body | block _ _ _ body | with_ _ body
  | filterBlock _ body | autoescape _ body =>
    simp [hz, Node.children] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr hy
  | _ =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, hz, List.not_mem_nil, or_false] at hy
    exact Or.inl hy

/-- A fact of a node comes from a nested node whose own facts, under any
collector, are among the node's. -/
theorem collect_desc {β : Type} (g : Node → List β) (n : Node) {y : β}
    (hy : y ∈ Node.collect (fun _ => []) g n) :
    ∃ m, y ∈ g m ∧ ∀ {γ : Type} (f' : Expr → List γ) (g' : Node → List γ) (z : γ),
      z ∈ Node.collect f' g' m → z ∈ Node.collect f' g' n := by
  rcases collect_cases g hy with h | ⟨x, hx, h⟩
  · exact ⟨n, h, fun _ _ _ hz => hz⟩
  · have := Node.sizeOf_child hx
    obtain ⟨m, hm, hsub⟩ := collect_desc g x h
    exact ⟨m, hm, fun f' g' z hz => collect_child f' g' hx (hsub f' g' z hz)⟩
termination_by sizeOf n

/-- The body of a block a template defines contributes only facts of the
template. -/
theorem blockDefs_facts {body bb : List Node} {b : String} {sc req : Bool}
    (h : (b, sc, req, bb) ∈ blockDefs body) {fct : Fact} (hf : fct ∈ factsOf bb) :
    fct ∈ factsOf body := by
  simp only [blockDefs, nodesCollect, List.mem_flatMap] at h
  obtain ⟨n, hn, hy⟩ := h
  obtain ⟨m, hm, hsub⟩ := collect_desc _ n hy
  cases m <;> simp at hm
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
  simp only [factsOf, nodesCollect, List.mem_flatMap] at hf ⊢
  obtain ⟨x, hx, hfx⟩ := hf
  exact ⟨n, hn, hsub _ _ _ (collect_child _ _ (by simpa [Node.children] using hx) hfx)⟩

end LeanJinja2
