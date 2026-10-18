import LeanJinja2.Proofs.Parser.Nodes
import LeanJinja2.Proofs.Parser.Length

/-!
# The parser reads a printed template back

`body_ok` (the subparser reads a printed body up to the end tag it is
looking for), `node_ok` (the statement parser reads a printed tag) and
`ifRest_ok` (the `if` parser reads the branches) by induction on size.
-/

namespace LeanJinja2

open Parse

set_option linter.unusedSimpArgs false

mutual
/-- A node's size, for fuel. -/
def Node.sz : Node → Nat
  | .text _ => 0
  | .output e => e.sz
  | .if_ bs els => Node.szBranches bs + Node.szs els + 1
  | .for_ t it fl _ body els => t.sz + it.sz + Expr.szOpt fl + Node.szs body + Node.szs els + 1
  | .set t e => t.sz + e.sz + 1
  | .setBlock t fs body => t.sz + szChain fs + Node.szs body + 1
  | .macro _ ps body => szParams ps + Node.szs body + 1
  | .callBlock ps c body => szParams ps + c.sz + Node.szs body + 1
  | .include e _ _ | .extends e | .import_ e _ _ => e.sz + 1
  | .fromImport e names _ => e.sz + names.length + 1
  | .block _ _ _ body => Node.szs body + 1
  | .with_ as body => szAssigns as + Node.szs body + 1
  | .filterBlock fs body => szChain fs + Node.szs body + 1
  | .autoescape e body => e.sz + Node.szs body + 1

def Node.szs : List Node → Nat
  | [] => 0
  | n :: ns => n.sz + Node.szs ns + 1

def Node.szBranches : List (Expr × List Node) → Nat
  | [] => 0
  | (t, b) :: bs => t.sz + Node.szs b + Node.szBranches bs + 1
end

/-- Whether a node is printed as a block tag. -/
def Node.isTag : Node → Bool
  | .text _ | .output _ => false
  | _ => true

/-- An `else` clause, printed. -/
def elsePart (els : List Node) : List TokKind :=
  if els.isEmpty then [] else Pretty.tag [Pretty.nm "else"] ++ Pretty.nodes els

/-- The tokens of an `if` tag after `if`, up to the last `%}`. -/
def ifToks (t : Expr) (b : List Node) (bs : List (Expr × List Node)) (els : List Node) : List TokKind :=
  Pretty.expr t ++ .blockEnd :: (Pretty.nodes b ++ (Pretty.elifs bs ++ (elsePart els ++
    [.blockBegin, .name "endif"])))

/-- A `for` loop's printed filter. -/
def forFilt : Option Expr → List TokKind
  | some f => .name "if" :: Pretty.expr f
  | none => []

/-- A `for` loop's printed `recursive` flag. -/
def forRec (rc : Bool) : List TokKind := if rc then [.name "recursive"] else []

/-- What `node_ok` says about a tag node. -/
def TagOK (nd : Node) : Prop :=
  ∃ kw inner, kw ∈ statementKeywords ∧ Pretty.node nd = .blockBegin :: .name kw :: (inner ++ [.blockEnd]) ∧
    ∀ (stack : TagStack) (R : List TokKind) (n : Nat), 40 * nd.sz + 40 ≤ n →
      pStatement n stack (.name kw :: (inner ++ .blockEnd :: R)) = .ok ([nd], .blockEnd :: R)

theorem expr_ok {e : Expr} (hw : e.WF) {r : List TokKind} (hr : Stop 10 r) (n : Nat) (hn : 30 * e.sz + 12 ≤ n) :
    pExpr n true (Pretty.expr e ++ r) = .ok (e, r) := by
  obtain ⟨k, hk⟩ : ∃ k, 30 * e.sz = k + 1 := ⟨30 * e.sz - 1, by have := e.sz_pos; omega⟩
  have hp := prim_ok e hw
  rw [hk] at hp
  exact (hp.exprOK hw) r hr n (by omega)

theorem stop_be (k : Nat) (r : List TokKind) (hk : k < 99 := by omega) : Stop k (.blockEnd :: r) :=
  stop_cons _ _ (by simp [contLevel]; omega)

/-- The printed `with context` / `without context`. -/
def ctxToks (wc : Bool) : List TokKind := [.name (if wc then "with" else "without"), .name "context"]

theorem importContext_ctx (wc : Bool) (R : List TokKind) :
    importContext false (ctxToks wc ++ R) = (wc, R) := by
  cases wc <;> rfl

theorem isContextAt_ctx (wc : Bool) (R : List TokKind) : isContextAt (ctxToks wc ++ R) = true := by
  cases wc <;> rfl

/-- The separator `pFromNames` expects before the next name. -/
def namesSep (acc : List (String × Option String)) : List TokKind :=
  if acc.isEmpty then [] else [.op .comma]

theorem namesSep_read (acc : List (String × Option String)) (X : List TokKind) :
    (if acc.isEmpty then (.ok ((), namesSep acc ++ X) : PR Unit) else expect (.op .comma) (namesSep acc ++ X)) =
      .ok ((), X) := by
  cases acc <;> simp [namesSep, expect]

/-- One name and what follows it (`T`, which starts with a comma or the
context): `pFromNames` reads the name and its alias. -/
theorem fromName_step (p : String × Option String) (hp : ImportNameWF p)
    (acc : List (String × Option String)) (k : Nat) (T : List TokKind)
    (hT : T.head? = some (.op .comma) ∨ ∃ wc R, T = ctxToks wc ++ R) :
    pFromNames (k + 1) acc (namesSep acc ++ (Pretty.importName p ++ T)) =
      if isContextAt T then .ok (((p :: acc).reverse, (importContext false T).1), (importContext false T).2)
      else if isOp .comma T.head? then pFromNames k (p :: acc) T
      else .ok (((p :: acc).reverse, false), T) := by
  obtain ⟨n, a⟩ := p
  obtain ⟨hn, hu, ha⟩ := hp
  have hT1 : isName "as" T.head? = false := by
    rcases hT with h | ⟨wc, R, rfl⟩
    · simp [h, isName]
    · cases wc <;> simp [ctxToks, isName]
  have hnc2 : isContextAt (.name n :: T) = false := by
    unfold isContextAt
    rcases hT with h | ⟨wc, R, rfl⟩
    · cases T with
      | nil => simp at h
      | cons t T' => simp at h; subst h; split <;> simp_all
    · cases wc <;> simp [ctxToks]
  rw [pFromNames]
  cases a with
  | none =>
    cases hacc : acc.isEmpty <;>
    simp only [namesSep, hacc, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.cons_append,
      expect, beq_self_eq_true, bind, Except.bind, Pretty.importName, Pretty.nm, hnc2,
      pParamName_ok hn, hu, hT1] <;> rfl
  | some a =>
    have hnc : isContextAt (.name n :: .name "as" :: .name a :: T) = false := by
      simp [isContextAt]
    cases hacc : acc.isEmpty <;>
    simp only [namesSep, hacc, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.cons_append,
      expect, beq_self_eq_true, bind, Except.bind, Pretty.importName, Pretty.nm, hnc,
      pParamName_ok hn, hu, isName, List.head?_cons, List.tail_cons, pParamName_ok (ha a rfl)] <;> rfl

theorem fromNames_ok (wc : Bool) (R : List TokKind) :
    ∀ (ps : List (String × Option String)) (p : String × Option String)
      (acc : List (String × Option String)) (k : Nat),
    ImportNameWF p → (∀ q ∈ ps, ImportNameWF q) → ps.length ≤ k →
    pFromNames (k + 1) acc (namesSep acc ++ (Pretty.importNames (p :: ps) ++ (ctxToks wc ++ R))) =
      .ok ((acc.reverse ++ p :: ps, wc), R) := by
  intro ps
  induction ps with
  | nil =>
    intro p acc k hp _ _
    rw [show Pretty.importNames [p] = Pretty.importName p by rfl,
      fromName_step p hp acc k _ (Or.inr ⟨wc, R, rfl⟩), isContextAt_ctx, importContext_ctx]
    simp
  | cons q qs ih =>
    intro p acc k hp hps hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hq := hps q (by simp)
    have hqs : ∀ r ∈ qs, ImportNameWF r := fun r hr => hps r (by simp [hr])
    rw [show Pretty.importNames (p :: q :: qs) = Pretty.importName p ++ (.op .comma :: Pretty.importNames (q :: qs))
        by simp [Pretty.importNames, Pretty.op]]
    simp only [List.append_assoc, List.cons_append]
    rw [fromName_step p hp acc (k + 1) _ (Or.inl rfl)]
    have hc : isContextAt (.op .comma :: (Pretty.importNames (q :: qs) ++ (ctxToks wc ++ R))) = false := by
      simp [isContextAt]
    simp only [hc, Bool.false_eq_true, ↓reduceIte, List.head?_cons, isOp]
    have := ih q (p :: acc) k hq hqs (by simp at hk; omega)
    simp only [namesSep, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.nil_append] at this
    rw [this]; simp

mutual
theorem body_ok : (b : List Node) → Node.BodyWF b → ∀ (stack : TagStack) (ends : List String), EndsOK ends →
    ∀ R R', EndsAt ends R R' → ∀ n, 40 * Node.szs b + 41 ≤ n →
    subparse n stack ends (Pretty.nodes b ++ R) = .ok (b, R')
  | [], _, stack, ends, hends, R, R', hR, n, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rcases hR with ⟨rfl, rfl⟩ | ⟨e, R2, he, rfl, rfl⟩
    · simp [Pretty.nodes, subparse]
    · simp [Pretty.nodes, subparse, he]
  | nd :: rest, hw, stack, ends, hends, R, R', hR, n, hn => by
    simp only [Node.BodyWF] at hw
    obtain ⟨hnd, hrest, htxt⟩ := hw
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ih := body_ok rest hrest stack ends hends R R' hR m (by simp [Node.szs] at hn; omega)
    cases hk : nd.isTag with
    | false =>
      cases nd with
      | text s =>
        simp only [Node.WF, TextOK] at hnd
        have hne : s.isEmpty = false := by
          cases h : s.isEmpty with
          | false => rfl
          | true => exact absurd (by simpa [String.isEmpty_iff] using h) hnd.1
        have hcons : consText s rest = .text s :: rest := by
          cases rest with
          | nil => simp [consText, hne]
          | cons r rs => cases r <;> simp_all [consText, Node.isText]
        simp [Pretty.nodes, Pretty.node, subparse, bind, Except.bind, ih, hcons]
      | output e =>
        simp only [Node.WF] at hnd
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [Node.szs, Node.sz] at hn; omega⟩
        have ht := tuple_one hnd (extra := []) (by simp) true (r := .varEnd :: (Pretty.nodes rest ++ R))
          (stop_cons _ _ (by simp [contLevel])) (by simp) k (by simp [Node.szs, Node.sz] at hn; omega)
        simp only [Pretty.nodes, Pretty.node, List.append_assoc, List.cons_append, List.singleton_append,
          List.nil_append] at ht ⊢
        rw [subparse]
        simp [ht, expect, bind, Except.bind, ih]
      | _ => simp [Node.isTag] at hk
    | true =>
      obtain ⟨kw, inner, hkw, hpr, hst⟩ := node_ok nd hnd hk
      have hs := hst stack (Pretty.nodes rest ++ R) m (by simp [Node.szs] at hn; omega)
      simp only [Pretty.nodes, hpr, List.append_assoc, List.cons_append, List.singleton_append,
        List.nil_append] at hs ⊢
      have hnot : kw ∉ ends := fun h => hends kw h hkw
      rw [subparse]
      simp [hnot, hs, expect, bind, Except.bind, ih]
termination_by b => 2 * Node.szs b + 1
decreasing_by all_goals simp_wf; simp [Node.szs] <;> omega

theorem node_ok : (nd : Node) → nd.WF → nd.isTag = true → TagOK nd
  | .text _, _, h => by simp [Node.isTag] at h
  | .output _, _, h => by simp [Node.isTag] at h
  | .if_ [] _, hw, _ => by simp [Node.WF] at hw
  | .if_ ((t, b) :: bs) els, hw, _ => by
    simp only [Node.WF, Node.BranchesWF] at hw
    obtain ⟨_, ⟨ht, hb, hbs⟩, hels⟩ := hw
    refine ⟨"if", ifToks t b bs els, by decide, ?_, ?_⟩
    · simp [Pretty.node, Pretty.tag, ifToks, elsePart]
    · intro stack R n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h := ifRest_ok t b bs els ht hb hbs hels stack R m (by simp [Node.sz] at hn; omega)
      simp [pStatement, h, bind, Except.bind]
  | .set t e, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨ht, he⟩ := hw
    refine ⟨"set", Pretty.target t ++ .op .assign :: Pretty.expr e, by decide, by simp [Pretty.node, Pretty.tag], ?_⟩
    intro stack R n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hT := target_ok (t := t) (extra := []) (withNs := true) (rest := .op .assign :: (Pretty.expr e ++ .blockEnd :: R))
      ht (fun h => absurd h (by simp)) (by simp) (by intro s; simp)
      (by intro x hx; simp at hx; subst hx; simp) (k + 1) (by simp [Node.sz] at hn; omega)
    have hE := tuple_one he (extra := []) (by simp) true (r := .blockEnd :: R) (stop_be 10 _) (by simp) k
      (by simp [Node.sz] at hn; omega)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hT ⊢
    simp [pStatement, hT, hE, bind, Except.bind, isOp]
  | .extends e, hw, _ => by
    simp only [Node.WF] at hw
    refine ⟨"extends", Pretty.expr e, by decide, by simp [Pretty.node, Pretty.tag], ?_⟩
    intro stack R n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := expr_ok hw (stop_be 10 R) m (by simp [Node.sz] at hn; omega)
    simp [pStatement, h, bind, Except.bind]
  | .import_ e t wc, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨he, ht⟩ := hw
    refine ⟨"import", Pretty.expr e ++ (.name "as" :: .name t :: ctxToks wc), by decide,
      by cases wc <;> simp [Pretty.node, Pretty.tag, ctxToks, Pretty.nm], ?_⟩
    intro stack R n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := expr_ok he (r := .name "as" :: .name t :: (ctxToks wc ++ .blockEnd :: R))
      (stop_cons _ _ (by simp [contLevel])) m (by simp [Node.sz] at hn; omega)
    simp only [List.append_assoc, List.cons_append] at h ⊢
    simp [pStatement, h, expect, pParamName_ok ht, importContext_ctx, bind, Except.bind]
  | .fromImport e names wc, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨he, hns⟩ := hw
    refine ⟨"from", Pretty.expr e ++ (.name "import" :: (Pretty.importNames names ++ ctxToks wc)), by decide,
      by cases wc <;> simp [Pretty.node, Pretty.tag, ctxToks, Pretty.nm], ?_⟩
    intro stack R n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := expr_ok he (r := .name "import" :: (Pretty.importNames names ++ (ctxToks wc ++ .blockEnd :: R)))
      (stop_cons _ _ (by simp [contLevel])) m (by simp [Node.sz] at hn; omega)
    have hN : pFromNames m [] (Pretty.importNames names ++ (ctxToks wc ++ .blockEnd :: R)) =
        .ok ((names, wc), .blockEnd :: R) := by
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by simp [Node.sz] at hn; omega⟩
      cases names with
      | nil => cases wc <;> rfl
      | cons p ps =>
        have := fromNames_ok wc (.blockEnd :: R) ps p [] j (hns p (by simp))
          (fun q hq => hns q (by simp [hq])) (by simp [Node.sz] at hn; omega)
        simpa [namesSep] using this
    simp only [List.append_assoc, List.cons_append] at h ⊢
    simp [pStatement, h, expect, hN, bind, Except.bind]
  | .autoescape e body, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨he, hb⟩ := hw
    refine ⟨"autoescape", Pretty.expr e ++ .blockEnd :: (Pretty.nodes body ++ [.blockBegin, .name "endautoescape"]),
      by decide, by simp [Pretty.node, Pretty.tag], ?_⟩
    intro stack R n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hB := body_ok body hb (("autoescape", ["endautoescape"]) :: stack) ["endautoescape"] (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "endautoescape" :: .blockEnd :: R) (.name "endautoescape" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.sz] at hn; omega)
    have hS := statements_ok (drop := true) hB
    have hE := expr_ok he (r := .blockEnd :: (Pretty.nodes body ++ .blockBegin :: .name "endautoescape" :: .blockEnd :: R))
      (stop_be 10 _) (k + 1) (by simp [Node.sz] at hn; omega)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    simp [pStatement, hE, hS, bind, Except.bind]
  | .with_ as body, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨has, hb⟩ := hw
    refine ⟨"with", Pretty.assigns as ++ .blockEnd :: (Pretty.nodes body ++ [.blockBegin, .name "endwith"]),
      by decide, by simp [Pretty.node, Pretty.tag], ?_⟩
    intro stack R n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hB := body_ok body hb (("with", ["endwith"]) :: stack) ["endwith"] (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "endwith" :: .blockEnd :: R) (.name "endwith" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.sz] at hn; omega)
    have hS := statements_ok (drop := true) hB
    have hA := assigns_ok as (Pretty.nodes body ++ .blockBegin :: .name "endwith" :: .blockEnd :: R) has k
      (by simp [Node.sz] at hn; omega)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    simp [pStatement, hA, hS, bind, Except.bind]
  | .filterBlock fs body, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨hne, hfs, hb⟩ := hw
    refine ⟨"filter", Pretty.filterChain fs ++ .blockEnd :: (Pretty.nodes body ++ [.blockBegin, .name "endfilter"]),
      by decide, by simp [Pretty.node, Pretty.tag], ?_⟩
    intro stack R n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hB := body_ok body hb (("filter", ["endfilter"]) :: stack) ["endfilter"] (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "endfilter" :: .blockEnd :: R) (.name "endfilter" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.sz] at hn; omega)
    have hS := statements_ok (drop := true) hB
    have hF := chainFirst_ok fs (Pretty.nodes body ++ .blockBegin :: .name "endfilter" :: .blockEnd :: R) hne hfs (k + 1)
      (by simp [Node.sz] at hn; omega)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    simp [pStatement, hF, hS, bind, Except.bind]
  | .setBlock t fs body, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨ht, hfs, hb⟩ := hw
    refine ⟨"set", Pretty.target t ++ ((fs.flatMap fun f => [Pretty.op .pipe] ++ Pretty.filterCall f) ++
      .blockEnd :: (Pretty.nodes body ++ [.blockBegin, .name "endset"])), by decide,
      by simp [Pretty.node, Pretty.tag], ?_⟩
    intro stack R n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hB := body_ok body hb (("set", ["endset"]) :: stack) ["endset"] (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "endset" :: .blockEnd :: R) (.name "endset" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.sz] at hn; omega)
    have hS := statements_ok (drop := true) hB
    have hF := chainPipe_ok fs (Pretty.nodes body ++ .blockBegin :: .name "endset" :: .blockEnd :: R) hfs (k + 1)
      (by simp [Node.sz] at hn; omega)
    have hhd : ∀ x, ((fs.flatMap fun f => [Pretty.op .pipe] ++ Pretty.filterCall f) ++ .blockEnd ::
        (Pretty.nodes body ++ .blockBegin :: .name "endset" :: .blockEnd :: R)).head? = some x →
        x = .blockEnd ∨ x = .op .pipe := by
      intro x hx
      cases fs with
      | nil => simp at hx; exact Or.inl hx.symm
      | cons f fs => simp at hx; exact Or.inr hx.symm
    have hT := target_ok (t := t) (extra := []) (withNs := true)
      (rest := (fs.flatMap fun f => [Pretty.op .pipe] ++ Pretty.filterCall f) ++ .blockEnd ::
        (Pretty.nodes body ++ .blockBegin :: .name "endset" :: .blockEnd :: R))
      ht (fun h => absurd h (by simp)) (by simp)
      (by intro s hs; rcases hhd _ hs with h | h <;> cases h)
      (by intro x hx; rcases hhd x hx with h | h <;> subst h <;> simp) (k + 1) (by simp [Node.sz] at hn; omega)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hT hF ⊢
    rcases fs with _ | ⟨f, fs⟩
    · simp only [List.flatMap_nil, List.nil_append] at hT hF ⊢
      simp [pStatement, hT, hF, hS, bind, Except.bind, isOp]
    · simp only [List.flatMap_cons, List.cons_append, List.append_assoc, List.singleton_append] at hT hF ⊢
      simp [pStatement, hT, hF, hS, bind, Except.bind, isOp]
  | .macro nm ps body, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨hnm, hps, hb⟩ := hw
    refine ⟨"macro", .name nm :: .op .lparen :: (Pretty.params ps ++ .op .rparen :: .blockEnd ::
      (Pretty.nodes body ++ [.blockBegin, .name "endmacro"])), by decide, by simp [Pretty.node, Pretty.tag], ?_⟩
    intro stack R n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hB := body_ok body hb (("macro", ["endmacro"]) :: stack) ["endmacro"] (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "endmacro" :: .blockEnd :: R) (.name "endmacro" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.sz] at hn; omega)
    have hS := statements_ok (drop := true) hB
    have hP := params_ok ps false (.blockEnd :: (Pretty.nodes body ++ .blockBegin :: .name "endmacro" :: .blockEnd :: R))
      hps k (by simp [Node.sz] at hn; omega)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    simp [pStatement, pParamName_ok hnm, expect, hP, hS, bind, Except.bind]
  | .callBlock ps c body, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨hps, ⟨f, args, kw, rfl⟩, hc, hb⟩ := hw
    refine ⟨"call", .op .lparen :: (Pretty.params ps ++ .op .rparen :: (Pretty.expr (.call f args kw) ++ .blockEnd ::
      (Pretty.nodes body ++ [.blockBegin, .name "endcall"]))), by decide, by simp [Pretty.node, Pretty.tag], ?_⟩
    intro stack R n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hB := body_ok body hb (("call", ["endcall"]) :: stack) ["endcall"] (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "endcall" :: .blockEnd :: R) (.name "endcall" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.sz] at hn; omega)
    have hS := statements_ok (drop := true) hB
    have hE := expr_ok hc (r := .blockEnd :: (Pretty.nodes body ++ .blockBegin :: .name "endcall" :: .blockEnd :: R))
      (stop_be 10 _) (k + 1) (by simp [Node.sz] at hn; omega)
    have hP := params_ok ps false (Pretty.expr (.call f args kw) ++ .blockEnd ::
      (Pretty.nodes body ++ .blockBegin :: .name "endcall" :: .blockEnd :: R)) hps k (by simp [Node.sz] at hn; omega)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hE hP ⊢
    simp [pStatement, pOptParams, isOp, hP, hE, hS, bind, Except.bind]
  | .include e ig wc, hw, _ => by
    simp only [Node.WF] at hw
    refine ⟨"include", Pretty.expr e ++ ((if ig then [.name "ignore", .name "missing"] else []) ++
      [.name (if wc then "with" else "without"), .name "context"]), by decide, by simp [Pretty.node, Pretty.tag], ?_⟩
    intro stack R n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := expr_ok hw (r := (if ig then [.name "ignore", .name "missing"] else []) ++
      ([.name (if wc then "with" else "without"), .name "context"] ++ .blockEnd :: R))
      (by cases ig <;> cases wc <;> exact stop_cons _ _ (by simp [contLevel])) m (by simp [Node.sz] at hn; omega)
    simp only [List.append_assoc] at h ⊢
    cases ig <;> cases wc <;> simp_all [pStatement, bind, Except.bind]
  | .block nm sc req body, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨hnm, hb, hreq⟩ := hw
    refine ⟨"block", .name nm :: ((if sc then [.name "scoped"] else []) ++ ((if req then [.name "required"] else []) ++
      .blockEnd :: (Pretty.nodes body ++ [.blockBegin, .name "endblock"]))), by decide,
      by simp [Pretty.node, Pretty.tag], ?_⟩
    intro stack R n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hB := body_ok body hb (("block", ["endblock"]) :: stack) ["endblock"] (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "endblock" :: .blockEnd :: R) (.name "endblock" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.sz] at hn; omega)
    have hS := statements_ok (drop := true) hB
    have hw' : (req && !onlyWhitespace body) = false := by
      cases req <;> simp_all
    cases sc <;> cases req <;> simp_all [pStatement, expectName, isName, isOp, bind, Except.bind]
  | .for_ t it fl rc body els, hw, _ => by
    simp only [Node.WF] at hw
    obtain ⟨ht, hit, hfl, hb, hels⟩ := hw
    refine ⟨"for", Pretty.target t ++ .name "in" :: (Pretty.expr it ++ (forFilt fl ++ (forRec rc ++ .blockEnd ::
      (Pretty.nodes body ++ (elsePart els ++ [.blockBegin, .name "endfor"]))))), by decide,
      by cases fl <;> simp [Pretty.node, Pretty.tag, forFilt, forRec, elsePart], ?_⟩
    intro stack R n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    -- the tokens after the `for` header
    have hY : ∀ Y : List TokKind, Y.head? = some .blockEnd →
        pForFilter (k + 1) (forFilt fl ++ (forRec rc ++ Y)) = .ok (fl, forRec rc ++ Y) ∧
        Stop 9 (forFilt fl ++ (forRec rc ++ Y)) ∧ (∀ x, (forFilt fl ++ (forRec rc ++ Y)).head? = some x → x ≠ .op .comma) ∧
        (if isName "recursive" (forRec rc ++ Y).head? then (true, (forRec rc ++ Y).tail) else (false, forRec rc ++ Y)) =
          (rc, Y) := by
      intro Y hY
      obtain ⟨Y, rfl⟩ : ∃ Y', Y = .blockEnd :: Y' := by
        cases Y with
        | nil => simp at hY
        | cons y ys => simp at hY; exact ⟨ys, by rw [hY]⟩
      have hR : Stop 10 (forRec rc ++ .blockEnd :: Y) := by
        cases rc <;> exact stop_cons _ _ (by simp [contLevel])
      refine ⟨?_, ?_, ?_, ?_⟩
      · cases fl with
        | none => cases rc <;> simp [pForFilter, forFilt, forRec, isName]
        | some f =>
          simp only [Expr.WFOpt] at hfl
          have := expr_ok hfl hR (k + 1) (by simp [Node.sz, Expr.szOpt] at hn; omega)
          simp [pForFilter, forFilt, isName, this, bind, Except.bind]
      · cases fl with
        | none => cases rc <;> exact stop_cons _ _ (by simp [forFilt, forRec, contLevel])
        | some f => exact stop_cons _ _ (by simp [contLevel])
      · intro x hx
        cases fl <;> cases rc <;> simp [forFilt, forRec] at hx <;> subst hx <;> simp
      · cases rc <;> simp [forRec, isName]
    have hTg := target_ok (t := t) (extra := ["in"]) (withNs := false)
      (rest := .name "in" :: (Pretty.expr it ++ (forFilt fl ++ (forRec rc ++ .blockEnd ::
        (Pretty.nodes body ++ (elsePart els ++ .blockBegin :: .name "endfor" :: .blockEnd :: R))))))
      (by cases t <;> simp_all [Target.Settable, Target.Plain]) (fun _ => ht) (by simp) (by intro s; simp)
      (by intro x hx; simp at hx; subst hx; simp) (k + 1) (by simp [Node.sz] at hn; omega)
    obtain ⟨hF, hS9, hC, hRc⟩ := hY (.blockEnd :: (Pretty.nodes body ++ (elsePart els ++
      .blockBegin :: .name "endfor" :: .blockEnd :: R))) rfl
    have hIt := tuple_one hit (extra := ["recursive"]) (by simp) false (r := forFilt fl ++ (forRec rc ++ .blockEnd ::
        (Pretty.nodes body ++ (elsePart els ++ .blockBegin :: .name "endfor" :: .blockEnd :: R))))
      (by simpa using hS9) hC k (by simp [Node.sz] at hn; omega)
    cases hel : els.isEmpty with
    | true =>
      have he : els = [] := by simpa using hel
      subst he
      have hB := body_ok body hb (("for", ["endfor", "else"]) :: stack) ["endfor", "else"]
        (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "endfor" :: .blockEnd :: R) (.name "endfor" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.sz] at hn; omega)
      have hS := statements_ok (drop := false) hB
      simp only [elsePart, List.isEmpty_nil, ↓reduceIte, List.nil_append] at hTg hF hIt hRc ⊢
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hTg ⊢
      cases rc <;> simp only [forRec, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.cons_append] at hTg hF hIt ⊢ <;>
        simp only [pStatement, hTg, bind, Except.bind, expect] <;> simp [hIt, hF, hS, isName]
    | false =>
      have hX : elsePart els ++ .blockBegin :: .name "endfor" :: .blockEnd :: R =
          .blockBegin :: .name "else" :: .blockEnd :: (Pretty.nodes els ++ .blockBegin :: .name "endfor" :: .blockEnd :: R) := by
        simp [elsePart, hel, Pretty.tag]
      have hB := body_ok body hb (("for", ["endfor", "else"]) :: stack) ["endfor", "else"]
        (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "else" :: .blockEnd :: (Pretty.nodes els ++ .blockBegin :: .name "endfor" :: .blockEnd :: R))
        (.name "else" :: .blockEnd :: (Pretty.nodes els ++ .blockBegin :: .name "endfor" :: .blockEnd :: R))
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.sz] at hn; omega)
      have hS := statements_ok (drop := false) hB
      have hB2 := body_ok els hels (("for", ["endfor"]) :: stack) ["endfor"] (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "endfor" :: .blockEnd :: R) (.name "endfor" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.sz] at hn; omega)
      have hS2 := statements_ok (drop := true) hB2
      rw [hX] at hTg hF hIt hRc
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hTg ⊢
      rw [hX]
      cases rc <;> simp only [forRec, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.cons_append] at hTg hF hIt ⊢ <;>
        simp only [pStatement, hTg, bind, Except.bind, expect] <;> simp [hIt, hF, hS, hS2, isName]
termination_by nd => 2 * nd.sz
decreasing_by all_goals simp_wf; simp [Node.sz, Node.szBranches] <;> omega

theorem ifRest_ok : (t : Expr) → (b : List Node) → (bs : List (Expr × List Node)) → (els : List Node) →
    t.WF → Node.BodyWF b → Node.BranchesWF bs → Node.BodyWF els →
    ∀ (stack : TagStack) (R : List TokKind) (n : Nat), 40 * (Node.szBranches ((t, b) :: bs) + Node.szs els) + 3 ≤ n →
    pIfRest n stack (ifToks t b bs els ++ .blockEnd :: R) = .ok (((t, b) :: bs, els), .blockEnd :: R)
  | t, b, [], els, ht, hb, hbs, hels, stack, R, n, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hT := tuple_one ht (extra := []) (by simp) false
      (r := .blockEnd :: (Pretty.nodes b ++ (Pretty.elifs [] ++ (elsePart els ++
        .blockBegin :: .name "endif" :: .blockEnd :: R)))) (stop_be 9 _) (by simp) k
      (by simp [Node.szBranches] at hn; omega)
    have hE : EndsOK ["elif", "else", "endif"] := by simp [EndsOK, statementKeywords]
    simp only [ifToks, List.append_assoc, List.cons_append, List.nil_append]
    cases hel : els.isEmpty with
    | true =>
      have he : els = [] := by simpa using hel
      subst he
      have hB := body_ok b hb (("if", ["elif", "else", "endif"]) :: stack) _ hE
        (.blockBegin :: .name "endif" :: .blockEnd :: R) (.name "endif" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.szBranches] at hn; omega)
      have hS := statements_ok (drop := false) hB
      simp only [Pretty.elifs, elsePart, List.isEmpty_nil, ↓reduceIte, List.nil_append] at hT ⊢
      rw [pIfRest]
      simp [bind, Except.bind, hT, hS]
    | false =>
      have hX : elsePart els ++ .blockBegin :: .name "endif" :: .blockEnd :: R =
          .blockBegin :: .name "else" :: .blockEnd :: (Pretty.nodes els ++ .blockBegin :: .name "endif" :: .blockEnd :: R) := by
        simp [elsePart, hel, Pretty.tag]
      have hB := body_ok b hb (("if", ["elif", "else", "endif"]) :: stack) _ hE
        (.blockBegin :: .name "else" :: .blockEnd :: (Pretty.nodes els ++ .blockBegin :: .name "endif" :: .blockEnd :: R))
        (.name "else" :: .blockEnd :: (Pretty.nodes els ++ .blockBegin :: .name "endif" :: .blockEnd :: R))
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.szBranches] at hn; omega)
      have hS := statements_ok (drop := false) hB
      have hB2 := body_ok els hels (("if", ["endif"]) :: stack) ["endif"] (by simp [EndsOK, statementKeywords])
        (.blockBegin :: .name "endif" :: .blockEnd :: R) (.name "endif" :: .blockEnd :: R)
        (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k (by simp [Node.szBranches] at hn; omega)
      have hS2 := statements_ok (drop := true) hB2
      simp only [Pretty.elifs, List.nil_append] at hT ⊢
      rw [hX] at hT ⊢
      rw [pIfRest]
      simp [bind, Except.bind, hT, hS, hS2]
  | t, b, (t', b') :: bs', els, ht, hb, hbs, hels, stack, R, n, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hT := tuple_one ht (extra := []) (by simp) false
      (r := .blockEnd :: (Pretty.nodes b ++ (Pretty.elifs ((t', b') :: bs') ++ (elsePart els ++
        .blockBegin :: .name "endif" :: .blockEnd :: R)))) (stop_be 9 _) (by simp) k
      (by simp [Node.szBranches] at hn; omega)
    have hE : EndsOK ["elif", "else", "endif"] := by simp [EndsOK, statementKeywords]
    simp only [ifToks, List.append_assoc, List.cons_append, List.nil_append]
    simp only [Node.BranchesWF] at hbs
    obtain ⟨ht', hb', hbs'⟩ := hbs
    have hX : Pretty.elifs ((t', b') :: bs') ++ (elsePart els ++ .blockBegin :: .name "endif" :: .blockEnd :: R) =
        .blockBegin :: .name "elif" :: (ifToks t' b' bs' els ++ .blockEnd :: R) := by
      simp [Pretty.elifs, Pretty.tag, ifToks]
    have hB := body_ok b hb (("if", ["elif", "else", "endif"]) :: stack) _ hE
      (.blockBegin :: .name "elif" :: (ifToks t' b' bs' els ++ .blockEnd :: R))
      (.name "elif" :: (ifToks t' b' bs' els ++ .blockEnd :: R)) (Or.inr ⟨_, _, by simp, rfl, rfl⟩) k
      (by simp [Node.szBranches] at hn; omega)
    have hS := statements_ok (drop := false) hB
    have hI := ifRest_ok t' b' bs' els ht' hb' hbs' hels stack R (k + 1)
      (by simp [Node.szBranches] at hn ⊢; omega)
    rw [hX] at hT ⊢
    rw [pIfRest]
    simp [bind, Except.bind, hT, hS, hI]
termination_by t b bs els => 2 * (Node.szBranches ((t, b) :: bs) + Node.szs els)
decreasing_by all_goals simp_wf; simp [Node.szBranches] <;> omega
end

end LeanJinja2

namespace LeanJinja2

open Parse

/-! ## Sizes are bounded by token counts -/

mutual
theorem target_length : (t : Target) → t.sz ≤ (Pretty.target t).length
  | .name _ => by simp [Target.sz, Target.toExpr, Expr.sz, Pretty.target]
  | .nsAttr _ _ => by simp [Target.sz, Target.toExpr, Expr.sz, Pretty.target]
  | .tuple [] => by simp [Target.sz, Target.toExpr, Target.toExprs, Expr.sz, Expr.szs, Pretty.target,
      Pretty.target.targets]
  | .tuple [t] => by
    have := target_length t
    simp only [Target.sz] at this
    simp [Target.sz, Target.toExpr, Target.toExprs, Expr.sz, Expr.szs, Pretty.target]; omega
  | .tuple (t :: u :: us) => by
    have := targets_length (t :: u :: us)
    simp only [Target.sz, Target.toExpr, Expr.sz, Pretty.target, List.length_append, List.length_cons,
      List.length_nil] at this ⊢
    omega
theorem targets_length : (ts : List Target) → Expr.szs (Target.toExprs ts) ≤ (Pretty.target.targets ts).length + 1
  | [] => by simp [Target.toExprs, Expr.szs, Pretty.target.targets]
  | [t] => by
    have := target_length t
    simp only [Target.sz] at this
    simp [Target.toExprs, Expr.szs, Pretty.target.targets]; omega
  | t :: u :: us => by
    have := target_length t
    have := targets_length (u :: us)
    simp only [Target.sz] at *
    simp only [Target.toExprs, Expr.szs, Pretty.target.targets, List.length_append, List.length_cons,
      List.length_nil] at *
    omega
end

theorem params_length : (ps : List Param) → szParams ps ≤ (Pretty.params ps).length + 1
  | [] => by simp [szParams, Pretty.params]
  | [(p, d)] => by
    cases d with
    | none => simp [szParams, Expr.szOpt, Pretty.params, Pretty.param]
    | some e => have := expr_length e; simp [szParams, Expr.szOpt, Pretty.params, Pretty.param]; omega
  | (p, d) :: q :: qs => by
    have := params_length (q :: qs)
    have : Expr.szOpt d + 1 ≤ (Pretty.param (p, d)).length := by
      cases d with
      | none => simp [Expr.szOpt, Pretty.param]
      | some e => have := expr_length e; simp [Expr.szOpt, Pretty.param]; omega
    obtain ⟨q1, q2⟩ := q
    simp only [szParams, Pretty.params, List.length_append, List.length_cons, List.length_nil] at *
    omega

theorem filterCall_length (f : FilterCall) : f.sz ≤ (Pretty.filterCall f).length + 1 := by
  have := parenArgs_length f.args f.kwargs (exprs_length _) (kwargs_length _)
  simp only [FilterCall.sz, Pretty.filterCall, List.length_append, List.length_cons, List.length_nil] at *
  omega

theorem chainPipe_length : (fs : List FilterCall) →
    szChain fs ≤ (fs.flatMap fun f => [Pretty.op .pipe] ++ Pretty.filterCall f).length
  | [] => by simp [szChain]
  | f :: fs => by
    have := filterCall_length f
    have := chainPipe_length fs
    simp only [szChain, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at *
    omega

theorem chain_length : (fs : List FilterCall) → szChain fs ≤ (Pretty.filterChain fs).length + 1
  | [] => by simp [szChain]
  | [f] => by
    have := filterCall_length f
    simp [szChain, Pretty.filterChain]; omega
  | f :: g :: gs => by
    have := filterCall_length f
    have := chain_length (g :: gs)
    simp only [szChain, Pretty.filterChain, List.length_append, List.length_cons, List.length_nil] at *
    omega

theorem assigns_length : (as : List (Target × Expr)) → szAssigns as ≤ (Pretty.assigns as).length
  | [] => by simp [szAssigns]
  | [(t, e)] => by
    have := target_length t
    have := expr_length e
    simp [szAssigns, Pretty.assigns]; omega
  | (t, e) :: a :: as => by
    have := target_length t
    have := expr_length e
    have := assigns_length (a :: as)
    obtain ⟨a1, a2⟩ := a
    simp only [szAssigns, Pretty.assigns, List.length_append, List.length_cons, List.length_nil] at *
    omega

theorem importNames_length : (names : List (String × Option String)) →
    names.length ≤ (Pretty.importNames names).length
  | [] => by simp
  | [(n, a)] => by cases a <;> simp [Pretty.importNames, Pretty.importName]
  | (n, a) :: q :: qs => by
    have := importNames_length (q :: qs)
    cases a <;> simp only [Pretty.importNames, Pretty.importName, List.length_append, List.length_cons,
      List.length_nil] at * <;> omega

mutual
theorem node_length : (nd : Node) → nd.sz + 1 ≤ (Pretty.node nd).length
  | .text _ => by simp [Node.sz, Pretty.node]
  | .output e => by
    have := expr_length e
    simp [Node.sz, Pretty.node]; omega
  | .if_ [] els => by
    have := nodes_length els
    simp [Node.sz, Node.szBranches, Pretty.node, Pretty.tag]; omega
  | .if_ ((t, b) :: bs) els => by
    have := expr_length t
    have := nodes_length b
    have := elifs_length bs
    have := nodes_length els
    have : Node.szs els ≤ (if els.isEmpty then [] else Pretty.tag [Pretty.nm "else"] ++ Pretty.nodes els).length := by
      cases els <;> simp_all [Node.szs, Pretty.tag]; omega
    simp only [Node.sz, Node.szBranches, Pretty.node, Pretty.tag, List.length_append, List.length_cons,
      List.length_nil] at *
    omega
  | .for_ t it fl rc body els => by
    have := target_length t
    have := expr_length it
    have := nodes_length body
    have := nodes_length els
    rcases fl with _ | f
    · cases rc <;> cases els <;> simp_all [Node.sz, Node.szs, Expr.szOpt, Pretty.node, Pretty.tag, Pretty.nodes] <;>
        omega
    · have := expr_length f
      cases rc <;> cases els <;> simp_all [Node.sz, Node.szs, Expr.szOpt, Pretty.node, Pretty.tag, Pretty.nodes] <;>
        omega
  | .set t e => by
    have := target_length t
    have := expr_length e
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .setBlock t fs body => by
    have := target_length t
    have := chainPipe_length fs
    have := nodes_length body
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .macro _ ps body => by
    have := params_length ps
    have := nodes_length body
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .callBlock ps c body => by
    have := params_length ps
    have := expr_length c
    have := nodes_length body
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .include e ig wc => by
    have := expr_length e
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .extends e => by
    have := expr_length e
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .import_ e _ wc => by
    have := expr_length e
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .fromImport e names wc => by
    have := expr_length e
    have := importNames_length names
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .block _ _ _ body => by
    have := nodes_length body
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .with_ as body => by
    have := assigns_length as
    have := nodes_length body
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .filterBlock fs body => by
    have := chain_length fs
    have := nodes_length body
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
  | .autoescape e body => by
    have := expr_length e
    have := nodes_length body
    simp only [Node.sz, Pretty.node, Pretty.tag, List.length_append, List.length_cons, List.length_nil] at *
    omega
theorem nodes_length : (b : List Node) → Node.szs b ≤ (Pretty.nodes b).length
  | [] => by simp [Node.szs, Pretty.nodes]
  | nd :: ns => by
    have := node_length nd
    have := nodes_length ns
    simp only [Node.szs, Pretty.nodes, List.length_append] at *
    omega
theorem elifs_length : (bs : List (Expr × List Node)) → Node.szBranches bs ≤ (Pretty.elifs bs).length
  | [] => by simp [Node.szBranches, Pretty.elifs]
  | (t, b) :: bs => by
    have := expr_length t
    have := nodes_length b
    have := elifs_length bs
    simp only [Node.szBranches, Pretty.elifs, Pretty.tag, List.length_append, List.length_cons,
      List.length_nil] at *
    omega
end

/-- The parser reads a well-formed template's printed token stream back. -/
theorem parseTokens_pretty (t : List Node) (h : WellFormed t) : parseTokens (Pretty.nodes t) = .ok t := by
  have hl := nodes_length t
  have hb := body_ok t h [] [] (by simp [EndsOK]) [] [] (Or.inl ⟨rfl, rfl⟩) (fuelFor (Pretty.nodes t))
    (by simp only [fuelFor]; omega)
  simp only [List.append_nil] at hb
  simp [parseTokens, hb]

end LeanJinja2
