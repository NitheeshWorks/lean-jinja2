import LeanJinja2.Proofs.Parser.Expr

/-!
# The parser reads printed statements back

Targets, parameters, filter chains and `with` assignments first, then the
template body by induction on its size: `body_ok` (the subparser reads a
printed body up to an end tag) and `node_ok` (the statement parser reads a
printed tag), proved together.
-/

namespace LeanJinja2

open Parse

set_option linter.unusedSimpArgs false

/-! ## Targets -/

mutual
/-- A target as the expression it is printed as. -/
def Target.toExpr : Target → Expr
  | .name n => .name n
  | .nsAttr n a => .getattr (.name n) a
  | .tuple ts => .tuple (Target.toExprs ts)

def Target.toExprs : List Target → List Expr
  | [] => []
  | t :: ts => t.toExpr :: Target.toExprs ts
end

mutual
theorem Target.print_eq : (t : Target) → t.Plain → Pretty.target t = Pretty.expr t.toExpr
  | .name n, _ => by simp [Pretty.target, Target.toExpr, Pretty.expr]
  | .nsAttr .., h => by simp [Target.Plain] at h
  | .tuple [], _ => by simp [Pretty.target, Pretty.target.targets, Target.toExpr, Target.toExprs, Pretty.expr,
      Pretty.exprs]
  | .tuple [t], h => by
    simp only [Target.Plain, Target.Plain.Plains] at h
    simp [Pretty.target, Target.toExpr, Target.toExprs, Pretty.expr, Target.print_eq t h.1]
  | .tuple (t :: u :: us), h => by
    simp only [Target.Plain] at h
    have := Target.prints_eq (t :: u :: us) h
    simp only [Pretty.target, Target.toExpr, Target.toExprs, Pretty.expr] at this ⊢
    rw [this]
theorem Target.prints_eq : (ts : List Target) → Target.Plain.Plains ts →
    Pretty.target.targets ts = Pretty.exprs (Target.toExprs ts)
  | [], _ => by simp [Pretty.target.targets, Target.toExprs, Pretty.exprs]
  | [t], h => by
    simp only [Target.Plain.Plains] at h
    simp [Pretty.target.targets, Target.toExprs, Pretty.exprs, Target.print_eq t h.1]
  | t :: u :: us, h => by
    simp only [Target.Plain.Plains] at h
    have h1 := Target.print_eq t h.1
    have h2 := Target.prints_eq (u :: us) h.2
    simp only [Target.toExprs] at h2 ⊢
    simp [Pretty.target.targets, Pretty.exprs, h1, h2]
end

end LeanJinja2

namespace LeanJinja2

open Parse

mutual
theorem Target.toExpr_back : (t : Target) → t.Plain → exprToTarget t.toExpr = some t
  | .name n, _ => by simp [Target.toExpr, exprToTarget]
  | .nsAttr .., h => by simp [Target.Plain] at h
  | .tuple ts, h => by
    simp only [Target.Plain] at h
    simp [Target.toExpr, exprToTarget, Target.toExprs_back ts h]
theorem Target.toExprs_back : (ts : List Target) → Target.Plain.Plains ts →
    exprToTarget.go (Target.toExprs ts) = some ts
  | [], _ => by simp [Target.toExprs, exprToTarget.go]
  | t :: ts, h => by
    simp only [Target.Plain.Plains] at h
    simp [Target.toExprs, exprToTarget.go, Target.toExpr_back t h.1, Target.toExprs_back ts h.2]
end

mutual
theorem Target.toExpr_WF : (t : Target) → t.Plain → t.toExpr.WF
  | .name n, h => by simpa [Target.toExpr, Expr.WF, Target.Plain] using h
  | .nsAttr .., h => by simp [Target.Plain] at h
  | .tuple ts, h => by
    simp only [Target.Plain] at h
    simpa [Target.toExpr, Expr.WF] using Target.toExprs_WF ts h
theorem Target.toExprs_WF : (ts : List Target) → Target.Plain.Plains ts → Expr.WFs (Target.toExprs ts)
  | [], _ => by simp [Target.toExprs, Expr.WFs]
  | t :: ts, h => by
    simp only [Target.Plain.Plains] at h
    simp [Target.toExprs, Expr.WFs, Target.toExpr_WF t h.1, Target.toExprs_WF ts h.2]
end

/-- A target's size, for fuel. -/
def Target.sz (t : Target) : Nat := t.toExpr.sz

/-- The parser reads a printed target before a token that is not a comma or a dot. -/
theorem target_ok {t : Target} {extra : List String} {withNs : Bool} {rest : List TokKind}
    (ht : t.Settable) (hns : withNs = false → t.Plain)
    (hextra : ∀ s ∈ extra, s = "in") (hr : NotStr rest)
    (hrc : ∀ x, rest.head? = some x → x ≠ .op .comma ∧ x ≠ .op .dot) (n : Nat) (hn : 30 * t.sz ≤ n) :
    pTarget n extra withNs (Pretty.target t ++ rest) = .ok (t, rest) := by
  have hcomma : isOp .comma rest.head? = false := by
    cases h : rest.head? with
    | none => rfl
    | some x =>
      have := (hrc x h).1
      cases x with
      | op o => cases o <;> simp_all
      | _ => rfl
  cases t with
  | name v =>
    simp only [Target.Settable, Target.Plain, VarName] at ht
    have hnotEnd : isTupleEnd extra (some (.name v)) = false := by
      simp only [isTupleEnd]
      cases h : extra.contains v with
      | false => rfl
      | true =>
        have := hextra v (by simpa using h)
        subst this; simp [reservedNames] at ht
    have hdot : ∀ (r' : List TokKind), rest = .op .dot :: r' → False := by
      intro r' h; exact (hrc _ (by simp [h])).2 rfl
    simp only [pTarget, Pretty.target, List.cons_append, List.nil_append, List.head?_cons, hnotEnd,
      Bool.false_eq_true, ↓reduceIte, pTargetPrimary, constName_var ht.2, Option.isSome_none, bind,
      Except.bind]
    cases withNs with
    | false => simp [hcomma]
    | true =>
      simp only [↓reduceIte]
      cases rest with
      | nil => simp
      | cons x xs =>
        have hx := hrc x rfl
        cases x with
        | op o => cases o <;> simp_all
        | _ => simp_all
  | nsAttr ns a =>
    have hp : withNs = true := by
      cases withNs with
      | false => exact absurd (hns rfl) (by simp [Target.Plain])
      | true => rfl
    subst hp
    simp only [Target.Settable, VarName] at ht
    have hnotEnd : isTupleEnd extra (some (.name ns)) = false := by
      simp only [isTupleEnd]
      cases h : extra.contains ns with
      | false => rfl
      | true =>
        have := hextra ns (by simpa using h)
        subst this; simp [reservedNames] at ht
    simp [pTarget, Pretty.target, hnotEnd, pTargetPrimary, constName_var ht.1.2, bind, Except.bind, hcomma]
  | tuple ts =>
    have hplain : (Target.tuple ts).Plain := by simpa [Target.Settable] using ht
    rw [Target.print_eq _ hplain]
    have hw := Target.toExpr_WF _ hplain
    have hp := prim_ok _ hw rest hr n (by simpa [Target.sz] using hn)
    have hhead : (Pretty.expr (Target.tuple ts).toExpr ++ rest).head? = some (.op .lparen) := by
      simp only [Target.toExpr]
      match ts with
      | [] | [_] | _ :: _ :: _ => simp [Pretty.expr, Target.toExprs]
    have hcons : ∃ r', Pretty.expr (Target.tuple ts).toExpr ++ rest = .op .lparen :: r' := by
      cases h : Pretty.expr (Target.tuple ts).toExpr ++ rest with
      | nil => simp [h] at hhead
      | cons x xs => simp [h] at hhead; exact ⟨xs, by rw [hhead]⟩
    obtain ⟨r', hr'⟩ := hcons
    have hend : isTupleEnd extra (some (.op .lparen)) = false := rfl
    rw [hr'] at hp ⊢
    simp [pTarget, hend, pTargetPrimary, hp, bind, Except.bind, Target.toExpr_back _ hplain, hcomma]

end LeanJinja2

namespace LeanJinja2

open Parse

/-! ## Parameters, filter chains, assignments -/

def szParams : List Param → Nat
  | [] => 0
  | (_, d) :: ps => Expr.szOpt d + szParams ps + 1

theorem pParamName_ok {p : String} (hp : VarName p) (rest : List TokKind) :
    pParamName (.name p :: rest) = .ok (p, rest) := by
  simp [pParamName, constName_var hp.2]

theorem paramDefault_none {rest : List TokKind} (hra : ∀ x, rest.head? = some x → x ≠ .op .assign) (n : Nat) :
    pParamDefault n rest = .ok (none, rest) := by
  have : isOp .assign rest.head? = false := by
    cases h : rest.head? with
    | none => rfl
    | some x =>
      have := hra x h
      cases x with
      | op o => cases o <;> simp_all
      | _ => rfl
  simp [pParamDefault, this]

theorem paramDefault_some {e : Expr} (hw : e.WF) {rest : List TokKind} (hr : Stop 10 rest) (n : Nat)
    (hn : 30 * e.sz + 12 ≤ n) :
    pParamDefault n (.op .assign :: (Pretty.expr e ++ rest)) = .ok (some e, rest) := by
  obtain ⟨k, hk⟩ : ∃ k, 30 * e.sz = k + 1 := ⟨30 * e.sz - 1, by have := e.sz_pos; omega⟩
  have hp := prim_ok e hw
  rw [hk] at hp
  have he := (hp.exprOK hw) rest hr n (by omega)
  simp [pParamDefault, bind, Except.bind, he]

theorem params_ok : ∀ (ps : List Param) (had : Bool) (rest : List TokKind), ParamsWF had ps →
    ∀ n, 30 * szParams ps + 13 ≤ n → pParams (n + 1) had (Pretty.params ps ++ .op .rparen :: rest) = .ok (ps, rest)
  | [], _, rest, _, n, _ => by simp [pParams, Pretty.params]
  | (p, d) :: ps, had, rest, hw, n, hn => by
    simp only [ParamsWF] at hw
    obtain ⟨hp, hwd, hdef, hwps⟩ := hw
    have hnd : (d.isNone && had) = false := by
      cases d <;> cases had <;> simp_all
    -- the tokens after this parameter
    have tailOK : ∀ tl : List TokKind, Stop 10 tl → (∀ x, tl.head? = some x → x ≠ .op .assign) →
        pParamDefault n ((Pretty.param (p, d)).tail ++ tl) = .ok (d, tl) := by
      intro tl hs ha
      cases d with
      | none => simpa [Pretty.param] using paramDefault_none ha n
      | some e =>
        simp only [Expr.WFOpt] at hwd
        simpa [Pretty.param] using paramDefault_some hwd hs n (by simp [szParams, Expr.szOpt] at hn; omega)
    have hhead : Pretty.param (p, d) = .name p :: (Pretty.param (p, d)).tail := by cases d <;> rfl
    cases ps with
    | nil =>
      have ht := tailOK (.op .rparen :: rest) (stop_rp 10 rest) (by intro x hx; simp at hx; subst hx; simp)
      simp only [Pretty.params]
      rw [hhead]
      simp [pParams, pParamName_ok hp, bind, Except.bind, ht, hnd]
    | cons q qs =>
      have ih := params_ok (q :: qs) (had || d.isSome) rest hwps (n - 1) (by simp [szParams] at hn ⊢; omega)
      obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by simp [szParams] at hn; omega⟩
      have ht := tailOK (.op .comma :: (Pretty.params (q :: qs) ++ .op .rparen :: rest))
        (stop_cons _ _ (by simp [contLevel])) (by intro x hx; simp at hx; subst hx; simp)
      have hex : Pretty.params ((p, d) :: q :: qs) = Pretty.param (p, d) ++ .op .comma :: Pretty.params (q :: qs) := by
        simp [Pretty.params]
      rw [hex, hhead]
      simp only [Nat.add_sub_cancel] at ih
      simp only [List.cons_append, List.append_assoc] at ht ⊢
      rw [pParams]
      simp [pParamName_ok hp, bind, Except.bind, ht, hnd, expect, ih]

end LeanJinja2

namespace LeanJinja2

open Parse

def FilterCall.sz (f : FilterCall) : Nat := Expr.szs f.args + Expr.szKw f.kwargs + 1

def szChain : List FilterCall → Nat
  | [] => 0
  | f :: fs => f.sz + szChain fs

theorem args_items_ok {args : List Expr} (hwa : Expr.WFs args) :
    ∀ x ∈ args, x.WF ∧ ExprOK x (30 * x.sz + 12) := by
  intro x hx
  have hwx := WFs_mem hwa hx
  have hp := prim_ok x hwx
  obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
  rw [hk] at hp
  exact ⟨hwx, (hp.exprOK hwx).mono (by omega)⟩

theorem kw_items_ok {kw : List (String × Expr)} (hwk : Expr.WFKw kw) :
    ∀ p ∈ kw, VarName p.1 ∧ p.2.WF ∧ ExprOK p.2 (30 * p.2.sz + 12) := by
  intro p hp'
  obtain ⟨hn, hwv⟩ := WFKw_mem hwk hp'
  have hp := prim_ok p.2 hwv
  obtain ⟨k, hk⟩ : ∃ k, 30 * p.2.sz = k + 1 := ⟨30 * p.2.sz - 1, by have := p.2.sz_pos; omega⟩
  rw [hk] at hp
  exact ⟨hn, hwv, (hp.exprOK hwv).mono (by omega)⟩

/-- A token that can follow a filter in a chain. -/
def FilterFollow (rest : List TokKind) : Prop :=
  rest.head? = some .blockEnd ∨ rest.head? = some (.op .pipe)

theorem filterOne_ok (f : FilterCall) (hw : f.WF) (rest : List TokKind) (hr : FilterFollow rest) (n : Nat)
    (hn : 30 * f.sz + 15 ≤ n) : pFilterOne n (Pretty.filterCall f ++ rest) = .ok (f, rest) := by
  obtain ⟨nm, args, kw⟩ := f
  simp only [FilterCall.WF] at hw
  obtain ⟨_, hwa, hwk⟩ := hw
  obtain ⟨n, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by simp [FilterCall.sz] at hn; omega⟩
  have hdot : ∀ ts : List TokKind, (ts.head? = some .blockEnd ∨ ts.head? = some (.op .pipe) ∨
      ts.head? = some (.op .lparen)) → pDotted (n + 1) nm ts = .ok (nm, ts) := by
    intro ts h
    cases ts with
    | nil => simp at h
    | cons t ts => rcases h with h | h | h <;> simp at h <;> subst h <;> rfl
  simp only [Pretty.filterCall]
  rw [parenArgs_eq args kw (fun y hy => WFs_mem hwa hy)]
  by_cases ha : args = [] ∧ kw = []
  · obtain ⟨rfl, rfl⟩ := ha
    have hnl : isOp .lparen rest.head? = false := by
      rcases hr with h | h <;> simp [h]
    simp [pFilterOne, expectName, bind, Except.bind, hdot rest (by rcases hr with h | h <;> simp [h]), hnl]
  · have hc := callArgs_ok args kw rest (args_items_ok hwa) (kw_items_ok hwk) (n + 1)
      (by simp [FilterCall.sz] at hn; omega)
    simp only [ha, ↓reduceIte, List.cons_append, List.append_assoc, List.nil_append]
    simp [pFilterOne, expectName, bind, Except.bind, pDotted_lparen, hc]

theorem chainPipe_ok : ∀ (fs : List FilterCall) (rest : List TokKind), (∀ f ∈ fs, f.WF) →
    ∀ n, 30 * szChain fs + 17 ≤ n →
    pFilterChain n false ((fs.flatMap fun f => [Pretty.op .pipe] ++ Pretty.filterCall f) ++ .blockEnd :: rest) =
      .ok (fs, .blockEnd :: rest)
  | [], rest, _, n, hn => by
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    simp [pFilterChain]
  | f :: fs, rest, hw, n, hn => by
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have hf := filterOne_ok f (hw f List.mem_cons_self)
      ((fs.flatMap fun f => [Pretty.op .pipe] ++ Pretty.filterCall f) ++ .blockEnd :: rest)
      (by cases fs <;> simp [FilterFollow]) n (by simp [szChain, FilterCall.sz] at hn ⊢; omega)
    have ih := chainPipe_ok fs rest (fun g hg => hw g (List.mem_cons_of_mem _ hg)) n (by simp [szChain, FilterCall.sz] at hn ⊢; omega)
    simp only [List.flatMap_cons, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] at hf ih ⊢
    rw [pFilterChain]
    simp [bind, Except.bind, hf, ih]

theorem pipe_filterChain : ∀ (fs : List FilterCall), fs ≠ [] →
    Pretty.op .pipe :: Pretty.filterChain fs = fs.flatMap fun f => [Pretty.op .pipe] ++ Pretty.filterCall f
  | [], h => absurd rfl h
  | [f], _ => by simp [Pretty.filterChain]
  | f :: g :: gs, _ => by
    have := pipe_filterChain (g :: gs) (by simp)
    simp only [Pretty.filterChain, List.flatMap_cons] at this ⊢
    rw [List.cons_append, List.cons_append, ← this]
    simp

theorem chainFirst_ok (fs : List FilterCall) (rest : List TokKind) (hne : fs ≠ []) (hw : ∀ f ∈ fs, f.WF)
    (n : Nat) (hn : 30 * szChain fs + 17 ≤ n) :
    pFilterChain n true (Pretty.filterChain fs ++ .blockEnd :: rest) = .ok (fs, .blockEnd :: rest) := by
  obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  match fs, hne with
  | [f], _ =>
    have hf := filterOne_ok f (hw f List.mem_cons_self) (.blockEnd :: rest) (by simp [FilterFollow]) n
      (by simp [szChain, FilterCall.sz] at hn ⊢; omega)
    have hc := chainPipe_ok [] rest (by simp) n (by simp [szChain, FilterCall.sz] at hn ⊢; omega)
    simp only [Pretty.filterChain]
    rw [pFilterChain]
    simp only [List.flatMap_nil, List.nil_append] at hc
    simp [bind, Except.bind, hf, hc]
  | f :: g :: gs, _ =>
    have hc := chainPipe_ok (g :: gs) rest (fun h hh => hw h (List.mem_cons_of_mem _ hh)) n
      (by simp [szChain, FilterCall.sz] at hn ⊢; omega)
    rw [← pipe_filterChain (g :: gs) (by simp)] at hc
    have hf := filterOne_ok f (hw f List.mem_cons_self) (.op .pipe :: (Pretty.filterChain (g :: gs) ++ .blockEnd :: rest))
      (by simp [FilterFollow]) n (by simp [szChain, FilterCall.sz] at hn ⊢; omega)
    have hex : Pretty.filterChain (f :: g :: gs) = Pretty.filterCall f ++ .op .pipe :: Pretty.filterChain (g :: gs) := by
      simp [Pretty.filterChain]
    rw [hex]
    simp only [List.append_assoc, List.cons_append] at hf hc ⊢
    rw [pFilterChain]
    simp [bind, Except.bind, hf, hc]

end LeanJinja2

namespace LeanJinja2

open Parse

def szAssigns : List (Target × Expr) → Nat
  | [] => 0
  | (t, e) :: as => t.sz + e.sz + szAssigns as + 1

/-- What follows an assignment in a `with` tag: more assignments after a comma, or nothing. -/
def assignsTail (as : List (Target × Expr)) : List TokKind :=
  if as = [] then [] else .op .comma :: Pretty.assigns as

theorem assigns_cons (t : Target) (e : Expr) (as : List (Target × Expr)) :
    Pretty.assigns ((t, e) :: as) = Pretty.target t ++ .op .assign :: (Pretty.expr e ++ assignsTail as) := by
  cases as <;> simp [Pretty.assigns, assignsTail]

theorem target_head (t : Target) : ∃ x r, Pretty.target t = x :: r ∧ x ≠ .blockEnd := by
  cases t with
  | tuple ts' => match ts' with | [] | [_] | _ :: _ :: _ => simp [Pretty.target]
  | _ => simp [Pretty.target]

theorem target_head_ne (t : Target) (ts : List TokKind) :
    (Pretty.target t ++ ts).head? ≠ some .blockEnd := by
  obtain ⟨x, r, hx, hne⟩ := target_head t
  simp [hx, hne]

/-- One assignment, then whatever `pWithAssigns` reads after it. -/
theorem assign_step {t : Target} {e : Expr} {as : List (Target × Expr)} {first : Bool} {rest : List TokKind}
    (ht : t.Plain) (he : e.WF) (n : Nat) (hn : 30 * (t.sz + e.sz) + 12 ≤ n)
    (hmore : pWithAssigns n false (assignsTail as ++ .blockEnd :: rest) = .ok (as, .blockEnd :: rest)) :
    pWithAssigns (n + 1) first ((if first then [] else [.op .comma]) ++
      (Pretty.assigns ((t, e) :: as) ++ .blockEnd :: rest)) = .ok ((t, e) :: as, .blockEnd :: rest) := by
  obtain ⟨k, hk⟩ : ∃ k, 30 * e.sz = k + 1 := ⟨30 * e.sz - 1, by have := e.sz_pos; omega⟩
  have hpe := prim_ok e he
  rw [hk] at hpe
  have hstop : Stop 10 (assignsTail as ++ .blockEnd :: rest) := by
    by_cases h : as = [] <;> simp [assignsTail, h] <;> exact stop_cons _ _ (by simp [contLevel])
  have hexpr := (hpe.exprOK he) _ hstop n (by omega)
  have htarget := target_ok (t := t) (extra := []) (withNs := false)
    (rest := .op .assign :: (Pretty.expr e ++ (assignsTail as ++ .blockEnd :: rest)))
    (by cases t <;> simp_all [Target.Settable, Target.Plain]) (fun _ => ht) (by simp)
    (by intro s; simp) (by intro x hx; simp at hx; subst hx; simp) n (by omega)
  have hcomma : optComma first ((if first then [] else [TokKind.op .comma]) ++
      (Pretty.target t ++ .op .assign :: (Pretty.expr e ++ (assignsTail as ++ .blockEnd :: rest)))) =
      .ok ((), Pretty.target t ++ .op .assign :: (Pretty.expr e ++ (assignsTail as ++ .blockEnd :: rest))) := by
    cases first <;> simp [optComma, expect]
  have hhead : ((if first then [] else [TokKind.op .comma]) ++
      (Pretty.target t ++ .op .assign :: (Pretty.expr e ++ (assignsTail as ++ .blockEnd :: rest)))).head? ≠
      some .blockEnd := by
    cases first
    · simp
    · simpa using target_head_ne t (.op .assign :: (Pretty.expr e ++ (assignsTail as ++ .blockEnd :: rest)))
  rw [assigns_cons]
  simp only [List.append_assoc, List.cons_append] at hhead hcomma ⊢
  rw [pWithAssigns]
  obtain ⟨x, r, hx, hne⟩ := target_head t
  simp [bind, Except.bind, hcomma, htarget, expect, hexpr, hmore]
  cases first <;> simp [hx, hne]

theorem assignsTail_ok : ∀ (as : List (Target × Expr)) (rest : List TokKind), Node.AssignsWF as →
    ∀ n, 30 * szAssigns as + 13 ≤ n →
    pWithAssigns (n + 1) false (assignsTail as ++ .blockEnd :: rest) = .ok (as, .blockEnd :: rest)
  | [], rest, _, n, _ => by simp [assignsTail, pWithAssigns]
  | (t, e) :: as, rest, hw, n, hn => by
    simp only [Node.AssignsWF] at hw
    obtain ⟨ht, he, has⟩ := hw
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by simp [szAssigns] at hn; omega⟩
    have ih := assignsTail_ok as rest has n (by simp [szAssigns] at hn; omega)
    have := assign_step (first := false) ht he (n + 1) (by simp [szAssigns, Target.sz] at hn ⊢; omega) ih
    simpa [assignsTail] using this

theorem assigns_ok (as : List (Target × Expr)) (rest : List TokKind) (hw : Node.AssignsWF as) (n : Nat)
    (hn : 30 * szAssigns as + 14 ≤ n) :
    pWithAssigns (n + 1) true (Pretty.assigns as ++ .blockEnd :: rest) = .ok (as, .blockEnd :: rest) := by
  match as, hw with
  | [], _ => simp [Pretty.assigns, pWithAssigns]
  | (t, e) :: as, hw =>
    simp only [Node.AssignsWF] at hw
    obtain ⟨ht, he, has⟩ := hw
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by simp [szAssigns] at hn; omega⟩
    have ih := assignsTail_ok as rest has n (by simp [szAssigns] at hn; omega)
    simpa using assign_step (first := true) ht he (n + 1) (by simp [szAssigns, Target.sz] at hn ⊢; omega) ih

end LeanJinja2

namespace LeanJinja2

open Parse

/-! ## Single expressions where a tuple may stand -/

theorem isOp_false {o : Op} {r : List TokKind} (h : ∀ x, r.head? = some x → x ≠ .op o) : isOp o r.head? = false := by
  cases hr : r.head? with
  | none => rfl
  | some x =>
    have := h x hr
    cases x with
    | op p => simp only [isOp, beq_eq_false_iff_ne]; intro hp; exact this (by rw [hp])
    | _ => rfl

theorem isName_false {s : String} {r : List TokKind} (h : ∀ x, r.head? = some x → x ≠ .name s) :
    isName s r.head? = false := by
  cases hr : r.head? with
  | none => rfl
  | some x =>
    have := h x hr
    cases x with
    | name p => simp only [isName, beq_eq_false_iff_ne]; intro hp; exact this (by rw [hp])
    | _ => rfl

theorem tuple_one {e : Expr} (hw : e.WF) {extra : List String} (hx : ∀ s ∈ extra, s = "recursive")
    (wc : Bool) {r : List TokKind} (hr : Stop (if wc then 10 else 9) r) (hc : ∀ x, r.head? = some x → x ≠ .op .comma)
    (n : Nat) (hn : 30 * e.sz + 13 ≤ n) : pTuple (n + 1) wc extra false (Pretty.expr e ++ r) = .ok (e, r) := by
  obtain ⟨k, hk⟩ : ∃ k, 30 * e.sz = k + 1 := ⟨30 * e.sz - 1, by have := e.sz_pos; omega⟩
  have hp := prim_ok e hw
  rw [hk] at hp
  obtain ⟨t, hst, hh⟩ := expr_head' hw
  have hend : isTupleEnd extra (some t) = false := by
    cases t with
    | name s =>
      simp only [isTupleEnd]
      cases hcs : extra.contains s with
      | false => rfl
      | true =>
        have := hx s (by simpa using hcs)
        subst this
        simp [StartTok, reservedNames] at hst
    | op o => cases o <;> simp_all [StartTok, isTupleEnd]
    | _ => simp_all [StartTok, isTupleEnd]
  have hexpr : pExpr n wc (Pretty.expr e ++ r) = .ok (e, r) := by
    cases wc with
    | true => exact (hp.exprOK hw) r (by simpa using hr) n (by omega)
    | false => exact PrimOK.exprNoCond hp hw (by simpa using hr) n (by omega)
  simp [pTuple, hh, hend, bind, Except.bind, hexpr, isOp_false hc]

/-! ## End tags -/

/-- How a body ends: at the end of input, or at one of the end tags `ends`
(the subparser then stops at the tag's name). -/
def EndsAt (ends : List String) (R R' : List TokKind) : Prop :=
  (R = [] ∧ R' = []) ∨ ∃ e R2, e ∈ ends ∧ R = .blockBegin :: .name e :: R2 ∧ R' = .name e :: R2

/-- End tags are not statement keywords. -/
def EndsOK (ends : List String) : Prop := ∀ s ∈ ends, s ∉ statementKeywords

theorem EndsOK.contains_false {ends : List String} (h : EndsOK ends) {k : String} (hk : k ∈ statementKeywords) :
    ends.contains k = false := by
  cases hc : ends.contains k with
  | false => rfl
  | true => exact absurd hk (h k (by simpa using hc))

theorem statements_ok {stack : TagStack} {tag e : String} {ends : List String} {drop : Bool}
    {body : List Node} {R2 : List TokKind} {n : Nat}
    (hb : subparse n ((tag, ends) :: stack) ends (Pretty.nodes body ++ .blockBegin :: .name e :: R2) =
      .ok (body, .name e :: R2)) :
    pStatements (n + 1) stack tag ends drop (.blockEnd :: (Pretty.nodes body ++ .blockBegin :: .name e :: R2)) =
      .ok (body, if drop then R2 else .name e :: R2) := by
  simp [pStatements, expect, bind, Except.bind, hb]

end LeanJinja2
