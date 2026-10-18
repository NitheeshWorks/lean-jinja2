import LeanJinja2.Proofs.Parser.Levels

/-!
# The parser reads printed expressions back

`Pretty.expr e` is an atom or a parenthesised compound; `prim_ok` says the
primary parser reads it back to `e`, with fuel proportional to the size of
`e`, whatever follows (short of a token that would continue the operand).
The proof is by induction on the size: a compound's operands are read by the
level lemmas of `Levels.lean` at the operator's level.
-/

namespace LeanJinja2

open Parse

set_option linter.unusedSimpArgs false

/-! ## Size -/

mutual
def Expr.sz : Expr → Nat
  | .const _ | .name _ => 1
  | .tuple xs | .list xs | .concat xs => 1 + Expr.szs xs
  | .dict ps => 1 + Expr.szPairs ps
  | .getattr e _ | .unop _ e => 1 + e.sz
  | .getitem e i => 1 + e.sz + i.sz
  | .slice a b c => 1 + Expr.szOpt a + Expr.szOpt b + Expr.szOpt c
  | .call f args kw | .filter f _ args kw | .test f _ args kw => 1 + f.sz + Expr.szs args + Expr.szKw kw
  | .binop _ l r => 1 + l.sz + r.sz
  | .compare e ops => 1 + e.sz + Expr.szCmps ops
  | .cond t b e => 1 + t.sz + b.sz + Expr.szOpt e

def Expr.szs : List Expr → Nat
  | [] => 0
  | x :: xs => x.sz + Expr.szs xs + 1

def Expr.szPairs : List (Expr × Expr) → Nat
  | [] => 0
  | (k, v) :: ps => k.sz + v.sz + Expr.szPairs ps + 1

def Expr.szKw : List (String × Expr) → Nat
  | [] => 0
  | (_, v) :: kw => v.sz + Expr.szKw kw + 1

def Expr.szCmps : List (CmpOp × Expr) → Nat
  | [] => 0
  | (_, e) :: ops => e.sz + Expr.szCmps ops + 1

def Expr.szOpt : Option Expr → Nat
  | none => 0
  | some e => e.sz
end

theorem Expr.sz_pos (e : Expr) : 1 ≤ e.sz := by
  cases e <;> simp [Expr.sz] <;> omega

/-! ## The first token of a printed expression -/

/-- A token that may start a printed expression. -/
def StartTok : TokKind → Prop
  | .op .lparen | .op .lbracket | .op .lbrace | .int _ | .float .. | .str _ => True
  | .name s => s ∉ reservedNames ∨ s = "none" ∨ s = "true" ∨ s = "false"
  | _ => False

theorem constToks_head (c : Const) : ∃ t r, Pretty.constToks c = t :: r ∧ StartTok t := by
  cases c with
  | bool b => cases b <;> exact ⟨_, _, rfl, by simp [StartTok]⟩
  | _ => exact ⟨_, _, rfl, by simp [StartTok, reservedNames]⟩

theorem ex_head {l : List TokKind} (h : ∃ t, l.head? = some t ∧ StartTok t) :
    ∃ t r, l = t :: r ∧ StartTok t := by
  obtain ⟨t, ht, hs⟩ := h
  cases l with
  | nil => simp at ht
  | cons a r => simp at ht; subst ht; exact ⟨a, r, rfl, hs⟩

theorem expr_head (e : Expr) (h : e.WF) : ∃ t r, Pretty.expr e = t :: r ∧ StartTok t := by
  apply ex_head
  cases e with
  | const c =>
    obtain ⟨t, r, h1, h2⟩ := constToks_head c
    exact ⟨t, by simp [Pretty.expr, h1], h2⟩
  | name n =>
    simp only [Expr.WF, VarName] at h
    exact ⟨.name n, by simp [Pretty.expr], Or.inl h.2⟩
  | tuple xs =>
    match xs with
    | [] => exact ⟨.op .lparen, by simp [Pretty.expr], trivial⟩
    | [x] => exact ⟨.op .lparen, by simp [Pretty.expr], trivial⟩
    | x :: y :: zs => exact ⟨.op .lparen, by simp [Pretty.expr], trivial⟩
  | list xs => exact ⟨.op .lbracket, by simp [Pretty.expr], trivial⟩
  | dict ps => exact ⟨.op .lbrace, by simp [Pretty.expr], trivial⟩
  | slice => simp [Expr.WF] at h
  | unop o e => cases o <;> exact ⟨.op .lparen, by simp [Pretty.expr], trivial⟩
  | concat xs => cases xs <;> exact ⟨.op .lparen, by simp [Pretty.expr], trivial⟩
  | cond t b e => cases e <;> exact ⟨.op .lparen, by simp [Pretty.expr], trivial⟩
  | _ => exact ⟨.op .lparen, by simp [Pretty.expr], trivial⟩

theorem StartTok.noSign {t : TokKind} (h : StartTok t) (r : List TokKind) : NoSign (t :: r) := by
  intro t' ht; simp at ht; subst ht
  cases t with
  | op o => cases o <;> simp_all [StartTok]
  | _ => simp

theorem StartTok.noNot {t : TokKind} (h : StartTok t) (r : List TokKind) : NoNot (t :: r) := by
  simp only [NoNot, List.head?_cons, isName]
  cases t with
  | name s =>
    simp only [StartTok, reservedNames] at h
    simp only [beq_eq_false_iff_ne]
    intro hs; subst hs; simp at h
  | _ => rfl

end LeanJinja2

namespace LeanJinja2

open Parse

/-- The full expression parser reads `e` back before tokens that do not
continue it. -/
def ExprOK (e : Expr) (m : Nat) : Prop :=
  ∀ r, Stop 10 r → Reads (fun n => pExpr n true) m (Pretty.expr e ++ r) e r

/-- A start token is not one of the closers and separators the item loops test. -/
theorem StartTok.not_closer {t : TokKind} (h : StartTok t) :
    isOp .rbracket (some t) = false ∧ isOp .rbrace (some t) = false ∧ isOp .rparen (some t) = false ∧
      isOp .colon (some t) = false ∧ isOp .comma (some t) = false ∧
      isTupleEnd [] (some t) = false := by
  cases t with
  | op o => cases o <;> simp_all [StartTok, isOp, isTupleEnd]
  | name s => simp [isOp, isTupleEnd]
  | _ => simp_all [StartTok, isOp, isTupleEnd]

theorem stop_op (k : Nat) (o : Op) (ts : List TokKind) (h : k < contLevel (.op o)) : Stop k (.op o :: ts) :=
  Stop.cons h

theorem listItems_ok : ∀ (xs : List Expr) (r : List TokKind), (∀ x ∈ xs, x.WF ∧ ExprOK x (30 * x.sz + 12)) →
    Reads pListItems (30 * Expr.szs xs + 13) (Pretty.exprs xs ++ [.op .rbracket] ++ r) xs r
  | [], r, _ => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [pListItems, Pretty.exprs, isOp]
  | [x], r, hx => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hw, hok⟩ := hx x List.mem_cons_self
    obtain ⟨t, tr, ht, hst⟩ := expr_head x hw
    have hx' := hok (.op .rbracket :: r) (stop_op _ _ _ (by simp [contLevel])) n (by simp [Expr.szs] at hn ⊢; omega)
    simp only [Pretty.exprs, List.append_assoc, List.singleton_append] at hx' ⊢
    simp only [pListItems, ht, List.cons_append, List.head?_cons, hst.not_closer.1, Bool.false_eq_true,
      ↓reduceIte, bind, Except.bind]
    rw [← List.cons_append, ← ht, hx']
    simp [isOp]
  | x :: y :: zs, r, hx => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hw, hok⟩ := hx x List.mem_cons_self
    obtain ⟨t, tr, ht, hst⟩ := expr_head x hw
    have hx' := hok (.op .comma :: (Pretty.exprs (y :: zs) ++ [.op .rbracket] ++ r))
      (stop_op _ _ _ (by simp [contLevel])) n (by simp [Expr.szs] at hn ⊢; omega)
    have ih := listItems_ok (y :: zs) r (fun z hz => hx z (List.mem_cons_of_mem _ hz)) n
      (by simp [Expr.szs] at hn ⊢; omega)
    have hex : Pretty.exprs (x :: y :: zs) = Pretty.expr x ++ [.op .comma] ++ Pretty.exprs (y :: zs) := by
      simp [Pretty.exprs]
    rw [hex]
    simp only [List.append_assoc, List.singleton_append] at hx' ⊢
    simp only [pListItems, ht, List.cons_append, List.head?_cons, hst.not_closer.1, Bool.false_eq_true,
      ↓reduceIte, bind, Except.bind]
    rw [← List.cons_append, ← ht, hx']
    simp only [List.singleton_append, List.append_assoc] at ih
    simp [isOp, expect, ih]

end LeanJinja2

namespace LeanJinja2

open Parse

/-- The next token is not a string literal (the primary parser joins adjacent
string literals). -/
def NotStr (r : List TokKind) : Prop := ∀ s, r.head? ≠ some (.str s)

theorem Stop.notStr {k : Nat} {r : List TokKind} (h : Stop k r) : NotStr r := by
  intro s hs
  have := h _ hs
  simp [contLevel] at this

/-- The primary parser reads `e` back before anything but a string literal. -/
def PrimOK (e : Expr) (m : Nat) : Prop :=
  ∀ r, NotStr r → Reads pPrimary m (Pretty.expr e ++ r) e r

section Lift
variable {x : Expr} {m : Nat} {r : List TokKind} (h : PrimOK x (m + 1)) (hw : x.WF)
include h hw

theorem PrimOK.unary (wf : Bool) (hr : Stop (if wf then 1 else 0) r) :
    Reads (fun n => pUnary n wf) (m + 2) (Pretty.expr x ++ r) x r := by
  obtain ⟨t, tr, ht, hst⟩ := expr_head x hw
  refine Reads.unary wf (h r hr.notStr) ?_ hr
  rw [ht]; exact hst.noSign _

theorem PrimOK.pow (hr : Stop 2 r) : Reads pPow (m + 3) (Pretty.expr x ++ r) x r :=
  (PrimOK.unary h hw true (hr.mono (by simp))).pow hr

theorem PrimOK.math2 (hr : Stop 3 r) : Reads pMath2 (m + 4) (Pretty.expr x ++ r) x r :=
  (PrimOK.pow h hw (hr.mono (by omega))).math2 hr

theorem PrimOK.concat (hr : Stop 4 r) : Reads pConcat (m + 5) (Pretty.expr x ++ r) x r :=
  (PrimOK.math2 h hw (hr.mono (by omega))).concat hr

theorem PrimOK.math1 (hr : Stop 5 r) : Reads pMath1 (m + 6) (Pretty.expr x ++ r) x r :=
  (PrimOK.concat h hw (hr.mono (by omega))).math1 hr

theorem PrimOK.compare (hr : Stop 6 r) : Reads pCompare (m + 7) (Pretty.expr x ++ r) x r :=
  (PrimOK.math1 h hw (hr.mono (by omega))).compare hr

theorem PrimOK.noNot : NoNot (Pretty.expr x ++ r) := by
  obtain ⟨t, tr, ht, hst⟩ := expr_head x hw
  rw [ht]; exact hst.noNot _

theorem PrimOK.not (hr : Stop 6 r) : Reads pNot (m + 8) (Pretty.expr x ++ r) x r :=
  (PrimOK.compare h hw hr).not (PrimOK.noNot h hw)

theorem PrimOK.and (hr : Stop 8 r) : Reads pAnd (m + 9) (Pretty.expr x ++ r) x r :=
  (PrimOK.not h hw (hr.mono (by omega))).and hr

theorem PrimOK.or (hr : Stop 9 r) : Reads pOr (m + 10) (Pretty.expr x ++ r) x r :=
  (PrimOK.and h hw (hr.mono (by omega))).or hr

theorem PrimOK.cond (hr : Stop 10 r) : Reads pCond (m + 11) (Pretty.expr x ++ r) x r :=
  (PrimOK.or h hw (hr.mono (by omega))).cond hr

theorem PrimOK.expr (hr : Stop 10 r) : Reads (fun n => pExpr n true) (m + 12) (Pretty.expr x ++ r) x r :=
  (PrimOK.cond h hw hr).expr

theorem PrimOK.exprNoCond (hr : Stop 9 r) :
    Reads (fun n => pExpr n false) (m + 11) (Pretty.expr x ++ r) x r :=
  (PrimOK.or h hw hr).exprNoCond

end Lift

theorem PrimOK.exprOK {x : Expr} {m : Nat} (h : PrimOK x (m + 1)) (hw : x.WF) : ExprOK x (m + 12) :=
  fun _ hr => PrimOK.expr h hw hr

theorem PrimOK.mono {x : Expr} {m m' : Nat} (h : PrimOK x m) (hm : m ≤ m') : PrimOK x m' :=
  fun r hr => (h r hr).mono hm

theorem ExprOK.mono {x : Expr} {m m' : Nat} (h : ExprOK x m) (hm : m ≤ m') : ExprOK x m' :=
  fun r hr => (h r hr).mono hm

end LeanJinja2

namespace LeanJinja2

open Parse

theorem stop_cons (k : Nat) {t : TokKind} (ts : List TokKind) (h : k < contLevel t) : Stop k (t :: ts) :=
  Stop.cons h

/-- A printed expression whose first token is a name is that one token. -/
theorem expr_name_head {x : Expr} (hw : x.WF) {s : String} {tr : List TokKind}
    (h : Pretty.expr x = .name s :: tr) : tr = [] := by
  cases x with
  | slice => simp [Expr.WF] at hw
  | const c => cases c <;> simp_all [Pretty.expr, Pretty.constToks]
  | name n => simp_all [Pretty.expr]
  | tuple xs => match xs with
    | [] | [_] | _ :: _ :: _ => simp_all [Pretty.expr]
  | unop o e => cases o <;> simp_all [Pretty.expr]
  | concat xs => cases xs <;> simp_all [Pretty.expr]
  | cond t b e => cases e <;> simp_all [Pretty.expr]
  | _ => simp_all [Pretty.expr]

theorem kwKey_expr {x : Expr} (hw : x.WF) {t : TokKind} (ht : t ≠ .op .assign) (r : List TokKind) :
    kwKey (Pretty.expr x ++ t :: r) = none := by
  obtain ⟨t0, tr, h0, _⟩ := expr_head x hw
  rw [h0]
  cases t0 with
  | name s =>
    rw [expr_name_head hw h0]
    cases t with
    | op o => cases o <;> simp_all [kwKey]
    | _ => simp [kwKey]
  | _ => simp [kwKey]

theorem StartTok.notStar {t : TokKind} (h : StartTok t) : isStarArg (some t) = false := by
  cases t with
  | op o => cases o <;> simp_all [StartTok, isStarArg]
  | _ => rfl

theorem expr_head' {x : Expr} (hw : x.WF) : ∃ t, StartTok t ∧ ∀ rest, (Pretty.expr x ++ rest).head? = some t := by
  obtain ⟨t, tr, ht, hst⟩ := expr_head x hw
  exact ⟨t, hst, fun rest => by simp [ht]⟩

theorem tupleRest_ok : ∀ (xs : List Expr) (r : List TokKind), (∀ x ∈ xs, x.WF ∧ ExprOK x (30 * x.sz + 12)) →
    Reads (fun n => pTupleRest n true []) (30 * Expr.szs xs + 13)
      (.op .comma :: (Pretty.exprs xs ++ .op .rparen :: r)) xs (.op .rparen :: r)
  | [], r, _ => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [pTupleRest, Pretty.exprs, expect, isTupleEnd, bind, Except.bind]
  | x :: xs, r, hx => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hw, hok⟩ := hx x List.mem_cons_self
    obtain ⟨t, hst, hh⟩ := expr_head' hw
    have hend := hst.not_closer.2.2.2.2.2
    cases xs with
    | nil =>
      have hx' := hok (.op .rparen :: r) (stop_cons _ _ (by simp [contLevel])) n (by simp [Expr.szs] at hn ⊢; omega)
      simp only [Pretty.exprs] at hx' ⊢
      simp [pTupleRest, expect, bind, Except.bind, hh, hend, hx']
    | cons y zs =>
      have hx' := hok (.op .comma :: (Pretty.exprs (y :: zs) ++ .op .rparen :: r))
        (stop_cons _ _ (by simp [contLevel])) n (by simp [Expr.szs] at hn ⊢; omega)
      have ih := tupleRest_ok (y :: zs) r (fun z hz => hx z (List.mem_cons_of_mem _ hz)) n
        (by simp [Expr.szs] at hn ⊢; omega)
      have hex : Pretty.exprs (x :: y :: zs) = Pretty.expr x ++ .op .comma :: Pretty.exprs (y :: zs) := by
        simp [Pretty.exprs]
      rw [hex]
      simp only [List.append_assoc, List.cons_append] at hx' ih ⊢
      simp [pTupleRest, expect, bind, Except.bind, hh, hend, hx', ih]

theorem dictItems_ok : ∀ (ps : List (Expr × Expr)) (r : List TokKind),
    (∀ p ∈ ps, p.1.WF ∧ p.2.WF ∧ ExprOK p.1 (30 * p.1.sz + 12) ∧ ExprOK p.2 (30 * p.2.sz + 12)) →
    Reads pDictItems (30 * Expr.szPairs ps + 13) (Pretty.pairs ps ++ [.op .rbrace] ++ r) ps r
  | [], r, _ => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [pDictItems, Pretty.pairs, isOp]
  | (k, v) :: ps, r, hp => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hwk, hwv, hok, hov⟩ := hp (k, v) List.mem_cons_self
    obtain ⟨t, hst, hh⟩ := expr_head' hwk
    cases ps with
    | nil =>
      have hv := hov (.op .rbrace :: r) (stop_cons _ _ (by simp [contLevel])) n (by simp [Expr.szPairs] at hn ⊢; omega)
      have hk := hok (.op .colon :: (Pretty.expr v ++ .op .rbrace :: r)) (stop_cons _ _ (by simp [contLevel])) n
        (by simp [Expr.szPairs] at hn ⊢; omega)
      simp only [Pretty.pairs, List.append_assoc, List.cons_append, List.singleton_append] at hk hv ⊢
      simp [pDictItems, hh, hst.not_closer.2.1, bind, Except.bind, hk, expect, hv]
    | cons q qs =>
      have ih := dictItems_ok (q :: qs) r (fun p hp' => hp p (List.mem_cons_of_mem _ hp')) n
        (by obtain ⟨_, _⟩ := q; simp [Expr.szPairs] at hn ⊢; omega)
      have hv := hov (.op .comma :: (Pretty.pairs (q :: qs) ++ [.op .rbrace] ++ r))
        (stop_cons _ _ (by simp [contLevel])) n (by simp [Expr.szPairs] at hn ⊢; omega)
      have hk := hok (.op .colon :: (Pretty.expr v ++ .op .comma :: (Pretty.pairs (q :: qs) ++ [.op .rbrace] ++ r)))
        (stop_cons _ _ (by simp [contLevel])) n (by simp [Expr.szPairs] at hn ⊢; omega)
      have hex : Pretty.pairs ((k, v) :: q :: qs) =
          Pretty.expr k ++ .op .colon :: (Pretty.expr v ++ .op .comma :: Pretty.pairs (q :: qs)) := by
        obtain ⟨_, _⟩ := q; simp [Pretty.pairs]
      rw [hex]
      simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at hk hv ih ⊢
      simp [pDictItems, hh, hst.not_closer.2.1, bind, Except.bind, hk, expect, hv, ih]

end LeanJinja2

namespace LeanJinja2

open Parse

theorem expr_ne_nil {x : Expr} (hw : x.WF) : Pretty.expr x ≠ [] := by
  obtain ⟨t, tr, ht, _⟩ := expr_head x hw
  rw [ht]; simp

theorem kwargs_eq_nil {kw : List (String × Expr)} : Pretty.kwargs kw = [] ↔ kw = [] := by
  cases kw with
  | nil => simp [Pretty.kwargs]
  | cons p ps => obtain ⟨k, v⟩ := p; cases ps <;> simp [Pretty.kwargs]

theorem exprs_eq_nil {xs : List Expr} (hw : ∀ x ∈ xs, x.WF) : Pretty.exprs xs = [] ↔ xs = [] := by
  cases xs with
  | nil => simp [Pretty.exprs]
  | cons x xs =>
    have := expr_ne_nil (hw x List.mem_cons_self)
    cases xs <;> simp [Pretty.exprs, this]

/-- The printed arguments of a call. -/
def argToks (args : List Expr) (kw : List (String × Expr)) : List TokKind :=
  Pretty.joinArgs (Pretty.exprs args) (Pretty.kwargs kw)

theorem argToks_nil (kw : List (String × Expr)) : argToks [] kw = Pretty.kwargs kw := by
  simp [argToks, Pretty.joinArgs, Pretty.exprs]

theorem argToks_cons {x : Expr} {xs : List Expr} {kw : List (String × Expr)} (hw : ∀ y ∈ x :: xs, y.WF) :
    argToks (x :: xs) kw =
      Pretty.expr x ++ (if xs = [] ∧ kw = [] then [] else .op .comma :: argToks xs kw) := by
  have hx := expr_ne_nil (hw x List.mem_cons_self)
  cases xs with
  | nil =>
    by_cases hk : kw = []
    · subst hk; simp [argToks, Pretty.joinArgs, Pretty.exprs, Pretty.kwargs]
    · simp [argToks, Pretty.joinArgs, Pretty.exprs, hx, hk, kwargs_eq_nil]
  | cons y ys =>
    have hy : Pretty.exprs (y :: ys) ≠ [] := by
      rw [ne_eq, exprs_eq_nil (fun z hz => hw z (List.mem_cons_of_mem _ hz))]; simp
    have : Pretty.exprs (x :: y :: ys) = Pretty.expr x ++ .op .comma :: Pretty.exprs (y :: ys) := by
      simp [Pretty.exprs]
    simp only [argToks, Pretty.joinArgs, this]
    simp [hy, hx]

theorem kwargs_ok : ∀ (kw : List (String × Expr)) (r : List TokKind),
    (∀ p ∈ kw, VarName p.1 ∧ p.2.WF ∧ ExprOK p.2 (30 * p.2.sz + 12)) →
    Reads pCallArgs (30 * Expr.szKw kw + 13) (Pretty.kwargs kw ++ .op .rparen :: r) ([], kw) r
  | [], r, _ => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [pCallArgs, Pretty.kwargs]
  | (k, v) :: kw, r, hp => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.szKw] at hn; omega⟩
    obtain ⟨_, hwv, hov⟩ := hp (k, v) List.mem_cons_self
    cases kw with
    | nil =>
      have hv := hov (.op .rparen :: r) (stop_cons _ _ (by simp [contLevel])) (n + 1) (by simp [Expr.szKw] at hn ⊢; omega)
      simp only [Pretty.kwargs, List.append_assoc, List.cons_append, List.nil_append] at hv ⊢
      simp [pCallArgs, isStarArg, kwKey, bind, Except.bind, hv, pArgsTail]
    | cons q qs =>
      have ih := kwargs_ok (q :: qs) r (fun p hp' => hp p (List.mem_cons_of_mem _ hp')) n
        (by obtain ⟨_, _⟩ := q; simp [Expr.szKw] at hn ⊢; omega)
      have hv := hov (.op .comma :: (Pretty.kwargs (q :: qs) ++ .op .rparen :: r))
        (stop_cons _ _ (by simp [contLevel])) (n + 1) (by simp [Expr.szKw] at hn ⊢; omega)
      have hex : Pretty.kwargs ((k, v) :: q :: qs) =
          .name k :: .op .assign :: (Pretty.expr v ++ .op .comma :: Pretty.kwargs (q :: qs)) := by
        obtain ⟨_, _⟩ := q; simp [Pretty.kwargs]
      rw [hex]
      simp only [List.append_assoc, List.cons_append] at hv ih ⊢
      simp [pCallArgs, isStarArg, kwKey, bind, Except.bind, hv, pArgsTail, expect, ih]

theorem callArgs_ok : ∀ (args : List Expr) (kw : List (String × Expr)) (r : List TokKind),
    (∀ x ∈ args, x.WF ∧ ExprOK x (30 * x.sz + 12)) →
    (∀ p ∈ kw, VarName p.1 ∧ p.2.WF ∧ ExprOK p.2 (30 * p.2.sz + 12)) →
    Reads pCallArgs (30 * (Expr.szs args + Expr.szKw kw) + 13) (argToks args kw ++ .op .rparen :: r)
      (args, kw) r
  | [], kw, r, _, hk => by
    rw [argToks_nil]
    exact (kwargs_ok kw r hk).mono (by simp [Expr.szs])
  | x :: xs, kw, r, hx, hk => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.szs] at hn; omega⟩
    obtain ⟨hw, hok⟩ := hx x List.mem_cons_self
    obtain ⟨t, hst, hh⟩ := expr_head' hw
    rw [argToks_cons (fun y hy => (hx y hy).1)]
    by_cases hz : xs = [] ∧ kw = []
    · obtain ⟨rfl, rfl⟩ := hz
      have hv := hok (.op .rparen :: r) (stop_cons _ _ (by simp [contLevel])) (n + 1) (by simp [Expr.szs] at hn ⊢; omega)
      simp only [and_self, ↓reduceIte, List.append_nil] at hv ⊢
      simp [pCallArgs, hh, hst.not_closer.2.2.1, hst.notStar, kwKey_expr hw (t := .op .rparen) (by simp),
        bind, Except.bind, hv, pArgsTail]
    · have ih := callArgs_ok xs kw r (fun y hy => hx y (List.mem_cons_of_mem _ hy)) hk n
        (by simp [Expr.szs] at hn ⊢; omega)
      have hv := hok (.op .comma :: (argToks xs kw ++ .op .rparen :: r))
        (stop_cons _ _ (by simp [contLevel])) (n + 1) (by simp [Expr.szs] at hn ⊢; omega)
      simp only [hz, ↓reduceIte, List.append_assoc, List.cons_append] at hv ih ⊢
      simp [pCallArgs, hh, hst.not_closer.2.2.1, hst.notStar, kwKey_expr hw (t := .op .comma) (by simp),
        bind, Except.bind, hv, pArgsTail, expect, ih]

end LeanJinja2

namespace LeanJinja2

open Parse

/-- The parser reads a printed subscript (an index or a slice) up to `]`. -/
theorem subscripted_ok {i : Expr} {m : Nat} (r : List TokKind) (hw : i.SubWF)
    (hok : ∀ x, ((∀ a b c, i ≠ .slice a b c) ∧ i = x ∨
      ∃ a b c, i = .slice a b c ∧ (a = some x ∨ b = some x ∨ c = some x)) → x.WF ∧ ExprOK x m) :
    Reads pSubscribed (m + 3) (Pretty.subscript i ++ .op .rbracket :: r) i (.op .rbracket :: r) := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  cases i with
  | slice a b c =>
    simp only [Expr.SubWF] at hw
    obtain ⟨wa, wb, wc⟩ := hw
    have hpart : ∀ x, (a = some x ∨ b = some x ∨ c = some x) → x.WF ∧ ExprOK x m :=
      fun x hx => hok x (Or.inr ⟨a, b, c, rfl, hx⟩)
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    -- the step: `: c` or nothing, then `]`
    have hstep : ∀ (stop : Option Expr), pSliceStep (n + 1) a stop (Pretty.optStep c ++ .op .rbracket :: r) =
        .ok (.slice a stop c, .op .rbracket :: r) := by
      intro stop
      cases c with
      | none => simp [pSliceStep, Pretty.optStep]
      | some z =>
        obtain ⟨wz, hz⟩ := hpart z (Or.inr (Or.inr rfl))
        obtain ⟨t, hst, hh⟩ := expr_head' wz
        have hv := hz (.op .rbracket :: r) (stop_cons _ _ (by simp [contLevel])) n (by omega)
        simp [pSliceStep, Pretty.optStep, hh, hst.not_closer.1, hst.not_closer.2.2.2.2.1, bind, Except.bind, hv]
    -- the stop
    have hrest : pSliceRest (n + 2) a (Pretty.optExpr b ++ Pretty.optStep c ++ .op .rbracket :: r) =
        .ok (.slice a b c, .op .rbracket :: r) := by
      cases b with
      | none =>
        have hfirst : (isOp .colon (Pretty.optStep c ++ .op .rbracket :: r).head? ||
            isOp .rbracket (Pretty.optStep c ++ .op .rbracket :: r).head? ||
            isOp .comma (Pretty.optStep c ++ .op .rbracket :: r).head?) = true := by
          cases c <;> simp [Pretty.optStep]
        simp only [pSliceRest, Pretty.optExpr, List.nil_append] at hfirst ⊢
        rw [if_pos hfirst]
        exact hstep none
      | some y =>
        obtain ⟨wy, hy⟩ := hpart y (Or.inr (Or.inl rfl))
        obtain ⟨t, hst, hh⟩ := expr_head' wy
        have hs : Stop 10 (Pretty.optStep c ++ .op .rbracket :: r) := by
          cases c <;> simp [Pretty.optStep] <;> exact stop_cons _ _ (by simp [contLevel])
        have hv := hy _ hs (n + 1) (by omega)
        simp only [Pretty.optExpr, List.append_assoc] at hv ⊢
        simp [pSliceRest, hh, hst.not_closer.1, hst.not_closer.2.2.2.1, hst.not_closer.2.2.2.2.1, bind,
          Except.bind, hv, hstep]
    cases a with
    | none =>
      simp only [Pretty.subscript, Pretty.optExpr, List.nil_append, List.append_assoc, List.cons_append]
        at hrest ⊢
      simp [pSubscribed]
      exact (by simpa using hrest)
    | some x =>
      obtain ⟨wx, hx⟩ := hpart x (Or.inl rfl)
      obtain ⟨t, hst, hh⟩ := expr_head' wx
      have hv := hx (.op .colon :: (Pretty.optExpr b ++ Pretty.optStep c ++ .op .rbracket :: r))
        (stop_cons _ _ (by simp [contLevel])) (n + 2) (by omega)
      simp only [Pretty.subscript, Pretty.optExpr, List.append_assoc, List.cons_append] at hv hrest ⊢
      simp [pSubscribed, hh, hst.not_closer.2.2.2.1, bind, Except.bind, hv, hrest]
  | _ =>
    obtain ⟨wi, hi⟩ := hok _ (Or.inl ⟨fun _ _ _ h => Expr.noConfusion h, rfl⟩)
    obtain ⟨t, hst, hh⟩ := expr_head' wi
    have hv := hi (.op .rbracket :: r) (stop_cons _ _ (by simp [contLevel])) n (by omega)
    simp only [Pretty.subscript] at hv hh ⊢
    simp [pSubscribed, hh, hst.not_closer.2.2.2.1, bind, Except.bind, hv]

end LeanJinja2

namespace LeanJinja2

open Parse

theorem subscripts_ok {i : Expr} {m : Nat} (r : List TokKind) (hw : i.SubWF)
    (hok : ∀ x, ((∀ a b c, i ≠ .slice a b c) ∧ i = x ∨
      ∃ a b c, i = .slice a b c ∧ (a = some x ∨ b = some x ∨ c = some x)) → x.WF ∧ ExprOK x m) :
    Reads pSubscripts (m + 5) (Pretty.subscript i ++ .op .rbracket :: r) i r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hs := subscripted_ok r hw hok n (by omega)
  have hnot : isOp .rbracket (Pretty.subscript i ++ .op .rbracket :: r).head? = false := by
    cases i with
    | slice a b c =>
      cases a with
      | none => simp [Pretty.subscript, Pretty.optExpr]
      | some x =>
        obtain ⟨wx, _⟩ := hok x (Or.inr ⟨some x, b, c, rfl, Or.inl rfl⟩)
        obtain ⟨t, hst, hh⟩ := expr_head' wx
        simp only [Pretty.subscript, Pretty.optExpr, List.append_assoc]
        rw [hh]; exact hst.not_closer.1
    | _ =>
      obtain ⟨wi, _⟩ := hok _ (Or.inl ⟨fun _ _ _ h => Expr.noConfusion h, rfl⟩)
      obtain ⟨t, hst, hh⟩ := expr_head' wi
      simp only [Pretty.subscript] at hh ⊢
      rw [hh]; exact hst.not_closer.1
  simp only [pSubscripts, pSubscriptItems, hnot, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, hs]
  simp

end LeanJinja2

namespace LeanJinja2

open Parse

/-! ## Lifting from each level to the top -/

section LiftUp
variable {m : Nat} {ts r : List TokKind} {e : Expr} (hr : Stop 10 r)
include hr

theorem Reads.liftCond (h : Reads pCond (m + 1) ts e r) : Reads (fun n => pExpr n true) (m + 2) ts e r :=
  h.expr

theorem Reads.liftOr (h : Reads pOr (m + 1) ts e r) : Reads (fun n => pExpr n true) (m + 3) ts e r :=
  Reads.liftCond hr (h.cond hr)

theorem Reads.liftAnd (h : Reads pAnd (m + 1) ts e r) : Reads (fun n => pExpr n true) (m + 4) ts e r :=
  Reads.liftOr hr (h.or (hr.mono (by omega)))

theorem Reads.liftNot (h : Reads pNot (m + 1) ts e r) : Reads (fun n => pExpr n true) (m + 5) ts e r :=
  Reads.liftAnd hr (h.and (hr.mono (by omega)))

theorem Reads.liftCompare (h : Reads pCompare (m + 1) ts e r) (hn : NoNot ts) :
    Reads (fun n => pExpr n true) (m + 6) ts e r :=
  Reads.liftNot hr (h.not hn)

theorem Reads.liftMath1 (h : Reads pMath1 (m + 1) ts e r) (hn : NoNot ts) :
    Reads (fun n => pExpr n true) (m + 7) ts e r :=
  Reads.liftCompare hr (h.compare (hr.mono (by omega))) hn

theorem Reads.liftConcat (h : Reads pConcat (m + 1) ts e r) (hn : NoNot ts) :
    Reads (fun n => pExpr n true) (m + 8) ts e r :=
  Reads.liftMath1 hr (h.math1 (hr.mono (by omega))) hn

theorem Reads.liftMath2 (h : Reads pMath2 (m + 1) ts e r) (hn : NoNot ts) :
    Reads (fun n => pExpr n true) (m + 9) ts e r :=
  Reads.liftConcat hr (h.concat (hr.mono (by omega))) hn

theorem Reads.liftPow (h : Reads pPow (m + 1) ts e r) (hn : NoNot ts) :
    Reads (fun n => pExpr n true) (m + 10) ts e r :=
  Reads.liftMath2 hr (h.math2 (hr.mono (by omega))) hn

theorem Reads.liftUnary (h : Reads (fun n => pUnary n true) (m + 1) ts e r) (hn : NoNot ts) :
    Reads (fun n => pExpr n true) (m + 11) ts e r :=
  Reads.liftPow hr (h.pow (hr.mono (by omega))) hn

end LiftUp

/-! ## Binary operators at their levels -/

theorem pow_binop {l r : Expr} {ml mr : Nat} {rest : List TokKind}
    (hl : Reads (fun n => pUnary n true) (ml + 1) (Pretty.expr l ++ .op .pow :: (Pretty.expr r ++ rest)) l
      (.op .pow :: (Pretty.expr r ++ rest)))
    (hr : Reads (fun n => pUnary n true) (mr + 1) (Pretty.expr r ++ rest) r rest) (hs : Stop 2 rest) :
    Reads pPow (ml + mr + 4) (Pretty.expr l ++ .op .pow :: (Pretty.expr r ++ rest)) (.binop .pow l r) rest := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pPow, hl (n + 2) (by omega), bind, Except.bind, pPowLoop, hr (n + 1) (by omega)]
  exact pPowLoop_stop hs

theorem math2_binop {l r : Expr} {o : Op} {b : BinOp} (hb : math2Op o = some b) {ml mr : Nat}
    {rest : List TokKind}
    (hl : Reads pPow (ml + 1) (Pretty.expr l ++ .op o :: (Pretty.expr r ++ rest)) l
      (.op o :: (Pretty.expr r ++ rest)))
    (hr : Reads pPow (mr + 1) (Pretty.expr r ++ rest) r rest) (hs : Stop 3 rest) :
    Reads pMath2 (ml + mr + 4) (Pretty.expr l ++ .op o :: (Pretty.expr r ++ rest)) (.binop b l r) rest := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pMath2, hl (n + 2) (by omega), bind, Except.bind, pMath2Loop, hb, hr (n + 1) (by omega)]
  exact pMath2Loop_stop hs

theorem math1_binop {l r : Expr} {o : Op} {b : BinOp} (hb : math1Op o = some b) {ml mr : Nat}
    {rest : List TokKind}
    (hl : Reads pConcat (ml + 1) (Pretty.expr l ++ .op o :: (Pretty.expr r ++ rest)) l
      (.op o :: (Pretty.expr r ++ rest)))
    (hr : Reads pConcat (mr + 1) (Pretty.expr r ++ rest) r rest) (hs : Stop 5 rest) :
    Reads pMath1 (ml + mr + 4) (Pretty.expr l ++ .op o :: (Pretty.expr r ++ rest)) (.binop b l r) rest := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pMath1, hl (n + 2) (by omega), bind, Except.bind, pMath1Loop, hb, hr (n + 1) (by omega)]
  exact pMath1Loop_stop hs

theorem and_binop {l r : Expr} {ml mr : Nat} {rest : List TokKind}
    (hl : Reads pNot (ml + 1) (Pretty.expr l ++ .name "and" :: (Pretty.expr r ++ rest)) l
      (.name "and" :: (Pretty.expr r ++ rest)))
    (hr : Reads pNot (mr + 1) (Pretty.expr r ++ rest) r rest) (hs : Stop 8 rest) :
    Reads pAnd (ml + mr + 4) (Pretty.expr l ++ .name "and" :: (Pretty.expr r ++ rest)) (.binop .and l r) rest := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pAnd, hl (n + 2) (by omega), bind, Except.bind, pAndLoop, List.head?_cons, isName_name,
    beq_self_eq_true, ↓reduceIte, List.tail_cons, hr (n + 1) (by omega)]
  exact pAndLoop_stop hs

theorem or_binop {l r : Expr} {ml mr : Nat} {rest : List TokKind}
    (hl : Reads pAnd (ml + 1) (Pretty.expr l ++ .name "or" :: (Pretty.expr r ++ rest)) l
      (.name "or" :: (Pretty.expr r ++ rest)))
    (hr : Reads pAnd (mr + 1) (Pretty.expr r ++ rest) r rest) (hs : Stop 9 rest) :
    Reads pOr (ml + mr + 4) (Pretty.expr l ++ .name "or" :: (Pretty.expr r ++ rest)) (.binop .or l r) rest := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pOr, hl (n + 2) (by omega), bind, Except.bind, pOrLoop, List.head?_cons, isName_name,
    beq_self_eq_true, ↓reduceIte, List.tail_cons, hr (n + 1) (by omega)]
  exact pOrLoop_stop hs

/-! ## Chains -/

theorem cmpOps_ok : ∀ (ops : List (CmpOp × Expr)) (r : List TokKind), Stop 6 r →
    (∀ p ∈ ops, p.2.WF ∧ PrimOK p.2 (30 * p.2.sz)) →
    Reads pCmpOps (30 * Expr.szCmps ops + 1) (Pretty.cmps ops ++ r) ops r
  | [], r, hr, _ => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simpa [Pretty.cmps] using pCmpOps_stop hr
  | (o, x) :: ops, r, hr, hp => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hw, hpx⟩ := hp (o, x) List.mem_cons_self
    have hs : Stop 5 (Pretty.cmps ops ++ r) := by
      cases ops with
      | nil => simpa [Pretty.cmps] using hr.mono (by omega)
      | cons q qs =>
        obtain ⟨o', _⟩ := q
        cases o' <;> simp [Pretty.cmps, Pretty.cmpTok] <;> exact stop_cons _ _ (by simp [contLevel, contLevel_name])
    obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
    rw [hk] at hpx
    have hx := PrimOK.math1 hpx hw hs n (by simp [Expr.szCmps] at hn ⊢; omega)
    have ih := cmpOps_ok ops r hr (fun p hp' => hp p (List.mem_cons_of_mem _ hp')) n (by simp [Expr.szCmps] at hn ⊢; omega)
    have key : pCmpOps (n + 1) (Pretty.cmpTok o ++ (Pretty.expr x ++ (Pretty.cmps ops ++ r))) =
        (do let (e, r) ← pMath1 n (Pretty.expr x ++ (Pretty.cmps ops ++ r))
            let (more, r) ← pCmpOps n r
            .ok ((o, e) :: more, r)) := by
      cases o <;> simp [pCmpOps, Pretty.cmpTok, cmpOpOf]
    simp only [Pretty.cmps, List.append_assoc] at key ⊢
    rw [key]
    simp [bind, Except.bind, hx, ih]

theorem concatRest_ok : ∀ (xs : List Expr) (r : List TokKind), Stop 4 r →
    (∀ x ∈ xs, x.WF ∧ PrimOK x (30 * x.sz)) →
    Reads pConcatRest (30 * Expr.szs xs + 1) (Pretty.tildes xs ++ r) xs r
  | [], r, hr, _ => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simpa [Pretty.tildes] using pConcatRest_stop hr
  | x :: xs, r, hr, hp => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hw, hpx⟩ := hp x List.mem_cons_self
    have hs : Stop 3 (Pretty.tildes xs ++ r) := by
      cases xs with
      | nil => simpa [Pretty.tildes] using hr.mono (by omega)
      | cons y ys => simp [Pretty.tildes]; exact stop_cons _ _ (by simp [contLevel])
    obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
    rw [hk] at hpx
    have hx := PrimOK.math2 hpx hw hs n (by simp [Expr.szs] at hn ⊢; omega)
    have ih := concatRest_ok xs r hr (fun y hy => hp y (List.mem_cons_of_mem _ hy)) n (by simp [Expr.szs] at hn ⊢; omega)
    simp only [Pretty.tildes, List.append_assoc, List.cons_append, List.singleton_append] at hx ih ⊢
    simp [pConcatRest, bind, Except.bind, hx, ih]

end LeanJinja2

namespace LeanJinja2

open Parse

/-! ## Postfix operations and filters -/

theorem postfix_getattr {x : Expr} {a : String} {rest : List TokKind} (hs : Stop 0 rest) (n : Nat) :
    pPostfix (n + 2) x (.op .dot :: .name a :: rest) = .ok (.getattr x a, rest) := by
  simp only [pPostfix]; exact pPostfix_stop hs

theorem postfix_getitem {x i : Expr} {m : Nat} {rest : List TokKind} (hs : Stop 0 rest)
    (hi : Reads pSubscripts m (Pretty.subscript i ++ .op .rbracket :: rest) i rest) :
    Reads (fun n => pPostfix n x) (m + 2) (.op .lbracket :: (Pretty.subscript i ++ .op .rbracket :: rest))
      (.getitem x i) rest := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pPostfix, hi (n + 1) (by omega), bind, Except.bind]
  exact pPostfix_stop hs

theorem postfix_call {x : Expr} {args : List Expr} {kw : List (String × Expr)} {m : Nat}
    {rest : List TokKind} (hs : Stop 0 rest)
    (hc : Reads pCallArgs m (argToks args kw ++ .op .rparen :: rest) (args, kw) rest) :
    Reads (fun n => pPostfix n x) (m + 2) (.op .lparen :: (argToks args kw ++ .op .rparen :: rest))
      (.call x args kw) rest := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pPostfix, hc (n + 1) (by omega), bind, Except.bind]
  exact pPostfix_stop hs

/-- Printed filter or test arguments: nothing, or `( args )`. -/
theorem parenArgs_eq (args : List Expr) (kw : List (String × Expr)) (hw : ∀ x ∈ args, x.WF) :
    Pretty.parenArgs (Pretty.exprs args) (Pretty.kwargs kw) =
      if args = [] ∧ kw = [] then [] else .op .lparen :: (argToks args kw ++ [.op .rparen]) := by
  simp only [Pretty.parenArgs, argToks]
  by_cases h : args = [] ∧ kw = []
  · obtain ⟨rfl, rfl⟩ := h; simp [Pretty.exprs, Pretty.kwargs]
  · have : ¬ ((Pretty.exprs args).isEmpty = true ∧ (Pretty.kwargs kw).isEmpty = true) := by
      simp only [List.isEmpty_iff, exprs_eq_nil hw, kwargs_eq_nil]; exact h
    simp only [Bool.and_eq_true]
    rw [if_neg this, if_neg h]
    rfl

theorem pDotted_rparen (n : Nat) (nm : String) (r : List TokKind) :
    pDotted (n + 1) nm (.op .rparen :: r) = .ok (nm, .op .rparen :: r) := rfl

theorem pDotted_lparen (n : Nat) (nm : String) (r : List TokKind) :
    pDotted (n + 1) nm (.op .lparen :: r) = .ok (nm, .op .lparen :: r) := rfl

theorem filterExpr_filter {x : Expr} {nm : String} {args : List Expr} {kw : List (String × Expr)} {m : Nat}
    {r : List TokKind} (hw : ∀ y ∈ args, y.WF)
    (hc : ∀ r', Reads pCallArgs m (argToks args kw ++ .op .rparen :: r') (args, kw) r') :
    Reads (fun n => pFilterExpr n x) (m + 4)
      (.op .pipe :: .name nm :: (Pretty.parenArgs (Pretty.exprs args) (Pretty.kwargs kw) ++ .op .rparen :: r))
      (.filter x nm args kw) (.op .rparen :: r) := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [parenArgs_eq args kw hw]
  by_cases ha : args = [] ∧ kw = []
  · obtain ⟨rfl, rfl⟩ := ha
    simp only [and_self, ↓reduceIte, List.nil_append]
    simp only [pFilterExpr, pFilterOne, expectName, bind, Except.bind, pDotted_rparen, List.head?_cons,
      isOp_op, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, beq_iff_eq]
    try rfl
  · simp only [ha, ↓reduceIte, List.cons_append, List.append_assoc, List.nil_append]
    simp only [pFilterExpr, pFilterOne, expectName, bind, Except.bind, pDotted_lparen, List.head?_cons,
      isOp_op, beq_self_eq_true, ↓reduceIte, List.tail_cons, hc (.op .rparen :: r) (n + 1) (by omega)]
    try rfl

theorem filterExpr_test {x : Expr} {nm : String} {args : List Expr} {kw : List (String × Expr)} {m : Nat}
    {r : List TokKind} (hw : ∀ y ∈ args, y.WF) (hnm : nm ≠ "not")
    (hc : ∀ r', Reads pCallArgs m (argToks args kw ++ .op .rparen :: r') (args, kw) r') :
    Reads (fun n => pFilterExpr n x) (m + 4)
      (.name "is" :: .name nm :: (Pretty.parenArgs (Pretty.exprs args) (Pretty.kwargs kw) ++ .op .rparen :: r))
      (.test x nm args kw) (.op .rparen :: r) := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [parenArgs_eq args kw hw]
  have hnot : isName "not" (some (TokKind.name nm)) = false := by simp [hnm]
  by_cases ha : args = [] ∧ kw = []
  · obtain ⟨rfl, rfl⟩ := ha
    simp only [and_self, ↓reduceIte, List.nil_append]
    simp only [pFilterExpr, pTest, List.head?_cons, hnot, Bool.false_eq_true, ↓reduceIte, expectName,
      bind, Except.bind, pDotted_rparen, pTestArgs, isOp_op, testArgStart, reduceCtorEq, beq_iff_eq]
    try rfl
  · simp only [ha, ↓reduceIte, List.cons_append, List.append_assoc, List.nil_append]
    simp only [pFilterExpr, pTest, List.head?_cons, hnot, Bool.false_eq_true, ↓reduceIte, expectName,
      bind, Except.bind, pDotted_lparen, pTestArgs, isOp_op, beq_self_eq_true, List.tail_cons,
      hc (.op .rparen :: r) n (by omega)]
    try rfl

end LeanJinja2

namespace LeanJinja2

open Parse

theorem paren_ok {inner : List TokKind} {e : Expr} {m : Nat} {r : List TokKind}
    (h : Reads (fun n => pExpr n true) m (inner ++ .op .rparen :: r) e (.op .rparen :: r))
    (hhead : isTupleEnd [] (inner ++ .op .rparen :: r).head? = false) :
    Reads pPrimary (m + 2) (.op .lparen :: (inner ++ .op .rparen :: r)) e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pPrimary, pTuple, hhead, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
    h n (by omega), List.head?_cons, isOp_op, expect]
  rfl

theorem sz_lt_szs {x : Expr} {xs : List Expr} (h : x ∈ xs) : x.sz < Expr.szs xs + 1 := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [Expr.szs]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem sz_lt_szPairs {p : Expr × Expr} {ps : List (Expr × Expr)} (h : p ∈ ps) :
    p.1.sz + p.2.sz < Expr.szPairs ps + 1 := by
  induction ps with
  | nil => simp at h
  | cons q qs ih =>
    obtain ⟨k, v⟩ := q
    simp only [Expr.szPairs]
    rcases List.mem_cons.mp h with rfl | h
    · simp; omega
    · have := ih h; omega

theorem sz_lt_szKw {p : String × Expr} {kw : List (String × Expr)} (h : p ∈ kw) :
    p.2.sz < Expr.szKw kw + 1 := by
  induction kw with
  | nil => simp at h
  | cons q qs ih =>
    obtain ⟨k, v⟩ := q
    simp only [Expr.szKw]
    rcases List.mem_cons.mp h with rfl | h
    · simp; omega
    · have := ih h; omega

theorem sz_lt_szCmps {p : CmpOp × Expr} {ops : List (CmpOp × Expr)} (h : p ∈ ops) :
    p.2.sz < Expr.szCmps ops + 1 := by
  induction ops with
  | nil => simp at h
  | cons q qs ih =>
    obtain ⟨o, v⟩ := q
    simp only [Expr.szCmps]
    rcases List.mem_cons.mp h with rfl | h
    · simp; omega
    · have := ih h; omega

theorem length_le_szs (xs : List Expr) : xs.length ≤ Expr.szs xs := by
  induction xs with
  | nil => simp [Expr.szs]
  | cons x xs ih => simp [Expr.szs]; omega

theorem length_le_szPairs (ps : List (Expr × Expr)) : ps.length ≤ Expr.szPairs ps := by
  induction ps with
  | nil => simp [Expr.szPairs]
  | cons p ps ih => obtain ⟨_, _⟩ := p; simp [Expr.szPairs]; omega

theorem length_le_szKw (kw : List (String × Expr)) : kw.length ≤ Expr.szKw kw := by
  induction kw with
  | nil => simp [Expr.szKw]
  | cons p ps ih => obtain ⟨_, _⟩ := p; simp [Expr.szKw]; omega

theorem length_le_szCmps (ops : List (CmpOp × Expr)) : ops.length ≤ Expr.szCmps ops := by
  induction ops with
  | nil => simp [Expr.szCmps]
  | cons p ps ih => obtain ⟨_, _⟩ := p; simp [Expr.szCmps]; omega

theorem WFs_mem {xs : List Expr} (h : Expr.WFs xs) {x : Expr} (hx : x ∈ xs) : x.WF := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [Expr.WFs] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ih h.2 hx

theorem WFPairs_mem {ps : List (Expr × Expr)} (h : Expr.WFPairs ps) {p : Expr × Expr} (hp : p ∈ ps) :
    p.1.WF ∧ p.2.WF := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    obtain ⟨k, v⟩ := q
    simp only [Expr.WFPairs] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨h.1, h.2.1⟩
    · exact ih h.2.2 hp

theorem WFKw_mem {kw : List (String × Expr)} (h : Expr.WFKw kw) {p : String × Expr} (hp : p ∈ kw) :
    VarName p.1 ∧ p.2.WF := by
  induction kw with
  | nil => simp at hp
  | cons q qs ih =>
    obtain ⟨k, v⟩ := q
    simp only [Expr.WFKw] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨h.1, h.2.1⟩
    · exact ih h.2.2 hp

theorem WFCmps_mem {ops : List (CmpOp × Expr)} (h : Expr.WFCmps ops) {p : CmpOp × Expr} (hp : p ∈ ops) :
    p.2.WF := by
  induction ops with
  | nil => simp at hp
  | cons q qs ih =>
    obtain ⟨o, v⟩ := q
    simp only [Expr.WFCmps] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact ih h.2 hp

end LeanJinja2

namespace LeanJinja2

open Parse

theorem unary_postfix {x e : Expr} {P rest : List TokKind} {m : Nat}
    (hp : PrimOK x m) (hw : x.WF) (hns : NotStr (P ++ rest))
    (hpost : Reads (fun n => pPostfix n x) m (P ++ rest) e rest) (hs : Stop 1 rest) :
    Reads (fun n => pUnary n true) (m + 2) (Pretty.expr x ++ (P ++ rest)) e rest := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨t, tr, ht, hst⟩ := expr_head x hw
  have hsign : NoSign (Pretty.expr x ++ (P ++ rest)) := by rw [ht]; exact hst.noSign _
  simp only [pUnary_primary hsign, hp (P ++ rest) hns (n + 1) (by omega), bind, Except.bind,
    hpost (n + 1) (by omega), ite_true]
  exact pFilterExpr_stop hs

theorem unary_filterExpr {x e : Expr} {F rest : List TokKind} {m : Nat}
    (hp : PrimOK x m) (hw : x.WF) (hstop : Stop 0 (F ++ rest))
    (hf : Reads (fun n => pFilterExpr n x) m (F ++ rest) e rest) :
    Reads (fun n => pUnary n true) (m + 2) (Pretty.expr x ++ (F ++ rest)) e rest := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨t, tr, ht, hst⟩ := expr_head x hw
  have hsign : NoSign (Pretty.expr x ++ (F ++ rest)) := by rw [ht]; exact hst.noSign _
  simp only [pUnary_primary hsign, hp (F ++ rest) hstop.notStr (n + 1) (by omega), bind, Except.bind,
    pPostfix_stop hstop, ite_true]
  exact hf (n + 1) (by omega)

theorem expr_noNot {x : Expr} (hw : x.WF) (rest : List TokKind) : NoNot (Pretty.expr x ++ rest) := by
  obtain ⟨t, tr, ht, hst⟩ := expr_head x hw
  rw [ht]; exact hst.noNot _

theorem expr_notEnd {x : Expr} (hw : x.WF) (rest : List TokKind) :
    isTupleEnd [] (Pretty.expr x ++ rest).head? = false := by
  obtain ⟨t, hst, hh⟩ := expr_head' hw
  rw [hh]; exact hst.not_closer.2.2.2.2.2

end LeanJinja2

namespace LeanJinja2

open Parse

theorem constName_var {v : String} (h : v ∉ reservedNames) : constName v = none := by
  simp only [reservedNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  unfold constName
  split <;> simp_all

theorem pStrings_notStr {n : Nat} {r : List TokKind} (hr : NotStr r) : pStrings (n + 1) r = .ok ("", r) := by
  cases r with
  | nil => rfl
  | cons t ts =>
    cases t with
    | str s => exact absurd rfl (hr s)
    | _ => rfl

theorem pUnary_sub (n : Nat) (wf : Bool) (rest : List TokKind) :
    pUnary (n + 1) wf (.op .sub :: rest) = (do
      let (e, r) ← pUnary n false rest
      let (e, r) ← pPostfix n (.unop .neg e) r
      if wf then pFilterExpr n e r else .ok (e, r)) := rfl

theorem pUnary_add (n : Nat) (wf : Bool) (rest : List TokKind) :
    pUnary (n + 1) wf (.op .add :: rest) = (do
      let (e, r) ← pUnary n false rest
      let (e, r) ← pPostfix n (.unop .pos e) r
      if wf then pFilterExpr n e r else .ok (e, r)) := rfl

theorem compound_ok {inner : List TokKind} {e : Expr} {m M : Nat} {r : List TokKind}
    (hex : Pretty.expr e = .op .lparen :: (inner ++ [.op .rparen]))
    (hh : isTupleEnd [] (inner ++ .op .rparen :: r).head? = false)
    (h : Reads (fun n => pExpr n true) m (inner ++ .op .rparen :: r) e (.op .rparen :: r)) (hm : m + 2 ≤ M) :
    Reads pPrimary M (Pretty.expr e ++ r) e r := by
  rw [hex]
  simp only [List.cons_append, List.append_assoc, List.singleton_append]
  exact (paren_ok h hh).mono hm

theorem stop_rp (k : Nat) (r : List TokKind) (hk : k < 99 := by omega) : Stop k (.op .rparen :: r) :=
  stop_cons _ _ (by simp [contLevel]; omega)

/-- `prim_ok`: the primary parser reads a well-formed printed expression back,
with fuel thirty times its size. -/
theorem prim_ok : (e : Expr) → e.WF → PrimOK e (30 * e.sz)
  | .const c, hw => by
    intro r hr n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
    cases c with
    | none => simp [Pretty.expr, Pretty.constToks, pPrimary, constName]
    | bool b => cases b <;> simp [Pretty.expr, Pretty.constToks, pPrimary, constName]
    | int i =>
      simp only [Expr.WF, Const.WF] at hw
      simp [Pretty.expr, Pretty.constToks, pPrimary, Int.toNat_of_nonneg hw]
    | float m s =>
      simp only [Expr.WF, Const.WF] at hw
      simp [Pretty.expr, Pretty.constToks, pPrimary, Int.toNat_of_nonneg hw]
    | str s =>
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
      simp [Pretty.expr, Pretty.constToks, pPrimary, pStrings_notStr hr, bind, Except.bind]
  | .name v, hw => by
    intro r hr n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
    simp only [Expr.WF, VarName] at hw
    simp [Pretty.expr, pPrimary, constName_var hw.2]
  | .tuple xs, hw => by
    intro r hr
    have hxs : ∀ x ∈ xs, x.WF ∧ ExprOK x (30 * x.sz + 12) := by
      intro x hx
      have hwx := WFs_mem (by simpa [Expr.WF] using hw) hx
      have hp := prim_ok x hwx
      obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
      rw [hk] at hp
      exact ⟨hwx, (hp.exprOK hwx).mono (by omega)⟩
    match xs, hxs with
    | [], _ =>
      intro n hn
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
      simp [Pretty.expr, Pretty.exprs, pPrimary, pTuple, isTupleEnd, bind, Except.bind, expect]
    | [x], hxs =>
      obtain ⟨hwx, hox⟩ := hxs x List.mem_cons_self
      obtain ⟨t, hst, hh⟩ := expr_head' hwx
      have hh0 : (Pretty.expr x).head? = some t := by simpa using hh []
      intro n hn
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
      have h1 := hox (.op .comma :: .op .rparen :: r) (stop_cons _ _ (by simp [contLevel])) n
        (by simp [Expr.sz, Expr.szs] at hn ⊢; omega)
      have h2 := tupleRest_ok [] r (by simp) n (by simp [Expr.sz, Expr.szs] at hn ⊢; omega)
      simp only [Pretty.exprs, List.nil_append] at h2
      simp [Pretty.expr, pPrimary, pTuple, hh0, hst.not_closer.2.2.2.2.2, bind, Except.bind, h1, h2, expect]
    | x :: y :: zs, hxs =>
      obtain ⟨hwx, hox⟩ := hxs x List.mem_cons_self
      obtain ⟨t, hst, hh⟩ := expr_head' hwx
      have hh0 : (Pretty.expr x).head? = some t := by simpa using hh []
      intro n hn
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
      obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
      have h1 := hox (.op .comma :: (Pretty.exprs (y :: zs) ++ .op .rparen :: r))
        (stop_cons _ _ (by simp [contLevel])) n (by simp [Expr.sz, Expr.szs] at hn ⊢; omega)
      have h2 := tupleRest_ok (y :: zs) r (fun z hz => hxs z (List.mem_cons_of_mem _ hz)) n
        (by simp [Expr.sz, Expr.szs] at hn ⊢; omega)
      have hex : Pretty.expr (.tuple (x :: y :: zs)) =
          .op .lparen :: (Pretty.expr x ++ .op .comma :: (Pretty.exprs (y :: zs) ++ [.op .rparen])) := by
        simp [Pretty.expr, Pretty.exprs]
      rw [hex]
      simp only [List.cons_append, List.append_assoc, List.singleton_append] at h1 h2 ⊢
      simp [pPrimary, pTuple, hh0, hst.not_closer.2.2.2.2.2, bind, Except.bind, h1, h2, expect]
  | .list xs, hw => by
    intro r hr
    have hxs : ∀ x ∈ xs, x.WF ∧ ExprOK x (30 * x.sz + 12) := by
      intro x hx
      have hwx := WFs_mem (by simpa [Expr.WF] using hw) hx
      have hp := prim_ok x hwx
      obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
      rw [hk] at hp
      exact ⟨hwx, (hp.exprOK hwx).mono (by omega)⟩
    have hl := listItems_ok xs r hxs
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
    simp only [Pretty.expr, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] at hl ⊢
    simp [pPrimary, bind, Except.bind, hl n (by simp [Expr.sz] at hn; omega)]
  | .dict ps, hw => by
    intro r hr
    have hps : ∀ p ∈ ps, p.1.WF ∧ p.2.WF ∧ ExprOK p.1 (30 * p.1.sz + 12) ∧ ExprOK p.2 (30 * p.2.sz + 12) := by
      intro p hp
      obtain ⟨hw1, hw2⟩ := WFPairs_mem (by simpa [Expr.WF] using hw) hp
      have hp1 := prim_ok p.1 hw1
      have hp2 := prim_ok p.2 hw2
      obtain ⟨k1, hk1⟩ : ∃ k, 30 * p.1.sz = k + 1 := ⟨30 * p.1.sz - 1, by have := p.1.sz_pos; omega⟩
      obtain ⟨k2, hk2⟩ : ∃ k, 30 * p.2.sz = k + 1 := ⟨30 * p.2.sz - 1, by have := p.2.sz_pos; omega⟩
      rw [hk1] at hp1; rw [hk2] at hp2
      exact ⟨hw1, hw2, (hp1.exprOK hw1).mono (by omega), (hp2.exprOK hw2).mono (by omega)⟩
    have hl := dictItems_ok ps r hps
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [Expr.sz] at hn; omega⟩
    simp only [Pretty.expr, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] at hl ⊢
    simp [pPrimary, bind, Except.bind, hl n (by simp [Expr.sz] at hn; omega)]
  | .slice .., hw => by simp [Expr.WF] at hw
  | .getattr x a, hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨hwx, _⟩ := hw
    obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
    have hpx := prim_ok x hwx
    rw [hk] at hpx
    have hpost : Reads (fun n => pPostfix n x) (k + 1) ([.op .dot, .name a] ++ .op .rparen :: r)
        (.getattr x a) (.op .rparen :: r) := by
      intro n hn
      obtain ⟨n, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by have := x.sz_pos; omega⟩
      exact postfix_getattr (stop_rp 0 r) n
    have hu := unary_postfix hpx hwx (by simp [NotStr]) hpost (stop_rp 1 r)
    have he := hu.liftUnary (stop_rp 10 r) (expr_noNot hwx _)
    refine compound_ok (inner := Pretty.expr x ++ [.op .dot, .name a]) (by simp [Pretty.expr])
      (by rw [List.append_assoc]; exact expr_notEnd hwx _) (by rw [List.append_assoc]; exact he)
      (by simp [Expr.sz]; omega)
  | .getitem x i, hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨hwx, hwi⟩ := hw
    obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
    have hpx := prim_ok x hwx
    rw [hk] at hpx
    have hok : ∀ y, ((∀ a b c, i ≠ .slice a b c) ∧ i = y ∨
        ∃ a b c, i = .slice a b c ∧ (a = some y ∨ b = some y ∨ c = some y)) →
        y.WF ∧ ExprOK y (30 * i.sz + 12) := by
      intro y hy
      rcases hy with ⟨hns, rfl⟩ | ⟨a, b, c, hi, hy⟩
      · have hwy : i.WF := by
          cases i with
          | slice a b c => exact absurd rfl (hns a b c)
          | _ => simpa [Expr.SubWF] using hwi
        have hp := prim_ok i hwy
        obtain ⟨k', hk'⟩ : ∃ k, 30 * i.sz = k + 1 := ⟨30 * i.sz - 1, by have := i.sz_pos; omega⟩
        rw [hk'] at hp
        exact ⟨hwy, (hp.exprOK hwy).mono (by omega)⟩
      · rw [hi] at hwi
        simp only [Expr.SubWF] at hwi
        obtain ⟨wa, wb, wc⟩ := hwi
        have hwy : y.WF := by
          rcases hy with rfl | rfl | rfl
          · simpa [Expr.WFOpt] using wa
          · simpa [Expr.WFOpt] using wb
          · simpa [Expr.WFOpt] using wc
        have hsz : y.sz < i.sz := by
          rw [hi]; rcases hy with rfl | rfl | rfl <;> simp [Expr.sz, Expr.szOpt] <;> omega
        have hp := prim_ok y hwy
        obtain ⟨k', hk'⟩ : ∃ k, 30 * y.sz = k + 1 := ⟨30 * y.sz - 1, by have := y.sz_pos; omega⟩
        rw [hk'] at hp
        exact ⟨hwy, (hp.exprOK hwy).mono (by omega)⟩
    have hsub := subscripts_ok (.op .rparen :: r) hwi hok
    have hpost := postfix_getitem (x := x) (stop_rp 0 r) hsub
    have hpost' : Reads (fun n => pPostfix n x) (k + 1 + 30 * i.sz + 16)
        ((.op .lbracket :: (Pretty.subscript i ++ [.op .rbracket])) ++ .op .rparen :: r) (.getitem x i)
        (.op .rparen :: r) := by
      simpa [List.append_assoc] using hpost.mono (m' := k + 1 + 30 * i.sz + 16) (by omega)
    have hu := unary_postfix (P := .op .lbracket :: (Pretty.subscript i ++ [.op .rbracket]))
      (hpx.mono (m' := k + 1 + 30 * i.sz + 16) (by omega)) hwx (by simp [NotStr]) hpost' (stop_rp 1 r)
    have he := hu.liftUnary (stop_rp 10 r) (expr_noNot hwx _)
    refine compound_ok (inner := Pretty.expr x ++ (.op .lbracket :: (Pretty.subscript i ++ [.op .rbracket])))
      (by simp [Pretty.expr]) (by rw [List.append_assoc]; exact expr_notEnd hwx _)
      (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega)
  | .call f args kw, hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨hwf, hwa, hwk⟩ := hw
    obtain ⟨k, hk⟩ : ∃ k, 30 * f.sz = k + 1 := ⟨30 * f.sz - 1, by have := f.sz_pos; omega⟩
    have hpf := prim_ok f hwf
    rw [hk] at hpf
    have hargs : ∀ x ∈ args, x.WF ∧ ExprOK x (30 * x.sz + 12) := by
      intro x hx
      have hwx := WFs_mem hwa hx
      have := sz_lt_szs hx
      have hp := prim_ok x hwx
      obtain ⟨k', hk'⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
      rw [hk'] at hp
      exact ⟨hwx, (hp.exprOK hwx).mono (by omega)⟩
    have hkws : ∀ p ∈ kw, VarName p.1 ∧ p.2.WF ∧ ExprOK p.2 (30 * p.2.sz + 12) := by
      intro p hp'
      obtain ⟨hn, hwv⟩ := WFKw_mem hwk hp'
      have := sz_lt_szKw hp'
      have hp := prim_ok p.2 hwv
      obtain ⟨k', hk'⟩ : ∃ k, 30 * p.2.sz = k + 1 := ⟨30 * p.2.sz - 1, by have := p.2.sz_pos; omega⟩
      rw [hk'] at hp
      exact ⟨hn, hwv, (hp.exprOK hwv).mono (by omega)⟩
    have hc := callArgs_ok args kw (.op .rparen :: r) hargs hkws
    have hpost := postfix_call (x := f) (stop_rp 0 r) hc
    have hpost' : Reads (fun n => pPostfix n f) (k + 1 + 30 * (Expr.szs args + Expr.szKw kw) + 15)
        ((.op .lparen :: (argToks args kw ++ [.op .rparen])) ++ .op .rparen :: r) (.call f args kw)
        (.op .rparen :: r) := by
      simpa [List.append_assoc] using hpost.mono (m' := k + 1 + 30 * (Expr.szs args + Expr.szKw kw) + 15) (by omega)
    have hu := unary_postfix (P := .op .lparen :: (argToks args kw ++ [.op .rparen]))
      (hpf.mono (m' := k + 1 + 30 * (Expr.szs args + Expr.szKw kw) + 15) (by omega)) hwf (by simp [NotStr])
      hpost' (stop_rp 1 r)
    have he := hu.liftUnary (stop_rp 10 r) (expr_noNot hwf _)
    refine compound_ok (inner := Pretty.expr f ++ (.op .lparen :: (argToks args kw ++ [.op .rparen])))
      (by simp [Pretty.expr, argToks]) (by rw [List.append_assoc]; exact expr_notEnd hwf _)
      (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega)
  | .filter x nm args kw, hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨hwx, _, hwa, hwk⟩ := hw
    obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
    have hpx := prim_ok x hwx
    rw [hk] at hpx
    have hargs : ∀ y ∈ args, y.WF ∧ ExprOK y (30 * y.sz + 12) := by
      intro y hy
      have hwy := WFs_mem hwa hy
      have := sz_lt_szs hy
      have hp := prim_ok y hwy
      obtain ⟨k', hk'⟩ : ∃ k, 30 * y.sz = k + 1 := ⟨30 * y.sz - 1, by have := y.sz_pos; omega⟩
      rw [hk'] at hp
      exact ⟨hwy, (hp.exprOK hwy).mono (by omega)⟩
    have hkws : ∀ p ∈ kw, VarName p.1 ∧ p.2.WF ∧ ExprOK p.2 (30 * p.2.sz + 12) := by
      intro p hp'
      obtain ⟨hn, hwv⟩ := WFKw_mem hwk hp'
      have := sz_lt_szKw hp'
      have hp := prim_ok p.2 hwv
      obtain ⟨k', hk'⟩ : ∃ k, 30 * p.2.sz = k + 1 := ⟨30 * p.2.sz - 1, by have := p.2.sz_pos; omega⟩
      rw [hk'] at hp
      exact ⟨hn, hwv, (hp.exprOK hwv).mono (by omega)⟩
    have hf := filterExpr_filter (x := x) (nm := nm) (r := r) (fun y hy => WFs_mem hwa hy)
      (fun r' => callArgs_ok args kw r' hargs hkws)
    have hu := unary_filterExpr (F := .op .pipe :: .name nm :: Pretty.parenArgs (Pretty.exprs args) (Pretty.kwargs kw))
      (hpx.mono (m' := k + 1 + 30 * (Expr.szs args + Expr.szKw kw) + 16) (by omega)) hwx
      (stop_cons _ _ (by simp [contLevel])) (by simpa [List.append_assoc] using hf.mono (by omega))
    have he := hu.liftUnary (stop_rp 10 r) (expr_noNot hwx _)
    refine compound_ok
      (inner := Pretty.expr x ++ (.op .pipe :: .name nm :: Pretty.parenArgs (Pretty.exprs args) (Pretty.kwargs kw)))
      (by simp [Pretty.expr]) (by rw [List.append_assoc]; exact expr_notEnd hwx _)
      (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega)
  | .test x nm args kw, hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨hwx, hnm, hwa, hwk⟩ := hw
    have hnot : nm ≠ "not" := by
      intro h; subst h; exact hnm.2 (by simp [reservedNames])
    obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
    have hpx := prim_ok x hwx
    rw [hk] at hpx
    have hargs : ∀ y ∈ args, y.WF ∧ ExprOK y (30 * y.sz + 12) := by
      intro y hy
      have hwy := WFs_mem hwa hy
      have := sz_lt_szs hy
      have hp := prim_ok y hwy
      obtain ⟨k', hk'⟩ : ∃ k, 30 * y.sz = k + 1 := ⟨30 * y.sz - 1, by have := y.sz_pos; omega⟩
      rw [hk'] at hp
      exact ⟨hwy, (hp.exprOK hwy).mono (by omega)⟩
    have hkws : ∀ p ∈ kw, VarName p.1 ∧ p.2.WF ∧ ExprOK p.2 (30 * p.2.sz + 12) := by
      intro p hp'
      obtain ⟨hn, hwv⟩ := WFKw_mem hwk hp'
      have := sz_lt_szKw hp'
      have hp := prim_ok p.2 hwv
      obtain ⟨k', hk'⟩ : ∃ k, 30 * p.2.sz = k + 1 := ⟨30 * p.2.sz - 1, by have := p.2.sz_pos; omega⟩
      rw [hk'] at hp
      exact ⟨hn, hwv, (hp.exprOK hwv).mono (by omega)⟩
    have hf := filterExpr_test (x := x) (nm := nm) (r := r) (fun y hy => WFs_mem hwa hy) hnot
      (fun r' => callArgs_ok args kw r' hargs hkws)
    have hu := unary_filterExpr (F := .name "is" :: .name nm :: Pretty.parenArgs (Pretty.exprs args) (Pretty.kwargs kw))
      (hpx.mono (m' := k + 1 + 30 * (Expr.szs args + Expr.szKw kw) + 16) (by omega)) hwx
      (stop_cons _ _ (by simp [contLevel])) (by simpa [List.append_assoc] using hf.mono (by omega))
    have he := hu.liftUnary (stop_rp 10 r) (expr_noNot hwx _)
    refine compound_ok
      (inner := Pretty.expr x ++ (.name "is" :: .name nm :: Pretty.parenArgs (Pretty.exprs args) (Pretty.kwargs kw)))
      (by simp [Pretty.expr]) (by rw [List.append_assoc]; exact expr_notEnd hwx _)
      (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega)
  | .unop o x, hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
    have hpx := prim_ok x hw
    rw [hk] at hpx
    cases o with
    | not =>
      have hn := PrimOK.not hpx hw (stop_rp 6 r)
      have hread : Reads pNot (k + 9) (.name "not" :: (Pretty.expr x ++ .op .rparen :: r)) (.unop .not x)
          (.op .rparen :: r) := by
        intro n hn'
        obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
        simp [pNot, hn n (by omega), bind, Except.bind]
      have he := hread.liftNot (stop_rp 10 r)
      refine compound_ok (inner := .name "not" :: Pretty.expr x) (by simp [Pretty.expr]) (by simp [isTupleEnd])
        (by simpa using he) (by simp [Expr.sz]; omega)
    | neg | pos =>
      have hun := PrimOK.unary hpx hw false (stop_rp 0 r)
      have hread : ∀ (so : Op) (uo : UnOp), (so = .sub ∧ uo = .neg ∨ so = .add ∧ uo = .pos) →
          Reads (fun n => pUnary n true) (k + 4) (.op so :: (Pretty.expr x ++ .op .rparen :: r)) (.unop uo x)
            (.op .rparen :: r) := by
        intro so uo hso n hn'
        obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
        obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
        rcases hso with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · show pUnary (n + 1 + 1) true _ = _; rw [pUnary_sub]
          simp only [hun (n + 1) (by omega), bind, Except.bind, pure, Except.pure]
          rw [pPostfix_stop (stop_rp 0 r)]
          simp only [ite_true]
          exact pFilterExpr_stop (stop_rp 1 r)
        · show pUnary (n + 1 + 1) true _ = _; rw [pUnary_add]
          simp only [hun (n + 1) (by omega), bind, Except.bind, pure, Except.pure]
          rw [pPostfix_stop (stop_rp 0 r)]
          simp only [ite_true]
          exact pFilterExpr_stop (stop_rp 1 r)
      first
      | have he := (hread .sub .neg (Or.inl ⟨rfl, rfl⟩)).liftUnary (stop_rp 10 r) (by simp [NoNot])
        refine compound_ok (inner := .op .sub :: Pretty.expr x) (by simp [Pretty.expr]) (by simp [isTupleEnd])
          (by simpa using he) (by simp [Expr.sz]; omega)
      | have he := (hread .add .pos (Or.inr ⟨rfl, rfl⟩)).liftUnary (stop_rp 10 r) (by simp [NoNot])
        refine compound_ok (inner := .op .add :: Pretty.expr x) (by simp [Pretty.expr]) (by simp [isTupleEnd])
          (by simpa using he) (by simp [Expr.sz]; omega)
  | .binop o l x, hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨hwl, hwx⟩ := hw
    obtain ⟨kl, hkl⟩ : ∃ k, 30 * l.sz = k + 1 := ⟨30 * l.sz - 1, by have := l.sz_pos; omega⟩
    obtain ⟨kx, hkx⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
    have hpl := prim_ok l hwl
    have hpx := prim_ok x hwx
    rw [hkl] at hpl
    rw [hkx] at hpx
    have hnn := expr_noNot hwl (Pretty.binTok o ++ Pretty.expr x ++ [.op .rparen] ++ r)
    have hex : ∀ t : List TokKind, Pretty.binTok o = t →
        Pretty.expr (.binop o l x) = .op .lparen :: (Pretty.expr l ++ t ++ Pretty.expr x ++ [.op .rparen]) := by
      intro t ht; subst ht; simp [Pretty.expr]
    cases o with
    | add | sub =>
      first
      | (have hb : math1Op .add = some .add := rfl
         have h := math1_binop hb (hpl.concat hwl (stop_cons _ _ (by simp [contLevel]))) (hpx.concat hwx (stop_rp 4 r))
           (stop_rp 5 r)
         have he := h.liftMath1 (stop_rp 10 r) (by simpa [Pretty.binTok, List.append_assoc] using hnn)
         exact compound_ok (inner := Pretty.expr l ++ [.op .add] ++ Pretty.expr x) (hex _ rfl)
           (by simpa [List.append_assoc] using expr_notEnd hwl (.op .add :: (Pretty.expr x ++ .op .rparen :: r)))
           (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega))
      | (have hb : math1Op .sub = some .sub := rfl
         have h := math1_binop hb (hpl.concat hwl (stop_cons _ _ (by simp [contLevel]))) (hpx.concat hwx (stop_rp 4 r))
           (stop_rp 5 r)
         have he := h.liftMath1 (stop_rp 10 r) (by simpa [Pretty.binTok, List.append_assoc] using hnn)
         exact compound_ok (inner := Pretty.expr l ++ [.op .sub] ++ Pretty.expr x) (hex _ rfl)
           (by simpa [List.append_assoc] using expr_notEnd hwl (.op .sub :: (Pretty.expr x ++ .op .rparen :: r)))
           (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega))
    | mul | div | floordiv | mod =>
      first
      | (have hb : math2Op .mul = some .mul := rfl
         have h := math2_binop hb (hpl.pow hwl (stop_cons _ _ (by simp [contLevel]))) (hpx.pow hwx (stop_rp 2 r))
           (stop_rp 3 r)
         have he := h.liftMath2 (stop_rp 10 r) (by simpa [Pretty.binTok, List.append_assoc] using hnn)
         exact compound_ok (inner := Pretty.expr l ++ [.op .mul] ++ Pretty.expr x) (hex _ rfl)
           (by simpa [List.append_assoc] using expr_notEnd hwl (.op .mul :: (Pretty.expr x ++ .op .rparen :: r)))
           (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega))
      | (have hb : math2Op .div = some .div := rfl
         have h := math2_binop hb (hpl.pow hwl (stop_cons _ _ (by simp [contLevel]))) (hpx.pow hwx (stop_rp 2 r))
           (stop_rp 3 r)
         have he := h.liftMath2 (stop_rp 10 r) (by simpa [Pretty.binTok, List.append_assoc] using hnn)
         exact compound_ok (inner := Pretty.expr l ++ [.op .div] ++ Pretty.expr x) (hex _ rfl)
           (by simpa [List.append_assoc] using expr_notEnd hwl (.op .div :: (Pretty.expr x ++ .op .rparen :: r)))
           (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega))
      | (have hb : math2Op .floordiv = some .floordiv := rfl
         have h := math2_binop hb (hpl.pow hwl (stop_cons _ _ (by simp [contLevel]))) (hpx.pow hwx (stop_rp 2 r))
           (stop_rp 3 r)
         have he := h.liftMath2 (stop_rp 10 r) (by simpa [Pretty.binTok, List.append_assoc] using hnn)
         exact compound_ok (inner := Pretty.expr l ++ [.op .floordiv] ++ Pretty.expr x) (hex _ rfl)
           (by simpa [List.append_assoc] using expr_notEnd hwl (.op .floordiv :: (Pretty.expr x ++ .op .rparen :: r)))
           (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega))
      | (have hb : math2Op .mod = some .mod := rfl
         have h := math2_binop hb (hpl.pow hwl (stop_cons _ _ (by simp [contLevel]))) (hpx.pow hwx (stop_rp 2 r))
           (stop_rp 3 r)
         have he := h.liftMath2 (stop_rp 10 r) (by simpa [Pretty.binTok, List.append_assoc] using hnn)
         exact compound_ok (inner := Pretty.expr l ++ [.op .mod] ++ Pretty.expr x) (hex _ rfl)
           (by simpa [List.append_assoc] using expr_notEnd hwl (.op .mod :: (Pretty.expr x ++ .op .rparen :: r)))
           (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega))
    | pow =>
      have h := pow_binop (hpl.unary hwl true (stop_cons _ _ (by simp [contLevel])))
        (hpx.unary hwx true (stop_rp 1 r)) (stop_rp 2 r)
      have he := h.liftPow (stop_rp 10 r) (by simpa [Pretty.binTok, List.append_assoc] using hnn)
      exact compound_ok (inner := Pretty.expr l ++ [.op .pow] ++ Pretty.expr x) (hex _ rfl)
        (by simpa [List.append_assoc] using expr_notEnd hwl (.op .pow :: (Pretty.expr x ++ .op .rparen :: r)))
        (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega)
    | and =>
      have h := and_binop (hpl.not hwl (stop_cons _ _ (by simp [contLevel_name])))
        (hpx.not hwx (stop_rp 6 r)) (stop_rp 8 r)
      have he := h.liftAnd (stop_rp 10 r)
      exact compound_ok (inner := Pretty.expr l ++ [.name "and"] ++ Pretty.expr x) (hex _ rfl)
        (by simpa [List.append_assoc] using expr_notEnd hwl (.name "and" :: (Pretty.expr x ++ .op .rparen :: r)))
        (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega)
    | or =>
      have h := or_binop (hpl.and hwl (stop_cons _ _ (by simp [contLevel_name])))
        (hpx.and hwx (stop_rp 8 r)) (stop_rp 9 r)
      have he := h.liftOr (stop_rp 10 r)
      exact compound_ok (inner := Pretty.expr l ++ [.name "or"] ++ Pretty.expr x) (hex _ rfl)
        (by simpa [List.append_assoc] using expr_notEnd hwl (.name "or" :: (Pretty.expr x ++ .op .rparen :: r)))
        (by simpa [List.append_assoc] using he) (by simp [Expr.sz]; omega)
  | .compare x ops, hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨hwx, hne, hwo⟩ := hw
    obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
    have hpx := prim_ok x hwx
    rw [hk] at hpx
    have hops : ∀ p ∈ ops, p.2.WF ∧ PrimOK p.2 (30 * p.2.sz) := by
      intro p hp'
      have hwp := WFCmps_mem hwo hp'
      have := sz_lt_szCmps hp'
      exact ⟨hwp, prim_ok p.2 hwp⟩
    have hc := cmpOps_ok ops (.op .rparen :: r) (stop_rp 6 r) hops
    have hs5 : Stop 5 (Pretty.cmps ops ++ .op .rparen :: r) := by
      cases ops with
      | nil => exact absurd rfl hne
      | cons q qs =>
        obtain ⟨o', _⟩ := q
        cases o' <;> simp [Pretty.cmps, Pretty.cmpTok] <;> first | done | exact stop_cons _ _ (by simp [contLevel, contLevel_name])
    have hm := hpx.math1 hwx hs5
    have hread : Reads pCompare (k + 30 * Expr.szCmps ops + 8) (Pretty.expr x ++ (Pretty.cmps ops ++ .op .rparen :: r))
        (.compare x ops) (.op .rparen :: r) := by
      intro n hn
      obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      have hne' : ops.isEmpty = false := by cases ops <;> simp_all
      simp [pCompare, hm n (by omega), hc n (by omega), bind, Except.bind, hne']
    have he := hread.liftCompare (stop_rp 10 r) (expr_noNot hwx _)
    exact compound_ok (inner := Pretty.expr x ++ Pretty.cmps ops) (by simp [Pretty.expr])
      (by rw [List.append_assoc]; exact expr_notEnd hwx _) (by simpa [List.append_assoc] using he)
      (by simp [Expr.sz]; omega)
  | .concat [], hw => by simp [Expr.WF] at hw
  | .concat [_], hw => by simp [Expr.WF] at hw
  | .concat (x :: y :: zs), hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨_, hws⟩ := hw
    have hwx : x.WF := WFs_mem hws List.mem_cons_self
    obtain ⟨k, hk⟩ : ∃ k, 30 * x.sz = k + 1 := ⟨30 * x.sz - 1, by have := x.sz_pos; omega⟩
    have hpx := prim_ok x hwx
    rw [hk] at hpx
    have hrest : ∀ z ∈ y :: zs, z.WF ∧ PrimOK z (30 * z.sz) := by
      intro z hz
      have hwz := WFs_mem hws (List.mem_cons_of_mem _ hz)
      have := sz_lt_szs (List.mem_cons_of_mem x hz)
      exact ⟨hwz, prim_ok z hwz⟩
    have hc := concatRest_ok (y :: zs) (.op .rparen :: r) (stop_rp 4 r) hrest
    have hm := hpx.math2 hwx (show Stop 3 (Pretty.tildes (y :: zs) ++ .op .rparen :: r) by
      simp [Pretty.tildes]; exact stop_cons _ _ (by simp [contLevel]))
    have hread : Reads pConcat (k + 30 * Expr.szs (y :: zs) + 5)
        (Pretty.expr x ++ (Pretty.tildes (y :: zs) ++ .op .rparen :: r)) (.concat (x :: y :: zs)) (.op .rparen :: r) := by
      intro n hn
      obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      simp [pConcat, hm n (by omega), hc n (by omega), bind, Except.bind]
    have he := hread.liftConcat (stop_rp 10 r) (expr_noNot hwx _)
    exact compound_ok (inner := Pretty.expr x ++ Pretty.tildes (y :: zs)) (by simp [Pretty.expr])
      (by rw [List.append_assoc]; exact expr_notEnd hwx _) (by simpa [List.append_assoc] using he)
      (by simp [Expr.sz, Expr.szs] at *; omega)
  | .cond t b none, hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨hwt, hwb, hwe⟩ := hw
    obtain ⟨kb, hkb⟩ : ∃ k, 30 * b.sz = k + 1 := ⟨30 * b.sz - 1, by have := b.sz_pos; omega⟩
    obtain ⟨kt, hkt⟩ : ∃ k, 30 * t.sz = k + 1 := ⟨30 * t.sz - 1, by have := t.sz_pos; omega⟩
    have hpb := prim_ok b hwb
    have hpt := prim_ok t hwt
    rw [hkb] at hpb
    rw [hkt] at hpt
    have hb := hpb.or hwb (show Stop 9 (.name "if" :: (Pretty.expr t ++ .op .rparen :: r)) from
      stop_cons _ _ (by simp [contLevel_name]))
    have ht := hpt.or hwt (stop_rp 9 r)
    have hread : Reads pCond (kb + kt + 13) (Pretty.expr b ++ .name "if" :: (Pretty.expr t ++ .op .rparen :: r))
        (.cond t b none) (.op .rparen :: r) := by
      intro n hn
      obtain ⟨n, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
      simp only [pCond, hb (n + 2) (by omega), bind, Except.bind, pCondLoop, List.head?_cons, isName_name,
        beq_self_eq_true, ↓reduceIte, List.tail_cons, ht (n + 1) (by omega), isName_op, Bool.false_eq_true]
      all_goals exact pCondLoop_stop (stop_rp 10 r)
    have he := hread.liftCond (stop_rp 10 r)
    exact compound_ok (inner := Pretty.expr b ++ [.name "if"] ++ Pretty.expr t) (by simp [Pretty.expr])
      (by simpa [List.append_assoc] using expr_notEnd hwb (.name "if" :: (Pretty.expr t ++ .op .rparen :: r)))
      (by simpa [List.append_assoc] using he) (by simp [Expr.sz, Expr.szOpt]; omega)
  | .cond t b (some e), hw => by
    intro r _
    simp only [Expr.WF] at hw
    obtain ⟨hwt, hwb, hwe⟩ := hw
    obtain ⟨kb, hkb⟩ : ∃ k, 30 * b.sz = k + 1 := ⟨30 * b.sz - 1, by have := b.sz_pos; omega⟩
    obtain ⟨kt, hkt⟩ : ∃ k, 30 * t.sz = k + 1 := ⟨30 * t.sz - 1, by have := t.sz_pos; omega⟩
    have hpb := prim_ok b hwb
    have hpt := prim_ok t hwt
    rw [hkb] at hpb
    rw [hkt] at hpt
    simp only [Expr.WFOpt] at hwe
    obtain ⟨ke, hke⟩ : ∃ k, 30 * e.sz = k + 1 := ⟨30 * e.sz - 1, by have := e.sz_pos; omega⟩
    have hpe := prim_ok e hwe
    rw [hke] at hpe
    have hb := hpb.or hwb (show Stop 9 (.name "if" :: (Pretty.expr t ++ .name "else" ::
      (Pretty.expr e ++ .op .rparen :: r))) from stop_cons _ _ (by simp [contLevel_name]))
    have ht := hpt.or hwt (show Stop 9 (.name "else" :: (Pretty.expr e ++ .op .rparen :: r)) from
      stop_cons _ _ (by simp [contLevel_name]))
    have hc := hpe.cond hwe (stop_rp 10 r)
    have hread : Reads pCond (kb + kt + ke + 15)
        (Pretty.expr b ++ .name "if" :: (Pretty.expr t ++ .name "else" :: (Pretty.expr e ++ .op .rparen :: r)))
        (.cond t b (some e)) (.op .rparen :: r) := by
      intro n hn
      obtain ⟨n, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
      rw [pCond]
      simp only [hb (n + 2) (by omega), bind, Except.bind]
      rw [pCondLoop]
      simp only [List.head?_cons, isName_name, beq_self_eq_true, ↓reduceIte, List.tail_cons,
        ht (n + 1) (by omega), bind, Except.bind]
      rw [hc (n + 1) (by omega)]
      exact pCondLoop_stop (stop_rp 10 r)
    have he := hread.liftCond (stop_rp 10 r)
    have hend := expr_notEnd hwb (.name "if" :: (Pretty.expr t ++ .name "else" :: (Pretty.expr e ++ .op .rparen :: r)))
    exact compound_ok (inner := Pretty.expr b ++ [.name "if"] ++ Pretty.expr t ++ [.name "else"] ++ Pretty.expr e)
      (by simp [Pretty.expr]) (by simpa [List.append_assoc] using hend)
      (by simpa [List.append_assoc] using he) (by simp [Expr.sz, Expr.szOpt]; omega)
termination_by e => e.sz
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp [Expr.sz, Expr.szs, Expr.szOpt] <;> omega)
    | (have := sz_lt_szs ‹_›; simp [Expr.sz] <;> omega)
    | (have := sz_lt_szPairs ‹_›; simp [Expr.sz] <;> omega)
    | (have := sz_lt_szKw ‹_›; simp [Expr.sz] <;> omega)
    | (have := sz_lt_szCmps ‹_›; simp [Expr.sz] <;> omega)
    | (simp [Expr.sz] at *; omega)

end LeanJinja2
