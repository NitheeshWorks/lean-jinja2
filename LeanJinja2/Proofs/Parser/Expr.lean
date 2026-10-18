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

theorem listItems_ok : ∀ (xs : List Expr) (m : Nat) (r : List TokKind), (∀ x ∈ xs, x.WF ∧ ExprOK x m) →
    Reads pListItems (m + xs.length + 1) (Pretty.exprs xs ++ [.op .rbracket] ++ r) xs r
  | [], m, r, _ => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [pListItems, Pretty.exprs, isOp]
  | [x], m, r, hx => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hw, hok⟩ := hx x List.mem_cons_self
    obtain ⟨t, tr, ht, hst⟩ := expr_head x hw
    have hx' := hok (.op .rbracket :: r) (stop_op _ _ _ (by simp [contLevel])) n (by simp at hn; omega)
    simp only [Pretty.exprs, List.append_assoc, List.singleton_append] at hx' ⊢
    simp only [pListItems, ht, List.cons_append, List.head?_cons, hst.not_closer.1, Bool.false_eq_true,
      ↓reduceIte, bind, Except.bind]
    rw [← List.cons_append, ← ht, hx']
    simp [isOp]
  | x :: y :: zs, m, r, hx => by
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hw, hok⟩ := hx x List.mem_cons_self
    obtain ⟨t, tr, ht, hst⟩ := expr_head x hw
    have hx' := hok (.op .comma :: (Pretty.exprs (y :: zs) ++ [.op .rbracket] ++ r))
      (stop_op _ _ _ (by simp [contLevel])) n (by simp at hn; omega)
    have ih := listItems_ok (y :: zs) m r (fun z hz => hx z (List.mem_cons_of_mem _ hz)) n
      (by simp at hn ⊢; omega)
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
