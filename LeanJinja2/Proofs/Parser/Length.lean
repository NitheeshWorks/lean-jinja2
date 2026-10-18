import LeanJinja2.Proofs.Parser.Expr

/-!
# Printed expressions are at least as long as they are big

The parser's fuel is a multiple of the token count; the lemmas about it need
fuel a multiple of the expression's size. An expression prints to at least
`sz` tokens.
-/

namespace LeanJinja2

set_option linter.unusedSimpArgs false

theorem joinArgs_length (pos kw : List TokKind) : pos.length + kw.length ≤ (Pretty.joinArgs pos kw).length := by
  simp only [Pretty.joinArgs, List.length_append]; omega

theorem expr_ne_nil' (e : Expr) : Pretty.expr e ≠ [] := by
  cases e with
  | tuple xs => match xs with | [] | [_] | _ :: _ :: _ => simp [Pretty.expr]
  | concat xs => match xs with | [] | _ :: _ => simp [Pretty.expr]
  | cond t b e => cases e <;> simp [Pretty.expr]
  | unop o e => cases o <;> simp [Pretty.expr]
  | const c => cases c <;> simp [Pretty.expr, Pretty.constToks]
  | _ => simp [Pretty.expr]

theorem exprs_nil' : (xs : List Expr) → Pretty.exprs xs = [] → xs = []
  | [], _ => rfl
  | [x], h => absurd (by simpa [Pretty.exprs] using h) (expr_ne_nil' x)
  | x :: y :: ys, h => by simp [Pretty.exprs] at h

theorem kwargs_nil' : (kw : List (String × Expr)) → Pretty.kwargs kw = [] → kw = []
  | [], _ => rfl
  | [(k, v)], h => by simp [Pretty.kwargs] at h
  | (k, v) :: (k', v') :: kw, h => by simp [Pretty.kwargs] at h

theorem parenArgs_length (args : List Expr) (kw : List (String × Expr))
    (h1 : Expr.szs args ≤ (Pretty.exprs args).length + 1) (h2 : Expr.szKw kw ≤ (Pretty.kwargs kw).length) :
    Expr.szs args + Expr.szKw kw ≤ (Pretty.parenArgs (Pretty.exprs args) (Pretty.kwargs kw)).length + 1 := by
  have := joinArgs_length (Pretty.exprs args) (Pretty.kwargs kw)
  unfold Pretty.parenArgs
  split
  · rename_i h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨ha, hk⟩ := h
    rw [exprs_nil' args ha, kwargs_nil' kw hk]
    simp [Expr.szs, Expr.szKw]
  · simp only [List.length_append, List.length_cons, List.length_nil] at *; omega

mutual
theorem expr_length : (e : Expr) → e.sz ≤ (Pretty.expr e).length
  | .const c => by cases c <;> simp [Expr.sz, Pretty.expr, Pretty.constToks]
  | .name _ => by simp [Expr.sz, Pretty.expr]
  | .tuple [x] => by
    have := expr_length x
    simp [Expr.sz, Expr.szs, Pretty.expr]; omega
  | .tuple [] => by simp [Expr.sz, Expr.szs, Pretty.expr, Pretty.exprs]
  | .tuple (x :: y :: ys) => by
    have := exprs_length (x :: y :: ys)
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at this ⊢; omega
  | .list xs => by
    have := exprs_length xs
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at this ⊢; omega
  | .dict ps => by
    have := pairs_length ps
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at this ⊢; omega
  | .getattr e a => by
    have := expr_length e
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at this ⊢; omega
  | .getitem e i => by
    have := expr_length e
    have := subscript_length i
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at *; omega
  | .slice a b c => by
    have := optExpr_length a
    have := optExpr_length b
    have := optStep_length c
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at *; omega
  | .call f args kw => by
    have := expr_length f
    have := exprs_length args
    have := kwargs_length kw
    have := joinArgs_length (Pretty.exprs args) (Pretty.kwargs kw)
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at *; omega
  | .filter e n args kw => by
    have := expr_length e
    have := parenArgs_length args kw (exprs_length args) (kwargs_length kw)
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at *; omega
  | .test e n args kw => by
    have := expr_length e
    have := parenArgs_length args kw (exprs_length args) (kwargs_length kw)
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at *; omega
  | .unop o e => by
    have := expr_length e
    cases o <;> simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at * <;> omega
  | .binop o l r => by
    have := expr_length l
    have := expr_length r
    have : 1 ≤ (Pretty.binTok o).length := by cases o <;> simp [Pretty.binTok]
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at *; omega
  | .compare e ops => by
    have := expr_length e
    have := cmps_length ops
    simp only [Expr.sz, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at *; omega
  | .concat [] => by simp [Expr.sz, Expr.szs, Pretty.expr]
  | .concat (x :: xs) => by
    have := expr_length x
    have := tildes_length xs
    simp only [Expr.sz, Expr.szs, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at *; omega
  | .cond t b none => by
    have := expr_length t
    have := expr_length b
    simp only [Expr.sz, Expr.szOpt, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at *; omega
  | .cond t b (some e) => by
    have := expr_length t
    have := expr_length b
    have := expr_length e
    simp only [Expr.sz, Expr.szOpt, Pretty.expr, List.length_append, List.length_cons, List.length_nil] at *; omega

theorem exprs_length : (xs : List Expr) → Expr.szs xs ≤ (Pretty.exprs xs).length + 1
  | [] => by simp [Expr.szs, Pretty.exprs]
  | [x] => by
    have := expr_length x
    simp [Expr.szs, Pretty.exprs]; omega
  | x :: y :: ys => by
    have := expr_length x
    have := exprs_length (y :: ys)
    simp only [Expr.szs, Pretty.exprs, List.length_append, List.length_cons, List.length_nil] at *; omega

theorem pairs_length : (ps : List (Expr × Expr)) → Expr.szPairs ps ≤ (Pretty.pairs ps).length + 1
  | [] => by simp [Expr.szPairs, Pretty.pairs]
  | [(k, v)] => by
    have := expr_length k
    have := expr_length v
    simp [Expr.szPairs, Pretty.pairs]; omega
  | (k, v) :: q :: qs => by
    have := expr_length k
    have := expr_length v
    have := pairs_length (q :: qs)
    obtain ⟨a, b⟩ := q
    simp only [Expr.szPairs, Pretty.pairs, List.length_append, List.length_cons, List.length_nil] at *; omega

theorem subscript_length : (i : Expr) → i.sz ≤ (Pretty.subscript i).length
  | .slice a b c => by
    have := optExpr_length a
    have := optExpr_length b
    have := optStep_length c
    simp only [Expr.sz, Pretty.subscript, List.length_append, List.length_cons, List.length_nil] at *; omega
  | .const c => by simpa [Pretty.subscript] using expr_length (.const c)
  | .name s => by simpa [Pretty.subscript] using expr_length (.name s)
  | .tuple xs => by simpa [Pretty.subscript] using expr_length (.tuple xs)
  | .list xs => by simpa [Pretty.subscript] using expr_length (.list xs)
  | .dict xs => by simpa [Pretty.subscript] using expr_length (.dict xs)
  | .getattr e a => by simpa [Pretty.subscript] using expr_length (.getattr e a)
  | .getitem e a => by simpa [Pretty.subscript] using expr_length (.getitem e a)
  | .call f a k => by simpa [Pretty.subscript] using expr_length (.call f a k)
  | .filter e n a k => by simpa [Pretty.subscript] using expr_length (.filter e n a k)
  | .test e n a k => by simpa [Pretty.subscript] using expr_length (.test e n a k)
  | .unop o e => by simpa [Pretty.subscript] using expr_length (.unop o e)
  | .binop o l r => by simpa [Pretty.subscript] using expr_length (.binop o l r)
  | .compare e o => by simpa [Pretty.subscript] using expr_length (.compare e o)
  | .concat xs => by simpa [Pretty.subscript] using expr_length (.concat xs)
  | .cond t b e => by simpa [Pretty.subscript] using expr_length (.cond t b e)

theorem optExpr_length : (o : Option Expr) → Expr.szOpt o ≤ (Pretty.optExpr o).length
  | none => by simp [Expr.szOpt, Pretty.optExpr]
  | some e => by simpa [Expr.szOpt, Pretty.optExpr] using expr_length e

theorem optStep_length : (o : Option Expr) → Expr.szOpt o ≤ (Pretty.optStep o).length
  | none => by simp [Expr.szOpt, Pretty.optStep]
  | some e => by
    have := expr_length e
    simp [Expr.szOpt, Pretty.optStep]; omega

theorem cmps_length : (ops : List (CmpOp × Expr)) → Expr.szCmps ops ≤ (Pretty.cmps ops).length
  | [] => by simp [Expr.szCmps, Pretty.cmps]
  | (o, e) :: ops => by
    have := expr_length e
    have := cmps_length ops
    have : 1 ≤ (Pretty.cmpTok o).length := by cases o <;> simp [Pretty.cmpTok]
    simp only [Expr.szCmps, Pretty.cmps, List.length_append] at *; omega

theorem tildes_length : (xs : List Expr) → Expr.szs xs ≤ (Pretty.tildes xs).length
  | [] => by simp [Expr.szs, Pretty.tildes]
  | x :: xs => by
    have := expr_length x
    have := tildes_length xs
    simp only [Expr.szs, Pretty.tildes, List.length_append, List.length_cons, List.length_nil] at *; omega

theorem kwargs_length : (kw : List (String × Expr)) → Expr.szKw kw ≤ (Pretty.kwargs kw).length
  | [] => by simp [Expr.szKw, Pretty.kwargs]
  | [(k, v)] => by
    have := expr_length v
    simp [Expr.szKw, Pretty.kwargs]; omega
  | (k, v) :: q :: qs => by
    have := expr_length v
    have := kwargs_length (q :: qs)
    obtain ⟨a, b⟩ := q
    simp only [Expr.szKw, Pretty.kwargs, List.length_append, List.length_cons, List.length_nil] at *; omega

end

end LeanJinja2
