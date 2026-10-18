import LeanJinja2.Proofs.Parser.Body

/-!
# Printed tag contents are lexable

The lexer reads the inside of a tag token by token and keeps a stack of the
closing brackets it expects. A printed expression (and every other tag
content the printer produces) consists of tokens the lexer reads back
(`InnerAll`) and is bracket-balanced (`Bal`).
-/

namespace LeanJinja2

open Lex

set_option linter.unusedSimpArgs false

/-- A token the lexer reads back from its printed text inside a tag. -/
def InnerTok : TokKind → Prop
  | .name s => IsIdent s
  | .int _ | .float .. | .str _ | .op _ => True
  | _ => False

def InnerAll (ks : List TokKind) : Prop := ∀ k ∈ ks, InnerTok k

@[simp] theorem innerAll_nil : InnerAll [] := by simp [InnerAll]
@[simp] theorem innerAll_cons {k : TokKind} {ks : List TokKind} : InnerAll (k :: ks) ↔ InnerTok k ∧ InnerAll ks := by
  simp [InnerAll]
@[simp] theorem innerAll_append {a b : List TokKind} : InnerAll (a ++ b) ↔ InnerAll a ∧ InnerAll b := by
  simp only [InnerAll, List.mem_append]
  constructor
  · intro h; exact ⟨fun k hk => h k (Or.inl hk), fun k hk => h k (Or.inr hk)⟩
  · rintro ⟨h1, h2⟩ k (hk | hk)
    · exact h1 k hk
    · exact h2 k hk

/-- The lexer's bracket stack after one token (`stepTag`'s update). -/
def stackStep (st : List Char) : TokKind → Option (List Char)
  | .op o =>
    match closerOf o, isCloser o with
    | some c, _ => some (c :: st)
    | none, some c =>
      match st with
      | [] => none
      | e :: st => if e == c then some st else none
    | none, none => some st
  | _ => some st

/-- The bracket stack after a token list. -/
def stackAfter : List Char → List TokKind → Option (List Char)
  | st, [] => some st
  | st, k :: ks =>
    match stackStep st k with
    | none => none
    | some st' => stackAfter st' ks

/-- A balanced token list: it leaves every bracket stack as it found it. -/
abbrev Bal (ks : List TokKind) : Prop := ∀ st rest, stackAfter st (ks ++ rest) = stackAfter st rest

/-- Identifiers by computation. -/
def identB (s : String) : Bool :=
  match s.toList with
  | c :: cs => isIdentChar c && !c.isDigit && c != '\xb7' && cs.all isIdentChar
  | [] => false

theorem IsIdent.of_identB {s : String} (h : identB s = true) : IsIdent s := by
  unfold identB at h
  split at h
  · rename_i c cs hs
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, List.all_eq_true] at h
    exact ⟨c, cs, hs, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · cases h

theorem inner_name_lit (s : String) (h : identB s = true := by decide) : InnerTok (.name s) :=
  IsIdent.of_identB h

theorem bal_nil : Bal [] := fun _ _ => rfl

@[simp] theorem stackAfter_cons (st : List Char) (k : TokKind) (ks : List TokKind) :
    stackAfter st (k :: ks) = (stackStep st k).bind (fun st' => stackAfter st' ks) := by
  simp only [stackAfter]; cases stackStep st k <;> rfl

end LeanJinja2

namespace LeanJinja2

open Lex

set_option linter.unusedSimpArgs false

theorem bal_joinArgs {pos kw : List TokKind} (hp : Bal pos) (hk : Bal kw) : Bal (Pretty.joinArgs pos kw) := by
  intro st rest
  simp only [Pretty.joinArgs, List.append_assoc]
  rw [hp]
  split <;> simp [stackStep, closerOf, isCloser, hk]

theorem bal_parenArgs {pos kw : List TokKind} (hp : Bal pos) (hk : Bal kw) : Bal (Pretty.parenArgs pos kw) := by
  intro st rest
  simp only [Pretty.parenArgs]
  split
  · rfl
  · simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [stackStep, closerOf, isCloser, bal_joinArgs hp hk _ _]

mutual
theorem expr_bal : (e : Expr) → Bal (Pretty.expr e)
  | .const c => by intro st rest; cases c <;> simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok]
  | .name _ => by intro st rest; simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok]
  | .tuple [x] => by
    have h := expr_bal x
    intro st rest; simp only [Pretty.expr, Pretty.exprs, Pretty.pairs, Pretty.subscript, Pretty.optStep, Pretty.optExpr, Pretty.cmps, Pretty.tildes, Pretty.kwargs, Pretty.joinArgs, Pretty.parenArgs, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]; simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h]
  | .tuple [] => by intro st rest; simp only [Pretty.expr, Pretty.exprs, Pretty.pairs, Pretty.subscript, Pretty.optStep, Pretty.optExpr, Pretty.cmps, Pretty.tildes, Pretty.kwargs, Pretty.joinArgs, Pretty.parenArgs, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]; simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok]
  | .tuple (x :: y :: ys) => by
    have h := exprs_bal (x :: y :: ys)
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h]
  | .list xs => by
    have h := exprs_bal xs
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h]
  | .dict ps => by
    have h := pairs_bal ps
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h]
  | .getattr e a => by
    have h := expr_bal e
    intro st rest; simp only [Pretty.expr, Pretty.exprs, Pretty.pairs, Pretty.subscript, Pretty.optStep, Pretty.optExpr, Pretty.cmps, Pretty.tildes, Pretty.kwargs, Pretty.joinArgs, Pretty.parenArgs, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]; simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h]
  | .getitem e i => by
    have h := expr_bal e
    have h2 := subscript_bal i
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h, h2]
  | .slice a b c => by
    have h1 := optExpr_bal a
    have h2 := optExpr_bal b
    have h3 := optStep_bal c
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2, h3]
  | .call f args kw => by
    have h := expr_bal f
    have h2 := bal_joinArgs (exprs_bal args) (kwargs_bal kw)
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h, h2]
  | .filter e n args kw => by
    have h := expr_bal e
    have h2 := bal_parenArgs (exprs_bal args) (kwargs_bal kw)
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h, h2]
  | .test e n args kw => by
    have h := expr_bal e
    have h2 := bal_parenArgs (exprs_bal args) (kwargs_bal kw)
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h, h2]
  | .unop o e => by
    have h := expr_bal e
    intro st rest
    cases o <;> simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append,
      List.singleton_append] <;> simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h]
  | .binop o l r => by
    have h1 := expr_bal l
    have h2 := expr_bal r
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    cases o <;> simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2]
  | .compare e ops => by
    have h1 := expr_bal e
    have h2 := cmps_bal ops
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2]
  | .concat [] => by intro st rest; simp [Pretty.expr, stackStep, closerOf, isCloser]
  | .concat (x :: xs) => by
    have h1 := expr_bal x
    have h2 := tildes_bal xs
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2]
  | .cond t b none => by
    have h1 := expr_bal t
    have h2 := expr_bal b
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2]
  | .cond t b (some e) => by
    have h1 := expr_bal t
    have h2 := expr_bal b
    have h3 := expr_bal e
    intro st rest
    simp only [Pretty.expr, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2, h3]

theorem exprs_bal : (xs : List Expr) → Bal (Pretty.exprs xs)
  | [] => by simp only [Pretty.exprs]; exact bal_nil
  | [x] => by simpa [Pretty.exprs] using expr_bal x
  | x :: y :: ys => by
    have h1 := expr_bal x
    have h2 := exprs_bal (y :: ys)
    intro st rest
    simp only [Pretty.exprs, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2]

theorem pairs_bal : (ps : List (Expr × Expr)) → Bal (Pretty.pairs ps)
  | [] => by simp only [Pretty.pairs]; exact bal_nil
  | [(k, v)] => by
    have h1 := expr_bal k
    have h2 := expr_bal v
    intro st rest
    simp only [Pretty.pairs, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2]
  | (k, v) :: q :: qs => by
    have h1 := expr_bal k
    have h2 := expr_bal v
    have h3 := pairs_bal (q :: qs)
    obtain ⟨a, b⟩ := q
    intro st rest
    simp only [Pretty.pairs, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at h3 ⊢
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2, h3]

theorem subscript_bal : (i : Expr) → Bal (Pretty.subscript i)
  | .slice a b c => by
    have h1 := optExpr_bal a
    have h2 := optExpr_bal b
    have h3 := optStep_bal c
    intro st rest
    simp only [Pretty.subscript, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2, h3]
  | .const c => by simpa [Pretty.subscript] using expr_bal (.const c)
  | .name s => by simpa [Pretty.subscript] using expr_bal (.name s)
  | .tuple xs => by simpa [Pretty.subscript] using expr_bal (.tuple xs)
  | .list xs => by simpa [Pretty.subscript] using expr_bal (.list xs)
  | .dict xs => by simpa [Pretty.subscript] using expr_bal (.dict xs)
  | .getattr e a => by simpa [Pretty.subscript] using expr_bal (.getattr e a)
  | .getitem e a => by simpa [Pretty.subscript] using expr_bal (.getitem e a)
  | .call f a k => by simpa [Pretty.subscript] using expr_bal (.call f a k)
  | .filter e n a k => by simpa [Pretty.subscript] using expr_bal (.filter e n a k)
  | .test e n a k => by simpa [Pretty.subscript] using expr_bal (.test e n a k)
  | .unop o e => by simpa [Pretty.subscript] using expr_bal (.unop o e)
  | .binop o l r => by simpa [Pretty.subscript] using expr_bal (.binop o l r)
  | .compare e o => by simpa [Pretty.subscript] using expr_bal (.compare e o)
  | .concat xs => by simpa [Pretty.subscript] using expr_bal (.concat xs)
  | .cond t b e => by simpa [Pretty.subscript] using expr_bal (.cond t b e)

theorem optExpr_bal : (o : Option Expr) → Bal (Pretty.optExpr o)
  | none => by simp only [Pretty.optExpr]; exact bal_nil
  | some e => by simpa [Pretty.optExpr] using expr_bal e

theorem optStep_bal : (o : Option Expr) → Bal (Pretty.optStep o)
  | none => by simp only [Pretty.optStep]; exact bal_nil
  | some e => by
    have h := expr_bal e
    intro st rest
    simp only [Pretty.optStep, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h]

theorem cmps_bal : (ops : List (CmpOp × Expr)) → Bal (Pretty.cmps ops)
  | [] => by simp only [Pretty.cmps]; exact bal_nil
  | (o, e) :: ops => by
    have h1 := expr_bal e
    have h2 := cmps_bal ops
    intro st rest
    simp only [Pretty.cmps, List.append_assoc]
    cases o <;> simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2]

theorem tildes_bal : (xs : List Expr) → Bal (Pretty.tildes xs)
  | [] => by simp only [Pretty.tildes]; exact bal_nil
  | x :: xs => by
    have h1 := expr_bal x
    have h2 := tildes_bal xs
    intro st rest
    simp only [Pretty.tildes, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    simp [Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2]

theorem kwargs_bal : (kw : List (String × Expr)) → Bal (Pretty.kwargs kw)
  | [] => by simp only [Pretty.kwargs]; exact bal_nil
  | [(k, v)] => by
    have h := expr_bal v
    intro st rest
    simp only [Pretty.kwargs, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    rcases kwKey_cases k with h0 | h0 | h0 <;>
      simp [h0, Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h]
  | (k, v) :: q :: qs => by
    have h1 := expr_bal v
    have h2 := kwargs_bal (q :: qs)
    obtain ⟨a, b⟩ := q
    intro st rest
    simp only [Pretty.kwargs, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at h2 ⊢
    rcases kwKey_cases k with h0 | h0 | h0 <;>
      simp [h0, Pretty.expr, stackStep, closerOf, isCloser, Pretty.constToks, Pretty.binTok, Pretty.cmpTok, h1, h2]
end

end LeanJinja2

namespace LeanJinja2

set_option linter.unusedSimpArgs false

@[simp] theorem isIdent_is : IsIdent "is" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_in : IsIdent "in" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_not : IsIdent "not" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_and : IsIdent "and" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_or : IsIdent "or" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_if : IsIdent "if" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_else : IsIdent "else" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_none : IsIdent "none" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_true : IsIdent "true" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_false : IsIdent "false" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_recursive : IsIdent "recursive" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_for : IsIdent "for" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_set : IsIdent "set" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_macro : IsIdent "macro" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_call : IsIdent "call" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_filter : IsIdent "filter" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_include : IsIdent "include" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_extends : IsIdent "extends" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_block : IsIdent "block" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_with : IsIdent "with" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_without : IsIdent "without" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_context : IsIdent "context" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_ignore : IsIdent "ignore" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_missing : IsIdent "missing" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_scoped : IsIdent "scoped" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_required : IsIdent "required" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_autoescape : IsIdent "autoescape" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_elif : IsIdent "elif" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_endif : IsIdent "endif" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_endfor : IsIdent "endfor" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_endset : IsIdent "endset" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_endmacro : IsIdent "endmacro" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_endcall : IsIdent "endcall" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_endfilter : IsIdent "endfilter" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_endblock : IsIdent "endblock" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_endwith : IsIdent "endwith" := IsIdent.of_identB (by decide)
@[simp] theorem isIdent_endautoescape : IsIdent "endautoescape" := IsIdent.of_identB (by decide)

theorem innerAll_joinArgs {pos kw : List TokKind} (hp : InnerAll pos) (hk : InnerAll kw) :
    InnerAll (Pretty.joinArgs pos kw) := by
  simp only [Pretty.joinArgs, innerAll_append]; refine ⟨⟨hp, ?_⟩, hk⟩; split <;> simp [InnerTok]

theorem innerAll_parenArgs {pos kw : List TokKind} (hp : InnerAll pos) (hk : InnerAll kw) :
    InnerAll (Pretty.parenArgs pos kw) := by
  simp only [Pretty.parenArgs]; split
  · simp
  · simp [InnerTok, innerAll_joinArgs hp hk]

mutual
theorem expr_inner : (e : Expr) → e.WF → InnerAll (Pretty.expr e)
  | .const c, _ => by
    cases c with
    | bool b => cases b <;> simp [Pretty.expr, Pretty.constToks, InnerTok]
    | _ => simp [Pretty.expr, Pretty.constToks, InnerTok]
  | .name _, hw => by simp_all [Expr.WF, Pretty.expr, InnerTok, VarName]
  | .tuple [x], hw => by
    have h := expr_inner x (by simp_all [Expr.WF, Expr.WFs])
    simp [Pretty.expr, InnerTok, h]
  | .tuple [], _ => by simp [Pretty.expr, Pretty.exprs, InnerTok]
  | .tuple (x :: y :: ys), hw => by
    have h := exprs_inner (x :: y :: ys) (by simpa [Expr.WF] using hw)
    simp only [Pretty.expr] at h ⊢; simp [InnerTok, h]
  | .list xs, hw => by
    have h := exprs_inner xs (by simpa [Expr.WF] using hw)
    simp [Pretty.expr, InnerTok, h]
  | .dict ps, hw => by
    have h := pairs_inner ps (by simpa [Expr.WF] using hw)
    simp [Pretty.expr, InnerTok, h]
  | .getattr e a, hw => by
    simp only [Expr.WF] at hw
    have h := expr_inner e hw.1
    simp [Pretty.expr, InnerTok, h, hw.2.1]
  | .getitem e i, hw => by
    simp only [Expr.WF] at hw
    have h := expr_inner e hw.1
    have h2 := subscript_inner i hw.2
    simp [Pretty.expr, InnerTok, h, h2]
  | .slice .., hw => by simp [Expr.WF] at hw
  | .call f args kw, hw => by
    simp only [Expr.WF] at hw
    have h := expr_inner f hw.1
    have h2 := innerAll_joinArgs (exprs_inner args hw.2.1) (kwargs_inner kw hw.2.2)
    simp [Pretty.expr, InnerTok, h, h2]
  | .filter e n args kw, hw => by
    simp only [Expr.WF] at hw
    have h := expr_inner e hw.1
    have h2 := innerAll_parenArgs (exprs_inner args hw.2.2.1) (kwargs_inner kw hw.2.2.2)
    simp [Pretty.expr, InnerTok, h, h2, hw.2.1.1]
  | .test e n args kw, hw => by
    simp only [Expr.WF] at hw
    have h := expr_inner e hw.1
    have h2 := innerAll_parenArgs (exprs_inner args hw.2.2.1) (kwargs_inner kw hw.2.2.2)
    simp [Pretty.expr, InnerTok, h, h2, hw.2.1.1]
  | .unop o e, hw => by
    simp only [Expr.WF] at hw
    have h := expr_inner e hw
    cases o <;> simp [Pretty.expr, InnerTok, h]
  | .binop o l r, hw => by
    simp only [Expr.WF] at hw
    have h1 := expr_inner l hw.1
    have h2 := expr_inner r hw.2
    cases o <;> simp [Pretty.expr, Pretty.binTok, InnerTok, h1, h2]
  | .compare e ops, hw => by
    simp only [Expr.WF] at hw
    have h1 := expr_inner e hw.1
    have h2 := cmps_inner ops hw.2.2
    simp [Pretty.expr, InnerTok, h1, h2]
  | .concat [], _ => by simp [Pretty.expr, InnerTok]
  | .concat (x :: xs), hw => by
    simp only [Expr.WF, Expr.WFs] at hw
    have h1 := expr_inner x hw.2.1
    have h2 := tildes_inner xs hw.2.2
    simp [Pretty.expr, InnerTok, h1, h2]
  | .cond t b none, hw => by
    simp only [Expr.WF] at hw
    have h1 := expr_inner t hw.1
    have h2 := expr_inner b hw.2.1
    simp [Pretty.expr, InnerTok, h1, h2]
  | .cond t b (some e), hw => by
    simp only [Expr.WF, Expr.WFOpt] at hw
    have h1 := expr_inner t hw.1
    have h2 := expr_inner b hw.2.1
    have h3 := expr_inner e hw.2.2
    simp [Pretty.expr, InnerTok, h1, h2, h3]

theorem exprs_inner : (xs : List Expr) → Expr.WFs xs → InnerAll (Pretty.exprs xs)
  | [], _ => by simp [Pretty.exprs]
  | [x], hw => by simpa [Pretty.exprs] using expr_inner x (by simp_all [Expr.WFs])
  | x :: y :: ys, hw => by
    simp only [Expr.WFs] at hw
    have h1 := expr_inner x hw.1
    have h2 := exprs_inner (y :: ys) (by simpa [Expr.WFs] using hw.2)
    simp only [Pretty.exprs] at h2 ⊢
    simp [InnerTok, h1, h2]

theorem pairs_inner : (ps : List (Expr × Expr)) → Expr.WFPairs ps → InnerAll (Pretty.pairs ps)
  | [], _ => by simp [Pretty.pairs]
  | [(k, v)], hw => by
    simp only [Expr.WFPairs] at hw
    simp [Pretty.pairs, InnerTok, expr_inner k hw.1, expr_inner v hw.2.1]
  | (k, v) :: q :: qs, hw => by
    simp only [Expr.WFPairs] at hw
    have h3 := pairs_inner (q :: qs) hw.2.2
    obtain ⟨a, b⟩ := q
    simp only [Pretty.pairs] at h3 ⊢
    simp [InnerTok, expr_inner k hw.1, expr_inner v hw.2.1, h3]

theorem subscript_inner : (i : Expr) → i.SubWF → InnerAll (Pretty.subscript i)
  | .slice a b c, hw => by
    simp only [Expr.SubWF] at hw
    simp [Pretty.subscript, InnerTok, optExpr_inner a hw.1, optExpr_inner b hw.2.1, optStep_inner c hw.2.2]
  | .const c, hw => by simpa [Pretty.subscript] using expr_inner (.const c) (by simpa [Expr.SubWF] using hw)
  | .name s, hw => by simpa [Pretty.subscript] using expr_inner (.name s) (by simpa [Expr.SubWF] using hw)
  | .tuple xs, hw => by simpa [Pretty.subscript] using expr_inner (.tuple xs) (by simpa [Expr.SubWF] using hw)
  | .list xs, hw => by simpa [Pretty.subscript] using expr_inner (.list xs) (by simpa [Expr.SubWF] using hw)
  | .dict xs, hw => by simpa [Pretty.subscript] using expr_inner (.dict xs) (by simpa [Expr.SubWF] using hw)
  | .getattr e a, hw => by simpa [Pretty.subscript] using expr_inner (.getattr e a) (by simpa [Expr.SubWF] using hw)
  | .getitem e a, hw => by simpa [Pretty.subscript] using expr_inner (.getitem e a) (by simpa [Expr.SubWF] using hw)
  | .call f a k, hw => by simpa [Pretty.subscript] using expr_inner (.call f a k) (by simpa [Expr.SubWF] using hw)
  | .filter e n a k, hw => by simpa [Pretty.subscript] using expr_inner (.filter e n a k) (by simpa [Expr.SubWF] using hw)
  | .test e n a k, hw => by simpa [Pretty.subscript] using expr_inner (.test e n a k) (by simpa [Expr.SubWF] using hw)
  | .unop o e, hw => by simpa [Pretty.subscript] using expr_inner (.unop o e) (by simpa [Expr.SubWF] using hw)
  | .binop o l r, hw => by simpa [Pretty.subscript] using expr_inner (.binop o l r) (by simpa [Expr.SubWF] using hw)
  | .compare e o, hw => by simpa [Pretty.subscript] using expr_inner (.compare e o) (by simpa [Expr.SubWF] using hw)
  | .concat xs, hw => by simpa [Pretty.subscript] using expr_inner (.concat xs) (by simpa [Expr.SubWF] using hw)
  | .cond t b e, hw => by simpa [Pretty.subscript] using expr_inner (.cond t b e) (by simpa [Expr.SubWF] using hw)

theorem optExpr_inner : (o : Option Expr) → Expr.WFOpt o → InnerAll (Pretty.optExpr o)
  | none, _ => by simp [Pretty.optExpr]
  | some e, hw => by simpa [Pretty.optExpr] using expr_inner e (by simpa [Expr.WFOpt] using hw)

theorem optStep_inner : (o : Option Expr) → Expr.WFOpt o → InnerAll (Pretty.optStep o)
  | none, _ => by simp [Pretty.optStep]
  | some e, hw => by simp [Pretty.optStep, InnerTok, expr_inner e (by simpa [Expr.WFOpt] using hw)]

theorem cmps_inner : (ops : List (CmpOp × Expr)) → Expr.WFCmps ops → InnerAll (Pretty.cmps ops)
  | [], _ => by simp [Pretty.cmps]
  | (o, e) :: ops, hw => by
    simp only [Expr.WFCmps] at hw
    have h1 := expr_inner e hw.1
    have h2 := cmps_inner ops hw.2
    cases o <;> simp [Pretty.cmps, Pretty.cmpTok, InnerTok, h1, h2]

theorem tildes_inner : (xs : List Expr) → Expr.WFs xs → InnerAll (Pretty.tildes xs)
  | [], _ => by simp [Pretty.tildes]
  | x :: xs, hw => by
    simp only [Expr.WFs] at hw
    simp [Pretty.tildes, InnerTok, expr_inner x hw.1, tildes_inner xs hw.2]

theorem kwargs_inner : (kw : List (String × Expr)) → Expr.WFKw kw → InnerAll (Pretty.kwargs kw)
  | [], _ => by simp [Pretty.kwargs]
  | [(k, v)], hw => by
    simp only [Expr.WFKw] at hw
    simp [Pretty.kwargs, kwKey_var hw.1, InnerTok, expr_inner v hw.2.1, hw.1.1]
  | (k, v) :: q :: qs, hw => by
    simp only [Expr.WFKw] at hw
    have h2 := kwargs_inner (q :: qs) hw.2.2
    obtain ⟨a, b⟩ := q
    simp only [Pretty.kwargs] at h2 ⊢
    simp [kwKey_var hw.1, InnerTok, expr_inner v hw.2.1, hw.1.1, h2]
end

end LeanJinja2
