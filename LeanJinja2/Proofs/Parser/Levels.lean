import LeanJinja2.Specifications.Syntax

/-!
# The expression grammar's levels

Upstream's precedence tower, read as levels: a token *continues* an
expression at level `k` when the parser function for that level (or one
below it) would consume it after an operand. `Stop k ts` says the tokens
after an operand do not continue it at level `k`, so every loop up to level
`k` returns the operand unchanged. With it, one lemma per level lifts "the
primary parser reads `e`" to "the level-`k` parser reads `e`".
-/

namespace LeanJinja2

open Parse

set_option linter.unusedSimpArgs false

@[simp] theorem isOp_op (o p : Op) : isOp o (some (.op p)) = (p == o) := rfl
@[simp] theorem isOp_none (o : Op) : isOp o none = false := rfl
@[simp] theorem isOp_name (o : Op) (s : String) : isOp o (some (.name s)) = false := rfl
@[simp] theorem isOp_str (o : Op) (s : String) : isOp o (some (.str s)) = false := rfl
@[simp] theorem isOp_int (o : Op) (k : Nat) : isOp o (some (.int k)) = false := rfl
@[simp] theorem isOp_float (o : Op) (a b : Nat) : isOp o (some (.float a b)) = false := rfl
@[simp] theorem isOp_data (o : Op) (s : String) : isOp o (some (.data s)) = false := rfl
@[simp] theorem isOp_varEnd (o : Op) : isOp o (some .varEnd) = false := rfl
@[simp] theorem isOp_blockEnd (o : Op) : isOp o (some .blockEnd) = false := rfl
@[simp] theorem isOp_varBegin (o : Op) : isOp o (some .varBegin) = false := rfl
@[simp] theorem isOp_blockBegin (o : Op) : isOp o (some .blockBegin) = false := rfl

@[simp] theorem isName_name (s t : String) : isName s (some (.name t)) = (t == s) := rfl
@[simp] theorem isName_none (s : String) : isName s none = false := rfl
@[simp] theorem isName_op (s : String) (o : Op) : isName s (some (.op o)) = false := rfl
@[simp] theorem isName_str (s t : String) : isName s (some (.str t)) = false := rfl
@[simp] theorem isName_int (s : String) (k : Nat) : isName s (some (.int k)) = false := rfl
@[simp] theorem isName_float (s : String) (a b : Nat) : isName s (some (.float a b)) = false := rfl
@[simp] theorem isName_data (s t : String) : isName s (some (.data t)) = false := rfl
@[simp] theorem isName_varEnd (s : String) : isName s (some .varEnd) = false := rfl
@[simp] theorem isName_blockEnd (s : String) : isName s (some .blockEnd) = false := rfl
@[simp] theorem isName_blockBegin (s : String) : isName s (some .blockBegin) = false := rfl

/-- The lowest level at which a token continues an expression (99: never). -/
def contLevel : TokKind → Nat
  | .op .dot | .op .lbracket | .op .lparen | .str _ => 0
  | .op .pipe => 1
  | .op .pow => 2
  | .op .mul | .op .div | .op .floordiv | .op .mod => 3
  | .op .tilde => 4
  | .op .add | .op .sub => 5
  | .op .eq | .op .ne | .op .lt | .op .lteq | .op .gt | .op .gteq => 6
  | .name s =>
    if s = "is" then 1 else if s = "in" ∨ s = "not" then 6 else if s = "and" then 8
    else if s = "or" then 9 else if s = "if" then 10 else 99
  | _ => 99

/-- The tokens after an operand do not continue it at level `k`. -/
def Stop (k : Nat) (ts : List TokKind) : Prop := ∀ t, ts.head? = some t → k < contLevel t

theorem Stop.mono {k k' : Nat} {ts : List TokKind} (h : Stop k ts) (hk : k' ≤ k) : Stop k' ts :=
  fun t ht => Nat.lt_of_le_of_lt hk (h t ht)

theorem Stop.cons {k : Nat} {t : TokKind} {ts : List TokKind} (h : k < contLevel t) : Stop k (t :: ts) := by
  intro t' ht; simp at ht; subst ht; exact h

theorem Stop.nil (k : Nat) : Stop k [] := fun _ h => by simp at h

theorem stop_rparen (k : Nat) (ts : List TokKind) (hk : k < 99) : Stop k (.op .rparen :: ts) :=
  Stop.cons (by simp [contLevel]; omega)

/-- A name token's level, decided. -/
theorem contLevel_name (s : String) :
    contLevel (.name s) =
      if s = "is" then 1 else if s = "in" ∨ s = "not" then 6 else if s = "and" then 8
      else if s = "or" then 9 else if s = "if" then 10 else 99 := rfl

theorem isName_of_stop {k : Nat} {ts : List TokKind} {s : String} (h : Stop k ts)
    (hs : contLevel (.name s) ≤ k) : isName s ts.head? = false := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have := h t rfl
    cases t <;> simp [isName] at *
    rename_i s'
    intro heq; subst heq; omega

/-! ## Loops return on a stop -/

theorem pCondLoop_stop {n e ts} (h : Stop 10 ts) : pCondLoop (n + 1) e ts = .ok (e, ts) := by
  simp [pCondLoop, isName_of_stop (s := "if") h (by simp [contLevel_name])]

theorem pOrLoop_stop {n e ts} (h : Stop 9 ts) : pOrLoop (n + 1) e ts = .ok (e, ts) := by
  simp [pOrLoop, isName_of_stop (s := "or") h (by simp [contLevel_name])]

theorem pAndLoop_stop {n e ts} (h : Stop 8 ts) : pAndLoop (n + 1) e ts = .ok (e, ts) := by
  simp [pAndLoop, isName_of_stop (s := "and") h (by simp [contLevel_name])]

theorem pCmpOps_stop {n ts} (h : Stop 6 ts) : pCmpOps (n + 1) ts = .ok ([], ts) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have := h t rfl
    simp only [pCmpOps]
    cases t with
    | op o => cases o <;> simp_all [contLevel, cmpOpOf]
    | name s =>
      simp only [contLevel_name] at this
      by_cases h1 : s = "in"
      · subst h1; simp at this
      by_cases h2 : s = "not"
      · subst h2; simp at this
      split <;> simp_all
    | _ => rfl

theorem pMath1Loop_stop {n e ts} (h : Stop 5 ts) : pMath1Loop (n + 1) e ts = .ok (e, ts) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have := h t rfl
    cases t with
    | op o => cases o <;> simp_all [contLevel, pMath1Loop, math1Op]
    | _ => rfl

theorem pConcatRest_stop {n ts} (h : Stop 4 ts) : pConcatRest (n + 1) ts = .ok ([], ts) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have := h t rfl
    cases t with
    | op o => cases o <;> simp_all [contLevel, pConcatRest]
    | _ => rfl

theorem pMath2Loop_stop {n e ts} (h : Stop 3 ts) : pMath2Loop (n + 1) e ts = .ok (e, ts) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have := h t rfl
    cases t with
    | op o => cases o <;> simp_all [contLevel, pMath2Loop, math2Op]
    | _ => rfl

theorem pPowLoop_stop {n e ts} (h : Stop 2 ts) : pPowLoop (n + 1) e ts = .ok (e, ts) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have := h t rfl
    cases t with
    | op o => cases o <;> simp_all [contLevel, pPowLoop]
    | _ => rfl

theorem pPostfix_stop {n e ts} (h : Stop 0 ts) : pPostfix (n + 1) e ts = .ok (e, ts) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have := h t rfl
    cases t with
    | op o => cases o <;> simp_all [contLevel, pPostfix]
    | _ => rfl

theorem pFilterExpr_stop {n e ts} (h : Stop 1 ts) : pFilterExpr (n + 1) e ts = .ok (e, ts) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have := h t rfl
    cases t with
    | op o => cases o <;> simp_all [contLevel, pFilterExpr]
    | name s =>
      simp only [contLevel_name] at this
      by_cases h1 : s = "is"
      · subst h1; simp at this
      · simp [pFilterExpr, h1]
    | _ => rfl

/-! ## Lifting a read through the levels -/

/-- `p` reads `a` from `ts`, leaving `r`, with any fuel from `m` on. -/
def Reads {α : Type} (p : Nat → List TokKind → PR α) (m : Nat) (ts : List TokKind) (a : α)
    (r : List TokKind) : Prop :=
  ∀ n, m ≤ n → p n ts = .ok (a, r)

/-- `ts` does not start with a unary sign. -/
def NoSign (ts : List TokKind) : Prop := ∀ t, ts.head? = some t → t ≠ .op .sub ∧ t ≠ .op .add

theorem pUnary_primary {n wf ts} (hs : NoSign ts) :
    pUnary (n + 1) wf ts = (do
      let (e, ts) ← pPrimary n ts
      let (e, ts) ← pPostfix n e ts
      if wf then pFilterExpr n e ts else .ok (e, ts)) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have := hs t rfl
    cases t with
    | op o => cases o <;> first | rfl | simp_all
    | _ => rfl

theorem Reads.unary {m ts e r} (wf : Bool) (h : Reads pPrimary (m + 1) ts e r) (hs : NoSign ts)
    (hr : Stop (if wf then 1 else 0) r) : Reads (fun n => pUnary n wf) (m + 2) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pUnary_primary hs, h (n + 1) (by omega), bind, Except.bind]
  rw [pPostfix_stop (hr.mono (by split <;> omega))]
  cases wf with
  | true => simp only [ite_true]; exact pFilterExpr_stop (by simpa using hr)
  | false => rfl

theorem Reads.pow {m ts e r} (h : Reads (fun n => pUnary n true) (m + 1) ts e r) (hr : Stop 2 r) :
    Reads pPow (m + 2) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pPow, h (n + 1) (by omega), bind, Except.bind]
  exact pPowLoop_stop hr

theorem Reads.math2 {m ts e r} (h : Reads pPow (m + 1) ts e r) (hr : Stop 3 r) :
    Reads pMath2 (m + 2) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pMath2, h (n + 1) (by omega), bind, Except.bind]
  exact pMath2Loop_stop hr

theorem Reads.concat {m ts e r} (h : Reads pMath2 (m + 1) ts e r) (hr : Stop 4 r) :
    Reads pConcat (m + 2) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pConcat, h (n + 1) (by omega), bind, Except.bind, pConcatRest_stop hr]
  rfl

theorem Reads.math1 {m ts e r} (h : Reads pConcat (m + 1) ts e r) (hr : Stop 5 r) :
    Reads pMath1 (m + 2) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pMath1, h (n + 1) (by omega), bind, Except.bind]
  exact pMath1Loop_stop hr

theorem Reads.compare {m ts e r} (h : Reads pMath1 (m + 1) ts e r) (hr : Stop 6 r) :
    Reads pCompare (m + 2) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pCompare, h (n + 1) (by omega), bind, Except.bind, pCmpOps_stop hr]
  rfl

/-- `ts` does not start with `not`. -/
def NoNot (ts : List TokKind) : Prop := isName "not" ts.head? = false

theorem Reads.not {m ts e r} (h : Reads pCompare (m + 1) ts e r) (hs : NoNot ts) :
    Reads pNot (m + 2) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pNot, show isName "not" ts.head? = false from hs, Bool.false_eq_true, ↓reduceIte]
  exact h n (by omega)

theorem Reads.and {m ts e r} (h : Reads pNot (m + 1) ts e r) (hr : Stop 8 r) :
    Reads pAnd (m + 2) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pAnd, h (n + 1) (by omega), bind, Except.bind]
  exact pAndLoop_stop hr

theorem Reads.or {m ts e r} (h : Reads pAnd (m + 1) ts e r) (hr : Stop 9 r) :
    Reads pOr (m + 2) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pOr, h (n + 1) (by omega), bind, Except.bind]
  exact pOrLoop_stop hr

theorem Reads.cond {m ts e r} (h : Reads pOr (m + 1) ts e r) (hr : Stop 10 r) :
    Reads pCond (m + 2) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pCond, h (n + 1) (by omega), bind, Except.bind]
  exact pCondLoop_stop hr

theorem Reads.expr {m ts e r} (h : Reads pCond m ts e r) : Reads (fun n => pExpr n true) (m + 1) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pExpr, ite_true]
  exact h n (by omega)

theorem Reads.exprNoCond {m ts e r} (h : Reads pOr m ts e r) :
    Reads (fun n => pExpr n false) (m + 1) ts e r := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pExpr]
  exact h n (by omega)

theorem Reads.mono {α : Type} {p : Nat → List TokKind → PR α} {m m' ts a r}
    (h : Reads p m ts a r) (hm : m ≤ m') : Reads p m' ts a r :=
  fun n hn => h n (by omega)

/-- From the unary level to the top: an operand followed by a full stop is
read by every level above. -/
theorem Reads.fromUnary {m ts e r} (h : Reads (fun n => pUnary n true) (m + 1) ts e r)
    (hn : NoNot ts) (hr : Stop 10 r) : Reads (fun n => pExpr n true) (m + 11) ts e r :=
  ((((((((h.pow (hr.mono (by omega))).math2 (hr.mono (by omega))).concat (hr.mono (by omega))).math1
    (hr.mono (by omega))).compare (hr.mono (by omega))).not hn).and (hr.mono (by omega))).or
    (hr.mono (by omega))).cond hr |>.expr

end LeanJinja2
