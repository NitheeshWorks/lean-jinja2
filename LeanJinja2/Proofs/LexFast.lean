import LeanJinja2.RepoImpl.LexFast
import LeanJinja2.RepoImpl.Pretty

/-!
# The in-place lexer is the specification lexer

Each helper of `LexFast.lean` equals its namesake in `Lexer.lean` at
`rest p`; the steps and the loop follow, and `lexFast_eq` states the result:
the compiler's lexer produces exactly `lex`'s tokens, seen through
`Token.light`.
-/

namespace LeanJinja2

open String Cursor

set_option linter.unusedSimpArgs false

namespace LexF

variable {s : Slice}

theorem pre_eq (d : String) (p : s.Pos) : pre d p = Lex.pre d (rest p) := preW_eq p d.toList

theorem signAt_take (l : List Char) : Lex.signAt l = Lex.signAt (l.take 1) := by
  simp only [Lex.signAt, List.take_take, Nat.min_self]

theorem signAt_eq (p : s.Pos) : signAt p = Lex.signAt (rest p) := by
  rw [signAt, takeL_eq, ← signAt_take]

theorem spaceLen_eq (p : s.Pos) : spaceLen p = Lex.spaceLen (rest p) := by
  simp [spaceLen, countWhile_eq, Lex.spaceLen]

theorem newlineLen_take (l : List Char) : newlineLen l = newlineLen (l.take 2) := by
  simp only [newlineLen, List.take_take, Nat.min_self]

theorem newlineLenAt_eq (p : s.Pos) : newlineLenAt p = newlineLen (rest p) := by
  rw [newlineLenAt, takeL_eq, ← newlineLen_take]

theorem opAt_take (l : List Char) : Lex.opAt l = Lex.opAt (l.take 2) := by
  simp only [Lex.opAt, List.take_take, Nat.min_self]

theorem opAt_eq (p : s.Pos) : opAt p = Lex.opAt (rest p) := by
  rw [opAt, takeL_eq, ← opAt_take]


/-- The rewrites that turn a fast helper's body into its specification's. -/
macro "to_spec" : tactic =>
  `(tactic| simp only [pre_eq, peek_eq, rest_advN, rest_adv, spaceLen_eq, newlineLenAt_eq,
    signAt_eq, List.drop_drop, List.tail_drop, List.drop_one])

theorem blockEndAt_eq (cfg : LexConfig) (p : s.Pos) :
    blockEndAt cfg p = Lex.blockEndAt cfg (rest p) := by
  simp only [blockEndAt, Lex.blockEndAt]; to_spec

theorem varEndAt_eq (cfg : LexConfig) (p : s.Pos) :
    varEndAt cfg p = Lex.varEndAt cfg (rest p) := by
  simp only [varEndAt, Lex.varEndAt]; to_spec

theorem commentEndAt_eq (cfg : LexConfig) (p : s.Pos) :
    commentEndAt cfg p = Lex.commentEndAt cfg (rest p) := by
  simp only [commentEndAt, Lex.commentEndAt]; to_spec

theorem rawBeginAt_eq (cfg : LexConfig) (p : s.Pos) :
    rawBeginAt cfg p = Lex.rawBeginAt cfg (rest p) := by
  simp only [rawBeginAt, Lex.rawBeginAt]; to_spec

theorem rawEndAt_eq (cfg : LexConfig) (p : s.Pos) :
    rawEndAt cfg p = Lex.rawEndAt cfg (rest p) := by
  simp only [rawEndAt, Lex.rawEndAt, blockEndAt_eq]; to_spec
  split <;> (try split) <;> (try split) <;> simp_all

theorem lastPre_eq (d : List Char) (n : Nat) : ∀ (p : s.Pos) (i : Nat) (acc : Option Nat),
    lastPre d p n i acc = Lex.lastPre d (rest p) n i acc := by
  induction n with
  | zero => intro p i acc; unfold lastPre Lex.lastPre; simp only [preW_eq]; all_goals (cases rest p <;> rfl)
  | succ n ih =>
    intro p i acc
    unfold lastPre
    by_cases hp : p = s.endPos
    · subst hp; simp only [preW_eq, rest_endPos, ↓reduceDIte]; unfold Lex.lastPre; rfl
    · simp only [hp, ↓reduceDIte, preW_eq, ih]
      conv => rhs; rw [rest_next p hp]
      conv => lhs; rw [rest_next p hp]
      rfl

theorem linePrefixAt_eq (cls : Char → Bool) (d : String) (p : s.Pos) :
    linePrefixAt cls d.toList p = Lex.linePrefixAt cls d (rest p) := by
  unfold linePrefixAt Lex.linePrefixAt
  rw [lastPre_eq, countWhile_eq, Nat.zero_add]
  cases Lex.lastPre d.toList (rest p) _ 0 none with
  | none => rfl
  | some k => simp only [signAt_eq, rest_advN, String.length_toList]

theorem ruleAt_eq (prev : Prev) (p : s.Pos) (rank : Nat) (d : String) :
    ruleAt prev p rank d.toList = Lex.ruleAt prev (rest p) rank d := by
  simp only [ruleAt, Lex.ruleAt, linePrefixAt_eq, preW_eq, String.length_toList]; to_spec; rfl

theorem pick_eq (prev : Prev) (p : s.Pos) (ds : List (Nat × String)) :
    pick prev p (ds.map (fun x => (x.1, x.2.toList))) = Lex.tagAt.pick prev (rest p) ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, pick, Lex.tagAt.pick, ih, ruleAt_eq]
    cases Lex.ruleAt prev (rest p) d.fst d.snd <;> rfl

theorem tagAt_eq (cfg : LexConfig) (prev : Prev) (p : s.Pos) :
    tagAt cfg (ctx cfg).bs (ctx cfg).ord prev p = Lex.tagAt cfg prev (rest p) := by
  have hraw : (if preW p (ctx cfg).bs then rawBeginAt cfg p else none) = rawBeginAt cfg p := by
    split
    · rfl
    · rename_i h
      rw [rawBeginAt_eq]; unfold Lex.rawBeginAt
      rw [preW_eq] at h
      simp [Lex.pre, ctx] at h ⊢
      simp [h]
  unfold tagAt
  rw [hraw]
  simp only [Lex.tagAt, ctx, rawBeginAt_eq, pick_eq]; rfl


theorem pre_cons_false {d : String} {c : Char} (r : List Char)
    (h : d.toList.head?.all (· == c) = false) : Lex.pre d (c :: r) = false := by
  unfold Lex.pre
  cases hd : d.toList with
  | nil => simp [hd] at h
  | cons d0 ds =>
    rw [hd] at h
    simp only [List.head?_cons, Option.all_some] at h
    simp [List.isPrefixOf, h]

theorem pick_none {prev : Prev} {c : Char} (r : List Char) (ds : List (Nat × String))
    (h : ∀ x ∈ ds, Lex.ruleAt prev (c :: r) x.1 x.2 = none) : Lex.tagAt.pick prev (c :: r) ds = none := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [Lex.tagAt.pick]
    rw [h d (by simp)]
    exact ih (fun x hx => h x (by simp [hx]))

theorem lastPre_zero (d l : List Char) (i : Nat) (acc : Option Nat) :
    Lex.lastPre d l 0 i acc = if d.isPrefixOf l then some i else acc := by
  unfold Lex.lastPre; rfl

/-- A line rule cannot start at a character that neither begins its prefix
nor belongs to the run class. -/
theorem linePrefixAt_none {cls : Char → Bool} {d : String} {c : Char} (r : List Char)
    (hc : cls c = false) (hd : d.toList.head?.all (· == c) = false) :
    Lex.linePrefixAt cls d (c :: r) = none := by
  have hp := pre_cons_false r hd
  unfold Lex.pre at hp
  simp [Lex.linePrefixAt, List.takeWhile, hc, lastPre_zero, hp]

theorem mem_beginOrder_ins (le : Nat × String → Nat × String → Bool) (x y : Nat × String)
    (l : List (Nat × String)) :
    x ∈ Lex.beginOrder.ins le y l ↔ x = y ∨ x ∈ l := by
  induction l with
  | nil => simp [Lex.beginOrder.ins]
  | cons z zs ih =>
    unfold Lex.beginOrder.ins
    split
    · simp
    · simp only [List.mem_cons, ih]; exact or_left_comm

theorem mem_beginOrder {cfg : LexConfig} {x : Nat × String} (h : x ∈ Lex.beginOrder cfg) :
    (x.1 = 3 ∨ x.1 = 2) → lineOn cfg = true := by
  have hf : ∀ le (l : List (Nat × String)), x ∈ l.foldr (Lex.beginOrder.ins le) [] → x ∈ l := by
    intro le l; induction l with
    | nil => simp
    | cons y ys ih =>
      intro hx; rw [List.foldr_cons, mem_beginOrder_ins] at hx; simp only [List.mem_cons]
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (ih hx)
  unfold Lex.beginOrder at h
  have hx := hf _ _ h
  intro hr
  cases h1 : cfg.lineStatementPrefix <;> cases h2 : cfg.lineCommentPrefix <;>
    simp only [lineOn, h1, h2, Option.isSome_some, Option.isSome_none, Bool.true_or, Bool.or_true]
  simp [h1, h2] at hx
  rcases hx with rfl | rfl | rfl <;> simp at hr

theorem candOne_eq (o : Option Char) (c : Char) : candOne o c = o.all (· == c) := by
  cases o <;> rfl

theorem isCand_eq (cs : List (Option Char)) (c : Char) :
    isCand cs c = cs.any (fun o => o.all (· == c)) := by
  induction cs with
  | nil => rfl
  | cons o os ih => simp [isCand, ih, candOne_eq]

theorem tagAt_none {cfg : LexConfig} {prev : Prev} {c : Char} (r : List Char)
    (h : isCand (cands cfg) c = false) (hl : (lineOn cfg && prev != .space && isSpace c) = false) :
    Lex.tagAt cfg prev (c :: r) = none := by
  rw [isCand_eq] at h
  simp only [cands, List.any_eq_false, List.mem_map, List.mem_cons] at h
  have hb : Lex.rawBeginAt cfg (c :: r) = none := by
    unfold Lex.rawBeginAt
    rw [pre_cons_false r]
    · rfl
    · have := h _ ⟨cfg.blockStart, Or.inl rfl, rfl⟩
      simpa using this
  simp only [Lex.tagAt, hb]
  apply pick_none
  intro x hx
  have hd : x.2.toList.head?.all (· == c) = false := by
    have := h _ ⟨x.2, Or.inr ⟨x, hx, rfl⟩, rfl⟩
    simpa using this
  have hon := mem_beginOrder hx
  unfold Lex.ruleAt
  split
  · rename_i h3
    split
    · rename_i hpv
      have hc : Lex.isIndent c = false := by
        have h3' : x.1 = 3 := by simpa using h3
        have := hon (Or.inl h3')
        simp only [beq_iff_eq] at hpv
        subst hpv
        cases hi : Lex.isIndent c
        · rfl
        · have : isSpace c = true := by
            simp only [Lex.isIndent, Bool.or_eq_true, beq_iff_eq] at hi
            rcases hi with (rfl | rfl) | rfl <;> decide
          simp_all
      rw [linePrefixAt_none r hc hd]; rfl
    · rfl
  · split
    · rename_i _ h2
      split
      · rename_i hpv
        have hc : Lex.isBlank c = false := by
          have h2' : x.1 = 2 := by simpa using h2
          have := hon (Or.inr h2')
          cases hi : Lex.isBlank c
          · rfl
          · have : isSpace c = true := by
              simp only [Lex.isBlank, Bool.and_eq_true] at hi; exact hi.1
            simp_all
        rw [linePrefixAt_none r hc hd]; rfl
      · rfl
    · rw [pre_cons_false r hd]; rfl

/-- Without line rules, what precedes a position does not matter. -/
theorem tagAt_prev_irrel {cfg : LexConfig} (h : lineOn cfg = false) (prev prev' : Prev) (l : List Char) :
    Lex.tagAt cfg prev l = Lex.tagAt cfg prev' l := by
  unfold Lex.tagAt
  split
  · rfl
  · have : ∀ ds : List (Nat × String), (∀ x ∈ ds, x ∈ Lex.beginOrder cfg) →
        Lex.tagAt.pick prev l ds = Lex.tagAt.pick prev' l ds := by
      intro ds
      induction ds with
      | nil => intro _; rfl
      | cons d ds ih =>
        intro hm
        have hd := mem_beginOrder (hm d (by simp))
        have h3 : d.1 ≠ 3 := fun e => by simp [hd (Or.inl e)] at h
        have h2 : d.1 ≠ 2 := fun e => by simp [hd (Or.inr e)] at h
        have hr : Lex.ruleAt prev l d.1 d.2 = Lex.ruleAt prev' l d.1 d.2 := by
          unfold Lex.ruleAt
          simp [h3, h2]
        simp only [Lex.tagAt.pick, hr, ih (fun x hx => hm x (by simp [hx]))]
    exact this _ (fun x hx => hx)

theorem findTag_eq' (cfg : LexConfig) (prev prev' : Prev) (hpv : lineOn cfg = true → prev' = prev)
    (p : s.Pos) (i : Nat) :
    findTag cfg (ctx cfg) prev' p i =
      match Lex.findTag cfg prev (rest p) i with
      | none => .error (i + (rest p).length)
      | some r => .ok r := by
  induction h : (rest p).length generalizing p i prev prev' with
  | zero =>
    rw [List.length_eq_zero_iff, rest_eq_nil_iff] at h
    subst h; unfold findTag; simp [rest_endPos, Lex.findTag]
  | succ n ih =>
    have hp : p ≠ s.endPos := by
      intro he; subst he; simp [rest_endPos] at h
    have hl : (rest (p.next hp)).length = n := by rw [rest_next p hp] at h; simpa using h
    have hsame : ∀ l, Lex.tagAt cfg prev' l = Lex.tagAt cfg prev l := by
      intro l
      cases hlo : lineOn cfg
      · exact tagAt_prev_irrel hlo _ _ _
      · rw [hpv hlo]
    have hnext : lineOn cfg = true →
        (if (ctx cfg).lc then prevClass (p.get hp) else Prev.text) = prevClass (p.get hp) := by
      intro hlo; simp [ctx, hlo]
    unfold findTag
    simp only [hp, ↓reduceDIte]
    rw [rest_next p hp]
    simp only [Lex.findTag]
    split
    · rw [tagAt_eq, hsame, rest_next p hp]
      cases ht : Lex.tagAt cfg prev (p.get hp :: rest (p.next hp)) with
      | some t => rfl
      | none =>
        simp only [ih _ _ hnext _ _ hl]
        cases Lex.findTag cfg (prevClass (p.get hp)) (rest (p.next hp)) (i + 1) <;> simp; omega
    · rename_i hc
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
      rw [← hsame, tagAt_none _ hc.1 hc.2]
      simp only [ih _ _ hnext _ _ hl]
      cases Lex.findTag cfg (prevClass (p.get hp)) (rest (p.next hp)) (i + 1) <;> simp; omega

theorem findTag_eq (cfg : LexConfig) (prev : Prev) (p : s.Pos) (i : Nat) :
    findTag cfg (ctx cfg) prev p i =
      match Lex.findTag cfg prev (rest p) i with
      | none => .error (i + (rest p).length)
      | some r => .ok r :=
  findTag_eq' cfg prev prev (fun _ => rfl) p i

theorem findMatch_eq {α : Type} (m : s.Pos → Option α) (M : List Char → Option α)
    (hm : ∀ q, m q = M (rest q)) (p : s.Pos) (i : Nat) :
    findMatch m p i = Lex.findMatch M (rest p) i := by
  induction h : (rest p).length generalizing p i with
  | zero =>
    rw [List.length_eq_zero_iff, rest_eq_nil_iff] at h
    subst h; unfold findMatch; simp [rest_endPos, Lex.findMatch]
  | succ n ih =>
    have hp : p ≠ s.endPos := by
      intro he; subst he; simp [rest_endPos] at h
    have hl : (rest (p.next hp)).length = n := by rw [rest_next p hp] at h; simpa using h
    unfold findMatch
    simp only [hp, ↓reduceDIte]
    have hr := rest_next p hp
    rw [hm p]
    conv => rhs; rw [hr]
    simp only [Lex.findMatch]
    rw [← hr]
    split
    · rename_i heq; simp [heq]
    · rename_i heq; rw [ih _ _ hl]; simp [heq]


theorem findMatchC_eq {α : Type} (cand : Char → Bool) (m : s.Pos → Option α)
    (M : List Char → Option α) (hm : ∀ q, m q = M (rest q))
    (hc : ∀ c l, cand c = false → M (c :: l) = none) (p : s.Pos) (i : Nat) :
    findMatchC cand m p i = Lex.findMatch M (rest p) i := by
  rw [← findMatch_eq m M hm]
  induction h : (rest p).length using Nat.strongRecOn generalizing p i with
  | _ n ih =>
  unfold findMatchC findMatch
  by_cases hp : p = s.endPos
  · simp [hp]
  simp only [hp, ↓reduceDIte]
  have hl : (rest (p.next hp)).length < n := by rw [← h]; exact rest_next_length p hp
  split
  · split <;> rename_i heq
    · rfl
    · rw [ih _ hl _ _ rfl]
  · rename_i hn
    have : m p = none := by
      rw [hm, rest_next p hp]; exact hc _ _ (by simpa using hn)
    rw [this, ih _ hl _ _ rfl]

theorem commentEndAt_cand (cfg : LexConfig) (c : Char) (l : List Char)
    (h : commentCand cfg.commentEnd.toList.head? c = false) : Lex.commentEndAt cfg (c :: l) = none := by
  simp only [commentCand, candOne_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold Lex.commentEndAt
  simp [h1, h2, pre_cons_false l h3]

theorem rawEndAt_cand (cfg : LexConfig) (c : Char) (l : List Char)
    (h : candOne cfg.blockStart.toList.head? c = false) : Lex.rawEndAt cfg (c :: l) = none := by
  simp only [candOne_eq] at h
  unfold Lex.rawEndAt
  simp [pre_cons_false l h]

/-! ## Statistics of a run of text, as folds -/

/-- Induction from the right end of a list. -/
@[elab_as_elim]
theorem rev_ind {P : List Char → Prop} (nil : P []) (snoc : ∀ t c, P t → P (t ++ [c])) :
    ∀ l, P l := by
  have h : ∀ r : List Char, P r.reverse := by
    intro r
    induction r with
    | nil => exact nil
    | cons c r ih => simpa using snoc _ c ih
  intro l; simpa using h l.reverse

theorem rstripList_append (t : List Char) (c : Char) :
    rstripList (t ++ [c]) = if isSpace c then rstripList t else t ++ [c] := by
  unfold rstripList
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.dropWhile_cons]
  split <;> simp

theorem rstripList_length_le (t : List Char) : (rstripList t).length ≤ t.length := by
  unfold rstripList
  simp only [List.length_reverse]
  exact Nat.le_trans (List.dropWhile_suffix _).length_le (by simp)

theorem fold_rstrip (t : List Char) :
    t.foldl rstripStep (0, 0) = ((rstripList t).length, t.length - (rstripList t).length) := by
  induction t using rev_ind with
  | nil => rfl
  | snoc t c ih =>
    rw [List.foldl_append, ih, rstripList_append]
    have := rstripList_length_le t
    simp only [List.foldl_cons, List.foldl_nil, rstripStep, List.length_append, List.length_singleton]
    split <;> simp <;> omega

theorem afterLastNewline_go (l : List Char) (i acc : Nat) :
    afterLastNewline.go l i acc = (l.foldl nlStep (i, acc)).2 := by
  induction l generalizing i acc with
  | nil => rfl
  | cons c cs ih => simp only [afterLastNewline.go, ih, List.foldl_cons, nlStep]

theorem fold_nl_fst (l : List Char) (i acc : Nat) : (l.foldl nlStep (i, acc)).1 = i + l.length := by
  induction l generalizing i acc with
  | nil => simp
  | cons c cs ih => simp only [List.foldl_cons, nlStep, ih, List.length_cons]; omega

theorem afterLastNewline_eq (t : List Char) : afterLastNewline t = (t.foldl nlStep (0, 0)).2 :=
  afterLastNewline_go t 0 0

theorem afterLastNewline_append (t : List Char) (c : Char) :
    afterLastNewline (t ++ [c]) = if isNewline c then t.length + 1 else afterLastNewline t := by
  rw [afterLastNewline_eq, afterLastNewline_eq, List.foldl_append]
  have := fold_nl_fst t 0 0
  simp only [List.foldl_cons, List.foldl_nil, nlStep]
  rw [this]; simp

theorem afterLastNewline_le (t : List Char) : afterLastNewline t ≤ t.length := by
  induction t using rev_ind with
  | nil => simp [afterLastNewline_eq]
  | snoc t c ih => rw [afterLastNewline_append]; split <;> simp <;> omega

theorem fold_tailSpace (t : List Char) :
    t.foldl tailSpaceStep true = (t.drop (afterLastNewline t)).all isSpace := by
  induction t using rev_ind with
  | nil => rfl
  | snoc t c ih =>
    rw [List.foldl_append, ih, afterLastNewline_append]
    simp only [List.foldl_cons, List.foldl_nil, tailSpaceStep]
    split
    · simp
    · rw [List.drop_append_of_le_length (afterLastNewline_le t)]
      simp

theorem fold_len (t : List Char) (n : Nat) : t.foldl lenStep n = n + t.length := by
  induction t generalizing n with
  | nil => simp
  | cons c cs ih => simp only [List.foldl_cons, lenStep, ih, List.length_cons]; omega

theorem fold_last (t : List Char) :
    t.foldl (fun _ c => prevClass c) .text = LeanJinja2.prevOf t := by
  induction t using rev_ind with
  | nil => rfl
  | snoc t c ih => simp [LeanJinja2.prevOf, List.foldl_append]

theorem prevOf_eq (p : s.Pos) (n : Nat) :
    prevOf p n = LeanJinja2.prevOf ((rest p).take n) := by
  rw [prevOf, foldTake_eq, fold_last]

theorem head_isNone {α : Type} (l : List α) : l.head?.isNone = l.isEmpty := by
  cases l <;> rfl

theorem lineEndAt_eq (p : s.Pos) : lineEndAt p = Lex.lineEndAt (rest p) := by
  simp only [lineEndAt, Lex.lineEndAt, peek_eq, rest_advN, head_isNone, spaceLen_eq, foldTake_eq,
    ← afterLastNewline_eq]

theorem lineRest_eq (p : s.Pos) : lineRest p = Lex.lineRest (rest p) := by
  simp [lineRest, Lex.lineRest, countWhile_eq]

theorem stripSplit_eq (cfg : LexConfig) (isVar : Bool) (sign : Option Char) (ls : Bool)
    (p : s.Pos) (n : Nat) :
    stripSplit cfg isVar sign ls p n = Lex.stripSplit cfg isVar sign ls ((rest p).take n) := by
  simp only [stripSplit, Lex.stripSplit, foldTake_eq, fold_rstrip, fold_len, fold_tailSpace,
    ← afterLastNewline_eq, Nat.zero_add]
  have hle : ∀ (t : List Char) (a : Nat), (t.drop a).isEmpty = decide (t.length ≤ a) := by
    intro t a; rw [Bool.eq_iff_iff, List.isEmpty_iff, List.drop_eq_nil_iff]; simp
  simp only [hle]


/-! ## Literals -/

/-- Induction on the characters left at `p`: the end, or a character and the
position after it. -/
theorem rest_cases (p : s.Pos) :
    (p = s.endPos ∧ rest p = []) ∨ ∃ h : p ≠ s.endPos, rest p = p.get h :: rest (p.next h) := by
  by_cases h : p = s.endPos
  · exact Or.inl ⟨h, h ▸ rest_endPos⟩
  · exact Or.inr ⟨h, rest_next p h⟩

theorem digitRunGo_eq (base : Nat) (p : s.Pos) (n : Nat) :
    digitRunGo base p n = Lex.digitRun.go (isD base) (rest p) n := by
  induction h : (rest p).length generalizing p n with
  | zero =>
    rw [List.length_eq_zero_iff, rest_eq_nil_iff] at h
    subst h; unfold digitRunGo; simp [rest_endPos, Lex.digitRun.go]
  | succ k ih =>
    have hp : p ≠ s.endPos := by
      intro he; subst he; simp [rest_endPos] at h
    have hl : (rest (p.next hp)).length = k := by rw [rest_next p hp] at h; simpa using h
    unfold digitRunGo
    simp only [hp, ↓reduceDIte]
    rw [rest_next p hp, peek_eq]
    simp only [Lex.digitRun.go]
    split
    · rw [ih _ _ hl]
    · split
      · cases hr : rest (p.next hp) with
        | nil => rfl
        | cons d t =>
          simp only [List.head?_cons]
          split
          · rw [ih _ _ hl, hr]
          · rfl
      · rfl

theorem digitRun_eq (base : Nat) (p : s.Pos) : digitRun base p = Lex.digitRun base (rest p) := by
  unfold digitRun Lex.digitRun
  rw [peek_eq, digitRunGo_eq, rest_adv]
  cases rest p with
  | nil => rfl
  | cons c t => rfl

theorem fracLen_eq (p : s.Pos) : fracLen p = Lex.fracLen (rest p) := by
  unfold fracLen Lex.fracLen
  rw [peek_eq, digitRun_eq, rest_adv]
  cases hr : rest p with
  | nil => rfl
  | cons c t =>
    simp only [List.head?_cons, List.tail_cons]
    by_cases hc : c = '.'
    · subst hc; rfl
    · split
      · rename_i h; cases h; exact absurd rfl hc
      · split
        · rename_i h; cases h; exact absurd rfl hc
        · rfl

theorem expLen_eq (p : s.Pos) : expLen p = Lex.expLen (rest p) := by
  unfold expLen Lex.expLen
  simp only [peek_eq, digitRun_eq, rest_advN, rest_adv]
  cases rest p with
  | nil => rfl
  | cons c t =>
    simp only [List.head?_cons, List.tail_cons]
    cases t with
    | nil => rfl
    | cons d u =>
      simp only [List.head?_cons]
      by_cases h1 : d = '+'
      · subst h1; rfl
      · by_cases h2 : d = '-'
        · subst h2; rfl
        · split <;> simp_all <;> split <;> simp_all

theorem floatAt_eq (p : s.Pos) : floatAt p = Lex.floatAt (rest p) := by
  simp only [floatAt, Lex.floatAt, digitRun_eq, fracLen_eq, expLen_eq, rest_advN]


theorem digitVal_underscore (base : Nat) : (digitVal base '_').isSome = false := by
  simp [digitVal]

/-- Strong induction on the characters left at `p`. -/
theorem rest_induction {P : s.Pos → Prop}
    (h : ∀ p, (∀ q : s.Pos, (rest q).length < (rest p).length → P q) → P p) (p : s.Pos) : P p := by
  have key : ∀ n, ∀ p : s.Pos, (rest p).length ≤ n → P p := by
    intro n
    induction n with
    | zero => intro p hp; exact h p (fun q hq => by omega)
    | succ n ih => intro p hp; exact h p (fun q hq => ih q (by omega))
  exact key _ p (Nat.le_refl _)

theorem rest_next2_length (p : s.Pos) (hp : p ≠ s.endPos) (hq : p.next hp ≠ s.endPos) :
    (rest ((p.next hp).next hq)).length < (rest p).length :=
  Nat.lt_trans (rest_next_length _ hq) (rest_next_length p hp)

theorem prefixedRun_eq (base : Nat) (p : s.Pos) (acc : Nat) :
    prefixedRun base p acc = acc + Lex.prefixedRun base (rest p) := by
  induction p using rest_induction generalizing acc with
  | h p ih =>
  unfold prefixedRun
  by_cases hp : p = s.endPos
  · subst hp; simp [rest_endPos, Lex.prefixedRun]
  simp only [hp, ↓reduceDIte]
  rw [rest_next p hp]
  by_cases hu : p.get hp = '_'
  · rw [hu]
    simp only [beq_self_eq_true, ↓reduceIte]
    by_cases hq : p.next hp = s.endPos
    · simp only [hq, ↓reduceDIte, rest_endPos]
      rw [Lex.prefixedRun.eq_2 base _ _ (fun _ _ _ h => by cases h)]
      simp [digitVal_underscore]
    · simp only [hq, ↓reduceDIte]
      rw [rest_next _ hq, Lex.prefixedRun.eq_1]
      cases hd : (digitVal base ((p.next hp).get hq)).isSome
      · simp [isD, hd]
      · simp only [isD, hd, ↓reduceIte]
        rw [ih _ (rest_next2_length p hp hq)]; omega
  · have hne : (p.get hp == '_') = false := by simpa using hu
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [Lex.prefixedRun.eq_2 base _ _ (fun _ _ h _ => hu h)]
    cases hd : (digitVal base (p.get hp)).isSome
    · simp [isD, hd]
    · simp only [isD, hd, ↓reduceIte]
      rw [ih _ (rest_next_length p hp)]; omega


theorem zeros_eq (p : s.Pos) (acc : Nat) : zeros p acc = acc + Lex.intAt.z (rest p) := by
  induction p using rest_induction generalizing acc with
  | h p ih =>
  unfold zeros
  by_cases hp : p = s.endPos
  · subst hp; simp [rest_endPos, Lex.intAt.z]
  simp only [hp, ↓reduceDIte]
  rw [rest_next p hp]
  by_cases hu : p.get hp = '_'
  · rw [hu]
    simp only [beq_self_eq_true, ↓reduceIte]
    by_cases hq : p.next hp = s.endPos
    · simp only [hq, ↓reduceDIte, rest_endPos]
      rw [Lex.intAt.z.eq_3 _ (by intro r h; simp at h) (by intro r h; simp at h)]
      simp
    · simp only [hq, ↓reduceDIte]
      rw [rest_next _ hq]
      by_cases h0 : (p.next hp).get hq = '0'
      · rw [h0, Lex.intAt.z.eq_1]
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [ih _ (rest_next2_length p hp hq)]; omega
      · have hne : ((p.next hp).get hq == '0') = false := by simpa using h0
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        rw [Lex.intAt.z.eq_3 _ (by intro r h; simp at h; exact h0 h.1)
          (by intro r h; simp at h)]
        simp
  · have hne : (p.get hp == '_') = false := by simpa using hu
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : p.get hp = '0'
    · rw [h0, Lex.intAt.z.eq_2]
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [ih _ (rest_next_length p hp)]; omega
    · have hne0 : (p.get hp == '0') = false := by simpa using h0
      simp only [hne0, Bool.false_eq_true, ↓reduceIte]
      rw [Lex.intAt.z.eq_3 _ (by intro r h; simp at h; exact hu h.1)
        (by intro r h; simp at h; exact h0 h.1)]
      simp

theorem intAt_eq (p : s.Pos) : intAt p = Lex.intAt (rest p) := by
  unfold intAt
  simp only [peek_eq, rest_adv, prefixedRun_eq, zeros_eq, takeL_eq, digitRun_eq, Nat.zero_add]
  cases hr : rest p with
  | nil => rfl
  | cons c0 t =>
    simp only [List.head?_cons, List.tail_cons]
    by_cases h0 : c0 = '0'
    · subst h0
      cases t with
      | nil => rfl
      | cons c cs =>
        simp only [List.head?_cons, List.tail_cons]
        rw [Lex.intAt.eq_1]; rfl
    · have : Lex.intAt (c0 :: t) = if '1' ≤ c0 ∧ c0 ≤ '9' then
          some (Lex.digitRun 10 (c0 :: t), digitsValue 10 (List.take (Lex.digitRun 10 (c0 :: t)) (c0 :: t)))
          else none :=
        Lex.intAt.eq_3 _ _ (fun _ _ h _ => h0 h) (fun h _ => h0 h)
      rw [this]
      split
      · rename_i h; cases h; exact absurd rfl h0
      · rename_i h; cases h; rfl
      · rename_i h; cases h

theorem nameLen_eq (p : s.Pos) : nameLen p = Lex.nameLen (rest p) := by
  simp [nameLen, countWhile_eq, Lex.nameLen]

theorem stringGo_eq (q : Char) (p : s.Pos) (n : Nat) :
    stringGo q p n = Lex.stringAt.go q (rest p) n := by
  induction p using rest_induction generalizing n with
  | h p ih =>
  unfold stringGo
  by_cases hp : p = s.endPos
  · subst hp; simp [rest_endPos, Lex.stringAt.go]
  simp only [hp, ↓reduceDIte]
  rw [rest_next p hp]
  by_cases hb : p.get hp = '\\'
  · rw [hb]
    simp only [beq_self_eq_true, ↓reduceIte]
    by_cases hq : p.next hp = s.endPos
    · simp only [hq, ↓reduceDIte, rest_endPos]
      rw [Lex.stringAt.go.eq_3 _ _ _ _ (by intro _ _ _ h; cases h)]
      split <;> simp [Lex.stringAt.go]
    · simp only [hq, ↓reduceDIte]
      rw [rest_next _ hq, Lex.stringAt.go.eq_2, ih _ (rest_next2_length p hp hq)]
  · have hne : (p.get hp == '\\') = false := by simpa using hb
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [Lex.stringAt.go.eq_3 _ _ _ _ (fun _ _ h _ => hb h)]
    split
    · rfl
    · rw [ih _ (rest_next_length p hp)]

theorem stringAt_eq (p : s.Pos) : stringAt p = Lex.stringAt (rest p) := by
  unfold stringAt Lex.stringAt
  rw [peek_eq]
  cases hr : rest p with
  | nil => rfl
  | cons c t =>
    simp only [List.head?_cons]
    rw [stringGo_eq, rest_adv, hr]; rfl


theorem copyTake_eq (p : s.Pos) (n : Nat) : copyTake p n = String.ofList ((rest p).take n) := by
  rw [← copyTake_toList, String.ofList_toList]

/-! ## Cutting -/

theorem scan_eq {β : Type} (f : β → Char → β) (b : β) (p : s.Pos) (n k : Nat) :
    (scan f b p n k).1 = ((rest p).take n).foldl f b ∧
    (scan f b p n k).2.1 = k + ((rest p).take n).length ∧
    rest (scan f b p n k).2.2 = (rest p).drop n := by
  induction n generalizing p b k with
  | zero => simp [scan]
  | succ n ih =>
    unfold scan
    by_cases hp : p = s.endPos
    · subst hp; simp [rest_endPos]
    · simp only [hp, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := ih (f b (p.get hp)) (p.next hp) (k + 1)
      rw [h1, h2, h3, rest_next p hp]
      simp; omega

/-- A fast cutter agrees with a specification cutter at every position. -/
def CutRel (f : Cut s) (F : List Char → List Token × List Char) : Prop :=
  ∀ p, (f p).1 = (F (rest p)).1.map Token.light ∧ rest (f p).2 = (F (rest p)).2

theorem cut_rel (k : TokKind) (n : Nat) : CutRel (s := s) (cut k n) (Lex.cut k n) := by
  intro p
  obtain ⟨-, h2, h3⟩ := scan_eq (fun u _ => u) () p n 0
  simp only [cut, Lex.cut, h2, h3, List.map, Token.light, Nat.zero_add]
  simp

theorem cutOpt_rel (k : TokKind) (n : Nat) : CutRel (s := s) (cutOpt k n) (Lex.cutOpt k n) := by
  intro p
  unfold cutOpt Lex.cutOpt
  split
  · simp
  · exact cut_rel k n p

theorem cutData_rel (cfg : LexConfig) (n : Nat) :
    CutRel (s := s) (cutData cfg n) (Lex.cutData cfg n) := by
  intro p
  unfold cutData Lex.cutData Lex.cutOpt
  split
  · simp
  · obtain ⟨h1, h2, h3⟩ := scan_eq (normStep cfg.newlineSequence) ("", false) p n 0
    simp only [h1, h2, h3, Lex.cut, List.map, Token.light, Nat.zero_add, normStep_fold]
    simp

theorem seq_rel {a b : Cut s} {A B : List Char → List Token × List Char}
    (ha : CutRel a A) (hb : CutRel b B) : CutRel (seq a b) (Lex.seq A B) := by
  intro p
  obtain ⟨ha1, ha2⟩ := ha p
  obtain ⟨hb1, hb2⟩ := hb (a p).2
  simp only [seq, Lex.seq]
  rw [ha2] at hb1 hb2
  rw [ha1, hb1, hb2]
  simp

/-- A fast step agrees with a specification step: the same error, or the
same tokens (seen through `Token.light`), mode and remaining input. -/
def RelStep (x : Except LexError (List TokL × LexMode × s.Pos))
    (y : Except LexError (List Token × LexMode × List Char)) : Prop :=
  match x, y with
  | .error e, .error e' => e = e'
  | .ok (ts, m, q), .ok (ts', m', r) => ts = ts'.map Token.light ∧ m = m' ∧ rest q = r
  | _, _ => False

theorem emit_rel {f : Cut s} {F : List Char → List Token × List Char} (h : CutRel f F)
    (m : LexMode) (p : s.Pos) : RelStep (emit f m p) (Lex.emit F m (rest p)) := by
  obtain ⟨h1, h2⟩ := h p
  simp only [emit, Lex.emit, RelStep]
  simp [h1, h2]

theorem error_rel (e : LexError) :
    RelStep (s := s) (.error e) (.error e) := rfl

/-- Prove `CutRel` for a cutter built from `seq`, `cut`, `cutOpt`, `cutData`. -/
macro "cut_rel_tac" : tactic =>
  `(tactic| repeat' (first | apply seq_rel | apply cut_rel | apply cutOpt_rel | apply cutData_rel))


theorem stringGo_le (q : Char) : ∀ (cs : List Char) (k m : Nat),
    Lex.stringAt.go q cs k = some m → m ≤ k + cs.length := by
  intro cs
  induction h : cs.length using Nat.strongRecOn generalizing cs with
  | _ n ih =>
  intro k m hg
  match cs with
  | [] => simp [Lex.stringAt.go] at hg
  | c :: r =>
    simp only [List.length_cons] at h
    by_cases hc : c = '\\' ∧ r ≠ []
    · obtain ⟨rfl, hr⟩ := hc
      match r, hr with
      | d :: r', _ =>
        rw [Lex.stringAt.go.eq_2] at hg
        have := ih r'.length (by simp at h; omega) r' rfl _ _ hg
        simp at h; omega
    · rw [Lex.stringAt.go.eq_3 _ _ _ _ (fun _ _ h1 h2 => hc ⟨h1, by simp [h2]⟩)] at hg
      split at hg
      · cases hg; omega
      · have := ih r.length (by omega) r rfl _ _ hg
        omega

theorem stringAt_le {l : List Char} {n : Nat} (h : Lex.stringAt l = some n) : n ≤ l.length := by
  unfold Lex.stringAt at h
  split at h
  · split at h
    · have := stringGo_le _ _ _ _ h; simp; omega
    · cases h
  · cases h

theorem strValue_eq (cfg : LexConfig) {p : s.Pos} {n : Nat} (h : Lex.stringAt (rest p) = some n) :
    strValue cfg p n = Lex.strValue cfg (rest p) n := by
  have hle := stringAt_le h
  unfold strValue Lex.strValue
  rw [Lex.unescF_eq, rest_startPos, String.copy_toSlice, foldTake_eq, normStep_fold,
    String.toList_ofList, rest_adv]
  have hl : (((rest p).take n).drop 1).dropLast = ((rest p).tail.take (n - 2)) := by
    rw [List.drop_take, List.dropLast_eq_take, List.take_take, List.length_take,
      List.length_drop, List.drop_one]
    congr 1; omega
  rw [hl]
  cases Lex.unescapeStr _ <;> simp [Except.map]

/-! ## Steps -/

theorem stepRoot_rel (cfg : LexConfig) (ls : Prev) (p : s.Pos) (pos : Nat) :
    RelStep (stepRoot cfg (ctx cfg) ls p pos) (Lex.stepRoot cfg ls (rest p) pos) := by
  unfold stepRoot Lex.stepRoot
  rw [findTag_eq]
  cases Lex.findTag cfg ls (rest p) 0 with
  | none =>
    simp only [Nat.zero_add]
    exact emit_rel (cutData_rel cfg _) _ _
  | some r =>
    obtain ⟨i, t⟩ := r
    simp only [stripSplit_eq]
    cases t with
    | var n sg => exact emit_rel (by cut_rel_tac) _ _
    | block n sg => exact emit_rel (by cut_rel_tac) _ _
    | lineStmt n sg => exact emit_rel (by cut_rel_tac) _ _
    | lineComment n sg =>
      simp only [lineRest_eq, rest_advN, prevOf_eq]
      exact emit_rel (by cut_rel_tac) _ _
    | comment n sg =>
      simp only [findMatchC_eq (commentCand cfg.commentEnd.toList.head?) (commentEndAt cfg) (Lex.commentEndAt cfg)
          (commentEndAt_eq cfg) (commentEndAt_cand cfg),
        rest_advN, prevOf_eq]
      cases Lex.findMatch (Lex.commentEndAt cfg) (List.drop (i + n) (rest p)) 0 with
      | none => rfl
      | some r => exact emit_rel (by cut_rel_tac) _ _
    | raw n sg =>
      simp only [findMatchC_eq (candOne cfg.blockStart.toList.head?) (rawEndAt cfg) (Lex.rawEndAt cfg) (rawEndAt_eq cfg)
          (rawEndAt_cand cfg),
        rest_advN, prevOf_eq, stripSplit_eq]
      cases Lex.findMatch (Lex.rawEndAt cfg) (List.drop (i + n) (rest p)) 0 with
      | none => rfl
      | some r =>
        obtain ⟨j, e, esign⟩ := r
        exact emit_rel (by cut_rel_tac) _ _


theorem stepTag_rel (cfg : LexConfig) (k : TagKind) (st : List Char) (ad : Bool) (p : s.Pos)
    (pos : Nat) : RelStep (stepTag cfg k st ad p pos) (Lex.stepTag cfg k st ad (rest p) pos) := by
  unfold stepTag Lex.stepTag
  simp only [blockEndAt_eq, varEndAt_eq, lineEndAt_eq, spaceLen_eq, floatAt_eq, intAt_eq, nameLen_eq,
    peek_eq, copyTake_eq, takeL_eq, stringAt_eq, opAt_eq, prevOf_eq, List.headD_eq_head?_getD]
  cases k <;>
  repeat' (first
    | with_reducible refine emit_rel ?_ _ _
    | with_reducible exact error_rel _
    | with_reducible exact cut_rel _ _
    | rw [strValue_eq cfg (by assumption)]
    | (split <;> (try (rename_i heq; simp only [heq, ↓reduceIte]))))
  -- the bracket-stack update is split separately on each side: join the two
  all_goals
    rename_i hA _ _ hB
    have hE := hA.symm.trans hB
    cases hE
    all_goals first
      | exact error_rel _
      | exact emit_rel (cut_rel _ _) _ _

theorem closeLine_rel {x : Except LexError (List TokL × LexMode × s.Pos)}
    {y : Except LexError (List Token × LexMode × List Char)} (h : RelStep x y) :
    RelStep (closeLine x) (Lex.closeLine y) := by
  cases x with
  | error e => cases y with
    | error e' => exact h
    | ok _ => simp [RelStep] at h
  | ok a => cases y with
    | error _ => simp [RelStep] at h
    | ok b =>
      obtain ⟨ts, m, q⟩ := a
      obtain ⟨ts', m', r⟩ := b
      simp only [RelStep] at h
      obtain ⟨rfl, rfl, hq⟩ := h
      simp only [closeLine, Lex.closeLine, peek_eq, head_isNone, hq]
      split <;> simp [RelStep, hq, Token.light]

theorem step_rel (cfg : LexConfig) (m : LexMode) (p : s.Pos) (pos : Nat) :
    RelStep (step cfg (ctx cfg) m p pos) (Lex.step cfg m (rest p) pos) := by
  apply closeLine_rel
  cases m with
  | root ls => exact stepRoot_rel cfg ls p pos
  | tag k st ad => exact stepTag_rel cfg k st ad p pos

theorem consumed_light (ts : List Token) : consumed (ts.map Token.light) = Lex.consumed ts := by
  simp only [consumed, Lex.consumed, List.foldl_map, Token.light]

theorem loop_eq (cfg : LexConfig) : ∀ (fuel : Nat) (m : LexMode) (p : s.Pos) (pos : Nat)
    (acc : List Token),
    loop cfg (ctx cfg) fuel m p pos (acc.map Token.light) =
      (Lex.loop cfg fuel m (rest p) pos acc).map (·.map Token.light) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m p pos acc
    unfold loop
    by_cases hp : p = s.endPos
    · subst hp; simp [rest_endPos, Lex.loop, Except.map, List.map_reverse]
    · rw [rest_next p hp]; simp [hp, Lex.loop, Except.map]
  | succ fuel ih =>
    intro m p pos acc
    unfold loop
    by_cases hp : p = s.endPos
    · subst hp; simp [rest_endPos, Lex.loop, Except.map, List.map_reverse]
    · simp only [hp, ↓reduceIte]
      have hr := step_rel cfg m p pos
      obtain ⟨c, cs, hcs⟩ : ∃ c cs, rest p = c :: cs := ⟨_, _, rest_next p hp⟩
      rw [hcs] at hr ⊢
      simp only [Lex.loop]
      cases hx : step cfg (ctx cfg) m p pos with
      | error e =>
        cases hy : Lex.step cfg m (c :: cs) pos with
        | error e' => rw [hx, hy] at hr; simp only [RelStep] at hr; subst hr; rfl
        | ok y => rw [hx, hy] at hr; simp only [RelStep] at hr
      | ok x =>
        obtain ⟨ts, m', q⟩ := x
        cases hy : Lex.step cfg m (c :: cs) pos with
        | error e' => rw [hx, hy] at hr; simp only [RelStep] at hr
        | ok y =>
          obtain ⟨ts', m'', r⟩ := y
          rw [hx, hy] at hr
          simp only [RelStep] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          simp only
          rw [consumed_light, ← List.map_reverse, ← List.map_append, ih]

/-- The trailing newline depends on the last two characters only. -/
theorem trailingNewlineLen_drop (cfg : LexConfig) (l : List Char) :
    Lex.trailingNewlineLen cfg (l.drop (l.length - 2)) = Lex.trailingNewlineLen cfg l := by
  unfold Lex.trailingNewlineLen
  have h : l.length - (l.length - 2) - 2 = 0 := by omega
  simp only [List.take_reverse, List.length_drop, List.drop_drop, h, Nat.add_zero]

theorem trailingNewlineLen_le (cfg : LexConfig) (l : List Char) :
    Lex.trailingNewlineLen cfg l ≤ l.length := by
  unfold Lex.trailingNewlineLen
  split
  · omega
  · generalize ht : l.reverse.take 2 = t
    have hlen : t.length = min 2 l.length := by rw [← ht, List.length_take, List.length_reverse]
    split <;> simp_all <;> omega

end LexF

/-- The compiler's lexer is `lex`: the same tokens, seen through
`Token.light` (kind and length), or the same error. -/
theorem lexFast_eq (cfg : LexConfig) (src : String) :
    lexFast cfg src = (lex cfg src).map (·.map Token.light) := by
  unfold lexFast lex lexList
  have hk : Lex.trailingNewlineLen cfg (src.takeEnd 2).copy.toList =
      Lex.trailingNewlineLen cfg src.toList := by
    rw [String.toList_copy_takeEnd, LexF.trailingNewlineLen_drop]
  generalize Lex.trailingNewlineLen cfg (src.takeEnd 2).copy.toList = k' at *
  subst hk
  generalize hK : Lex.trailingNewlineLen cfg src.toList = k
  have hkle : k ≤ src.toList.length := hK ▸ LexF.trailingNewlineLen_le cfg src.toList
  have hstart : Cursor.rest (src.dropEnd k).startPos = src.toList.take (src.toList.length - k) := by
    rw [Cursor.rest_startPos, String.toList_copy_dropEnd]
  have hfuel : (src.toList.take (src.toList.length - k)).length + 1 = src.length - k + 1 := by
    simp only [List.length_take, String.length_toList]; omega
  have := LexF.loop_eq cfg (src.length - k + 1) (.root .line) (src.dropEnd k).startPos 0 []
  simp only [List.map_nil] at this
  simp only []
  rw [this, hstart, hfuel]
  cases Lex.loop cfg (src.length - k + 1) (.root .line) (src.toList.take (src.toList.length - k)) 0 [] with
  | error e => rfl
  | ok ts =>
    simp only [Except.map, List.map_append]
    split
    · rfl
    · simp [Token.light]; omega

theorem significantL_light (ts : List Token) : significantL (ts.map Token.light) = significant ts := by
  simp [significantL, significant, List.filter_map, Function.comp_def, Token.light]

/-- `parse`, which lexes in place, is the lexer specification followed by
the parser. -/
theorem parse_eq (cfg : LexConfig) (src : String) :
    parse cfg src =
      match lex cfg src with
      | .error e => .error ⟨e.msg, 0⟩
      | .ok ts => parseTokens (significant ts) := by
  unfold parse
  rw [lexFast_eq]
  cases lex cfg src with
  | error e => rfl
  | ok ts => simp [Except.map, significantL_light]

end LeanJinja2
