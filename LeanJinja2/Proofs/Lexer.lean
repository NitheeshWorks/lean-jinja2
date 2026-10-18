import LeanJinja2.RepoImpl.Lexer

namespace LeanJinja2
namespace Lex

/-- A cutter splits its input: the emitted tokens print to a prefix, the
remainder is the rest. -/
def Splits (f : List Char → List Token × List Char) : Prop :=
  ∀ l, Token.printList (f l).1 ++ (f l).2 = l

theorem splits_cut (k : TokKind) (n : Nat) : Splits (cut k n) := by
  intro l; simp [cut, Token.printList]

theorem splits_cutOpt (k : TokKind) (n : Nat) : Splits (cutOpt k n) := by
  intro l; unfold cutOpt; split
  · simp [Token.printList]
  · exact splits_cut k n l

theorem splits_cutData (cfg : LexConfig) (n : Nat) : Splits (cutData cfg n) := by
  intro l; exact splits_cutOpt _ n l

theorem splits_seq {a b : List Char → List Token × List Char} (ha : Splits a) (hb : Splits b) :
    Splits (seq a b) := by
  intro l
  simp only [seq, Token.printList, List.flatMap_append, List.append_assoc]
  have := hb (a l).2
  simp only [Token.printList] at this
  rw [this]; exact ha l

theorem emit_split {f : List Char → List Token × List Char} (hf : Splits f) {m : LexMode}
    {l : List Char} {ts m' r} (h : emit f m l = .ok (ts, m', r)) : Token.printList ts ++ r = l := by
  simp only [emit, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact hf l

/-- Prove `Splits f` for a cutter built from `seq`, `cut`, `cutOpt`, `cutData`. -/
macro "splits_tac" : tactic =>
  `(tactic| repeat' (first | apply splits_seq | apply splits_cut | apply splits_cutOpt | apply splits_cutData))

theorem stepRoot_split {cfg ls l pos ts m r} (h : stepRoot cfg ls l pos = .ok (ts, m, r)) :
    Token.printList ts ++ r = l := by
  unfold stepRoot at h
  dsimp only at h
  repeat' (first | exact emit_split (by splits_tac) h | (cases h; done) | split at h)

theorem stepTag_split {cfg k st ad l pos ts m r} (h : stepTag cfg k st ad l pos = .ok (ts, m, r)) :
    Token.printList ts ++ r = l := by
  unfold stepTag at h
  dsimp only at h
  repeat' (first | exact emit_split (by splits_tac) h | (cases h; done) | split at h)

theorem step_split {cfg m l pos ts m' r} (h : step cfg m l pos = .ok (ts, m', r)) :
    Token.printList ts ++ r = l := by
  unfold step at h
  split at h
  · exact stepRoot_split h
  · exact stepTag_split h

theorem loop_print {cfg} : ∀ fuel m l pos ts, loop cfg fuel m l pos = .ok ts → Token.printList ts = l
  | _, _, [], _, ts, h => by simp [loop] at h; subst h; rfl
  | 0, _, _ :: _, _, _, h => by simp [loop] at h
  | fuel + 1, m, c :: cs, pos, ts, h => by
    simp only [loop] at h
    split at h
    · cases h
    · rename_i ts1 m' r hs
      split at h
      · cases h
      · rename_i us hl
        cases h
        have h1 := step_split hs
        have h2 := loop_print fuel m' r _ us hl
        simp only [Token.printList, List.flatMap_append] at h1 h2 ⊢
        rw [h2]; exact h1

theorem lexList_print {cfg l ts} (h : lexList cfg l = .ok ts) : Token.printList ts = l := by
  unfold lexList at h
  dsimp only at h
  split at h
  · cases h
  · rename_i us hl
    cases h
    have := loop_print _ _ _ _ _ hl
    simp only [Token.printList, List.flatMap_append] at this ⊢
    rw [this]
    split
    · rename_i hk
      simp [hk]
    · simp

end Lex

/-- `lex_print_roundtrip`: lexing loses nothing; the token stream prints back
to exactly the source it came from, for every configuration. -/
theorem lex_print_roundtrip (cfg : LexConfig) (s : String) (ts : List Token)
    (h : lex cfg s = .ok ts) : Token.print ts = s := by
  unfold Token.print
  rw [Lex.lexList_print h]
  simp

end LeanJinja2
