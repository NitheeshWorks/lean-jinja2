import LeanJinja2.Proofs.Roundtrip.Steps

/-!
# Runs of lexer steps

`Run m l ts m' r`: from mode `m` on input `l`, the lexer takes steps that
emit `ts` and leave it in mode `m'` with `r` still to read. A run to the end
of the input is what `Lex.loop` computes.
-/

namespace LeanJinja2

open Lex

set_option linter.unusedSimpArgs false

inductive Run : LexMode → List Char → List Token → LexMode → List Char → Prop
  | refl (m : LexMode) (l : List Char) : Run m l [] m l
  | cons {m l ts m1 r1 us m2 r2} : (∀ pos, Lex.step dcfg m l pos = .ok (ts, m1, r1)) → r1.length < l.length →
      Run m1 r1 us m2 r2 → Run m l (ts ++ us) m2 r2

theorem Run.trans {m l ts m1 l1 us m2 l2} (h1 : Run m l ts m1 l1) (h2 : Run m1 l1 us m2 l2) :
    Run m l (ts ++ us) m2 l2 := by
  induction h1 with
  | refl => simpa using h2
  | cons hs hl _ ih => rw [List.append_assoc]; exact Run.cons hs hl (ih h2)

theorem Run.one {m l ts m1 r1} (hs : ∀ pos, Lex.step dcfg m l pos = .ok (ts, m1, r1)) (hl : r1.length < l.length) :
    Run m l ts m1 r1 := by
  simpa using Run.cons hs hl (Run.refl m1 r1)

theorem Run.loop {m l ts m'} (h : Run m l ts m' []) :
    ∀ fuel pos acc, l.length ≤ fuel → loop dcfg fuel m l pos acc = .ok (acc.reverse ++ ts) := by
  generalize hr : ([] : List Char) = r at h
  induction h with
  | refl m l => intro fuel pos acc _; subst hr; cases fuel <;> simp [Lex.loop]
  | @cons m l ts m1 r1 us m2 r2 hs hl _ ih =>
    intro fuel pos acc hf
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, l = c :: cs := by
      cases l with
      | nil => simp at hl
      | cons c cs => exact ⟨c, cs, rfl⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have := ih hr f (pos + consumed ts) (ts.reverse ++ acc) (by simp at hl hf; omega)
    simp only [List.reverse_append, List.reverse_reverse, List.append_assoc] at this
    simp [Lex.loop, hs pos, this]

/-- Input that does not start with whitespace. -/
def NoLead (l : List Char) : Prop := ∀ c, l.head? = some c → isSpace c = false

theorem significant_append (a b : List Token) : significant (a ++ b) = significant a ++ significant b := by
  simp [significant, List.filter_append]

/-! ## Inside a tag -/

/-- A token's printed text inside a tag, without the separating space. -/
def innerText : TokKind → List Char
  | .name s => s.toList
  | .int n => natDigits n
  | .float m s => floatText m s
  | .str s => strText s
  | .op o => o.text.toList
  | _ => []

theorem tokText_inner {k : TokKind} (hk : InnerTok k) : Pretty.tokText k = innerText k ++ [' '] := by
  cases k <;> simp_all [InnerTok, Pretty.tokText, innerText, floatText, strText]

theorem innerText_head {k : TokKind} (hk : InnerTok k) : ∃ c cs, innerText k = c :: cs ∧ isSpace c = false := by
  cases k with
  | name s =>
    obtain ⟨c, cs, hl, hc, -⟩ := hk
    exact ⟨c, cs, hl, ident_not_space hc⟩
  | int n =>
    cases h : natDigits n with
    | nil => exact absurd h (natDigits_ne_nil n)
    | cons d ds =>
      exact ⟨d, ds, by simp [innerText, h], dig_not_space (natDigits_dig n d (by rw [h]; simp))⟩
  | float m s =>
    cases h : natDigits m with
    | nil => exact absurd h (natDigits_ne_nil m)
    | cons d ds =>
      exact ⟨d, ds ++ 'e' :: '-' :: natDigits s, by simp [innerText, floatText, h], dig_not_space (natDigits_dig m d (by rw [h]; simp))⟩
  | str s => exact ⟨_, _, rfl, by decide⟩
  | op o => cases o <;> exact ⟨_, _, rfl, by decide⟩
  | _ => simp [InnerTok] at hk

/-- A tag step that leaves input, or does not leave an open line statement,
is the lexer's step. -/
theorem step_tag {k : TagKind} {st : List Char} {ad : Bool} {l : List Char} {pos : Nat} {ts m r}
    (h : stepTag dcfg k st ad l pos = .ok (ts, m, r)) (hm : r ≠ [] ∨ m.openLine = false) :
    Lex.step dcfg (.tag k st ad) l pos = .ok (ts, m, r) := by
  simp only [Lex.step, h, closeLine]
  rcases hm with hm | hm <;> simp [hm]

theorem inner_first {k : TokKind} (hk : InnerTok k) {st st' : List Char} (hs : stackStep st k = some st')
    (kd : TagKind) (rest : List Char) : ∃ ad, ∀ pos,
    Lex.step dcfg (.tag kd st false) (innerText k ++ ' ' :: rest) pos =
      .ok ([⟨k, innerText k⟩], .tag kd st' ad, ' ' :: rest) := by
  cases k with
  | name s =>
    simp [stackStep] at hs; subst hs
    exact ⟨false, fun pos => step_tag (by simpa [innerText] using name_step hk kd st rest pos) (Or.inl (by simp))⟩
  | int n =>
    simp [stackStep] at hs; subst hs
    exact ⟨false, fun pos => step_tag (by simpa [innerText] using int_step n kd st rest pos) (Or.inl (by simp))⟩
  | float m s =>
    simp [stackStep] at hs; subst hs
    exact ⟨false, fun pos => step_tag (by simpa [innerText] using float_step m s kd st rest pos) (Or.inl (by simp))⟩
  | str s =>
    simp [stackStep] at hs; subst hs
    exact ⟨false, fun pos => step_tag (by simpa [innerText] using str_step s kd st rest pos) (Or.inl (by simp))⟩
  | op o => exact ⟨_, fun pos => step_tag (by simpa [innerText] using op_step o kd st st' hs rest pos) (Or.inl (by simp))⟩
  | _ => simp [InnerTok] at hk

theorem inner_run : ∀ (ks : List TokKind) (st st' : List Char), InnerAll ks → stackAfter st ks = some st' →
    ∀ (kd : TagKind), kd ≠ .line → ∀ (rest : List Char), NoLead rest →
    ∃ ts, Run (.tag kd st false) (Pretty.render ks ++ rest) ts (.tag kd st' false) rest ∧ significant ts = ks
  | [], st, st', _, h, kd, _, rest, _ => by
    simp [stackAfter] at h; subst h
    exact ⟨[], by simpa [Pretty.render] using Run.refl _ rest, rfl⟩
  | k :: ks, st, st', hin, h, kd, hkd, rest, hr => by
    simp only [innerAll_cons] at hin
    simp only [stackAfter_cons] at h
    cases hs : stackStep st k with
    | none => simp [hs] at h
    | some s1 =>
      simp only [hs, Option.bind_some] at h
      have hnl : NoLead (Pretty.render ks ++ rest) := by
        cases ks with
        | nil => simpa [Pretty.render] using hr
        | cons k' ks' =>
          have hk' := (innerAll_cons.mp hin.2).1
          obtain ⟨c, cs, hc, hsp⟩ := innerText_head hk'
          intro x hx
          simp [Pretty.render, List.flatMap_cons, tokText_inner hk', hc] at hx
          subst hx; exact hsp
      obtain ⟨ts, hrun, hsig⟩ := inner_run ks s1 st' hin.2 h kd hkd rest hr
      obtain ⟨ad, hfirst⟩ := inner_first hin.1 hs kd (Pretty.render ks ++ rest)
      obtain ⟨c, cs, hc, -⟩ := innerText_head hin.1
      have hws : ∀ pos, Lex.step dcfg (.tag kd s1 ad) (' ' :: (Pretty.render ks ++ rest)) pos =
          .ok ([⟨.ws, [' ']⟩], .tag kd s1 false, Pretty.render ks ++ rest) := fun pos => by
        exact step_tag (ws_step kd hkd s1 ad hnl pos) (Or.inr (by cases kd <;> simp_all [LexMode.openLine]))
      have hrender : Pretty.render (k :: ks) ++ rest = innerText k ++ ' ' :: (Pretty.render ks ++ rest) := by
        simp [Pretty.render, List.flatMap_cons, tokText_inner hin.1]
      refine ⟨[⟨k, innerText k⟩] ++ ([⟨.ws, [' ']⟩] ++ ts), ?_, ?_⟩
      · rw [hrender]
        refine Run.cons hfirst (by simp [hc]; omega) (Run.cons hws (by simp) hrun)
      · have hki : k.ignored = false := by cases k <;> simp_all [InnerTok, TokKind.ignored]
        rw [significant_append, significant_append, hsig]
        simp [significant, hki, show TokKind.ws.ignored = true from rfl]

end LeanJinja2
