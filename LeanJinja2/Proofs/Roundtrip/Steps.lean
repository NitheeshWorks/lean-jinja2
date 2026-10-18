import LeanJinja2.Proofs.Roundtrip.Tokens
import LeanJinja2.Proofs.Lexer

/-!
# One lexer step per printed token

With the default delimiters, the lexer reads each printed token back in one
step, then the separating space in another.
-/

namespace LeanJinja2

open Lex

set_option linter.unusedSimpArgs false

/-- The default configuration `parse` uses. -/
abbrev dcfg : LexConfig := {}

theorem ite_t {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
theorem ite_f {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬c) : (if c then a else b) = b := by simp [h]

/-! ## Characters -/

theorem ident_not_space {c : Char} (h : isIdentChar c = true) : isSpace c = false := by
  unfold isIdentChar at h
  cases hs : isSpace c
  · rfl
  · exfalso
    simp only [hs, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
    unfold isSpace at hs
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, Char.ext_iff,
      UInt32.le_iff_toNat_le] at hs
    simp only [Char.isAlphanum, Char.isAlpha, Char.isDigit, Char.isUpper, Char.isLower, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, Char.ext_iff, UInt32.le_iff_toNat_le] at h
    simp only [← UInt32.toNat_inj, UInt32.reduceToNat, Char.toNat_val, Char.reduceToNat] at hs h
    omega

/-- Facts about a character, by its code point. -/
theorem char_eq_iff {c d : Char} : c = d ↔ c.toNat = d.toNat := by
  constructor
  · rintro rfl; rfl
  · intro h; exact Char.ext (UInt32.toNat_inj.mp h)

theorem char_le_iff {c d : Char} : c ≤ d ↔ c.toNat ≤ d.toNat := Iff.rfl

/-- An ASCII digit. -/
def IsDig (c : Char) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57

theorem isDigit_false_iff {c : Char} : c.isDigit = false ↔ ¬ IsDig c := by
  simp only [Char.isDigit, IsDig, Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt32.le_iff_toNat_le,
    UInt32.reduceToNat, Char.toNat_val, Char.reduceToNat]
  omega

theorem digitVal_dig {c : Char} (h : IsDig c) : digitVal 10 c = some (c.toNat - 48) := by
  simp only [IsDig] at h
  unfold digitVal
  simp only [char_le_iff, Char.reduceToNat]
  rw [ite_t h]
  simp only
  rw [ite_t (by omega)]

theorem digitVal_nondig {c : Char} (h : ¬ IsDig c) : digitVal 10 c = none := by
  simp only [IsDig] at h
  unfold digitVal
  simp only [char_le_iff, Char.reduceToNat]
  rw [ite_f h]
  by_cases h2 : 97 ≤ c.toNat ∧ c.toNat ≤ 102
  · rw [ite_t h2]; simp only; rw [ite_f (by omega)]
  · rw [ite_f h2]
    by_cases h3 : 65 ≤ c.toNat ∧ c.toNat ≤ 70
    · rw [ite_t h3]; simp only; rw [ite_f (by omega)]
    · rw [ite_f h3]

theorem dig_ne {c : Char} (h : IsDig c) (d : Char) (hd : ¬ IsDig d) : c ≠ d := by
  rintro rfl; exact hd h

theorem dig_not_space {c : Char} (h : IsDig c) : isSpace c = false := by
  simp only [IsDig] at h
  unfold isSpace
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, char_eq_iff, Char.reduceToNat,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt32.le_iff_toNat_le, UInt32.reduceToNat, Char.toNat_val]
  omega

theorem digChar_toNat {k : Nat} (hk : k < 10) : (Char.ofNat (48 + k)).toNat = 48 + k := by
  obtain h | h | h | h | h | h | h | h | h | h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
    k = 8 ∨ k = 9 := by omega
  all_goals (subst h; rfl)

theorem natDigits_eq (n : Nat) :
    natDigits n = if n < 10 then [Char.ofNat (48 + n)] else natDigits (n / 10) ++ [Char.ofNat (48 + n % 10)] := by
  rw [natDigits]; split <;> simp_all

theorem natDigits_dig (n : Nat) : ∀ c ∈ natDigits n, IsDig c := by
  rw [natDigits_eq]
  split
  · intro c hc
    simp at hc; subst hc
    simp only [IsDig, digChar_toNat (by omega : n < 10)]; omega
  · intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact natDigits_dig (n / 10) c hc
    · simp only [IsDig, digChar_toNat (Nat.mod_lt n (by omega))]; omega
termination_by n
decreasing_by omega

theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  rw [natDigits_eq]; split <;> simp

theorem natDigits_zero : natDigits 0 = ['0'] := by rw [natDigits_eq]; rfl

theorem natDigits_head (n : Nat) (hn : 0 < n) : ∃ d ds, natDigits n = d :: ds ∧ 49 ≤ d.toNat := by
  rw [natDigits_eq]
  split
  · exact ⟨_, [], rfl, by rw [digChar_toNat (by omega)]; omega⟩
  · obtain ⟨d, ds, h, hd⟩ := natDigits_head (n / 10) (by omega)
    exact ⟨d, ds ++ [Char.ofNat (48 + n % 10)], by rw [h]; rfl, hd⟩
termination_by n
decreasing_by omega

theorem digitsValue_snoc (l : List Char) (c : Char) (hc : IsDig c) :
    digitsValue 10 (l ++ [c]) = digitsValue 10 l * 10 + (c.toNat - 48) := by
  have hne : c ≠ '_' := by
    simp only [IsDig] at hc
    simp only [ne_eq, char_eq_iff, Char.reduceToNat]; omega
  simp [digitsValue, List.foldl_append, hne, digitVal_dig hc]

theorem digitsValue_natDigits (n : Nat) : digitsValue 10 (natDigits n) = n := by
  rw [natDigits_eq]
  split
  · have := digitsValue_snoc [] (Char.ofNat (48 + n))
      (by simp only [IsDig, digChar_toNat (by omega : n < 10)]; omega)
    simp only [List.nil_append] at this
    rw [this, digChar_toNat (by omega)]
    simp [digitsValue]
  · rw [digitsValue_snoc _ _ (by simp only [IsDig, digChar_toNat (Nat.mod_lt n (by omega))]; omega),
      digitsValue_natDigits (n / 10), digChar_toNat (Nat.mod_lt n (by omega))]
    omega
termination_by n
decreasing_by omega

/-! ## The scanners on printed tokens -/

theorem digitRun_go (ds : List Char) (hd : ∀ c ∈ ds, IsDig c) (c : Char) (hc : ¬ IsDig c) (hu : c ≠ '_')
    (r : List Char) (n : Nat) : digitRun.go (fun c => (digitVal 10 c).isSome) (ds ++ c :: r) n = n + ds.length := by
  induction ds generalizing n with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    rw [digitRun.go.eq_def]
    simp [digitVal_nondig hc, hu]
  | cons d ds ih =>
    rw [List.cons_append, digitRun.go.eq_def]
    have hdd := hd d (by simp)
    simp only [digitVal_dig hdd, Option.isSome_some, ↓reduceIte]
    rw [ih (fun x hx => hd x (by simp [hx]))]
    simp; omega

theorem digitRun_digits (ds : List Char) (hne : ds ≠ []) (hd : ∀ c ∈ ds, IsDig c) (c : Char) (hc : ¬ IsDig c)
    (hu : c ≠ '_') (r : List Char) : digitRun 10 (ds ++ c :: r) = ds.length := by
  obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by cases ds with | nil => exact absurd rfl hne | cons d ds' => exact ⟨d, ds', rfl⟩
  have hdd := hd d (by simp)
  simp only [digitRun, List.cons_append, digitVal_dig hdd, Option.isSome_some, ↓reduceIte]
  rw [digitRun_go ds' (fun x hx => hd x (by simp [hx])) c hc hu r 1]
  simp; omega

theorem digitRun_nondig {c : Char} (hc : ¬ IsDig c) (r : List Char) : digitRun 10 (c :: r) = 0 := by
  simp [digitRun, digitVal_nondig hc]

theorem takeWhile_append_stop {p : Char → Bool} (xs : List Char) (hx : ∀ c ∈ xs, p c = true) (y : Char)
    (hy : p y = false) (ys : List Char) : (xs ++ y :: ys).takeWhile p = xs := by
  induction xs with
  | nil => simp [List.takeWhile, hy]
  | cons x xs ih =>
    simp only [List.cons_append, List.takeWhile, hx x (by simp)]
    rw [ih (fun c hc => hx c (by simp [hc]))]

theorem spaceLen_nonspace {c : Char} (h : isSpace c = false) (r : List Char) : spaceLen (c :: r) = 0 := by
  simp [spaceLen, List.takeWhile, h]

/-- The characters an end-of-tag alternative starts with. -/
def EndStart (c : Char) : Prop := c = '+' ∨ c = '-' ∨ c = '%' ∨ c = '}'

theorem endAt_none {c : Char} (hc : ¬ EndStart c) (r : List Char) :
    blockEndAt dcfg (c :: r) = none ∧ varEndAt dcfg (c :: r) = none := by
  simp only [EndStart, not_or] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have h1' := Ne.symm h1; have h2' := Ne.symm h2; have h3' := Ne.symm h3; have h4' := Ne.symm h4
  constructor
  · simp [blockEndAt, pre, h1, h2, h3, h3']
  · simp [varEndAt, pre, h2, h4, h4']

theorem intAt_nondig {c : Char} (hc : ¬ IsDig c) (r : List Char) : intAt (c :: r) = none := by
  simp only [IsDig] at hc
  unfold intAt
  split
  · rename_i h; simp only [List.cons.injEq] at h; obtain ⟨rfl, -⟩ := h; simp at hc
  · rename_i h; simp only [List.cons.injEq] at h; obtain ⟨rfl, -⟩ := h; simp at hc
  · rename_i c' r' h1 h2 h
    simp only [List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    rw [ite_f]
    simp only [char_le_iff, Char.reduceToNat]; omega
  · simp at *

theorem floatAt_nondig {c : Char} (hc : ¬ IsDig c) (r : List Char) : floatAt (c :: r) = none := by
  simp [floatAt, digitRun_nondig hc]

theorem nondig_of_isDigit {c : Char} (h : c.isDigit = false) : ¬ IsDig c := isDigit_false_iff.mp h

/-- The step after a token: the separating space. -/
theorem ws_step (kd : TagKind) (st : List Char) (ad : Bool) {rest : List Char}
    (hr : ∀ c, rest.head? = some c → isSpace c = false) (pos : Nat) :
    stepTag dcfg kd st ad (' ' :: rest) pos = .ok ([⟨.ws, [' ']⟩], .tag kd st false, rest) := by
  have hend := endAt_none (c := ' ') (by simp [EndStart]) rest
  have hs : isSpace ' ' = true := by decide
  have hsp : spaceLen (' ' :: rest) = 1 := by
    cases rest with
    | nil => simp [spaceLen, List.takeWhile, hs]
    | cons c cs =>
      have := hr c rfl
      simp [spaceLen, List.takeWhile, hs, this]
  unfold stepTag
  cases kd <;> cases st <;> simp [hend.1, hend.2, hsp, emit, cut]

theorem name_step {s : String} (hs : IsIdent s) (kd : TagKind) (st : List Char) (rest : List Char) (pos : Nat) :
    stepTag dcfg kd st false (s.toList ++ ' ' :: rest) pos = .ok ([⟨.name s, s.toList⟩], .tag kd st false, ' ' :: rest) := by
  obtain ⟨c, cs, hl, hc1, hc2, hc3, hcs⟩ := hs
  have hnd := nondig_of_isDigit hc2
  have hend := endAt_none (c := c) (by
    simp only [EndStart]; rintro (rfl | rfl | rfl | rfl) <;> simp [isIdentChar] at hc1) (cs ++ ' ' :: rest)
  have hsp := spaceLen_nonspace (ident_not_space hc1) (cs ++ ' ' :: rest)
  have hname : nameLen (c :: (cs ++ ' ' :: rest)) = cs.length + 1 := by
    have := takeWhile_append_stop (p := isIdentChar) (c :: cs) (by simpa [hc1] using hcs) ' ' (by decide) rest
    simp only [List.cons_append] at this
    simp [nameLen, this]
  have hofl : String.ofList (c :: cs) = s := by rw [← hl, String.ofList_toList]
  rw [hl]
  unfold stepTag
  cases kd <;> cases st <;> simp [hend.1, hend.2, hsp, floatAt_nondig hnd, intAt_nondig hnd, hname, hc3, emit, cut, hofl]

theorem space_nondig : ¬ IsDig ' ' := by simp [IsDig]

theorem dig_not_endStart {c : Char} (h : IsDig c) : ¬ EndStart c := by
  simp only [IsDig] at h
  simp only [EndStart, char_eq_iff, Char.reduceToNat]; omega

theorem intAt_digits (n : Nat) (rest : List Char) :
    intAt (natDigits n ++ ' ' :: rest) = some ((natDigits n).length, n) := by
  have hrun := digitRun_digits (natDigits n) (natDigits_ne_nil n) (natDigits_dig n) ' ' space_nondig
    (by decide) rest
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [natDigits_zero]; simp [intAt, intAt.z]
  · obtain ⟨d, ds, hds, hd⟩ := natDigits_head n hn
    have hdd := natDigits_dig n d (by rw [hds]; simp)
    simp only [IsDig] at hdd
    rw [hds] at hrun ⊢
    have hd0 : d ≠ '0' := by simp only [ne_eq, char_eq_iff, Char.reduceToNat]; omega
    have h19 : '1' ≤ d ∧ d ≤ '9' := by simp only [char_le_iff, Char.reduceToNat]; omega
    unfold intAt
    split
    · rename_i h; simp only [List.cons_append, List.cons.injEq] at h; exact absurd h.1 hd0
    · rename_i h; simp only [List.cons_append, List.cons.injEq] at h; exact absurd h.1 hd0
    · rename_i c' r' _ _ h
      simp only [List.cons_append, List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [ite_t h19]
      simp only
      rw [hrun, List.take_left, ← hds, digitsValue_natDigits]
    · simp at *

theorem floatAt_int (n : Nat) (rest : List Char) : floatAt (natDigits n ++ ' ' :: rest) = none := by
  have hrun := digitRun_digits (natDigits n) (natDigits_ne_nil n) (natDigits_dig n) ' ' space_nondig
    (by decide) rest
  have hne : (natDigits n).length ≠ 0 := by simpa using natDigits_ne_nil n
  simp [floatAt, hrun, hne, List.drop_left, fracLen, expLen]

theorem int_step (n : Nat) (kd : TagKind) (st : List Char) (rest : List Char) (pos : Nat) :
    stepTag dcfg kd st false (natDigits n ++ ' ' :: rest) pos =
      .ok ([⟨.int n, natDigits n⟩], .tag kd st false, ' ' :: rest) := by
  obtain ⟨d, ds, hds⟩ : ∃ d ds, natDigits n = d :: ds := by
    cases h : natDigits n with
    | nil => exact absurd h (natDigits_ne_nil n)
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hdd := natDigits_dig n d (by rw [hds]; simp)
  have hend := endAt_none (dig_not_endStart hdd) (ds ++ ' ' :: rest)
  have hsp := spaceLen_nonspace (dig_not_space hdd) (ds ++ ' ' :: rest)
  have hf := floatAt_int n rest
  have hi := intAt_digits n rest
  have hlen : (natDigits n).length = ds.length + 1 := by simp [hds]
  rw [hds] at hf hi hlen ⊢
  simp only [List.cons_append] at hf hi hend hsp ⊢
  unfold stepTag
  cases kd <;> cases st <;> simp [hend.1, hend.2, hsp, hf, hi, emit, cut, hlen]

theorem isDigit_of_dig {c : Char} (h : IsDig c) : c.isDigit = true := by
  cases hc : c.isDigit
  · exact absurd h (isDigit_false_iff.mp hc)
  · rfl

/-- The printed text of a float token, without the separating space. -/
def floatText (m sc : Nat) : List Char := natDigits m ++ 'e' :: '-' :: natDigits sc

theorem floatAt_float (m sc : Nat) (rest : List Char) :
    floatAt (floatText m sc ++ ' ' :: rest) = some (floatText m sc).length := by
  have he : ¬ IsDig 'e' := by simp [IsDig]
  have h1 := digitRun_digits (natDigits m) (natDigits_ne_nil m) (natDigits_dig m) 'e' he (by decide)
    ('-' :: (natDigits sc ++ ' ' :: rest))
  have h2 := digitRun_digits (natDigits sc) (natDigits_ne_nil sc) (natDigits_dig sc) ' ' space_nondig
    (by decide) rest
  have hne : (natDigits m).length ≠ 0 := by simpa using natDigits_ne_nil m
  have hne2 : (natDigits sc).length ≠ 0 := by simpa using natDigits_ne_nil sc
  simp only [floatText, List.append_assoc, List.cons_append] at h1 ⊢
  simp only [floatAt, h1, beq_iff_eq, hne, ↓reduceIte, List.drop_left, fracLen]
  have hpos : 0 < (natDigits sc).length := by omega
  simp [expLen, h2, hne2, hpos]
  omega

theorem floatValue_float (m sc : Nat) : floatValue (floatText m sc) = (m, sc) := by
  have hdm := natDigits_dig m
  have hds := natDigits_dig sc
  have hint : (floatText m sc).takeWhile (fun c => c != '.' && c != 'e' && c != 'E') = natDigits m := by
    unfold floatText
    apply takeWhile_append_stop
    · intro c hc
      have := hdm c hc
      simp only [IsDig] at this
      simp only [bne_iff_ne, ne_eq, char_eq_iff, Char.reduceToNat, Bool.and_eq_true, decide_eq_true_eq]
      omega
    · decide
  have hfilt : (natDigits sc).filter (fun c => c.isDigit) = natDigits sc :=
    List.filter_eq_self.2 (fun c hc => isDigit_of_dig (hds c hc))
  simp only [floatValue, hint]
  simp [floatText, List.drop_left, hfilt, digitsValue_natDigits]

theorem float_step (m sc : Nat) (kd : TagKind) (st : List Char) (rest : List Char) (pos : Nat) :
    stepTag dcfg kd st false (floatText m sc ++ ' ' :: rest) pos =
      .ok ([⟨.float m sc, floatText m sc⟩], .tag kd st false, ' ' :: rest) := by
  obtain ⟨d, ds, hds⟩ : ∃ d ds, natDigits m = d :: ds := by
    cases h : natDigits m with
    | nil => exact absurd h (natDigits_ne_nil m)
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hdd := natDigits_dig m d (by rw [hds]; simp)
  have hf := floatAt_float m sc rest
  have hv := floatValue_float m sc
  have hX : floatText m sc ++ ' ' :: rest = d :: (ds ++ 'e' :: '-' :: natDigits sc ++ ' ' :: rest) := by
    simp [floatText, hds]
  have hend : blockEndAt dcfg (floatText m sc ++ ' ' :: rest) = none ∧
      varEndAt dcfg (floatText m sc ++ ' ' :: rest) = none := by
    rw [hX]; exact endAt_none (dig_not_endStart hdd) _
  have hsp : spaceLen (floatText m sc ++ ' ' :: rest) = 0 := by
    rw [hX]; exact spaceLen_nonspace (dig_not_space hdd) _
  have htake : (floatText m sc ++ ' ' :: rest).take (floatText m sc).length = floatText m sc := List.take_left
  have hdrop : (floatText m sc ++ ' ' :: rest).drop (floatText m sc).length = ' ' :: rest := List.drop_left
  generalize floatText m sc = X at hf hv hend hsp htake hdrop
  generalize X ++ ' ' :: rest = L at hf hend hsp htake hdrop
  unfold stepTag
  cases kd <;> cases st <;> simp [hend.1, hend.2, hsp, hf, emit, cut, htake, hdrop, hv]

/-! ## String literals -/

theorem escapeStr_cons (c : Char) (cs : List Char) :
    Pretty.escapeStr (c :: cs) =
      (if c == '\\' then ['\\', '\\'] else if c == '\'' then ['\\', '\'']
        else if c == '\r' then ['\\', 'r'] else [c]) ++ Pretty.escapeStr cs := by
  rw [Pretty.escapeStr]

theorem cr_not_mem_escapeStr : ∀ cs : List Char, '\r' ∉ Pretty.escapeStr cs
  | [] => by simp [Pretty.escapeStr]
  | c :: cs => by
    rw [escapeStr_cons]
    have := cr_not_mem_escapeStr cs
    by_cases h1 : c = '\\' <;> by_cases h2 : c = '\'' <;> by_cases h3 : c = '\r' <;> simp_all [@eq_comm _ '\r']

theorem normalizeNewlines_id : ∀ l : List Char, '\r' ∉ l → normalizeNewlines ['\n'] l = l
  | [] => fun _ => by simp [normalizeNewlines]
  | c :: l => fun h => by
    simp only [List.mem_cons, not_or] at h
    have ih := normalizeNewlines_id l h.2
    by_cases hn : c = '\n'
    · subst hn; rw [normalizeNewlines]; simp [ih]
    · rw [normalizeNewlines.eq_def]
      split <;> simp_all

theorem stringGo_escape (r : List Char) : ∀ (cs : List Char) (n : Nat),
    stringAt.go '\'' (Pretty.escapeStr cs ++ '\'' :: r) n = some (n + (Pretty.escapeStr cs).length + 1)
  | [], n => by simp [Pretty.escapeStr, stringAt.go]
  | c :: cs, n => by
    have ih := stringGo_escape r cs
    rw [escapeStr_cons]
    by_cases h1 : c = '\\'
    · subst h1; simp [stringAt.go, ih]; omega
    · by_cases h2 : c = '\''
      · subst h2; simp [stringAt.go, ih]; omega
      · by_cases h3 : c = '\r'
        · subst h3; simp [stringAt.go, ih]; omega
        · simp only [beq_iff_eq, h1, h2, h3, ↓reduceIte, List.singleton_append, List.cons_append]
          rw [stringAt.go.eq_def]
          split
          · simp_all
          · simp_all
          · rename_i c' r' hne h
            simp only [List.cons.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [h2, ih]; omega

theorem unescape_escape : ∀ cs : List Char, unescapeStr (Pretty.escapeStr cs) = .ok cs
  | [] => by simp [Pretty.escapeStr, unescapeStr]
  | c :: cs => by
    have ih := unescape_escape cs
    rw [escapeStr_cons]
    by_cases h1 : c = '\\'
    · subst h1; simp [unescapeStr, ih, bind, Except.bind, pure, Except.pure]
    · by_cases h2 : c = '\''
      · subst h2; simp [unescapeStr, ih, bind, Except.bind, pure, Except.pure]
      · by_cases h3 : c = '\r'
        · subst h3; simp [unescapeStr, ih, bind, Except.bind, pure, Except.pure]
        · simp only [beq_iff_eq, h1, h2, h3, ↓reduceIte, List.singleton_append]
          rw [unescapeStr.eq_def]
          split
          · simp_all
          · simp_all
          · rename_i c' r' hne h
            simp only [List.cons.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [ih, bind, Except.bind, pure, Except.pure]

/-- The printed text of a string literal, without the separating space. -/
def strText (s : String) : List Char := '\'' :: (Pretty.escapeStr s.toList ++ ['\''])

theorem str_step (s : String) (kd : TagKind) (st : List Char) (rest : List Char) (pos : Nat) :
    stepTag dcfg kd st false (strText s ++ ' ' :: rest) pos =
      .ok ([⟨.str s, strText s⟩], .tag kd st false, ' ' :: rest) := by
  have hq : ¬ IsDig '\'' := by simp [IsDig]
  have hend := endAt_none (c := '\'') (by simp [EndStart]) (Pretty.escapeStr s.toList ++ ['\''] ++ ' ' :: rest)
  have hsp := spaceLen_nonspace (c := '\'') (by decide) (Pretty.escapeStr s.toList ++ ['\''] ++ ' ' :: rest)
  have hname : nameLen ('\'' :: (Pretty.escapeStr s.toList ++ ['\''] ++ ' ' :: rest)) = 0 := by
    simp [nameLen, List.takeWhile, show isIdentChar '\'' = false by decide]
  have hstr : stringAt (strText s ++ ' ' :: rest) = some (strText s).length := by
    simp only [strText, List.cons_append, List.append_assoc, List.singleton_append]
    simp only [stringAt, beq_self_eq_true, Bool.true_or, ↓reduceIte]
    rw [stringGo_escape]
    simp; omega
  have htake : (strText s ++ ' ' :: rest).take (strText s).length = strText s := List.take_left
  have hinner : (strText s).tail.dropLast = Pretty.escapeStr s.toList := by
    simp [strText]
  have hnorm := normalizeNewlines_id _ (cr_not_mem_escapeStr s.toList)
  have hun := unescape_escape s.toList
  have hX : strText s ++ ' ' :: rest = '\'' :: (Pretty.escapeStr s.toList ++ ['\''] ++ ' ' :: rest) := by
    simp [strText]
  have hdrop : (strText s ++ ' ' :: rest).drop (strText s).length = ' ' :: rest := List.drop_left
  rw [hX] at hstr htake hdrop ⊢
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] at hend hsp hname hstr htake hdrop ⊢
  unfold stepTag
  cases kd <;> cases st <;>
    simp [hend.1, hend.2, hsp, floatAt_nondig hq, intAt_nondig hq, hname, hstr, htake, hinner, hnorm, hun,
      emit, cut, hdrop, String.ofList_toList]

/-! ## Operators -/

theorem op_step (o : Op) (kd : TagKind) (st st' : List Char) (hs : stackStep st (.op o) = some st')
    (rest : List Char) (pos : Nat) :
    stepTag dcfg kd st false (o.text.toList ++ ' ' :: rest) pos =
      .ok ([⟨.op o, o.text.toList⟩], .tag kd st' (o == .dot), ' ' :: rest) := by
  cases o <;> cases kd <;> rcases st with _ | ⟨e, st⟩ <;> simp only [stackStep, closerOf, isCloser] at hs <;>
    unfold stepTag <;>
    simp_all [Op.text, blockEndAt, varEndAt, pre, spaceLen, isSpace, floatAt, digitRun, digitVal, intAt, nameLen,
      isIdentChar, stringAt, opAt, closerOf, isCloser, emit, cut]

end LeanJinja2
