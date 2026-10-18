import LeanJinja2.Proofs.Roundtrip.Run

/-!
# Lexing printed template text and tags

In template data the lexer looks for the next tag start. Printed text has
none (`NoOpen`), so the lexer reads it whole, together with the `{{ ` or
`{% ` that follows; the tag's contents are `inner_run`, and `}}` or `%}`
return to template data.
-/

namespace LeanJinja2

open Lex

set_option linter.unusedSimpArgs false

theorem len2a : "{{".length = 2 := rfl
theorem len2b : "{%".length = 2 := rfl
theorem len2c : "{#".length = 2 := rfl
theorem len2d : "}}".length = 2 := rfl
theorem len2e : "%}".length = 2 := rfl

theorem beginOrder_dcfg : beginOrder dcfg = [(4, "{{"), (1, "{#"), (0, "{%")] := by decide

theorem tagAt_var (pv : Prev) (X : List Char) : tagAt dcfg pv ('{' :: '{' :: ' ' :: X) = some (.var 2 none) := by
  simp [tagAt, rawBeginAt, pre, beginOrder_dcfg, tagAt.pick, ruleAt, signAt, signLen, len2a, len2b, len2c]

theorem tagAt_block (pv : Prev) (X : List Char) (hX : X.head? ≠ some 'r') (hn : NoLead X) :
    tagAt dcfg pv ('{' :: '%' :: ' ' :: X) = some (.block 2 none) := by
  have hsp : List.takeWhile isSpace X = [] := by
    cases X with
    | nil => rfl
    | cons c cs => simp [List.takeWhile, hn c rfl]
  have hraw : ¬ (['r', 'a', 'w'] <+: X) := by
    rintro ⟨t, rfl⟩; simp at hX
  have hs : isSpace ' ' = true := by decide
  simp [tagAt, rawBeginAt, pre, beginOrder_dcfg, tagAt.pick, ruleAt, signAt, signLen, spaceLen, List.takeWhile, hsp,
    hraw, hs, len2a, len2b, len2c]

theorem tagAt_none_ne {pv : Prev} {c : Char} (hc : c ≠ '{') (r : List Char) : tagAt dcfg pv (c :: r) = none := by
  have hc' : '{' ≠ c := Ne.symm hc
  simp [tagAt, rawBeginAt, pre, beginOrder_dcfg, tagAt.pick, ruleAt, hc, hc']

theorem tagAt_none_brace {pv : Prev} {d : Char} (h1 : d ≠ '{') (h2 : d ≠ '%') (h3 : d ≠ '#') (r : List Char) :
    tagAt dcfg pv ('{' :: d :: r) = none := by
  have h1' : '{' ≠ d := Ne.symm h1
  have h2' : '%' ≠ d := Ne.symm h2
  have h3' : '#' ≠ d := Ne.symm h3
  simp [tagAt, rawBeginAt, pre, beginOrder_dcfg, tagAt.pick, ruleAt, h1, h2, h3, h1', h2', h3']

/-- Text with no tag start in it. -/
def NoOpen : List Char → Prop
  | [] => True
  | c :: cs => (c = '{' → ∃ d ds, cs = d :: ds ∧ d ≠ '{' ∧ d ≠ '%' ∧ d ≠ '#') ∧ NoOpen cs

theorem noOpen_of_index : ∀ l : List Char,
    (∀ i, l[i]? = some '{' → ∃ c, l[i + 1]? = some c ∧ c ≠ '{' ∧ c ≠ '%' ∧ c ≠ '#') → NoOpen l
  | [], _ => trivial
  | c :: cs, h => by
    refine ⟨fun hc => ?_, noOpen_of_index cs (fun i hi => by simpa using h (i + 1) (by simpa using hi))⟩
    obtain ⟨d, hd, h1, h2, h3⟩ := h 0 (by simp [hc])
    cases cs with
    | nil => simp at hd
    | cons d' ds => simp at hd; subst hd; exact ⟨d', ds, rfl, h1, h2, h3⟩

theorem findTag_skip : ∀ (p : List Char), NoOpen p → ∀ (q : List Char) (i : Nat) (pv : Prev),
    ∃ pv', findTag dcfg pv (p ++ q) i = findTag dcfg pv' q (i + p.length)
  | [], _, q, i, pv => ⟨pv, by simp⟩
  | c :: cs, ⟨hc, hcs⟩, q, i, pv => by
    have hnone : tagAt dcfg pv (c :: (cs ++ q)) = none := by
      by_cases h : c = '{'
      · obtain ⟨d, ds, rfl, h1, h2, h3⟩ := hc h
        subst h
        exact tagAt_none_brace h1 h2 h3 _
      · exact tagAt_none_ne h _
    obtain ⟨pv', h'⟩ := findTag_skip cs hcs q (i + 1) (prevClass c)
    refine ⟨pv', ?_⟩
    rw [List.cons_append, findTag, hnone]
    simp only
    rw [h']
    simp only [List.length_cons]
    congr 1; omega

theorem findTag_here {pv : Prev} {l : List Char} {t : TagStart} (h : tagAt dcfg pv l = some t) (hl : l ≠ [])
    (i : Nat) : findTag dcfg pv l i = some (i, t) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons c cs => rw [findTag, h]

/-- The tokens for printed template text (none when there is no text). -/
def dataToks (p : List Char) : List Token := if p = [] then [] else [⟨.data (String.ofList p), p⟩]

/-- `{{`/`{%` and the token kinds of the tag delimiters. -/
def openChar (blk : Bool) : Char := if blk then '%' else '{'
def openKind (blk : Bool) : TokKind := if blk then .blockBegin else .varBegin
def closeKind (blk : Bool) : TokKind := if blk then .blockEnd else .varEnd
def tagKind (blk : Bool) : TagKind := if blk then .block else .var
def closeChars (blk : Bool) : List Char := if blk then ['%', '}'] else ['}', '}']

theorem root_open (ls : Prev) (p : List Char) (hp : NoOpen p) (hcr : '\r' ∉ p) (blk : Bool) (X : List Char)
    (hX : blk = true → X.head? ≠ some 'r') (hn : NoLead X) (pos : Nat) :
    Lex.step dcfg (.root ls) (p ++ '{' :: openChar blk :: ' ' :: X) pos =
      .ok (dataToks p ++ [⟨openKind blk, ['{', openChar blk]⟩], .tag (tagKind blk) [] false, ' ' :: X) := by
  have hf : findTag dcfg ls (p ++ '{' :: openChar blk :: ' ' :: X) 0 =
      some (p.length, if blk then .block 2 none else .var 2 none) := by
    obtain ⟨pv', h'⟩ := findTag_skip p hp ('{' :: openChar blk :: ' ' :: X) 0 ls
    rw [h', findTag_here (t := if blk then .block 2 none else .var 2 none) _ (by simp)]
    · simp
    · cases blk
      · simpa [openChar] using tagAt_var pv' X
      · simpa [openChar] using tagAt_block pv' X (hX rfl) hn
  have hnorm := normalizeNewlines_id p hcr
  have htake : (p ++ '{' :: openChar blk :: ' ' :: X).take p.length = p := List.take_left
  have hdrop : (p ++ '{' :: openChar blk :: ' ' :: X).drop p.length = '{' :: openChar blk :: ' ' :: X :=
    List.drop_left
  simp only [Lex.step, stepRoot, hf]
  simp only [closeLine]
  cases blk <;>
    simp [stripSplit, seq, cutData, cutOpt, cut, emit, htake, hdrop, hnorm, dataToks, openKind, openChar, tagKind] <;>
    split <;> simp_all

theorem close_step (blk : Bool) (R : List Char) (pos : Nat) :
    Lex.step dcfg (.tag (tagKind blk) [] false) (closeChars blk ++ R) pos =
      .ok ([⟨closeKind blk, closeChars blk⟩], .root .text, R) := by
  cases blk <;> simp [Lex.step, closeLine, LexMode.openLine, stepTag, tagKind, closeChars, closeKind, blockEndAt,
    varEndAt, pre, emit, cut, prevOf, prevClass, isNewline, isSpace, len2d, len2e]

theorem root_text (ls : Prev) (p : List Char) (hp : NoOpen p) (hcr : '\r' ∉ p) (hne : p ≠ []) (pos : Nat) :
    Lex.step dcfg (.root ls) p pos = .ok ([⟨.data (String.ofList p), p⟩], .root .text, []) := by
  have hf : findTag dcfg ls p 0 = none := by
    obtain ⟨pv', h'⟩ := findTag_skip p hp [] 0 ls
    simp only [List.append_nil] at h'
    rw [h']; rfl
  have hnorm := normalizeNewlines_id p hcr
  simp [Lex.step, closeLine, LexMode.openLine, stepRoot, hf, emit, cutData, cutOpt, cut, hnorm, hne]

end LeanJinja2
