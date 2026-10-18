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

theorem beginOrder_dcfg : beginOrder dcfg = [(2, "{{"), (1, "{#"), (0, "{%")] := by decide

theorem tagAt_var (X : List Char) : tagAt dcfg ('{' :: '{' :: ' ' :: X) = some (.var 2 none) := by
  simp [tagAt, rawBeginAt, pre, beginOrder_dcfg, tagAt.pick, signAt, signLen, len2a, len2b, len2c]

theorem tagAt_block (X : List Char) (hX : X.head? ≠ some 'r') (hn : NoLead X) :
    tagAt dcfg ('{' :: '%' :: ' ' :: X) = some (.block 2 none) := by
  have hsp : List.takeWhile isSpace X = [] := by
    cases X with
    | nil => rfl
    | cons c cs => simp [List.takeWhile, hn c rfl]
  have hraw : ¬ (['r', 'a', 'w'] <+: X) := by
    rintro ⟨t, rfl⟩; simp at hX
  have hs : isSpace ' ' = true := by decide
  simp [tagAt, rawBeginAt, pre, beginOrder_dcfg, tagAt.pick, signAt, signLen, spaceLen, List.takeWhile, hsp,
    hraw, hs, len2a, len2b, len2c]

theorem tagAt_none_ne {c : Char} (hc : c ≠ '{') (r : List Char) : tagAt dcfg (c :: r) = none := by
  have hc' : '{' ≠ c := Ne.symm hc
  simp [tagAt, rawBeginAt, pre, beginOrder_dcfg, tagAt.pick, hc, hc']

theorem tagAt_none_brace {d : Char} (h1 : d ≠ '{') (h2 : d ≠ '%') (h3 : d ≠ '#') (r : List Char) :
    tagAt dcfg ('{' :: d :: r) = none := by
  have h1' : '{' ≠ d := Ne.symm h1
  have h2' : '%' ≠ d := Ne.symm h2
  have h3' : '#' ≠ d := Ne.symm h3
  simp [tagAt, rawBeginAt, pre, beginOrder_dcfg, tagAt.pick, h1, h2, h3, h1', h2', h3']

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

theorem findTag_skip : ∀ (p : List Char), NoOpen p → ∀ (q : List Char) (i : Nat),
    findTag dcfg (p ++ q) i = findTag dcfg q (i + p.length)
  | [], _, q, i => by simp
  | c :: cs, ⟨hc, hcs⟩, q, i => by
    have hnone : tagAt dcfg (c :: (cs ++ q)) = none := by
      by_cases h : c = '{'
      · obtain ⟨d, ds, rfl, h1, h2, h3⟩ := hc h
        subst h
        exact tagAt_none_brace h1 h2 h3 _
      · exact tagAt_none_ne h _
    rw [List.cons_append, findTag, hnone]
    simp only
    rw [findTag_skip cs hcs q (i + 1)]
    simp only [List.length_cons]
    congr 1; omega

theorem findTag_here {l : List Char} {t : TagStart} (h : tagAt dcfg l = some t) (hl : l ≠ []) (i : Nat) :
    findTag dcfg l i = some (i, t) := by
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

theorem root_open (ls : Bool) (p : List Char) (hp : NoOpen p) (hcr : '\r' ∉ p) (blk : Bool) (X : List Char)
    (hX : blk = true → X.head? ≠ some 'r') (hn : NoLead X) (pos : Nat) :
    Lex.step dcfg (.root ls) (p ++ '{' :: openChar blk :: ' ' :: X) pos =
      .ok (dataToks p ++ [⟨openKind blk, ['{', openChar blk]⟩], .tag (tagKind blk) [] false, ' ' :: X) := by
  have hf : findTag dcfg (p ++ '{' :: openChar blk :: ' ' :: X) 0 =
      some (p.length, if blk then .block 2 none else .var 2 none) := by
    rw [findTag_skip p hp, findTag_here (t := if blk then .block 2 none else .var 2 none) _ (by simp)]
    · simp
    · cases blk
      · simpa [openChar] using tagAt_var X
      · simpa [openChar] using tagAt_block X (hX rfl) hn
  have hnorm := normalizeNewlines_id p hcr
  have htake : (p ++ '{' :: openChar blk :: ' ' :: X).take p.length = p := List.take_left
  have hdrop : (p ++ '{' :: openChar blk :: ' ' :: X).drop p.length = '{' :: openChar blk :: ' ' :: X :=
    List.drop_left
  simp only [Lex.step, stepRoot, hf]
  cases blk <;>
    simp [stripSplit, seq, cutData, cutOpt, cut, emit, htake, hdrop, hnorm, dataToks, openKind, openChar, tagKind] <;>
    split <;> simp_all

theorem close_step (blk : Bool) (R : List Char) (pos : Nat) :
    Lex.step dcfg (.tag (tagKind blk) [] false) (closeChars blk ++ R) pos =
      .ok ([⟨closeKind blk, closeChars blk⟩], .root false, R) := by
  cases blk <;> simp [Lex.step, stepTag, tagKind, closeChars, closeKind, blockEndAt, varEndAt, pre, emit, cut,
    endsNewline, isNewline, len2d, len2e]

theorem root_text (ls : Bool) (p : List Char) (hp : NoOpen p) (hcr : '\r' ∉ p) (hne : p ≠ []) (pos : Nat) :
    Lex.step dcfg (.root ls) p pos = .ok ([⟨.data (String.ofList p), p⟩], .root false, []) := by
  have hf : findTag dcfg p 0 = none := by
    have := findTag_skip p hp [] 0
    simp only [List.append_nil] at this
    rw [this]; rfl
  have hnorm := normalizeNewlines_id p hcr
  simp [Lex.step, stepRoot, hf, emit, cutData, cutOpt, cut, hnorm, hne]

end LeanJinja2
