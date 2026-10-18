import LeanJinja2.Proofs.Roundtrip.Template

/-!
# `parse_pretty_roundtrip`

The parser reads a well-formed template's canonical print back to the same
template: lexing the print gives back the printed token stream
(`lex_pretty`, from `stream_run`), and the parser reads that stream back
(`parseTokens_pretty`).
-/

namespace LeanJinja2

open Lex

set_option linter.unusedSimpArgs false

theorem stream_last_ne_cr {ks : List TokKind} (h : Stream ks) : (Pretty.render ks).getLast? ≠ some '\r' := by
  induction h with
  | nil => simp [Pretty.render]
  | text s hs =>
    intro hl
    have := List.mem_of_getLast? (by simpa [Pretty.render, Pretty.tokText] using hl)
    exact hs.2.1 this
  | tag pre blk ks rest _ _ _ _ _ ih =>
    intro hl
    have heq : Pretty.render (preTok pre ++ openKind blk :: (ks ++ closeKind blk :: rest)) =
        Pretty.render (preTok pre ++ openKind blk :: ks) ++ closeChars blk ++ Pretty.render rest := by
      cases blk <;> simp [render_append, render_cons, Pretty.tokText, closeKind, closeChars, Pretty.render]
    rw [heq, List.getLast?_append] at hl
    cases hr : (Pretty.render rest).getLast? with
    | some c => rw [hr] at hl; simp at hl; exact ih (by rw [hr, hl])
    | none => rw [hr] at hl; cases blk <;> simp [closeChars, List.getLast?_append] at hl

/-- Lexing a template's canonical print gives back its token stream. -/
theorem lex_pretty (t : List Node) (h : WellFormed t) :
    ∃ ts, lex {} (pretty t) = .ok ts ∧ significant ts = Pretty.nodes t := by
  have hs := nodes_stream t h
  obtain ⟨ts, m, hrun, hsig⟩ := stream_run hs true
  have hcr := stream_last_ne_cr hs
  generalize hcs : Pretty.render (Pretty.nodes t) = cs at hrun hcr
  have hloop : ∀ fuel, cs.length ≤ fuel → loop dcfg fuel (.root true) cs 0 [] = .ok ts :=
    fun fuel hf => by simpa using hrun.loop fuel 0 [] hf
  unfold lex lexList pretty
  rw [hcs]
  by_cases hnl : cs.getLast? = some '\n'
  · have hk : trailingNewlineLen {} (cs ++ ['\n']) = 1 := by
      obtain ⟨cs', rfl⟩ : ∃ cs', cs = cs' ++ ['\n'] := List.getLast?_eq_some_iff.mp hnl
      simp [trailingNewlineLen]
    refine ⟨ts ++ [⟨.ws, ['\n']⟩], ?_, ?_⟩
    · simp [hnl, String.toList_ofList, hk, hloop (cs.length + 1) (by omega)]
    · rw [significant_append, hsig]; simp [significant, TokKind.ignored]
  · have hk : trailingNewlineLen {} cs = 0 := by
      unfold trailingNewlineLen
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hr : cs.reverse with
      | nil => rfl
      | cons c r =>
        have hc : cs.getLast? = some c := by
          rw [← List.head?_reverse, hr]; rfl
        have h1 : c ≠ '\n' := fun e => hnl (by rw [hc, e])
        have h2 : c ≠ '\r' := fun e => hcr (by rw [hc, e])
        split <;> simp_all
    refine ⟨ts, ?_, hsig⟩
    simp [hnl, String.toList_ofList, hk, hloop (cs.length + 1) (by omega)]

/-- `parse_pretty_roundtrip`: the parser reads a well-formed template's
canonical print back to the same template. -/
theorem parse_pretty_roundtrip (t : List Node) (h : WellFormed t) : parse {} (pretty t) = .ok t := by
  obtain ⟨ts, hl, hs⟩ := lex_pretty t h
  simp [parse, hl, hs, parseTokens_pretty t h]

end LeanJinja2
