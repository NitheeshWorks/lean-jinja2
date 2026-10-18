import LeanJinja2.Proofs.Roundtrip.Segments

/-!
# Printed token streams lex back

`Stream ks`: `ks` is template text and tags in the shape the printer
produces. The lexer reads the rendering of such a stream back to tokens
whose significant part is `ks` (`stream_run`).
-/

namespace LeanJinja2

open Lex

set_option linter.unusedSimpArgs false

def preTok : Option String → List TokKind
  | none => []
  | some s => [.data s]

def preChars : Option String → List Char
  | none => []
  | some s => s.toList

def PreOK : Option String → Prop
  | none => True
  | some s => TextOK s

/-- A block tag starts with a name that is not `raw…` (which would open a raw block). -/
def BlockHead (ks : List TokKind) : Prop := ∃ kw r, ks = .name kw :: r ∧ kw.toList.head? ≠ some 'r'

inductive Stream : List TokKind → Prop
  | nil : Stream []
  | text (s : String) : TextOK s → Stream [.data s]
  | tag (pre : Option String) (blk : Bool) (ks rest : List TokKind) : PreOK pre → InnerAll ks →
      stackAfter [] ks = some [] → (blk = true → BlockHead ks) → Stream rest →
      Stream (preTok pre ++ openKind blk :: (ks ++ closeKind blk :: rest))

theorem render_append (a b : List TokKind) : Pretty.render (a ++ b) = Pretty.render a ++ Pretty.render b := by
  simp [Pretty.render]

theorem render_cons (k : TokKind) (b : List TokKind) : Pretty.render (k :: b) = Pretty.tokText k ++ Pretty.render b := by
  simp [Pretty.render]

theorem stream_run : ∀ {ks : List TokKind}, Stream ks → ∀ ls, ∃ ts m, Run (.root ls) (Pretty.render ks) ts m [] ∧
    significant ts = ks
  | _, .nil, ls => ⟨[], _, Run.refl _ _, rfl⟩
  | _, .text s hs, ls => by
    obtain ⟨hne, hcr, hidx⟩ := hs
    have h := root_text ls s.toList (noOpen_of_index _ hidx) hcr hne
    have hl : 0 < s.toList.length := List.length_pos_iff.mpr hne
    refine ⟨_, _, Run.one (by simpa [Pretty.render, Pretty.tokText] using h)
      (by simpa [Pretty.render, Pretty.tokText] using hl), ?_⟩
    simp [significant, TokKind.ignored, String.ofList_toList]
  | _, .tag pre blk ks rest hpre hin hbal hhead hrest, ls => by
    obtain ⟨ts3, m3, hrun3, hsig3⟩ := stream_run hrest .text
    have hcl : NoLead (closeChars blk ++ Pretty.render rest) := by
      intro c hc; cases blk <;> simp [closeChars] at hc <;> subst hc <;> decide
    obtain ⟨ts2, hrun2, hsig2⟩ := inner_run ks [] [] hin hbal (tagKind blk) (by cases blk <;> simp [tagKind]) _ hcl
    have hX : NoLead (Pretty.render ks ++ (closeChars blk ++ Pretty.render rest)) := by
      cases ks with
      | nil => simpa [Pretty.render] using hcl
      | cons k ks' =>
        have hk := (innerAll_cons.mp hin).1
        obtain ⟨c, cs, hc, hsp⟩ := innerText_head hk
        intro x hx
        simp [render_cons, tokText_inner hk, hc] at hx
        subst hx; exact hsp
    have hXr : blk = true → (Pretty.render ks ++ (closeChars blk ++ Pretty.render rest)).head? ≠ some 'r' := by
      intro hb
      obtain ⟨kw, r, rfl, hkw⟩ := hhead hb
      have hk := (innerAll_cons.mp hin).1
      obtain ⟨c, cs, hl, -⟩ := hk
      simp [render_cons, Pretty.tokText, hl] at hkw ⊢
      exact hkw
    let p : List Char := preChars pre
    have hp : NoOpen p ∧ '\r' ∉ p ∧ significant (dataToks p) = preTok pre := by
      cases pre with
      | none => simp [p, preChars, NoOpen, dataToks, preTok, significant]
      | some s =>
        obtain ⟨hne, hcr, hidx⟩ := hpre
        refine ⟨noOpen_of_index _ hidx, hcr, ?_⟩
        simp [p, preChars, dataToks, hne, preTok, significant, TokKind.ignored, String.ofList_toList]
    have h1 := root_open ls p hp.1 hp.2.1 blk _ hXr hX
    have hws : ∀ pos, Lex.step dcfg (.tag (tagKind blk) [] false)
        (' ' :: (Pretty.render ks ++ (closeChars blk ++ Pretty.render rest))) pos =
        .ok ([⟨.ws, [' ']⟩], .tag (tagKind blk) [] false, Pretty.render ks ++ (closeChars blk ++ Pretty.render rest)) :=
      fun pos => step_tag (ws_step (tagKind blk) (by cases blk <;> simp [tagKind]) [] false hX pos)
        (Or.inr (by cases blk <;> rfl))
    have h4 := close_step blk (Pretty.render rest)
    have hren : Pretty.render (preTok pre ++ openKind blk :: (ks ++ closeKind blk :: rest)) =
        p ++ '{' :: openChar blk :: ' ' :: (Pretty.render ks ++ (closeChars blk ++ Pretty.render rest)) := by
      cases pre <;> cases blk <;>
        simp [p, preChars, preTok, render_append, render_cons, Pretty.tokText, openKind, closeKind, openChar, closeChars,
          Pretty.render]
    refine ⟨(dataToks p ++ [⟨openKind blk, ['{', openChar blk]⟩]) ++ ([⟨.ws, [' ']⟩] ++
      (ts2 ++ ([⟨closeKind blk, closeChars blk⟩] ++ ts3))), m3, ?_, ?_⟩
    · rw [hren]
      refine Run.cons h1 (by simp; omega) (Run.cons hws (by simp) ?_)
      exact Run.trans hrun2 (Run.cons h4 (by cases blk <;> simp [closeChars] <;> omega) hrun3)
    · simp only [significant_append, hp.2.2, hsig2, hsig3]
      cases blk <;> simp [significant, openKind, closeKind, TokKind.ignored]

end LeanJinja2
