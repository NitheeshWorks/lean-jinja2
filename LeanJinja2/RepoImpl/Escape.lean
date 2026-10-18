import LeanMarkupsafe

/-!
# Escaping in place

lean-markupsafe's `escape` maps the string to a `List Char`, escapes it with
the non-tail-recursive `escapeList` and packs the result: about 90 bytes per
input byte and a stack frame per character. `escapeFast` escapes in one
`String.foldl` into a `String`. `escape_eq_fast` proves the two equal and, as
`@[csimp]`, makes every `escape` this package compiles run the fast one;
the proofs, all about `escape`, are untouched.
-/

namespace LeanJinja2

open LeanMarkupsafe

/-- Append the escape of one character. -/
def escPush (acc : String) (c : Char) : String :=
  match c with
  | '&' => acc ++ "&amp;"
  | '<' => acc ++ "&lt;"
  | '>' => acc ++ "&gt;"
  | '"' => acc ++ "&#34;"
  | '\'' => acc ++ "&#39;"
  | c => acc.push c

/-- `escape`, in one pass into a `String`. -/
def escapeFast (s : String) : Markup := ⟨s.foldl escPush ""⟩

theorem escPush_toList (acc : String) (c : Char) :
    (escPush acc c).toList = acc.toList ++ escapeChar c := by
  unfold escPush escapeChar
  split <;> simp_all [String.toList_push]

theorem foldl_escPush (l : List Char) (acc : String) :
    (l.foldl escPush acc).toList = acc.toList ++ escapeList l := by
  induction l generalizing acc with
  | nil => simp [escapeList]
  | cons c cs ih => rw [List.foldl_cons, ih, escPush_toList]; simp [escapeList]

@[csimp] theorem escape_eq_fast : @LeanMarkupsafe.escape = @escapeFast := by
  funext s
  unfold LeanMarkupsafe.escape escapeFast
  congr 1
  apply String.ext
  rw [String.foldl_eq_foldl_toList, foldl_escPush, String.toList_ofList]
  simp

end LeanJinja2
