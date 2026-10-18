import LeanJinja2.Specifications.Semantics
import LeanJinja2.Proofs.Render

/-!
# Filter semantics

One equation per builtin filter, about the public `applyFilter`: dispatch
by name reaches the filter's definition (`applyFilter_builtin`), and the
filter computes what upstream's does.
-/

namespace LeanJinja2

set_option linter.unusedSimpArgs false

open LeanMarkupsafe

/-- Name dispatch: a builtin filter name applies that filter. -/
theorem applyFilter_builtin {fc : FCtx} {name : String} {f : FilterFn} {v : Value}
    {args : List Value} {kw : List (String × Value)}
    (h : ∀ apply, (builtinFilterTable apply).lookup name = some f) :
    applyFilter fc name v args kw = f fc v args kw := by
  simp only [applyFilter, applyFilterD, h]

theorem filter_upper (fc : FCtx) (s : String) :
    applyFilter fc "upper" (.str s) [] [] = .ok (.str (strUpper s)) := by
  rw [applyFilter_builtin (f := Filters.upper) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_lower (fc : FCtx) (s : String) :
    applyFilter fc "lower" (.str s) [] [] = .ok (.str (strLower s)) := by
  rw [applyFilter_builtin (f := Filters.lower) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_length (fc : FCtx) (xs : List Value) :
    applyFilter fc "length" (.list xs) [] [] = .ok (.int xs.length) := by
  rw [applyFilter_builtin (f := Filters.length) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_length_str (fc : FCtx) (s : String) :
    applyFilter fc "length" (.str s) [] [] = .ok (.int s.length) := by
  rw [applyFilter_builtin (f := Filters.length) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_default_undefined (fc : FCtx) (i : UndefInfo) (d : Value) :
    applyFilter fc "default" (.undef i) [d] [] = .ok d := by
  rw [applyFilter_builtin (f := Filters.default) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_default_defined (fc : FCtx) (v d : Value) (hv : v.isUndef = false) :
    applyFilter fc "default" v [d] [] = .ok v := by
  rw [applyFilter_builtin (f := Filters.default) (fun _ => by simp [builtinFilterTable, List.lookup])]
  simp [Filters.default, hv, argAt]
  rfl

theorem filter_escape (fc : FCtx) (s : String) :
    applyFilter fc "escape" (.str s) [] [] = .ok (.markup (escape s)) := by
  rw [applyFilter_builtin (f := Filters.e) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_escape_markup (fc : FCtx) (m : Markup) :
    applyFilter fc "escape" (.markup m) [] [] = .ok (.markup m) := by
  rw [applyFilter_builtin (f := Filters.e) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_safe (fc : FCtx) (s : String) :
    applyFilter fc "safe" (.str s) [] [] = .ok (.markup (Markup.markSafe s)) := by
  rw [applyFilter_builtin (f := Filters.safe) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_first (fc : FCtx) (x : Value) (xs : List Value) :
    applyFilter fc "first" (.list (x :: xs)) [] [] = .ok x := by
  rw [applyFilter_builtin (f := Filters.first) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_last (fc : FCtx) (xs : List Value) (x : Value) :
    applyFilter fc "last" (.list (xs ++ [x])) [] [] = .ok x := by
  rw [applyFilter_builtin (f := Filters.last) (fun _ => by simp [builtinFilterTable, List.lookup])]
  simp [Filters.last, iterOf, pure, Except.pure, bind, Except.bind]

theorem filter_list (fc : FCtx) (xs : List Value) :
    applyFilter fc "list" (.list xs) [] [] = .ok (.list xs) := by
  rw [applyFilter_builtin (f := Filters.list) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_reverse (fc : FCtx) (xs : List Value) :
    applyFilter fc "reverse" (.list xs) [] [] = .ok (.list xs.reverse) := by
  rw [applyFilter_builtin (f := Filters.reverse) (fun _ => by simp [builtinFilterTable, List.lookup])]
  rfl

theorem filter_join (fc : FCtx) (ss : List String) (sep : String) (hae : fc.autoescape = false) :
    applyFilter fc "join" (.list (ss.map Value.str)) [.str sep] [] = .ok (.str (sep.intercalate ss)) := by
  rw [applyFilter_builtin (f := Filters.join) (fun _ => by simp [builtinFilterTable, List.lookup])]
  simp only [Filters.join, iterOf, argAt, bind, Except.bind, pure, Except.pure, joinFilter, hae]
  have : ∀ ss : List String, (ss.map Value.str).mapM (strOf fc.pol) = .ok ss := by
    intro ss; induction ss with
    | nil => rfl
    | cons s ss ih => simp [List.mapM_cons, strOf, Value.toStr, ih, bind, Except.bind, pure, Except.pure]
  simp [this, strOf, Value.toStr]

end LeanJinja2

namespace LeanJinja2

open LeanMarkupsafe


theorem htmlsafeChar_safe (d : Char) : ∀ c ∈ (htmlsafeChar d).toList, htmlUnsafe c = false := by
  intro c hc
  unfold htmlsafeChar at hc
  split at hc
  all_goals first
    | (simp at hc; rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    | (simp at hc; subst hc; simp_all [htmlUnsafe])

/-- `htmlsafe_json_dumps`' replacement leaves none of `< > & '` in the text. -/
theorem htmlsafeJson_safe (s : String) : ∀ c ∈ (htmlsafeJson s).toList, htmlUnsafe c = false := by
  intro c hc
  simp only [htmlsafeJson, String.toList_join, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨_, ⟨d, -, rfl⟩, hc⟩ := hc
  exact htmlsafeChar_safe d c hc

/-- `tojson` returns markup without a raw `<`, `>`, `&` or `'`: safe to
interpolate in HTML and inside `<script>` (upstream `htmlsafe_json_dumps`). -/
theorem filter_tojson_htmlsafe (fc : FCtx) (v r : Value)
    (h : applyFilter fc "tojson" v [] [] = .ok r) :
    ∃ m : Markup, r = .markup m ∧ ∀ c ∈ m.str.toList, htmlUnsafe c = false := by
  rw [applyFilter_builtin (f := Filters.tojson) (fun _ => by simp [builtinFilterTable, List.lookup])] at h
  simp only [Filters.tojson, argAt, bind, Except.bind, pure, Except.pure] at h
  cases hj : jsonDump none 0 v with
  | error e => simp [hj] at h
  | ok j =>
    simp [hj] at h
    exact ⟨_, h.symm, htmlsafeJson_safe j⟩

end LeanJinja2
