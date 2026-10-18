import Std.Data.HashMap
import LeanJinja2.RepoImpl.Runtime

/-!
# De-duplication with a hash of the value

Upstream `unique` keeps a `set` of the keys seen so far. `uniqueSpec` states
it with a list of seen keys and Python equality (`Value.pyEq`), which costs a
scan of everything seen per item. `uniqueFast` buckets the seen keys by
`Value.bkey`, a hash key that equal values share (`bkey_of_pyEq`: numbers by
their integer part, text by its content), and scans one bucket.
`unique_eq_fast` proves the two equal and, as `@[csimp]`, makes compiled code
run the fast one.
-/

namespace LeanJinja2

/-- The bucket of a value: Python-equal values share it. -/
inductive BKey where
  | none
  | num (i : Int)
  | text (s : String)
  | other
  deriving DecidableEq, Hashable, Repr

def Value.bkey (v : Value) : BKey :=
  match v.num? with
  | some x => .num (x.1 / 10 ^ x.2)
  | Option.none =>
    match v.text? with
    | some t => .text t
    | Option.none => match v with
      | .none => .none
      | _ => .other

theorem text?_of_num? {v : Value} {x : Int × Nat} (h : v.num? = some x) : v.text? = Option.none := by
  cases v <;> simp_all [Value.num?, Value.text?]

theorem num?_of_text? {v : Value} {t : String} (h : v.text? = some t) : v.num? = Option.none := by
  cases v <;> simp_all [Value.num?, Value.text?]

theorem bkey_other {v : Value} (h1 : v.num? = Option.none) (h2 : v.text? = Option.none)
    (h3 : v ≠ .none) : v.bkey = .other := by
  cases v <;> simp_all [Value.bkey]

/-- Equal decimals have the same integer part. -/
theorem decCmp_floor {x y : Int × Nat} (h : decCmp x y = .eq) :
    x.1 / 10 ^ x.2 = y.1 / 10 ^ y.2 := by
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  simp only [decCmp, decAlign] at h
  by_cases hst : s = t
  · subst hst
    simp only [if_true] at h
    show a / 10 ^ s = b / 10 ^ s
    rw [Int.compare_eq_eq.mp h]
  simp only [hst, ite_false] at h
  have he : a * 10 ^ (max s t - s) = b * 10 ^ (max s t - t) := by
    exact Int.compare_eq_eq.mp h
  have hs : (10 : Int) ^ max s t = 10 ^ s * 10 ^ (max s t - s) := by
    rw [← Int.pow_add]; congr 1; omega
  have ht : (10 : Int) ^ max s t = 10 ^ t * 10 ^ (max s t - t) := by
    rw [← Int.pow_add]; congr 1; omega
  have h1 : a / 10 ^ s = a * 10 ^ (max s t - s) / 10 ^ max s t := by
    rw [hs]
    exact (Int.mul_ediv_mul_of_pos_left a (10 ^ s) (Int.pow_pos (by decide) : (0 : Int) < 10 ^ (max s t - s))).symm
  have h2 : b / 10 ^ t = b * 10 ^ (max s t - t) / 10 ^ max s t := by
    rw [ht]
    exact (Int.mul_ediv_mul_of_pos_left b (10 ^ t) (Int.pow_pos (by decide) : (0 : Int) < 10 ^ (max s t - t))).symm
  show a / 10 ^ s = b / 10 ^ t
  rw [h1, h2, he]

/-- Python-equal values share a bucket. -/
theorem bkey_of_pyEq {a b : Value} (h : Value.pyEq a b = true) : a.bkey = b.bkey := by
  rw [Value.pyEq.eq_def] at h
  split at h
  · rfl
  · simp only [beq_iff_eq] at h; subst h; rfl
  · simp only [beq_iff_eq] at h; subst h; rfl
  all_goals first
    | (simp [Value.bkey, Value.num?, Value.text?]; done)
    | skip
  rename_i hne1 hne2 hne3 hne4 hne5 hne6 hne7
  split at h
  · rename_i x y hx hy
    simp only [beq_iff_eq] at h
    simp [Value.bkey, hx, hy, decCmp_floor h]
  · split at h
    · rename_i hnn x y hx hy
      simp only [beq_iff_eq] at h
      subst h
      simp [Value.bkey, num?_of_text? hx, num?_of_text? hy, hx, hy]
    · cases h

/-- One step of `uniqueSpec`: the keys seen, and the items kept. -/
def uniqueSpecStep (key : Value → Except ValueError Value) (st : List Value × List Value) (x : Value) :
    Except ValueError (List Value × List Value) := do
  let k ← key x
  if st.1.any (fun s => Value.pyEq s k) then pure st else pure (k :: st.1, st.2 ++ [x])

/-- `unique` as upstream states it: a list of the keys seen. -/
def uniqueSpec (key : Value → Except ValueError Value) (xs : List Value) :
    Except ValueError (List Value) := do
  let (_, out) ← xs.foldlM (uniqueSpecStep key) ([], [])
  pure out

/-- One step of `uniqueFast`. -/
def uniqueStep (key : Value → Except ValueError Value) (st : Std.HashMap BKey (List Value) × Array Value)
    (x : Value) : Except ValueError (Std.HashMap BKey (List Value) × Array Value) := do
  let k ← key x
  let bucket := st.1.getD k.bkey []
  if bucket.any (fun s => Value.pyEq s k) then pure st
  else pure (st.1.insert k.bkey (k :: bucket), st.2.push x)

/-- `unique` with the seen keys bucketed by `bkey`. -/
def uniqueFast (key : Value → Except ValueError Value) (xs : List Value) :
    Except ValueError (List Value) := do
  let (_, out) ← xs.foldlM (uniqueStep key) ({}, #[])
  pure out.toList

theorem any_filter_bkey (l : List Value) (k : Value) :
    (l.filter (fun s => s.bkey == k.bkey)).any (fun s => Value.pyEq s k) =
      l.any (fun s => Value.pyEq s k) := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    by_cases hp : Value.pyEq s k = true
    · have := bkey_of_pyEq hp
      simp [List.filter_cons, this, hp]
    · simp only [Bool.not_eq_true] at hp
      by_cases hb : s.bkey = k.bkey <;> simp [List.filter_cons, hb, hp, ih]

/-- The fast state represents the specification state. -/
def UniqRel (st : List Value × List Value) (st' : Std.HashMap BKey (List Value) × Array Value) : Prop :=
  (∀ b, st'.1.getD b [] = st.1.filter (fun s => s.bkey == b)) ∧ st'.2.toList = st.2

theorem uniqueStep_rel (key : Value → Except ValueError Value) {st st'} (h : UniqRel st st') (x : Value) :
    match uniqueStep key st' x, uniqueSpecStep key st x with
    | .error e, .error e' => e = e'
    | .ok a', .ok a => UniqRel a a'
    | _, _ => False := by
  unfold uniqueStep uniqueSpecStep
  cases hk : key x with
  | error e => rfl
  | ok k =>
    have hany : (st'.1.getD k.bkey []).any (fun s => Value.pyEq s k) =
        st.1.any (fun s => Value.pyEq s k) := by
      rw [h.1, any_filter_bkey]
    simp only [bind, Except.bind, hany]
    by_cases hc : (st.1.any fun s => Value.pyEq s k) = true
    · simp only [hc, ↓reduceIte, pure, Except.pure]; exact h
    · simp only [hc, ↓reduceIte, pure, Except.pure, Bool.false_eq_true]
      refine ⟨fun b => ?_, ?_⟩
      · rw [Std.HashMap.getD_insert]
        by_cases hb : k.bkey = b
        · subst hb; simp [h.1, List.filter_cons]
        · simp [hb, h.1, List.filter_cons]
      · simp [h.2]

theorem unique_fold (key : Value → Except ValueError Value) : ∀ (xs : List Value) st st', UniqRel st st' →
    (xs.foldlM (uniqueStep key) st').map (fun r => r.2.toList) =
      (xs.foldlM (uniqueSpecStep key) st).map (fun r => r.2)
  | [], st, st', h => by simp [List.foldlM, Except.map, pure, Except.pure, h.2]
  | x :: xs, st, st', h => by
    have hs := uniqueStep_rel key h x
    simp only [List.foldlM_cons]
    revert hs
    cases uniqueStep key st' x <;> cases uniqueSpecStep key st x <;> intro hs <;> simp only at hs
    · subst hs; rfl
    · exact unique_fold key xs _ _ hs

theorem unique_eq_fast_apply (key : Value → Except ValueError Value) (xs : List Value) :
    uniqueSpec key xs = uniqueFast key xs := by
  have := unique_fold key xs ([], []) ({}, #[]) ⟨fun b => by simp, rfl⟩
  unfold uniqueSpec uniqueFast
  revert this
  generalize xs.foldlM (uniqueStep key) ({}, #[]) = r1
  generalize xs.foldlM (uniqueSpecStep key) ([], []) = r2
  intro h
  cases r1 <;> cases r2 <;> simp_all [Except.map, bind, Except.bind] <;> rfl

@[csimp] theorem unique_eq_fast : @uniqueSpec = @uniqueFast := by
  funext key xs; exact unique_eq_fast_apply key xs

/-! `unique` of a string reads its characters in place: no list of a value
per character (a 10 MB string would need hundreds of MB). -/

/-- `uniqueFast` over the characters of `s`, folding over the string itself. -/
def uniqueStr (key : Value → Except ValueError Value) (s : String) : Except ValueError (List Value) := do
  let (_, out) ← s.foldl (fun acc c => acc.bind (fun st => uniqueStep key st (.str (String.singleton c))))
    (.ok ({}, #[]))
  pure out.toList

theorem foldlM_map_bind {α β γ ε : Type} (f : α → β → Except ε α) (g : γ → β) :
    ∀ (l : List γ) (acc : Except ε α),
      acc.bind (fun st => (l.map g).foldlM f st) = l.foldl (fun acc c => acc.bind (fun st => f st (g c))) acc
  | [], acc => by cases acc <;> rfl
  | c :: l, acc => by
    rw [List.foldl_cons, ← foldlM_map_bind f g l]
    cases acc with
    | error e => rfl
    | ok st =>
      simp only [Except.bind, List.map_cons, List.foldlM_cons]
      cases f st (g c) <;> rfl

/-- `unique` of a string's characters, in place, is `unique` of its list of
characters. -/
theorem uniqueStr_eq (key : Value → Except ValueError Value) (s : String) :
    uniqueStr key s = uniqueSpec key (charValues s) := by
  rw [unique_eq_fast_apply, uniqueStr, uniqueFast, String.foldl_eq_foldl_toList, charValues,
    ← foldlM_map_bind]
  rfl

end LeanJinja2
