import LeanJinja2.DataTypes.Syntax
import LeanJinja2.RepoImpl.Chars
import LeanJinja2.RepoImpl.Cursor

/-!
# The lexer

A re-expression of upstream `jinja2.lexer.Lexer.tokeniter`, as a state
machine over `List Char`. Each step recognises a prefix of the remaining input
by its *length* and emits tokens whose `raw` is exactly that prefix (split by
`List.take`/`List.drop`), so the token stream prints back to the source
(`lex_print_roundtrip`, `Proofs/Lexer.lean`).

States (upstream's state stack): `root` (template data), and inside a
`{% %}` or `{{ }}` tag with its bracket-balancing stack. Comments and raw
blocks are recognised in one step from their start.

Whitespace control is decided here, as upstream does: `-` strips the adjacent
whitespace, `lstrip_blocks` strips the indentation before a block or comment
tag, `trim_blocks` removes the newline after a block tag. The removed
characters become `ws` tokens rather than disappearing.

This is the specification. The compiler runs `lexFast` (`LexFast.lean`), the
same machine reading the source in place, proved equal to `lex`
(`lexFast_eq`). The helpers that read a bounded prefix match on `l.take k`,
which is what lets their in-place twins read only `k` characters.
-/

namespace LeanJinja2

/-- A lexical error (upstream `TemplateSyntaxError` raised by the lexer):
message and character offset. -/
structure LexError where
  msg : String
  pos : Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Which kind of tag the lexer is inside. -/
inductive TagKind where
  | block | var
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The lexer state. -/
inductive LexMode where
  /-- Template data; `lineStart` says the previous character was a line break
  (or this is the start of input), upstream's `line_starting`. -/
  | root (lineStart : Bool)
  /-- Inside a tag. `stack` holds the closing brackets expected; `afterDot`
  says the last character was `.` (the float rule's look-behind). -/
  | tag (k : TagKind) (stack : List Char) (afterDot : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- The start of a tag found in template data. -/
inductive TagStart where
  /-- `{% raw %}` (its whole opening tag, `len` characters, strip sign). -/
  | raw (len : Nat) (sign : Option Char)
  | comment (len : Nat) (sign : Option Char)
  | block (len : Nat) (sign : Option Char)
  | var (len : Nat) (sign : Option Char)
  deriving DecidableEq, Repr, Inhabited

namespace Lex

/-- `p` is a prefix of `l`. -/
def pre (p : String) (l : List Char) : Bool := p.toList.isPrefixOf l

/-- Optional `-`/`+` whitespace-control sign after a start delimiter (it
reads one character: the match is on `l.take 1`). -/
def signAt (l : List Char) : Option Char :=
  match l.take 1 with
  | '-' :: _ => some '-'
  | '+' :: _ => some '+'
  | _ => none

def signLen : Option Char → Nat
  | some _ => 1
  | none => 0

/-- Length of the leading whitespace run. -/
def spaceLen (l : List Char) : Nat := (l.takeWhile isSpace).length

/-- `kw` followed by a non-identifier character (or the end). -/
def kwAt (kw : String) (l : List Char) : Bool :=
  pre kw l && !((l.drop kw.length).head?.map isIdentChar).getD false

/-- Upstream's block-end alternatives: `+%}` | `-%}\s*` | `%}` (+ newline
when `trim_blocks`). Returns the matched length. -/
def blockEndAt (cfg : LexConfig) (l : List Char) : Option Nat :=
  let be := cfg.blockEnd
  if l.head? == some '+' && pre be (l.drop 1) then some (1 + be.length)
  else if l.head? == some '-' && pre be (l.drop 1) then
    some (1 + be.length + spaceLen (l.drop (1 + be.length)))
  else if pre be l then
    some (be.length + (if cfg.trimBlocks then newlineLen (l.drop be.length) else 0))
  else none

/-- Upstream's variable-end alternatives: `-}}\s*` | `}}`. -/
def varEndAt (cfg : LexConfig) (l : List Char) : Option Nat :=
  let ve := cfg.variableEnd
  if l.head? == some '-' && pre ve (l.drop 1) then
    some (1 + ve.length + spaceLen (l.drop (1 + ve.length)))
  else if pre ve l then some ve.length
  else none

/-- Upstream's comment-end alternatives: `+#}` | `-#}\s*` | `#}` (+ newline
when `trim_blocks`). -/
def commentEndAt (cfg : LexConfig) (l : List Char) : Option Nat :=
  let ce := cfg.commentEnd
  if l.head? == some '+' && pre ce (l.drop 1) then some (1 + ce.length)
  else if l.head? == some '-' && pre ce (l.drop 1) then
    some (1 + ce.length + spaceLen (l.drop (1 + ce.length)))
  else if pre ce l then
    some (ce.length + (if cfg.trimBlocks then newlineLen (l.drop ce.length) else 0))
  else none

/-- `{%(-|+|)\s*raw\s*(-%}\s*|%})` at the head: its length and sign. -/
def rawBeginAt (cfg : LexConfig) (l : List Char) : Option (Nat × Option Char) :=
  if pre cfg.blockStart l then
    let n0 := cfg.blockStart.length
    let sg := signAt (l.drop n0)
    let n1 := n0 + signLen sg
    let n2 := n1 + spaceLen (l.drop n1)
    if pre "raw" (l.drop n2) then
      let n3 := n2 + 3
      let n4 := n3 + spaceLen (l.drop n3)
      let r := l.drop n4
      if r.head? == some '-' && pre cfg.blockEnd (r.drop 1) then
        let n5 := n4 + 1 + cfg.blockEnd.length
        some (n5 + spaceLen (l.drop n5), sg)
      else if pre cfg.blockEnd r then some (n4 + cfg.blockEnd.length, sg)
      else none
    else none
  else none

/-- `{%(-|+|)\s*endraw\s*(+%}|-%}\s*|%}\n?)` at the head: its length and sign. -/
def rawEndAt (cfg : LexConfig) (l : List Char) : Option (Nat × Option Char) :=
  if pre cfg.blockStart l then
    let n0 := cfg.blockStart.length
    let sg := signAt (l.drop n0)
    let n1 := n0 + signLen sg
    let n2 := n1 + spaceLen (l.drop n1)
    if pre "endraw" (l.drop n2) then
      let n3 := n2 + 6
      let n4 := n3 + spaceLen (l.drop n3)
      match blockEndAt cfg (l.drop n4) with
      | some e => some (n4 + e, sg)
      | none => none
    else none
  else none

/-- The begin delimiters, in upstream's priority order: longer first, then by
token name descending (`variable_begin`, `comment_begin`, `block_begin`). -/
def beginOrder (cfg : LexConfig) : List (Nat × String) :=
  -- rank: 2 = variable, 1 = comment, 0 = block
  let ds := [(2, cfg.variableStart), (1, cfg.commentStart), (0, cfg.blockStart)]
  let le := fun (a b : Nat × String) => a.2.length > b.2.length || (a.2.length == b.2.length && a.1 ≥ b.1)
  -- a stable insertion sort (the list has three entries)
  let rec ins (x : Nat × String) : List (Nat × String) → List (Nat × String)
    | [] => [x]
    | y :: ys => if le x y then x :: y :: ys else y :: ins x ys
  ds.foldr ins []

/-- A tag start at the head of `l`, if any. -/
def tagAt (cfg : LexConfig) (l : List Char) : Option TagStart :=
  match rawBeginAt cfg l with
  | some (n, sg) => some (.raw n sg)
  | none =>
    let rec pick : List (Nat × String) → Option TagStart
      | [] => none
      | (rank, d) :: ds =>
        if pre d l then
          let sg := signAt (l.drop d.length)
          let n := d.length + signLen sg
          some (if rank == 2 then .var n sg else if rank == 1 then .comment n sg else .block n sg)
        else pick ds
    pick (beginOrder cfg)

/-- The first tag start in `l`: the length of the text before it, and the tag. -/
def findTag (cfg : LexConfig) : List Char → Nat → Option (Nat × TagStart)
  | [], _ => none
  | l@(_ :: cs), i =>
    match tagAt cfg l with
    | some t => some (i, t)
    | none => findTag cfg cs (i + 1)

/-- The first position where `m` matches: (offset, match length). -/
def findMatch {α : Type} (m : List Char → Option α) : List Char → Nat → Option (Nat × α)
  | [], _ => none
  | l@(_ :: cs), i =>
    match m l with
    | some a => some (i, a)
    | none => findMatch m cs (i + 1)

/-- Split template text in front of a tag into (kept, stripped) lengths:
`-` strips trailing whitespace; `lstrip_blocks` strips the indentation of a
block or comment tag that starts its line (upstream `OptionalLStrip`). -/
def stripSplit (cfg : LexConfig) (isVar : Bool) (sign : Option Char) (lineStart : Bool)
    (text : List Char) : Nat :=
  if sign == some '-' then (rstripList text).length
  else if sign != some '+' && cfg.lstripBlocks && !isVar then
    let lpos := afterLastNewline text
    let tail := text.drop lpos
    if (lpos > 0 || lineStart) && !tail.isEmpty && tail.all isSpace then lpos else text.length
  else text.length

/-- `(\d+_)*\d+`: digits with single underscores between them. -/
def digitRun (base : Nat) (l : List Char) : Nat :=
  let isD := fun c => (digitVal base c).isSome
  let rec go : List Char → Nat → Nat
    | c :: cs, n =>
      if isD c then go cs (n + 1)
      else if c == '_' then
        match cs with
        | d :: _ => if isD d then go cs (n + 1) else n
        | [] => n
      else n
    | [], n => n
  match l with
  | c :: cs => if isD c then go cs 1 else 0
  | [] => 0

/-- `e[+-]?(\d+_)*\d+`. -/
def expLen (l : List Char) : Nat :=
  match l with
  | c :: cs =>
    if c == 'e' || c == 'E' then
      let s := match cs with | '+' :: _ => 1 | '-' :: _ => 1 | _ => 0
      let d := digitRun 10 (cs.drop s)
      if d > 0 then 1 + s + d else 0
    else 0
  | [] => 0

/-- `\.(\d+_)*\d+`. -/
def fracLen (l : List Char) : Nat :=
  match l with
  | '.' :: cs => if digitRun 10 cs > 0 then 1 + digitRun 10 cs else 0
  | _ => 0

/-- Upstream `float_re` at the head (without the look-behind, checked by the
caller). -/
def floatAt (l : List Char) : Option Nat :=
  let p := digitRun 10 l
  if p == 0 then none
  else
    let r := l.drop p
    let f := fracLen r
    if f > 0 && expLen (r.drop f) > 0 then some (p + f + expLen (r.drop f))
    else if expLen r > 0 then some (p + expLen r)
    else if f > 0 then some (p + f)
    else none

/-- The decimal value of a float literal: (mantissa, scale). -/
def floatValue (raw : List Char) : Nat × Nat :=
  let intPart := raw.takeWhile (fun c => c != '.' && c != 'e' && c != 'E')
  let rest := raw.drop intPart.length
  let fracPart :=
    if rest.head? == some '.' then (rest.drop 1).takeWhile (fun c => c != 'e' && c != 'E') else []
  let rest2 := if rest.head? == some '.' then rest.drop (1 + fracPart.length) else rest
  let expNeg := (rest2.drop 1).head? == some '-'
  let expDigits := (rest2.drop 1).filter (fun c => c.isDigit)
  let e := digitsValue 10 expDigits
  let fdigits := fracPart.filter (· != '_')
  let m := digitsValue 10 (intPart ++ fdigits)
  let f := fdigits.length
  if expNeg then (m, f + e)
  else if e ≥ f then (m * 10 ^ (e - f), 0) else (m, f - e)

/-- `(_?d)+` for the digits of a prefixed integer. -/
def prefixedRun (base : Nat) : List Char → Nat
  | '_' :: d :: cs => if (digitVal base d).isSome then 2 + prefixedRun base cs else 0
  | d :: cs => if (digitVal base d).isSome then 1 + prefixedRun base cs else 0
  | [] => 0

/-- Upstream `integer_re` at the head: length and value. -/
def intAt (l : List Char) : Option (Nat × Nat) :=
  match l with
  | '0' :: c :: cs =>
    let pfx := fun (base : Nat) =>
      let n := prefixedRun base cs
      if n > 0 then some (2 + n, digitsValue base (cs.take n)) else none
    let zeros : Option (Nat × Nat) :=
      let rec z : List Char → Nat
        | '_' :: '0' :: r => 2 + z r
        | '0' :: r => 1 + z r
        | _ => 0
      some (1 + z (c :: cs), 0)
    if c == 'b' || c == 'B' then (pfx 2).orElse (fun _ => zeros)
    else if c == 'o' || c == 'O' then (pfx 8).orElse (fun _ => zeros)
    else if c == 'x' || c == 'X' then (pfx 16).orElse (fun _ => zeros)
    else zeros
  | ['0'] => some (1, 0)
  | c :: _ =>
    if '1' ≤ c ∧ c ≤ '9' then
      let n := digitRun 10 l
      some (n, digitsValue 10 (l.take n))
    else none
  | [] => none

/-- Upstream `name_re` at the head. -/
def nameLen (l : List Char) : Nat := (l.takeWhile isIdentChar).length

/-- Upstream `string_re` at the head: the length of the whole literal,
quotes included. -/
def stringAt (l : List Char) : Option Nat :=
  match l with
  | q :: cs =>
    if q == '\'' || q == '"' then
      let rec go : List Char → Nat → Option Nat
        | [], _ => none
        | '\\' :: _ :: r, n => go r (n + 2)
        | c :: r, n => if c == q then some (n + 1) else go r (n + 1)
      go cs 1
    else none
  | [] => none

/-- Hex digits to a number, requiring exactly `k` of them. -/
def hexN (k : Nat) (l : List Char) : Option Nat :=
  let ds := l.take k
  if ds.length == k && ds.all (fun c => (digitVal 16 c).isSome) then some (digitsValue 16 ds)
  else none

/-- Resolve the escapes of a string literal's content (upstream decodes with
Python's `unicode-escape`). An unknown escape keeps its backslash. -/
def unescapeStr : List Char → Except String (List Char)
  | [] => .ok []
  | '\\' :: c :: r =>
    let simple := fun (x : Char) => do let t ← unescapeStr r; pure (x :: t)
    match c with
    | '\\' => simple '\\' | '\'' => simple '\'' | '"' => simple '"'
    | 'a' => simple '\x07' | 'b' => simple '\x08' | 'f' => simple '\x0c'
    | 'n' => simple '\n' | 'r' => simple '\r' | 't' => simple '\t' | 'v' => simple '\x0b'
    | '\n' => unescapeStr r
    | 'x' => match hexN 2 r with
      | some v => do let t ← unescapeStr (r.drop 2); pure (Char.ofNat v :: t)
      | none => .error "truncated \\xXX escape"
    | 'u' => match hexN 4 r with
      | some v => do let t ← unescapeStr (r.drop 4); pure (Char.ofNat v :: t)
      | none => .error "truncated \\uXXXX escape"
    | 'U' => match hexN 8 r with
      | some v =>
        if v > 0x10FFFF then .error "illegal Unicode character"
        else do let t ← unescapeStr (r.drop 8); pure (Char.ofNat v :: t)
      | none => .error "truncated \\UXXXXXXXX escape"
    | 'N' => .error "\\N{...} escapes are not supported"
    | _ =>
      if '0' ≤ c ∧ c ≤ '7' then
        let more := (r.take 2).takeWhile (fun d => '0' ≤ d ∧ d ≤ '7')
        let v := digitsValue 8 (c :: more)
        do let t ← unescapeStr (r.drop more.length); pure (Char.ofNat v :: t)
      else do let t ← unescapeStr r; pure ('\\' :: c :: t)
  | c :: r => do let t ← unescapeStr r; pure (c :: t)
termination_by l => l.length
decreasing_by all_goals simp_all <;> omega

/-- A position no further from the end than `r`. -/
abbrev PosLE {s : String.Slice} (r : s.Pos) := {r' : s.Pos // (Cursor.rest r').length ≤ (Cursor.rest r).length}

def PosLE.self {s : String.Slice} (r : s.Pos) : PosLE r := ⟨r, Nat.le_refl _⟩

def PosLE.adv {s : String.Slice} (r : s.Pos) (k : Nat) : PosLE r :=
  ⟨Cursor.advN r k, by rw [Cursor.rest_advN, List.length_drop]; omega⟩

/-- One escape `\c2...` with `r` after `c2`: the characters it stands for
and where the rest starts (`unescapeStr`'s `'\\' :: c :: r` case). -/
def escape1 {s : String.Slice} (c2 : Char) (r : s.Pos) : Except String (List Char × PosLE r) :=
  match c2 with
  | '\\' => .ok (['\\'], .self r) | '\'' => .ok (['\''], .self r) | '"' => .ok (['"'], .self r)
  | 'a' => .ok (['\x07'], .self r) | 'b' => .ok (['\x08'], .self r) | 'f' => .ok (['\x0c'], .self r)
  | 'n' => .ok (['\n'], .self r) | 'r' => .ok (['\r'], .self r) | 't' => .ok (['\t'], .self r)
  | 'v' => .ok (['\x0b'], .self r)
  | '\n' => .ok ([], .self r)
  | 'x' => match hexN 2 (Cursor.takeL r 2) with
    | some v => .ok ([Char.ofNat v], .adv r 2)
    | none => .error "truncated \\xXX escape"
  | 'u' => match hexN 4 (Cursor.takeL r 4) with
    | some v => .ok ([Char.ofNat v], .adv r 4)
    | none => .error "truncated \\uXXXX escape"
  | 'U' => match hexN 8 (Cursor.takeL r 8) with
    | some v => if v > 0x10FFFF then .error "illegal Unicode character" else .ok ([Char.ofNat v], .adv r 8)
    | none => .error "truncated \\UXXXXXXXX escape"
  | 'N' => .error "\\N{...} escapes are not supported"
  | c2 =>
    if '0' ≤ c2 ∧ c2 ≤ '7' then
      let more := (Cursor.takeL r 2).takeWhile (fun d => '0' ≤ d ∧ d ≤ '7')
      .ok ([Char.ofNat (digitsValue 8 (c2 :: more))], .adv r more.length)
    else .ok (['\\', c2], .self r)

/-- `unescapeStr` as it runs: over a string in place, the text built in a
`String`, tail recursive. `unescapeStr_eq_TR` proves them equal. -/
def unescF {s : String.Slice} (p : s.Pos) (acc : String) : Except String String :=
  if h : p = s.endPos then .ok acc
  else
    let c := p.get h
    let q := p.next h
    if c == '\\' then
      if h2 : q = s.endPos then .ok (acc.push '\\')
      else
        match escape1 (q.get h2) (q.next h2) with
        | .error e => .error e
        | .ok (out, r') => unescF r'.1 (out.foldl String.push acc)
    else unescF q (acc.push c)
termination_by (Cursor.rest p).length
decreasing_by
  · exact Nat.lt_of_le_of_lt r'.2
      (Nat.lt_trans (Cursor.rest_next_length q h2) (Cursor.rest_next_length p h))
  · exact Cursor.rest_next_length p h

theorem hexN_take (k : Nat) (l : List Char) : hexN k (l.take k) = hexN k l := by
  simp [hexN, List.take_take]

theorem bind_cons (u : Except String (List Char)) (x : List Char) :
    (do let t ← u; pure (x ++ t)) = u.map (x ++ ·) := by
  cases u <;> rfl

set_option linter.unusedSimpArgs false in
/-- `escape1` computes `unescapeStr`'s escape step. -/
theorem escape1_eq {s : String.Slice} (c2 : Char) (r : s.Pos) :
    unescapeStr ('\\' :: c2 :: Cursor.rest r) =
      (escape1 c2 r).bind (fun x => (unescapeStr (Cursor.rest x.2.1)).map (x.1 ++ ·)) := by
  unfold escape1
  split
  all_goals simp only [unescapeStr.eq_2, unescapeStr.eq_3, unescapeStr.eq_4, unescapeStr.eq_5,
    unescapeStr.eq_6, unescapeStr.eq_7, unescapeStr.eq_8, unescapeStr.eq_9, unescapeStr.eq_10,
    unescapeStr.eq_11, unescapeStr.eq_12, unescapeStr.eq_13, unescapeStr.eq_14, unescapeStr.eq_15,
    unescapeStr.eq_16, Cursor.takeL_eq, hexN_take, PosLE.self, PosLE.adv, Cursor.rest_advN]
  case h_16 =>
    rw [unescapeStr.eq_17 _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›]
    split
    · simp only [Except.bind, Cursor.takeL_eq, Cursor.rest_advN]
      cases unescapeStr _ <;> rfl
    · simp only [Except.bind]
      cases unescapeStr _ <;> rfl
  all_goals (try simp only [Except.bind, Cursor.rest_advN])
  all_goals (try split)
  all_goals (try simp only [Except.bind, Cursor.rest_advN])
  all_goals (try split)
  all_goals first
    | with_reducible rfl
    | (cases unescapeStr _ <;> rfl)
    | (simp only [Cursor.rest_advN]; cases unescapeStr _ <;> rfl)

theorem push_foldl (out : List Char) (acc : String) :
    out.foldl String.push acc = acc ++ String.ofList out := by
  induction out generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    apply String.ext
    simp [String.toList_push]

theorem unescF_eq {s : String.Slice} (p : s.Pos) (acc : String) :
    unescF p acc = (unescapeStr (Cursor.rest p)).map (fun t => acc ++ String.ofList t) := by
  induction h : (Cursor.rest p).length using Nat.strongRecOn generalizing p acc with
  | _ n ih =>
  unfold unescF
  by_cases hp : p = s.endPos
  · subst hp; simp [Cursor.rest_endPos, unescapeStr, Except.map]
  simp only [hp, ↓reduceDIte]
  have hr := Cursor.rest_next p hp
  by_cases hb : p.get hp = '\\'
  · simp only [hb, beq_self_eq_true, ↓reduceIte]
    rw [hb] at hr
    by_cases hq : p.next hp = s.endPos
    · simp only [hq, ↓reduceDIte]
      rw [hr, hq, Cursor.rest_endPos, unescapeStr.eq_18 _ _ (fun _ _ _ h => by cases h),
        unescapeStr.eq_1]
      simp only [Except.map, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
      apply String.ext; simp [String.toList_push]
    · simp only [hq, ↓reduceDIte]
      rw [hr, Cursor.rest_next _ hq, escape1_eq]
      cases he : escape1 ((p.next hp).get hq) ((p.next hp).next hq) with
      | error e => rfl
      | ok x =>
        obtain ⟨out, r', hr'⟩ := x
        simp only [Except.bind]
        have hlt : (Cursor.rest r').length < n := by
          rw [← h, hr, Cursor.rest_next _ hq]; simp at hr' ⊢; omega
        rw [ih _ hlt r' _ rfl, push_foldl]
        cases unescapeStr (Cursor.rest r') with
        | error e => rfl
        | ok t =>
          simp only [Except.map, Except.ok.injEq]
          apply String.ext; simp
  · have hne : (p.get hp == '\\') = false := by simpa using hb
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    have hlt : (Cursor.rest (p.next hp)).length < n := by rw [← h, hr]; simp
    rw [hr, unescapeStr.eq_18 _ _ (fun _ _ h _ => hb h), ih _ hlt _ _ rfl]
    cases unescapeStr (Cursor.rest (p.next hp)) with
    | error e => rfl
    | ok t =>
      simp only [Except.map, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
      apply String.ext; simp [String.toList_push]

/-- `unescapeStr` as it runs (`unescF` over the text, in place). -/
def unescapeStrTR (l : List Char) : Except String (List Char) :=
  (unescF (String.ofList l).toSlice.startPos "").map String.toList

@[csimp] theorem unescapeStr_eq_TR : @unescapeStr = @unescapeStrTR := by
  funext l
  rw [unescapeStrTR, unescF_eq, Cursor.rest_startPos, String.copy_toSlice, String.toList_ofList]
  cases unescapeStr l <;> simp [Except.map]

/-- The two-character operators, then the one-character ones (it reads two
characters: the match is on `l.take 2`). -/
def opAt (l : List Char) : Option (Nat × Op) :=
  match l.take 2 with
  | '/' :: '/' :: _ => some (2, .floordiv)
  | '*' :: '*' :: _ => some (2, .pow)
  | '=' :: '=' :: _ => some (2, .eq)
  | '!' :: '=' :: _ => some (2, .ne)
  | '>' :: '=' :: _ => some (2, .gteq)
  | '<' :: '=' :: _ => some (2, .lteq)
  | '+' :: _ => some (1, .add) | '-' :: _ => some (1, .sub) | '/' :: _ => some (1, .div)
  | '*' :: _ => some (1, .mul) | '%' :: _ => some (1, .mod) | '~' :: _ => some (1, .tilde)
  | '[' :: _ => some (1, .lbracket) | ']' :: _ => some (1, .rbracket)
  | '(' :: _ => some (1, .lparen) | ')' :: _ => some (1, .rparen)
  | '{' :: _ => some (1, .lbrace) | '}' :: _ => some (1, .rbrace)
  | '>' :: _ => some (1, .gt) | '<' :: _ => some (1, .lt) | '=' :: _ => some (1, .assign)
  | '.' :: _ => some (1, .dot) | ':' :: _ => some (1, .colon) | '|' :: _ => some (1, .pipe)
  | ',' :: _ => some (1, .comma) | ';' :: _ => some (1, .semicolon)
  | _ => none

/-- Cut a token of `n` characters off the head of `l`. -/
def cut (k : TokKind) (n : Nat) (l : List Char) : List Token × List Char :=
  ([⟨k, l.take n⟩], l.drop n)

/-- Cut a token of `n` characters, or nothing when `n = 0`. -/
def cutOpt (k : TokKind) (n : Nat) (l : List Char) : List Token × List Char :=
  if n = 0 then ([], l) else cut k n l

/-- Cut template data: its value is the newline-normalised text. -/
def cutData (cfg : LexConfig) (n : Nat) (l : List Char) : List Token × List Char :=
  cutOpt (.data (String.ofList (normalizeNewlines cfg.newlineSequence.toList (l.take n)))) n l

/-- Run two cutters in sequence. -/
def seq (a : List Char → List Token × List Char) (b : List Char → List Token × List Char)
    (l : List Char) : List Token × List Char :=
  ((a l).1 ++ (b (a l).2).1, (b (a l).2).2)

/-- Emit the tokens a cutter produces and continue in mode `m`. -/
def emit (f : List Char → List Token × List Char) (m : LexMode) (l : List Char) :
    Except LexError (List Token × LexMode × List Char) :=
  .ok ((f l).1, m, (f l).2)

/-- Whether the characters end with a line break. -/
def endsNewline (l : List Char) : Bool := (l.getLast?.map isNewline).getD false

/-- The value of the string literal of `n` characters at the head of `l`:
its content with newlines normalised and escapes resolved. -/
def strValue (cfg : LexConfig) (l : List Char) (n : Nat) : Except String String :=
  (unescapeStr (normalizeNewlines cfg.newlineSequence.toList ((l.take n).drop 1 |>.dropLast))).map
    String.ofList

/-- The kind of a bracket closer, or none. -/
def closerOf : Op → Option Char
  | .lparen => some ')' | .lbracket => some ']' | .lbrace => some '}' | _ => none

def isCloser : Op → Option Char
  | .rparen => some ')' | .rbracket => some ']' | .rbrace => some '}' | _ => none

/-- One step in `root` mode on non-empty input. -/
def stepRoot (cfg : LexConfig) (lineStart : Bool) (l : List Char) (pos : Nat) :
    Except LexError (List Token × LexMode × List Char) :=
  match findTag cfg l 0 with
  | none =>
    emit (cutData cfg l.length) (.root false) l
  | some (i, t) =>
    let text := l.take i
    let (isVar, sign) := match t with
      | .raw _ s => (false, s) | .comment _ s => (false, s)
      | .block _ s => (false, s) | .var _ s => (true, s)
    let keep := stripSplit cfg isVar sign lineStart text
    let pre := seq (cutData cfg keep) (cutOpt .ws (i - keep))
    match t with
    | .var n _ =>
      emit (seq pre (cut .varBegin n)) (.tag .var [] false) l
    | .block n _ =>
      emit (seq pre (cut .blockBegin n)) (.tag .block [] false) l
    | .comment n _ =>
      let body := l.drop (i + n)
      match findMatch (commentEndAt cfg) body 0 with
      | none => .error ⟨"Missing end of comment tag", pos + i⟩
      | some (j, e) =>
        emit (seq pre (cut .comment (n + j + e))) (.root (endsNewline (l.take (i + n + j + e)))) l
    | .raw n _ =>
      let body := l.drop (i + n)
      match findMatch (rawEndAt cfg) body 0 with
      | none => .error ⟨"Missing end of raw directive", pos + i⟩
      | some (j, (e, esign)) =>
        let inner := body.take j
        let keep2 := stripSplit cfg false esign (endsNewline (l.take (i + n))) inner
        emit (seq pre (seq (cut .rawBegin n)
            (seq (cutData cfg keep2) (seq (cutOpt .ws (j - keep2)) (cut .rawEnd e)))))
          (.root (endsNewline (l.take (i + n + j + e)))) l

/-- One step inside a tag on non-empty input. -/
def stepTag (cfg : LexConfig) (k : TagKind) (stack : List Char) (afterDot : Bool)
    (l : List Char) (pos : Nat) : Except LexError (List Token × LexMode × List Char) :=
  let endM := if stack.isEmpty then
      (match k with | .block => blockEndAt cfg l | .var => varEndAt cfg l)
    else none
  match endM with
  | some n =>
    emit (cut (match k with | .block => .blockEnd | .var => .varEnd) n) (.root (endsNewline (l.take n))) l
  | none =>
    let sp := spaceLen l
    if sp > 0 then
      emit (cut .ws sp) (.tag k stack false) l
    else
    match (if afterDot then none else floatAt l) with
    | some n =>
      emit (cut (.float (floatValue (l.take n)).1 (floatValue (l.take n)).2) n) (.tag k stack false) l
    | none =>
    match intAt l with
    | some (n, v) =>
      emit (cut (.int v) n) (.tag k stack false) l
    | none =>
    let nl := nameLen l
    if nl > 0 && l.head? == some '\xb7' then .error ⟨"Invalid character in identifier", pos⟩
    else if nl > 0 then
      emit (cut (.name (String.ofList (l.take nl))) nl) (.tag k stack false) l
    else
    match stringAt l with
    | some n =>
      match strValue cfg l n with
      | .error e => .error ⟨e, pos⟩
      | .ok v =>
        emit (cut (.str v) n) (.tag k stack false) l
    | none =>
    match opAt l with
    | some (n, o) =>
      let stack' : Except LexError (List Char) :=
        match closerOf o, isCloser o with
        | some c, _ => .ok (c :: stack)
        | none, some c =>
          match stack with
          | [] => .error ⟨s!"unexpected '{c}'", pos⟩
          | e :: st => if e == c then .ok st else .error ⟨s!"unexpected '{c}', expected '{e}'", pos⟩
        | none, none => .ok stack
      match stack' with
      | .error e => .error e
      | .ok st =>
        emit (cut (.op o) n) (.tag k st (o == .dot)) l
    | none =>
      .error ⟨s!"unexpected char {repr (l.headD ' ')} at {pos}", pos⟩

/-- One lexer step on non-empty input. -/
def step (cfg : LexConfig) (m : LexMode) (l : List Char) (pos : Nat) :
    Except LexError (List Token × LexMode × List Char) :=
  match m with
  | .root ls => stepRoot cfg ls l pos
  | .tag k st ad => stepTag cfg k st ad l pos

/-- How many characters a step's tokens cover. -/
def consumed (ts : List Token) : Nat := ts.foldl (fun n t => n + t.raw.length) 0

/-- The lexer loop: `fuel` bounds the number of steps (the input length
suffices, every step consumes a character). Tail recursive, with the tokens
so far in reverse in `acc`, so it runs in constant stack and linear time. -/
def loop (cfg : LexConfig) : Nat → LexMode → List Char → Nat → List Token → Except LexError (List Token)
  | _, _, [], _, acc => .ok acc.reverse
  | 0, _, _ :: _, pos, _ => .error ⟨"lexer step bound exceeded", pos⟩
  | fuel + 1, m, l@(_ :: _), pos, acc =>
    match step cfg m l pos with
    | .error e => .error e
    | .ok (ts, m', r) => loop cfg fuel m' r (pos + consumed ts) (ts.reverse ++ acc)

/-- The trailing newline upstream strips from the source (unless
`keep_trailing_newline`): its length. It reads the last two characters (the
match is on `l.reverse.take 2`). -/
def trailingNewlineLen (cfg : LexConfig) (l : List Char) : Nat :=
  if cfg.keepTrailingNewline then 0
  else match l.reverse.take 2 with
    | '\n' :: '\r' :: _ => 2
    | '\n' :: _ => 1
    | '\r' :: _ => 1
    | _ => 0

end Lex

/-- Tokenize a character list. -/
def lexList (cfg : LexConfig) (l : List Char) : Except LexError (List Token) :=
  let k := Lex.trailingNewlineLen cfg l
  let body := l.take (l.length - k)
  match Lex.loop cfg (body.length + 1) (.root true) body 0 [] with
  | .error e => .error e
  | .ok ts => .ok (ts ++ (if k = 0 then [] else [⟨.ws, l.drop (l.length - k)⟩]))

/-- Tokenize template source (upstream `Lexer.tokeniter`, plus the tokens it
drops). -/
def lex (cfg : LexConfig) (s : String) : Except LexError (List Token) := lexList cfg s.toList

end LeanJinja2
