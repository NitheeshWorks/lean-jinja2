import LeanJinja2.RepoImpl.Lexer
import LeanJinja2.RepoImpl.Cursor

/-!
# The lexer, in place

`Lexer.lean` is the lexer's specification: a state machine over `List Char`,
with the proofs (`lex_print_roundtrip`, `parse_pretty_roundtrip`) stated
about it. Run as is, it holds the source as a list (24 bytes a character) and
copies runs of template data several times, which is 110 bytes per input byte
on plain text.

This file is the same machine reading the source in place: positions of a
`String.Slice` (see `Cursor.lean`), template data built straight into a
`String`, and tokens that keep only their kind and length (`TokL`), which is
all the compiler needs. Each helper mirrors the specification's helper of the
same name, with `l` replaced by a position `p` and `l.drop n` by
`advN p n`; `Proofs/LexFast.lean` proves each one equal to its original at
`rest p`, and so `lexFast cfg s = (lex cfg s).map (·.map Token.light)`
(`lexFast_eq`).

Every loop is tail recursive, every token costs time linear in its length,
and the only per-token lists are those of short literals (numbers, string
literals) the specification decodes from a list.
-/

namespace LeanJinja2

open String Cursor

/-- A token as the compiler sees it: its kind and how many source
characters it covers. -/
structure TokL where
  kind : TokKind
  len : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The compiler's view of a token. -/
def Token.light (t : Token) : TokL := ⟨t.kind, t.raw.length⟩

/-- The tokens the parser reads (`significant`, for `TokL`). -/
def significantL (ts : List TokL) : List TokKind :=
  (ts.filter (fun t => !t.kind.ignored)).map TokL.kind

namespace LexF

variable {s : Slice}

/-! ## Small lookahead -/

def pre (d : String) (p : s.Pos) : Bool := preW p d.toList

def signAt (p : s.Pos) : Option Char := Lex.signAt (takeL p 1)

def spaceLen (p : s.Pos) : Nat := countWhile isSpace p 0

def newlineLenAt (p : s.Pos) : Nat := newlineLen (takeL p 2)

def blockEndAt (cfg : LexConfig) (p : s.Pos) : Option Nat :=
  let be := cfg.blockEnd
  if peek p == some '+' && pre be (advN p 1) then some (1 + be.length)
  else if peek p == some '-' && pre be (advN p 1) then
    some (1 + be.length + spaceLen (advN p (1 + be.length)))
  else if pre be p then
    some (be.length + (if cfg.trimBlocks then newlineLenAt (advN p be.length) else 0))
  else none

def varEndAt (cfg : LexConfig) (p : s.Pos) : Option Nat :=
  let ve := cfg.variableEnd
  if peek p == some '-' && pre ve (advN p 1) then
    some (1 + ve.length + spaceLen (advN p (1 + ve.length)))
  else if pre ve p then some ve.length
  else none

def commentEndAt (cfg : LexConfig) (p : s.Pos) : Option Nat :=
  let ce := cfg.commentEnd
  if peek p == some '+' && pre ce (advN p 1) then some (1 + ce.length)
  else if peek p == some '-' && pre ce (advN p 1) then
    some (1 + ce.length + spaceLen (advN p (1 + ce.length)))
  else if pre ce p then
    some (ce.length + (if cfg.trimBlocks then newlineLenAt (advN p ce.length) else 0))
  else none

def rawBeginAt (cfg : LexConfig) (p : s.Pos) : Option (Nat × Option Char) :=
  if pre cfg.blockStart p then
    let n0 := cfg.blockStart.length
    let sg := signAt (advN p n0)
    let n1 := n0 + Lex.signLen sg
    let n2 := n1 + spaceLen (advN p n1)
    if pre "raw" (advN p n2) then
      let n3 := n2 + 3
      let n4 := n3 + spaceLen (advN p n3)
      let r := advN p n4
      if peek r == some '-' && pre cfg.blockEnd (advN r 1) then
        let n5 := n4 + 1 + cfg.blockEnd.length
        some (n5 + spaceLen (advN p n5), sg)
      else if pre cfg.blockEnd r then some (n4 + cfg.blockEnd.length, sg)
      else none
    else none
  else none

def rawEndAt (cfg : LexConfig) (p : s.Pos) : Option (Nat × Option Char) :=
  if pre cfg.blockStart p then
    let n0 := cfg.blockStart.length
    let sg := signAt (advN p n0)
    let n1 := n0 + Lex.signLen sg
    let n2 := n1 + spaceLen (advN p n1)
    if pre "endraw" (advN p n2) then
      let n3 := n2 + 6
      let n4 := n3 + spaceLen (advN p n3)
      match blockEndAt cfg (advN p n4) with
      | some e => some (n4 + e, sg)
      | none => none
    else none
  else none

def lastPre (d : List Char) (p : s.Pos) (n i : Nat) (acc : Option Nat) : Option Nat :=
  let acc := if preW p d then some i else acc
  match n with
  | n + 1 => if h : p = s.endPos then acc else lastPre d (p.next h) n (i + 1) acc
  | 0 => acc

def linePrefixAt (cls : Char → Bool) (d : List Char) (p : s.Pos) : Option (Nat × Option Char) :=
  match lastPre d p (countWhile cls p 0) 0 none with
  | some k =>
    let sg := signAt (advN p (k + d.length))
    some (k + d.length + Lex.signLen sg, sg)
  | none => none

/-- `Lex.ruleAt`, with the delimiter as a list (converted once, by `ctx`). -/
def ruleAt (prev : Prev) (p : s.Pos) (rank : Nat) (d : List Char) : Option TagStart :=
  if rank == 3 then
    if prev == .line then (linePrefixAt Lex.isIndent d p).map (fun r => .lineStmt r.1 r.2) else none
  else if rank == 2 then
    if prev != .space then (linePrefixAt Lex.isBlank d p).map (fun r => .lineComment r.1 r.2) else none
  else if preW p d then
    let sg := signAt (advN p d.length)
    let n := d.length + Lex.signLen sg
    some (if rank == 4 then .var n sg else if rank == 1 then .comment n sg else .block n sg)
  else none

def pick (prev : Prev) (p : s.Pos) : List (Nat × List Char) → Option TagStart
  | [] => none
  | (rank, d) :: ds =>
    match ruleAt prev p rank d with
    | some t => some t
    | none => pick prev p ds

/-- `Lex.tagAt`, with the rule order `ord` (`Lex.beginOrder cfg`, delimiters
as lists) computed once by the caller. -/
def tagAt (cfg : LexConfig) (bs : List Char) (ord : List (Nat × List Char)) (prev : Prev) (p : s.Pos) :
    Option TagStart :=
  match (if preW p bs then rawBeginAt cfg p else none) with
  | some (n, sg) => some (.raw n sg)
  | none => pick prev p ord

/-- The characters a tag can start with: the first character of each begin
delimiter (`none` for an empty one, which would match anywhere). -/
def cands (cfg : LexConfig) : List (Option Char) :=
  (cfg.blockStart :: (Lex.beginOrder cfg).map Prod.snd).map (·.toList.head?)

/-- `c` may start a delimiter whose first character is `o` (`none`: an empty
delimiter, which matches anywhere). -/
def candOne : Option Char → Char → Bool
  | none, _ => true
  | some d, c => d == c

/-- `c` may start one of the delimiters (no closure per character). -/
def isCand : List (Option Char) → Char → Bool
  | [], _ => false
  | o :: os, c => candOne o c || isCand os c

/-- Whether a line prefix is set (then a run of whitespace may start a line
rule). -/
def lineOn (cfg : LexConfig) : Bool := cfg.lineStatementPrefix.isSome || cfg.lineCommentPrefix.isSome

/-- What the scan for tags computes once per template: the candidate first
characters, whether line rules are on, and the rule order. -/
structure Ctx where
  cs : List (Option Char)
  lc : Bool
  ord : List (Nat × List Char)
  bs : List Char

def ctx (cfg : LexConfig) : Ctx :=
  ⟨cands cfg, lineOn cfg, (Lex.beginOrder cfg).map (fun x => (x.1, x.2.toList)), cfg.blockStart.toList⟩

/-- The first tag start from `p`, counting from `i`; when there is none, the
count at the end (`i` plus the characters left). Only positions holding a
delimiter's first character, or (`lc`, with a line prefix set) starting a
run of whitespace, are tried. Without line rules the class of the previous
character is not needed, and not computed. -/
def findTag (cfg : LexConfig) (k : Ctx) (prev : Prev) (p : s.Pos) (i : Nat) :
    Except Nat (Nat × TagStart) :=
  if h : p = s.endPos then .error i
  else
    let c := p.get h
    if isCand k.cs c || (k.lc && prev != .space && isSpace c) then
      match tagAt cfg k.bs k.ord prev p with
      | some t => .ok (i, t)
      | none => findTag cfg k (if k.lc then prevClass c else .text) (p.next h) (i + 1)
    else findTag cfg k (if k.lc then prevClass c else .text) (p.next h) (i + 1)
termination_by (rest p).length
decreasing_by all_goals exact rest_next_length p h

/-- The first position from `p` where `m` matches, counting from `i`. -/
def findMatch {α : Type} (m : s.Pos → Option α) (p : s.Pos) (i : Nat) : Option (Nat × α) :=
  if h : p = s.endPos then none
  else match m p with
    | some a => some (i, a)
    | none => findMatch m (p.next h) (i + 1)
termination_by (rest p).length
decreasing_by exact rest_next_length p h

/-- `findMatch`, trying `m` only where `cand` holds of the character (the
others cannot start a match). -/
def findMatchC {α : Type} (cand : Char → Bool) (m : s.Pos → Option α) (p : s.Pos) (i : Nat) :
    Option (Nat × α) :=
  if h : p = s.endPos then none
  else if cand (p.get h) then
    match m p with
    | some a => some (i, a)
    | none => findMatchC cand m (p.next h) (i + 1)
  else findMatchC cand m (p.next h) (i + 1)
termination_by (rest p).length
decreasing_by all_goals exact rest_next_length p h

/-- The characters a comment end can start with, given the first character
of the comment end delimiter (computed once, by the caller). -/
def commentCand (h : Option Char) (c : Char) : Bool := c == '+' || c == '-' || candOne h c

/-! ## Statistics of a run of text -/

/-- `rstrip` as a fold: (kept length, pending whitespace). -/
def rstripStep : Nat × Nat → Char → Nat × Nat
  | (k, w), c => if isSpace c then (k, w + 1) else (k + w + 1, 0)

/-- `afterLastNewline` as a fold: (index, answer). -/
def nlStep : Nat × Nat → Char → Nat × Nat
  | (i, acc), c => (i + 1, if isNewline c then i + 1 else acc)

/-- Whether everything after the last line break is whitespace, as a fold. -/
def tailSpaceStep (b : Bool) (c : Char) : Bool := if isNewline c then true else b && isSpace c

def lenStep (n : Nat) (_ : Char) : Nat := n + 1

/-- `Lex.stripSplit` on the `n` characters at `p`. -/
def stripSplit (cfg : LexConfig) (isVar : Bool) (sign : Option Char) (lineStart : Bool)
    (p : s.Pos) (n : Nat) : Nat :=
  if sign == some '-' then (foldTake rstripStep (0, 0) p n).1
  else if sign != some '+' && cfg.lstripBlocks && !isVar then
    let lpos := (foldTake nlStep (0, 0) p n).2
    let len := foldTake lenStep 0 p n
    if (lpos > 0 || lineStart) && !(decide (len ≤ lpos)) && foldTake tailSpaceStep true p n
    then lpos else len
  else foldTake lenStep 0 p n

/-- The class of the last of the `n` characters at `p`. -/
def prevOf (p : s.Pos) (n : Nat) : Prev := foldTake (fun _ c => prevClass c) .text p n

/-- `Lex.lineEndAt` in place. -/
def lineEndAt (p : s.Pos) : Option Nat :=
  let w := spaceLen p
  if (peek (advN p w)).isNone then some w
  else
    let k := (foldTake nlStep (0, 0) p w).2
    if k > 0 then some k else none

def lineRest (p : s.Pos) : Nat := countWhile (fun c => !isNewline c) p 0

/-! ## Literals inside tags -/

def isD (base : Nat) (c : Char) : Bool := (digitVal base c).isSome

def digitRunGo (base : Nat) (p : s.Pos) (n : Nat) : Nat :=
  if h : p = s.endPos then n
  else
    let c := p.get h
    if isD base c then digitRunGo base (p.next h) (n + 1)
    else if c == '_' then
      match peek (p.next h) with
      | some d => if isD base d then digitRunGo base (p.next h) (n + 1) else n
      | none => n
    else n
termination_by (rest p).length
decreasing_by all_goals exact rest_next_length p h

def digitRun (base : Nat) (p : s.Pos) : Nat :=
  match peek p with
  | some c => if isD base c then digitRunGo base (adv p) 1 else 0
  | none => 0

def expLen (p : s.Pos) : Nat :=
  match peek p with
  | some c =>
    if c == 'e' || c == 'E' then
      let q := adv p
      let sg := match peek q with | some '+' => 1 | some '-' => 1 | _ => 0
      let d := digitRun 10 (advN q sg)
      if d > 0 then 1 + sg + d else 0
    else 0
  | none => 0

def fracLen (p : s.Pos) : Nat :=
  match peek p with
  | some '.' => if digitRun 10 (adv p) > 0 then 1 + digitRun 10 (adv p) else 0
  | _ => 0

def floatAt (p : s.Pos) : Option Nat :=
  let n := digitRun 10 p
  if n == 0 then none
  else
    let r := advN p n
    let f := fracLen r
    if f > 0 && expLen (advN r f) > 0 then some (n + f + expLen (advN r f))
    else if expLen r > 0 then some (n + expLen r)
    else if f > 0 then some (n + f)
    else none

/-- `Lex.prefixedRun`, with an accumulator. -/
def prefixedRun (base : Nat) (p : s.Pos) (acc : Nat) : Nat :=
  if h : p = s.endPos then acc
  else
    let c := p.get h
    let q := p.next h
    if c == '_' then
      if h2 : q = s.endPos then acc
      else if isD base (q.get h2) then prefixedRun base (q.next h2) (acc + 2) else acc
    else if isD base c then prefixedRun base q (acc + 1) else acc
termination_by (rest p).length
decreasing_by
  · exact Nat.lt_trans (rest_next_length q h2) (rest_next_length p h)
  · exact rest_next_length p h

/-- `Lex.intAt.z`, with an accumulator. -/
def zeros (p : s.Pos) (acc : Nat) : Nat :=
  if h : p = s.endPos then acc
  else
    let c := p.get h
    let q := p.next h
    if c == '_' then
      if h2 : q = s.endPos then acc
      else if q.get h2 == '0' then zeros (q.next h2) (acc + 2) else acc
    else if c == '0' then zeros q (acc + 1) else acc
termination_by (rest p).length
decreasing_by
  · exact Nat.lt_trans (rest_next_length q h2) (rest_next_length p h)
  · exact rest_next_length p h

def intAt (p : s.Pos) : Option (Nat × Nat) :=
  match peek p with
  | some '0' =>
    let q := adv p
    match peek q with
    | some c =>
      let cs := adv q
      let pfx := fun (base : Nat) =>
        let n := prefixedRun base cs 0
        if n > 0 then some (2 + n, digitsValue base (takeL cs n)) else none
      let zs : Option (Nat × Nat) := some (1 + zeros q 0, 0)
      if c == 'b' || c == 'B' then (pfx 2).orElse (fun _ => zs)
      else if c == 'o' || c == 'O' then (pfx 8).orElse (fun _ => zs)
      else if c == 'x' || c == 'X' then (pfx 16).orElse (fun _ => zs)
      else zs
    | none => some (1, 0)
  | some c =>
    if '1' ≤ c ∧ c ≤ '9' then
      let n := digitRun 10 p
      some (n, digitsValue 10 (takeL p n))
    else none
  | none => none

def nameLen (p : s.Pos) : Nat := countWhile isIdentChar p 0

def stringGo (q : Char) (p : s.Pos) (n : Nat) : Option Nat :=
  if h : p = s.endPos then none
  else
    let c := p.get h
    let r := p.next h
    if c == '\\' then
      if h2 : r = s.endPos then (if c == q then some (n + 1) else none)
      else stringGo q (r.next h2) (n + 2)
    else if c == q then some (n + 1) else stringGo q r (n + 1)
termination_by (rest p).length
decreasing_by
  · exact Nat.lt_trans (rest_next_length r h2) (rest_next_length p h)
  · exact rest_next_length p h

def stringAt (p : s.Pos) : Option Nat :=
  match peek p with
  | some q => if q == '\'' || q == '"' then stringGo q (adv p) 1 else none
  | none => none

/-- `Lex.strValue` in place: the content normalised into a `String`, then
unescaped from it into another. -/
def strValue (cfg : LexConfig) (p : s.Pos) (n : Nat) : Except String String :=
  Lex.unescF (foldTake (normStep cfg.newlineSequence) ("", false) (adv p) (n - 2)).1.toSlice.startPos ""

def opAt (p : s.Pos) : Option (Nat × Op) := Lex.opAt (takeL p 2)

/-! ## Cutting tokens -/

/-- Fold `f` over up to `n` characters at `p`, counting them from `k`:
(result, count, position after). One pass for a token's value, length and
end. -/
def scan {β : Type} (f : β → Char → β) (b : β) (p : s.Pos) : Nat → Nat → β × Nat × s.Pos
  | 0, k => (b, k, p)
  | n + 1, k => if h : p = s.endPos then (b, k, p) else scan f (f b (p.get h)) (p.next h) n (k + 1)

/-- A cutter: the tokens at `p` and the position after them. -/
abbrev Cut (s : Slice) := s.Pos → List TokL × s.Pos

def cut (k : TokKind) (n : Nat) : Cut s := fun p =>
  let r := scan (fun u _ => u) () p n 0
  ([⟨k, r.2.1⟩], r.2.2)

def cutOpt (k : TokKind) (n : Nat) : Cut s := fun p => if n = 0 then ([], p) else cut k n p

/-- Template data: its value is the text with newlines normalised, built in
the same pass that measures it. -/
def cutData (cfg : LexConfig) (n : Nat) : Cut s := fun p =>
  if n = 0 then ([], p)
  else
    let r := scan (normStep cfg.newlineSequence) ("", false) p n 0
    ([⟨.data r.1.1, r.2.1⟩], r.2.2)

def seq (a b : Cut s) : Cut s := fun p => ((a p).1 ++ (b (a p).2).1, (b (a p).2).2)

def emit (f : Cut s) (m : LexMode) (p : s.Pos) : Except LexError (List TokL × LexMode × s.Pos) :=
  .ok ((f p).1, m, (f p).2)

/-! ## Steps -/

def stepRoot (cfg : LexConfig) (k : Ctx) (prev : Prev) (p : s.Pos)
    (pos : Nat) : Except LexError (List TokL × LexMode × s.Pos) :=
  match findTag cfg k prev p 0 with
  | .error len =>
    emit (cutData cfg len) (.root .text) p
  | .ok (i, t) =>
    let (isVar, sign) := match t with
      | .raw _ s => (false, s) | .comment _ s => (false, s)
      | .block _ s => (false, s) | .var _ s => (true, s)
      | .lineStmt _ s => (false, s) | .lineComment _ s => (false, s)
    let keep := stripSplit cfg isVar sign (prev == .line) p i
    let pre := seq (cutData cfg keep) (cutOpt .ws (i - keep))
    match t with
    | .var n _ =>
      emit (seq pre (cut .varBegin n)) (.tag .var [] false) p
    | .block n _ =>
      emit (seq pre (cut .blockBegin n)) (.tag .block [] false) p
    | .lineStmt n _ =>
      emit (seq pre (cut .blockBegin n)) (.tag .line [] false) p
    | .lineComment n _ =>
      let j := lineRest (advN p (i + n))
      emit (seq pre (cut .comment (n + j))) (.root (prevOf p (i + n + j))) p
    | .comment n _ =>
      let body := advN p (i + n)
      match findMatchC (commentCand cfg.commentEnd.toList.head?) (commentEndAt cfg) body 0 with
      | none => .error ⟨"Missing end of comment tag", pos + i⟩
      | some (j, e) =>
        emit (seq pre (cut .comment (n + j + e))) (.root (prevOf p (i + n + j + e))) p
    | .raw n _ =>
      let body := advN p (i + n)
      match findMatchC (candOne cfg.blockStart.toList.head?) (rawEndAt cfg) body 0 with
      | none => .error ⟨"Missing end of raw directive", pos + i⟩
      | some (j, (e, esign)) =>
        let keep2 := stripSplit cfg false esign (prevOf p (i + n) == .line) body j
        emit (seq pre (seq (cut .rawBegin n)
            (seq (cutData cfg keep2) (seq (cutOpt .ws (j - keep2)) (cut .rawEnd e)))))
          (.root (prevOf p (i + n + j + e))) p

def stepTag (cfg : LexConfig) (k : TagKind) (stack : List Char) (afterDot : Bool)
    (p : s.Pos) (pos : Nat) : Except LexError (List TokL × LexMode × s.Pos) :=
  let endM := if stack.isEmpty then
      (match k with | .block => blockEndAt cfg p | .var => varEndAt cfg p | .line => lineEndAt p)
    else none
  match endM with
  | some n =>
    emit (cut (match k with | .block => .blockEnd | .var => .varEnd | .line => .blockEnd) n)
      (.root (prevOf p n)) p
  | none =>
    let sp := spaceLen p
    if sp > 0 then
      emit (cut .ws sp) (.tag k stack false) p
    else
    match (if afterDot then none else floatAt p) with
    | some n =>
      emit (cut (.float (Lex.floatValue (takeL p n)).1 (Lex.floatValue (takeL p n)).2) n)
        (.tag k stack false) p
    | none =>
    match intAt p with
    | some (n, v) =>
      emit (cut (.int v) n) (.tag k stack false) p
    | none =>
    let nl := nameLen p
    if nl > 0 && peek p == some '\xb7' then .error ⟨"Invalid character in identifier", pos⟩
    else if nl > 0 then
      emit (cut (.name (copyTake p nl)) nl) (.tag k stack false) p
    else
    match stringAt p with
    | some n =>
      match strValue cfg p n with
      | .error e => .error ⟨e, pos⟩
      | .ok v =>
        emit (cut (.str v) n) (.tag k stack false) p
    | none =>
    match opAt p with
    | some (n, o) =>
      let stack' : Except LexError (List Char) :=
        match Lex.closerOf o, Lex.isCloser o with
        | some c, _ => .ok (c :: stack)
        | none, some c =>
          match stack with
          | [] => .error ⟨s!"unexpected '{c}'", pos⟩
          | e :: st => if e == c then .ok st else .error ⟨s!"unexpected '{c}', expected '{e}'", pos⟩
        | none, none => .ok stack
      match stack' with
      | .error e => .error e
      | .ok st =>
        emit (cut (.op o) n) (.tag k st (o == .dot)) p
    | none =>
      .error ⟨s!"unexpected char {repr ((peek p).getD ' ')} at {pos}", pos⟩

def closeLine : Except LexError (List TokL × LexMode × s.Pos) →
    Except LexError (List TokL × LexMode × s.Pos)
  | .ok (ts, m, q) =>
    if (peek q).isNone && m.openLine then .ok (ts ++ [⟨.blockEnd, 0⟩], .root .text, q) else .ok (ts, m, q)
  | .error e => .error e

def step (cfg : LexConfig) (k : Ctx) (m : LexMode) (p : s.Pos)
    (pos : Nat) : Except LexError (List TokL × LexMode × s.Pos) :=
  closeLine (match m with
    | .root ls => stepRoot cfg k ls p pos
    | .tag k st ad => stepTag cfg k st ad p pos)

def consumed (ts : List TokL) : Nat := ts.foldl (fun n t => n + t.len) 0

/-- The loop, as `Lex.loop`: tail recursive, the tokens so far reversed. -/
def loop (cfg : LexConfig) (k : Ctx) :
    Nat → LexMode → s.Pos → Nat → List TokL → Except LexError (List TokL)
  | fuel, m, p, pos, acc =>
    if p = s.endPos then .ok acc.reverse
    else match fuel with
      | 0 => .error ⟨"lexer step bound exceeded", pos⟩
      | fuel + 1 =>
        match step cfg k m p pos with
        | .error e => .error e
        | .ok (ts, m', q) => loop cfg k fuel m' q (pos + consumed ts) (ts.reverse ++ acc)

/-- `loop` keeping only the significant token kinds (`significantL`), the
ones the parser reads: for the compiler, which then holds no list of all
tokens. `loopSig_eq` relates it to `loop`. -/
def loopSig (cfg : LexConfig) (k : Ctx) :
    Nat → LexMode → s.Pos → Nat → List TokKind → Except LexError (List TokKind)
  | fuel, m, p, pos, acc =>
    if p = s.endPos then .ok acc.reverse
    else match fuel with
      | 0 => .error ⟨"lexer step bound exceeded", pos⟩
      | fuel + 1 =>
        match step cfg k m p pos with
        | .error e => .error e
        | .ok (ts, m', q) => loopSig cfg k fuel m' q (pos + consumed ts) ((significantL ts).reverse ++ acc)

theorem significantL_append (a b : List TokL) :
    significantL (a ++ b) = significantL a ++ significantL b := by
  simp [significantL]

theorem loopSig_eq (cfg : LexConfig) (k : Ctx) : ∀ (fuel : Nat) (m : LexMode) (p : s.Pos) (pos : Nat)
    (acc : List TokL),
    loopSig cfg k fuel m p pos (significantL acc.reverse).reverse = (loop cfg k fuel m p pos acc).map significantL
  | fuel, m, p, pos, acc => by
    unfold loopSig loop
    split
    · simp [Except.map]
    · match fuel with
      | 0 => simp [Except.map]
      | fuel + 1 =>
        simp only
        cases step cfg k m p pos with
        | error e => simp [Except.map]
        | ok r =>
          obtain ⟨ts, m', q⟩ := r
          simp only
          rw [← loopSig_eq cfg k fuel m' q (pos + consumed ts) (ts.reverse ++ acc)]
          simp [significantL_append]

end LexF

/-- Tokenize template source in place (`lex`, for the compiler: kinds and
lengths). `lexFast_eq` proves it equal to `lex`. -/
def lexFast (cfg : LexConfig) (src : String) : Except LexError (List TokL) :=
  let k := Lex.trailingNewlineLen cfg (src.takeEnd 2).copy.toList
  let body := src.dropEnd k
  match LexF.loop cfg (LexF.ctx cfg) (src.length - k + 1) (.root .line) body.startPos 0 [] with
  | .error e => .error e
  | .ok ts => .ok (ts ++ (if k = 0 then [] else [⟨.ws, k⟩]))

/-- `lexFast` keeping only the significant token kinds (`lexFastSig_eq`). -/
def lexFastSig (cfg : LexConfig) (src : String) : Except LexError (List TokKind) :=
  let k := Lex.trailingNewlineLen cfg (src.takeEnd 2).copy.toList
  let body := src.dropEnd k
  LexF.loopSig cfg (LexF.ctx cfg) (src.length - k + 1) (.root .line) body.startPos 0 []

theorem lexFastSig_eq (cfg : LexConfig) (src : String) :
    lexFastSig cfg src = (lexFast cfg src).map significantL := by
  unfold lexFastSig lexFast
  generalize Lex.trailingNewlineLen cfg (src.takeEnd 2).copy.toList = k
  have h := LexF.loopSig_eq cfg (LexF.ctx cfg) (src.length - k + 1) (.root .line) (src.dropEnd k).startPos 0 []
  simp only [List.reverse_nil, significantL, List.filter_nil, List.map_nil] at h
  simp only
  rw [h]
  cases LexF.loop cfg (LexF.ctx cfg) (src.length - k + 1) (.root .line) (src.dropEnd k).startPos 0 [] with
  | error e => rfl
  | ok ts =>
    simp only [Except.map]
    rw [LexF.significantL_append]
    split <;> simp [significantL, TokKind.ignored]

end LeanJinja2
