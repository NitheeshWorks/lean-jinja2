import LeanJinja2.RepoImpl.Chars
import LeanJinja2.RepoImpl.UnicodeTables

/-!
# `urlize`

Upstream `jinja2.utils.urlize` (3.1.6): the text is escaped and split on
whitespace; each word loses its leading `(`/`<`/`&lt;` and trailing
`)`/`>`/`.`/`,`/`&gt;` punctuation (kept around the link, with brackets moved
back to balance the word), and the word becomes a link when it matches
upstream's `_http_re`, is a `mailto:` address, an email address, or starts
with one of `extra_schemes`.

Upstream's regular expressions are decided here directly. Each is anchored
at both ends, and what may follow the host (`(?::\d{1,5})?(?:[/?#]\S*)?$`)
starts with a character no host contains, so the host must end at the first
character outside its alphabet: one candidate split, one linear pass.
`\w`, `\d` and `\s` are CPython's, from the tables `scripts/unicode_tables.py`
measures (`UnicodeTables`). Under `re.IGNORECASE` a letter also matches its Unicode case
partners (`ſ` for `s`, `K` for `k`, `İ`/`ı` for `i`), as in Python.
-/

namespace LeanJinja2

/-- Membership in sorted, disjoint code point ranges (binary search). -/
def inRanges (rs : Array (Nat × Nat)) (c : Nat) : Bool :=
  go 64 0 rs.size
where
  go : Nat → Nat → Nat → Bool
    | 0, _, _ => false
    | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        let (a, b) := rs.getD mid (0, 0)
        if c < a then go fuel lo mid else if b < c then go fuel (mid + 1) hi else true
      else false

/-- Regex `\w` (CPython `re`). -/
def isWordC (c : Char) : Bool := inRanges UnicodeTables.word c.toNat

/-- Regex `\d` (CPython `re`). -/
def isReDigit (c : Char) : Bool := inRanges UnicodeTables.digit c.toNat

/-- Regex `\s` (CPython `re`). -/
def isReSpace (c : Char) : Bool := inRanges UnicodeTables.space c.toNat

/-- `c` matches the pattern letter `t` (ASCII lower case) under `re.IGNORECASE`. -/
def ciEq (c t : Char) : Bool :=
  (if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c) == t ||
  (t == 's' && c == 'ſ') || (t == 'k' && c == 'K') || (t == 'i' && (c == 'İ' || c == 'ı'))

/-- `[a-z]` under `re.IGNORECASE`. -/
def isAzI (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == 'ſ' || c == 'K' || c == 'İ' || c == 'ı'

/-- `[\da-f]` under `re.IGNORECASE`. -/
def isHexI (c : Char) : Bool := isReDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Strip a case-insensitive literal prefix. -/
def stripCI : List Char → List Char → Option (List Char)
  | [], l => some l
  | t :: ts, c :: cs => if ciEq c t then stripCI ts cs else none
  | _ :: _, [] => none

/-- `(?::\d{1,5})?(?:[/?#]\S*)?$`: what may follow the host. -/
def urlRestOk : List Char → Bool
  | [] => true
  | ':' :: r =>
    let ds := r.takeWhile isReDigit
    let r' := r.dropWhile isReDigit
    1 ≤ ds.length && ds.length ≤ 5 &&
      (match r' with
       | [] => true
       | c :: s => (c == '/' || c == '?' || c == '#') && s.all (fun c => !isReSpace c))
  | c :: s => (c == '/' || c == '?' || c == '#') && s.all (fun c => !isReSpace c)

/-- `[\w%-]`. -/
def isHostC (c : Char) : Bool := isWordC c || c == '%' || c == '-'

/-- The host and what follows it: the longest run of `[\w%-.]`. -/
def hostSpan (l : List Char) : List Char × List Char :=
  (l.takeWhile (fun c => isHostC c || c == '.'), l.dropWhile (fun c => isHostC c || c == '.'))

/-- `(([\w%-]+\.)+)?([a-z]{2,63}|xn--[\w%]{2,59})`, on a run of `[\w%-.]`. -/
def subdomainTldOk (seg : List Char) : Bool :=
  let ps := seg.splitOn '.'
  ps.dropLast.all (fun p => !p.isEmpty) &&
    (let t := ps.getLastD []
     (2 ≤ t.length && t.length ≤ 63 && t.all isAzI) ||
       (match stripCI "xn--".toList t with
        | some r => 2 ≤ r.length && r.length ≤ 59 && r.all (fun c => isWordC c || c == '%')
        | none => false))

/-- `([\w%-]{2,63}\.)+(com|net|int|edu|gov|org|info|mil)`, on a run of `[\w%-.]`. -/
def basicDomainOk (seg : List Char) : Bool :=
  let ps := seg.splitOn '.'
  2 ≤ ps.length && ps.dropLast.all (fun p => 2 ≤ p.length && p.length ≤ 63) &&
    (let t := ps.getLastD []
     ["com", "net", "int", "edu", "gov", "org", "info", "mil"].any
       (fun d => stripCI d.toList t == some []))

/-- `https?://`, case-insensitive. -/
def stripHttp (l : List Char) : Option (List Char) :=
  match stripCI "https://".toList l with
  | some r => some r
  | none => stripCI "http://".toList l

/-- The items of `([\da-f]{0,4}:?){1,6}` a run of hex digits and colons needs. -/
def v6Items (groups : List (List Char)) : Nat :=
  let rec go : List (List Char) → Nat
    | [] => 0
    | [g] => (g.length + 3) / 4
    | g :: gs => max 1 ((g.length + 3) / 4) + go gs
  go groups

/-- `\[([\da-f]{0,4}:){2}([\da-f]{0,4}:?){1,6}]` then the rest. -/
def ipv6Ok : List Char → Bool
  | '[' :: r =>
    let content := r.takeWhile (· != ']')
    match r.dropWhile (· != ']') with
    | ']' :: rest =>
      content.all (fun c => isHexI c || c == ':') &&
        (match content.splitOn ':' with
         | g0 :: g1 :: g2 :: gs => g0.length ≤ 4 && g1.length ≤ 4 && v6Items (g2 :: gs) ≤ 6
         | _ => false) &&
        urlRestOk rest
    | _ => false
  | _ => false

/-- `(\d{1,3})(\.\d{1,3}){3}` then the rest. -/
def ipv4Ok (l : List Char) : Bool :=
  let seg := l.takeWhile (fun c => isReDigit c || c == '.')
  let ps := seg.splitOn '.'
  ps.length == 4 && ps.all (fun p => 1 ≤ p.length && p.length ≤ 3) &&
    urlRestOk (l.dropWhile (fun c => isReDigit c || c == '.'))

/-- Upstream `_http_re.match(word)`. -/
def httpMatch (m : List Char) : Bool :=
  let viaScheme := fun (r : List Char) =>
    let (seg, rest) := hostSpan r
    subdomainTldOk seg && urlRestOk rest
  (match stripHttp m with
   | some r => viaScheme r || ipv4Ok r || ipv6Ok r
   | none => false) ||
  (match stripCI "www.".toList m with
   | some r => viaScheme r
   | none => false) ||
  (let (seg, rest) := hostSpan m
   basicDomainOk seg && urlRestOk rest)

/-- Upstream `_email_re.match(s)`: `^\S+@\w[\w.-]*\.\w+$`. -/
def emailMatch (l : List Char) : Bool :=
  let post := (l.reverse.takeWhile (· != '@')).reverse
  let pre := (l.reverse.dropWhile (· != '@')).drop 1
  !pre.isEmpty && pre.all (fun c => !isReSpace c) &&
    (match post with
     | c :: _ =>
       isWordC c && post.all (fun c => isWordC c || c == '.' || c == '-') &&
         (let after := (post.reverse.takeWhile (· != '.')).reverse
          let before := (post.reverse.dropWhile (· != '.')).drop 1
          !before.isEmpty && !after.isEmpty && after.all isWordC)
     | [] => false)

/-- Strip `^([(<]|&lt;)+`; `h` is the head so far, reversed. -/
def urlHead : List Char → List Char → List Char × List Char
  | h, '(' :: r => urlHead ('(' :: h) r
  | h, '<' :: r => urlHead ('<' :: h) r
  | h, '&' :: 'l' :: 't' :: ';' :: r => urlHead (';' :: 't' :: 'l' :: '&' :: h) r
  | h, r => (h.reverse, r)

/-- Strip `([)>.,\n]|&gt;)+$`, on the reversed word: the reversed rest and the tail. -/
def urlTail : List Char → List Char → List Char × List Char
  | ';' :: 't' :: 'g' :: '&' :: r, t => urlTail r ("&gt;".toList ++ t)
  | c :: r, t => if c == ')' || c == '>' || c == '.' || c == ',' || c == '\n' then urlTail r (c :: t)
    else (c :: r, t)
  | [], t => ([], t)

/-- Non-overlapping occurrences of `p` (non-empty) in `l`, as `str.count`. -/
def countSub (p : List Char) : List Char → Nat → Nat
  | [], n => n
  | l@(_ :: r), n =>
    if p.isPrefixOf l then countSub p (r.drop (p.length - 1)) (n + 1) else countSub p r n
termination_by l => l.length
decreasing_by all_goals (simp only [List.length_drop, List.length_cons]; omega)

/-- `tail.index(end) + len(end)`: the prefix of `tail` through the first
`end`, and the rest (`none` if absent). -/
def splitThrough (p : List Char) : List Char → List Char → Option (List Char × List Char)
  | _, [] => none
  | acc, l@(c :: r) =>
    if p.isPrefixOf l then some (acc.reverse ++ p, l.drop p.length) else splitThrough p (c :: acc) r

/-- Move up to `k` closing brackets (with what precedes each) from the tail
to the middle; `moved` is what moved so far, reversed. -/
def moveClosers (e : List Char) : Nat → List Char → List Char → List Char × List Char
  | 0, moved, t => (moved.reverse, t)
  | k + 1, moved, t =>
    match splitThrough e [] t with
    | some (pre, rest) => moveClosers e k (pre.reverse ++ moved) rest
    | none => (moved.reverse, t)

/-- Upstream's bracket balancing: for each pair, when the middle has more
openers than closers, move `min(openers, closers in tail)` closers back. -/
def balance (m t : List Char) : List Char × List Char :=
  [("(".toList, ")".toList), ("<".toList, ">".toList), ("&lt;".toList, "&gt;".toList)].foldl
    (fun (m, t) (s, e) =>
      let sc := countSub s m 0
      if sc ≤ countSub e m 0 then (m, t) else
        let (moved, t) := moveClosers e (min sc (countSub e t 0)) [] t
        (m ++ moved, t))
    (m, t)

/-- The options of one `urlize` call (after `do_urlize` resolved them). -/
structure UrlizeOpts where
  /-- `trim_url_limit`. -/
  trim : Option Int := none
  /-- The ` rel="..."` attribute text, escaped, or empty. -/
  relAttr : String := ""
  /-- The ` target="..."` attribute text, escaped, or empty. -/
  targetAttr : String := ""
  extraSchemes : List String := []

/-- Upstream `trim_url`: Python `x[:limit] + "..."` when longer than the limit. -/
def trimUrl (o : UrlizeOpts) (x : String) : String :=
  match o.trim with
  | none => x
  | some k =>
    if (x.length : Int) > k then
      let n := if k ≥ 0 then k.toNat else ((x.length : Int) + k).toNat
      String.ofList (x.toList.take n) ++ "..."
    else x

/-- One whitespace-free word of escaped text. -/
def urlizeWord (o : UrlizeOpts) (w : List Char) : String :=
  let (head, m) := urlHead [] w
  let (mr, tail) := urlTail m.reverse []
  let (m, tail) := balance mr.reverse tail
  let ms := String.ofList m
  let mid :=
    if httpMatch m then
      if ms.startsWith "https://" || ms.startsWith "http://" then
        s!"<a href=\"{ms}\"{o.relAttr}{o.targetAttr}>{trimUrl o ms}</a>"
      else s!"<a href=\"https://{ms}\"{o.relAttr}{o.targetAttr}>{trimUrl o ms}</a>"
    else if ms.startsWith "mailto:" && emailMatch (m.drop 7) then
      s!"<a href=\"{ms}\">{String.ofList (m.drop 7)}</a>"
    else if m.contains '@' && !ms.startsWith "www." && !ms.startsWith "@" && !m.contains ':' &&
        emailMatch m then
      s!"<a href=\"mailto:{ms}\">{ms}</a>"
    else
      match o.extraSchemes.find? (fun s => ms != s && ms.startsWith s) with
      | some _ => s!"<a href=\"{ms}\"{o.relAttr}{o.targetAttr}>{ms}</a>"
      | none => ms
  String.ofList head ++ mid ++ String.ofList tail

/-- Upstream `urlize` on already-escaped text: words are linked, whitespace
is kept. `cur` is the current word, reversed. -/
def urlizeGo (o : UrlizeOpts) : List Char → List Char → String → String
  | [], cur, acc => if cur.isEmpty then acc else acc ++ urlizeWord o cur.reverse
  | c :: r, cur, acc =>
    if isReSpace c then
      urlizeGo o r [] ((if cur.isEmpty then acc else acc ++ urlizeWord o cur.reverse).push c)
    else urlizeGo o r (c :: cur) acc

/-- Upstream `urlize(text, ...)` on the escaped text. -/
def urlizeText (o : UrlizeOpts) (escaped : String) : String := urlizeGo o escaped.toList [] ""

/-- Upstream `_uri_scheme_re`: `^([\w.+-]{2,}:(/){0,2})$`. -/
def uriSchemeOk (s : String) : Bool :=
  let l := s.toList
  let body := l.takeWhile (fun c => isWordC c || c == '.' || c == '+' || c == '-')
  match l.drop body.length with
  | ':' :: r => 2 ≤ body.length && r.length ≤ 2 && r.all (· == '/')
  | _ => false

end LeanJinja2
