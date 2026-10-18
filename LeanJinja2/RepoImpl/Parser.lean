import LeanJinja2.DataTypes.Ast
import LeanJinja2.DataTypes.Syntax
import LeanJinja2.RepoImpl.Chars

/-!
# The parser

A re-expression of upstream `jinja2.parser.Parser`: recursive descent over
the significant tokens, one function per upstream method, the same
precedence tower (`condexpr` < `or` < `and` < `not` < `compare` < `math1`
(`+ -`) < `concat` (`~`) < `math2` (`* / // %`) < `pow` < `unary`, with
postfix subscripts/calls and then filters/tests binding to the unary
operand).

Every function takes a `fuel` argument that bounds the call depth, so the
parser is total by structural recursion; `parseTemplate` gives it a bound
proportional to the token count, which is never reached on a template whose
nesting the tokens can express (each nesting level consumes a token).
Running out reports an error instead of looping.
-/

namespace LeanJinja2

/-- A syntax error: the message and how many significant tokens were left
when it was raised (the API maps that back to a line number). -/
structure ParseError where
  msg : String
  remaining : Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-- A parser result: the value and the remaining tokens. -/
macro "PR " α:term:max : term => `(Except ParseError ($α × List TokKind))

namespace Parse

/-- Upstream `describe_token`. -/
def describe : TokKind → String
  | .name s => s
  | .op o => o.text
  | .data _ => "template data / text"
  | .varBegin => "begin of print statement"
  | .varEnd => "end of print statement"
  | .blockBegin => "begin of statement block"
  | .blockEnd => "end of statement block"
  | .int _ => "integer"
  | .float _ _ => "float"
  | .str _ => "string"
  | .comment => "comment"
  | .ws => "whitespace"
  | .rawBegin => "raw_begin"
  | .rawEnd => "raw_end"

def fail {α : Type} (msg : String) (ts : List TokKind) : PR α := .error ⟨msg, ts.length⟩

def deep {α : Type} (ts : List TokKind) : PR α := fail "template nesting too deep" ts

/-- `stream.expect(tok)`. -/
def expect (k : TokKind) (ts : List TokKind) : PR Unit :=
  match ts with
  | t :: r => if t == k then .ok ((), r)
    else fail s!"expected token '{describe k}', got '{describe t}'" ts
  | [] => fail s!"unexpected end of template, expected '{describe k}'." ts

def expectName (ts : List TokKind) : PR String :=
  match ts with
  | .name s :: r => .ok (s, r)
  | t :: _ => fail s!"expected token 'name', got '{describe t}'" ts
  | [] => fail "unexpected end of template, expected 'name'." ts

def isName (s : String) : Option TokKind → Bool
  | some (.name t) => t == s
  | _ => false

def isOp (o : Op) : Option TokKind → Bool
  | some (.op p) => p == o
  | _ => false

/-- Names that are constants, not variables. -/
def constName : String → Option Const
  | "true" | "True" => some (.bool true)
  | "false" | "False" => some (.bool false)
  | "none" | "None" => some .none
  | _ => none

/-- Upstream `is_tuple_end`. -/
def isTupleEnd (extra : List String) : Option TokKind → Bool
  | some .varEnd | some .blockEnd | some (.op .rparen) => true
  | some (.name s) => extra.contains s
  | _ => false

def cmpOpOf : Op → Option CmpOp
  | .eq => some .eq | .ne => some .ne | .lt => some .lt | .lteq => some .lteq
  | .gt => some .gt | .gteq => some .gteq | _ => none

def math1Op : Op → Option BinOp
  | .add => some .add | .sub => some .sub | _ => none

def math2Op : Op → Option BinOp
  | .mul => some .mul | .div => some .div | .floordiv => some .floordiv | .mod => some .mod
  | _ => none

/-- Tokens that may start a test argument without parentheses. -/
def testArgStart : Option TokKind → Bool
  | some (.name s) => s != "else" && s != "or" && s != "and"
  | some (.str _) | some (.int _) | some (.float _ _) => true
  | some (.op .lparen) | some (.op .lbracket) | some (.op .lbrace) => true
  | _ => false

/-- Convert a parsed expression to an assignment target (upstream
`can_assign` + `set_ctx("store")`). -/
def exprToTarget : Expr → Option Target
  | .name n => some (.name n)
  | .tuple items => (go items).map .tuple
  | _ => none
where
  go : List Expr → Option (List Target)
    | [] => some []
    | e :: es => match exprToTarget e, go es with
      | some t, some ts => some (t :: ts)
      | _, _ => none

mutual

/-- `parse_expression(with_condexpr)`. -/
def pExpr : Nat → Bool → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, wc, ts => if wc then pCond n ts else pOr n ts

/-- `parse_condexpr`. -/
def pCond : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts => do
    let (e1, ts) ← pOr n ts
    pCondLoop n e1 ts

def pCondLoop : Nat → Expr → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, e1, ts =>
    if isName "if" ts.head? then do
      let (e2, ts) ← pOr n ts.tail
      if isName "else" ts.head? then do
        let (e3, ts) ← pCond n ts.tail
        pCondLoop n (.cond e2 e1 (some e3)) ts
      else pCondLoop n (.cond e2 e1 none) ts
    else .ok (e1, ts)

/-- `parse_or`. -/
def pOr : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts => do
    let (l, ts) ← pAnd n ts
    pOrLoop n l ts

def pOrLoop : Nat → Expr → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, l, ts =>
    if isName "or" ts.head? then do
      let (r, ts) ← pAnd n ts.tail
      pOrLoop n (.binop .or l r) ts
    else .ok (l, ts)

/-- `parse_and`. -/
def pAnd : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts => do
    let (l, ts) ← pNot n ts
    pAndLoop n l ts

def pAndLoop : Nat → Expr → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, l, ts =>
    if isName "and" ts.head? then do
      let (r, ts) ← pNot n ts.tail
      pAndLoop n (.binop .and l r) ts
    else .ok (l, ts)

/-- `parse_not`. -/
def pNot : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts =>
    if isName "not" ts.head? then do
      let (e, ts) ← pNot n ts.tail
      .ok (.unop .not e, ts)
    else pCompare n ts

/-- `parse_compare`. -/
def pCompare : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts => do
    let (e, ts) ← pMath1 n ts
    let (ops, ts) ← pCmpOps n ts
    if ops.isEmpty then .ok (e, ts) else .ok (.compare e ops, ts)

def pCmpOps : Nat → List TokKind → PR (List (CmpOp × Expr))
  | 0, ts => deep ts
  | n + 1, ts =>
    let op : Option (CmpOp × List TokKind) :=
      match ts with
      | .op o :: r => (cmpOpOf o).map (·, r)
      | .name "in" :: r => some (.in, r)
      | .name "not" :: .name "in" :: r => some (.notin, r)
      | _ => none
    match op with
    | some (o, r) => do
      let (e, r) ← pMath1 n r
      let (more, r) ← pCmpOps n r
      .ok ((o, e) :: more, r)
    | none => .ok ([], ts)

/-- `parse_math1` (`+`, `-`). -/
def pMath1 : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts => do
    let (l, ts) ← pConcat n ts
    pMath1Loop n l ts

def pMath1Loop : Nat → Expr → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, l, ts =>
    match ts with
    | .op o :: r =>
      match math1Op o with
      | some b => do
        let (rhs, r) ← pConcat n r
        pMath1Loop n (.binop b l rhs) r
      | none => .ok (l, ts)
    | _ => .ok (l, ts)

/-- `parse_concat` (`~`). -/
def pConcat : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts => do
    let (e, ts) ← pMath2 n ts
    let (more, ts) ← pConcatRest n ts
    if more.isEmpty then .ok (e, ts) else .ok (.concat (e :: more), ts)

def pConcatRest : Nat → List TokKind → PR (List Expr)
  | 0, ts => deep ts
  | n + 1, ts =>
    match ts with
    | .op .tilde :: r => do
      let (e, r) ← pMath2 n r
      let (more, r) ← pConcatRest n r
      .ok (e :: more, r)
    | _ => .ok ([], ts)

/-- `parse_math2` (`*`, `/`, `//`, `%`). -/
def pMath2 : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts => do
    let (l, ts) ← pPow n ts
    pMath2Loop n l ts

def pMath2Loop : Nat → Expr → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, l, ts =>
    match ts with
    | .op o :: r =>
      match math2Op o with
      | some b => do
        let (rhs, r) ← pPow n r
        pMath2Loop n (.binop b l rhs) r
      | none => .ok (l, ts)
    | _ => .ok (l, ts)

/-- `parse_pow` (`**`, left-associative as upstream). -/
def pPow : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts => do
    let (l, ts) ← pUnary n true ts
    pPowLoop n l ts

def pPowLoop : Nat → Expr → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, l, ts =>
    match ts with
    | .op .pow :: r => do
      let (rhs, r) ← pUnary n true r
      pPowLoop n (.binop .pow l rhs) r
    | _ => .ok (l, ts)

/-- `parse_unary(with_filter)`. -/
def pUnary : Nat → Bool → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, wf, ts => do
    let (e, ts) ← match ts with
      | .op .sub :: r => do let (e, r) ← pUnary n false r; pure (Expr.unop .neg e, r)
      | .op .add :: r => do let (e, r) ← pUnary n false r; pure (Expr.unop .pos e, r)
      | _ => pPrimary n ts
    let (e, ts) ← pPostfix n e ts
    if wf then pFilterExpr n e ts else .ok (e, ts)

/-- `parse_primary`. -/
def pPrimary : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts =>
    match ts with
    | .name s :: r =>
      match constName s with
      | some c => .ok (.const c, r)
      | none => .ok (.name s, r)
    | .str s :: r => do
      let (more, r) ← pStrings n r
      .ok (.const (.str (s ++ more)), r)
    | .int v :: r => .ok (.const (.int v), r)
    | .float m s :: r => .ok (.const (.float m s), r)
    | .op .lparen :: r => do
      let (e, r) ← pTuple n true [] true r
      let ((), r) ← expect (.op .rparen) r
      .ok (e, r)
    | .op .lbracket :: r => do
      let (items, r) ← pListItems n r
      .ok (.list items, r)
    | .op .lbrace :: r => do
      let (items, r) ← pDictItems n r
      .ok (.dict items, r)
    | t :: _ => fail s!"unexpected '{describe t}'" ts
    | [] => fail "unexpected end of template" ts

/-- Adjacent string literals are concatenated. -/
def pStrings : Nat → List TokKind → PR String
  | 0, ts => deep ts
  | n + 1, ts =>
    match ts with
    | .str s :: r => do
      let (more, r) ← pStrings n r
      .ok (s ++ more, r)
    | _ => .ok ("", ts)

/-- `parse_tuple` (not simplified): `explicit` is `explicit_parentheses`. -/
def pTuple : Nat → Bool → List String → Bool → List TokKind → PR Expr
  | 0, _, _, _, ts => deep ts
  | n + 1, wc, extra, explicit, ts =>
    if isTupleEnd extra ts.head? then
      if explicit then .ok (.tuple [], ts)
      else fail s!"Expected an expression, got '{(ts.head?.map describe).getD "end of template"}'" ts
    else do
      let (e, ts) ← pExpr n wc ts
      if isOp .comma ts.head? then do
        let (more, ts) ← pTupleRest n wc extra ts
        .ok (.tuple (e :: more), ts)
      else .ok (e, ts)

/-- The rest of a tuple, starting at a comma. -/
def pTupleRest : Nat → Bool → List String → List TokKind → PR (List Expr)
  | 0, _, _, ts => deep ts
  | n + 1, wc, extra, ts => do
    let ((), ts) ← expect (.op .comma) ts
    if isTupleEnd extra ts.head? then .ok ([], ts)
    else do
      let (e, ts) ← pExpr n wc ts
      if isOp .comma ts.head? then do
        let (more, ts) ← pTupleRest n wc extra ts
        .ok (e :: more, ts)
      else .ok ([e], ts)

/-- `parse_list` after `[`. -/
def pListItems : Nat → List TokKind → PR (List Expr)
  | 0, ts => deep ts
  | n + 1, ts =>
    if isOp .rbracket ts.head? then .ok ([], ts.tail)
    else do
      let (e, ts) ← pExpr n true ts
      if isOp .rbracket ts.head? then .ok ([e], ts.tail)
      else do
        let ((), ts) ← expect (.op .comma) ts
        let (more, ts) ← pListItems n ts
        .ok (e :: more, ts)

/-- `parse_dict` after `{`. -/
def pDictItems : Nat → List TokKind → PR (List (Expr × Expr))
  | 0, ts => deep ts
  | n + 1, ts =>
    if isOp .rbrace ts.head? then .ok ([], ts.tail)
    else do
      let (k, ts) ← pExpr n true ts
      let ((), ts) ← expect (.op .colon) ts
      let (v, ts) ← pExpr n true ts
      if isOp .rbrace ts.head? then .ok ([(k, v)], ts.tail)
      else do
        let ((), ts) ← expect (.op .comma) ts
        let (more, ts) ← pDictItems n ts
        .ok ((k, v) :: more, ts)

/-- `parse_postfix`: subscripts and calls. -/
def pPostfix : Nat → Expr → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, e, ts =>
    match ts with
    | .op .dot :: r =>
      match r with
      | .name a :: r => pPostfix n (.getattr e a) r
      | .int v :: r => pPostfix n (.getitem e (.const (.int v))) r
      | _ => fail "expected name or number" r
    | .op .lbracket :: r => do
      let (idx, r) ← pSubscripts n r
      pPostfix n (.getitem e idx) r
    | .op .lparen :: r => do
      let ((args, kwargs), r) ← pCallArgs n r
      pPostfix n (.call e args kwargs) r
    | _ => .ok (e, ts)

/-- `parse_filter_expr`: filters, tests and calls after a unary operand. -/
def pFilterExpr : Nat → Expr → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, e, ts =>
    match ts with
    | .op .pipe :: r => do
      let (f, r) ← pFilterOne n r
      pFilterExpr n (.filter e f.name f.args f.kwargs) r
    | .name "is" :: r => do
      let (e, r) ← pTest n e r
      pFilterExpr n e r
    | .op .lparen :: r => do
      let ((args, kwargs), r) ← pCallArgs n r
      pFilterExpr n (.call e args kwargs) r
    | _ => .ok (e, ts)

/-- The subscripts after `[`, up to and including `]`. -/
def pSubscripts : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts => do
    let (items, ts) ← pSubscriptItems n ts
    match items with
    | [i] => .ok (i, ts)
    | is => .ok (.tuple is, ts)

def pSubscriptItems : Nat → List TokKind → PR (List Expr)
  | 0, ts => deep ts
  | n + 1, ts =>
    if isOp .rbracket ts.head? then .ok ([], ts.tail)
    else do
      let (e, ts) ← pSubscribed n ts
      if isOp .rbracket ts.head? then .ok ([e], ts.tail)
      else do
        let ((), ts) ← expect (.op .comma) ts
        let (more, ts) ← pSubscriptItems n ts
        .ok (e :: more, ts)

/-- `parse_subscribed`: an expression or a slice. -/
def pSubscribed : Nat → List TokKind → PR Expr
  | 0, ts => deep ts
  | n + 1, ts => do
    let (start, ts) ← if isOp .colon ts.head? then pure (none, ts)
      else do let (e, ts) ← pExpr n true ts; pure (some e, ts)
    match start with
    | some e => if isOp .colon ts.head? then pSliceRest n (some e) ts.tail else .ok (e, ts)
    | none => pSliceRest n none ts.tail

/-- A slice after its first colon. -/
def pSliceRest : Nat → Option Expr → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, start, ts => do
    let stopEnd := fun (t : Option TokKind) => isOp .colon t || isOp .rbracket t || isOp .comma t
    let (stop, ts) ← if stopEnd ts.head? then pure (none, ts)
      else do let (e, ts) ← pExpr n true ts; pure (some e, ts)
    if isOp .colon ts.head? then
      let ts := ts.tail
      if isOp .rbracket ts.head? || isOp .comma ts.head? then .ok (.slice start stop none, ts)
      else do
        let (step, ts) ← pExpr n true ts
        .ok (.slice start stop (some step), ts)
    else .ok (.slice start stop none, ts)

/-- `parse_call_args` after `(`, up to and including `)`. `*args`/`**kwargs`
are not supported. -/
def pCallArgs : Nat → List TokKind → PR (List Expr × List (String × Expr))
  | 0, ts => deep ts
  | n + 1, ts =>
    if isOp .rparen ts.head? then .ok (([], []), ts.tail)
    else do
      let (item, ts) ← match ts with
        | .op .mul :: _ | .op .pow :: _ => fail "*args and **kwargs are not supported" ts
        | .name k :: .op .assign :: r => do
          let (v, r) ← pExpr n true r
          pure (Sum.inr (k, v), r)
        | _ => do
          let (v, r) ← pExpr n true ts
          pure (Sum.inl v, r)
      let (rest, ts) ←
        if isOp .rparen ts.head? then pure (([], []), ts.tail)
        else do
          let ((), ts) ← expect (.op .comma) ts
          pCallArgs n ts
      match item with
      | .inl v => .ok ((v :: rest.1, rest.2), ts)
      | .inr kv =>
        if rest.1.isEmpty then .ok ((rest.1, kv :: rest.2), ts)
        else fail "invalid syntax for function call expression" ts

/-- One filter: dotted name and optional arguments (`parse_filter`, one
iteration). -/
def pFilterOne : Nat → List TokKind → PR FilterCall
  | 0, ts => deep ts
  | n + 1, ts => do
    let (name, ts) ← expectName ts
    let (name, ts) ← pDotted n name ts
    if isOp .lparen ts.head? then do
      let ((args, kwargs), ts) ← pCallArgs n ts.tail
      .ok (⟨name, args, kwargs⟩, ts)
    else .ok (⟨name, [], []⟩, ts)

/-- `.name` continuations of a filter or test name. -/
def pDotted : Nat → String → List TokKind → PR String
  | 0, _, ts => deep ts
  | n + 1, name, ts =>
    match ts with
    | .op .dot :: r => do
      let (a, r) ← expectName r
      pDotted n (name ++ "." ++ a) r
    | _ => .ok (name, ts)

/-- `parse_test`, after `is`. -/
def pTest : Nat → Expr → List TokKind → PR Expr
  | 0, _, ts => deep ts
  | n + 1, e, ts => do
    let (neg, ts) := if isName "not" ts.head? then (true, ts.tail) else (false, ts)
    let (name, ts) ← expectName ts
    let (name, ts) ← pDotted n name ts
    let ((args, kwargs), ts) ←
      if isOp .lparen ts.head? then pCallArgs n ts.tail
      else if testArgStart ts.head? then
        if isName "is" ts.head? then fail "You cannot chain multiple tests with is" ts
        else do
          let (a, ts) ← pPrimary n ts
          let (a, ts) ← pPostfix n a ts
          pure (([a], []), ts)
      else pure (([], []), ts)
    let t := Expr.test e name args kwargs
    .ok (if neg then .unop .not t else t, ts)

end

/-- `parse_primary` for assignment targets: a name, `ns.attr` (when
`withNs`), or a parenthesised tuple. -/
def pTargetPrimary (n : Nat) (withNs : Bool) (ts : List TokKind) : PR Target :=
  match ts with
  | .name s :: r =>
    if (constName s).isSome then fail s!"can't assign to 'const'" ts
    else if withNs then
      match r with
      | .op .dot :: .name a :: r' => .ok (.nsAttr s a, r')
      | .op .dot :: r' => do let _ ← expectName r'; fail "expected name" r'
      | _ => .ok (.name s, r)
    else .ok (.name s, r)
  | .op .lparen :: _ => do
    let (e, r) ← pPrimary n ts
    match exprToTarget e with
    | some t => .ok (t, r)
    | none => fail "can't assign to expression" ts
  | t :: _ => fail s!"can't assign to '{describe t}'" ts
  | [] => fail "unexpected end of template" ts

/-- The rest of a target tuple, starting at a comma. -/
def pTargetRest : Nat → List String → Bool → List TokKind → PR (List Target)
  | 0, _, _, ts => deep ts
  | n + 1, extra, withNs, ts => do
    let ((), ts) ← expect (.op .comma) ts
    if isTupleEnd extra ts.head? then .ok ([], ts)
    else do
      let (t, ts) ← pTargetPrimary n withNs ts
      if isOp .comma ts.head? then do
        let (more, ts) ← pTargetRest n extra withNs ts
        .ok (t :: more, ts)
      else .ok ([t], ts)

/-- `parse_assign_target` (with tuples): upstream `parse_tuple(simplified=True)`. -/
def pTarget (n : Nat) (extra : List String) (withNs : Bool) (ts : List TokKind) : PR Target :=
  if isTupleEnd extra ts.head? then
    fail s!"Expected an expression, got '{(ts.head?.map describe).getD "end of template"}'" ts
  else do
    let (t, ts) ← pTargetPrimary n withNs ts
    if isOp .comma ts.head? then do
      let (more, ts) ← pTargetRest n extra withNs ts
      .ok (.tuple (t :: more), ts)
    else .ok (t, ts)

/-- A parameter name (`parse_assign_target(name_only=True)`). -/
def pParamName (ts : List TokKind) : PR String :=
  match ts with
  | .name s :: r =>
    if (constName s).isSome then fail "can't assign to 'const'" ts else .ok (s, r)
  | t :: _ => fail s!"expected token 'name', got '{describe t}'" ts
  | [] => fail "unexpected end of template, expected 'name'." ts

/-- `parse_signature` after `(`, up to and including `)`. `hadDefault` says
an earlier parameter had a default. -/
def pParams : Nat → Bool → List TokKind → PR (List Param)
  | 0, _, ts => deep ts
  | n + 1, hadDefault, ts =>
    if isOp .rparen ts.head? then .ok ([], ts.tail)
    else do
      let (p, ts) ← pParamName ts
      let (d, ts) ← if isOp .assign ts.head? then do
          let (e, ts) ← pExpr n true ts.tail
          pure (some e, ts)
        else pure (none, ts)
      if d.isNone && hadDefault then fail "non-default argument follows default argument" ts
      else if isOp .rparen ts.head? then .ok ([(p, d)], ts.tail)
      else do
        let ((), ts) ← expect (.op .comma) ts
        let (more, ts) ← pParams n (hadDefault || d.isSome) ts
        .ok ((p, d) :: more, ts)

/-- A filter chain: `f(args) | g | ...` (`parse_filter`). `first` says the
first filter needs no leading `|` (`start_inline`). -/
def pFilterChain : Nat → Bool → List TokKind → PR (List FilterCall)
  | 0, _, ts => deep ts
  | n + 1, first, ts =>
    if first then do
      let (f, ts) ← pFilterOne n ts
      let (more, ts) ← pFilterChain n false ts
      .ok (f :: more, ts)
    else if isOp .pipe ts.head? then do
      let (f, ts) ← pFilterOne n ts.tail
      let (more, ts) ← pFilterChain n false ts
      .ok (f :: more, ts)
    else .ok ([], ts)

/-- An open tag: its name and the end tags it is looking for (upstream
`_tag_stack` / `_end_token_stack`). -/
abbrev TagStack := List (String × List String)

/-- Upstream `_fail_ut_eof`. -/
def failUnknownOrEof {α : Type} (name : Option String) (stack : TagStack) (ts : List TokKind) : PR α :=
  let expected := stack.flatMap (·.2)
  let quote := fun (s : String) => s!"'{s}'"
  let looking := match stack.head? with
    | some (_, ends) => some (" or ".intercalate (ends.map quote))
    | none => none
  let first := match name with
    | none => "Unexpected end of template."
    | some n => s!"Encountered unknown tag '{n}'."
  let mid := match looking with
    | some l =>
      if name.isSome && expected.contains (name.getD "") then
        s!" You probably made a nesting mistake. Jinja is expecting this tag, but currently looking for {l}."
      else s!" Jinja was looking for the following tags: {l}."
    | none => ""
  let last := match stack.head? with
    | some (tag, _) => s!" The innermost block that needs to be closed is '{tag}'."
    | none => ""
  fail (first ++ mid ++ last) ts

/-- Prepend template text, merging with a following text node. -/
def consText (v : String) : List Node → List Node
  | .text w :: b => .text (v ++ w) :: b
  | b => if v.isEmpty then b else .text v :: b

/-- Whether a block body is only whitespace text (required blocks). -/
def onlyWhitespace (body : List Node) : Bool :=
  body.all fun
    | .text s => s.toList.all isSpace && !s.isEmpty
    | _ => false

/-- The statement keywords (upstream `_statement_keywords` plus `call` and
`filter`). -/
def statementKeywords : List String :=
  ["for", "if", "block", "extends", "print", "macro", "include", "from", "import", "set",
   "with", "autoescape", "call", "filter"]

mutual

/-- `subparse(end_tokens)`: nodes up to an end tag (the remaining tokens
then start at the end tag's name) or the end of input. -/
def subparse : Nat → TagStack → List String → List TokKind → PR (List Node)
  | 0, _, _, ts => deep ts
  | n + 1, stack, ends, ts =>
    match ts with
    | [] => .ok ([], [])
    | .data v :: r => do
      let (body, r) ← subparse n stack ends r
      .ok (consText v body, r)
    | .varBegin :: r => do
      let (e, r) ← pTuple n true [] false r
      let ((), r) ← expect .varEnd r
      let (body, r) ← subparse n stack ends r
      .ok (.output e :: body, r)
    | .blockBegin :: r =>
      match r with
      | .name s :: _ =>
        if ends.contains s then .ok ([], r)
        else do
          let (nodes, r) ← pStatement n stack r
          let ((), r) ← expect .blockEnd r
          let (body, r) ← subparse n stack ends r
          .ok (nodes ++ body, r)
      | _ => fail "tag name expected" r
    | t :: _ => fail s!"unexpected '{describe t}'" ts

/-- `parse_statements(end_tokens, drop_needle)`: `: %}`, the body, and the
end tag's name when `drop` (otherwise the remaining tokens start at it). -/
def pStatements : Nat → TagStack → String → List String → Bool → List TokKind → PR (List Node)
  | 0, _, _, _, _, ts => deep ts
  | n + 1, stack, tag, ends, drop, ts => do
    let ts := if isOp .colon ts.head? then ts.tail else ts
    let ((), ts) ← expect .blockEnd ts
    let stack' := (tag, ends) :: stack
    let (body, ts) ← subparse n stack' ends ts
    if ts.isEmpty then failUnknownOrEof none stack' ts
    else .ok (body, if drop then ts.tail else ts)

/-- `parse_statement`: one tag, after `{%`. Returns the nodes it stands for
(`print` may stand for several outputs). -/
def pStatement : Nat → TagStack → List TokKind → PR (List Node)
  | 0, _, ts => deep ts
  | n + 1, stack, ts =>
    match ts with
    | .name "for" :: r => do
      let (target, r) ← pTarget n ["in"] false r
      let ((), r) ← expect (.name "in") r
      let (iter, r) ← pTuple n false ["recursive"] false r
      let (filt, r) ← if isName "if" r.head? then do
          let (e, r) ← pExpr n true r.tail
          pure (some e, r)
        else pure (none, r)
      let (recursive, r) := if isName "recursive" r.head? then (true, r.tail) else (false, r)
      let (body, r) ← pStatements n stack "for" ["endfor", "else"] false r
      if isName "endfor" r.head? then .ok ([.for_ target iter filt recursive body []], r.tail)
      else do
        let (els, r) ← pStatements n stack "for" ["endfor"] true r.tail
        .ok ([.for_ target iter filt recursive body els], r)
    | .name "if" :: r => do
      let ((branches, els), r) ← pIfRest n stack r
      .ok ([.if_ branches els], r)
    | .name "set" :: r => do
      let (target, r) ← pTarget n [] true r
      if isOp .assign r.head? then do
        let (e, r) ← pTuple n true [] false r.tail
        .ok ([.set target e], r)
      else do
        let (fs, r) ← pFilterChain n false r
        let (body, r) ← pStatements n stack "set" ["endset"] true r
        .ok ([.setBlock target fs body], r)
    | .name "macro" :: r => do
      let (name, r) ← pParamName r
      let ((), r) ← expect (.op .lparen) r
      let (params, r) ← pParams n false r
      let (body, r) ← pStatements n stack "macro" ["endmacro"] true r
      .ok ([.macro name params body], r)
    | .name "call" :: r => do
      let (params, r) ← if isOp .lparen r.head? then pParams n false r.tail else pure ([], r)
      let (c, r) ← pExpr n true r
      match c with
      | .call .. => do
        let (body, r) ← pStatements n stack "call" ["endcall"] true r
        .ok ([.callBlock params c body], r)
      | _ => fail "expected call" r
    | .name "filter" :: r => do
      let (fs, r) ← pFilterChain n true r
      let (body, r) ← pStatements n stack "filter" ["endfilter"] true r
      .ok ([.filterBlock fs body], r)
    | .name "include" :: r => do
      let (e, r) ← pExpr n true r
      let (ign, r) := match r with
        | .name "ignore" :: .name "missing" :: r' => (true, r')
        | _ => (false, r)
      let (ctx, r) := match r with
        | .name "with" :: .name "context" :: r' => (true, r')
        | .name "without" :: .name "context" :: r' => (false, r')
        | _ => (true, r)
      .ok ([.include e ign ctx], r)
    | .name "extends" :: r => do
      let (e, r) ← pExpr n true r
      .ok ([.extends e], r)
    | .name "block" :: r => do
      let (name, r) ← expectName r
      let (sc, r) := if isName "scoped" r.head? then (true, r.tail) else (false, r)
      let (req, r) := if isName "required" r.head? then (true, r.tail) else (false, r)
      if isOp .sub r.head? then
        fail "Block names in Jinja have to be valid Python identifiers and may not contain hyphens, use an underscore instead." r
      else do
        let (body, r) ← pStatements n stack "block" ["endblock"] true r
        if req && !onlyWhitespace body then
          fail "Required blocks can only contain comments or whitespace" r
        else
          let r := if isName name r.head? then r.tail else r
          .ok ([.block name sc req body], r)
    | .name "with" :: r => do
      let (assigns, r) ← pWithAssigns n true r
      let (body, r) ← pStatements n stack "with" ["endwith"] true r
      .ok ([.with_ assigns body], r)
    | .name "autoescape" :: r => do
      let (e, r) ← pExpr n true r
      let (body, r) ← pStatements n stack "autoescape" ["endautoescape"] true r
      .ok ([.autoescape e body], r)
    | .name "print" :: r => do
      let (es, r) ← pPrintItems n true r
      .ok (es.map Node.output, r)
    | .name "import" :: _ | .name "from" :: _ =>
      fail "'import' and 'from' are not supported by lean-jinja2" ts
    | .name s :: _ => failUnknownOrEof (some s) stack ts
    | _ => fail "tag name expected" ts

/-- The `if` test, body and what follows (`elif`, `else`, `endif`). -/
def pIfRest : Nat → TagStack → List TokKind → PR (List (Expr × List Node) × List Node)
  | 0, _, ts => deep ts
  | n + 1, stack, ts => do
    let (test, r) ← pTuple n false [] false ts
    let (body, r) ← pStatements n stack "if" ["elif", "else", "endif"] false r
    match r with
    | .name "elif" :: r => do
      let ((more, els), r) ← pIfRest n stack r
      .ok (((test, body) :: more, els), r)
    | .name "else" :: r => do
      let (els, r) ← pStatements n stack "if" ["endif"] true r
      .ok (([(test, body)], els), r)
    | _ => .ok (([(test, body)], []), r.tail)

/-- `with` assignments up to `%}`. -/
def pWithAssigns : Nat → Bool → List TokKind → PR (List (Target × Expr))
  | 0, _, ts => deep ts
  | n + 1, first, ts =>
    if ts.head? == some .blockEnd then .ok ([], ts)
    else do
      let ((), ts) ← if first then pure ((), ts) else expect (.op .comma) ts
      let (t, ts) ← pTarget n [] false ts
      let ((), ts) ← expect (.op .assign) ts
      let (e, ts) ← pExpr n true ts
      let (more, ts) ← pWithAssigns n false ts
      .ok ((t, e) :: more, ts)

/-- `print` expressions up to `%}`. -/
def pPrintItems : Nat → Bool → List TokKind → PR (List Expr)
  | 0, _, ts => deep ts
  | n + 1, first, ts =>
    if ts.head? == some .blockEnd then .ok ([], ts)
    else do
      let ((), ts) ← if first then pure ((), ts) else expect (.op .comma) ts
      let (e, ts) ← pExpr n true ts
      let (more, ts) ← pPrintItems n false ts
      .ok (e :: more, ts)

end

/-- The fuel `parseTokens` gives the parser: generous in the token count. -/
def fuelFor (ts : List TokKind) : Nat := 16 * (ts.length + 2)

end Parse

/-- Parse significant tokens into a template (upstream `Parser.parse`). -/
def parseTokens (ts : List TokKind) : Except ParseError (List Node) :=
  match Parse.subparse (Parse.fuelFor ts) [] [] ts with
  | .error e => .error e
  | .ok (body, []) => .ok body
  | .ok (_, r) => .error ⟨"unexpected tokens after the template", r.length⟩

end LeanJinja2
