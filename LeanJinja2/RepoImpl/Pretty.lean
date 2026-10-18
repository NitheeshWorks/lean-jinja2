import LeanJinja2.DataTypes.Ast
import LeanJinja2.DataTypes.Syntax
import LeanJinja2.RepoImpl.Chars
import LeanJinja2.RepoImpl.LexFast
import LeanJinja2.RepoImpl.Parser

/-!
# The pretty printer

Prints a template back to source in a canonical form the parser reads back
to the same AST (`parse_pretty_roundtrip`): every compound expression is
parenthesised, every token inside a tag is followed by one space, and
statements use their full spelling (`{% endfor %}`, explicit `with context`).

The printer works in two stages: `Pretty.nodes` gives the significant token
stream, `Pretty.render` spells it out.
-/

namespace LeanJinja2

namespace Pretty

abbrev nm (s : String) : TokKind := .name s
abbrev op (o : Op) : TokKind := .op o

def binTok : BinOp → List TokKind
  | .add => [op .add] | .sub => [op .sub] | .mul => [op .mul] | .div => [op .div]
  | .floordiv => [op .floordiv] | .mod => [op .mod] | .pow => [op .pow]
  | .and => [nm "and"] | .or => [nm "or"]

def cmpTok : CmpOp → List TokKind
  | .eq => [op .eq] | .ne => [op .ne] | .lt => [op .lt] | .lteq => [op .lteq]
  | .gt => [op .gt] | .gteq => [op .gteq] | .in => [nm "in"] | .notin => [nm "not", nm "in"]

def constToks : Const → List TokKind
  | .none => [nm "none"]
  | .bool b => [nm (if b then "true" else "false")]
  | .int i => [.int i.toNat]
  | .float m s => [.float m.toNat s]
  | .str s => [.str s]

/-- Positional then keyword arguments, comma-separated (printed already). -/
def joinArgs (pos kw : List TokKind) : List TokKind :=
  pos ++ (if !pos.isEmpty && !kw.isEmpty then [op .comma] else []) ++ kw

/-- Arguments in parentheses, or nothing when there are none. -/
def parenArgs (pos kw : List TokKind) : List TokKind :=
  if pos.isEmpty && kw.isEmpty then [] else [op .lparen] ++ joinArgs pos kw ++ [op .rparen]

mutual
/-- An expression: an atom, or a compound in parentheses. -/
def expr : Expr → List TokKind
  | .const c => constToks c
  | .name n => [nm n]
  | .tuple [x] => [op .lparen] ++ expr x ++ [op .comma, op .rparen]
  | .tuple xs => [op .lparen] ++ exprs xs ++ [op .rparen]
  | .list xs => [op .lbracket] ++ exprs xs ++ [op .rbracket]
  | .dict ps => [op .lbrace] ++ pairs ps ++ [op .rbrace]
  | .getattr e a => [op .lparen] ++ expr e ++ [op .dot, nm a, op .rparen]
  | .getitem e i => [op .lparen] ++ expr e ++ [op .lbracket] ++ subscript i ++ [op .rbracket, op .rparen]
  | .slice a b c => optExpr a ++ [op .colon] ++ optExpr b ++ optStep c
  | .call f args kw =>
    [op .lparen] ++ expr f ++ [op .lparen] ++ joinArgs (exprs args) (kwargs kw) ++ [op .rparen, op .rparen]
  | .filter e n args kw => [op .lparen] ++ expr e ++ [op .pipe, nm n] ++ parenArgs (exprs args) (kwargs kw) ++
      [op .rparen]
  | .test e n args kw => [op .lparen] ++ expr e ++ [nm "is", nm n] ++ parenArgs (exprs args) (kwargs kw) ++
      [op .rparen]
  | .unop .neg e => [op .lparen, op .sub] ++ expr e ++ [op .rparen]
  | .unop .pos e => [op .lparen, op .add] ++ expr e ++ [op .rparen]
  | .unop .not e => [op .lparen, nm "not"] ++ expr e ++ [op .rparen]
  | .binop o l r => [op .lparen] ++ expr l ++ binTok o ++ expr r ++ [op .rparen]
  | .compare e ops => [op .lparen] ++ expr e ++ cmps ops ++ [op .rparen]
  | .concat (x :: xs) => [op .lparen] ++ expr x ++ tildes xs ++ [op .rparen]
  | .concat [] => [op .lparen, op .rparen]
  | .cond t b none => [op .lparen] ++ expr b ++ [nm "if"] ++ expr t ++ [op .rparen]
  | .cond t b (some e) => [op .lparen] ++ expr b ++ [nm "if"] ++ expr t ++ [nm "else"] ++ expr e ++
      [op .rparen]

/-- Comma-separated expressions. -/
def exprs : List Expr → List TokKind
  | [] => []
  | [x] => expr x
  | x :: xs => expr x ++ [op .comma] ++ exprs xs

def pairs : List (Expr × Expr) → List TokKind
  | [] => []
  | [(k, v)] => expr k ++ [op .colon] ++ expr v
  | (k, v) :: ps => expr k ++ [op .colon] ++ expr v ++ [op .comma] ++ pairs ps

/-- `a : b : c` inside a subscript, or an expression. -/
def subscript : Expr → List TokKind
  | .slice a b c => optExpr a ++ [op .colon] ++ optExpr b ++ optStep c
  | e => expr e

def optStep : Option Expr → List TokKind
  | some e => [op .colon] ++ expr e
  | none => []

def optExpr : Option Expr → List TokKind
  | some e => expr e
  | none => []

def cmps : List (CmpOp × Expr) → List TokKind
  | [] => []
  | (o, e) :: ops => cmpTok o ++ expr e ++ cmps ops

def tildes : List Expr → List TokKind
  | [] => []
  | x :: xs => [op .tilde] ++ expr x ++ tildes xs

def kwargs : List (String × Expr) → List TokKind
  | [] => []
  | [(k, v)] => [nm k, op .assign] ++ expr v
  | (k, v) :: kw => [nm k, op .assign] ++ expr v ++ [op .comma] ++ kwargs kw
end

/-- An assignment target: a name, `ns.attr`, or a parenthesised tuple. -/
def target : Target → List TokKind
  | .name n => [nm n]
  | .nsAttr n a => [nm n, op .dot, nm a]
  | .tuple [t] => [op .lparen] ++ target t ++ [op .comma, op .rparen]
  | .tuple ts => [op .lparen] ++ targets ts ++ [op .rparen]
where
  targets : List Target → List TokKind
    | [] => []
    | [t] => target t
    | t :: ts => target t ++ [op .comma] ++ targets ts

def filterCall (f : FilterCall) : List TokKind := [nm f.name] ++ parenArgs (exprs f.args) (kwargs f.kwargs)

/-- `f1 | f2 | ...` (the first without a leading `|`). -/
def filterChain : List FilterCall → List TokKind
  | [] => []
  | [f] => filterCall f
  | f :: fs => filterCall f ++ [op .pipe] ++ filterChain fs

def param : Param → List TokKind
  | (n, none) => [nm n]
  | (n, some e) => [nm n, op .assign] ++ expr e

def params : List Param → List TokKind
  | [] => []
  | [p] => param p
  | p :: ps => param p ++ [op .comma] ++ params ps

def assigns : List (Target × Expr) → List TokKind
  | [] => []
  | [(t, e)] => target t ++ [op .assign] ++ expr e
  | (t, e) :: as => target t ++ [op .assign] ++ expr e ++ [op .comma] ++ assigns as

/-- A block tag `{% ... %}` around its tokens. -/
def tag (ks : List TokKind) : List TokKind := [.blockBegin] ++ ks ++ [.blockEnd]

mutual
/-- A node's significant tokens. -/
def node : Node → List TokKind
  | .text s => [.data s]
  | .output e => [.varBegin] ++ expr e ++ [.varEnd]
  | .if_ [] els => tag [nm "if", nm "false"] ++ nodes els ++ tag [nm "endif"]
  | .if_ ((t, b) :: bs) els =>
    tag ([nm "if"] ++ expr t) ++ nodes b ++ elifs bs ++
      (if els.isEmpty then [] else tag [nm "else"] ++ nodes els) ++ tag [nm "endif"]
  | .for_ t it fl rc body els =>
    tag ([nm "for"] ++ target t ++ [nm "in"] ++ expr it ++
        (match fl with | some f => [nm "if"] ++ expr f | none => []) ++
        (if rc then [nm "recursive"] else [])) ++ nodes body ++
      (if els.isEmpty then [] else tag [nm "else"] ++ nodes els) ++ tag [nm "endfor"]
  | .set t e => tag ([nm "set"] ++ target t ++ [op .assign] ++ expr e)
  | .setBlock t fs body =>
    tag ([nm "set"] ++ target t ++ (fs.flatMap (fun f => [op .pipe] ++ filterCall f))) ++ nodes body ++
      tag [nm "endset"]
  | .macro n ps body =>
    tag ([nm "macro", nm n, op .lparen] ++ params ps ++ [op .rparen]) ++ nodes body ++ tag [nm "endmacro"]
  | .callBlock ps c body =>
    tag ([nm "call", op .lparen] ++ params ps ++ [op .rparen] ++ expr c) ++ nodes body ++ tag [nm "endcall"]
  | .include e ig wc =>
    tag ([nm "include"] ++ expr e ++ (if ig then [nm "ignore", nm "missing"] else []) ++
      [nm (if wc then "with" else "without"), nm "context"])
  | .extends e => tag ([nm "extends"] ++ expr e)
  | .block n sc req body =>
    tag ([nm "block", nm n] ++ (if sc then [nm "scoped"] else []) ++ (if req then [nm "required"] else [])) ++
      nodes body ++ tag [nm "endblock"]
  | .with_ as body => tag ([nm "with"] ++ assigns as) ++ nodes body ++ tag [nm "endwith"]
  | .filterBlock fs body => tag ([nm "filter"] ++ filterChain fs) ++ nodes body ++ tag [nm "endfilter"]
  | .autoescape e body => tag ([nm "autoescape"] ++ expr e) ++ nodes body ++ tag [nm "endautoescape"]

def nodes : List Node → List TokKind
  | [] => []
  | n :: ns => node n ++ nodes ns

def elifs : List (Expr × List Node) → List TokKind
  | [] => []
  | (t, b) :: bs => tag ([nm "elif"] ++ expr t) ++ nodes b ++ elifs bs
end

/-- Escape a string literal's content: backslash, quote and carriage return. -/
def escapeStr : List Char → List Char
  | [] => []
  | c :: cs =>
    (if c == '\\' then ['\\', '\\'] else if c == '\'' then ['\\', '\''] else if c == '\r' then ['\\', 'r']
      else [c]) ++ escapeStr cs

/-- The text of a token, followed by the space that separates tokens inside a
tag (none after template data or an end delimiter). -/
def tokText : TokKind → List Char
  | .data s => s.toList
  | .varBegin => "{{ ".toList
  | .blockBegin => "{% ".toList
  | .varEnd => "}}".toList
  | .blockEnd => "%}".toList
  | .name s => s.toList ++ [' ']
  | .int n => natDigits n ++ [' ']
  | .float m s => natDigits m ++ ['e', '-'] ++ natDigits s ++ [' ']
  | .str s => '\'' :: escapeStr s.toList ++ ['\'', ' ']
  | .op o => o.text.toList ++ [' ']
  | .ws | .comment | .rawBegin | .rawEnd => []

/-- Spell out a significant token stream. -/
def render (ks : List TokKind) : List Char := ks.flatMap tokText

end Pretty

/-- Print a template in canonical form. A final newline is doubled, since the
lexer strips one trailing newline (upstream's `keep_trailing_newline=False`). -/
def pretty (t : List Node) : String :=
  let cs := Pretty.render (Pretty.nodes t)
  String.ofList (if cs.getLast? == some '\n' then cs ++ ['\n'] else cs)

end LeanJinja2

namespace LeanJinja2

/-- Parse template source: lex, keep the significant tokens, parse
(upstream `Environment.parse`). It lexes in place (`lexFast`); `parse_eq`
states it through `lex`. -/
def parse (cfg : LexConfig) (src : String) : Except ParseError (List Node) :=
  match lexFast cfg src with
  | .error e => .error ⟨e.msg, 0⟩
  | .ok ts => parseTokens (significantL ts)

end LeanJinja2
