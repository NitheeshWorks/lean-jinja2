/-!
# Lexical syntax: delimiters, tokens

`LexConfig` is the part of upstream's `Environment` the lexer reads: the six
delimiters and the whitespace switches (`trim_blocks`, `lstrip_blocks`,
`keep_trailing_newline`, `newline_sequence`). Delimiters are non-empty; that is
an invariant field, not a comment.

A `Token` keeps the exact source text it was lexed from (`raw`), so the token
stream prints back to the source (`lex_print_roundtrip`). Tokens upstream
discards (whitespace inside tags, comments, the whitespace removed by `-`,
`trim_blocks` and `lstrip_blocks`, the raw-block delimiters, the stripped
trailing newline) are kept as `ws`/`comment`/`rawBegin`/`rawEnd` and skipped by
the parser.
-/

namespace LeanJinja2

/-- Operator tokens (upstream `lexer.operators`). -/
inductive Op where
  | add | sub | div | floordiv | mul | mod | pow | tilde
  | lbracket | rbracket | lparen | rparen | lbrace | rbrace
  | eq | ne | gt | gteq | lt | lteq | assign | dot | colon | pipe | comma | semicolon
  deriving DecidableEq, Repr, Inhabited

/-- The source text of an operator. -/
def Op.text : Op → String
  | .add => "+" | .sub => "-" | .div => "/" | .floordiv => "//" | .mul => "*"
  | .mod => "%" | .pow => "**" | .tilde => "~" | .lbracket => "[" | .rbracket => "]"
  | .lparen => "(" | .rparen => ")" | .lbrace => "{" | .rbrace => "}" | .eq => "=="
  | .ne => "!=" | .gt => ">" | .gteq => ">=" | .lt => "<" | .lteq => "<=" | .assign => "="
  | .dot => "." | .colon => ":" | .pipe => "|" | .comma => "," | .semicolon => ";"

/-- What a token is. Payloads are already decoded: a string literal's escapes
are resolved, a number's digits are a `Nat`, template data has its newlines
normalised to the configured sequence. -/
inductive TokKind where
  /-- Template text outside tags (upstream `data`). -/
  | data (value : String)
  /-- Whitespace the parser ignores: inside tags, or removed from template
  text by whitespace control, or the stripped trailing newline. -/
  | ws
  /-- A whole comment, delimiters included. -/
  | comment
  /-- `{% raw %}`; the raw content follows as `data`. -/
  | rawBegin
  /-- `{% endraw %}`. -/
  | rawEnd
  | varBegin
  | varEnd
  | blockBegin
  | blockEnd
  | name (s : String)
  /-- An integer literal (decimal, `0b`, `0o`, `0x`, underscores allowed). -/
  | int (n : Nat)
  /-- A float literal, value `m / 10^s` (exact decimal). -/
  | float (m : Nat) (s : Nat)
  | str (s : String)
  | op (o : Op)
  deriving DecidableEq, Repr, Inhabited

/-- A token: its kind and the exact source characters it covers. -/
structure Token where
  kind : TokKind
  raw : List Char
  deriving DecidableEq, Repr, Inhabited

/-- The characters a token list covers, in order. -/
def Token.printList (ts : List Token) : List Char := ts.flatMap Token.raw

/-- Print a token list back to source text. -/
def Token.print (ts : List Token) : String := String.ofList (Token.printList ts)

/-- Whether the parser ignores a token kind (upstream `ignored_tokens` plus the
raw delimiters, which upstream's `wrap` also drops). -/
def TokKind.ignored : TokKind → Bool
  | .ws | .comment | .rawBegin | .rawEnd => true
  | _ => false

/-- The significant token kinds, what the parser reads. -/
def significant (ts : List Token) : List TokKind :=
  (ts.filter (fun t => !t.kind.ignored)).map Token.kind

/-- The delimiters and whitespace switches of an environment (upstream
`Environment(block_start_string=..., trim_blocks=..., ...)`), including the
optional line statement and line comment prefixes. -/
structure LexConfig where
  blockStart : String := "{%"
  blockEnd : String := "%}"
  variableStart : String := "{{"
  variableEnd : String := "}}"
  commentStart : String := "{#"
  commentEnd : String := "#}"
  /-- Remove the first newline after a block tag. -/
  trimBlocks : Bool := false
  /-- Strip spaces and tabs from the start of a line up to a block tag. -/
  lstripBlocks : Bool := false
  /-- Keep a single trailing newline of the source. -/
  keepTrailingNewline : Bool := false
  /-- The newline sequence template data is normalised to. -/
  newlineSequence : String := "\n"
  /-- `line_statement_prefix`: a line whose first non-blank text is this
  prefix is a statement, up to the end of the line. -/
  lineStatementPrefix : Option String := none
  /-- `line_comment_prefix`: from this prefix to the end of the line is a
  comment. -/
  lineCommentPrefix : Option String := none
  /-- Delimiters are non-empty (an empty delimiter would match everywhere). -/
  h_nonempty : blockStart ≠ "" ∧ blockEnd ≠ "" ∧ variableStart ≠ "" ∧ variableEnd ≠ "" ∧
    commentStart ≠ "" ∧ commentEnd ≠ "" := by decide
  /-- So are the line prefixes, when set. -/
  h_lineNonempty : lineStatementPrefix ≠ some "" ∧ lineCommentPrefix ≠ some "" := by decide

instance : Inhabited LexConfig := ⟨{}⟩

/-- Upstream's defaults: `{% %}`, `{{ }}`, `{# #}`, no trimming. -/
def LexConfig.default : LexConfig := {}

end LeanJinja2
