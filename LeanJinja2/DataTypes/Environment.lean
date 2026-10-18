import LeanJinja2.DataTypes.Syntax
import LeanJinja2.DataTypes.Value

/-!
# The environment

Upstream `jinja2.Environment`: the syntax configuration, the autoescape
policy, the undefined policy, globals, custom filters/tests/functions, and the
template loader.

A loader is pure data here: `DictLoader` is its mapping, and
`FileSystemLoader` (in `Loader.lean`, the one effectful module) reads the
search path once into the same shape. Rendering never performs IO.
-/

namespace LeanJinja2

/-- Where templates come from (upstream `BaseLoader` subclasses). -/
inductive Loader where
  /-- `DictLoader(mapping)`: template names to sources. -/
  | dict (templates : List (String × String))
  /-- `FileSystemLoader(searchpath)`, as read from disk: the search path and
  the template files found under it (relative names with `/`). -/
  | fileSystem (searchpath : List String) (files : List (String × String))
  deriving Repr, Inhabited

/-- `DictLoader(mapping)`. -/
def DictLoader (templates : List (String × String)) : Loader := .dict templates

/-- An environment (upstream `Environment(...)`). Every field has upstream's
default; the delimiter and whitespace fields (`blockStart`, `trimBlocks`,
`lstripBlocks`, ...) come from `LexConfig`. -/
structure Environment extends LexConfig where
  /-- `autoescape=`: a constant, or `selectAutoescape [...]`. -/
  autoescape : AutoescapePolicy := .const false
  /-- `undefined=`: `Undefined`, `StrictUndefined`, `ChainableUndefined`, `DebugUndefined`. -/
  undefined : UndefinedPolicy := .default
  /-- `env.globals`, on top of the builtins (`builtinGlobals`). -/
  globals : List (String × Value) := []
  /-- Host functions, referenced from values as `Value.native name`. -/
  functions : List (String × NativeFn) := []
  /-- `env.filters` additions. -/
  filters : List (String × NativeFn) := []
  /-- `env.tests` additions. -/
  tests : List (String × NativeFn) := []
  /-- `loader=`. -/
  loader : Loader := .dict []
  /-- The rendering depth budget (upstream's recursion limit): exceeding it
  is a `RecursionError`. -/
  maxDepth : Nat := 1000
  /-- `policies["truncate.leeway"]`. -/
  truncateLeeway : Nat := 5
  /-- The seed of the generator the `random` filter and `lipsum` draw from
  (upstream uses Python's process-wide `random`): a render is a function of
  its inputs and this seed. -/
  randomSeed : Nat := 0
  /-- `policies["urlize.rel"]`. -/
  urlizeRel : Option String := some "noopener"
  /-- `policies["urlize.target"]`. -/
  urlizeTarget : Option String := none
  /-- `policies["urlize.extra_schemes"]`. -/
  urlizeExtraSchemes : List String := []

instance : Inhabited Environment := ⟨{}⟩

/-- `select_autoescape(enabled_extensions=("html", "htm", "xml"), disabled_extensions=(),
default_for_string=True, default=False)`. -/
def selectAutoescape (enabled : List String := ["html", "htm", "xml"]) (disabled : List String := [])
    (defaultForString : Bool := true) (default : Bool := false) : AutoescapePolicy :=
  .select enabled disabled defaultForString default

/-- Whether autoescaping is on for a template name (`none` for a template
from a string). -/
def AutoescapePolicy.enabledFor : AutoescapePolicy → Option String → Bool
  | .const b, _ => b
  | .select _ _ dfs _, none => dfs
  | .select en dis _ dflt, some name =>
    let lower := String.ofList (name.toList.map Char.toLower)
    if en.any (fun e => lower.endsWith ("." ++ e)) then true
    else if dis.any (fun e => lower.endsWith ("." ++ e)) then false
    else dflt

/-- The builtin globals (upstream `DEFAULT_NAMESPACE`). -/
def builtinGlobals : List (String × Value) :=
  [("range", .native "range"), ("dict", .native "dict"), ("lipsum", .native "lipsum"),
   ("cycler", .native "cycler"), ("joiner", .native "joiner"), ("namespace", .native "namespace")]

end LeanJinja2
