import LeanJinja2

/-!
# Conformance cases

Each case re-expresses one upstream test (https://github.com/pallets/jinja,
`tests/`) in Lean and names it, so `docs/traceability.toml` can point at both.
The upstream suite is the behavioural specification; no upstream code is
copied. Python objects with attributes become dicts (attribute access falls
back to items, as upstream's `getattr` does).

Run with `lake exe conformance`.
-/

open LeanJinja2

structure Case where
  /-- Upstream test this mirrors, e.g. `tests/test_path.py::test_int`. -/
  upstream : String
  name : String
  run : IO Bool

/-- Render `src` from a string and compare. -/
def renders (upstream : String) (src : String) (expected : String)
    (vars : List (String × Value) := []) (env : Environment := {}) : Case :=
  { upstream, name := upstream.splitOn "::" |>.getLast!, run := do
      match env.fromString src >>= (·.render vars) with
      | .ok out =>
        if out == expected then pure true
        else do IO.println s!"      got {repr out}, expected {repr expected}"; pure false
      | .error e => do IO.println s!"      error {e}"; pure false }

/-- Render a named template from the environment's loader and compare. -/
def rendersT (upstream : String) (env : Environment) (name : String) (expected : String)
    (vars : List (String × Value) := []) : Case :=
  { upstream, name := upstream.splitOn "::" |>.getLast!, run := do
      match env.getTemplate name >>= (·.render vars) with
      | .ok out =>
        if out == expected then pure true
        else do IO.println s!"      got {repr out}, expected {repr expected}"; pure false
      | .error e => do IO.println s!"      error {e}"; pure false }

/-- Loading or rendering fails with an error the predicate accepts. -/
def fails (upstream : String) (src : String) (p : TemplateError → Bool)
    (vars : List (String × Value) := []) (env : Environment := {}) : Case :=
  { upstream, name := upstream.splitOn "::" |>.getLast!, run := do
      match env.fromString src >>= (·.render vars) with
      | .ok out => do IO.println s!"      rendered {repr out}, expected an error"; pure false
      | .error e => if p e then pure true else do IO.println s!"      wrong error {e}"; pure false }

def failsT (upstream : String) (env : Environment) (name : String) (p : TemplateError → Bool)
    (vars : List (String × Value) := []) : Case :=
  { upstream, name := upstream.splitOn "::" |>.getLast!, run := do
      match env.getTemplate name >>= (·.render vars) with
      | .ok out => do IO.println s!"      rendered {repr out}, expected an error"; pure false
      | .error e => if p e then pure true else do IO.println s!"      wrong error {e}"; pure false }

def isSyntax : TemplateError → Bool
  | .syntax .. | .assertion _ => true
  | _ => false
def isUndefined : TemplateError → Bool
  | .undefined _ => true
  | _ => false
def isType : TemplateError → Bool
  | .typeError _ => true
  | _ => false
def isRuntime : TemplateError → Bool
  | .runtime _ => true
  | _ => false
def isOverflow : TemplateError → Bool
  | .overflow m => m == "Range too big. The sandbox blocks ranges larger than MAX_RANGE (100000)."
  | _ => false

def msgHas (sub : String) : TemplateError → Bool
  | e => ((toString e).splitOn sub).length > 1

def ints (ns : List Int) : Value := .list (ns.map Value.int)
def strs (ss : List String) : Value := .list (ss.map Value.str)
def obj (kvs : List (String × Value)) : Value := Value.ofDict kvs
def range' (n : Nat) : Value := ints ((List.range n).map (fun (k : Nat) => (k : Int)))

def F := "tests/test_filters.py::TestFilter::"
def T := "tests/test_tests.py::TestTestsCase::"
def FL := "tests/test_core_tags.py::TestForLoop::"
def IF := "tests/test_core_tags.py::TestIfCondition::"
def MA := "tests/test_core_tags.py::TestMacros::"
def SE := "tests/test_core_tags.py::TestSet::"
def WI := "tests/test_core_tags.py::TestWith::"
def LX := "tests/test_lexnparse.py::TestLexer::"
def PA := "tests/test_lexnparse.py::TestParser::"
def SY := "tests/test_lexnparse.py::TestSyntax::"
def LS := "tests/test_lexnparse.py::TestLstripBlocks::"
def TB := "tests/test_lexnparse.py::TestTrimBlocks::"
def IN := "tests/test_inheritance.py::TestInheritance::"
def UN := "tests/test_api.py::TestUndefined::"

def trimEnv : Environment := { trimBlocks := true }
def ae : Environment := { autoescape := true }
def lstrip : Environment := { lstripBlocks := true }
def lstripTrim : Environment := { lstripBlocks := true, trimBlocks := true }

def filterCases : List Case := [
  renders (F ++ "test_capitalize") "{{ \"foo bar\"|capitalize }}" "Foo bar",
  renders (F ++ "test_center") "{{ \"foo\"|center(9) }}" "   foo   ",
  renders (F ++ "test_default")
    "{{ missing|default('no') }}|{{ false|default('no') }}|{{ false|default('no', true) }}|{{ given|default('no') }}"
    "no|False|no|yes" [("given", "yes")],
  renders (F ++ "test_dictsort[]") "{{ foo|dictsort() }}" "[('aa', 0), ('AB', 3), ('b', 1), ('c', 2)]"
    [("foo", obj [("aa", 0), ("b", 1), ("c", 2), ("AB", 3)])],
  renders (F ++ "test_dictsort[true]") "{{ foo|dictsort(true) }}" "[('AB', 3), ('aa', 0), ('b', 1), ('c', 2)]"
    [("foo", obj [("aa", 0), ("b", 1), ("c", 2), ("AB", 3)])],
  renders (F ++ "test_dictsort[by=value]") "{{ foo|dictsort(by=\"value\") }}"
    "[('aa', 0), ('b', 1), ('c', 2), ('AB', 3)]" [("foo", obj [("aa", 0), ("b", 1), ("c", 2), ("AB", 3)])],
  renders (F ++ "test_dictsort[reverse=true]") "{{ foo|dictsort(reverse=true) }}"
    "[('c', 2), ('b', 1), ('AB', 3), ('aa', 0)]" [("foo", obj [("aa", 0), ("b", 1), ("c", 2), ("AB", 3)])],
  renders (F ++ "test_batch") "{{ foo|batch(3)|list }}|{{ foo|batch(3, 'X')|list }}"
    "[[0, 1, 2], [3, 4, 5], [6, 7, 8], [9]]|[[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 'X', 'X']]"
    [("foo", range' 10)],
  renders (F ++ "test_slice") "{{ foo|slice(3)|list }}|{{ foo|slice(3, 'X')|list }}"
    "[[0, 1, 2, 3], [4, 5, 6], [7, 8, 9]]|[[0, 1, 2, 3], [4, 5, 6, 'X'], [7, 8, 9, 'X']]"
    [("foo", range' 10)],
  renders (F ++ "test_escape") "{{ '<\">&'|escape }}" "&lt;&#34;&gt;&amp;",
  renders (F ++ "test_trim[None]") "{{ foo|trim(chars) }}" "..stays.." [("foo", "  ..stays.."), ("chars", .none)],
  renders (F ++ "test_trim[.]") "{{ foo|trim(chars) }}" "  ..stays" [("foo", "  ..stays.."), ("chars", ".")],
  renders (F ++ "test_trim[ .]") "{{ foo|trim(chars) }}" "stays" [("foo", "  ..stays.."), ("chars", " .")],
  renders (F ++ "test_striptags") "{{ foo|striptags }}" "just a small example link to a webpage"
    [("foo", "  <p>just a small   \n <a href=\"#\">example</a> link</p>\n<p>to a webpage</p> <!-- <p>and some commented stuff</p> -->")],
  renders (F ++ "test_filesizeformat")
    "{{ 100|filesizeformat }}|{{ 1000|filesizeformat }}|{{ 1000000|filesizeformat }}|{{ 1000000000|filesizeformat }}|{{ 1000000000000|filesizeformat }}|{{ 100|filesizeformat(true) }}|{{ 1000|filesizeformat(true) }}|{{ 1000000|filesizeformat(true) }}|{{ 1000000000|filesizeformat(true) }}|{{ 1000000000000|filesizeformat(true) }}"
    "100 Bytes|1.0 kB|1.0 MB|1.0 GB|1.0 TB|100 Bytes|1000 Bytes|976.6 KiB|953.7 MiB|931.3 GiB",
  renders (F ++ "test_filesizeformat_issue59")
    "{{ 300|filesizeformat }}|{{ 3000|filesizeformat }}|{{ 3000000|filesizeformat }}|{{ 3000000000|filesizeformat }}|{{ 3000000000000|filesizeformat }}|{{ 300|filesizeformat(true) }}|{{ 3000|filesizeformat(true) }}|{{ 3000000|filesizeformat(true) }}"
    "300 Bytes|3.0 kB|3.0 MB|3.0 GB|3.0 TB|300 Bytes|2.9 KiB|2.9 MiB",
  renders (F ++ "test_first") "{{ foo|first }}" "0" [("foo", range' 10)],
  renders (F ++ "test_float[42]") "{{ value|float }}" "42.0" [("value", "42")],
  renders (F ++ "test_float[abc]") "{{ value|float }}" "0.0" [("value", "abc")],
  renders (F ++ "test_float[32.32]") "{{ value|float }}" "32.32" [("value", "32.32")],
  renders (F ++ "test_float_default") "{{ value|float(default=1.0) }}" "1.0" [("value", "abc")],
  renders (F ++ "test_format") "{{ '%s|%s'|format('a', 'b') }}" "a|b",
  renders (F ++ "test_indent[ff]") "{{ foo|indent(2, false, false) }}" "\n  foo bar\n  \"baz\"\n"
    [("foo", "\nfoo bar\n\"baz\"\n")],
  renders (F ++ "test_indent[ft]") "{{ foo|indent(2, false, true) }}" "\n  foo bar\n  \"baz\"\n  "
    [("foo", "\nfoo bar\n\"baz\"\n")],
  renders (F ++ "test_indent[tf]") "{{ foo|indent(2, true, false) }}" "  \n  foo bar\n  \"baz\"\n"
    [("foo", "\nfoo bar\n\"baz\"\n")],
  renders (F ++ "test_indent[tt]") "{{ foo|indent(2, true, true) }}" "  \n  foo bar\n  \"baz\"\n  "
    [("foo", "\nfoo bar\n\"baz\"\n")],
  renders (F ++ "test_indent[plain]") "{{ \"jinja\"|indent }}|{{ \"jinja\"|indent(first=true) }}|{{ \"jinja\"|indent(blank=true) }}"
    "jinja|    jinja|jinja",
  renders (F ++ "test_indent_width_string") "{{ 'jinja\nflask'|indent(width='>>> ', first=True) }}"
    ">>> jinja\n>>> flask",
  renders (F ++ "test_int[42]") "{{ value|int }}" "42" [("value", "42")],
  renders (F ++ "test_int[abc]") "{{ value|int }}" "0" [("value", "abc")],
  renders (F ++ "test_int[32.32]") "{{ value|int }}" "32" [("value", "32.32")],
  renders (F ++ "test_int[big]") "{{ value|int }}" "12345678901234567890" [("value", "12345678901234567890")],
  renders (F ++ "test_int_base[0x4d32]") "{{ value|int(base=base) }}" "19762" [("value", "0x4d32"), ("base", 16)],
  renders (F ++ "test_int_base[011]") "{{ value|int(base=base) }}" "9" [("value", "011"), ("base", 8)],
  renders (F ++ "test_int_base[0x33Z]") "{{ value|int(base=base) }}" "0" [("value", "0x33Z"), ("base", 16)],
  renders (F ++ "test_int_default") "{{ value|int(default=1) }}" "1" [("value", "abc")],
  renders (F ++ "test_join") "{{ [1, 2, 3]|join(\"|\") }}" "1|2|3",
  renders (F ++ "test_join[autoescape]") "{{ [\"<foo>\", \"<span>foo</span>\"|safe]|join }}"
    "&lt;foo&gt;<span>foo</span>" (env := ae),
  renders (F ++ "test_join_attribute") "{{ users|join(', ', 'username') }}" "foo, bar"
    [("users", .list [obj [("username", "foo")], obj [("username", "bar")]])],
  renders (F ++ "test_last") "{{ foo|last }}" "9" [("foo", range' 10)],
  renders (F ++ "test_length") "{{ \"hello world\"|length }}" "11",
  renders (F ++ "test_lower") "{{ \"FOO\"|lower }}" "foo",
  renders (F ++ "test_items") "{{ d|items|list }}" "[(0, 'a'), (1, 'b'), (2, 'c')]"
    [("d", .dict [(.int 0, "a"), (.int 1, "b"), (.int 2, "c")])],
  renders (F ++ "test_items_undefined") "{{ d|items|list }}" "[]",
  renders (F ++ "test_reverse") "{{ 'foobar'|reverse|join }}|{{ [1, 2, 3]|reverse|list }}" "raboof|[3, 2, 1]",
  renders (F ++ "test_string") "{{ obj|string }}" "[1, 2, 3, 4, 5]" [("obj", ints [1, 2, 3, 4, 5])],
  renders (F ++ "test_title")
    "{{ \"foo bar\"|title }}|{{ \"foo's bar\"|title }}|{{ \"foo   bar\"|title }}|{{ \"f bar f\"|title }}|{{ \"foo-bar\"|title }}|{{ \"foo\tbar\"|title }}|{{ \"FOO\tBAR\"|title }}|{{ \"foo (bar)\"|title }}|{{ \"foo {bar}\"|title }}|{{ \"foo [bar]\"|title }}|{{ \"foo <bar>\"|title }}"
    "Foo Bar|Foo's Bar|Foo   Bar|F Bar F|Foo-Bar|Foo\tBar|Foo\tBar|Foo (Bar)|Foo {Bar}|Foo [Bar]|Foo <Bar>",
  renders (F ++ "test_truncate")
    "{{ data|truncate(15, true, \">>>\") }}|{{ data|truncate(15, false, \">>>\") }}|{{ smalldata|truncate(15) }}"
    "foobar baz b>>>|foobar baz>>>|foobar baz bar"
    [("data", .str (String.join (List.replicate 1000 "foobar baz bar"))), ("smalldata", "foobar baz bar")],
  renders (F ++ "test_truncate_very_short") "{{ \"foo bar baz\"|truncate(9) }}|{{ \"foo bar baz\"|truncate(9, true) }}"
    "foo bar baz|foo bar baz",
  renders (F ++ "test_truncate_end_length") "{{ \"Joel is a slug\"|truncate(7, true) }}" "Joel...",
  renders (F ++ "test_upper") "{{ \"foo\"|upper }}" "FOO",
  renders (F ++ "test_wordcount") "{{ \"foo bar baz\"|wordcount }}" "3",
  fails (F ++ "test_wordcount[strict]") "{{ s|wordcount }}" isUndefined (env := { undefined := .strict }),
  renders (F ++ "test_block") "{% filter lower|escape %}<HEHE>{% endfilter %}" "&lt;hehe&gt;",
  renders (F ++ "test_chaining") "{{ ['<foo>', '<bar>']|first|upper|escape }}" "&lt;FOO&gt;",
  renders (F ++ "test_sum") "{{ [1, 2, 3, 4, 5, 6]|sum }}" "21",
  renders (F ++ "test_sum_attributes") "{{ values|sum('value') }}" "42"
    [("values", .list [obj [("value", 23)], obj [("value", 1)], obj [("value", 18)]])],
  renders (F ++ "test_sum_attributes_nested") "{{ values|sum('real.value') }}" "42"
    [("values", .list [obj [("real", obj [("value", 23)])], obj [("real", obj [("value", 1)])],
      obj [("real", obj [("value", 18)])]])],
  renders (F ++ "test_sum_attributes_tuple") "{{ values.items()|sum('1') }}" "42"
    [("values", obj [("foo", 23), ("bar", 1), ("baz", 18)])],
  renders (F ++ "test_abs") "{{ -1|abs }}|{{ 1|abs }}" "1|1",
  renders (F ++ "test_round_positive")
    "{{ 2.7|round }}|{{ 2.1|round }}|{{ 2.1234|round(3, 'floor') }}|{{ 2.1|round(0, 'ceil') }}" "3.0|2.0|2.123|3.0",
  renders (F ++ "test_round_negative")
    "{{ 21.3|round(-1)}}|{{ 21.3|round(-1, 'ceil')}}|{{ 21.3|round(-1, 'floor')}}" "20.0|30.0|20.0",
  renders (F ++ "test_xmlattr")
    "{{ {'foo': 42, 'bar': 23, 'fish': none, 'spam': missing, 'blub:blub': '<?>'}|xmlattr }}"
    " foo=\"42\" bar=\"23\" blub:blub=\"&lt;?&gt;\"",
  fails (F ++ "test_xmlattr_key_invalid") "{{ {key: 'my_class'}|xmlattr }}" (msgHas "Invalid character")
    [("key", "class onclick=alert(1)")],
  renders (F ++ "test_sort1") "{{ [2, 3, 1]|sort }}|{{ [2, 3, 1]|sort(true) }}" "[1, 2, 3]|[3, 2, 1]",
  renders (F ++ "test_sort2") "{{ \"\".join([\"c\", \"A\", \"b\", \"D\"]|sort) }}" "AbcD",
  renders (F ++ "test_sort3") "{{ ['foo', 'Bar', 'blah']|sort }}" "['Bar', 'blah', 'foo']",
  renders (F ++ "test_sort4") "{{ items|sort(attribute='value')|map(attribute='value')|join }}" "1234"
    [("items", .list ([3, 2, 4, 1].map (fun (i : Int) => obj [("value", .int i)])))],
  renders (F ++ "test_sort6") "{{ items|sort(attribute='value1,value2')|map('string')|join }}"
    "{'value1': 2, 'value2': 1}{'value1': 2, 'value2': 2}{'value1': 2, 'value2': 5}{'value1': 3, 'value2': 1}"
    [("items", .list ([(3, 1), (2, 2), (2, 1), (2, 5)].map (fun (p : Int × Int) =>
      obj [("value1", .int p.1), ("value2", .int p.2)])))],
  renders (F ++ "test_unique") "{{ \"\".join([\"b\", \"A\", \"a\", \"b\"]|unique) }}" "bA",
  renders (F ++ "test_unique_case_sensitive") "{{ \"\".join([\"b\", \"A\", \"a\", \"b\"]|unique(true)) }}" "bAa",
  renders (F ++ "test_unique_attribute") "{{ items|unique(attribute='value')|map(attribute='value')|join }}" "3241"
    [("items", .list ([3, 2, 4, 1, 2].map (fun (i : Int) => obj [("value", .int i)])))],
  renders (F ++ "test_min_max[min]") "{{ [\"a\", \"B\"]|min }}" "a",
  renders (F ++ "test_min_max[min-cs]") "{{ [\"a\", \"B\"]|min(case_sensitive=true) }}" "B",
  renders (F ++ "test_min_max[min-empty]") "{{ []|min }}" "",
  renders (F ++ "test_min_max[max]") "{{ [\"a\", \"B\"]|max }}" "B",
  renders (F ++ "test_min_max[max-cs]") "{{ [\"a\", \"B\"]|max(case_sensitive=true) }}" "a",
  renders (F ++ "test_min_max_attribute[min]") "{{ (items|min(attribute=\"value\")).value }}" "1"
    [("items", .list ([5, 1, 9].map (fun (i : Int) => obj [("value", .int i)])))],
  renders (F ++ "test_groupby")
    "{%- for grouper, list in [{'foo': 1, 'bar': 2}, {'foo': 2, 'bar': 3}, {'foo': 1, 'bar': 1}, {'foo': 3, 'bar': 4}]|groupby('foo') -%}{{ grouper }}{% for x in list %}: {{ x.foo }}, {{ x.bar }}{% endfor %}|{%- endfor %}"
    "1: 1, 2: 1, 1|2: 2, 3|3: 3, 4|",
  renders (F ++ "test_groupby_tuple_index")
    "{%- for grouper, list in [('a', 1), ('a', 2), ('b', 1)]|groupby(0) -%}{{ grouper }}{% for x in list %}:{{ x.1 }}{% endfor %}|{%- endfor %}"
    "a:1:2|b:1|",
  renders (F ++ "test_groupby_default")
    "{% for city, items in users|groupby('city', default='NY') %}{{ city }}: {{ items|map(attribute='name')|join(', ') }}\n{% endfor %}"
    "NY: emma, john\nWA: smith\n"
    [("users", .list [obj [("name", "emma"), ("city", "NY")], obj [("name", "smith"), ("city", "WA")],
      obj [("name", "john")]])],
  renders (F ++ "test_groupby_case[False]")
    "{% for k, vs in data|groupby('k', case_sensitive=cs) %}{{ k }}: {{ vs|join(', ', attribute='v') }}\n{% endfor %}"
    "a: 1, 3\nb: 2\n"
    [("data", .list [obj [("k", "a"), ("v", 1)], obj [("k", "b"), ("v", 2)], obj [("k", "A"), ("v", 3)]]),
     ("cs", false)],
  renders (F ++ "test_groupby_case[True]")
    "{% for k, vs in data|groupby('k', case_sensitive=cs) %}{{ k }}: {{ vs|join(', ', attribute='v') }}\n{% endfor %}"
    "A: 3\na: 1\nb: 2\n"
    [("data", .list [obj [("k", "a"), ("v", 1)], obj [("k", "b"), ("v", 2)], obj [("k", "A"), ("v", 3)]]),
     ("cs", true)],
  renders (F ++ "test_filtertag") "{% filter upper|replace('FOO', 'foo') %}foobar{% endfilter %}" "fooBAR",
  renders (F ++ "test_replace") "{{ string|replace(\"o\", 42) }}" "<f4242>" [("string", "<foo>")],
  renders (F ++ "test_replace[autoescape]") "{{ string|replace(\"o\", 42) }}" "&lt;f4242&gt;"
    [("string", "<foo>")] (env := ae),
  renders (F ++ "test_replace[autoescape-lt]") "{{ string|replace(\"<\", 42) }}" "42foo&gt;"
    [("string", "<foo>")] (env := ae),
  renders (F ++ "test_replace[markup]") "{{ string|replace(\"o\", \">x<\") }}" "f&gt;x&lt;&gt;x&lt;"
    [("string", .markup (LeanMarkupsafe.Markup.markSafe "foo"))] (env := ae),
  renders (F ++ "test_forceescape") "{{ x|forceescape }}" "&lt;div /&gt;"
    [("x", .markup (LeanMarkupsafe.Markup.markSafe "<div />"))],
  renders (F ++ "test_safe") "{{ \"<div>foo</div>\"|safe }}" "<div>foo</div>" (env := ae),
  renders (F ++ "test_safe[escaped]") "{{ \"<div>foo</div>\" }}" "&lt;div&gt;foo&lt;/div&gt;" (env := ae),
  renders (F ++ "test_urlencode[str]") "{{ value|urlencode }}" "Hello%2C%20world%21" [("value", "Hello, world!")] (env := ae),
  renders (F ++ "test_urlencode[unicode]") "{{ value|urlencode }}" "Hello%2C%20world%E2%80%BD" [("value", "Hello, world‽")] (env := ae),
  renders (F ++ "test_urlencode[dict]") "{{ value|urlencode }}" "f=1" [("value", obj [("f", 1)])] (env := ae),
  renders (F ++ "test_urlencode[pairs]") "{{ value|urlencode }}" "f=1&amp;z=2"
    [("value", .list [.tuple ["f", 1], .tuple ["z", 2]])] (env := ae),
  renders (F ++ "test_urlencode[intkey]") "{{ value|urlencode }}" "0=1" [("value", .dict [(.int 0, 1)])] (env := ae),
  renders (F ++ "test_urlencode[qs]") "{{ value|urlencode }}" "a+b%2Fc=a+b%2Fc"
    [("value", .list [.tuple ["a b/c", "a b/c"]])] (env := ae),
  renders (F ++ "test_urlencode[path]") "{{ value|urlencode }}" "a%20b/c" [("value", "a b/c")] (env := ae),
  renders (F ++ "test_simple_map") "{{ [\"1\", \"2\", \"3\"]|map(\"int\")|sum }}" "6",
  renders (F ++ "test_map_sum") "{{ [[1,2], [3], [4,5,6]]|map(\"sum\")|list }}" "[3, 3, 15]",
  renders (F ++ "test_attribute_map") "{{ users|map(attribute=\"name\")|join(\"|\") }}" "john|jane|mike"
    [("users", .list [obj [("name", "john")], obj [("name", "jane")], obj [("name", "mike")]])],
  renders (F ++ "test_empty_map") "{{ none|map(\"upper\")|list }}" "[]",
  renders (F ++ "test_map_default") "{{ users|map(attribute=\"lastname\", default=\"smith\")|join(\", \") }}"
    "lennon, edwards, None, smith"
    [("users", .list [obj [("firstname", "john"), ("lastname", "lennon")],
      obj [("firstname", "jane"), ("lastname", "edwards")], obj [("firstname", "jon"), ("lastname", .none)],
      obj [("firstname", "mike")]])],
  renders (F ++ "test_simple_select") "{{ [1, 2, 3, 4, 5]|select(\"odd\")|join(\"|\") }}" "1|3|5",
  renders (F ++ "test_bool_select") "{{ [none, false, 0, 1, 2, 3, 4, 5]|select|join(\"|\") }}" "1|2|3|4|5",
  renders (F ++ "test_simple_reject") "{{ [1, 2, 3, 4, 5]|reject(\"odd\")|join(\"|\") }}" "2|4",
  renders (F ++ "test_bool_reject") "{{ [none, false, 0, 1, 2, 3, 4, 5]|reject|join(\"|\") }}" "None|False|0",
  renders (F ++ "test_simple_select_attr") "{{ users|selectattr(\"is_active\")|map(attribute=\"name\")|join(\"|\") }}"
    "john|jane" [("users", .list [obj [("name", "john"), ("is_active", true)],
      obj [("name", "jane"), ("is_active", true)], obj [("name", "mike"), ("is_active", false)]])],
  renders (F ++ "test_simple_reject_attr") "{{ users|rejectattr(\"is_active\")|map(attribute=\"name\")|join(\"|\") }}"
    "mike" [("users", .list [obj [("name", "john"), ("is_active", true)],
      obj [("name", "jane"), ("is_active", true)], obj [("name", "mike"), ("is_active", false)]])],
  renders (F ++ "test_func_select_attr") "{{ users|selectattr(\"id\", \"odd\")|map(attribute=\"name\")|join(\"|\") }}"
    "john|mike" [("users", .list [obj [("id", 1), ("name", "john")], obj [("id", 2), ("name", "jane")],
      obj [("id", 3), ("name", "mike")]])],
  renders (F ++ "test_func_reject_attr") "{{ users|rejectattr(\"id\", \"odd\")|map(attribute=\"name\")|join(\"|\") }}"
    "jane" [("users", .list [obj [("id", 1), ("name", "john")], obj [("id", 2), ("name", "jane")],
      obj [("id", 3), ("name", "mike")]])],
  renders (F ++ "test_json_dump[dict]") "{{ x|tojson }}" "{\"foo\": \"bar\"}" [("x", obj [("foo", "bar")])] (env := ae),
  renders (F ++ "test_json_dump[quotes]") "{{ x|tojson }}" "\"\\\"ba\\u0026r\\u0027\"" [("x", "\"ba&r'")] (env := ae),
  renders (F ++ "test_json_dump[lt]") "{{ x|tojson }}" "\"\\u003cbar\\u003e\"" [("x", "<bar>")] (env := ae),
  renders (F ++ "test_wordwrap") "{{ s|wordwrap(20) }}" "Hello!\nThis is Jinja saying\nsomething."
    [("s", "Hello!\nThis is Jinja saying something.")],
  fails (F ++ "test_filter_undefined") "{{ var|f }}" (msgHas "No filter named 'f'"),
  renders (F ++ "test_filter_undefined_in_if") "{%- if x is defined -%}{{ x|f }}{%- else -%}x{% endif %}" "x",
  fails (F ++ "test_filter_undefined_in_if[runtime]") "{%- if x is defined -%}{{ x|f }}{%- else -%}x{% endif %}"
    (fun e => isRuntime e && msgHas "No filter named 'f'" e) [("x", 42)],
  renders (F ++ "test_filter_undefined_in_elif")
    "{%- if x is defined -%}{{ x }}{%- elif y is defined -%}{{ y|f }}{%- else -%}foo{%- endif -%}" "foo",
  renders (F ++ "test_filter_undefined_in_nested_if")
    "{%- if x is not defined -%}foo{%- else -%}{%- if y is defined -%}{{ y|f }}{%- endif -%}{{ x }}{%- endif -%}"
    "42" [("x", 42)],
  renders (F ++ "test_filter_undefined_in_condexpr") "{{ x|f if x is defined else 'foo' }}" "foo",
  fails (F ++ "test_filter_undefined_in_condexpr[runtime]") "{{ 'foo' if x is not defined else x|f }}"
    isRuntime [("x", 42)]
]

def testCases : List Case :=
  let ty := fun (op : String) (expect : Bool) => renders (T ++ s!"test_types[{op}]") ("{{ " ++ op ++ " }}")
    (if expect then "True" else "False") [("mydict", obj [])]
  [ renders (T ++ "test_defined") "{{ missing is defined }}|{{ true is defined }}" "False|True",
    renders (T ++ "test_even") "{{ 1 is even }}|{{ 2 is even }}" "False|True",
    renders (T ++ "test_odd") "{{ 1 is odd }}|{{ 2 is odd }}" "True|False",
    renders (T ++ "test_lower") "{{ \"foo\" is lower }}|{{ \"FOO\" is lower }}" "True|False",
    ty "none is none" true, ty "false is none" false, ty "true is none" false, ty "42 is none" false,
    ty "none is true" false, ty "false is true" false, ty "true is true" true, ty "0 is true" false,
    ty "1 is true" false, ty "none is false" false, ty "false is false" true, ty "0 is false" false,
    ty "none is boolean" false, ty "false is boolean" true, ty "true is boolean" true,
    ty "0 is boolean" false, ty "1.0 is boolean" false, ty "none is integer" false,
    ty "false is integer" false, ty "42 is integer" true, ty "3.14159 is integer" false,
    ty "(10 ** 100) is integer" true, ty "4.2 is float" true, ty "42 is float" false,
    ty "(10 ** 100) is float" false, ty "none is number" false, ty "false is number" true,
    ty "42 is number" true, ty "3.14159 is number" true, ty "(10 ** 100) is number" true,
    ty "none is string" false, ty "42 is string" false, ty "\"foo\" is string" true,
    ty "none is sequence" false, ty "42 is sequence" false, ty "\"foo\" is sequence" true,
    ty "[] is sequence" true, ty "[1, 2, 3] is sequence" true, ty "{} is sequence" true,
    ty "none is mapping" false, ty "\"foo\" is mapping" false, ty "[] is mapping" false,
    ty "{} is mapping" true, ty "mydict is mapping" true, ty "none is iterable" false,
    ty "42 is iterable" false, ty "\"foo\" is iterable" true, ty "[] is iterable" true,
    ty "{} is iterable" true, ty "range(5) is iterable" true, ty "none is callable" false,
    ty "\"foo\" is callable" false, ty "range is callable" true,
    renders (T ++ "test_upper") "{{ \"FOO\" is upper }}|{{ \"foo\" is upper }}" "True|False",
    renders (T ++ "test_equalto")
      "{{ foo is eq 12 }}|{{ foo is eq 0 }}|{{ foo is eq (3 * 4) }}|{{ bar is eq \"baz\" }}|{{ bar is eq \"zab\" }}|{{ bar is eq (\"ba\" + \"z\") }}|{{ bar is eq bar }}|{{ bar is eq foo }}"
      "True|False|True|True|False|True|True|False" [("foo", 12), ("bar", "baz")],
    renders (T ++ "test_compare_aliases")
      "{{ 2 is eq 2 }}{{ 2 is eq 3 }}{{ 2 is ne 3 }}{{ 2 is ne 2 }}{{ 2 is lt 3 }}{{ 2 is lt 2 }}{{ 2 is le 2 }}{{ 2 is le 1 }}{{ 2 is gt 1 }}{{ 2 is gt 2 }}{{ 2 is ge 2 }}{{ 2 is ge 3 }}"
      "TrueFalseTrueFalseTrueFalseTrueFalseTrueFalseTrueFalse",
    renders (T ++ "test_sameas") "{{ foo is sameas false }}|{{ 0 is sameas false }}" "True|False" [("foo", false)],
    renders (T ++ "test_no_paren_for_arg1") "{{ foo is sameas none }}" "True" [("foo", .none)],
    renders (T ++ "test_escaped") "{{ x is escaped }}|{{ y is escaped }}" "False|True"
      [("x", "foo"), ("y", .markup (LeanMarkupsafe.Markup.markSafe "foo"))] (env := ae),
    renders (T ++ "test_greaterthan") "{{ 1 is greaterthan 0 }}|{{ 0 is greaterthan 1 }}" "True|False",
    renders (T ++ "test_lessthan") "{{ 0 is lessthan 1 }}|{{ 1 is lessthan 0 }}" "True|False",
    renders (T ++ "test_in")
      "{{ \"o\" is in \"foo\" }}|{{ \"foo\" is in \"foo\" }}|{{ \"b\" is in \"foo\" }}|{{ 1 is in ((1, 2)) }}|{{ 3 is in ((1, 2)) }}|{{ 1 is in [1, 2] }}|{{ 3 is in [1, 2] }}|{{ \"foo\" is in {\"foo\": 1}}}|{{ \"baz\" is in {\"bar\": 1}}}"
      "True|True|False|True|False|True|False|True|False",
    fails "tests/test_tests.py::test_name_undefined" "{{ x is f }}" (msgHas "No test named 'f'"),
    renders "tests/test_tests.py::test_name_undefined_in_if" "{% if x is defined %}{{ x is f }}{% endif %}" "",
    fails "tests/test_tests.py::test_name_undefined_in_if[runtime]" "{% if x is defined %}{{ x is f }}{% endif %}"
      isRuntime [("x", 1)],
    renders "tests/test_tests.py::test_is_filter" "{{ 'title' is filter }}|{{ 'bad-name' is filter }}" "True|False",
    renders "tests/test_tests.py::test_is_test" "{{ 'number' is test }}|{{ 'bad-name' is test }}" "True|False" ]

def recSeq : Value := .list [
  obj [("a", 1), ("b", .list [obj [("a", 1)], obj [("a", 2)]])],
  obj [("a", 2), ("b", .list [obj [("a", 1)], obj [("a", 2)]])],
  obj [("a", 3), ("b", .list [obj [("a", "a")]])]]

def coreCases : List Case := [
  renders (FL ++ "test_simple") "{% for item in seq %}{{ item }}{% endfor %}" "0123456789" [("seq", range' 10)],
  renders (FL ++ "test_else") "{% for item in seq %}XXX{% else %}...{% endfor %}" "...",
  renders (FL ++ "test_else_scoping_item") "{% for item in [] %}{% else %}{{ item }}{% endfor %}" "42" [("item", 42)],
  renders (FL ++ "test_empty_blocks") "<{% for item in seq %}{% else %}{% endfor %}>" "<>",
  renders (FL ++ "test_context_vars")
    "{% for item in seq -%}{{ loop.index }}|{{ loop.index0 }}|{{ loop.revindex }}|{{ loop.revindex0 }}|{{ loop.first }}|{{ loop.last }}|{{ loop.length }}###{% endfor %}"
    "1|0|2|1|True|False|2###2|1|1|0|False|True|2###" [("seq", ints [42, 24])],
  renders (FL ++ "test_cycling") "{% for item in seq %}{{ loop.cycle('<1>', '<2>') }}{% endfor %}"
    "<1><2><1><2>" [("seq", range' 4)],
  renders (FL ++ "test_lookaround")
    "{% for item in seq -%}{{ loop.previtem|default('x') }}-{{ item }}-{{ loop.nextitem|default('x') }}|{%- endfor %}"
    "x-0-1|0-1-2|1-2-3|2-3-x|" [("seq", range' 4)],
  renders (FL ++ "test_changed") "{% for item in seq -%}{{ loop.changed(item) }},{%- endfor %}"
    "True,False,True,True,False,True,True,False,False," [("seq", .list [.none, .none, 1, 2, 2, 3, 4, 4, 4])],
  renders (FL ++ "test_scope") "{% for item in seq %}{% endfor %}{{ item }}" "" [("seq", range' 10)],
  renders (FL ++ "test_varlen") "{% for item in iter %}{{ item }}{% endfor %}" "01234" [("iter", range' 5)],
  fails (FL ++ "test_noniter") "{% for item in none %}...{% endfor %}" isType,
  renders (FL ++ "test_recursive")
    "{% for item in seq recursive -%}[{{ item.a }}{% if item.b %}<{{ loop(item.b) }}>{% endif %}]{%- endfor %}"
    "[1<[1][2]>][2<[1][2]>][3<[a]>]" [("seq", recSeq)],
  renders (FL ++ "test_recursive_lookaround")
    "{% for item in seq recursive -%}[{{ loop.previtem.a if loop.previtem is defined else 'x' }}.{{ item.a }}.{{ loop.nextitem.a if loop.nextitem is defined else 'x' }}{% if item.b %}<{{ loop(item.b) }}>{% endif %}]{%- endfor %}"
    "[x.1.2<[x.1.2][1.2.x]>][1.2.3<[x.1.2][1.2.x]>][2.3.x<[x.a.x]>]" [("seq", recSeq)],
  renders (FL ++ "test_recursive_depth0")
    "{% for item in seq recursive -%}[{{ loop.depth0 }}:{{ item.a }}{% if item.b %}<{{ loop(item.b) }}>{% endif %}]{%- endfor %}"
    "[0:1<[1:1][1:2]>][0:2<[1:1][1:2]>][0:3<[1:a]>]" [("seq", recSeq)],
  renders (FL ++ "test_recursive_depth")
    "{% for item in seq recursive -%}[{{ loop.depth }}:{{ item.a }}{% if item.b %}<{{ loop(item.b) }}>{% endif %}]{%- endfor %}"
    "[1:1<[2:1][2:2]>][1:2<[2:1][2:2]>][1:3<[2:a]>]" [("seq", recSeq)],
  renders (FL ++ "test_looploop")
    "{% for row in table %}{%- set rowloop = loop -%}{% for cell in row -%}[{{ rowloop.index }}|{{ loop.index }}]{%- endfor %}{%- endfor %}"
    "[1|1][1|2][2|1][2|2]" [("table", strs ["ab", "cd"])],
  renders (FL ++ "test_reversed_bug") "{% for i in items %}{{ i }}{% if not loop.last %},{% endif %}{% endfor %}"
    "1,2,3" [("items", ints [1, 2, 3])],
  fails (FL ++ "test_loop_errors") "{% for item in [1] if loop.index == 0 %}...{% endfor %}" isUndefined,
  renders (FL ++ "test_loop_errors[else]") "{% for item in [] %}...{% else %}{{ loop }}{% endfor %}" "",
  renders (FL ++ "test_loop_filter") "{% for item in range(10) if item is even %}[{{ item }}]{% endfor %}" "[0][2][4][6][8]",
  renders (FL ++ "test_loop_filter[index]") "{%- for item in range(10) if item is even %}[{{ loop.index }}:{{ item }}]{% endfor %}"
    "[1:0][2:2][3:4][4:6][5:8]",
  fails (FL ++ "test_loop_unassignable") "{% for loop in seq %}...{% endfor %}" isSyntax,
  renders (FL ++ "test_scoped_special_var")
    "{% for s in seq %}[{{ loop.first }}{% for c in s %}|{{ loop.first }}{% endfor %}]{% endfor %}"
    "[True|True|False][False|True|False]" [("seq", .tuple ["ab", "cd"])],
  renders (FL ++ "test_scoped_loop_var") "{% for x in seq %}{{ loop.first }}{% for y in seq %}{% endfor %}{% endfor %}"
    "TrueFalse" [("seq", "ab")],
  renders (FL ++ "test_scoped_loop_var[inner]") "{% for x in seq %}{% for y in seq %}{{ loop.first }}{% endfor %}{% endfor %}"
    "TrueFalseTrueFalse" [("seq", "ab")],
  renders (FL ++ "test_recursive_empty_loop_iter") "{%- for item in foo recursive -%}{%- endfor -%}" "" [("foo", .list [])],
  renders (FL ++ "test_call_in_loop")
    "{%- macro do_something() -%}[{{ caller() }}]{%- endmacro %}{%- for i in [1, 2, 3] %}{%- call do_something() -%}{{ i }}{%- endcall %}{%- endfor -%}"
    "[1][2][3]",
  renders (FL ++ "test_scoping_bug")
    "{%- for item in foo %}...{{ item }}...{% endfor %}{%- macro item(a) %}...{{ a }}...{% endmacro %}{{- item(2) -}}"
    "...1......2..." [("foo", .tuple [1])],
  renders (FL ++ "test_unpacking") "{% for a, b, c in [[1, 2, 3]] %}{{ a }}|{{ b }}|{{ c }}{% endfor %}" "1|2|3",
  renders (FL ++ "test_intended_scoping_with_set") "{% for item in seq %}{{ x }}{% set x = item %}{{ x }}{% endfor %}"
    "010203" [("x", 0), ("seq", ints [1, 2, 3])],
  renders (FL ++ "test_intended_scoping_with_set[top]")
    "{% set x = 9 %}{% for item in seq %}{{ x }}{% set x = item %}{{ x }}{% endfor %}"
    "919293" [("x", 0), ("seq", ints [1, 2, 3])],
  renders (IF ++ "test_simple") "{% if true %}...{% endif %}" "...",
  renders (IF ++ "test_elif") "{% if false %}XXX{% elif true %}...{% else %}XXX{% endif %}" "...",
  renders (IF ++ "test_elif_deep")
    ("{% if a == 0 %}0" ++ String.join ((List.range 999).map (fun i => s!"\n\{% elif a == {i + 1} %}{i + 1}")) ++
      "{% else %}x{% endif %}") "999" [("a", 999)],
  renders (IF ++ "test_else") "{% if false %}XXX{% else %}...{% endif %}" "...",
  renders (IF ++ "test_empty") "[{% if true %}{% else %}{% endif %}]" "[]",
  renders (IF ++ "test_complete") "{% if a %}A{% elif b %}B{% elif c == d %}C{% else %}D{% endif %}" "C"
    [("a", 0), ("b", false), ("c", 42), ("d", .float 42 0)],
  renders (IF ++ "test_no_scope") "{% if a %}{% set foo = 1 %}{% endif %}{{ foo }}" "1" [("a", true)],
  renders (MA ++ "test_simple") "{% macro say_hello(name) %}Hello {{ name }}!{% endmacro %}\n{{ say_hello('Peter') }}"
    "Hello Peter!" (env := trimEnv),
  renders (MA ++ "test_scoping")
    "{% macro level1(data1) %}\n{% macro level2(data2) %}{{ data1 }}|{{ data2 }}{% endmacro %}\n{{ level2('bar') }}{% endmacro %}\n{{ level1('foo') }}"
    "foo|bar" (env := trimEnv),
  renders (MA ++ "test_arguments")
    "{% macro m(a, b, c='c', d='d') %}{{ a }}|{{ b }}|{{ c }}|{{ d }}{% endmacro %}\n{{ m() }}|{{ m('a') }}|{{ m('a', 'b') }}|{{ m(1, 2, 3) }}"
    "||c|d|a||c|d|a|b|c|d|1|2|3|d" (env := trimEnv),
  fails (MA ++ "test_arguments_defaults_nonsense")
    "{% macro m(a, b=1, c) %}a={{ a }}, b={{ b }}, c={{ c }}{% endmacro %}" isSyntax (env := trimEnv),
  fails (MA ++ "test_caller_defaults_nonsense")
    "{% macro a() %}{{ caller() }}{% endmacro %}\n{% call(x, y=1, z) a() %}{% endcall %}" isSyntax (env := trimEnv),
  renders (MA ++ "test_varargs") "{% macro test() %}{{ varargs|join('|') }}{% endmacro %}{{ test(1, 2, 3) }}"
    "1|2|3" (env := trimEnv),
  renders (MA ++ "test_simple_call") "{% macro test() %}[[{{ caller() }}]]{% endmacro %}{% call test() %}data{% endcall %}"
    "[[data]]" (env := trimEnv),
  renders (MA ++ "test_complex_call")
    "{% macro test() %}[[{{ caller('data') }}]]{% endmacro %}{% call(data) test() %}{{ data }}{% endcall %}"
    "[[data]]" (env := trimEnv),
  renders (MA ++ "test_caller_undefined")
    "{% set caller = 42 %}{% macro test() %}{{ caller is not defined }}{% endmacro %}{{ test() }}" "True" (env := trimEnv),
  renders (MA ++ "test_callself")
    "{% macro foo(x) %}{{ x }}{% if x > 1 %}|{{ foo(x - 1) }}{% endif %}{% endmacro %}{{ foo(5) }}" "5|4|3|2|1"
    (env := trimEnv),
  renders (MA ++ "test_macro_defaults_self_ref")
    "{%- set x = 42 %}{%- macro m(a, b=x, x=23) %}{{ a }}|{{ b }}|{{ x }}{% endmacro -%}{{ m(1) }},{{ m(1, 2) }},{{ m(1, 2, 3) }},{{ m(1, x=7) }}"
    "1||23,1|2|23,1|2|3,1|7|7",
  renders (SE ++ "test_normal") "{% set foo = 1 %}{{ foo }}" "1" (env := trimEnv),
  renders (SE ++ "test_block") "{% set foo %}42{% endset %}{{ foo }}" "42" (env := trimEnv),
  renders (SE ++ "test_block_escaping") "{% set foo %}<em>{{ test }}</em>{% endset %}foo: {{ foo }}"
    "foo: <em>&lt;unsafe&gt;</em>" [("test", "<unsafe>")] (env := ae),
  fails (SE ++ "test_set_invalid") "{% set foo['bar'] = 1 %}" isSyntax (env := trimEnv),
  fails (SE ++ "test_set_invalid[runtime]") "{% set foo.bar = 1 %}" (msgHas "non-namespace object")
    [("foo", obj [])] (env := trimEnv),
  fails (SE ++ "test_namespace_redefined") "{% set ns = namespace() %}{% set ns.bar = 'hi' %}"
    (msgHas "non-namespace object") [("namespace", .native "dict")] (env := trimEnv),
  renders (SE ++ "test_namespace") "{% set ns = namespace() %}{% set ns.bar = '42' %}{{ ns.bar }}" "42" (env := trimEnv),
  renders (SE ++ "test_namespace_block") "{% set ns = namespace() %}{% set ns.bar %}42{% endset %}{{ ns.bar }}" "42"
    (env := trimEnv),
  renders (SE ++ "test_init_namespace") "{% set ns = namespace(d, self=37) %}{% set ns.b = 42 %}{{ ns.a }}|{{ ns.self }}|{{ ns.b }}"
    "13|37|42" [("d", obj [("a", 13)])] (env := trimEnv),
  renders (SE ++ "test_namespace_loop")
    "{% set ns = namespace(found=false) %}{% for x in range(4) %}{% if x == v %}{% set ns.found = true %}{% endif %}{% endfor %}{{ ns.found }}"
    "True" [("v", 3)] (env := trimEnv),
  renders (SE ++ "test_namespace_loop[4]")
    "{% set ns = namespace(found=false) %}{% for x in range(4) %}{% if x == v %}{% set ns.found = true %}{% endif %}{% endfor %}{{ ns.found }}"
    "False" [("v", 4)] (env := trimEnv),
  renders (SE ++ "test_namespace_macro")
    "{% set ns = namespace() %}{% set ns.a = 13 %}{% macro magic(x) %}{% set x.b = 37 %}{% endmacro %}{{ magic(ns) }}{{ ns.a }}|{{ ns.b }}"
    "13|37" (env := trimEnv),
  renders (SE ++ "test_namespace_set_tuple")
    "{% set ns = namespace(a=12, b=36) %}{% set ns.a, ns.b = ns.a + 1, ns.b + 1 %}{{ ns.a }}|{{ ns.b }}" "13|37"
    (env := trimEnv),
  renders (SE ++ "test_block_escaping_filtered") "{% set foo | trim %}<em>{{ test }}</em>    {% endset %}foo: {{ foo }}"
    "foo: <em>&lt;unsafe&gt;</em>" [("test", "<unsafe>")] (env := ae),
  renders (SE ++ "test_block_filtered") "{% set foo | trim | length | string %} 42    {% endset %}{{ foo }}" "2"
    (env := trimEnv),
  renders (WI ++ "test_with") "{% with a=42, b=23 -%}{{ a }} = {{ b }}|{% endwith -%}{{ a }} = {{ b }}"
    "42 = 23|1 = 2" [("a", 1), ("b", 2)],
  renders (WI ++ "test_with_argument_scoping") "{%- with a=1, b=2, c=b, d=e, e=5 -%}{{ a }}|{{ b }}|{{ c }}|{{ d }}|{{ e }}{%- endwith -%}"
    "1|2|3|4|5" [("b", 3), ("e", 4)]
]

def lexCases : List Case := [
  renders (LX ++ "test_raw1") "{% raw %}foo{% endraw %}|{%raw%}{{ bar }}|{% baz %}{%       endraw    %}"
    "foo|{{ bar }}|{% baz %}",
  renders (LX ++ "test_raw2") "1  {%- raw -%}   2   {%- endraw -%}   3" "123",
  renders (LX ++ "test_raw3") "bar\n{% raw %}\n  {{baz}}2 spaces\n{% endraw %}\nfoo" "bar\n\n  {{baz}}2 spaces\nfoo"
    [("baz", "test")] (env := lstripTrim),
  renders (LX ++ "test_raw4") "bar\n{%- raw -%}\n\n  \n  2 spaces\n space{%- endraw -%}\nfoo" "bar2 spaces\n spacefoo"
    (env := lstrip),
  renders (LX ++ "test_balancing") "{% for item in seq\n%}${{'foo': item}|upper}{% endfor %}"
    "{'FOO': 0}{'FOO': 1}{'FOO': 2}" [("seq", range' 3)] (env := { variableStart := "${", variableEnd := "}" }),
  renders (LX ++ "test_comments") "<ul>\n<!--- for item in seq -->\n  <li>{item}</li>\n<!--- endfor -->\n</ul>"
    "<ul>\n  <li>0</li>\n  <li>1</li>\n  <li>2</li>\n</ul>" [("seq", range' 3)]
    (env := { blockStart := "<!--", blockEnd := "-->", variableStart := "{", variableEnd := "}" }),
  renders (LX ++ "test_string_escapes") "{{ '\\x00' }}|{{ '♨' }}|{{ '\\xe4' }}|{{ '\\t' }}|{{ '\\r' }}|{{ '\\n' }}"
    "\x00|♨|\xe4|\t|\r|\n",
  renders (LX ++ "test_bytefallback") "{{ 'foo'|pprint }}|{{ 'bär'|pprint }}" "'foo'|'bär'",
  renders (LX ++ "test_normalizing[\\r]") "1\n2\r\n3\n4\n" "1\r2\r3\r4" (env := { newlineSequence := "\r" }),
  renders (LX ++ "test_normalizing[\\r\\n]") "1\n2\r\n3\n4\n" "1\r\n2\r\n3\r\n4" (env := { newlineSequence := "\r\n" }),
  renders (LX ++ "test_trailing_newline[keep]") "with\nseveral\n\n\n" "with\nseveral\n\n\n" (env := { keepTrailingNewline := true }),
  renders (LX ++ "test_trailing_newline[strip]") "with\nseveral\n\n\n" "with\nseveral\n\n",
  renders (LX ++ "test_trailing_newline[one]") "with\nnewline\n" "with\nnewline",
  renders (LX ++ "test_name[föö]") "{{ föö }}" "",
  renders (LX ++ "test_name[き]") "{{ き }}" "",
  renders (LX ++ "test_name[_]") "{{ _ }}" "",
  fails (LX ++ "test_name[1a]") "{{ 1a }}" isSyntax,
  fails (LX ++ "test_name[a-]") "{{ a- }}" isSyntax,
  fails (LX ++ "test_name[emoji-start]") ("{{ " ++ String.singleton (Char.ofNat 0x1f40d) ++ "a }}") isSyntax,
  fails (LX ++ "test_name[middle-dot-start]") "{{ \xb7 }}" isSyntax,
  renders (LX ++ "test_name[middle-dot-continue]") "{{ a\xb7 }}" "",
  renders (PA ++ "test_php_syntax") "<!-- I'm a comment, I'm not interesting --><? for item in seq -?>\n    <?= item ?>\n<?- endfor ?>"
    "01234" [("seq", range' 5)] (env := { blockStart := "<?", blockEnd := "?>", variableStart := "<?=", variableEnd := "?>", commentStart := "<!--", commentEnd := "-->" }),
  renders (PA ++ "test_erb_syntax") "<%# I'm a comment, I'm not interesting %><% for item in seq -%>\n    <%= item %>\n<%- endfor %>"
    "01234" [("seq", range' 5)] (env := { blockStart := "<%", blockEnd := "%>", variableStart := "<%=", variableEnd := "%>", commentStart := "<%#", commentEnd := "%>" }),
  renders (PA ++ "test_comment_syntax") "<!--# I'm a comment, I'm not interesting --><!-- for item in seq --->\n    ${item}\n<!--- endfor -->"
    "01234" [("seq", range' 5)] (env := { blockStart := "<!--", blockEnd := "-->", variableStart := "${", variableEnd := "}", commentStart := "<!--#", commentEnd := "-->" }),
  renders (PA ++ "test_balancing") "{{{'foo':'bar'}.foo}}" "bar",
  renders (PA ++ "test_start_comment") "{# foo comment\nand bar comment #}\n{% macro blub() %}foo{% endmacro %}\n{{ blub() }}"
    "\n\nfoo",
  fails (PA ++ "test_error_messages[endif]") "{% for item in seq %}...{% endif %}"
    (msgHas "Encountered unknown tag 'endif'. Jinja was looking for the following tags: 'endfor' or 'else'. The innermost block that needs to be closed is 'for'."),
  fails (PA ++ "test_error_messages[endfor]") "{% if foo %}{% for item in seq %}...{% endfor %}{% endfor %}"
    (msgHas "Encountered unknown tag 'endfor'. Jinja was looking for the following tags: 'elif' or 'else' or 'endif'. The innermost block that needs to be closed is 'if'."),
  fails (PA ++ "test_error_messages[eof-if]") "{% if foo %}"
    (msgHas "Unexpected end of template. Jinja was looking for the following tags: 'elif' or 'else' or 'endif'. The innermost block that needs to be closed is 'if'."),
  fails (PA ++ "test_error_messages[eof-for]") "{% for item in seq %}"
    (msgHas "Unexpected end of template. Jinja was looking for the following tags: 'endfor' or 'else'. The innermost block that needs to be closed is 'for'."),
  fails (PA ++ "test_error_messages[hyphen]") "{% block foo-bar-baz %}"
    (msgHas "Block names in Jinja have to be valid Python identifiers and may not contain hyphens, use an underscore instead."),
  fails (PA ++ "test_error_messages[unknown]") "{% unknown_tag %}" (msgHas "Encountered unknown tag 'unknown_tag'."),
  renders (SY ++ "test_slicing") "{{ [1, 2, 3][:] }}|{{ [1, 2, 3][::-1] }}" "[1, 2, 3]|[3, 2, 1]",
  renders (SY ++ "test_attr") "{{ foo.bar }}|{{ foo['bar'] }}" "42|42" [("foo", obj [("bar", 42)])],
  renders (SY ++ "test_subscript") "{{ foo[0] }}|{{ foo[-1] }}" "0|2" [("foo", ints [0, 1, 2])],
  renders (SY ++ "test_tuple") "{{ () }}|{{ (1,) }}|{{ (1, 2) }}" "()|(1,)|(1, 2)",
  renders (SY ++ "test_math") "{{ (1 + 1 * 2) - 3 / 2 }}|{{ 2**3 }}" "1.5|8",
  renders (SY ++ "test_div") "{{ 3 // 2 }}|{{ 3 / 2 }}|{{ 3 % 2 }}" "1|1.5|1",
  renders (SY ++ "test_unary") "{{ +3 }}|{{ -3 }}" "3|-3",
  renders (SY ++ "test_concat") "{{ [1, 2] ~ 'foo' }}" "[1, 2]foo",
  renders (SY ++ "test_compare") "{{ 1 > 0 }}{{ 1 >= 1 }}{{ 2 < 3 }}{{ 3 <= 4 }}{{ 4 == 4 }}{{ 4 != 5 }}"
    "TrueTrueTrueTrueTrueTrue",
  renders (SY ++ "test_compare_parens") "{{ i * (j < 5) }}" "2" [("i", 2), ("j", 3)],
  renders (SY ++ "test_compare_compound")
    "{{ 4 < 2 < 3 }}|{{ a < b < c }}|{{ 4 > 2 > 3 }}|{{ a > b > c }}|{{ 4 > 2 < 3 }}|{{ a > b < c }}"
    "False|False|False|False|True|True" [("a", 4), ("b", 2), ("c", 3)],
  renders (SY ++ "test_inop") "{{ 1 in [1, 2, 3] }}|{{ 1 not in [1, 2, 3] }}" "True|False",
  renders (SY ++ "test_collection_literal") "{{ [] }}|{{ {} }}|{{ () }}" "[]|{}|()",
  renders (SY ++ "test_numeric_literal")
    "{{ 1 }}|{{ 123 }}|{{ 12_34_56 }}|{{ 1.2 }}|{{ 34.56 }}|{{ 3_4.5_6 }}|{{ 1e0 }}|{{ 10e1 }}|{{ 2.5e100 }}|{{ 2.5e+100 }}|{{ 25.6e-10 }}|{{ 1_2.3_4e5_6 }}|{{ 0 }}|{{ 0_00 }}|{{ 0b1001_1111 }}|{{ 0o123 }}|{{ 0o1_23 }}|{{ 0x123abc }}|{{ 0x12_3abc }}"
    "1|123|123456|1.2|34.56|34.56|1.0|100.0|2.5e+100|2.5e+100|2.56e-09|1.234e+57|0|0|159|83|83|1194684|1194684",
  renders (SY ++ "test_bool") "{{ true and false }}|{{ false or true }}|{{ not false }}" "False|True|True",
  renders (SY ++ "test_grouping") "{{ (true and false) or (false and true) and not false }}" "False",
  renders (SY ++ "test_django_attr") "{{ [1, 2, 3].0 }}|{{ [[1]].0.0 }}" "1|1",
  renders (SY ++ "test_conditional_expression") "{{ 0 if true else 1 }}" "0",
  renders (SY ++ "test_short_conditional_expression") "<{{ 1 if false }}>" "<>",
  fails (SY ++ "test_short_conditional_expression[attr]") "<{{ (1 if false).bar }}>" isUndefined,
  renders (SY ++ "test_filter_priority") "{{ \"foo\"|upper + \"bar\"|upper }}" "FOOBAR",
  renders (SY ++ "test_tuple_expr") "{{ (1, 2,) }}|{{ 1, }}|{{ 1, 2 }}" "(1, 2)|(1,)|(1, 2)",
  renders (SY ++ "test_trailing_comma") "{{ (1, 2,) }}|{{ [1, 2,] }}|{{ {1: 2,} }}" "(1, 2)|[1, 2]|{1: 2}",
  renders (SY ++ "test_block_end_name") "{% block foo %}...{% endblock foo %}" "...",
  fails (SY ++ "test_block_end_name[mismatch]") "{% block x %}{% endblock y %}" isSyntax,
  renders (SY ++ "test_constant_casing") "{{ True }}|{{ true }}|{{ TRUE }}|{{ None }}|{{ none }}|{{ NONE }}"
    "True|True||None|None|",
  fails (SY ++ "test_test_chaining") "{{ foo is string is sequence }}" isSyntax,
  renders (SY ++ "test_test_chaining[or]") "{{ 42 is string or 42 is number }}" "True",
  renders (SY ++ "test_string_concatenation") "{{ \"foo\" \"bar\" \"baz\" }}" "foobarbaz",
  renders (SY ++ "test_notin") "{{ not 42 in bar }}" "False" [("bar", range' 100)],
  renders (SY ++ "test_operator_precedence") "{{ 2 * 3 + 4 % 2 + 1 - 2 }}" "5",
  renders (SY ++ "test_raw2") "{% raw %}{{ FOO }} and {% BAR %}{% endraw %}" "{{ FOO }} and {% BAR %}",
  renders (SY ++ "test_const") "{{ true }}|{{ false }}|{{ none }}|{{ none is defined }}|{{ missing is defined }}"
    "True|False|None|True|False",
  fails (SY ++ "test_const_assign[set]") "{% set true = 42 %}" isSyntax,
  fails (SY ++ "test_const_assign[for]") "{% for none in seq %}{% endfor %}" isSyntax,
  renders (SY ++ "test_localset") "{% set foo = 0 %}{% for item in [1, 2] %}{% set foo = 1 %}{% endfor %}{{ foo }}" "0",
  renders (SY ++ "test_parse_unary") "{{ -foo[\"bar\"] }}|{{ -foo[\"bar\"]|abs }}" "-42|42" [("foo", obj [("bar", 42)])],
  renders (LS ++ "test_lstrip") "    {% if True %}\n    {% endif %}" "\n" (env := lstrip),
  renders (LS ++ "test_lstrip_trim") "    {% if True %}\n    {% endif %}" "" (env := lstripTrim),
  renders (LS ++ "test_no_lstrip") "    {%+ if True %}\n    {%+ endif %}" "    \n    " (env := lstrip),
  renders (LS ++ "test_lstrip_blocks_false_with_no_lstrip") "    {%+ if True %}\n    {%+ endif %}" "    \n    ",
  renders (LS ++ "test_lstrip_endline") "    hello{% if True %}\n    goodbye{% endif %}" "    hello\n    goodbye" (env := lstrip),
  renders (LS ++ "test_lstrip_inline") "    {% if True %}hello    {% endif %}" "hello    " (env := lstrip),
  renders (LS ++ "test_lstrip_nested") "    {% if True %}a {% if True %}b {% endif %}c {% endif %}" "a b c " (env := lstrip),
  renders (LS ++ "test_lstrip_left_chars") "    abc {% if True %}\n        hello{% endif %}" "    abc \n        hello"
    (env := lstrip),
  renders (LS ++ "test_lstrip_embeded_strings") "    {% set x = \" {% str %} \" %}{{ x }}" " {% str %} " (env := lstrip),
  renders (LS ++ "test_lstrip_preserve_leading_newlines") "\n\n\n{% set hello = 1 %}" "\n\n\n" (env := lstrip),
  renders (LS ++ "test_lstrip_comment") "    {# if True #}\nhello\n    {#endif#}" "\nhello\n" (env := lstrip),
  renders (LS ++ "test_lstrip_blocks_outside_with_new_line")
    "  {% if kvs %}(\n   {% for k, v in kvs %}{{ k }}={{ v }} {% endfor %}\n  ){% endif %}" "(\na=1 b=2 \n  )"
    [("kvs", .list [.tuple ["a", 1], .tuple ["b", 2]])] (env := lstrip),
  renders (LS ++ "test_lstrip_trim_blocks_outside_with_new_line")
    "  {% if kvs %}(\n   {% for k, v in kvs %}{{ k }}={{ v }} {% endfor %}\n  ){% endif %}" "(\na=1 b=2   )"
    [("kvs", .list [.tuple ["a", 1], .tuple ["b", 2]])] (env := lstripTrim),
  renders (LS ++ "test_lstrip_blocks_inside_with_new_line")
    "  ({% if kvs %}\n   {% for k, v in kvs %}{{ k }}={{ v }} {% endfor %}\n  {% endif %})" "  (\na=1 b=2 \n)"
    [("kvs", .list [.tuple ["a", 1], .tuple ["b", 2]])] (env := lstrip),
  renders (LS ++ "test_lstrip_trim_blocks_inside_with_new_line")
    "  ({% if kvs %}\n   {% for k, v in kvs %}{{ k }}={{ v }} {% endfor %}\n  {% endif %})" "  (a=1 b=2 )"
    [("kvs", .list [.tuple ["a", 1], .tuple ["b", 2]])] (env := lstripTrim),
  renders (LS ++ "test_lstrip_blocks_without_new_line")
    "  {% if kvs %}   {% for k, v in kvs %}{{ k }}={{ v }} {% endfor %}  {% endif %}" "   a=1 b=2   "
    [("kvs", .list [.tuple ["a", 1], .tuple ["b", 2]])] (env := lstrip),
  renders (LS ++ "test_lstrip_blocks_consume_after_without_new_line")
    "  {% if kvs -%}   {% for k, v in kvs %}{{ k }}={{ v }} {% endfor -%}  {% endif -%}" "a=1 b=2 "
    [("kvs", .list [.tuple ["a", 1], .tuple ["b", 2]])] (env := lstrip),
  renders (LS ++ "test_lstrip_trim_blocks_consume_before_without_new_line")
    "  {%- if kvs %}   {%- for k, v in kvs %}{{ k }}={{ v }} {% endfor -%}  {%- endif %}" "a=1 b=2 "
    [("kvs", .list [.tuple ["a", 1], .tuple ["b", 2]])],
  renders (LS ++ "test_lstrip_trim_blocks_comment") " {# 1 space #}\n  {# 2 spaces #}    {# 4 spaces #}" "    "
    (env := lstripTrim),
  renders (LS ++ "test_lstrip_trim_blocks_raw") "{{x}}\n{%- raw %} {% endraw -%}\n{{ y }}" "1 2"
    [("x", 1), ("y", 2)] (env := lstripTrim),
  renders (LS ++ "test_php_syntax_with_manual")
    "    <!-- I'm a comment, I'm not interesting -->\n    <? for item in seq -?>\n        <?= item ?>\n    <?- endfor ?>"
    "01234" [("seq", range' 5)] (env := { blockStart := "<?", blockEnd := "?>", variableStart := "<?=", variableEnd := "?>", commentStart := "<!--", commentEnd := "-->", lstripBlocks := true, trimBlocks := true }),
  renders (LS ++ "test_php_syntax")
    "    <!-- I'm a comment, I'm not interesting -->\n    <? for item in seq ?>\n        <?= item ?>\n    <? endfor ?>"
    "        0\n        1\n        2\n        3\n        4\n" [("seq", range' 5)]
    (env := { blockStart := "<?", blockEnd := "?>", variableStart := "<?=", variableEnd := "?>", commentStart := "<!--", commentEnd := "-->", lstripBlocks := true, trimBlocks := true }),
  renders (LS ++ "test_erb_syntax")
    "<%# I'm a comment, I'm not interesting %>\n    <% for item in seq %>\n    <%= item %>\n    <% endfor %>\n"
    "    0\n    1\n    2\n    3\n    4\n" [("seq", range' 5)]
    (env := { blockStart := "<%", blockEnd := "%>", variableStart := "<%=", variableEnd := "%>", commentStart := "<%#", commentEnd := "%>", lstripBlocks := true, trimBlocks := true }),
  renders (LS ++ "test_erb_syntax_no_lstrip")
    "<%# I'm a comment, I'm not interesting %>\n    <%+ for item in seq -%>\n        <%= item %>\n    <%- endfor %>"
    "    01234" [("seq", range' 5)]
    (env := { blockStart := "<%", blockEnd := "%>", variableStart := "<%=", variableEnd := "%>", commentStart := "<%#", commentEnd := "%>", lstripBlocks := true, trimBlocks := true }),
  renders (TB ++ "test_trim") "    {% if True %}\n    {% endif %}" "        " (env := trimEnv),
  renders (TB ++ "test_no_trim") "    {% if True +%}\n    {% endif %}" "    \n    " (env := trimEnv),
  renders (TB ++ "test_no_trim_outer") "{% if True %}X{% endif +%}\nmore things" "X\nmore things" (env := trimEnv),
  renders (TB ++ "test_lstrip_no_trim") "    {% if True +%}\n    {% endif %}" "\n" (env := lstripTrim),
  renders (TB ++ "test_trim_blocks_false_with_no_trim")
    "    {% if True +%}\n    {% endif %}|    {# comment +#}\n    |    {% raw %}{% endraw +%}\n    "
    "    \n    |    \n    |    \n    ",
  renders (TB ++ "test_trim_nested") "    {% if True %}\na {% if True %}\nb {% endif %}\nc {% endif %}" "a b c "
    (env := lstripTrim),
  renders (TB ++ "test_no_trim_nested") "    {% if True +%}\na {% if True +%}\nb {% endif +%}\nc {% endif %}"
    "\na \nb \nc " (env := lstripTrim),
  renders (TB ++ "test_comment_trim") "    {# comment #}\n\n  " "\n  " (env := lstripTrim),
  renders (TB ++ "test_comment_no_trim") "    {# comment +#}\n\n  " "\n\n  " (env := lstripTrim),
  renders (TB ++ "test_multiple_comment_trim_lstrip") "   {# comment #}\n\n{# comment2 #}\n   \n{# comment3 #}\n\n "
    "\n   \n\n " (env := lstripTrim),
  renders (TB ++ "test_multiple_comment_no_trim_lstrip") "   {# comment +#}\n\n{# comment2 +#}\n   \n{# comment3 +#}\n\n "
    "\n\n\n   \n\n\n " (env := lstripTrim),
  renders (TB ++ "test_raw_trim_lstrip") "{{x}}{% raw %}\n\n    {% endraw %}\n\n{{ y }}" "1\n\n\n2"
    [("x", 1), ("y", 2)] (env := lstripTrim),
  renders (TB ++ "test_raw_no_trim_lstrip") "{{x}}{% raw %}\n\n      {% endraw +%}\n\n{{ y }}" "1\n\n\n\n2"
    [("x", 1), ("y", 2)] (env := lstrip),
  fails (TB ++ "test_raw_no_trim_lstrip[start]") "{{x}}{% raw +%}\n\n  {% endraw +%}\n\n{{ y }}" isSyntax (env := lstrip),
  renders (TB ++ "test_no_trim_angle_bracket") "    <% if True +%>\n\n    <% endif %>" "\n\n"
    (env := { blockStart := "<%", blockEnd := "%>", variableStart := "${", variableEnd := "}", commentStart := "<%#", commentEnd := "%>", lstripBlocks := true, trimBlocks := true }),
  renders (TB ++ "test_no_trim_php_syntax") "    <? if True +?>\n\n    <? endif ?>" "    \n\n    "
    (env := { blockStart := "<?", blockEnd := "?>", variableStart := "<?=", variableEnd := "?>", commentStart := "<!--", commentEnd := "-->", trimBlocks := true })
]

def layout := "|{% block block1 %}block 1 from layout{% endblock %}\n|{% block block2 %}block 2 from layout{% endblock %}\n|{% block block3 %}\n{% block block4 %}nested block 4 from layout{% endblock %}\n{% endblock %}|"
def inhEnv : Environment := {
  trimBlocks := true,
  loader := DictLoader [
    ("layout", layout),
    ("level1", "{% extends \"layout\" %}\n{% block block1 %}block 1 from level1{% endblock %}"),
    ("level2", "{% extends \"level1\" %}\n{% block block2 %}{% block block5 %}nested block 5 from level2{%\nendblock %}{% endblock %}"),
    ("level3", "{% extends \"level2\" %}\n{% block block5 %}block 5 from level3{% endblock %}\n{% block block4 %}block 4 from level3{% endblock %}\n"),
    ("level4", "{% extends \"level3\" %}\n{% block block3 %}block 3 from level4{% endblock %}\n"),
    ("working", "{% extends \"layout\" %}\n{% block block1 %}\n  {% if false %}\n    {% block block2 %}\n      this should work\n    {% endblock %}\n  {% endif %}\n{% endblock %}\n"),
    ("doublee", "{% extends \"layout\" %}\n{% extends \"layout\" %}\n{% block block1 %}\n  {% if false %}\n    {% block block2 %}\n      this should work\n    {% endblock %}\n  {% endif %}\n{% endblock %}\n")] }

def superEnv : Environment := { loader := DictLoader [
  ("a", "{% block intro %}INTRO{% endblock %}|BEFORE|{% block data %}INNER{% endblock %}|AFTER"),
  ("b", "{% extends \"a\" %}{% block data %}({{ super() }}){% endblock %}"),
  ("c", "{% extends \"b\" %}{% block intro %}--{{ super() }}--{% endblock %}\n{% block data %}[{{ super() }}]{% endblock %}")] }

def dynEnv : Environment := { loader := DictLoader [
  ("default1", "DEFAULT1{% block x %}{% endblock %}"),
  ("default2", "DEFAULT2{% block x %}{% endblock %}"),
  ("child", "{% extends default %}{% block x %}CHILD{% endblock %}"),
  ("multi", "{% if default %}{% extends default %}{% else %}{% extends 'default1' %}{% endif %}{% block x %}CHILD{% endblock %}")] }

def scopedEnv : Environment := { loader := DictLoader [
  ("default.html", "{% for item in seq %}[{% block item scoped %}{% endblock %}]{% endfor %}"),
  ("super.html", "{% for item in seq %}[{% block item scoped %}{{ item }}{% endblock %}]{% endfor %}"),
  ("child.html", "{% extends 'default.html' %}{% block item %}{{ item }}{% endblock %}"),
  ("childsuper.html", "{% extends \"super.html\" %}{% block item %}{{ super() }}|{{ item * 2 }}{% endblock %}")] }

def reqEnv : Environment := { loader := DictLoader [
  ("default", "{% block x required %}{# comment #}\n {% endblock %}"),
  ("strict", "{% block x required %}{% endblock %}"),
  ("level1", "{% extends 'default' %}{% block x %}[1]{% endblock %}"),
  ("l1", "{% extends 'strict' %}"),
  ("l2", "{% extends 'l1' %}{% block x %}[2]{% endblock %}"),
  ("l3", "{% extends 'l2' %}"),
  ("text", "{% block x required %}data {# c #}{% endblock %}"),
  ("top", "{% extends t %}{% block x %}CHILD{% endblock %}"),
  ("default2", "{% for item in seq %}[{% block item required scoped %}{% endblock %}]{% endfor %}"),
  ("child2", "{% extends 'default2' %}{% block item %}{{ item }}{% endblock %}"),
  ("default1", "{% for item in seq %}[{% block item scoped required %}{% endblock %}]{% endfor %}"),
  ("child1", "{% extends 'default1' %}{% block item %}{{ item }}{% endblock %}")] }

def inheritanceCases : List Case := [
  rendersT (IN ++ "test_layout") inhEnv "layout" "|block 1 from layout|block 2 from layout|nested block 4 from layout|",
  rendersT (IN ++ "test_level1") inhEnv "level1" "|block 1 from level1|block 2 from layout|nested block 4 from layout|",
  rendersT (IN ++ "test_level2") inhEnv "level2" "|block 1 from level1|nested block 5 from level2|nested block 4 from layout|",
  rendersT (IN ++ "test_level3") inhEnv "level3" "|block 1 from level1|block 5 from level3|block 4 from level3|",
  rendersT (IN ++ "test_level4") inhEnv "level4" "|block 1 from level1|block 5 from level3|block 3 from level4|",
  rendersT (IN ++ "test_super") superEnv "c" "--INTRO--|BEFORE|[(INNER)]|AFTER",
  { upstream := IN ++ "test_working", name := "test_working",
    run := pure (match inhEnv.getTemplate "working" with | .ok _ => true | .error _ => false) },
  renders (IN ++ "test_reuse_blocks") "{{ self.foo() }}|{% block foo %}42{% endblock %}|{{ self.foo() }}" "42|42|42",
  rendersT (IN ++ "test_preserve_blocks") { loader := DictLoader [
      ("a", "{% if false %}{% block x %}A{% endblock %}{% endif %}{{ self.x() }}"),
      ("b", "{% extends \"a\" %}{% block x %}B{{ super() }}{% endblock %}")] } "b" "BA",
  rendersT (IN ++ "test_dynamic_inheritance[1]") dynEnv "child" "DEFAULT1CHILD" [("default", "default1")],
  rendersT (IN ++ "test_dynamic_inheritance[2]") dynEnv "child" "DEFAULT2CHILD" [("default", "default2")],
  rendersT (IN ++ "test_multi_inheritance[2]") dynEnv "multi" "DEFAULT2CHILD" [("default", "default2")],
  rendersT (IN ++ "test_multi_inheritance[none]") dynEnv "multi" "DEFAULT1CHILD",
  rendersT (IN ++ "test_scoped_block") scopedEnv "child.html" "[0][1][2][3][4]" [("seq", range' 5)],
  rendersT (IN ++ "test_super_in_scoped_block") scopedEnv "childsuper.html" "[0|0][1|2][2|4][3|6][4|8]" [("seq", range' 5)],
  rendersT (IN ++ "test_level1_required") reqEnv "level1" "[1]",
  failsT (IN ++ "test_level3_required[l1]") reqEnv "l1" (msgHas "Required block 'x' not found"),
  rendersT (IN ++ "test_level3_required[l2]") reqEnv "l2" "[2]",
  rendersT (IN ++ "test_level3_required[l3]") reqEnv "l3" "[2]",
  failsT (IN ++ "test_invalid_required[text]") reqEnv "top"
    (msgHas "Required blocks can only contain comments or whitespace") [("t", "text")],
  rendersT (IN ++ "test_invalid_required[empty]") reqEnv "top" "CHILD" [("t", "strict")],
  rendersT (IN ++ "test_required_with_scope") reqEnv "child1" "[0][1][2]" [("seq", range' 3)],
  failsT (IN ++ "test_required_with_scope[order]") reqEnv "child2" isSyntax [("seq", range' 3)],
  failsT "tests/test_inheritance.py::TestBugFix::test_double_extends" inhEnv "doublee" (msgHas "extended multiple times")
]

def undefinedCases : List Case :=
  let dflt : Environment := {}
  let chain : Environment := { undefined := .chainable }
  let debug : Environment := { undefined := .debug }
  let strict : Environment := { undefined := .strict }
  [ renders (UN ++ "test_default_undefined[print]") "{{ missing }}" "" (env := dflt),
    fails (UN ++ "test_default_undefined[attr]") "{{ missing.attribute }}" isUndefined (env := dflt),
    renders (UN ++ "test_default_undefined[list]") "{{ missing|list }}" "[]" (env := dflt),
    renders (UN ++ "test_default_undefined[defined]") "{{ missing is not defined }}" "True" (env := dflt),
    renders (UN ++ "test_default_undefined[int-attr]") "{{ foo.missing }}" "" [("foo", 42)] (env := dflt),
    renders (UN ++ "test_default_undefined[not]") "{{ not missing }}" "True" (env := dflt),
    fails (UN ++ "test_default_undefined[sub]") "{{ missing - 1}}" isUndefined (env := dflt),
    renders (UN ++ "test_default_undefined[in]") "{{ 'foo' in missing }}" "False" (env := dflt),
    renders (UN ++ "test_chainable_undefined[print]") "{{ missing }}" "" (env := chain),
    renders (UN ++ "test_chainable_undefined[list]") "{{ missing|list }}" "[]" (env := chain),
    renders (UN ++ "test_chainable_undefined[int-attr]") "{{ foo.missing }}" "" [("foo", 42)] (env := chain),
    fails (UN ++ "test_chainable_undefined[sub]") "{{ missing - 1}}" isUndefined (env := chain),
    renders (UN ++ "test_chainable_undefined[chain]") "{{ missing.bar[\"baz\"] }}" "" (env := chain),
    renders (UN ++ "test_debug_undefined[print]") "{{ missing }}" "{{ missing }}" (env := debug),
    fails (UN ++ "test_debug_undefined[attr]") "{{ missing.attribute }}" isUndefined (env := debug),
    renders (UN ++ "test_debug_undefined[list]") "{{ missing|list }}" "[]" (env := debug),
    renders (UN ++ "test_debug_undefined[int-attr]") "{{ foo.missing }}" "{{ no such element: int object['missing'] }}"
      [("foo", 42)] (env := debug),
    renders (UN ++ "test_debug_undefined[not]") "{{ not missing }}" "True" (env := debug),
    fails (UN ++ "test_strict_undefined[print]") "{{ missing }}" isUndefined (env := strict),
    fails (UN ++ "test_strict_undefined[attr]") "{{ missing.attribute }}" isUndefined (env := strict),
    fails (UN ++ "test_strict_undefined[list]") "{{ missing|list }}" isUndefined (env := strict),
    fails (UN ++ "test_strict_undefined[in]") "{{ 'foo' in missing }}" isUndefined (env := strict),
    renders (UN ++ "test_strict_undefined[defined]") "{{ missing is not defined }}" "True" (env := strict),
    fails (UN ++ "test_strict_undefined[int-attr]") "{{ foo.missing }}" isUndefined [("foo", 42)] (env := strict),
    fails (UN ++ "test_strict_undefined[not]") "{{ not missing }}" isUndefined (env := strict),
    renders (UN ++ "test_strict_undefined[default]") "{{ missing|default(\"default\", true) }}" "default" (env := strict),
    renders (UN ++ "test_strict_undefined[condexpr]") "{{ \"foo\" if false }}" "" (env := strict),
    fails (UN ++ "test_indexing_gives_undefined") "{{ var[42].foo }}" isUndefined [("var", 0)],
    renders "tests/test_api.py::TestExtendedAPI::test_item_and_attribute[items]" "{{ foo.items()|list }}"
      "[('items', 42)]" [("foo", obj [("items", 42)])],
    renders "tests/test_api.py::TestExtendedAPI::test_item_and_attribute[attr]" "{{ foo|attr(\"items\")()|list }}"
      "[('items', 42)]" [("foo", obj [("items", 42)])],
    renders "tests/test_api.py::TestExtendedAPI::test_item_and_attribute[item]" "{{ foo[\"items\"] }}" "42"
      [("foo", obj [("items", 42)])],
    rendersT "tests/test_api.py::TestExtendedAPI::test_autoescape_autoselect[txt]"
      { autoescape := selectAutoescape ["html"] [] false, loader := DictLoader [("test.txt", "{{ foo }}"), ("test.html", "{{ foo }}")] }
      "test.txt" "<foo>" [("foo", "<foo>")],
    rendersT "tests/test_api.py::TestExtendedAPI::test_autoescape_autoselect[html]"
      { autoescape := selectAutoescape ["html"] [] false, loader := DictLoader [("test.txt", "{{ foo }}"), ("test.html", "{{ foo }}")] }
      "test.html" "&lt;foo&gt;" [("foo", "<foo>")],
    renders "tests/test_api.py::TestExtendedAPI::test_autoescape_autoselect[string]" "{{ foo }}" "<foo>" [("foo", "<foo>")]
      (env := { autoescape := selectAutoescape ["html"] [] false }),
    fails "tests/test_api.py::TestExtendedAPI::test_sandbox_max_range"
      "{% for item in range(total) %}{{ item }}{% endfor %}" isOverflow [("total", 100001)],
    renders "tests/test_api.py::TestExtendedAPI::test_sandbox_max_range[at-limit]"
      "{{ range(total)|length }}" "100000" [("total", 100000)],
    -- Deviation UP-047: an unknown escape keeps its backslash before any character
    -- (upstream turns '\é' into the text \xe9 but keeps '\q').
    renders "tests/test_lexnparse.py::TestLexer::test_string_escapes[UP-047 deviation]"
      "{{ '\\q' }}|{{ '\\é' }}" "\\q|\\é",
    -- UP-048, as upstream: `title` returns a plain string, so markup is escaped again.
    renders "tests/test_filters.py::TestFilter::test_title[UP-048 markup]"
      "{{ x|title }}|{{ x|capitalize }}" "&lt;B&gt;hi&lt;/b&gt;|<b>hi</b>"
      [("x", .markup (LeanMarkupsafe.Markup.markSafe "<b>hi</b>"))] (env := { autoescape := .const true }) ]

/-! ## `FileSystemLoader` (tests/test_loader.py::TestFileSystemLoader), over a fixture written here -/

def fsRoot : System.FilePath := ".lake" / "conformance-fs" / "templates"

def writeFixture : IO Unit := do
  IO.FS.createDirAll (fsRoot / "foo")
  IO.FS.writeFile (fsRoot / "test.html") "BAR\n"
  IO.FS.writeFile (fsRoot / "foo" / "test.html") "FOO\n"

/-- The upstream `_test_common`: `test.html`, `foo/test.html`, a missing name. -/
def fsCommon (upstream : String) (mk : IO Loader) : Case :=
  { upstream, name := upstream.splitOn "::" |>.getLast!, run := do
      writeFixture
      let env : Environment := { loader := ← mk }
      let r1 := env.getTemplate "test.html" >>= (·.render)
      let r2 := env.getTemplate "foo/test.html" >>= (·.render)
      let r3 := env.getTemplate "missing.html"
      let ok3 := match r3 with | .error (.notFound _) => true | _ => false
      match r1, r2 with
      | .ok a, .ok b => pure (a.trimAscii.toString == "BAR" && b.trimAscii.toString == "FOO" && ok3)
      | _, _ => pure false }

def loaderCases : List Case := [
  fsCommon "tests/test_loader.py::TestFileSystemLoader::test_searchpath_as_str" (FileSystemLoader fsRoot.toString),
  fsCommon "tests/test_loader.py::TestFileSystemLoader::test_searchpath_as_pathlib" (FileSystemLoader fsRoot),
  fsCommon "tests/test_loader.py::TestFileSystemLoader::test_searchpath_as_list_including_pathlib"
    (FileSystemLoader ["/tmp/lean-jinja2-no-such-dir/templates", fsRoot.toString]) ]

def cases : List Case := filterCases ++ testCases ++ coreCases ++ lexCases ++ inheritanceCases ++ undefinedCases ++
  loaderCases

def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length} cases, {failures} failing"
  return if failures == 0 then 0 else 1
