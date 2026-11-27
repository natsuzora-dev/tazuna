import glance
import gleam/list
import gleam/option.{None, Some}
import gleam/string
import simplifile
import tazuna/internal/convert.{Source}
import tazuna/internal/ir
import tazuna/internal/kind.{type Restricted}
import tazuna/internal/names
import tazuna/internal/print

fn corpus() -> List(convert.Source) {
  ["shapes", "main"]
  |> list.map(fn(name) {
    let path = "test/corpus/" <> name <> ".gleam"
    let assert Ok(text) = simplifile.read(path)
    Source("corpus/" <> name, path, text)
  })
}

/// Converts the corpus, which also prints every module back and compares, and
/// leaves the IR where scripts/check hands it to the engine.
pub fn corpus_converts_and_prints_back_test() {
  let assert Ok(program) = convert.convert(corpus(), "corpus/main")
  let assert Ok(_) =
    simplifile.write("build/corpus.ir.json", convert.ir_text(program))
}

/// Swapping the labels of two Int fields gives a well-typed program Lean would
/// accept; printing it back is what tells it from the source.
pub fn round_trip_catches_a_same_type_label_swap_test() {
  let assert Ok(program) = convert.convert(corpus(), "corpus/main")
  let assert [_, main] = corpus()
  let assert Ok(ast) = glance.module(main.text)
  let swapped =
    list.map(program.functions, fn(f) {
      case f.name, f.body.node {
        "corpus/main.generics", ir.Block([ir.Let(at, p, a, value), ..rest]) -> {
          let assert ir.Ctor(t, v, [ir.Labelled(l1, x), ir.Labelled(l2, y)]) =
            value.node
          let value =
            ir.Expr(
              ..value,
              node: ir.Ctor(t, v, [ir.Labelled(l2, x), ir.Labelled(l1, y)]),
            )
          ir.Function(
            ..f,
            body: ir.Expr(
              ..f.body,
              node: ir.Block([ir.Let(at, p, a, value), ..rest]),
            ),
          )
        }
        _, _ -> f
      }
    })
  let mine = fn(name) { names.split(name).0 == "corpus/main" }
  let check = fn(functions: List(ir.Function)) {
    print.round_trip(
      names.imports("corpus/main", ast.imports),
      ast,
      list.filter(program.types, fn(t) { mine(t.name) }),
      list.filter(program.aliases, fn(a) { mine(a.name) }),
      list.filter(program.constants, fn(c) { mine(c.name) }),
      list.filter(functions, fn(f) { mine(f.name) }),
    )
  }
  assert check(program.functions) == Ok(Nil)
  assert check(swapped) == Error("function generics prints back differently")
}

pub fn ir_json_escapes_control_characters_test() {
  let assert Ok(program) = convert.convert(corpus(), "corpus/main")
  let text = convert.ir_text(program)
  assert !string.contains(text, "\t")
  assert string.contains(text, "tab\\traw")
}

/// A source that triggers the kind, and the line the finding points at.
fn example(k: Restricted) -> #(String, Int) {
  case k {
    kind.Float -> #("pub fn f() -> Int {\n  let _ = 1.5\n  2\n}", 2)
    kind.HighCodePoint -> #(
      "pub fn f(s: String) -> Int {\n  case s {\n    \"a\\u{30000}\" -> 1\n    _ -> 0\n  }\n}",
      3,
    )
    kind.BitArray -> #("pub fn f() -> Int {\n  let _ = <<1>>\n  1\n}", 2)
    kind.Panic -> #("pub fn f() -> Int {\n  panic\n}", 2)
    kind.Todo -> #("pub fn f() -> Int {\n  todo\n}", 2)
    kind.Echo -> #("pub fn f() -> Int {\n  echo 1\n}", 2)
    kind.LetAssert -> #(
      "pub fn f(o: Result(Int, Nil)) -> Int {\n  let assert Ok(x) = o\n  x\n}",
      2,
    )
    kind.Assert -> #("pub fn f() -> Int {\n  assert 1 == 1\n  2\n}", 2)
    kind.ListSpread -> #(
      "pub fn f(xs: List(Int)) -> List(Int) {\n  [1, ..xs]\n}",
      2,
    )
    kind.ListPattern -> #(
      "pub fn f(xs: List(Int)) -> Int {\n  case xs {\n    [] -> 0\n    _ -> 1\n  }\n}",
      3,
    )
    kind.StringPrefixPattern -> #(
      "pub fn f(s: String) -> Int {\n  case s {\n    \"a\" <> _ -> 1\n    _ -> 0\n  }\n}",
      3,
    )
    kind.External -> #(
      "@external(javascript, \"./x.mjs\", \"f\")\npub fn f() -> Int",
      2,
    )
    kind.ForeignFunction -> #(
      "import gleam/int\n\npub fn f() -> String {\n  int.to_string(1)\n}",
      4,
    )
    kind.ForeignType -> #(
      "import gleam/dict\n\npub fn f(d: dict.Dict(Int, Int)) -> Int {\n  1\n}",
      3,
    )
    kind.Recursion -> #(
      "pub fn f(n: Int) -> Int {\n  g(n)\n}\n\npub fn g(n: Int) -> Int {\n  f(n)\n}",
      2,
    )
    kind.RecursiveType -> #(
      "pub type Tree {\n  Leaf\n  Node(Forest)\n}\n\npub type Forest {\n  Forest(trees: List(Tree))\n}",
      1,
    )
    kind.Incomparable -> #(
      "import tazuna/table\n\npub fn f(t: table.Table(fn() -> Int, Int)) -> Int {\n  table.size(table.remove(t, fn() { 1 }))\n}",
      4,
    )
    kind.KeptCapture -> #(
      "import tazuna\n\npub fn f() -> tazuna.Query(Int, Int, Int, Int) {\n  let twice = fn(n) { n * 2 }\n  tazuna.query(name: \"q\", callers: [], accepts: fn(_) { [] }, resolve: fn(cx) {\n    twice(cx.input)\n  })\n}",
      6,
    )
    kind.ShadowedImport -> #(
      "import gleam/int.{to_string}\n\npub fn to_string() -> Int {\n  1\n}",
      3,
    )
    kind.MixedReference -> #(
      "import gleam/option.{type Option, Some}\n\npub fn f() -> Option(Int) {\n  option.Some(1)\n}",
      4,
    )
    kind.MultiVariantUpdate -> #(
      "pub type S {\n  A(n: Int)\n  B(n: Int)\n}\n\npub fn f(s: S) -> S {\n  case s {\n    A(..) as a -> A(..a, n: 1)\n    _ -> s\n  }\n}",
      8,
    )
    kind.VariantField -> #(
      "pub type S {\n  A(n: Int, m: Int)\n  B(n: Int)\n}\n\npub fn f(s: S) -> Int {\n  case s {\n    A(..) as a -> a.m\n    _ -> 0\n  }\n}",
      8,
    )
    kind.ConstructorValue -> #(
      "pub type P {\n  P(a: Int, b: Int)\n}\n\npub fn f() -> P {\n  1 |> P(2)\n}",
      6,
    )
    kind.AnnotationNeeded -> #("pub fn f(x) -> Int {\n  1\n}", 1)
    kind.RootSpec -> #(
      "import tazuna\n\npub fn spec(s: tazuna.Spec) -> tazuna.Spec {\n  s\n}",
      3,
    )
  }
}

pub fn each_restricted_kind_is_found_where_it_is_written_test() {
  list.each(kind.restricted, fn(k) {
    let #(text, line) = example(k)
    let findings = case
      convert.convert([Source("m", "src/m.gleam", text)], "m")
    {
      Ok(program) -> convert.root_findings(program)
      Error(findings) -> findings
    }
    let found =
      list.map(findings, fn(f) {
        let assert convert.Finding(found, "src/m.gleam", option_at, _) = f
        #(kind.name(found), case option_at {
          Some(at) -> at.line
          None -> 0
        })
      })
    assert found == [#(kind.name(kind.Restricted(k)), line)]
  })
}

pub fn high_code_points_are_found_raw_or_escaped_test() {
  let kinds = fn(literal) {
    let text = "pub fn f() -> String {\n  " <> literal <> "\n}"
    case convert.convert([Source("m", "src/m.gleam", text)], "m") {
      Ok(_) -> []
      Error(findings) ->
        list.map(findings, fn(f) {
          let convert.Finding(found, ..) = f
          kind.name(found)
        })
    }
  }
  assert kinds("\"\u{30000}\"") == ["Restricted.highCodePoint"]
  assert kinds("\"a\\u{2FFFF}\\u{30000}\"") == ["Restricted.highCodePoint"]
  assert kinds("\"\u{2FFFF}\"") == []
  assert kinds("\"\\\\u{30000}\"") == []
}

pub fn a_constant_whose_value_leaves_its_type_open_needs_its_type_test() {
  let text = "pub const empty = []"
  let assert Error([f]) =
    convert.convert([Source("m", "src/m.gleam", text)], "m")
  assert kind.name(f.kind) == "Restricted.annotationNeeded"
  assert f.at == Some(ir.At(1, 1))
}

pub fn a_finding_is_one_json_line_test() {
  let text = "pub fn f() -> Int {\n  panic\n}"
  let assert Error([f]) =
    convert.convert([Source("m", "src/m.gleam", text)], "m")
  assert convert.finding_line(f)
    == "{\"kind\":\"Restricted.panic\",\"file\":\"src/m.gleam\",\"line\":2,\"col\":3,\"message\":\"panic: a spec names its failures as rejections\"}"
}

pub fn tazuna_functions_besides_built_ins_are_foreign_test() {
  let text = "import tazuna\n\npub fn f() -> Nil {\n  tazuna.main()\n}"
  let assert Error([f]) =
    convert.convert([Source("m", "src/m.gleam", text)], "m")
  assert kind.name(f.kind) == "Restricted.foreignFunction"
  assert f.at == Some(ir.At(4, 3))
}

/// A generic function that compares its arguments passes the demand to the
/// type it is called at, so the call holding functions is the one refused.
pub fn equality_demands_flow_through_generic_functions_test() {
  let text =
    "pub fn same(a: x, b: x) -> Bool {\n  a == b\n}\n\npub fn twice(a: y) -> Bool {\n  same(a, a)\n}\n\npub fn ints() -> Bool {\n  twice(1)\n}\n\npub fn fns() -> Bool {\n  twice(ints)\n}"
  let assert Error([f]) =
    convert.convert([Source("m", "src/m.gleam", text)], "m")
  assert kind.name(f.kind) == "Restricted.incomparable"
  assert f.at == Some(ir.At(14, 3))
}

fn kept_findings(body: String) -> List(#(Int, String)) {
  let text =
    "import tazuna\n\npub fn f(s: tazuna.Service, n: Int) -> tazuna.Query(Int, Int, Int, Int) {\n"
    <> body
    <> "\n}"
  let assert Error(findings) =
    convert.convert([Source("m", "src/m.gleam", text)], "m")
  list.map(findings, fn(f) {
    let assert Some(at) = f.at
    assert kind.name(f.kind) == "Restricted.keptCapture"
    #(at.line, f.message)
  })
}

/// A kept function may capture data; a structure value, a local function
/// passed by its label alone, or one captured inside a piped call or a `use`
/// callback, is refused where it is written, with the fix.
pub fn kept_captures_name_the_fix_test() {
  let ok =
    "import tazuna\n\npub fn f(n: Int) -> tazuna.Query(Int, Int, Int, Int) {\n  tazuna.query(name: \"q\", callers: [], accepts: fn(_) { [] }, resolve: fn(cx) {\n    cx.input + n\n  })\n}"
  let assert Ok(_) = convert.convert([Source("m", "src/m.gleam", ok)], "m")
  assert kept_findings(
      "  tazuna.query(name: \"q\", callers: [], accepts: fn(_) { [] }, resolve: fn(_) {\n    let _ = s\n    n\n  })",
    )
    == [
      #(
        5,
        "resolve of tazuna.query captures `s`, which holds a tazuna.Service, a structure value Lean cannot keep as data: capture only the data the function reads",
      ),
    ]
  assert kept_findings(
      "  let resolve = fn(_) { n }\n  tazuna.query(name: \"q\", callers: [], accepts: fn(_) { [] }, resolve:)",
    )
    == [
      #(
        5,
        "resolve of tazuna.query is kept with the local function `resolve`, which Lean cannot keep as data: define it at the top level and pass it by name",
      ),
    ]
  let assert [#(5, _)] =
    kept_findings(
      "  let g = fn(x) { x }\n  \"q\" |> tazuna.query([], fn(_) { [] }, fn(cx) { g(cx.input) })",
    )
  let assert [#(5, _), #(6, _)] =
    kept_findings(
      "  let g = fn(x) { x }\n  use cx <- tazuna.query(name: \"q\", callers: [], accepts: fn(i) { [#(\"ok\", g(i) > 0)] })\n  g(cx.input)",
    )
}
