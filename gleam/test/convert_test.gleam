import glance
import gleam/list
import gleam/option.{None, Some}
import gleam/string
import simplifile
import tazuna/internal/convert.{type Restricted, Source}
import tazuna/internal/dsl_source
import tazuna/internal/ir
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
  let assert Ok(program) =
    convert.convert(corpus(), dsl_source.text, "corpus/main")
  let assert Ok(_) =
    simplifile.write("build/corpus.ir.json", convert.ir_text(program))
}

/// Swapping the labels of two Int fields gives a well-typed program Lean would
/// accept; printing it back is what tells it from the source.
pub fn round_trip_catches_a_same_type_label_swap_test() {
  let assert Ok(program) =
    convert.convert(corpus(), dsl_source.text, "corpus/main")
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
  let assert Ok(program) =
    convert.convert(corpus(), dsl_source.text, "corpus/main")
  let text = convert.ir_text(program)
  assert !string.contains(text, "\t")
  assert string.contains(text, "tab\\traw")
}

/// A source that triggers the kind, and the line the finding points at.
fn example(kind: Restricted) -> #(String, Int) {
  case kind {
    convert.Float -> #("pub fn f() -> Int {\n  let _ = 1.5\n  2\n}", 2)
    convert.BitArray -> #("pub fn f() -> Int {\n  let _ = <<1>>\n  1\n}", 2)
    convert.Panic -> #("pub fn f() -> Int {\n  panic\n}", 2)
    convert.Todo -> #("pub fn f() -> Int {\n  todo\n}", 2)
    convert.Echo -> #("pub fn f() -> Int {\n  echo 1\n}", 2)
    convert.LetAssert -> #(
      "pub fn f(o: Result(Int, Nil)) -> Int {\n  let assert Ok(x) = o\n  x\n}",
      2,
    )
    convert.Assert -> #("pub fn f() -> Int {\n  assert 1 == 1\n  2\n}", 2)
    convert.ListSpread -> #(
      "pub fn f(xs: List(Int)) -> List(Int) {\n  [1, ..xs]\n}",
      2,
    )
    convert.ListPattern -> #(
      "pub fn f(xs: List(Int)) -> Int {\n  case xs {\n    [] -> 0\n    _ -> 1\n  }\n}",
      3,
    )
    convert.StringPrefixPattern -> #(
      "pub fn f(s: String) -> Int {\n  case s {\n    \"a\" <> _ -> 1\n    _ -> 0\n  }\n}",
      3,
    )
    convert.FunctionCapture -> #(
      "pub fn g(a: Int, b: Int) -> Int {\n  a + b\n}\n\npub fn f() -> fn(Int) -> Int {\n  g(1, _)\n}",
      6,
    )
    convert.External -> #(
      "@external(javascript, \"./x.mjs\", \"f\")\npub fn f() -> Int",
      2,
    )
    convert.ForeignFunction -> #(
      "import gleam/int\n\npub fn f() -> String {\n  int.to_string(1)\n}",
      4,
    )
    convert.ForeignType -> #(
      "import gleam/dict\n\npub fn f(d: dict.Dict(Int, Int)) -> Int {\n  1\n}",
      3,
    )
    convert.Recursion -> #(
      "pub fn f(n: Int) -> Int {\n  g(n)\n}\n\npub fn g(n: Int) -> Int {\n  f(n)\n}",
      2,
    )
    convert.ShadowedImport -> #(
      "import gleam/int.{to_string}\n\npub fn to_string() -> Int {\n  1\n}",
      3,
    )
    convert.MixedReference -> #(
      "import gleam/option.{type Option, Some}\n\npub fn f() -> Option(Int) {\n  option.Some(1)\n}",
      4,
    )
    convert.MultiVariantUpdate -> #(
      "pub type S {\n  A(n: Int)\n  B(n: Int)\n}\n\npub fn f(s: S) -> S {\n  case s {\n    A(..) as a -> A(..a, n: 1)\n    _ -> s\n  }\n}",
      8,
    )
    convert.VariantField -> #(
      "pub type S {\n  A(n: Int, m: Int)\n  B(n: Int)\n}\n\npub fn f(s: S) -> Int {\n  case s {\n    A(..) as a -> a.m\n    _ -> 0\n  }\n}",
      8,
    )
    convert.ConstructorValue -> #(
      "pub type B {\n  B(n: Int)\n}\n\npub fn f() -> fn(Int) -> B {\n  B\n}",
      6,
    )
    convert.AnnotationNeeded -> #("pub fn f(x) -> Int {\n  1\n}", 1)
  }
}

pub fn each_restricted_kind_is_found_where_it_is_written_test() {
  list.each(convert.restricted, fn(kind) {
    let #(text, line) = example(kind)
    let found = case
      convert.convert([Source("m", "src/m.gleam", text)], dsl_source.text, "m")
    {
      Ok(_) -> []
      Error(findings) ->
        list.map(findings, fn(f) {
          let assert convert.Finding(k, "src/m.gleam", option_at, _) = f
          #(convert.kind_name(k), case option_at {
            Some(at) -> at.line
            None -> 0
          })
        })
    }
    assert found == [#(convert.kind_name(convert.Restricted(kind)), line)]
  })
}

pub fn a_finding_is_one_json_line_test() {
  let text = "pub fn f() -> Int {\n  panic\n}"
  let assert Error([f]) =
    convert.convert([Source("m", "src/m.gleam", text)], dsl_source.text, "m")
  assert convert.finding_line(f)
    == "{\"kind\":\"Restricted.panic\",\"file\":\"src/m.gleam\",\"line\":2,\"col\":3,\"message\":\"panic: a spec names its failures as rejections\"}"
}
