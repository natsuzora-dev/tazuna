//// Prints the IR of one module back as Gleam, and compares what glance reads
//// from that text with what it read from the source. The converter runs the
//// comparison on every conversion: a mapping that moved, dropped or relabelled
//// anything prints different Gleam.

import glance as g
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string
import tazuna/internal/ir.{
  type Annotation, type Arg, type Expr, type Pat, type PatArg, type Stmt,
  type Ty,
}
import tazuna/internal/names.{type Imports}

/// `Error` names the first definition that differs.
pub fn round_trip(
  imports: Imports,
  source: g.Module,
  types: List(ir.TypeDef),
  aliases: List(ir.Alias),
  constants: List(ir.Constant),
  functions: List(ir.Function),
) -> Result(Nil, String) {
  let text = module(imports, types, aliases, constants, functions)
  use printed <- result.try(
    g.module(text)
    |> result.replace_error("the printed IR is not Gleam:\n" <> text),
  )
  use _ <- result.try(
    same(
      "type",
      source.custom_types,
      printed.custom_types,
      fn(d) { d.definition.name },
      fn(d) {
        let t = d.definition
        g.CustomType(
          ..t,
          publicity: g.Private,
          opaque_: False,
          variants: list.map(t.variants, fn(v) {
            g.Variant(..v, attributes: [])
          }),
        )
      },
    ),
  )
  use _ <- result.try(
    same(
      "type alias",
      source.type_aliases,
      printed.type_aliases,
      fn(d) { d.definition.name },
      fn(d) { g.TypeAlias(..d.definition, publicity: g.Private) },
    ),
  )
  use _ <- result.try(
    same(
      "constant",
      source.constants,
      printed.constants,
      fn(d) { d.definition.name },
      fn(d) { g.Constant(..d.definition, publicity: g.Private) },
    ),
  )
  same(
    "function",
    source.functions,
    printed.functions,
    fn(d) { d.definition.name },
    fn(d) { g.Function(..d.definition, publicity: g.Private) },
  )
}

fn same(
  what: String,
  source: List(a),
  printed: List(a),
  name: fn(a) -> String,
  normal: fn(a) -> b,
) -> Result(Nil, String) {
  let shown = fn(x) { without_spans(string.inspect(normal(x))) }
  case list.length(source) == list.length(printed) {
    False -> Error("the IR has a different number of " <> what <> "s")
    True ->
      list.zip(source, printed)
      |> list.try_each(fn(p) {
        case shown(p.0) == shown(p.1) {
          True -> Ok(Nil)
          False -> Error(what <> " " <> name(p.0) <> " prints back differently")
        }
      })
  }
}

/// Drops every `Span(..)`. `string.inspect` writes `Span(start: 1, end: 2)` on
/// JavaScript and `Span(1, 2)` on Erlang; both lose their offsets.
fn without_spans(s: String) -> String {
  case string.split(s, "Span(") {
    [first, ..rest] ->
      list.fold(rest, first, fn(acc, piece) {
        case string.split_once(piece, ")") {
          Ok(#(_, after)) -> acc <> "Span" <> after
          Error(_) -> acc <> "Span(" <> piece
        }
      })
    [] -> s
  }
}

pub fn module(
  imports: Imports,
  types: List(ir.TypeDef),
  aliases: List(ir.Alias),
  constants: List(ir.Constant),
  functions: List(ir.Function),
) -> String {
  let p = Printer(imports)
  list.flatten([
    list.map(types, type_def(p, _)),
    list.map(aliases, fn(a) {
      "type " <> applied(local(a.name), a.params) <> " = " <> ty(p, a.ty)
    }),
    list.map(constants, fn(c) {
      "const "
      <> local(c.name)
      <> case c.annotation {
        Some(t) -> ": " <> ty(p, t)
        None -> ""
      }
      <> " = "
      <> expr(p, c.value)
    }),
    list.map(functions, fn(f) {
      "fn "
      <> local(f.name)
      <> "("
      <> commas(
        list.map(f.params, fn(q) {
          case q.label {
            Some(l) -> l <> " "
            None -> ""
          }
          <> q.name
          <> ": "
          <> ty(p, q.ty)
        }),
      )
      <> ") -> "
      <> ty(p, f.ret)
      <> " "
      <> body(p, f.body)
    }),
  ])
  |> string.join("\n\n")
}

type Printer {
  Printer(imports: Imports)
}

fn local(global: String) -> String {
  names.split(global).1
}

fn commas(items: List(String)) -> String {
  string.join(items, ", ")
}

fn value(p: Printer, global: String) -> String {
  names.spell_value(p.imports, global) |> result.unwrap("?" <> global)
}

fn type_name(p: Printer, global: String) -> String {
  names.spell_type(p.imports, global) |> result.unwrap("?" <> global)
}

fn applied(head: String, args: List(String)) -> String {
  case args {
    [] -> head
    _ -> head <> "(" <> commas(args) <> ")"
  }
}

fn type_def(p: Printer, t: ir.TypeDef) -> String {
  "type "
  <> applied(local(t.name), t.params)
  <> " {\n"
  <> string.join(
    list.map(t.variants, fn(v) {
      applied(
        v.name,
        list.map(v.fields, fn(f) {
          case f.0 {
            Some(l) -> l <> ": "
            None -> ""
          }
          <> ty(p, f.1)
        }),
      )
    }),
    "\n",
  )
  <> "\n}"
}

fn ty(p: Printer, t: Ty) -> String {
  case t {
    ir.Con(n, args) -> applied(type_name(p, n), list.map(args, ty(p, _)))
    ir.Fun(ps, r) ->
      "fn(" <> commas(list.map(ps, ty(p, _))) <> ") -> " <> ty(p, r)
    ir.Tuple(items) -> "#(" <> commas(list.map(items, ty(p, _))) <> ")"
    ir.Var(n) -> n
    ir.Meta(id) -> "?meta" <> int.to_string(id)
  }
}

fn annotation(p: Printer, a: Annotation) -> String {
  case a {
    ir.ACon(n, args) ->
      applied(type_name(p, n), list.map(args, annotation(p, _)))
    ir.AFun(ps, r) ->
      "fn("
      <> commas(list.map(ps, annotation(p, _)))
      <> ") -> "
      <> annotation(p, r)
    ir.ATuple(items) -> "#(" <> commas(list.map(items, annotation(p, _))) <> ")"
    ir.AVar(n) -> n
    ir.AHole(text) -> text
  }
}

/// A function or lambda body: a block node is the statements between the
/// braces, anything else the one expression there.
fn body(p: Printer, e: Expr) -> String {
  case e.node {
    ir.Block(stmts) -> block(p, stmts)
    _ -> "{\n" <> expr(p, e) <> "\n}"
  }
}

fn block(p: Printer, stmts: List(Stmt)) -> String {
  "{\n" <> string.join(list.map(stmts, stmt(p, _)), "\n") <> "\n}"
}

fn stmt(p: Printer, s: Stmt) -> String {
  case s {
    ir.Let(_, pat, ann, v) ->
      "let " <> pattern(p, pat) <> annotated(p, ann) <> " = " <> expr(p, v)
    ir.Use(_, pats, call) ->
      "use "
      <> commas(list.map(pats, fn(q) { pattern(p, q.0) <> annotated(p, q.1) }))
      <> " <- "
      <> expr(p, call)
    ir.Do(v) -> expr(p, v)
  }
}

fn annotated(p: Printer, ann: Option(Annotation)) -> String {
  case ann {
    Some(a) -> ": " <> annotation(p, a)
    None -> ""
  }
}

fn expr(p: Printer, e: Expr) -> String {
  let sub = expr(p, _)
  case e.node {
    ir.IntLit(text) | ir.StrLit(text) -> text
    ir.Local(n) -> n
    ir.Ref(n, _) -> value(p, n)
    ir.Ctor(t, v, args) ->
      applied(value(p, names.constructor(t, v)), list.map(args, arg(p, _)))
    ir.Field(r, l) -> sub(r) <> "." <> l
    ir.Index(t, k) -> sub(t) <> "." <> int.to_string(k)
    ir.Update(t, v, r, fields) ->
      value(p, names.constructor(t, v))
      <> "(.."
      <> sub(r)
      <> string.concat(list.map(fields, fn(f) { ", " <> arg(p, f) }))
      <> ")"
    ir.Call(f, args) ->
      sub(f) <> "(" <> commas(list.map(args, arg(p, _))) <> ")"
    ir.Capture(label, f, before, after) -> {
      let hole = case label {
        Some(l) -> l <> ": _"
        None -> "_"
      }
      sub(f)
      <> "("
      <> commas(
        list.flatten([
          list.map(before, arg(p, _)),
          [hole],
          list.map(after, arg(p, _)),
        ]),
      )
      <> ")"
    }
    ir.Pipe(l, r) -> sub(l) <> " |> " <> sub(r)
    ir.Lam(params, ret, b) ->
      "fn("
      <> commas(
        list.map(params, fn(q) { q.name <> annotated(p, q.annotation) }),
      )
      <> ")"
      <> case ret {
        Some(a) -> " -> " <> annotation(p, a)
        None -> ""
      }
      <> " "
      <> body(p, b)
    ir.Block(stmts) -> block(p, stmts)
    ir.Case(subjects, clauses) ->
      "case "
      <> commas(list.map(subjects, sub))
      <> " {\n"
      <> string.join(
        list.map(clauses, fn(c) {
          string.join(
            list.map(c.alternatives, fn(alt) {
              commas(list.map(alt, pattern(p, _)))
            }),
            " | ",
          )
          <> case c.guard {
            Some(guard) -> " if " <> sub(guard)
            None -> ""
          }
          <> " -> "
          <> sub(c.body)
        }),
        "\n",
      )
      <> "\n}"
    ir.ListOf(items) -> "[" <> commas(list.map(items, sub)) <> "]"
    ir.TupleOf(items) -> "#(" <> commas(list.map(items, sub)) <> ")"
    ir.Bin(op, l, r) -> sub(l) <> " " <> op <> " " <> sub(r)
    // `- 1` is a negation; `-1` would be a literal.
    ir.Un(op, x) -> op <> " " <> sub(x)
  }
}

fn arg(p: Printer, a: Arg) -> String {
  case a {
    ir.Positional(v) -> expr(p, v)
    ir.Labelled(l, v) -> l <> ": " <> expr(p, v)
    ir.Shorthand(_, l) -> l <> ":"
  }
}

fn pattern(p: Printer, pat: Pat) -> String {
  case pat.node {
    ir.PDiscard(n) | ir.PVar(n) -> n
    ir.PInt(text) | ir.PStr(text) -> text
    ir.PTuple(items) -> "#(" <> commas(list.map(items, pattern(p, _))) <> ")"
    ir.PCtor(t, v, args, spread) -> {
      let parts =
        list.map(args, pattern_arg(p, _))
        |> list.append(case spread {
          True -> [".."]
          False -> []
        })
      applied(value(p, names.constructor(t, v)), parts)
    }
    ir.PAs(q, n) -> pattern(p, q) <> " as " <> n
  }
}

fn pattern_arg(p: Printer, a: PatArg) -> String {
  case a {
    ir.PPositional(q) -> pattern(p, q)
    ir.PLabelled(l, q) -> l <> ": " <> pattern(p, q)
    ir.PShorthand(_, l) -> l <> ":"
  }
}
