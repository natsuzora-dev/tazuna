//// The IR the converter hands to Lean: Gleam's syntax with names resolved and
//// every node typed. Its JSON contract is the doc comment of
//// lean/Tazuna/Ir/Surface.lean; `to_json` writes exactly that shape.

import gleam/dict.{type Dict}
import gleam/list
import gleam/option.{type Option, None, Some}
import tazuna/internal/json.{type Json, Array, Object, Str}

pub type At {
  At(line: Int, col: Int)
}

pub type Ty {
  Con(name: String, args: List(Ty))
  Fun(params: List(Ty), ret: Ty)
  Tuple(items: List(Ty))
  Var(name: String)
  /// An inference variable, solved by `Program.solved`. One nothing
  /// constrains is written as `Nil`: no value of it is ever inspected.
  Meta(id: Int)
}

/// A type as the source wrote it in an annotation, names resolved.
pub type Annotation {
  ACon(name: String, args: List(Annotation))
  AFun(params: List(Annotation), ret: Annotation)
  ATuple(items: List(Annotation))
  AVar(name: String)
  AHole(text: String)
}

pub type Expr {
  Expr(at: At, ty: Ty, node: Node)
}

pub type Node {
  IntLit(text: String)
  StrLit(text: String)
  Local(name: String)
  Ref(name: String, targs: List(#(String, Ty)))
  Ctor(type_: String, variant: String, args: List(Arg))
  Field(record: Expr, label: String)
  Index(tuple: Expr, index: Int)
  Update(type_: String, variant: String, record: Expr, fields: List(Arg))
  Call(function: Expr, args: List(Arg))
  Pipe(left: Expr, right: Expr)
  Lam(params: List(Param), ret: Option(Annotation), body: Expr)
  Block(stmts: List(Stmt))
  Case(subjects: List(Expr), clauses: List(Clause))
  ListOf(items: List(Expr))
  TupleOf(items: List(Expr))
  Bin(operator: String, left: Expr, right: Expr)
  Un(operator: String, arg: Expr)
}

pub type Arg {
  Positional(value: Expr)
  Labelled(label: String, value: Expr)
  Shorthand(at: At, label: String)
}

pub type Param {
  Param(name: String, ty: Ty, annotation: Option(Annotation))
}

pub type Stmt {
  Let(at: At, pattern: Pat, annotation: Option(Annotation), value: Expr)
  Use(at: At, patterns: List(Pat), call: Expr)
  Do(value: Expr)
}

pub type Clause {
  Clause(alternatives: List(List(Pat)), guard: Option(Expr), body: Expr)
}

pub type Pat {
  Pat(at: At, ty: Ty, node: PatNode)
}

pub type PatNode {
  PDiscard(name: String)
  PVar(name: String)
  PInt(text: String)
  PStr(text: String)
  PTuple(items: List(Pat))
  PCtor(type_: String, variant: String, args: List(PatArg), spread: Bool)
  PAs(pattern: Pat, name: String)
}

pub type PatArg {
  PPositional(pattern: Pat)
  PLabelled(label: String, pattern: Pat)
  PShorthand(at: At, label: String)
}

pub type TypeDef {
  TypeDef(name: String, params: List(String), variants: List(Variant), at: At)
}

pub type Variant {
  Variant(name: String, fields: List(#(Option(String), Ty)))
}

pub type Function {
  Function(name: String, params: List(FnParam), ret: Ty, body: Expr, at: At)
}

pub type FnParam {
  FnParam(label: Option(String), name: String, ty: Ty)
}

pub type Constant {
  Constant(name: String, ty: Ty, value: Expr, at: At)
}

pub type Program {
  Program(
    root: String,
    sources: List(#(String, String)),
    types: List(TypeDef),
    functions: List(Function),
    constants: List(Constant),
    solved: Dict(Int, Ty),
  )
}

/// The version of the JSON contract, `irVersion` in lean/Tazuna/Ir/Load.lean.
pub const version = 2

pub fn solve(solved: Dict(Int, Ty), t: Ty) -> Ty {
  case t {
    Meta(id) ->
      case dict.get(solved, id) {
        Ok(u) -> solve(solved, u)
        Error(_) -> t
      }
    Con(n, args) -> Con(n, list.map(args, solve(solved, _)))
    Fun(ps, r) -> Fun(list.map(ps, solve(solved, _)), solve(solved, r))
    Tuple(items) -> Tuple(list.map(items, solve(solved, _)))
    Var(_) -> t
  }
}

pub fn to_json(p: Program) -> Json {
  let ty = fn(t) { ty_json(solve(p.solved, t)) }
  Object([
    #("tazuna_ir", json.Int(version)),
    #("root", Str(p.root)),
    #(
      "sources",
      Array(
        list.map(p.sources, fn(s) {
          Object([#("module", Str(s.0)), #("path", Str(s.1))])
        }),
      ),
    ),
    #(
      "types",
      Array(
        list.map(p.types, fn(t) {
          Object([
            #("name", Str(t.name)),
            #("params", Array(list.map(t.params, Str))),
            #(
              "variants",
              Array(
                list.map(t.variants, fn(v) {
                  Object([
                    #("name", Str(v.name)),
                    #(
                      "fields",
                      Array(
                        list.map(v.fields, fn(f) {
                          Object(label(f.0, [#("ty", ty(f.1))]))
                        }),
                      ),
                    ),
                  ])
                }),
              ),
            ),
            #("at", at_json(t.at)),
          ])
        }),
      ),
    ),
    #(
      "functions",
      Array(
        list.map(p.functions, fn(f) {
          Object([
            #("name", Str(f.name)),
            #(
              "params",
              Array(
                list.map(f.params, fn(q) {
                  Object(
                    label(q.label, [#("name", Str(q.name)), #("ty", ty(q.ty))]),
                  )
                }),
              ),
            ),
            #("ret", ty(f.ret)),
            #("body", expr_json(f.body, ty)),
            #("at", at_json(f.at)),
          ])
        }),
      ),
    ),
    #(
      "constants",
      Array(
        list.map(p.constants, fn(c) {
          Object([
            #("name", Str(c.name)),
            #("ty", ty(c.ty)),
            #("value", expr_json(c.value, ty)),
            #("at", at_json(c.at)),
          ])
        }),
      ),
    ),
  ])
}

fn label(
  l: Option(String),
  rest: List(#(String, Json)),
) -> List(#(String, Json)) {
  case l {
    Some(l) -> [#("label", Str(l)), ..rest]
    None -> rest
  }
}

fn at_json(at: At) -> Json {
  Array([json.Int(at.line), json.Int(at.col)])
}

fn ty_json(t: Ty) -> Json {
  case t {
    Con(n, args) ->
      Object([#("con", Str(n)), #("args", Array(list.map(args, ty_json)))])
    Fun(ps, r) ->
      Object([#("fn", Array(list.map(ps, ty_json))), #("ret", ty_json(r))])
    Tuple(items) -> Object([#("tuple", Array(list.map(items, ty_json)))])
    Var(n) -> Object([#("var", Str(n))])
    Meta(_) -> ty_json(Con("Nil", []))
  }
}

fn annotation_json(a: Annotation) -> Json {
  case a {
    ACon(n, args) ->
      Object([
        #("con", Str(n)),
        #("args", Array(list.map(args, annotation_json))),
      ])
    AFun(ps, r) ->
      Object([
        #("fn", Array(list.map(ps, annotation_json))),
        #("ret", annotation_json(r)),
      ])
    ATuple(items) ->
      Object([#("tuple", Array(list.map(items, annotation_json)))])
    AVar(n) -> Object([#("var", Str(n))])
    AHole(text) -> Object([#("hole", Str(text))])
  }
}

fn optional(
  key: String,
  value: Option(a),
  f: fn(a) -> Json,
) -> List(#(String, Json)) {
  case value {
    Some(v) -> [#(key, f(v))]
    None -> []
  }
}

fn expr_json(e: Expr, ty: fn(Ty) -> Json) -> Json {
  let sub = fn(x) { expr_json(x, ty) }
  let subs = fn(xs) { Array(list.map(xs, sub)) }
  let args = fn(xs) { Array(list.map(xs, arg_json(_, ty))) }
  let fields = case e.node {
    IntLit(text) -> [#("op", Str("int")), #("text", Str(text))]
    StrLit(text) -> [#("op", Str("str")), #("text", Str(text))]
    Local(name) -> [#("op", Str("var")), #("name", Str(name))]
    Ref(name, targs) -> [
      #("op", Str("ref")),
      #("name", Str(name)),
      #("targs", Object(list.map(targs, fn(t) { #(t.0, ty(t.1)) }))),
    ]
    Ctor(type_, variant, xs) -> [
      #("op", Str("ctor")),
      #("type", Str(type_)),
      #("variant", Str(variant)),
      #("args", args(xs)),
    ]
    Field(record, l) -> [
      #("op", Str("field")),
      #("record", sub(record)),
      #("label", Str(l)),
    ]
    Index(tuple, k) -> [
      #("op", Str("index")),
      #("tuple", sub(tuple)),
      #("index", json.Int(k)),
    ]
    Update(type_, variant, record, xs) -> [
      #("op", Str("update")),
      #("type", Str(type_)),
      #("variant", Str(variant)),
      #("record", sub(record)),
      #("fields", args(xs)),
    ]
    Call(f, xs) -> [#("op", Str("call")), #("fn", sub(f)), #("args", args(xs))]
    Pipe(l, r) -> [#("op", Str("pipe")), #("left", sub(l)), #("right", sub(r))]
    Lam(params, ret, body) -> [
      #("op", Str("lam")),
      #(
        "params",
        Array(
          list.map(params, fn(p) {
            Object([
              #("name", Str(p.name)),
              #("ty", ty(p.ty)),
              ..optional("annotation", p.annotation, annotation_json)
            ])
          }),
        ),
      ),
      #("body", sub(body)),
      ..optional("return_annotation", ret, annotation_json)
    ]
    Block(stmts) -> [
      #("op", Str("block")),
      #("stmts", Array(list.map(stmts, stmt_json(_, ty)))),
    ]
    Case(subjects, clauses) -> [
      #("op", Str("case")),
      #("subjects", subs(subjects)),
      #(
        "clauses",
        Array(
          list.map(clauses, fn(c) {
            Object([
              #(
                "alternatives",
                Array(
                  list.map(c.alternatives, fn(alt) {
                    Array(list.map(alt, pat_json(_, ty)))
                  }),
                ),
              ),
              #("body", sub(c.body)),
              ..optional("guard", c.guard, sub)
            ])
          }),
        ),
      ),
    ]
    ListOf(items) -> [#("op", Str("list")), #("items", subs(items))]
    TupleOf(items) -> [#("op", Str("tuple")), #("items", subs(items))]
    Bin(op, l, r) -> [
      #("op", Str("bin")),
      #("operator", Str(op)),
      #("left", sub(l)),
      #("right", sub(r)),
    ]
    Un(op, x) -> [#("op", Str("un")), #("operator", Str(op)), #("arg", sub(x))]
  }
  Object([#("ty", ty(e.ty)), #("at", at_json(e.at)), ..fields])
}

fn arg_json(a: Arg, ty: fn(Ty) -> Json) -> Json {
  case a {
    Positional(v) -> Object([#("value", expr_json(v, ty))])
    Labelled(l, v) -> Object([#("label", Str(l)), #("value", expr_json(v, ty))])
    Shorthand(at, l) -> Object([#("label", Str(l)), #("at", at_json(at))])
  }
}

fn stmt_json(s: Stmt, ty: fn(Ty) -> Json) -> Json {
  case s {
    Let(at, p, ann, v) ->
      Object([
        #("stmt", Str("let")),
        #("at", at_json(at)),
        #("pattern", pat_json(p, ty)),
        #("value", expr_json(v, ty)),
        ..optional("annotation", ann, annotation_json)
      ])
    Use(at, ps, call) ->
      Object([
        #("stmt", Str("use")),
        #("at", at_json(at)),
        #("patterns", Array(list.map(ps, pat_json(_, ty)))),
        #("call", expr_json(call, ty)),
      ])
    Do(v) -> Object([#("stmt", Str("expr")), #("value", expr_json(v, ty))])
  }
}

fn pat_json(p: Pat, ty: fn(Ty) -> Json) -> Json {
  let sub = fn(x) { pat_json(x, ty) }
  let fields = case p.node {
    PDiscard(n) -> [#("p", Str("discard")), #("name", Str(n))]
    PVar(n) -> [#("p", Str("var")), #("name", Str(n))]
    PInt(text) -> [#("p", Str("int")), #("text", Str(text))]
    PStr(text) -> [#("p", Str("str")), #("text", Str(text))]
    PTuple(items) -> [
      #("p", Str("tuple")),
      #("items", Array(list.map(items, sub))),
    ]
    PCtor(type_, variant, args, spread) -> [
      #("p", Str("ctor")),
      #("type", Str(type_)),
      #("variant", Str(variant)),
      #(
        "args",
        Array(
          list.map(args, fn(a) {
            case a {
              PPositional(q) -> Object([#("pattern", sub(q))])
              PLabelled(l, q) ->
                Object([#("label", Str(l)), #("pattern", sub(q))])
              PShorthand(at, l) ->
                Object([#("label", Str(l)), #("at", at_json(at))])
            }
          }),
        ),
      ),
      #("spread", json.Bool(spread)),
    ]
    PAs(q, n) -> [#("p", Str("as")), #("pattern", sub(q)), #("name", Str(n))]
  }
  Object([#("ty", ty(p.ty)), #("at", at_json(p.at)), ..fields])
}
