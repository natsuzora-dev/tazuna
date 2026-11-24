//// Where a spec asks `==` of a type holding functions. Gleam compares
//// functions by reference, which has no meaning in a spec, so Lean refuses
//// such a comparison; the converter finds it first, at the place it is
//// written. A generic function passes the demand on to the types it is called
//// at, as do the built-ins whose keys or items are compared.

import gleam/dict.{type Dict}
import gleam/list
import gleam/option.{None, Some}
import gleam/result
import tazuna/internal/dsl_source
import tazuna/internal/ir.{type Expr, type Ty, Con, Fun, Tuple, Var}

pub type Site {
  Site(at: ir.At, function: String, message: String)
}

/// The places in `p` that compare a type holding functions.
pub fn sites(p: ir.Program) -> List(Site) {
  let builtins =
    list.map(dsl_source.needs_equality, fn(b) { #("tazuna." <> b.0, b.1) })
    |> dict.from_list
  let needs = settle(p, builtins, dict.new(), list.length(p.functions) + 1)
  let all = dict.merge(builtins, needs)
  list.flat_map(p.functions, fn(f) {
    walk(p, all, f.body) |> list.filter_map(site(_, f.name))
  })
  |> list.append(
    list.flat_map(p.constants, fn(c) {
      walk(p, all, c.value) |> list.filter_map(site(_, c.name))
    }),
  )
}

/// Each generic function's type variables that some `==` inside it, directly
/// or through a call, needs. Functions call no function recursively, so the
/// demands settle after at most one round per function.
fn settle(
  p: ir.Program,
  builtins: Dict(String, List(String)),
  needs: Dict(String, List(String)),
  rounds: Int,
) -> Dict(String, List(String)) {
  let all = dict.merge(builtins, needs)
  let next =
    list.map(p.functions, fn(f) {
      #(
        f.name,
        walk(p, all, f.body)
          |> list.flat_map(fn(d) { result.unwrap(d.1, []) })
          |> list.unique,
      )
    })
    |> dict.from_list
  case next == needs || rounds == 0 {
    True -> next
    False -> settle(p, builtins, next, rounds - 1)
  }
}

fn site(d: #(Demand, Result(List(String), Nil)), function: String) {
  case d {
    #(Demand(at, what), Error(Nil)) -> Ok(Site(at, function, what))
    _ -> Error(Nil)
  }
}

type Demand {
  Demand(at: ir.At, what: String)
}

/// Every demand for `==` in `e`: the type variables it needs, or `Error` when
/// the type holds a function.
fn walk(
  p: ir.Program,
  needs: Dict(String, List(String)),
  e: Expr,
) -> List(#(Demand, Result(List(String), Nil))) {
  let here = case e.node {
    ir.Bin("==", l, _) | ir.Bin("!=", l, _) -> [
      #(
        Demand(
          e.at,
          "`==` on a type holding functions: Gleam compares functions by reference, which means nothing in a spec",
        ),
        tvars(p, ir.solve(p.solved, l.ty)),
      ),
    ]
    ir.Ref(name, targs) ->
      case dict.get(needs, name) {
        Ok(vs) ->
          list.filter_map(vs, fn(v) {
            case list.key_find(targs, v) {
              Ok(t) ->
                Ok(#(
                  Demand(
                    e.at,
                    name
                      <> " compares values of its type "
                      <> v
                      <> " with ==, and this one holds functions",
                  ),
                  tvars(p, ir.solve(p.solved, t)),
                ))
              Error(Nil) -> Error(Nil)
            }
          })
        Error(Nil) -> []
      }
    _ -> []
  }
  list.append(here, list.flat_map(children(e), walk(p, needs, _)))
}

/// The type variables `t` mentions outside functions, or `Error` when it holds
/// a function. A user type is looked through to its fields, an alias to what
/// it names; every other type holds what its arguments hold.
fn tvars(p: ir.Program, t: Ty) -> Result(List(String), Nil) {
  let all = fn(ts) { list.try_map(ts, tvars(p, _)) |> result.map(list.flatten) }
  case t {
    Fun(..) -> Error(Nil)
    Var(v) -> Ok([v])
    ir.Meta(_) -> Ok([])
    Tuple(items) -> all(items)
    Con(name, args) ->
      case
        list.find(p.types, fn(d) { d.name == name }),
        list.find(p.aliases, fn(a) { a.name == name })
      {
        Ok(d), _ -> {
          let by = list.zip(d.params, args)
          all(
            list.flat_map(d.variants, fn(v) {
              list.map(v.fields, fn(f) { subst(by, f.1) })
            }),
          )
        }
        _, Ok(a) -> tvars(p, subst(list.zip(a.params, args), a.ty))
        _, _ -> all(args)
      }
  }
}

fn subst(by: List(#(String, Ty)), t: Ty) -> Ty {
  case t {
    Var(v) -> result.unwrap(list.key_find(by, v), t)
    Con(n, args) -> Con(n, list.map(args, subst(by, _)))
    Fun(ps, r) -> Fun(list.map(ps, subst(by, _)), subst(by, r))
    Tuple(items) -> Tuple(list.map(items, subst(by, _)))
    ir.Meta(_) -> t
  }
}

fn children(e: Expr) -> List(Expr) {
  let arg = fn(a) {
    case a {
      ir.Positional(v) | ir.Labelled(_, v) -> [v]
      ir.Shorthand(..) -> []
    }
  }
  case e.node {
    ir.IntLit(_) | ir.StrLit(_) | ir.Local(_) | ir.Ref(..) -> []
    ir.Ctor(_, _, args) -> list.flat_map(args, arg)
    ir.Field(r, _) | ir.Index(r, _) | ir.Un(_, r) -> [r]
    ir.Update(_, _, r, fields) -> [r, ..list.flat_map(fields, arg)]
    ir.Call(f, args) -> [f, ..list.flat_map(args, arg)]
    ir.Pipe(l, r) | ir.Bin(_, l, r) -> [l, r]
    ir.Lam(_, _, body) -> [body]
    ir.Block(stmts) ->
      list.flat_map(stmts, fn(s) {
        case s {
          ir.Let(value: v, ..) | ir.Use(call: v, ..) | ir.Do(v) -> [v]
        }
      })
    ir.Case(subjects, clauses) ->
      list.append(
        subjects,
        list.flat_map(clauses, fn(c) {
          case c.guard {
            Some(g) -> [g, c.body]
            None -> [c.body]
          }
        }),
      )
    ir.ListOf(items) | ir.TupleOf(items) -> items
  }
}
