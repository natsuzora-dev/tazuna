//// Where a function a built-in keeps captures what Lean cannot keep. Lean
//// keeps such a function as its source with the values of the local
//// variables it uses, and those values must be data it can write as
//// constants: neither a function nor a structure value such as a command.
//// The converter finds such a capture first, at the place it is written, and
//// names the fix.

import gleam/dict.{type Dict}
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/set.{type Set}
import tazuna/internal/dsl_source
import tazuna/internal/ir.{type Expr, type Pat, type Ty, Con, Fun, Tuple, Var}

pub type Site {
  Site(at: ir.At, function: String, message: String)
}

type Kept {
  Kept(index: Int, label: String)
}

/// The places in `p` where a kept function captures a function or a
/// structure value.
pub fn sites(p: ir.Program) -> List(Site) {
  let kept =
    list.fold(list.reverse(dsl_source.kept), dict.new(), fn(d, k) {
      let #(global, index, label) = k
      dict.upsert(d, global, fn(ks) {
        [Kept(index, label), ..option.unwrap(ks, [])]
      })
    })
  let cx = Cx(p, kept)
  list.flat_map(p.functions, fn(f) {
    let env =
      list.fold(f.params, dict.new(), fn(env, q) {
        dict.insert(env, q.name, q.ty)
      })
    walk(cx, env, f.body) |> list.map(fn(s) { s(f.name) })
  })
  |> list.append(
    list.flat_map(p.constants, fn(c) {
      walk(cx, dict.new(), c.value) |> list.map(fn(s) { s(c.name) })
    }),
  )
}

type Cx {
  Cx(p: ir.Program, kept: Dict(String, List(Kept)))
}

type Found =
  fn(String) -> Site

/// Every bad capture in `e`, where `env` types the local variables in scope.
fn walk(cx: Cx, env: Dict(String, Ty), e: Expr) -> List(Found) {
  case e.node {
    ir.Call(f, args) -> {
      let here = case f.node {
        ir.Ref(name, _) -> call(cx, env, name, None, args, None)
        _ -> []
      }
      list.flatten([here, walk(cx, env, f), args_walk(cx, env, args)])
    }
    ir.Pipe(left, right) -> {
      let here = case right.node {
        ir.Call(ir.Expr(node: ir.Ref(name, _), ..), args) ->
          list.append(
            call(cx, env, name, Some(left), args, None),
            args_walk(cx, env, args),
          )
        ir.Ref(name, _) -> call(cx, env, name, Some(left), [], None)
        _ -> walk(cx, env, right)
      }
      list.append(here, walk(cx, env, left))
    }
    ir.Lam(params, _, body) ->
      walk(
        cx,
        list.fold(params, env, fn(env, q) { dict.insert(env, q.name, q.ty) }),
        body,
      )
    ir.Block(stmts) -> block(cx, env, stmts)
    ir.Case(subjects, clauses) ->
      list.append(
        list.flat_map(subjects, walk(cx, env, _)),
        list.flat_map(clauses, fn(c) {
          let env = case c.alternatives {
            [pats, ..] -> list.fold(pats, env, bind)
            [] -> env
          }
          let guard = case c.guard {
            Some(g) -> walk(cx, env, g)
            None -> []
          }
          list.append(guard, walk(cx, env, c.body))
        }),
      )
    ir.IntLit(_) | ir.StrLit(_) | ir.Local(_) | ir.Ref(..) -> []
    ir.Ctor(_, _, args) -> args_walk(cx, env, args)
    ir.Field(r, _) | ir.Index(r, _) | ir.Un(_, r) -> walk(cx, env, r)
    ir.Update(_, _, r, fields) ->
      list.append(walk(cx, env, r), args_walk(cx, env, fields))
    ir.Capture(_, f, before, after) ->
      list.append(
        walk(cx, env, f),
        args_walk(cx, env, list.append(before, after)),
      )
    ir.Bin(_, l, r) -> list.append(walk(cx, env, l), walk(cx, env, r))
    ir.ListOf(items) | ir.TupleOf(items) ->
      list.flat_map(items, walk(cx, env, _))
  }
}

fn args_walk(cx: Cx, env: Dict(String, Ty), args: List(ir.Arg)) -> List(Found) {
  list.flat_map(args, fn(a) {
    case a {
      ir.Positional(v) | ir.Labelled(_, v) -> walk(cx, env, v)
      ir.Shorthand(..) -> []
    }
  })
}

fn block(cx: Cx, env: Dict(String, Ty), stmts: List(ir.Stmt)) -> List(Found) {
  case stmts {
    [] -> []
    [ir.Let(pattern: pat, value: v, ..), ..rest] ->
      list.append(walk(cx, env, v), block(cx, bind(env, pat), rest))
    [ir.Do(v), ..rest] -> list.append(walk(cx, env, v), block(cx, env, rest))
    [ir.Use(_, pats, c), ..rest] -> {
      let inner = list.fold(pats, env, fn(env, p) { bind(env, p.0) })
      let callback = Callback(list.map(pats, fn(p) { p.0 }), rest)
      let here = case c.node {
        ir.Call(ir.Expr(node: ir.Ref(name, _), ..), args) ->
          list.append(
            call(cx, env, name, None, args, Some(callback)),
            args_walk(cx, env, args),
          )
        ir.Ref(name, _) -> call(cx, env, name, None, [], Some(callback))
        _ -> walk(cx, env, c)
      }
      list.append(here, block(cx, inner, rest))
    }
  }
}

type Callback {
  Callback(params: List(Pat), body: List(ir.Stmt))
}

/// The bad captures of the kept arguments of one call to `name`: `piped` is
/// the first argument, before `args`; `callback` is the function `use` passes
/// to the parameter no other argument fills.
fn call(
  cx: Cx,
  env: Dict(String, Ty),
  name: String,
  piped: Option(Expr),
  args: List(ir.Arg),
  callback: Option(Callback),
) -> List(Found) {
  let ks = result.unwrap(dict.get(cx.kept, name), [])
  let positional =
    list.append(
      option.map(piped, fn(v) { [v] }) |> option.unwrap([]),
      list.filter_map(args, fn(a) {
        case a {
          ir.Positional(v) -> Ok(v)
          _ -> Error(Nil)
        }
      }),
    )
  list.flat_map(ks, fn(k) {
    let what = k.label <> " of " <> name
    let by_label =
      list.find_map(args, fn(a) {
        case a {
          ir.Labelled(l, v) if l == k.label -> Ok(Arg(v))
          ir.Shorthand(at, l) if l == k.label -> Ok(Alias(at, l))
          _ -> Error(Nil)
        }
      })
    let arg = case by_label, list.drop(positional, k.index) {
      Ok(a), _ -> Some(a)
      Error(Nil), [v, ..] -> Some(Arg(v))
      Error(Nil), [] ->
        option.map(callback, fn(b) {
          Body(list.fold(b.params, set.new(), bound_pat), b.body)
        })
    }
    case arg {
      None -> []
      Some(Alias(at, l)) -> [local_function(at, what, l)]
      Some(Arg(v)) -> captures(cx, env, what, free(set.new(), v))
      Some(Body(bound, stmts)) ->
        captures(cx, env, what, free_block(bound, stmts))
    }
  })
}

type KeptArg {
  Arg(Expr)
  /// `label:` alone passes the local variable of that name.
  Alias(at: ir.At, name: String)
  Body(bound: Set(String), stmts: List(ir.Stmt))
}

fn local_function(at: ir.At, what: String, name: String) -> Found {
  fn(function) {
    Site(
      at,
      function,
      what
        <> " is kept with the local function `"
        <> name
        <> "`, which Lean cannot keep as data: define it at the top level and pass it by name",
    )
  }
}

fn captures(
  cx: Cx,
  env: Dict(String, Ty),
  what: String,
  used: List(#(String, ir.At, Option(Ty))),
) -> List(Found) {
  list.filter_map(used, fn(u) {
    let #(name, at, ty) = u
    let ty = case ty {
      Some(t) -> Ok(t)
      None -> dict.get(env, name)
    }
    use ty <- result.try(ty)
    case holds(cx.p, ir.solve(cx.p.solved, ty)) {
      Ok(Nil) -> Error(Nil)
      Error(FunctionValue) ->
        Ok(fn(function) {
          Site(
            at,
            function,
            what
              <> " captures `"
              <> name
              <> "`, which holds a function Lean cannot keep as data: define the function at the top level and call it by name",
          )
        })
      Error(StructureValue(t)) ->
        Ok(fn(function) {
          Site(
            at,
            function,
            what
              <> " captures `"
              <> name
              <> "`, which holds a "
              <> t
              <> ", a structure value Lean cannot keep as data: capture only the data the function reads",
          )
        })
    }
  })
}

type NotData {
  FunctionValue
  StructureValue(String)
}

/// Whether values of `t` are data. A user type is looked through to its
/// fields, an alias to what it names; every other type holds what its
/// arguments hold.
fn holds(p: ir.Program, t: Ty) -> Result(Nil, NotData) {
  let all = fn(ts) { list.try_each(ts, holds(p, _)) }
  case t {
    Fun(..) -> Error(FunctionValue)
    Var(_) | ir.Meta(_) -> Ok(Nil)
    Tuple(items) -> all(items)
    Con(name, args) ->
      case
        list.contains(dsl_source.structure_types, name),
        list.find(p.types, fn(d) { d.name == name }),
        list.find(p.aliases, fn(a) { a.name == name })
      {
        True, _, _ -> Error(StructureValue(name))
        _, Ok(d), _ -> {
          let by = list.zip(d.params, args)
          all(
            list.flat_map(d.variants, fn(v) {
              list.map(v.fields, fn(f) { subst(by, f.1) })
            }),
          )
        }
        _, _, Ok(a) -> holds(p, subst(list.zip(a.params, args), a.ty))
        _, _, _ -> all(args)
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

/// The local variables `e` uses that `bound` does not hold, each where it is
/// first written, with its type when the use carries one.
fn free(bound: Set(String), e: Expr) -> List(#(String, ir.At, Option(Ty))) {
  let all = fn(es) { list.flat_map(es, free(bound, _)) }
  let args = fn(args) {
    list.flat_map(args, fn(a) {
      case a {
        ir.Positional(v) | ir.Labelled(_, v) -> free(bound, v)
        ir.Shorthand(at, l) ->
          case set.contains(bound, l) {
            True -> []
            False -> [#(l, at, None)]
          }
      }
    })
  }
  let found = case e.node {
    ir.Local(n) ->
      case set.contains(bound, n) {
        True -> []
        False -> [#(n, e.at, Some(e.ty))]
      }
    ir.IntLit(_) | ir.StrLit(_) | ir.Ref(..) -> []
    ir.Ctor(_, _, a) -> args(a)
    ir.Field(r, _) | ir.Index(r, _) | ir.Un(_, r) -> free(bound, r)
    ir.Update(_, _, r, fields) -> list.append(free(bound, r), args(fields))
    ir.Call(f, a) -> list.append(free(bound, f), args(a))
    ir.Capture(_, f, before, after) ->
      list.append(free(bound, f), args(list.append(before, after)))
    ir.Pipe(l, r) | ir.Bin(_, l, r) -> all([l, r])
    ir.Lam(params, _, body) ->
      free(list.fold(params, bound, fn(b, q) { set.insert(b, q.name) }), body)
    ir.Block(stmts) -> free_block(bound, stmts)
    ir.Case(subjects, clauses) ->
      list.append(
        all(subjects),
        list.flat_map(clauses, fn(c) {
          let inner = case c.alternatives {
            [pats, ..] -> list.fold(pats, bound, bound_pat)
            [] -> bound
          }
          list.append(
            option.map(c.guard, free(inner, _)) |> option.unwrap([]),
            free(inner, c.body),
          )
        }),
      )
    ir.ListOf(items) | ir.TupleOf(items) -> all(items)
  }
  list.unique(found)
}

fn free_block(
  bound: Set(String),
  stmts: List(ir.Stmt),
) -> List(#(String, ir.At, Option(Ty))) {
  case stmts {
    [] -> []
    [ir.Let(pattern: pat, value: v, ..), ..rest] ->
      list.append(free(bound, v), free_block(bound_pat(bound, pat), rest))
    [ir.Do(v), ..rest] -> list.append(free(bound, v), free_block(bound, rest))
    [ir.Use(_, pats, c), ..rest] ->
      list.append(
        free(bound, c),
        free_block(list.fold(pats, bound, fn(b, p) { bound_pat(b, p.0) }), rest),
      )
  }
}

fn bound_pat(b: Set(String), p: Pat) -> Set(String) {
  list.fold(pat_vars(p), b, fn(b, v) { set.insert(b, v.0) })
}

/// Types the variables a pattern binds.
fn bind(env: Dict(String, Ty), p: Pat) -> Dict(String, Ty) {
  list.fold(pat_vars(p), env, fn(env, v) {
    case v.1 {
      Some(t) -> dict.insert(env, v.0, t)
      None -> dict.delete(env, v.0)
    }
  })
}

/// The variables a pattern binds, with their types where the pattern says.
fn pat_vars(p: Pat) -> List(#(String, Option(Ty))) {
  case p.node {
    ir.PVar(n) -> [#(n, Some(p.ty))]
    ir.PAs(inner, n) -> [#(n, Some(p.ty)), ..pat_vars(inner)]
    ir.PTuple(items) -> list.flat_map(items, pat_vars)
    ir.PCtor(_, _, args, _) ->
      list.flat_map(args, fn(a) {
        case a {
          ir.PPositional(q) | ir.PLabelled(_, q) -> pat_vars(q)
          ir.PShorthand(_, l) -> [#(l, None)]
        }
      })
    ir.PDiscard(_) | ir.PInt(_) | ir.PStr(_) -> []
  }
}
