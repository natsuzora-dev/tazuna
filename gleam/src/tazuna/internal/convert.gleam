//// The converter: parses a spec's modules with glance, resolves names, types
//// every node, and builds the IR. It decides no meaning; Lean does. Gleam
//// outside the subset Lean gives meaning to is a `Restricted` finding.
//// The input has passed `gleam build`, so a name or type the converter cannot
//// make sense of is its own bug, reported as `Internal`.

import glance as g
import gleam/bit_array
import gleam/dict.{type Dict}
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string
import tazuna/internal/dsl_source
import tazuna/internal/equality
import tazuna/internal/ir.{
  type Annotation, type Expr, type Pat, type Stmt, type Ty, At, Con, Expr, Fun,
  Meta, Pat, Tuple, Var,
}
import tazuna/internal/json
import tazuna/internal/kept
import tazuna/internal/names.{type Imports}
import tazuna/internal/print

pub type Source {
  Source(module: String, path: String, text: String)
}

/// Gleam the IR has no node for, or that the converter cannot type alone.
pub type Restricted {
  Float
  BitArray
  Panic
  Todo
  Echo
  LetAssert
  Assert
  ListSpread
  ListPattern
  StringPrefixPattern
  External
  ForeignFunction
  ForeignType
  Recursion
  RecursiveType
  Incomparable
  KeptCapture
  ShadowedImport
  MixedReference
  MultiVariantUpdate
  VariantField
  ConstructorValue
  AnnotationNeeded
  RootSpec
}

pub const restricted = [
  Float,
  BitArray,
  Panic,
  Todo,
  Echo,
  LetAssert,
  Assert,
  ListSpread,
  ListPattern,
  StringPrefixPattern,
  External,
  ForeignFunction,
  ForeignType,
  Recursion,
  RecursiveType,
  Incomparable,
  KeptCapture,
  ShadowedImport,
  MixedReference,
  MultiVariantUpdate,
  VariantField,
  ConstructorValue,
  AnnotationNeeded,
  RootSpec,
]

pub type Kind {
  Restricted(Restricted)
  /// A converter bug.
  Internal
}

pub type Finding {
  Finding(kind: Kind, file: String, at: Option(ir.At), message: String)
}

pub fn kind_name(kind: Kind) -> String {
  case kind {
    Internal -> "Internal.convert"
    Restricted(r) ->
      "Restricted."
      <> case r {
        Float -> "float"
        BitArray -> "bitArray"
        Panic -> "panic"
        Todo -> "todo"
        Echo -> "echo"
        LetAssert -> "letAssert"
        Assert -> "assert"
        ListSpread -> "listSpread"
        ListPattern -> "listPattern"
        StringPrefixPattern -> "stringPrefixPattern"
        External -> "external"
        ForeignFunction -> "foreignFunction"
        ForeignType -> "foreignType"
        Recursion -> "recursion"
        RecursiveType -> "recursiveType"
        Incomparable -> "incomparable"
        KeptCapture -> "keptCapture"
        ShadowedImport -> "shadowedImport"
        MixedReference -> "mixedReference"
        MultiVariantUpdate -> "multiVariantUpdate"
        VariantField -> "variantField"
        ConstructorValue -> "constructorValue"
        AnnotationNeeded -> "annotationNeeded"
        RootSpec -> "rootSpec"
      }
  }
}

/// One JSON line, shaped like the engine's lines.
pub fn finding_line(f: Finding) -> String {
  let at = case f.at {
    Some(at) -> [#("line", json.Int(at.line)), #("col", json.Int(at.col))]
    None -> []
  }
  json.encode(
    json.Object(
      list.flatten([
        [#("kind", json.Str(kind_name(f.kind))), #("file", json.Str(f.file))],
        at,
        [#("message", json.Str(f.message))],
      ]),
    ),
  )
}

pub fn ir_text(p: ir.Program) -> String {
  json.encode(ir.to_json(p))
}

type Mod {
  Mod(
    name: String,
    path: String,
    ast: g.Module,
    imports: Imports,
    bits: BitArray,
    starts: List(Int),
  )
}

type TypeInfo {
  TypeInfo(params: List(String), variants: List(ir.Variant))
}

/// `ty` has its aliases expanded, for typing; `written` keeps them, for the IR
/// and printing back.
type Global {
  GFn(labels: List(Option(String)), tvars: List(String), ty: Ty, written: Ty)
  GConst(ty: Ty, written: Ty)
  GCtor(type_: String, variant: String)
}

type Env {
  Env(
    /// The names of the `tazuna` modules.
    dsl: List(String),
    mods: Dict(String, Mod),
    types: Dict(String, TypeInfo),
    /// Alias to its parameters and the type it stands for, as written.
    aliases: Dict(String, #(List(String), Ty)),
    globals: Dict(String, Global),
  )
}

const option_type = "gleam/option.Option"

fn prelude_types() -> List(#(String, TypeInfo)) {
  let v = fn(name, fields) {
    ir.Variant(name, list.map(fields, fn(t) { #(None, t) }))
  }
  [
    #("Bool", TypeInfo([], [v("True", []), v("False", [])])),
    #("Nil", TypeInfo([], [v("Nil", [])])),
    #(
      "Result",
      TypeInfo(["a", "e"], [v("Ok", [Var("a")]), v("Error", [Var("e")])]),
    ),
    #(option_type, TypeInfo(["a"], [v("Some", [Var("a")]), v("None", [])])),
  ]
}

fn constructors(type_: String, info: TypeInfo) -> List(#(String, Global)) {
  list.map(info.variants, fn(v) {
    #(names.constructor(type_, v.name), GCtor(type_, v.name))
  })
}

fn load(s: Source) -> Result(Mod, Finding) {
  let bits = bit_array.from_string(s.text)
  let starts =
    string.split(s.text, "\n")
    |> list.scan(0, fn(acc, line) { acc + string.byte_size(line) + 1 })
    |> list.prepend(0)
  let m =
    Mod(
      s.module,
      s.path,
      g.Module([], [], [], [], []),
      names.imports(s.module, []),
      bits,
      starts,
    )
  case g.module(s.text) {
    Ok(ast) -> Ok(Mod(..m, ast:, imports: names.imports(s.module, ast.imports)))
    Error(g.UnexpectedEndOfInput) ->
      Error(Finding(Internal, s.path, None, "glance: unexpected end of input"))
    Error(g.UnexpectedToken(_, p)) ->
      Error(Finding(
        Internal,
        s.path,
        Some(position(m, p.byte_offset)),
        "glance: unexpected token",
      ))
  }
}

fn position(m: Mod, offset: Int) -> ir.At {
  let #(line, start) =
    list.fold(m.starts, #(0, 0), fn(acc, s) {
      case s <= offset {
        True -> #(acc.0 + 1, s)
        False -> acc
      }
    })
  let col =
    bit_array.slice(m.bits, start, offset - start)
    |> result.try(bit_array.to_string)
    |> result.map(fn(s) { list.length(string.to_utf_codepoints(s)) })
    |> result.unwrap(0)
  At(line, col + 1)
}

fn finding(m: Mod, kind: Restricted, span: g.Span, message: String) -> Finding {
  Finding(Restricted(kind), m.path, Some(position(m, span.start)), message)
}

fn bug(m: Mod, span: g.Span, message: String) -> Finding {
  Finding(Internal, m.path, Some(position(m, span.start)), message)
}

/// Converts the spec's modules beside the `tazuna` modules, whose types and
/// functions Lean owns.
pub fn convert(
  spec: List(Source),
  root_module: String,
) -> Result(ir.Program, List(Finding)) {
  use mods <- result.try(
    list.try_map(spec, load) |> result.map_error(list.wrap),
  )
  use dsls <- result.try(
    list.try_map(dsl_source.modules, fn(m) { load(Source(m.0, m.1, m.2)) })
    |> result.map_error(list.wrap),
  )
  let all = list.append(dsls, mods)
  use <- bail(list.flat_map(mods, module_findings))
  let env0 =
    Env(
      dsl: list.map(dsls, fn(m) { m.name }),
      mods: dict.from_list(list.map(all, fn(m) { #(m.name, m) })),
      types: dict.new(),
      aliases: dict.from_list(
        list.flat_map(all, fn(m) {
          list.map(m.ast.type_aliases, fn(a) {
            #(m.name <> "." <> a.definition.name, #([], Tuple([])))
          })
        }),
      ),
      globals: dict.new(),
    )
  let names_only =
    Env(
      ..env0,
      types: dict.from_list(
        list.flatten([
          prelude_types(),
          list.flat_map(all, fn(m) {
            list.map(m.ast.custom_types, fn(d) {
              #(m.name <> "." <> d.definition.name, TypeInfo([], []))
            })
          }),
        ]),
      ),
    )
  let #(typedefs, type_findings) =
    list.flat_map(all, fn(m) {
      list.map(list.reverse(m.ast.custom_types), fn(d) {
        type_def(names_only, m, d.definition)
      })
    })
    |> partition
  use <- bail(type_findings)
  let #(aliases, alias_findings) =
    list.flat_map(all, fn(m) {
      list.map(list.reverse(m.ast.type_aliases), fn(d) {
        let a = d.definition
        declared(names_only, m, a.aliased)
        |> result.map(ir.Alias(
          m.name <> "." <> a.name,
          a.parameters,
          _,
          position(m, a.location.start),
        ))
      })
    })
    |> partition
  use <- bail(alias_findings)
  let with_aliases =
    Env(
      ..env0,
      aliases: dict.from_list(
        list.map(aliases, fn(a) { #(a.name, #(a.params, a.ty)) }),
      ),
    )
  let types =
    dict.merge(
      dict.from_list(prelude_types()),
      dict.from_list(
        list.map(typedefs, fn(t) {
          let variants =
            list.map(t.variants, fn(v) {
              ir.Variant(
                v.name,
                list.map(v.fields, fn(f) { #(f.0, expand(with_aliases, f.1)) }),
              )
            })
          #(t.name, TypeInfo(t.params, variants))
        }),
      ),
    )
  use <- bail(recursive_type(mods, user_graph(types)))
  let env1 = Env(..with_aliases, types:)
  let #(sigs, sig_findings) =
    list.flat_map(all, fn(m) {
      list.append(
        list.map(m.ast.functions, fn(d) { function_sig(env1, m, d.definition) }),
        list.map(m.ast.constants, fn(d) { constant_sig(env1, m, d.definition) }),
      )
    })
    |> partition
  use <- bail(sig_findings)
  let env =
    Env(
      ..env1,
      globals: dict.from_list(
        list.flatten([
          list.flat_map(dict.to_list(types), fn(t) { constructors(t.0, t.1) }),
          sigs,
        ]),
      ),
    )
  let st0 = St(dict.new(), 0, [])
  let #(st, functions, constants, refs, findings) =
    list.fold(mods, #(st0, [], [], [], []), fn(acc, m) {
      let acc =
        list.fold(list.reverse(m.ast.functions), acc, fn(acc, d) {
          let #(st, fns, cs, refs, fs) = acc
          case function(env, m, St(..st, refs: []), d.definition) {
            Ok(#(f, st)) -> #(
              st,
              [f, ..fns],
              cs,
              [#(f.name, m, st.refs), ..refs],
              fs,
            )
            Error(e) -> #(st, fns, cs, refs, [e, ..fs])
          }
        })
      list.fold(list.reverse(m.ast.constants), acc, fn(acc, d) {
        let #(st, fns, cs, refs, fs) = acc
        case constant(env, m, St(..st, refs: []), d.definition) {
          Ok(#(c, st)) -> #(
            st,
            fns,
            [c, ..cs],
            [#(c.name, m, st.refs), ..refs],
            fs,
          )
          Error(e) -> #(st, fns, cs, refs, [e, ..fs])
        }
      })
    })
  use <- bail(list.reverse(findings))
  use <- bail(recursion(refs))
  let user = fn(name) { !list.contains(env.dsl, names.split(name).0) }
  let user_types = list.filter(typedefs, fn(t) { user(t.name) })
  let program =
    ir.Program(
      root: root_module <> ".spec",
      sources: list.map(mods, fn(m) { #(m.name, m.path) }),
      types: user_types,
      aliases: list.filter(aliases, fn(a) { user(a.name) }),
      functions: list.reverse(functions),
      constants: list.reverse(constants),
      solved: st.solved,
    )
  use <- bail(
    list.map(equality.sites(program), fn(site) {
      let path =
        list.key_find(program.sources, names.split(site.function).0)
        |> result.unwrap(site.function)
      Finding(Restricted(Incomparable), path, Some(site.at), site.message)
    }),
  )
  use <- bail(
    list.map(kept.sites(program), fn(site) {
      let path =
        list.key_find(program.sources, names.split(site.function).0)
        |> result.unwrap(site.function)
      Finding(Restricted(KeptCapture), path, Some(site.at), site.message)
    }),
  )
  use <- bail(list.filter_map(mods, round_trip(program, _)))
  Ok(program)
}

/// The root module must define `spec() -> tazuna.Spec`, the function the
/// engine evaluates. The launcher asks this of every spec it converts.
pub fn root_findings(p: ir.Program) -> List(Finding) {
  let #(module, _) = names.split(p.root)
  let path = list.key_find(p.sources, module) |> result.unwrap(module)
  case list.find(p.functions, fn(f) { f.name == p.root }) {
    Error(Nil) -> [
      Finding(
        Restricted(RootSpec),
        path,
        None,
        "the root module defines no spec() -> tazuna.Spec",
      ),
    ]
    Ok(f) ->
      case f.params, unalias(p.aliases, f.ret) {
        [], Con("tazuna.Spec", []) -> []
        _, _ -> [
          Finding(
            Restricted(RootSpec),
            path,
            Some(f.at),
            "spec must be spec() -> tazuna.Spec, the function the engine evaluates",
          ),
        ]
      }
  }
}

fn unalias(aliases: List(ir.Alias), t: Ty) -> Ty {
  case t {
    Con(n, args) ->
      case list.find(aliases, fn(a) { a.name == n }) {
        Ok(a) -> unalias(aliases, subst(list.zip(a.params, args), a.ty))
        Error(Nil) -> t
      }
    _ -> t
  }
}

fn subst(by: List(#(String, Ty)), t: Ty) -> Ty {
  case t {
    Var(n) -> list.key_find(by, n) |> result.unwrap(t)
    Con(n, args) -> Con(n, list.map(args, subst(by, _)))
    Tuple(items) -> Tuple(list.map(items, subst(by, _)))
    Fun(ps, r) -> Fun(list.map(ps, subst(by, _)), subst(by, r))
    Meta(_) -> t
  }
}

fn partition(results: List(Result(a, e))) -> #(List(a), List(e)) {
  #(
    result.values(results),
    list.filter_map(results, fn(r) {
      case r {
        Error(e) -> Ok(e)
        Ok(_) -> Error(Nil)
      }
    }),
  )
}

fn bail(
  findings: List(Finding),
  next: fn() -> Result(a, List(Finding)),
) -> Result(a, List(Finding)) {
  case findings {
    [] -> next()
    _ -> Error(findings)
  }
}

fn round_trip(p: ir.Program, m: Mod) -> Result(Finding, Nil) {
  let mine = fn(name) { names.split(name).0 == m.name }
  case
    print.round_trip(
      m.imports,
      m.ast,
      list.filter(p.types, fn(t) { mine(t.name) }),
      list.filter(p.aliases, fn(a) { mine(a.name) }),
      list.filter(p.constants, fn(c) { mine(c.name) }),
      list.filter(p.functions, fn(f) { mine(f.name) }),
    )
  {
    Ok(Nil) -> Error(Nil)
    Error(message) -> Ok(Finding(Internal, m.path, None, message))
  }
}

/// Findings about a module's declarations as a whole.
fn module_findings(m: Mod) -> List(Finding) {
  let externals =
    list.filter_map(m.ast.functions, fn(d) {
      case list.any(d.attributes, fn(a) { a.name == "external" }) {
        True ->
          Ok(finding(
            m,
            External,
            d.definition.location,
            "@external function "
              <> d.definition.name
              <> ": Lean cannot see its body",
          ))
        False -> Error(Nil)
      }
    })
  let own_values =
    list.flatten([
      list.map(m.ast.functions, fn(d) {
        #(d.definition.name, d.definition.location)
      }),
      list.map(m.ast.constants, fn(d) {
        #(d.definition.name, d.definition.location)
      }),
      list.flat_map(m.ast.custom_types, fn(d) {
        list.map(d.definition.variants, fn(v) {
          #(v.name, d.definition.location)
        })
      }),
    ])
  let own_types =
    list.map(m.ast.custom_types, fn(d) {
      #(d.definition.name, d.definition.location)
    })
  let shadowed = fn(
    own: List(#(String, g.Span)),
    imported: List(#(String, String)),
  ) {
    list.filter_map(own, fn(o) {
      case list.key_find(imported, o.0) {
        Ok(global) ->
          Ok(finding(
            m,
            ShadowedImport,
            o.1,
            o.0
              <> " is defined here and imported from "
              <> names.split(global).0
              <> "; rename one so each name means one thing",
          ))
        Error(_) -> Error(Nil)
      }
    })
  }
  list.flatten([
    externals,
    shadowed(own_values, m.imports.values),
    shadowed(own_types, m.imports.types),
  ])
}

/// The first cycle of references between globals, reported at the reference
/// that leaves the first global of the cycle in source order.
fn recursion(
  refs: List(#(String, Mod, List(#(String, g.Span)))),
) -> List(Finding) {
  let graph = dict.from_list(list.map(refs, fn(r) { #(r.0, r.2) }))
  list.reverse(refs)
  |> list.find_map(fn(r) {
    use path <- result.try(walk(graph, r.0, [], r.0))
    use #(_, span) <- result.map(case path {
      [_, next, ..] -> list.find(list.reverse(r.2), fn(e) { e.0 == next })
      _ -> Error(Nil)
    })
    finding(
      r.1,
      Recursion,
      span,
      "recursion: "
        <> string.join(path, " -> ")
        <> "; Lean evaluates and encodes spec functions by unfolding, so references must not form a cycle",
    )
  })
  |> result.map(list.wrap)
  |> result.unwrap([])
}

/// Each type to the types its fields name, after alias expansion.
fn user_graph(types: Dict(String, TypeInfo)) -> Dict(String, List(String)) {
  dict.map_values(types, fn(_, info) {
    list.flat_map(info.variants, fn(v) {
      list.flat_map(v.fields, fn(f) { named_types(f.1) })
    })
    |> list.filter(dict.has_key(types, _))
  })
}

fn named_types(t: Ty) -> List(String) {
  case t {
    Con(n, args) -> [n, ..list.flat_map(args, named_types)]
    Tuple(items) -> list.flat_map(items, named_types)
    Fun(ps, r) -> list.flat_map([r, ..ps], named_types)
    Var(_) | Meta(_) -> []
  }
}

/// The first type, in source order, that refers to itself through its fields.
fn recursive_type(
  mods: List(Mod),
  graph: Dict(String, List(String)),
) -> List(Finding) {
  list.find_map(mods, fn(m) {
    list.find_map(list.reverse(m.ast.custom_types), fn(d) {
      let name = m.name <> "." <> d.definition.name
      use path <- result.map(type_cycle(graph, name, [], name))
      finding(
        m,
        RecursiveType,
        d.definition.location,
        "recursive type: "
          <> string.join(path, " -> ")
          <> "; a spec walks values without recursion, so a type must not contain itself",
      )
    })
  })
  |> result.map(list.wrap)
  |> result.unwrap([])
}

fn type_cycle(
  graph: Dict(String, List(String)),
  start: String,
  path: List(String),
  node: String,
) -> Result(List(String), Nil) {
  case dict.get(graph, node) {
    Error(_) -> Error(Nil)
    Ok(out) ->
      list.find_map(out, fn(next) {
        case next == start, list.contains([node, ..path], next) {
          True, _ -> Ok(list.reverse([next, node, ..path]))
          False, True -> Error(Nil)
          False, False -> type_cycle(graph, start, [node, ..path], next)
        }
      })
  }
}

fn walk(
  graph: Dict(String, List(#(String, g.Span))),
  start: String,
  path: List(String),
  node: String,
) -> Result(List(String), Nil) {
  case dict.get(graph, node) {
    Error(_) -> Error(Nil)
    Ok(out) ->
      list.find_map(list.reverse(out), fn(edge) {
        case edge.0 == start, list.contains([node, ..path], edge.0) {
          True, _ -> Ok(list.reverse([edge.0, node, ..path]))
          False, True -> Error(Nil)
          False, False -> walk(graph, start, [node, ..path], edge.0)
        }
      })
  }
}

fn alias_module(m: Mod, alias: String) -> Result(String, Nil) {
  list.key_find(m.imports.aliases, alias)
}

fn type_global(
  env: Env,
  m: Mod,
  span: g.Span,
  module: Option(String),
  name: String,
) -> Result(String, Finding) {
  let known = fn(global) {
    case dict.has_key(env.aliases, global) || dict.has_key(env.types, global) {
      True -> Ok(global)
      False ->
        Error(finding(
          m,
          ForeignType,
          span,
          "type "
            <> name
            <> " comes from "
            <> names.split(global).0
            <> "; a spec uses Int, String, Bool, Nil, List, Result, Option, tazuna's types and its own",
        ))
    }
  }
  case module {
    Some(alias) ->
      case alias_module(m, alias) {
        Error(_) -> Error(bug(m, span, "unknown module " <> alias))
        Ok(mm) -> {
          let global = mm <> "." <> name
          case list.any(m.imports.types, fn(u) { u.1 == global }) {
            True ->
              Error(finding(
                m,
                MixedReference,
                span,
                alias
                  <> "."
                  <> name
                  <> " is also imported unqualified; write it unqualified",
              ))
            False -> known(global)
          }
        }
      }
    None -> {
      let own = m.name <> "." <> name
      case
        dict.has_key(env.types, own) || dict.has_key(env.aliases, own),
        list.key_find(m.imports.types, name),
        name
      {
        True, _, _ -> known(own)
        False, Ok(global), _ -> known(global)
        False, _, "Int"
        | False, _, "String"
        | False, _, "List"
        | False, _, "Bool"
        | False, _, "Nil"
        | False, _, "Result"
        -> Ok(name)
        False, _, "Float" ->
          Error(finding(
            m,
            Float,
            span,
            "Float: SMT reals are not IEEE floats; use Int",
          ))
        False, _, "BitArray" ->
          Error(finding(
            m,
            BitArray,
            span,
            "BitArray is outside the spec subset",
          ))
        False, _, _ ->
          Error(finding(
            m,
            ForeignType,
            span,
            "type " <> name <> " is outside the spec subset",
          ))
      }
    }
  }
}

/// A type in a declaration: type variables are rigid, holes are refused.
fn declared(env: Env, m: Mod, t: g.Type) -> Result(Ty, Finding) {
  case t {
    g.VariableType(_, n) -> Ok(Var(n))
    g.HoleType(span, _) ->
      Error(finding(m, AnnotationNeeded, span, "write the type here"))
    g.TupleType(_, items) ->
      list.try_map(items, declared(env, m, _)) |> result.map(Tuple)
    g.FunctionType(_, ps, r) -> {
      use ps <- result.try(list.try_map(ps, declared(env, m, _)))
      use r <- result.map(declared(env, m, r))
      Fun(ps, r)
    }
    g.NamedType(span, name, module, args) -> {
      use global <- result.try(type_global(env, m, span, module, name))
      use args <- result.map(list.try_map(args, declared(env, m, _)))
      Con(global, args)
    }
  }
}

/// Replaces every alias by the type it stands for. `gleam build` has refused
/// aliases that refer to themselves.
fn expand(env: Env, t: Ty) -> Ty {
  case t {
    Con(n, args) -> {
      let args = list.map(args, expand(env, _))
      case dict.get(env.aliases, n) {
        Ok(#(params, body)) ->
          expand(env, instantiate(body, list.zip(params, args)))
        Error(_) -> Con(n, args)
      }
    }
    Fun(ps, r) -> Fun(list.map(ps, expand(env, _)), expand(env, r))
    Tuple(items) -> Tuple(list.map(items, expand(env, _)))
    Var(_) | Meta(_) -> t
  }
}

fn type_def(env: Env, m: Mod, t: g.CustomType) -> Result(ir.TypeDef, Finding) {
  use variants <- result.map(
    list.try_map(t.variants, fn(v) {
      list.try_map(v.fields, fn(f) {
        case f {
          g.LabelledVariantField(item, label) ->
            declared(env, m, item) |> result.map(fn(t) { #(Some(label), t) })
          g.UnlabelledVariantField(item) ->
            declared(env, m, item) |> result.map(fn(t) { #(None, t) })
        }
      })
      |> result.map(ir.Variant(v.name, _))
    }),
  )
  ir.TypeDef(
    m.name <> "." <> t.name,
    t.parameters,
    variants,
    position(m, t.location.start),
  )
}

fn tvars(acc: List(String), t: Ty) -> List(String) {
  case t {
    Var(n) ->
      case list.contains(acc, n) {
        True -> acc
        False -> list.append(acc, [n])
      }
    Con(_, args) | Tuple(args) -> list.fold(args, acc, tvars)
    Fun(ps, r) -> tvars(list.fold(ps, acc, tvars), r)
    Meta(_) -> acc
  }
}

fn param_name(n: g.AssignmentName) -> String {
  case n {
    g.Named(n) -> n
    g.Discarded(n) -> "_" <> n
  }
}

fn function_sig(
  env: Env,
  m: Mod,
  f: g.Function,
) -> Result(#(String, Global), Finding) {
  let needed =
    finding(
      m,
      AnnotationNeeded,
      f.location,
      "annotate every parameter and the return type of " <> f.name,
    )
  use ps <- result.try(
    list.try_map(f.parameters, fn(p) {
      case p.type_ {
        Some(t) -> declared(env, m, t)
        None -> Error(needed)
      }
    }),
  )
  use r <- result.map(case f.return {
    Some(t) -> declared(env, m, t)
    None -> Error(needed)
  })
  let written = Fun(ps, r)
  let ty = expand(env, written)
  #(
    m.name <> "." <> f.name,
    GFn(list.map(f.parameters, fn(p) { p.label }), tvars([], ty), ty, written),
  )
}

fn constant_sig(
  env: Env,
  m: Mod,
  c: g.Constant,
) -> Result(#(String, Global), Finding) {
  case c.annotation {
    Some(t) ->
      declared(env, m, t)
      |> result.map(fn(t) {
        #(m.name <> "." <> c.name, GConst(expand(env, t), t))
      })
    None ->
      Error(finding(
        m,
        AnnotationNeeded,
        c.location,
        "annotate the type of constant " <> c.name,
      ))
  }
}

type St {
  St(solved: Dict(Int, Ty), next: Int, refs: List(#(String, g.Span)))
}

type R(a) =
  Result(#(a, St), Finding)

type Cx {
  Cx(env: Env, m: Mod, scope: Dict(String, Ty), rigid: List(String))
}

fn fresh(st: St) -> #(Ty, St) {
  #(Meta(st.next), St(..st, next: st.next + 1))
}

fn fresh_many(st: St, n: Int) -> #(List(Ty), St) {
  case n <= 0 {
    True -> #([], st)
    False -> {
      let #(t, st) = fresh(st)
      let #(ts, st) = fresh_many(st, n - 1)
      #([t, ..ts], st)
    }
  }
}

fn prune(st: St, t: Ty) -> Ty {
  case t {
    Meta(id) ->
      case dict.get(st.solved, id) {
        Ok(u) -> prune(st, u)
        Error(_) -> t
      }
    _ -> t
  }
}

fn unify(st: St, a: Ty, b: Ty) -> Result(St, Nil) {
  case prune(st, a), prune(st, b) {
    Meta(i), Meta(j) if i == j -> Ok(st)
    Meta(i), u | u, Meta(i) ->
      Ok(St(..st, solved: dict.insert(st.solved, i, u)))
    Con(n, xs), Con(k, ys) if n == k -> unify_all(st, xs, ys)
    Fun(xs, x), Fun(ys, y) -> unify_all(st, [x, ..xs], [y, ..ys])
    Tuple(xs), Tuple(ys) -> unify_all(st, xs, ys)
    Var(n), Var(k) if n == k -> Ok(st)
    _, _ -> Error(Nil)
  }
}

fn unify_all(st: St, xs: List(Ty), ys: List(Ty)) -> Result(St, Nil) {
  case xs, ys {
    [], [] -> Ok(st)
    [x, ..xs], [y, ..ys] -> unify(st, x, y) |> result.try(unify_all(_, xs, ys))
    _, _ -> Error(Nil)
  }
}

fn show(st: St, t: Ty) -> String {
  case prune(st, t) {
    Con(n, []) -> n
    Con(n, args) ->
      n <> "(" <> string.join(list.map(args, show(st, _)), ", ") <> ")"
    Fun(ps, r) ->
      "fn("
      <> string.join(list.map(ps, show(st, _)), ", ")
      <> ") -> "
      <> show(st, r)
    Tuple(items) ->
      "#(" <> string.join(list.map(items, show(st, _)), ", ") <> ")"
    Var(n) -> n
    Meta(_) -> "_"
  }
}

fn expect(
  cx: Cx,
  st: St,
  span: g.Span,
  want: Ty,
  got: Ty,
) -> Result(St, Finding) {
  unify(st, want, got)
  |> result.replace_error(bug(
    cx.m,
    span,
    "expected " <> show(st, want) <> ", found " <> show(st, got),
  ))
}

fn at(cx: Cx, span: g.Span) -> ir.At {
  position(cx.m, span.start)
}

fn instantiate(t: Ty, by: List(#(String, Ty))) -> Ty {
  case t {
    Var(n) -> list.key_find(by, n) |> result.unwrap(t)
    Con(n, args) -> Con(n, list.map(args, instantiate(_, by)))
    Fun(ps, r) -> Fun(list.map(ps, instantiate(_, by)), instantiate(r, by))
    Tuple(items) -> Tuple(list.map(items, instantiate(_, by)))
    Meta(_) -> t
  }
}

fn bind(cx: Cx, bindings: List(#(String, Ty))) -> Cx {
  Cx(
    ..cx,
    scope: list.fold(bindings, cx.scope, fn(s, b) { dict.insert(s, b.0, b.1) }),
  )
}

fn function(env: Env, m: Mod, st: St, f: g.Function) -> R(ir.Function) {
  let name = m.name <> "." <> f.name
  let assert Ok(GFn(_, tvs, Fun(ps, r), Fun(written_ps, written_r))) =
    dict.get(env.globals, name)
  let params =
    list.map2(f.parameters, written_ps, fn(p, t) {
      ir.FnParam(p.label, param_name(p.name), t)
    })
  let scope = list.map2(params, ps, fn(p, t) { #(p.name, t) }) |> dict.from_list
  let cx = Cx(env, m, scope, tvs)
  use #(body, st) <- result.try(body(cx, st, f.location, f.body))
  use st <- result.map(expect(cx, st, f.location, r, body.ty))
  #(ir.Function(name, params, written_r, body, at(cx, f.location)), st)
}

fn constant(env: Env, m: Mod, st: St, c: g.Constant) -> R(ir.Constant) {
  let name = m.name <> "." <> c.name
  let assert Ok(GConst(t, written)) = dict.get(env.globals, name)
  let cx = Cx(env, m, dict.new(), [])
  use #(value, st) <- result.map(check(cx, st, c.value, t))
  #(ir.Constant(name, written, value, at(cx, c.location)), st)
}

/// A function or lambda body: one expression stays itself, anything else is a
/// block node, so printing it back gives the same statements.
fn body(cx: Cx, st: St, span: g.Span, stmts: List(g.Statement)) -> R(Expr) {
  case stmts {
    [] -> Error(finding(cx.m, Todo, span, "an empty body is a todo"))
    [g.Expression(g.Block(..))]
    | [_, _, ..]
    | [g.Assignment(..)]
    | [g.Use(..)]
    | [g.Assert(..)] -> {
      use #(#(stmts, t), st) <- result.map(block(cx, st, span, stmts))
      #(Expr(at(cx, span), t, ir.Block(stmts)), st)
    }
    [g.Expression(e)] -> infer(cx, st, e)
  }
}

fn infer(cx: Cx, st: St, e: g.Expression) -> R(Expr) {
  expr(cx, st, e, None)
}

fn check(cx: Cx, st: St, e: g.Expression, want: Ty) -> R(Expr) {
  use #(x, st) <- result.try(expr(cx, st, e, Some(want)))
  use st <- result.map(expect(cx, st, e.location, want, x.ty))
  #(x, st)
}

fn node(cx: Cx, span: g.Span, ty: Ty, n: ir.Node) -> Expr {
  Expr(at(cx, span), ty, n)
}

const int_ty = Con("Int", [])

const bool_ty = Con("Bool", [])

const str_ty = Con("String", [])

/// `hint` is the type the context wants; only a lambda uses it, to type its
/// parameters before its body.
fn expr(cx: Cx, st: St, e: g.Expression, hint: Option(Ty)) -> R(Expr) {
  let restrict = fn(kind, span, message) {
    Error(finding(cx.m, kind, span, message))
  }
  case e {
    g.Int(span, text) -> Ok(#(node(cx, span, int_ty, ir.IntLit(text)), st))
    g.String(span, text) ->
      Ok(#(node(cx, span, str_ty, ir.StrLit("\"" <> text <> "\"")), st))
    g.Float(span, _) ->
      restrict(Float, span, "Float: SMT reals are not IEEE floats; use Int")
    g.Panic(span, _) ->
      restrict(Panic, span, "panic: a spec names its failures as rejections")
    g.Todo(span, _) -> restrict(Todo, span, "todo: finish the expression")
    g.Echo(span, _, _) ->
      restrict(Echo, span, "echo: debugging output is not part of a spec")
    g.BitString(span, _) ->
      restrict(BitArray, span, "bit arrays are outside the spec subset")
    g.FnCapture(span, label, f, before, after) ->
      capture(cx, st, span, label, f, before, after)
    g.Variable(span, name) ->
      case dict.get(cx.scope, name) {
        Ok(t) -> Ok(#(node(cx, span, t, ir.Local(name)), st))
        Error(_) -> {
          use #(global, gl) <- result.try(value_global(cx, span, None, name))
          global_value(cx, st, span, global, gl)
        }
      }
    g.NegateInt(span, x) -> {
      use #(x, st) <- result.map(check(cx, st, x, int_ty))
      #(node(cx, span, int_ty, ir.Un("-", x)), st)
    }
    g.NegateBool(span, x) -> {
      use #(x, st) <- result.map(check(cx, st, x, bool_ty))
      #(node(cx, span, bool_ty, ir.Un("!", x)), st)
    }
    g.Block(span, stmts) -> {
      use #(#(stmts, t), st) <- result.map(block(cx, st, span, stmts))
      #(node(cx, span, t, ir.Block(stmts)), st)
    }
    g.Tuple(span, items) -> {
      use #(items, st) <- result.map(infer_all(cx, st, items))
      #(
        node(
          cx,
          span,
          Tuple(list.map(items, fn(x) { x.ty })),
          ir.TupleOf(items),
        ),
        st,
      )
    }
    g.List(span, _, Some(_)) ->
      restrict(ListSpread, span, "list spread: a spec builds lists as literals")
    g.List(span, items, None) -> {
      let #(t, st) = fresh(st)
      use #(items, st) <- result.map(
        list.try_fold(items, #([], st), fn(acc, item) {
          use #(x, st) <- result.map(check(cx, acc.1, item, t))
          #(list.append(acc.0, [x]), st)
        }),
      )
      #(node(cx, span, Con("List", [t]), ir.ListOf(items)), st)
    }
    g.Fn(span, params, ret, stmts) ->
      lambda(cx, st, span, params, ret, stmts, hint)
    g.RecordUpdate(span, module, ctor, record, fields) ->
      update(cx, st, span, module, ctor, record, fields)
    g.FieldAccess(span, container, label) ->
      case module_alias(cx, container) {
        Some(alias) -> {
          use #(global, gl) <- result.try(value_global(
            cx,
            span,
            Some(alias),
            label,
          ))
          global_value(cx, st, span, global, gl)
        }
        None -> field(cx, st, span, container, label)
      }
    g.TupleIndex(span, tuple, k) -> {
      use #(x, st) <- result.try(infer(cx, st, tuple))
      case prune(st, x.ty) {
        Tuple(items) ->
          case list.drop(items, k) {
            [t, ..] -> Ok(#(node(cx, span, t, ir.Index(x, k)), st))
            [] -> Error(bug(cx.m, span, "tuple index out of range"))
          }
        Meta(_) ->
          restrict(
            AnnotationNeeded,
            span,
            "annotate the tuple's type so its element can be typed",
          )
        t -> Error(bug(cx.m, span, "tuple index on " <> show(st, t)))
      }
    }
    g.Call(span, f, args) -> {
      use #(c, st) <- result.try(callee(cx, st, f))
      use #(#(x, _), st) <- result.map(apply(cx, st, span, c, args, None, None))
      #(x, st)
    }
    g.Case(span, subjects, clauses) -> case_(cx, st, span, subjects, clauses)
    g.BinaryOperator(span, g.Pipe, l, r) -> pipe(cx, st, span, l, r)
    g.BinaryOperator(span, op, l, r) -> binary(cx, st, span, op, l, r)
  }
}

fn infer_all(cx: Cx, st: St, es: List(g.Expression)) -> R(List(Expr)) {
  list.try_fold(es, #([], st), fn(acc, e) {
    use #(x, st) <- result.map(infer(cx, acc.1, e))
    #(list.append(acc.0, [x]), st)
  })
}

fn binary(
  cx: Cx,
  st: St,
  span: g.Span,
  op: g.BinaryOperator,
  l: g.Expression,
  r: g.Expression,
) -> R(Expr) {
  let both = fn(symbol, operand, result) {
    use #(l, st) <- result.try(check(cx, st, l, operand))
    use #(r, st) <- result.map(check(cx, st, r, operand))
    #(node(cx, span, result, ir.Bin(symbol, l, r)), st)
  }
  case op {
    g.And -> both("&&", bool_ty, bool_ty)
    g.Or -> both("||", bool_ty, bool_ty)
    g.LtInt -> both("<", int_ty, bool_ty)
    g.LtEqInt -> both("<=", int_ty, bool_ty)
    g.GtInt -> both(">", int_ty, bool_ty)
    g.GtEqInt -> both(">=", int_ty, bool_ty)
    g.AddInt -> both("+", int_ty, int_ty)
    g.SubInt -> both("-", int_ty, int_ty)
    g.MultInt -> both("*", int_ty, int_ty)
    g.DivInt -> both("/", int_ty, int_ty)
    g.RemainderInt -> both("%", int_ty, int_ty)
    g.Concatenate -> both("<>", str_ty, str_ty)
    g.Eq | g.NotEq -> {
      use #(l, st) <- result.try(infer(cx, st, l))
      use #(r, st) <- result.map(check(cx, st, r, l.ty))
      let symbol = case op {
        g.Eq -> "=="
        _ -> "!="
      }
      #(node(cx, span, bool_ty, ir.Bin(symbol, l, r)), st)
    }
    g.Pipe -> pipe(cx, st, span, l, r)
    g.LtFloat
    | g.LtEqFloat
    | g.GtFloat
    | g.GtEqFloat
    | g.AddFloat
    | g.SubFloat
    | g.MultFloat
    | g.DivFloat ->
      Error(finding(
        cx.m,
        Float,
        span,
        "Float arithmetic: SMT reals are not IEEE floats; use Int",
      ))
  }
}

/// The module alias a `alias.name` container names, unless a local shadows it.
fn module_alias(cx: Cx, e: g.Expression) -> Option(String) {
  case e {
    g.Variable(_, a) ->
      case dict.has_key(cx.scope, a), alias_module(cx.m, a) {
        False, Ok(_) -> Some(a)
        _, _ -> None
      }
    _ -> None
  }
}

fn value_global(
  cx: Cx,
  span: g.Span,
  module: Option(String),
  name: String,
) -> Result(#(String, Global), Finding) {
  let env = cx.env
  let m = cx.m
  let found = fn(global) {
    let #(module, _) = names.split(global)
    let builtin = list.contains(dsl_source.builtins, global)
    let in_dsl = list.contains(env.dsl, module)
    case dict.get(env.globals, global) {
      Ok(GFn(..)) | Ok(GConst(..)) if in_dsl && !builtin ->
        Error(finding(
          m,
          ForeignFunction,
          span,
          global
            <> " is not a built-in: a spec calls its own functions and tazuna's built-ins",
        ))
      Ok(gl) -> Ok(#(global, gl))
      Error(_) ->
        case dict.has_key(env.mods, names.split(global).0) {
          True -> Error(bug(m, span, "unknown value " <> global))
          False ->
            Error(finding(
              m,
              ForeignFunction,
              span,
              global
                <> " is outside the spec: a spec calls its own functions and tazuna's",
            ))
        }
    }
  }
  case module {
    Some(alias) ->
      case alias_module(m, alias) {
        Error(_) -> Error(bug(m, span, "unknown module " <> alias))
        Ok(mm) -> {
          let global = mm <> "." <> name
          case list.any(m.imports.values, fn(u) { u.1 == global }) {
            True ->
              Error(finding(
                m,
                MixedReference,
                span,
                alias
                  <> "."
                  <> name
                  <> " is also imported unqualified; write it unqualified",
              ))
            False -> found(global)
          }
        }
      }
    None -> {
      let own = m.name <> "." <> name
      case
        dict.has_key(env.globals, own),
        list.key_find(m.imports.values, name)
      {
        True, _ -> found(own)
        False, Ok(global) -> found(global)
        False, Error(_) -> found("gleam." <> name)
      }
    }
  }
}

fn fields_of(
  cx: Cx,
  type_: String,
  variant: String,
) -> #(TypeInfo, List(#(Option(String), Ty))) {
  let assert Ok(info) = dict.get(cx.env.types, type_)
  let fields =
    list.find(info.variants, fn(v) { v.name == variant })
    |> result.map(fn(v) { v.fields })
    |> result.unwrap([])
  #(info, fields)
}

/// The type of a constructor's value with fresh type arguments, and its fields' types at them.
fn constructor_type(
  cx: Cx,
  st: St,
  type_: String,
  variant: String,
) -> #(Ty, List(#(Option(String), Ty)), TypeInfo, St) {
  let #(info, fields) = fields_of(cx, type_, variant)
  let #(metas, st) = fresh_many(st, list.length(info.params))
  let by = list.zip(info.params, metas)
  #(
    Con(type_, metas),
    list.map(fields, fn(f) { #(f.0, instantiate(f.1, by)) }),
    info,
    st,
  )
}

fn global_value(
  cx: Cx,
  st: St,
  span: g.Span,
  global: String,
  gl: Global,
) -> R(Expr) {
  let st = St(..st, refs: [#(global, span), ..st.refs])
  case gl {
    GFn(_, tvs, ty, _) -> {
      let #(metas, st) = fresh_many(st, list.length(tvs))
      let by = list.zip(tvs, metas)
      Ok(#(node(cx, span, instantiate(ty, by), ir.Ref(global, by)), st))
    }
    GConst(ty, _) -> Ok(#(node(cx, span, ty, ir.Ref(global, [])), st))
    GCtor(type_, variant) -> {
      let #(t, fields, _, st) = constructor_type(cx, st, type_, variant)
      Ok(#(constructor_value(cx, span, type_, variant, t, fields), st))
    }
  }
}

/// A constructor as a value: itself when it has no fields, else a function
/// of its fields, which Lean expands.
fn constructor_value(
  cx: Cx,
  span: g.Span,
  type_: String,
  variant: String,
  t: Ty,
  fields: List(#(Option(String), Ty)),
) -> Expr {
  let ty = case fields {
    [] -> t
    _ -> Fun(list.map(fields, fn(f) { f.1 }), t)
  }
  node(cx, span, ty, ir.Ctor(type_, variant, []))
}

/// `f(before.., label: _, after..)`, typed as the call with `_` a fresh local
/// and kept as a capture, which Lean expands into a function of `_`.
fn capture(
  cx: Cx,
  st: St,
  span: g.Span,
  label: Option(String),
  f: g.Expression,
  before: List(g.Field(g.Expression)),
  after: List(g.Field(g.Expression)),
) -> R(Expr) {
  use #(c, st) <- result.try(callee(cx, st, f))
  let #(c, st) = case c {
    CCtor(type_, variant, cspan) -> {
      let #(t, fields, _, st) = constructor_type(cx, st, type_, variant)
      let value = constructor_value(cx, cspan, type_, variant, t, fields)
      #(CFn(value, list.map(fields, fn(f) { f.0 })), st)
    }
    CFn(..) -> #(c, st)
  }
  let #(hole_ty, st) = fresh(st)
  let hole = g.Variable(span, "_")
  let field = case label {
    Some(l) -> g.LabelledField(l, span, hole)
    None -> g.UnlabelledField(hole)
  }
  let cx_hole = Cx(..cx, scope: dict.insert(cx.scope, "_", hole_ty))
  use #(#(call, _), st) <- result.try(apply(
    cx_hole,
    st,
    span,
    c,
    list.flatten([before, [field], after]),
    None,
    None,
  ))
  case call.node {
    ir.Call(function, args) -> {
      let n = list.length(before)
      Ok(#(
        node(
          cx,
          span,
          Fun([hole_ty], call.ty),
          ir.Capture(
            label,
            function,
            list.take(args, n),
            list.drop(args, n + 1),
          ),
        ),
        st,
      ))
    }
    _ -> Error(bug(cx.m, span, "a capture is no call"))
  }
}

fn field(
  cx: Cx,
  st: St,
  span: g.Span,
  container: g.Expression,
  label: String,
) -> R(Expr) {
  use #(x, st) <- result.try(infer(cx, st, container))
  case prune(st, x.ty) {
    Con(type_, args) ->
      case dict.get(cx.env.types, type_) {
        Ok(info) ->
          case accessor(info, label) {
            Ok(t) ->
              Ok(#(
                node(
                  cx,
                  span,
                  instantiate(t, list.zip(info.params, args)),
                  ir.Field(x, label),
                ),
                st,
              ))
            Error(_) ->
              Error(finding(
                cx.m,
                VariantField,
                span,
                label
                  <> " is not a field every variant of "
                  <> names.split(type_).1
                  <> " has at the same place; match the variant with case",
              ))
          }
        Error(_) -> Error(bug(cx.m, span, "field " <> label <> " of " <> type_))
      }
    Meta(_) ->
      Error(finding(
        cx.m,
        AnnotationNeeded,
        span,
        "annotate the record's type so ." <> label <> " can be typed",
      ))
    t -> Error(bug(cx.m, span, "field " <> label <> " of " <> show(st, t)))
  }
}

/// Gleam's record accessor, as Lean's `TypeDecl.accessor`: the label sits at
/// the same index with the same type in every variant.
fn accessor(info: TypeInfo, label: String) -> Result(Ty, Nil) {
  case info.variants {
    [first, ..] -> {
      let indexed = list.index_map(first.fields, fn(f, k) { #(k, f) })
      use #(k, #(_, t)) <- result.try(
        list.find(indexed, fn(p) { p.1.0 == Some(label) }),
      )
      let same =
        list.all(info.variants, fn(v) {
          case list.drop(v.fields, k) {
            [#(Some(l), u), ..] -> l == label && u == t
            _ -> False
          }
        })
      case same {
        True -> Ok(t)
        False -> Error(Nil)
      }
    }
    [] -> Error(Nil)
  }
}

fn update(
  cx: Cx,
  st: St,
  span: g.Span,
  module: Option(String),
  ctor: String,
  record: g.Expression,
  fields: List(g.RecordUpdateField(g.Expression)),
) -> R(Expr) {
  use #(_, gl) <- result.try(value_global(cx, span, module, ctor))
  case gl {
    GCtor(type_, variant) -> {
      let #(t, field_tys, info, st) = constructor_type(cx, st, type_, variant)
      case info.variants {
        [_, _, ..] ->
          Error(finding(
            cx.m,
            MultiVariantUpdate,
            span,
            "record update on "
              <> names.split(type_).1
              <> ", which has several variants: build the variant with its constructor",
          ))
        _ -> {
          use #(r, st) <- result.try(check(cx, st, record, t))
          use #(args, st) <- result.map(
            list.try_fold(fields, #([], st), fn(acc, f) {
              let #(args, st) = acc
              let assert Ok(want) = list.key_find(field_tys, Some(f.label))
              case f.item {
                Some(v) -> {
                  use #(v, st) <- result.map(check(cx, st, v, want))
                  #(list.append(args, [ir.Labelled(f.label, v)]), st)
                }
                None -> {
                  use st <- result.map(shorthand(cx, st, span, f.label, want))
                  #(
                    list.append(args, [ir.Shorthand(at(cx, span), f.label)]),
                    st,
                  )
                }
              }
            }),
          )
          #(node(cx, span, t, ir.Update(type_, variant, r, args)), st)
        }
      }
    }
    _ -> Error(bug(cx.m, span, ctor <> " is not a constructor"))
  }
}

fn shorthand(
  cx: Cx,
  st: St,
  span: g.Span,
  label: String,
  want: Ty,
) -> Result(St, Finding) {
  case dict.get(cx.scope, label) {
    Ok(t) -> expect(cx, st, span, want, t)
    Error(_) ->
      Error(bug(cx.m, span, "shorthand " <> label <> " names no variable"))
  }
}

fn lambda(
  cx: Cx,
  st: St,
  span: g.Span,
  params: List(g.FnParameter),
  ret: Option(g.Type),
  stmts: List(g.Statement),
  hint: Option(Ty),
) -> R(Expr) {
  let hinted = case option.map(hint, prune(st, _)) {
    Some(Fun(ps, _)) ->
      case list.length(ps) == list.length(params) {
        True -> list.map(ps, Some)
        False -> list.map(params, fn(_) { None })
      }
    _ -> list.map(params, fn(_) { None })
  }
  use #(ps, st) <- result.try(
    list.try_fold(list.zip(params, hinted), #([], st), fn(acc, p) {
      let #(ps, st) = acc
      let #(param, hint) = p
      use #(#(ann, t), st) <- result.try(case param.type_ {
        Some(a) -> {
          use #(#(a, t), st) <- result.try(annotation(cx, st, a))
          case hint {
            Some(h) ->
              expect(cx, st, span, h, t)
              |> result.map(fn(st) { #(#(Some(a), t), st) })
            None -> Ok(#(#(Some(a), t), st))
          }
        }
        None ->
          case hint {
            Some(h) -> Ok(#(#(None, h), st))
            None -> {
              let #(t, st) = fresh(st)
              Ok(#(#(None, t), st))
            }
          }
      })
      Ok(#(list.append(ps, [ir.Param(param_name(param.name), t, ann)]), st))
    }),
  )
  let inner = bind(cx, list.map(ps, fn(p) { #(p.name, p.ty) }))
  use #(b, st) <- result.try(body(inner, st, span, stmts))
  use #(ret_ann, st) <- result.map(case ret {
    Some(a) -> {
      use #(#(a, t), st) <- result.try(annotation(cx, st, a))
      use st <- result.map(expect(cx, st, span, t, b.ty))
      #(Some(a), st)
    }
    None -> Ok(#(None, st))
  })
  #(
    node(
      cx,
      span,
      Fun(list.map(ps, fn(p) { p.ty }), b.ty),
      ir.Lam(ps, ret_ann, b),
    ),
    st,
  )
}

/// A source annotation: holes and type variables the function does not bind
/// are fresh inference variables.
fn annotation(cx: Cx, st: St, t: g.Type) -> R(#(Annotation, Ty)) {
  case t {
    g.HoleType(_, name) -> {
      let #(m, st) = fresh(st)
      Ok(#(#(ir.AHole("_" <> name), m), st))
    }
    g.VariableType(_, n) ->
      case list.contains(cx.rigid, n) {
        True -> Ok(#(#(ir.AVar(n), Var(n)), st))
        False -> {
          let #(m, st) = fresh(st)
          Ok(#(#(ir.AVar(n), m), st))
        }
      }
    g.TupleType(_, items) -> {
      use #(items, st) <- result.map(annotations(cx, st, items))
      #(
        #(
          ir.ATuple(list.map(items, fn(i) { i.0 })),
          Tuple(list.map(items, fn(i) { i.1 })),
        ),
        st,
      )
    }
    g.FunctionType(_, ps, r) -> {
      use #(ps, st) <- result.try(annotations(cx, st, ps))
      use #(#(ra, rt), st) <- result.map(annotation(cx, st, r))
      #(
        #(
          ir.AFun(list.map(ps, fn(i) { i.0 }), ra),
          Fun(list.map(ps, fn(i) { i.1 }), rt),
        ),
        st,
      )
    }
    g.NamedType(span, name, module, args) -> {
      use global <- result.try(type_global(cx.env, cx.m, span, module, name))
      use #(args, st) <- result.map(annotations(cx, st, args))
      #(
        #(
          ir.ACon(global, list.map(args, fn(i) { i.0 })),
          expand(cx.env, Con(global, list.map(args, fn(i) { i.1 }))),
        ),
        st,
      )
    }
  }
}

fn annotations(cx: Cx, st: St, ts: List(g.Type)) -> R(List(#(Annotation, Ty))) {
  list.try_fold(ts, #([], st), fn(acc, t) {
    use #(x, st) <- result.map(annotation(cx, acc.1, t))
    #(list.append(acc.0, [x]), st)
  })
}

type Callee {
  CFn(function: Expr, labels: List(Option(String)))
  CCtor(type_: String, variant: String, span: g.Span)
}

/// A `use` callback: its patterns and the rest of the block.
type Callback {
  Callback(span: g.Span, patterns: List(g.UsePattern), rest: List(g.Statement))
}

fn callee(cx: Cx, st: St, f: g.Expression) -> R(Callee) {
  let named = case f {
    g.Variable(span, name) ->
      case dict.has_key(cx.scope, name) {
        True -> None
        False -> Some(#(span, None, name))
      }
    g.FieldAccess(span, container, label) ->
      module_alias(cx, container)
      |> option.map(fn(a) { #(span, Some(a), label) })
    _ -> None
  }
  case named {
    Some(#(span, module, name)) -> {
      use #(global, gl) <- result.try(value_global(cx, span, module, name))
      case gl {
        GCtor(type_, variant) -> Ok(#(CCtor(type_, variant, span), st))
        GFn(labels, ..) -> {
          use #(x, st) <- result.map(global_value(cx, st, span, global, gl))
          #(CFn(x, labels), st)
        }
        GConst(..) -> {
          use #(x, st) <- result.map(global_value(cx, st, span, global, gl))
          #(CFn(x, []), st)
        }
      }
    }
    None -> {
      use #(x, st) <- result.map(infer(cx, st, f))
      #(CFn(x, []), st)
    }
  }
}

type Slot {
  Written(index: Int, value: g.Expression)
  WrittenShorthand(index: Int, label: String)
  Piped(Expr)
  Back(Callback)
}

/// Gleam's placement: labelled arguments go to their parameter, the others
/// fill the remaining parameters in order, a piped value first and a `use`
/// callback last.
fn place(
  labels: List(Option(String)),
  slots: List(#(Option(String), Slot)),
) -> Result(List(Slot), Nil) {
  let labelled =
    list.filter_map(slots, fn(s) {
      option.to_result(s.0, Nil) |> result.map(fn(l) { #(l, s.1) })
    })
  let positional =
    list.filter_map(slots, fn(s) {
      case s.0 {
        None -> Ok(s.1)
        Some(_) -> Error(Nil)
      }
    })
  let #(rest, placed) =
    list.map_fold(labels, positional, fn(queue, l) {
      case
        option.to_result(l, Nil) |> result.try(list.key_find(labelled, _)),
        queue
      {
        Ok(s), _ -> #(queue, Ok(s))
        Error(_), [s, ..queue] -> #(queue, Ok(s))
        Error(_), [] -> #([], Error(Nil))
      }
    })
  case rest {
    [] -> result.all(placed)
    _ -> Error(Nil)
  }
}

fn is_lambda(s: Slot) -> Bool {
  case s {
    Written(_, g.Fn(..)) -> True
    _ -> False
  }
}

/// A call. Returns the call node and, for a `use`, the callback's typed
/// patterns and statements.
fn apply(
  cx: Cx,
  st: St,
  span: g.Span,
  c: Callee,
  args: List(g.Field(g.Expression)),
  piped: Option(Expr),
  callback: Option(Callback),
) -> R(#(Expr, Option(#(List(#(Pat, Option(Annotation))), List(Stmt))))) {
  let source =
    list.index_map(args, fn(a, k) {
      case a {
        g.UnlabelledField(v) -> #(None, Written(k, v))
        g.LabelledField(l, _, v) -> #(Some(l), Written(k, v))
        g.ShorthandField(l, _) -> #(Some(l), WrittenShorthand(k, l))
      }
    })
  let slots =
    list.flatten([
      option.map(piped, fn(p) { [#(None, Piped(p))] }) |> option.unwrap([]),
      source,
      option.map(callback, fn(b) { [#(None, Back(b))] }) |> option.unwrap([]),
    ])
  let total = list.length(slots)
  use #(labels, params, ret, function, st) <- result.try(case c {
    CCtor(type_, variant, cspan) ->
      case piped, callback {
        None, None -> {
          let #(t, fields, _, st) = constructor_type(cx, st, type_, variant)
          Ok(#(
            list.map(fields, fn(f) { f.0 }),
            list.map(fields, fn(f) { f.1 }),
            t,
            None,
            st,
          ))
        }
        _, _ ->
          Error(finding(
            cx.m,
            ConstructorValue,
            cspan,
            variant
              <> " called through a pipe or use: write "
              <> variant
              <> "(..) with every argument",
          ))
      }
    CFn(f, labels) ->
      case prune(st, f.ty) {
        Fun(ps, r) -> {
          let labels = case labels {
            [] -> list.map(ps, fn(_) { None })
            _ -> labels
          }
          Ok(#(labels, ps, r, Some(f), st))
        }
        t -> {
          let #(ps, st) = fresh_many(st, total)
          let #(r, st) = fresh(st)
          use st <- result.map(expect(cx, st, span, Fun(ps, r), t))
          #(list.map(ps, fn(_) { None }), ps, r, Some(f), st)
        }
      }
  })
  use placed <- result.try(
    place(labels, slots)
    |> result.replace_error(bug(
      cx.m,
      span,
      "arguments do not fit the parameters",
    )),
  )
  let pairs = list.zip(placed, params)
  let phase = fn(st, done, which: fn(Slot) -> Bool) {
    list.try_fold(pairs, #(done, None, st), fn(acc, p) {
      let #(done, back, st) = acc
      let #(slot, want) = p
      case which(slot), slot {
        False, _ -> Ok(acc)
        True, Written(k, v) -> {
          use #(x, st) <- result.map(check(cx, st, v, want))
          #(dict.insert(done, k, x), back, st)
        }
        True, WrittenShorthand(k, l) -> {
          use st <- result.map(shorthand(cx, st, span, l, want))
          #(
            done |> dict.insert(k, Expr(at(cx, span), want, ir.Local(l))),
            back,
            st,
          )
        }
        True, Piped(x) -> {
          use st <- result.map(expect(cx, st, span, want, x.ty))
          #(done, back, st)
        }
        True, Back(b) -> {
          use #(typed, st) <- result.map(use_callback(cx, st, b, want))
          #(done, Some(typed), st)
        }
      }
    })
  }
  use #(done, _, st) <- result.try(
    phase(st, dict.new(), fn(s) {
      case s {
        Back(_) -> False
        _ -> !is_lambda(s)
      }
    }),
  )
  use #(done, _, st) <- result.try(phase(st, done, is_lambda))
  use #(done, back, st) <- result.map(
    phase(st, done, fn(s) {
      case s {
        Back(_) -> True
        _ -> False
      }
    }),
  )
  let ir_args =
    list.index_map(args, fn(a, k) {
      let assert Ok(x) = dict.get(done, k)
      case a {
        g.UnlabelledField(_) -> ir.Positional(x)
        g.LabelledField(l, _, _) -> ir.Labelled(l, x)
        g.ShorthandField(l, lspan) -> ir.Shorthand(at(cx, lspan), l)
      }
    })
  let n = case function {
    Some(f) -> ir.Call(f, ir_args)
    None -> {
      let assert CCtor(type_, variant, _) = c
      ir.Ctor(type_, variant, ir_args)
    }
  }
  #(#(node(cx, span, ret, n), back), st)
}

fn use_callback(
  cx: Cx,
  st: St,
  b: Callback,
  want: Ty,
) -> R(#(List(#(Pat, Option(Annotation))), List(Stmt))) {
  use #(ps, r, st) <- result.try(case prune(st, want) {
    Fun(ps, r) -> Ok(#(ps, r, st))
    t -> {
      let #(ps, st) = fresh_many(st, list.length(b.patterns))
      let #(r, st) = fresh(st)
      use st <- result.map(expect(cx, st, b.span, Fun(ps, r), t))
      #(ps, r, st)
    }
  })
  use #(pats, bindings, st) <- result.try(
    list.try_fold(list.zip(b.patterns, ps), #([], [], st), fn(acc, p) {
      let #(pats, bindings, st) = acc
      let #(up, t) = p
      use #(ann, st) <- result.try(case up.annotation {
        Some(a) -> {
          use #(#(a, at), st) <- result.try(annotation(cx, st, a))
          use st <- result.map(expect(cx, st, b.span, at, t))
          #(Some(a), st)
        }
        None -> Ok(#(None, st))
      })
      use #(#(pat, bs), st) <- result.map(pattern(cx, st, up.pattern, t))
      #(list.append(pats, [#(pat, ann)]), list.append(bindings, bs), st)
    }),
  )
  use #(#(stmts, t), st) <- result.try(block(
    bind(cx, bindings),
    st,
    b.span,
    b.rest,
  ))
  use st <- result.map(expect(cx, st, b.span, r, t))
  #(#(pats, stmts), st)
}

fn pipe(
  cx: Cx,
  st: St,
  span: g.Span,
  l: g.Expression,
  r: g.Expression,
) -> R(Expr) {
  use #(left, st) <- result.try(infer(cx, st, l))
  let apply_to = fn(st, right: Expr) {
    let #(res, st) = fresh(st)
    use st <- result.map(expect(cx, st, span, Fun([left.ty], res), right.ty))
    #(node(cx, span, res, ir.Pipe(left, right)), st)
  }
  case r {
    g.Call(cspan, f, args) -> {
      use #(c, st) <- result.try(callee(cx, st, f))
      let inserted = case c {
        CFn(fx, _) ->
          case prune(st, fx.ty) {
            Fun(ps, _) -> list.length(ps) == list.length(args) + 1
            _ -> False
          }
        CCtor(..) -> True
      }
      case inserted {
        True -> {
          use #(#(call, _), st) <- result.map(apply(
            cx,
            st,
            cspan,
            c,
            args,
            Some(left),
            None,
          ))
          #(node(cx, span, call.ty, ir.Pipe(left, call)), st)
        }
        False -> {
          use #(#(call, _), st) <- result.try(apply(
            cx,
            st,
            cspan,
            c,
            args,
            None,
            None,
          ))
          apply_to(st, call)
        }
      }
    }
    _ -> {
      use #(right, st) <- result.try(infer(cx, st, r))
      apply_to(st, right)
    }
  }
}

fn block(
  cx: Cx,
  st: St,
  span: g.Span,
  stmts: List(g.Statement),
) -> R(#(List(Stmt), Ty)) {
  let prepend = fn(r: R(#(List(Stmt), Ty)), s: Stmt) {
    result.map(r, fn(p) { #(#([s, ..p.0.0], p.0.1), p.1) })
  }
  case stmts {
    [] -> Error(bug(cx.m, span, "empty block"))
    [g.Expression(e)] -> {
      use #(x, st) <- result.map(infer(cx, st, e))
      #(#([ir.Do(x)], x.ty), st)
    }
    [g.Expression(e), ..rest] -> {
      use #(x, st) <- result.try(infer(cx, st, e))
      prepend(block(cx, st, span, rest), ir.Do(x))
    }
    [g.Assert(s, ..), ..] ->
      Error(finding(
        cx.m,
        Assert,
        s,
        "assert: state the property as an invariant or ensures",
      ))
    [g.Assignment(s, g.LetAssert(_), ..), ..] ->
      Error(finding(
        cx.m,
        LetAssert,
        s,
        "let assert: a spec names its failures; use case and a rejection",
      ))
    [g.Assignment(s, g.Let, p, ann, value), ..rest] -> {
      use #(ann, st) <- result.try(case ann {
        Some(a) ->
          annotation(cx, st, a) |> result.map(fn(r) { #(Some({ r.0 }), r.1) })
        None -> Ok(#(None, st))
      })
      use #(v, st) <- result.try(case ann {
        Some(#(_, t)) -> check(cx, st, value, t)
        None -> infer(cx, st, value)
      })
      use #(#(pat, bindings), st) <- result.try(pattern(cx, st, p, v.ty))
      let stmt = ir.Let(at(cx, s), pat, option.map(ann, fn(a) { a.0 }), v)
      case rest {
        [] -> Ok(#(#([stmt], v.ty), st))
        _ -> prepend(block(bind(cx, bindings), st, span, rest), stmt)
      }
    }
    [g.Use(s, patterns, function), ..rest] -> {
      let b = Callback(s, patterns, rest)
      let #(f, args) = case function {
        g.Call(_, f, args) -> #(f, Some(args))
        f -> #(f, None)
      }
      use #(c, st) <- result.try(callee(cx, st, f))
      use #(#(call, back), st) <- result.try(apply(
        cx,
        st,
        function.location,
        c,
        option.unwrap(args, []),
        None,
        Some(b),
      ))
      let assert Some(#(pats, rest)) = back
      let shown = case args, c {
        Some(_), _ -> call
        None, CFn(fx, _) -> fx
        None, CCtor(..) -> call
      }
      Ok(#(#([ir.Use(at(cx, s), pats, shown), ..rest], call.ty), st))
    }
  }
}

fn case_(
  cx: Cx,
  st: St,
  span: g.Span,
  subjects: List(g.Expression),
  clauses: List(g.Clause),
) -> R(Expr) {
  use #(subjects, st) <- result.try(infer_all(cx, st, subjects))
  let #(res, st) = fresh(st)
  use #(clauses, st) <- result.map(
    list.try_fold(clauses, #([], st), fn(acc, c) {
      let #(done, st) = acc
      use #(alts, st) <- result.try(
        list.try_fold(c.patterns, #([], st), fn(acc, alt) {
          use #(pats, st) <- result.map(
            list.try_fold(list.zip(alt, subjects), #([], acc.1), fn(acc, p) {
              use #(#(pat, bs), st) <- result.map(pattern(
                cx,
                acc.1,
                p.0,
                { p.1 }.ty,
              ))
              #(list.append(acc.0, [#(pat, bs)]), st)
            }),
          )
          #(list.append(acc.0, [pats]), st)
        }),
      )
      let bindings = case alts {
        [first, ..] -> list.flat_map(first, fn(p) { p.1 })
        [] -> []
      }
      let inner = bind(cx, bindings)
      use #(guard, st) <- result.try(case c.guard {
        Some(gd) ->
          check(inner, st, gd, bool_ty)
          |> result.map(fn(r) { #(Some(r.0), r.1) })
        None -> Ok(#(None, st))
      })
      use #(b, st) <- result.map(check(inner, st, c.body, res))
      let alternatives = list.map(alts, list.map(_, fn(p) { p.0 }))
      #(list.append(done, [ir.Clause(alternatives, guard, b)]), st)
    }),
  )
  #(node(cx, span, res, ir.Case(subjects, clauses)), st)
}

fn pattern(
  cx: Cx,
  st: St,
  p: g.Pattern,
  t: Ty,
) -> R(#(Pat, List(#(String, Ty)))) {
  let pat = fn(span: g.Span, n) { Pat(at(cx, span), t, n) }
  let restrict = fn(kind, span, message) {
    Error(finding(cx.m, kind, span, message))
  }
  case p {
    g.PatternInt(span, text) -> {
      use st <- result.map(expect(cx, st, span, int_ty, t))
      #(#(pat(span, ir.PInt(text)), []), st)
    }
    g.PatternString(span, text) -> {
      use st <- result.map(expect(cx, st, span, str_ty, t))
      #(#(pat(span, ir.PStr("\"" <> text <> "\"")), []), st)
    }
    g.PatternFloat(span, _) -> restrict(Float, span, "Float pattern: use Int")
    g.PatternDiscard(span, name) ->
      Ok(#(#(pat(span, ir.PDiscard("_" <> name)), []), st))
    g.PatternVariable(span, name) ->
      Ok(#(#(pat(span, ir.PVar(name)), [#(name, t)]), st))
    g.PatternList(span, ..) ->
      restrict(
        ListPattern,
        span,
        "list pattern: a spec reads lists through tazuna's functions",
      )
    g.PatternConcatenate(span, ..) ->
      restrict(
        StringPrefixPattern,
        span,
        "string prefix pattern is outside the spec subset",
      )
    g.PatternBitString(span, ..) ->
      restrict(BitArray, span, "bit array pattern is outside the spec subset")
    g.PatternAssignment(span, inner, name) -> {
      use #(#(q, bs), st) <- result.map(pattern(cx, st, inner, t))
      #(#(pat(span, ir.PAs(q, name)), list.append(bs, [#(name, t)])), st)
    }
    g.PatternTuple(span, items) -> {
      let #(ts, st) = fresh_many(st, list.length(items))
      use st <- result.try(expect(cx, st, span, Tuple(ts), t))
      use #(qs, st) <- result.map(
        list.try_fold(list.zip(items, ts), #([], st), fn(acc, p) {
          use #(q, st) <- result.map(pattern(cx, acc.1, p.0, p.1))
          #(list.append(acc.0, [q]), st)
        }),
      )
      #(
        #(
          pat(span, ir.PTuple(list.map(qs, fn(q) { q.0 }))),
          list.flat_map(qs, fn(q) { q.1 }),
        ),
        st,
      )
    }
    g.PatternVariant(span, module, ctor, args, spread) -> {
      use #(_, gl) <- result.try(value_global(cx, span, module, ctor))
      case gl {
        GCtor(type_, variant) -> {
          let #(ct, fields, _, st) = constructor_type(cx, st, type_, variant)
          use st <- result.try(expect(cx, st, span, ct, t))
          let labelled =
            list.filter_map(args, fn(a) {
              case a {
                g.LabelledField(l, _, _) | g.ShorthandField(l, _) -> Ok(l)
                g.UnlabelledField(_) -> Error(Nil)
              }
            })
          let open =
            list.filter(fields, fn(f) {
              case f.0 {
                Some(l) -> !list.contains(labelled, l)
                None -> True
              }
            })
          use #(qs, _, st) <- result.map(
            list.try_fold(args, #([], open, st), fn(acc, a) {
              let #(qs, open, st) = acc
              case a {
                g.UnlabelledField(q) ->
                  case open {
                    [#(_, ft), ..open] -> {
                      use #(r, st) <- result.map(pattern(cx, st, q, ft))
                      #(
                        list.append(qs, [#(ir.PPositional(r.0), r.1)]),
                        open,
                        st,
                      )
                    }
                    [] ->
                      Error(bug(
                        cx.m,
                        span,
                        "too many fields in pattern " <> ctor,
                      ))
                  }
                g.LabelledField(l, _, q) -> {
                  let assert Ok(ft) = list.key_find(fields, Some(l))
                  use #(r, st) <- result.map(pattern(cx, st, q, ft))
                  #(list.append(qs, [#(ir.PLabelled(l, r.0), r.1)]), open, st)
                }
                g.ShorthandField(l, lspan) -> {
                  let assert Ok(ft) = list.key_find(fields, Some(l))
                  Ok(#(
                    list.append(qs, [
                      #(ir.PShorthand(at(cx, lspan), l), [#(l, ft)]),
                    ]),
                    open,
                    st,
                  ))
                }
              }
            }),
          )
          #(
            #(
              pat(
                span,
                ir.PCtor(type_, variant, list.map(qs, fn(q) { q.0 }), spread),
              ),
              list.flat_map(qs, fn(q) { q.1 }),
            ),
            st,
          )
        }
        _ -> Error(bug(cx.m, span, ctor <> " is not a constructor"))
      }
    }
  }
}
