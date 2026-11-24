//// How a module spells the globals it can see. A global's name is
//// `module.name`; the prelude's types are bare (`Int`, `Result`) and its
//// constructors live in `gleam` (`gleam.True`).

import glance as g
import gleam/list
import gleam/option.{None, Some}
import gleam/result
import gleam/string

pub type Imports {
  Imports(
    module: String,
    /// Module alias to module.
    aliases: List(#(String, String)),
    /// Unqualified value name to global.
    values: List(#(String, String)),
    /// Unqualified type name to global.
    types: List(#(String, String)),
  )
}

pub fn imports(module: String, defs: List(g.Definition(g.Import))) -> Imports {
  list.fold(defs, Imports(module, [], [], []), fn(acc, d) {
    let imp = d.definition
    let alias = case imp.alias {
      Some(g.Named(a)) -> [#(a, imp.module)]
      Some(g.Discarded(_)) -> []
      None -> [#(last_segment(imp.module), imp.module)]
    }
    let unqualified = fn(us: List(g.UnqualifiedImport)) {
      list.map(us, fn(u) {
        #(option.unwrap(u.alias, u.name), imp.module <> "." <> u.name)
      })
    }
    Imports(
      module:,
      aliases: list.append(acc.aliases, alias),
      values: list.append(acc.values, unqualified(imp.unqualified_values)),
      types: list.append(acc.types, unqualified(imp.unqualified_types)),
    )
  })
}

fn last_segment(module: String) -> String {
  string.split(module, "/") |> list.last |> result.unwrap(module)
}

/// Splits `a/b.name` into `#("a/b", "name")`; a bare name has module "".
pub fn split(global: String) -> #(String, String) {
  case string.split(global, ".") |> list.reverse {
    [name, ..rest] if rest != [] -> #(string.join(list.reverse(rest), "."), name)
    _ -> #("", global)
  }
}

pub fn spell_value(imports: Imports, global: String) -> Result(String, Nil) {
  spell(imports, imports.values, "gleam", global)
}

pub fn spell_type(imports: Imports, global: String) -> Result(String, Nil) {
  spell(imports, imports.types, "", global)
}

/// The unqualified spelling wins over the qualified one; the converter
/// refuses sources that write the qualified one instead.
fn spell(
  imports: Imports,
  unqualified: List(#(String, String)),
  prelude: String,
  global: String,
) -> Result(String, Nil) {
  let #(module, name) = split(global)
  case list.find(unqualified, fn(u) { u.1 == global }) {
    _ if module == imports.module -> Ok(name)
    Ok(#(local, _)) -> Ok(local)
    Error(_) if module == prelude -> Ok(name)
    Error(_) ->
      list.find(imports.aliases, fn(a) { a.1 == module })
      |> result.map(fn(a) { a.0 <> "." <> name })
  }
}

/// The global naming a constructor of `type_`.
pub fn constructor(type_: String, variant: String) -> String {
  case split(type_) {
    #("", _) -> "gleam." <> variant
    #(module, _) -> module <> "." <> variant
  }
}
