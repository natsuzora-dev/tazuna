import Tazuna.Ir.Builtin
import Tazuna.Ir.Literal
import Tazuna.Cli.Kind

-- Generated Gleam text: an unnamed type or label prints a placeholder.
set_option linter.tazuna.silentDefault false

/-- A module of the `tazuna` package that gen-dsl writes: its name, its path under gleam/src, what it is, and the
lines before its declarations (imports and, for `tazuna`, the launcher's entry point). -/
structure DslModule where
  name : String
  path : String
  doc : String
  head : String

def dslModules : List DslModule :=
  [ ⟨"tazuna", "tazuna.gleam",
      "The tazuna DSL: a spec's services, the externals they talk to, and their scenarios.",
      "import gleam/option.{type Option}\n" ++
      "import tazuna/bag.{type Bag}\n" ++
      "import tazuna/instant.{type Instant}\n" ++
      "import tazuna/internal/launch\n" ++
      "import tazuna/table.{type Table}\n\n" ++
      "/// `gleam run -m tazuna -- <command> <root> [...]` checks the spec whose\n" ++
      "/// root module is `src/<root>.gleam`.\n" ++
      "pub fn main() -> Nil {\n" ++
      "  launch.main()\n" ++
      "}\n\n"⟩,
    ⟨"tazuna/bag", "tazuna/bag.gleam", "Bags: multisets, whose items have no order.", ""⟩,
    ⟨"tazuna/table", "tazuna/table.gleam", "Tables: finite maps from keys to values.",
      "import gleam/option.{type Option}\nimport tazuna/bag.{type Bag}\n\n"⟩,
    ⟨"tazuna/date", "tazuna/date.gleam", "Dates: days without a calendar.", ""⟩,
    ⟨"tazuna/instant", "tazuna/instant.gleam", "Instants: points in time a spec cannot write, only move and compare.", ""⟩ ]

def moduleHead (m : DslModule) : String :=
  s!"//// {m.doc}\n" ++
  "////\n" ++
  "//// Lean gives a spec its meaning, so the bodies here only let a spec\n" ++
  "//// compile; Gleam never runs them.\n" ++
  "////\n" ++
  "//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`\n" ++
  "//// in lean/. DO NOT EDIT.\n\n" ++ m.head

open Tazuna Tazuna.Ir

/-- A type as Gleam writes it inside the `tazuna` module, with `tvars` naming the type variables and `int` the name
written for `Int`, so a time alias reaches an Int inside an `Option` or a function's result. -/
partial def gleamTy (tvars : List String) (int : String) : Ty → String
  | .list (.tuple [.str, .adt 0 [] _]) => "Rules"
  | .int => int
  | .str => "String"
  | .list t => s!"List({gleamTy tvars int t})"
  | .tuple ts => "#(" ++ ", ".intercalate (ts.map (gleamTy tvars int)) ++ ")"
  | .fn ps r => "fn(" ++ ", ".intercalate (ps.map (gleamTy tvars int)) ++ ") -> " ++ gleamTy tvars int r
  | .adt i args _ =>
    let full := (prelude[i]?.map (·.name)).getD s!"type{i}"
    let n := (full.splitOn ".").getLast!
    if args.isEmpty then n else n ++ "(" ++ ", ".intercalate (args.map (gleamTy tvars int)) ++ ")"
  | .param k => tvars[k]?.getD s!"t{k}"
  | .bag t => s!"Bag({gleamTy tvars int t})"
  | .table k v => s!"Table({gleamTy tvars int k}, {gleamTy tvars int v})"
  | .point .day => "Date"
  | .point .ms => "Instant"
  | .id => "Id"
  | .dsl .closure [t] | .dsl .effectClosure [t] => gleamTy tvars int t
  | .dsl k args =>
    let n := k.name
    if args.isEmpty then n else n ++ "(" ++ ", ".intercalate (args.map (gleamTy tvars int)) ++ ")"

/-- The time alias `timeAliases` names for the field or parameter `label` of `owner`, else `Int`. -/
def intName (owner : String) (label : Option String) : String :=
  ((label.bind fun l => timeAliases.find? fun (o, l', _) => o == owner && l' == l).map (·.2.2)).getD "Int"

/-- The type of the field or parameter `label` of `owner`, with its Ints written as the time alias it has. -/
def labelledTy (owner : String) (tvars : List String) (label : Option String) (t : Ty) : String :=
  gleamTy tvars (intName owner label) t

/-- A type as an alias's body writes it. -/
partial def surfaceTy : Surface.STy → String
  | .con n args => (n.splitOn ".").getLast! ++ (if args.isEmpty then "" else "(" ++ ", ".intercalate (args.map surfaceTy) ++ ")")
  | .tuple ts => "#(" ++ ", ".intercalate (ts.map surfaceTy) ++ ")"
  | .fn ps r => "fn(" ++ ", ".intercalate (ps.map surfaceTy) ++ ") -> " ++ surfaceTy r
  | .var n | .hole n => n

def docLines (doc : String) : String := s!"/// {doc}\n"

def typeParams (ps : List String) : String := if ps.isEmpty then "" else "(" ++ ", ".intercalate ps ++ ")"

/-- A function whose body panics, laid out as `gleam format` lays it out: on one line when it fits in 80 columns,
else one parameter per line. -/
def gleamFn (p : Prim) : String :=
  let s := p.sig
  let params := s.params.map fun q =>
    (q.label.map (· ++ " ")).getD "" ++ "_" ++ q.name ++ ": " ++ labelledTy s.name s.tvars q.label q.ty
  let ret := gleamTy s.tvars "Int" s.ret
  let oneLine := s!"pub fn {s.name}(" ++ ", ".intercalate params ++ s!") -> {ret} \{"
  let head := if oneLine.length ≤ 80 then oneLine
    else
      let line (q : PrimParam) : String :=
        let pre := (q.label.map (· ++ " ")).getD "" ++ "_" ++ q.name ++ ": "
        let whole := s!"  {pre}{labelledTy s.name s.tvars q.label q.ty},\n"
        match q.ty with
        | .fn ps r | .dsl .closure [.fn ps r] | .dsl .effectClosure [.fn ps r] =>
          if whole.length ≤ 81 then whole
          else
            let int := intName s.name q.label
            s!"  {pre}fn(" ++ ", ".intercalate (ps.map (gleamTy s.tvars int)) ++ s!") ->\n    {gleamTy s.tvars int r},\n"
        | _ => whole
      s!"pub fn {s.name}(\n" ++ String.join (s.params.map line) ++ s!") -> {ret} \{"
  docLines s.doc ++ head ++ "\n  panic as \"tazuna's built-ins run only in the engine\"\n}\n"

/-- The declarations Lean owns in the module `m`, in the order the module lists them. -/
def gleamSection (m : String) : String :=
  let types := (opaqueTypes.filter (·.module == m)).map fun t =>
    docLines t.doc ++ s!"pub type {t.name}{typeParams t.params}\n"
  let preludeTypes := (prelude.filter (·.name.startsWith (m ++ "."))).map fun d =>
    let n := (d.name.splitOn ".").getLast!
    let variant (v : Variant) : String :=
      if v.fields.isEmpty then s!"  {v.name}\n" else
      let fs := v.fields.map fun f => (f.label.map (· ++ ": ")).getD "" ++ labelledTy d.name d.params f.label f.ty
      let one := s!"  {v.name}(" ++ ", ".intercalate fs ++ ")"
      if one.length ≤ 80 then one ++ "\n"
      else s!"  {v.name}(\n" ++ String.join (fs.map (s!"    {·},\n")) ++ "  )\n"
    let doc := ((preludeDocs.lookup d.name).map docLines).getD ""
    if d.variants.isEmpty then doc ++ s!"pub type {n}{typeParams d.params}\n" else
    doc ++ s!"pub type {n}{typeParams d.params} \{\n" ++ String.join (d.variants.map variant) ++ "}\n"
  let aliases := (builtinAliases.filter (·.1.name.startsWith (m ++ "."))).map fun (a, doc) =>
    let body := surfaceTy a.ty
    docLines doc ++ s!"pub type {(a.name.splitOn ".").getLast!} =\n  {body}\n"
  "\n".intercalate (types ++ preludeTypes ++ aliases ++ (Prim.all.filter (·.module == m)).map gleamFn)

def moduleText (m : DslModule) : String := moduleHead m ++ gleamSection m.name

/-- The launcher converts with this copy of the DSL modules, so it needs no file from the user's build directory. -/
def embedded : String :=
  "//// The text of the tazuna modules in src/, which the converter reads as\n" ++
  "//// those modules. `lake exe gen-dsl --write ..` in lean/ writes this file.\n\n" ++
  "/// Each module's name, path under src/ and text.\n" ++
  "pub const modules = [\n" ++
  String.join (dslModules.map fun m =>
    s!"  #(\n    {Tazuna.Ir.Literal.printStr m.name},\n    {Tazuna.Ir.Literal.printStr m.path},\n" ++
    s!"    {Tazuna.Ir.Literal.printStr (moduleText m)},\n  ),\n") ++ "]\n\n" ++
  "/// The functions of the modules that are built-ins; a spec calls no other.\n" ++
  "pub const builtins = [\n" ++ String.join (Prim.all.map fun p => s!"  {Tazuna.Ir.Literal.printStr p.global},\n") ++ "]\n\n" ++
  "/// The built-ins whose type variables, by name, must be types `==` works on.\n" ++
  "pub const needs_equality = [\n" ++
  String.join ((Prim.all.filter (!·.sig.needsEq.isEmpty)).map fun p =>
    let vs := p.sig.needsEq.map fun k => Tazuna.Ir.Literal.printStr (p.sig.tvars[k]?.getD "")
    s!"  #({Tazuna.Ir.Literal.printStr p.global}, [" ++ ", ".intercalate vs ++ "]),\n") ++ "]\n\n" ++
  "/// The function parameters built-ins keep as closure records: the\n" ++
  "/// built-in, the parameter's position and its label.\n" ++
  "pub const kept = [\n" ++
  String.join (Prim.all.flatMap fun p => (p.sig.params.zipIdx.filter (·.1.ty matches .dsl .closure _ | .dsl .effectClosure _)).map
    fun (q, k) => s!"  #({Tazuna.Ir.Literal.printStr p.global}, {k}, {Tazuna.Ir.Literal.printStr (q.label.getD q.name)}),\n") ++
  "]\n\n" ++
  "/// The types whose values are structure values, not data.\n" ++
  "pub const structure_types = [\n" ++
  String.join ((Dsl.all.filter fun k => k != .fresh && !k.kept).map fun k =>
    s!"  {Tazuna.Ir.Literal.printStr ("tazuna." ++ k.name)},\n") ++ "]\n"

/-- The groups of kinds the launcher prints lines of, each with its kinds: the Gleam type of each group has a variant per
kind. -/
def launcherGroups : List (String × List Tazuna.Kind) :=
  [("Internal", InternalKind.all.map .internal), ("Usage", UsageKind.all.map .usage),
    ("Restricted", Restricted.all.map .restricted)]

/-- The Gleam variant of a kind: its name after the group, capitalized. -/
def variantOf (k : Tazuna.Kind) : String :=
  match k.name.splitOn "." with
  | [_, n] => n.capitalize
  | _ => k.name

/-- The launcher's copy of the kinds it prints, so its lines are named as Lean names them. -/
def kindModule : String :=
  let group (g : String × List Tazuna.Kind) : String :=
    s!"pub type {g.1} \{\n" ++ String.join (g.2.map (s!"  {variantOf ·}\n")) ++ "}\n\n"
  let arm (g : String) (k : Tazuna.Kind) : String :=
    s!"    {g}({variantOf k}) -> {Tazuna.Ir.Literal.printStr k.name}\n"
  let outcome (g : String) (k : Tazuna.Kind) : String :=
    s!"    {g}({variantOf k}) -> #({k.exit.rank}, {k.exit.code})\n"
  "//// The kinds of the lines the launcher prints itself, named as Lean names\n" ++
  "//// them (lean/Tazuna/Cli/Kind.lean, where `explain` reads what each means).\n" ++
  "////\n" ++
  "//// Generated by `lake exe gen-dsl --write ..` in lean/. DO NOT EDIT.\n\n" ++
  "import gleam/list\n\n" ++
  "pub type Kind {\n" ++ String.join (launcherGroups.map fun (g, _) => s!"  {g}({g})\n") ++ "}\n\n" ++
  String.join (launcherGroups.map group) ++
  "/// Every Restricted kind.\n" ++
  "pub const restricted = [\n" ++ String.join (Restricted.all.map fun k => s!"  {variantOf (.restricted k)},\n") ++
  "]\n\n" ++
  "/// The name a line of the kind carries as its `kind`.\n" ++
  "pub fn name(kind: Kind) -> String {\n  case kind {\n" ++
  String.join (launcherGroups.flatMap fun (g, ks) => ks.map (arm g)) ++ "  }\n}\n\n" ++
  "/// The exit code of a run that printed lines of these kinds: its worst line's.\n" ++
  "pub fn exit_code(kinds: List(Kind)) -> Int {\n" ++
  "  let #(_, code) =\n" ++
  "    list.fold(kinds, #(0, 0), fn(worst, kind) {\n" ++
  "      let next = outcome(kind)\n" ++
  "      case next.0 > worst.0 {\n        True -> next\n        False -> worst\n      }\n" ++
  "    })\n  code\n}\n\n" ++
  "/// A line's rank among outcomes, and its exit code.\n" ++
  "fn outcome(kind: Kind) -> #(Int, Int) {\n  case kind {\n" ++
  String.join (launcherGroups.flatMap fun (g, ks) => ks.map (outcome g)) ++ "  }\n}\n"

/-- Checks that the DSL modules match Lean's table and that the launcher's copy of them is current, or rewrites them
with `--write`. -/
def main (args : List String) : IO UInt32 := do
  let parsed : Option (Bool × String) := match args with
    | ["--write", root] => some (true, root)
    | [root] => some (false, root)
    | _ => none
  let some (write, root) := parsed
    | do IO.eprintln "usage: gen-dsl [--write] <repository root>"; return 3
  let files := (dslModules.map fun m => (root ++ "/gleam/src/" ++ m.path, moduleText m)) ++
    [(root ++ "/gleam/src/tazuna/internal/dsl_source.gleam", embedded),
      (root ++ "/gleam/src/tazuna/internal/kind.gleam", kindModule)]
  let read (p : String) : IO String := do if ← System.FilePath.pathExists p then IO.FS.readFile p else pure ""
  let stale ← files.filterM fun (path, text) => do pure ((← read path) != text)
  if stale.isEmpty then return 0
  if write then
    for (path, text) in stale do IO.FS.writeFile path text
    return 0
  IO.eprintln s!"{", ".intercalate (stale.map (·.1))} differ from Lean's table. Run `lake exe gen-dsl --write ..` in lean/."
  return 1
