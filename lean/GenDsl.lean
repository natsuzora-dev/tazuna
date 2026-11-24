import Tazuna.Ir.Builtin
import Tazuna.Ir.Literal

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
    ⟨"tazuna/date", "tazuna/date.gleam", "Dates: days without a calendar.", ""⟩ ]

def moduleHead (m : DslModule) : String :=
  s!"//// {m.doc}\n" ++
  "////\n" ++
  "//// Lean gives a spec its meaning, so the bodies here only let a spec\n" ++
  "//// compile; Gleam never runs them.\n" ++
  "////\n" ++
  "//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`\n" ++
  "//// in lean/. DO NOT EDIT.\n\n" ++ m.head

open Tazuna.Ir

/-- A type as Gleam writes it inside the `tazuna` module, with `tvars` naming the type variables. -/
partial def gleamTy (tvars : List String) : Ty → String
  | .list (.tuple [.str, .adt 0 [] _]) => "Rules"
  | .int => "Int"
  | .str => "String"
  | .list t => s!"List({gleamTy tvars t})"
  | .tuple ts => "#(" ++ ", ".intercalate (ts.map (gleamTy tvars)) ++ ")"
  | .fn ps r => "fn(" ++ ", ".intercalate (ps.map (gleamTy tvars)) ++ ") -> " ++ gleamTy tvars r
  | .adt i args _ =>
    let full := (prelude[i]?.map (·.name)).getD s!"type{i}"
    let n := (full.splitOn ".").getLast!
    if args.isEmpty then n else n ++ "(" ++ ", ".intercalate (args.map (gleamTy tvars)) ++ ")"
  | .param k => tvars[k]?.getD s!"t{k}"
  | .bag t => s!"Bag({gleamTy tvars t})"
  | .table k v => s!"Table({gleamTy tvars k}, {gleamTy tvars v})"
  | .date => "Date"
  | .id => "Id"
  | .dsl .closure [t] => gleamTy tvars t
  | .dsl k args =>
    let n := k.name
    if args.isEmpty then n else n ++ "(" ++ ", ".intercalate (args.map (gleamTy tvars)) ++ ")"

/-- The type of the field or parameter `label` of `owner`: a time alias when `timeAliases` names one. -/
def labelledTy (owner : String) (tvars : List String) (label : Option String) (t : Ty) : String :=
  match label.bind fun l => (timeAliases.find? fun (o, l', _) => o == owner && l' == l).map (·.2.2) with
  | some alias => alias
  | none => gleamTy tvars t

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
  let ret := gleamTy s.tvars s.ret
  let oneLine := s!"pub fn {s.name}(" ++ ", ".intercalate params ++ s!") -> {ret} \{"
  let head := if oneLine.length ≤ 80 then oneLine
    else
      let line (q : PrimParam) : String :=
        let pre := (q.label.map (· ++ " ")).getD "" ++ "_" ++ q.name ++ ": "
        let whole := s!"  {pre}{labelledTy s.name s.tvars q.label q.ty},\n"
        match q.ty with
        | .fn ps r | .dsl .closure [.fn ps r] =>
          if whole.length ≤ 81 then whole
          else s!"  {pre}fn(" ++ ", ".intercalate (ps.map (gleamTy s.tvars)) ++ s!") ->\n    {gleamTy s.tvars r},\n"
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
    s!"pub type {n}{typeParams d.params} \{\n" ++ String.join (d.variants.map variant) ++ "}\n"
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
  String.join (Prim.all.flatMap fun p => (p.sig.params.zipIdx.filter (·.1.ty matches .dsl .closure _)).map
    fun (q, k) => s!"  #({Tazuna.Ir.Literal.printStr p.global}, {k}, {Tazuna.Ir.Literal.printStr (q.label.getD q.name)}),\n") ++
  "]\n\n" ++
  "/// The types whose values are structure values, not data.\n" ++
  "pub const structure_types = [\n" ++
  String.join ((Dsl.all.filter fun k => k != .fresh && k != .closure).map fun k =>
    s!"  {Tazuna.Ir.Literal.printStr ("tazuna." ++ k.name)},\n") ++ "]\n"

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
    [(root ++ "/gleam/src/tazuna/internal/dsl_source.gleam", embedded)]
  let read (p : String) : IO String := do if ← System.FilePath.pathExists p then IO.FS.readFile p else pure ""
  let stale ← files.filterM fun (path, text) => do pure ((← read path) != text)
  if stale.isEmpty then return 0
  if write then
    for (path, text) in stale do IO.FS.writeFile path text
    return 0
  IO.eprintln s!"{", ".intercalate (stale.map (·.1))} differ from Lean's table. Run `lake exe gen-dsl --write ..` in lean/."
  return 1
