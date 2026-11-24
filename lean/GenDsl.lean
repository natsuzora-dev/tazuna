import Tazuna.Ir.Builtin
import Tazuna.Ir.Literal

def startMarker : String :=
  "// Built-ins begin. `lake exe gen-dsl --write ..` in lean/ writes them; do not edit.\n"

def endMarker : String :=
  "// Built-ins end.\n"

open Tazuna.Ir

/-- A type as Gleam writes it inside the `tazuna` module, with `tvars` naming the type variables. -/
partial def gleamTy (tvars : List String) : Ty → String
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

def docLines (doc : String) : String := s!"/// {doc}\n"

def typeParams (ps : List String) : String := if ps.isEmpty then "" else "(" ++ ", ".intercalate ps ++ ")"

/-- A function whose body panics, laid out as `gleam format` lays it out: on one line when it fits in 80 columns,
else one parameter per line. -/
def gleamFn (p : Prim) : String :=
  let s := p.sig
  let params := s.params.map fun q =>
    (q.label.map (· ++ " ")).getD "" ++ "_" ++ q.name ++ ": " ++ gleamTy s.tvars q.ty
  let ret := gleamTy s.tvars s.ret
  let oneLine := s!"pub fn {s.name}(" ++ ", ".intercalate params ++ s!") -> {ret} \{"
  let head := if oneLine.length ≤ 80 then oneLine
    else s!"pub fn {s.name}(\n" ++ String.join (params.map (s!"  {·},\n")) ++ s!") -> {ret} \{"
  docLines s.doc ++ head ++ "\n  panic as \"tazuna's built-ins run only in the engine\"\n}\n"

/-- The declarations Lean owns, in the order the DSL module lists them. -/
def gleamSection : String :=
  let types := opaqueTypes.map fun t => docLines t.doc ++ s!"pub type {t.name}{typeParams t.params}\n"
  let preludeTypes := (prelude.filter (·.name.startsWith "tazuna.")).map fun d =>
    let n := (d.name.splitOn ".").getLast!
    if d.variants.isEmpty then s!"pub type {n}\n"
    else s!"pub type {n} \{\n" ++ String.join (d.variants.map (s!"  {·.name}\n")) ++ "}\n"
  let aliases := builtinAliases.map fun (a, doc) =>
    let body := match a.ty with
      | .con n [] => n
      | _ => "?"
    docLines doc ++ s!"pub type {(a.name.splitOn ".").getLast!} =\n  {body}\n"
  "\n".intercalate (types ++ preludeTypes ++ aliases ++ Prim.all.map gleamFn)

/-- The launcher converts with this copy of the DSL module, so it needs no file from the user's build directory. -/
def embedded (dsl : String) : String :=
  "//// The text of src/tazuna.gleam, which the converter reads as the tazuna\n" ++
  "//// module. `lake exe gen-dsl --write ..` in lean/ writes this file.\n\n" ++
  "pub const text =\n  " ++ Tazuna.Ir.Literal.printStr dsl ++ "\n\n" ++
  "/// The functions of the module that are built-ins; a spec calls no other.\n" ++
  "pub const builtins = [\n" ++ String.join (Prim.all.map fun p => s!"  {Tazuna.Ir.Literal.printStr p.sig.name},\n") ++ "]\n\n" ++
  "/// The built-ins whose type variables, by name, must be types `==` works on.\n" ++
  "pub const needs_equality = [\n" ++
  String.join ((Prim.all.filter (!·.sig.needsEq.isEmpty)).map fun p =>
    let vs := p.sig.needsEq.map fun k => Tazuna.Ir.Literal.printStr (p.sig.tvars[k]?.getD "")
    s!"  #({Tazuna.Ir.Literal.printStr p.sig.name}, [" ++ ", ".intercalate vs ++ "]),\n") ++ "]\n"

/-- Checks that the built-in section of the DSL module matches Lean's table and that the launcher's copy of the module
is current, or rewrites both with `--write`. -/
def main (args : List String) : IO UInt32 := do
  let parsed : Option (Bool × String) := match args with
    | ["--write", root] => some (true, root)
    | [root] => some (false, root)
    | _ => none
  let some (write, root) := parsed
    | do IO.eprintln "usage: gen-dsl [--write] <repository root>"; return 3
  let path := root ++ "/gleam/src/tazuna.gleam"
  let copyPath := root ++ "/gleam/src/tazuna/internal/dsl_source.gleam"
  let text ← IO.FS.readFile path
  let some (before, after) := match text.splitOn startMarker with
      | [before, rest] => match rest.splitOn endMarker with
        | [_, after] => some (before, after)
        | _ => none
      | _ => none
    | do IO.eprintln s!"{path} needs one line each of:\n{startMarker}{endMarker}"; return 1
  let dsl := before ++ startMarker ++ gleamSection ++ endMarker ++ after
  let copy := embedded dsl
  let copyNow ← do if ← System.FilePath.pathExists copyPath then IO.FS.readFile copyPath else pure ""
  if text == dsl && copyNow == copy then return 0
  if write then
    IO.FS.writeFile path dsl
    IO.FS.writeFile copyPath copy
    return 0
  IO.eprintln s!"{path} or {copyPath} differs from Lean's table. Run `lake exe gen-dsl --write ..` in lean/."
  return 1
