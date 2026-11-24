import Tazuna.Builtin
import Tazuna.Ir.Literal

def startMarker : String :=
  "// Built-ins begin. `lake exe gen-dsl --write ..` in lean/ writes them; do not edit.\n"

def endMarker : String :=
  "// Built-ins end.\n"

/-- The launcher converts with this copy of the DSL module, so it needs no file from the user's build directory. -/
def embedded (dsl : String) : String :=
  "//// The text of src/tazuna.gleam, which the converter reads as the tazuna\n" ++
  "//// module. `lake exe gen-dsl --write ..` in lean/ writes this file.\n\n" ++
  "pub const text =\n  " ++ Tazuna.Ir.Literal.printStr dsl ++ "\n"

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
  let dsl := before ++ startMarker ++ Tazuna.Builtin.gleamSection ++ endMarker ++ after
  let copy := embedded dsl
  let copyNow ← do if ← System.FilePath.pathExists copyPath then IO.FS.readFile copyPath else pure ""
  if text == dsl && copyNow == copy then return 0
  if write then
    IO.FS.writeFile path dsl
    IO.FS.writeFile copyPath copy
    return 0
  IO.eprintln s!"{path} or {copyPath} differs from Lean's table. Run `lake exe gen-dsl --write ..` in lean/."
  return 1
