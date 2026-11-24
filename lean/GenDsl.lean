import Tazuna.Builtin

def startMarker : String :=
  "// Built-ins begin. `lake exe gen-dsl --write ..` in lean/ writes them; do not edit.\n"

def endMarker : String :=
  "// Built-ins end.\n"

/-- Checks that the built-in section of the DSL module matches Lean's table, or rewrites it with `--write`. -/
def main (args : List String) : IO UInt32 := do
  let parsed : Option (Bool × String) := match args with
    | ["--write", root] => some (true, root)
    | [root] => some (false, root)
    | _ => none
  let some (write, root) := parsed
    | do IO.eprintln "usage: gen-dsl [--write] <repository root>"; return 3
  let path := root ++ "/gleam/src/tazuna.gleam"
  let text ← IO.FS.readFile path
  let some (before, current, after) := match text.splitOn startMarker with
      | [before, rest] => match rest.splitOn endMarker with
        | [current, after] => some (before, current, after)
        | _ => none
      | _ => none
    | do IO.eprintln s!"{path} needs one line each of:\n{startMarker}{endMarker}"; return 1
  if current == Tazuna.Builtin.gleamSection then return 0
  if write then
    IO.FS.writeFile path (before ++ startMarker ++ Tazuna.Builtin.gleamSection ++ endMarker ++ after)
    return 0
  IO.eprintln s!"The built-ins in {path} differ from Lean's table. Run `lake exe gen-dsl --write ..` in lean/."
  return 1
