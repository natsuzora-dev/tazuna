import Tazuna.Cli.Kind
import Tazuna.Ir.Load

/-! The `check` command. For now it loads the IR; structure rules join it in later units. -/

namespace Tazuna.Cli

open Lean (Json)

def invalidIrLine (e : Ir.Elab.LoadError) : Json :=
  Json.mkObj ([("kind", Json.str Kind.invalidIr.name)] ++ (e.file.map fun f => ("file", Json.str f)).toList ++
    (e.pos.map fun p => [("line", Json.num p.line), ("col", Json.num p.col)]).getD [] ++
    [("message", Json.str e.message)])

/-- Loads the IR at `path`, printing one line per finding; returns the exit code. -/
def check (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let result := match Json.parse text with
    | .ok j => Ir.Load.load (.fn [] Ir.Ty.spec) j
    | .error e => .error ⟨none, none, s!"not JSON: {e}"⟩
  match result with
  | .ok _ => return 0
  | .error e =>
    IO.println (invalidIrLine e).compress
    return 4

end Tazuna.Cli
