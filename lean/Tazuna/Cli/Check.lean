import Tazuna.Cli.Kind
import Tazuna.Ir.Load
import Tazuna.Semantics.Eval

/-! The `check` command: it loads the IR, evaluates the spec and reports each broken structure rule. -/

namespace Tazuna.Cli

open Lean (Json)

def invalidIrLine (e : Ir.Elab.LoadError) : Json :=
  Json.mkObj ([("kind", Json.str Kind.invalidIr.name)] ++ (e.file.map fun f => ("file", Json.str f)).toList ++
    (e.pos.map fun p => [("line", Json.num p.line), ("col", Json.num p.col)]).getD [] ++
    [("message", Json.str e.message)])

/-- Loads the IR at `path`, which the launcher converted from the root module `root`, printing one line per finding;
returns the exit code. -/
def check (root path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let result := match Json.parse text with
    | .ok j => match j.getObjValAs? String "root" with
      | .ok r =>
        if r == root ++ ".spec" then (Ir.Load.load (.fn [] Ir.Ty.spec) j).map fun (p : Ir.Program (.fn [] Ir.Ty.spec)) => Ir.SpecV.illegal p.types (p.eval ())
        else .error ⟨none, none, s!"the IR's root is {r}, but the launcher was asked for {root}"⟩
      | .error e => .error ⟨none, none, s!"no root: {e}"⟩
    | .error e => .error ⟨none, none, s!"not JSON: {e}"⟩
  match result with
  | .ok [] => return 0
  | .ok findings =>
    for (k, message) in findings do
      IO.println (Json.mkObj [("kind", Json.str (Kind.illegal k).name), ("message", Json.str message)]).compress
    return 1
  | .error e =>
    IO.println (invalidIrLine e).compress
    return 4

end Tazuna.Cli
