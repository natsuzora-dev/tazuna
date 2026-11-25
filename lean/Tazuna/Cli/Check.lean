import Tazuna.Cli.Kind
import Tazuna.Ir.Load
import Tazuna.Semantics.Reach

/-! The `check` command: it loads the IR, evaluates the spec and reports each broken structure rule. Every other
command runs it first. -/

namespace Tazuna.Cli

open Lean (Json)

-- An error without a position has no line or column fields.
set_option linter.tazuna.silentDefault false in
def invalidIrLine (e : Ir.Elab.LoadError) : Json :=
  Json.mkObj ([("kind", Json.str Kind.invalidIr.name)] ++ (e.file.map fun f => ("file", Json.str f)).toList ++
    (e.pos.map fun p => [("line", Json.num p.line), ("col", Json.num p.col)]).getD [] ++
    [("message", Json.str e.message)])

def printLine (kind : Kind) (fields : List (String × Json)) : IO Unit :=
  IO.println (Json.mkObj (("kind", Json.str kind.name) :: fields)).compress

/-- The spec's user types and structure, when the IR at `path` loads, `root` is its root, and the structure breaks no
rule; otherwise the lines are printed and the result is the exit code. -/
def loadSpec (root path : String) : IO (Except UInt32 (List Ir.TypeDecl × Ir.SpecV)) := do
  let text ← IO.FS.readFile path
  let result := match Json.parse text with
    | .ok j => match j.getObjValAs? String "root" with
      | .ok r =>
        if r == root ++ ".spec" then
          (Ir.Load.load (.fn [] Ir.Ty.spec) j).bind fun (p : Ir.Program (.fn [] Ir.Ty.spec)) =>
            if Ir.SitesUnique p.defs.sites then .ok (p.types, p.eval (), p.defs.handles)
            else .error ⟨none, none, "two kept functions share a site id"⟩
        else .error ⟨none, none, s!"the IR's root is {r}, but the launcher was asked for {root}"⟩
      | .error e => .error ⟨none, none, s!"no root: {e}"⟩
    | .error e => .error ⟨none, none, s!"not JSON: {e}"⟩
  match result with
  | .error e =>
    IO.println (invalidIrLine e).compress
    return .error 4
  | .ok (types, spec, handles) =>
    match Ir.SpecV.illegal types spec handles with
    | [] => return .ok (types, spec)
    | findings =>
      for (k, message) in findings do
        printLine (.illegal k) [("message", Json.str message)]
      return .error 1

/-- Loads the IR at `path`, which the launcher converted from the root module `root`, printing one line per finding;
returns the exit code. -/
def check (root path : String) : IO UInt32 := do
  match ← loadSpec root path with
  | .ok _ => return 0
  | .error code => return code

end Tazuna.Cli
