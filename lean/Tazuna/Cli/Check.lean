import Tazuna.Cli.Kind
import Tazuna.Ir.Load
import Tazuna.Smt.Checked

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

/-- The spec with what check established of it (`Smt.check_ok`), when the IR at `path` loads, `root` is its root, and
the structure breaks no rule; otherwise the lines are printed and the result is the exit code. -/
def loadSpec (root path : String) : IO (Except UInt32 Smt.CheckedSpec) := do
  let text ← IO.FS.readFile path
  let result : Except Ir.Elab.LoadError (Ir.Program (.fn [] Ir.Ty.spec)) := match Json.parse text with
    | .ok j => match j.getObjValAs? String "root" with
      | .ok r =>
        if r == root ++ ".spec" then Ir.Load.load (.fn [] Ir.Ty.spec) j
        else .error ⟨none, none, s!"the IR's root is {r}, but the launcher was asked for {root}"⟩
      | .error e => .error ⟨none, none, s!"no root: {e}"⟩
    | .error e => .error ⟨none, none, s!"not JSON: {e}"⟩
  match result with
  | .error e =>
    IO.println (invalidIrLine e).compress
    return .error 4
  | .ok p =>
    if hP : Ir.SitesUnique p.defs.sites then
      let captures := p.defs.sites.map fun ⟨Γ, _, s⟩ => (s.site, Γ)
      match h : Ir.SpecV.illegal p.types (p.eval ()) p.defs.handles captures with
      | [] =>
        if htys : (p.eval ()).services.all (·.stateTys p.defs.sites) = true then
          return .ok ⟨p, Smt.check_ok hP (Ir.Program.reach p () trivial) (by simpa using htys) h⟩
        else
          IO.println (invalidIrLine ⟨none, none,
            "a state, event or caller type has a type variable, an ADT 0 that is not Bool or a table with no plain key"⟩).compress
          return .error 4
      | findings =>
        for (k, message) in findings do
          printLine (.illegal k) [("message", Json.str message)]
        return .error 1
    else
      IO.println (invalidIrLine ⟨none, none, "two kept functions share a site id"⟩).compress
      return .error 4

/-- Loads the IR at `path`, which the launcher converted from the root module `root`, printing one line per finding;
returns the exit code. -/
def check (root path : String) : IO UInt32 := do
  match ← loadSpec root path with
  | .ok _ => return 0
  | .error code => return code

end Tazuna.Cli
