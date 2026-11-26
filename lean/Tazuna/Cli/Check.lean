import Tazuna.Cli.Kind
import Tazuna.Ir.Load
import Tazuna.Smt.Checked

/-! The `check` command: it loads the IR, evaluates the spec and reports each broken structure rule. Every other
command runs it first. -/

namespace Tazuna.Cli

open Lean (Json)

/-- A command: it prints its lines and keeps the worst outcome they give, which is its exit code (`Kind.exit`). -/
abbrev Cmd := ReaderT (IO.Ref Exit) IO

/-- Prints one line of the kind with its fields. -/
def printLine (kind : Kind) (fields : List (String × Json)) : Cmd Unit := do
  IO.println (Json.mkObj (("kind", Json.str kind.name) :: fields)).compress
  (← read).modify (·.max kind.exit)

/-- Runs a command; its exit code. An error the system raises (a file that does not read, a program that does not
start) is a Usage.system line: none of the engine's own checks throws. -/
def Cmd.exitCode (c : Cmd Unit) : IO UInt32 := do
  let worst ← IO.mkRef Exit.ok
  try c.run worst
  catch e => (printLine (.usage .system) [("message", Json.str (toString e))]).run worst
  return (← worst.get).code

/-- Prints the engine's bug: a state its proofs rule out. The command stops after it. -/
def internal (message : String) : Cmd Unit := printLine (.internal .engine) [("message", Json.str message)]

-- An error without a position has no line or column fields.
set_option linter.tazuna.silentDefault false in
def invalidIr (e : Ir.Elab.LoadError) : Cmd Unit :=
  printLine (.internal .invalidIr) ((e.file.map fun f => ("file", Json.str f)).toList ++
    (e.pos.map fun p => [("line", Json.num p.line), ("col", Json.num p.col)]).getD [] ++
    [("message", Json.str e.message)])

/-- The spec with what check established of it (`Smt.check_ok`), when the IR at `path` loads, `root` is its root, and
the structure breaks no rule; otherwise none, and the lines are printed. -/
def loadSpec (root path : String) : Cmd (Option Smt.CheckedSpec) := do
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
    invalidIr e
    return none
  | .ok p =>
    if hP : Ir.SitesUnique p.defs.sites then
      let captures := p.defs.sites.map fun ⟨Γ, _, s⟩ => (s.site, Γ)
      match h : Ir.SpecV.illegal p.types (p.eval ()) p.defs.handles captures Ir.ServiceV.sentHandles with
      | [] =>
        if htys : (p.eval ()).services.all (·.stateTys) = true then
          if hw : (p.eval ()).services.all (·.wireOk p.types) = true then
            return some ⟨p, Smt.check_ok hP (Ir.Program.reach p () trivial) (by simpa using htys) (by simpa using hw) h,
              Smt.handles_ok h⟩
          else
            invalidIr ⟨none, none,
              "a wire type has a type variable, a variant without a key per field, or no canonical order"⟩
            return none
        else
          invalidIr ⟨none, none,
            "a state, event or caller type has a type variable, an ADT 0 that is not Bool or a table with no plain key"⟩
          return none
      | findings =>
        for (k, message) in findings do
          printLine (.illegal k) [("message", Json.str message)]
        return none
    else
      invalidIr ⟨none, none, "two kept functions share a site id"⟩
      return none

/-- Loads the IR at `path`, which the launcher converted from the root module `root`, printing one line per
finding, or one line per service when there is none. -/
def check (root path : String) : Cmd Unit := do
  if let some c ← loadSpec root path then
    c.spec.services.forM fun v => printLine .checkPassed [("service", Json.str v.name)]

end Tazuna.Cli
