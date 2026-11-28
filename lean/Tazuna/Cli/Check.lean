import Tazuna.Cli.Kind
import Tazuna.Ir.Load
import Tazuna.Smt.Checked
import Tazuna.Semantics.Equivariance

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

/-- The IR at `path` as JSON, when it reads and its root module is `root`; otherwise none, and the line is printed. -/
def readIr (root path : String) : Cmd (Option Json) := do
  let text ← IO.FS.readFile path
  let result : Except Ir.Elab.LoadError Json := match Json.parse text with
    | .ok j => match j.getObjValAs? String "root" with
      | .ok r =>
        if r == root ++ ".spec" then .ok j
        else .error ⟨none, none, s!"the IR's root is {r}, but the launcher was asked for {root}"⟩
      | .error e => .error ⟨none, none, s!"no root: {e}"⟩
    | .error e => .error ⟨none, none, s!"not JSON: {e}"⟩
  match result with
  | .ok j => return some j
  | .error e =>
    invalidIr e
    return none

/-- The checked spec `s` of the program `p`, when `s` breaks no structure rule and the model `m` (none for `spec()`)
none of its own; otherwise none, and one line per finding is printed, each prefixed by `context`. Its services must
reach only the program's sites and relate to themselves, as `p`'s root gives them. -/
def checkedOf {r : Ir.Ty} (p : Ir.Program r) (s : Ir.SpecV) (m : Option Ir.ModelV) (context : String)
    (hreach : ∀ v ∈ s.services, v.Reach p.defs.sites p.defs.effectSites)
    (hself : ∀ R, ∀ v ∈ s.services, v.Self R) : Cmd (Option Smt.CheckedSpec) := do
  let report (findings : List (Ir.Illegal × String)) : Cmd Unit :=
    for (k, message) in findings do
      printLine (.illegal k) [("message", Json.str (context ++ message))]
  if hP : Ir.SitesUnique p.defs.sites then
    let captures := p.defs.sites.map fun ⟨Γ, _, s⟩ => (s.site, Γ)
    -- No proof reads the callers rule: a send it misses is still a fault, `Fault.invalidEffect`.
    let callerFindings := s.services.flatMap Ir.ServiceV.callerRules
    let modelFindings := match m with
      | some m => m.illegal p.types
      | none => []
    match h : Ir.SpecV.illegal p.types s p.defs.handles captures Ir.ServiceV.sentHandles with
    | [] =>
      if !callerFindings.isEmpty || !modelFindings.isEmpty then
        report (callerFindings ++ modelFindings)
        return none
      if htys : s.services.all (·.stateTys) = true then
        if hw : s.services.all (·.wireOk p.types) = true then
          return some ⟨r, p, s, Smt.check_ok hP hreach (by simpa using htys) (by simpa using hw) h,
            Smt.handles_ok h, hself⟩
        else
          invalidIr ⟨none, none,
            "a wire type has a type variable, a variant without a key per field, or no canonical order"⟩
          return none
      else
        invalidIr ⟨none, none,
          "a state, event or caller type has a type variable, an ADT 0 that is not Bool or a table with no plain key"⟩
        return none
    | findings =>
      report (findings ++ callerFindings ++ modelFindings)
      return none
  else
    invalidIr ⟨none, none, "two kept functions share a site id"⟩
    return none

/-- The spec `spec()` gives, with what check established of it, when the IR at `path` loads, `root` is its root module,
and the structure breaks no rule; otherwise none, and the lines are printed. -/
def loadSpec (root path : String) : Cmd (Option Smt.CheckedSpec) := do
  let some j ← readIr root path | return none
  match Ir.Load.load (.fn [] Ir.Ty.spec) j "spec" with
  | .error e =>
    invalidIr e
    return none
  | .ok p =>
    have hreach : ∀ v ∈ (p.eval ()).services, v.Reach p.defs.sites p.defs.effectSites := Ir.Program.reach p () trivial
    checkedOf p (p.eval ()) none "" hreach
      fun R => Ir.Var.get_rel p.root (Ir.Defs.eval_rel (R := R) p.defs) () () trivial rfl

/-- A model that passed check: the checked spec it wraps, the model, and the slots and run length its scope gives each
service of the spec, beside the service's meaning. -/
structure CheckedModel where
  checked : Smt.CheckedSpec
  model : Ir.ModelV
  bounds : ∀ v ∈ checked.spec.services, Ir.BoundsV v.records

/-- The bounds the model's scopes give the spec's services, where each has a scope, as check requires. -/
def modelBounds (m : Ir.ModelV) (s : Ir.SpecV) : Option (∀ v ∈ s.services, Ir.BoundsV v.records) :=
  if h : s.services.all (fun v => (m.scopeOf v).isSome) = true then
    some fun v hv => ((m.scopeOf v).get (List.all_eq_true.1 h v hv)).boundsOf v
  else none

/-- The spec of the model function `name`, as `loadSpec` checks a spec, with the model and its bounds; none where it
does not load or breaks a rule, and the lines are printed, each naming the model. -/
def loadNamedModel (j : Json) (name : String) : Cmd (Option CheckedModel) := do
  match Ir.Load.load (.fn [] (.dsl .model [])) j name with
  | .error e =>
    invalidIr e
    return none
  | .ok p =>
    let m : Ir.ModelV := p.eval ()
    have hm : Ir.Reach p.defs.sites p.defs.effectSites (.dsl .model []) m := Ir.Program.reach p () trivial
    let some c ← checkedOf p m.spec (some m) s!"model {name}(): " hm.1
      fun R => Ir.Var.get_rel p.root (Ir.Defs.eval_rel (R := R) p.defs) () () trivial rfl | return none
    -- Check gives every service one scope (`ModelV.illegal`), so only an engine bug finds none.
    match modelBounds m c.spec with
    | some bounds => return some ⟨c, m, bounds⟩
    | none =>
      invalidIr ⟨none, none, s!"model {name}(): a service has no scope after check"⟩
      return none

/-- The checked model `--model` names, or of the root module's one model function where it names none;
none where there is no such model or it does not check, and the lines are printed. -/
def loadModel (root path : String) (name? : Option String) : Cmd (Option (CheckedModel × String)) := do
  let some j ← readIr root path | return none
  let some _ ← loadSpec root path | return none
  let models ← match Ir.Load.models j with
    | .ok ms => pure ms
    | .error e =>
      invalidIr e
      return none
  let usage (message : String) : Cmd (Option (CheckedModel × String)) := do
    printLine (.usage .arguments) [("message", Json.str message)]
    return none
  let name ← match name?, models with
    | some n, _ =>
      if models.contains n then pure n
      else return ← usage s!"{root} defines no model function {n}() -> tazuna.Model; its models: {", ".intercalate models}"
    | none, [n] => pure n
    | none, [] => return ← usage s!"{root} defines no model: prove and generate need a function <name>() -> tazuna.Model"
    | none, ms => return ← usage s!"{root} defines the models {", ".intercalate ms}: name one with --model <name>"
  return (← loadNamedModel j name).map (·, name)

/-- Loads the IR at `path`, which the launcher converted from the root module `root`, printing one line per
finding, or one line per service when there is none. Every model function of the root module is checked too, so a
model that prove or generate would refuse shows here. -/
def check (root path : String) : Cmd Unit := do
  if let some c ← loadSpec root path then
    let some j ← readIr root path | return
    let models ← match Ir.Load.models j with
      | .ok ms => pure ms
      | .error e => return ← invalidIr e
    let mut ok := true
    for name in models do
      if (← loadNamedModel j name).isNone then ok := false
    if ok then
      c.spec.services.forM fun v => printLine .checkPassed [("service", Json.str v.name)]

end Tazuna.Cli
