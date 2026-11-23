import Engine.Json
import Engine.Protocol
import Tazuna.Semantics.Validation.Canonical
import Tazuna.Semantics.Value.Parse

/-!
The engine: it reads one Request per line on stdin and writes one Response per line on stdout (precedents:
leanprover-community/repl, the Lean LSP). Engine/Protocol.lean defines the messages.
-/

open Tazuna Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Json Tazuna.Engine

def sendLine {α : Type} [ToValue α] (stdout : IO.FS.Stream) (message : α) : IO Unit := do
  stdout.putStrLn (render (ToValue.toValue message))
  stdout.flush

/-- The response to `request`, asking `solve` for Z3's outputs mid-request. A snapshot line is none for a blank line. -/
def respond (solve : List String → IO (List String)) : Engine.Request → IO Response
  | .check s => pure (.checked (Validation.check s))
  | .checkCanonical s => pure (.checkedCanonical (Validation.Canonical.check s))
  | .pairSnapshots services expected folders =>
    let found := Verify.pairSnapshots services expected folders
    pure (.pairedSnapshots found.compare (unpaired found.violations))
  | .compareSnapshot snapshot run => pure (.comparedSnapshot (Verify.compareSnapshot snapshot run))
  | .afters snapshot =>
    let lines := snapshot.map (·.map fun l : TraceLine => ({ l with value := none } : Verify.Line))
    pure (.afters (Verify.unknownAfters lines))
  | .decodeLines values =>
    pure (.decodedLines (values.map fun v => (FromValue.fromValue v : Except String TraceLine).toOption))
  | .test s scenarios => do pure (.tested (← Engine.test s scenarios))
  | .verify s logs => do
    let (replayed, uncovered) ← Engine.verify s logs
    pure (.verified replayed uncovered)
  | .bindings s service snapshot trace => do
    let (findings, bindings) ← Engine.bindingsOf s service snapshot trace
    pure (.bound findings bindings)
  | .verifyExternal s service trace => do pure (.verifiedExternal (← Engine.verifyExternal s service trace))
  | .givenRecords s sc service => do pure (.given (← Engine.givenRecordsOf s sc service))
  | .readLines s service lines => do pure (.read (← Engine.readSnapshotLines s service lines))
  | .evaluate body input records keys fields =>
    let env : Eval.Env := { args := Eval.argsOf [(.input, .json input)], records := records.map Stored.row, keys,
                            fields := fun e => (fields.lookup e).getD [] }
    let (answer, trace) := (do Eval.encode env (← Eval.eval env [] body)).run'
    let reads := trace.parts.map ReadPart.of
    let created := trace.created
    pure (match answer with
      | .ok value => .evaluated { value, issue := none, reads, created }
      | .error issue => .evaluated { value := none, issue, reads, created })
  | .parse schema value =>
    -- What prove's record facts say of the record that parse gives, or of `value` when parse gives none.
    let facts (v : Value) := Smt.recordHolds schema v
    pure (match Semantics.parse schema value with
    | none => .parsed false none none false none
    | some (.error ()) => .parsed true none none true (facts value)
    | some (.ok (.ok v)) => .parsed true (some v) none false (facts v)
    | some (.ok (.error issues)) => .parsed true none (some issues) false (facts value))
  | .proveQueries s => do pure (.queried (← proveQueriesOf s))
  | .prove s answers => do pure (.proved (← proveOf s answers))
  | .generate s depth => do pure (.generated (← generateOf s depth solve))
  | .solved _ => throw (IO.userError "solved answers no solve")
where
  unpaired (l : List (Verify.At × Verify.Uncomparable)) : List Unpaired := l.map fun (place, violation) => { «at» := place, violation }

/-- Z3's outputs on `scripts`: a `solve` response out, and the `solved` request that TS answers it with. -/
def solveOver (stdin stdout : IO.FS.Stream) (scripts : List String) : IO (List String) := do
  sendLine stdout (Response.solve scripts)
  match ← IO.ofExcept (parse (← stdin.getLine) >>= FromValue.fromValue) with
  | Engine.Request.solved outputs => pure outputs
  | _ => throw (IO.userError "expected solved")

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let reply ← try
      respond (solveOver stdin stdout) (← IO.ofExcept (parse line >>= FromValue.fromValue))
    catch e => pure (.error (toString e))
  sendLine stdout reply
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
