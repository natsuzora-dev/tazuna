import Tazuna.Semantics.Sim.Order

/-! This module builds the lines of a snapshot from a running service's trace. -/

namespace Tazuna.Semantics.Sim

open Tazuna.Ir Tazuna.Semantics.Service

/--
The strings of a line body in which createKey values are searched. Rejection kinds are excluded, since they can never
be createKey values.
-/
def bodyStrings : LineBody → List String
  | .command _ input caller | .query _ input caller | .subscribe _ input caller => input.strings ++ caller.strings
  | .event _ payload _ => payload.strings
  | .answer _ a => match a with
    | .accepted none => ["accepted"]
    | .accepted (some o) => "accepted" :: o.strings
    | .fulfilled o => "fulfilled" :: o.strings
    | .rejected r => "rejected" :: r.reason.toList
  | .unsubscribe _ | .time | .restart => []
  | .operation _ _ _ payload => (payload.map Value.strings).getD []

/-- The first `out` line where createKey value `v` appears. -/
def firstOut (s : Service.State) (v : String) : Option Nat :=
  (s.lines.toList.zipIdx.find? fun (l, _) => l.dir == .out && v ∈ bodyStrings l.body).map (·.2)

/-- The createKey values whose first `out` line is `i`, in createKey order. -/
def createdAt (s : Service.State) (i : Nat) : List String :=
  (s.created.map (·.2)).filter (firstOut s · == some i)

def trace (s : Service.State) : List (Line × List LineId × List String) :=
  s.lines.toList.zipIdx.map fun (line, i) => (line, after s i, createdAt s i)

/--
The trace line of `line` of the trace of `service` as a snapshot holds it, with its `after` and `created`. This is where
a definition gets its trace name and a line id its text.
-/
def traceLineOf (service : String) (line : Line) (after : List LineId) (created : List String) : TraceLine :=
  let (dir, id) := (line.dir, line.id.text)
  let name (r : Ir.Ref) := r.traceName service
  let body : TraceLine.Body := match line.body with
    | .command r input caller => .command dir id (name r) input caller
    | .query r input caller => .query dir id (name r) input caller
    | .subscribe r input caller => .subscribe dir id (name r) input caller
    | .event r payload resultOf => .event dir id (name r) payload (resultOf.map (·.text))
    | .answer to answer => .answer dir id to.text answer
    | .unsubscribe to => .unsubscribe dir id to.text
    | .time => .time .in id
    | .restart => .restart .in id
    | .operation screen control nth payload => .operation dir id (operationName (name screen) control) nth payload
  { time := line.time
    body
    after := if after.isEmpty then none else some (after.map (·.text))
    created := if created.isEmpty then none else some created }

end Tazuna.Semantics.Sim
