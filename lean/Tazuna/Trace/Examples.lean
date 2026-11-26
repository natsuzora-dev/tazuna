import Tazuna.Trace.Verify
import Tazuna.Semantics.StepExamples

/-! The trace writer and verify agree: a trace written from inputs (`traceOf`, what generate writes), printed as text
and read back, replays as passed, header and all. -/

namespace Tazuna.Trace.Examples

open Tazuna.Ir Tazuna.Ir.StepExamples

/-- The lines of a written trace after its header, printed and parsed again, numbered as verify numbers them. -/
def reread (ws : List Wire) : Option (List (Nat × Line)) :=
  (ws.drop 1).zipIdx.mapM fun (w, k) => match Wire.parse w.text with
    | .ok w' => (Line.ofWire w').map (k + 2, ·)
    | .error _ => none

/-- Whether the trace of the inputs replays as passed. -/
def replays (xs : List (Input svc)) : Bool :=
  match traceOf prelude svc xs with
  | .ok ws => match reread ws with
    | some lines => match replay prelude svc lines with
      | .passed => (ws.head?.map Wire.text) == some (header "sum").text
      | _ => false
    | none => false
  | .error _ => false

-- Commands (accepted, invalid, rejected), a query, an event, which sets the machine's timer, a clock line firing it
-- and sending `ping`, and the answer to it.
#guard replays [cmd 1 5, cmd 2 5, cmd 1 0, .query ⟨0, by decide⟩ (1 : Int) (0 : Int), .event ⟨0, by decide⟩ (2 : Int),
  .clock 10, .answer 0 ⟨Ty.result .int .str, .inl ((0 : Int), ())⟩]
-- A trace stops where the spec faults; generate writes no such trace.
#guard match traceOf prelude svc [cmd 1 60] with
  | .error (.fault 1 _) => true
  | _ => false

end Tazuna.Trace.Examples
