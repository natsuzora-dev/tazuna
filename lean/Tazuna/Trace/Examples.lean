import Tazuna.Trace.Verify
import Tazuna.Semantics.StepExamples

/-! The trace writer and verify agree: a trace written from inputs (`traceOf`, what generate writes), printed as text
and read back as verify reads a file, replays as passed. -/

namespace Tazuna.Trace.Examples

open Tazuna.Ir Tazuna.Ir.StepExamples

/-- Whether the trace of the inputs, printed and parsed again, replays as passed. -/
def replays (xs : List (Input svc)) : Bool :=
  match traceOf prelude svc xs with
  | .ok tr =>
    let text (w : Wire) := (Wire.parse w.text).toOption
    let read := tr.numbered.mapM fun (k, l) => (text l.toWire >>= Line.ofWire).map (k, ·)
    match (text (header tr.service) >>= headerService?), read with
    | some "sum", some lines => match replay prelude svc lines with
      | .passed => true
      | _ => false
    | _, _ => false
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
