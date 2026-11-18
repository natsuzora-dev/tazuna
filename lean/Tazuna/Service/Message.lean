import Tazuna.Data.Answer
import Tazuna.Data.Time
import Tazuna.Data.Trace
import Tazuna.Service.Limits
import Tazuna.Service.Fault
import Tazuna.Service.InvalidInput
import Tazuna.Spec.Structure

namespace Tazuna.Service

open Tazuna.Data

inductive LineBody where
  | command (target : Spec.Ref) (input : Value)
  | query (target : Spec.Ref) (input : Value)
  | subscribe (target : Spec.Ref) (input : Value)
  /-- An event whose `resultOf` is the id of the request line of the command that the event results from. -/
  | event (event : Spec.Ref) (payload : Value) (resultOf : Option LineId)
  | answer (to : LineId) (answer : Answer)
  | unsubscribe (to : LineId)
  | time
  | restart
  /--
  An operation of `control` of an instance of `screen`: the `nth` of its open instances in opening order when more than
  one is open. `payload` is written only when the control's payload schema has fields.
  -/
  | operation (screen : Spec.Ref) (control : String) (nth : Option Nat) (payload : Option Value)
deriving DecidableEq, Repr, Inhabited

/-- What the line carries, as TS contentOf gives it: a request's input, an event's or operation's payload, an answer. -/
def LineBody.content : LineBody → Value
  | .command _ v | .query _ v | .subscribe _ v | .event _ v _ => v
  | .operation _ _ _ p => p.getD .null
  | .answer _ a => ToValue.toValue a
  | .unsubscribe _ | .time | .restart => .null

/-- The name that LineIds counts, as the trace of `service` writes it. -/
def LineBody.idName (service : String) : LineBody → String
  | .command r _ | .query r _ | .subscribe r _ | .event r _ _ => r.traceName service
  | .operation screen control _ _ => operationName (screen.traceName service) control
  | .answer _ _ => "answer"
  | .unsubscribe _ => "unsubscribe"
  | .time => "time"
  | .restart => "restart"

/--
A trace line. Test adds `after` and `created` when it writes a snapshot.
-/
structure Line where
  time : Time
  dir : Dir
  id : LineId
  body : LineBody
deriving DecidableEq, Repr, Inhabited

structure Emit where
  event : Spec.Ref
  payload : Value
deriving DecidableEq, Repr, Inhabited

derive_wire Emit

/-- What the run reports: a fault of the spec, or a message that the service takes and that is invalid. -/
inductive Finding where
  | fault (fault : Fault)
  | invalidInput (invalid : InvalidInput)
deriving Repr

def Finding.halts : Finding → Bool
  | .fault f => f.halts
  | .invalidInput i => i.halts

def Finding.toViolation : Finding → Violation
  | .fault f => f.toViolation
  | .invalidInput i => i.toViolation

end Tazuna.Service
