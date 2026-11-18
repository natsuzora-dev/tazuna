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

/-- The step that wrote an event line, and the place of the line's group among the groups that its decide returned. -/
structure EmittedBy where
  step : Nat
  group : Nat
deriving DecidableEq, Repr, Inhabited

/--
What a line with direction `dir` and body `body` names besides: an `out` request line names the definition of the
service that sent the request (Requester.sender), which a check of the request at the end of the run blames after a
restart forgot who waits for it. No other line names one.
-/
abbrev SenderOf (dir : Dir) (body : LineBody) : Type :=
  match body, dir with
  | .command .., .out | .query .., .out | .subscribe .., .out => String
  | _, _ => Unit

/-- `sender` on the line with direction `dir` and body `body` if it names one (SenderOf). -/
def SenderOf.given (sender : String) (dir : Dir) : (body : LineBody) → SenderOf dir body
  | .command .. | .query .. | .subscribe .. => match dir with
    | .out => sender
    | .in => ()
  | .event .. | .answer .. | .unsubscribe .. | .time | .restart | .operation .. => ()

instance (dir : Dir) (body : LineBody) : DecidableEq (SenderOf dir body) := by
  unfold SenderOf; split <;> infer_instance

instance (dir : Dir) (body : LineBody) : Repr (SenderOf dir body) := by
  unfold SenderOf; split <;> infer_instance

/--
What a line with direction `dir` and body `body` names besides its sender: an `out` answer line names the definition of
the request that it answers, which the answer travels as. No other line names one.
-/
abbrev RequestOf (dir : Dir) (body : LineBody) : Type :=
  match body, dir with
  | .answer .., .out => Spec.Ref
  | _, _ => Unit

/-- `request` on the line with direction `dir` and body `body` if it names one (RequestOf). -/
def RequestOf.given (request : Spec.Ref) (dir : Dir) : (body : LineBody) → RequestOf dir body
  | .answer .. => match dir with
    | .out => request
    | .in => ()
  | .command .. | .query .. | .subscribe .. | .event .. | .unsubscribe .. | .time | .restart | .operation .. => ()

instance (dir : Dir) (body : LineBody) : DecidableEq (RequestOf dir body) := by
  unfold RequestOf; split <;> infer_instance

instance (dir : Dir) (body : LineBody) : Repr (RequestOf dir body) := by
  unfold RequestOf; split <;> infer_instance

/--
A trace line. Test adds `after` and `created` when it writes a snapshot.
-/
structure Line where
  time : Time
  dir : Dir
  id : LineId
  body : LineBody
  /-- Set on the `out` event lines that a command writes, and on no other line. -/
  emitted : Option EmittedBy := none
  sender : SenderOf dir body := by exact ()
  request : RequestOf dir body := by exact ()
deriving DecidableEq, Repr

instance : Inhabited Line := ⟨{ time := default, dir := .in, id := default, body := .time }⟩

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
