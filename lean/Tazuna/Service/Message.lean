import Tazuna.Data.Answer
import Tazuna.Data.Time
import Tazuna.Data.Trace
import Tazuna.Service.Limits
import Tazuna.Service.Fault
import Tazuna.Service.InvalidInput
import Tazuna.Syntax.Structure

namespace Tazuna.Semantics

open Tazuna.Data

def RejectionKind.byCaller : RejectionKind → Bool
  | .unavailable => false
  | _ => true

inductive LineBody where
  | command (name : String) (input : Value)
  | query (name : String) (input : Value)
  | subscribe (name : String) (input : Value)
  /-- An event whose `resultOf` is the id of the request line of the command that the event results from. -/
  | event (name : String) (payload : Value) (resultOf : Option String)
  | answer (to : String) (answer : Answer)
  | unsubscribe (to : String)
  | time
  | restart
  /-- An operation of a screen's control. `name` is `screen.control`, and `payload` is written only when the control's
  payload schema has fields. -/
  | operation (name : String) (payload : Option Value)
deriving DecidableEq, Repr, Inhabited

/-- The name that LineIds counts. -/
def LineBody.idName : LineBody → String
  | .command name _ | .query name _ | .subscribe name _ | .event name _ _ | .operation name _ => name
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
  id : String
  body : LineBody
deriving DecidableEq, Repr, Inhabited

structure Emit where
  event : String
  payload : Value
deriving DecidableEq, Repr, Inhabited

/--
A violation. `kind` is the group and the constructor, such as `Fault.exception`, and `definition` is the definition
that caused the violation, or null when the subject is no definition.
-/
structure Violation where
  kind : String
  definition : Value
  data : Value
deriving DecidableEq, Repr, Inhabited

derive_wire Violation

/-- What the run reports: a fault of the spec, or a scenario input that is invalid. -/
inductive Finding where
  | fault (fault : Fault)
  | invalidInput (invalid : InvalidInput)

def Finding.halts : Finding → Bool
  | .fault f => f.halts
  | .invalidInput i => i.halts

def Finding.toViolation : Finding → Violation
  | .fault f => { kind := f.kind, definition := f.definition, data := f.data }
  | .invalidInput i => { kind := i.kind, definition := i.definition, data := i.data }

end Tazuna.Semantics
