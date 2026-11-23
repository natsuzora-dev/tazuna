import Tazuna.Data.Answer
import Tazuna.Data.Time

namespace Tazuna.Data

inductive Dir where
  | «in»
  | out
deriving DecidableEq, Repr, Inhabited

derive_wire Dir

inductive InDir where
  | «in»
deriving DecidableEq, Repr, Inhabited

derive_wire InDir

/-- The id of a line of a run: one that the run gives, or the id that `sender` gave a message that the run received. -/
inductive LineId where
  | own (id : String)
  | received (sender id : String)
deriving DecidableEq, Repr, Inhabited

derive_wire LineId tag "kind"

/-- The id as a trace line writes it, `<sender>/<id>` for a received message. -/
def LineId.text : LineId → String
  | .own id => id
  | .received sender id => s!"{sender}/{id}"

/--
Who sent a request, as the receiver knows it from outside the spec (authentication): a record of an entity of the
receiving service, by its key, or a service, by its name. A Cedar request names its principal the same way.
-/
inductive Caller where
  | entity (entity : String) (key : Value)
  | service (service : String)
deriving DecidableEq, Repr, Inhabited

derive_wire Caller untagged

/-- The strings of the caller in which created keys are searched: an entity record's key. -/
def Caller.strings : Caller → List String
  | .entity _ key => key.strings
  | .service _ => []

/--
The body of a trace line. Every line has `dir` and `id`, `type` decides the other fields, and the `dir` of a time or
restart line is "in".
-/
inductive TraceLine.Body where
  | command (dir : Dir) (id : String) (name : String) (input : Value) (caller : Caller)
  | query (dir : Dir) (id : String) (name : String) (input : Value) (caller : Caller)
  | subscribe (dir : Dir) (id : String) (name : String) (input : Value) (caller : Caller)
  | answer (dir : Dir) (id : String) (to : String) (answer : Answer)
  | unsubscribe (dir : Dir) (id : String) (to : String)
  | event (dir : Dir) (id : String) (name : String) (payload : Value) (resultOf : Option String)
  /--
  `nth` is the operated instance's index among the open instances of its screen in opening order, written only when
  more than one is open.
  -/
  | operation (dir : Dir) (id : String) (name : String) (nth : Option Nat) (payload : Option Value)
  | time (dir : InDir) (id : String)
  | restart (dir : InDir) (id : String)
deriving DecidableEq, Repr, Inhabited

derive_wire TraceLine.Body tag "type" after dir skip_serializing_none

def TraceLine.Body.dir : TraceLine.Body → Dir
  | .command dir .. | .query dir .. | .subscribe dir .. | .answer dir .. | .unsubscribe dir .. | .event dir ..
  | .operation dir .. => dir
  | .time .in _ | .restart .in _ => .in

def TraceLine.Body.id : TraceLine.Body → String
  | .command _ id .. | .query _ id .. | .subscribe _ id .. | .answer _ id .. | .unsubscribe _ id .. | .event _ id ..
  | .operation _ id .. | .time _ id | .restart _ id => id

def TraceLine.Body.name? : TraceLine.Body → Option String
  | .command _ _ name _ _ | .query _ _ name _ _ | .subscribe _ _ name _ _ | .event _ _ name _ _ | .operation _ _ name _ _ => some name
  | .answer .. | .unsubscribe .. | .time .. | .restart .. => none

def TraceLine.Body.caller? : TraceLine.Body → Option Caller
  | .command _ _ _ _ caller | .query _ _ _ _ caller | .subscribe _ _ _ _ caller => some caller
  | _ => none

def TraceLine.Body.to? : TraceLine.Body → Option String
  | .answer _ _ to _ | .unsubscribe _ _ to => some to
  | _ => none

def TraceLine.Body.resultOf? : TraceLine.Body → Option String
  | .event _ _ _ _ resultOf => resultOf
  | _ => none

/-- One line of a trace file, as an implementation writes it for `tazuna verify`. -/
structure TraceLine where
  time : Time
  body : TraceLine.Body
  after : Option (List String)
  created : Option (List String)
deriving DecidableEq, Repr, Inhabited

derive_wire TraceLine flatten body skip_serializing_none

def isEventLine (l : TraceLine) : Bool :=
  match l.body with
  | .event .. => true
  | _ => false

/-- Pairs of a snapshot string and the trace string that stands for it. -/
abbrev Bindings := List (String × String)

/-- `v` with each string that `bindings` binds replaced by its bound value. -/
def Bindings.substitute (bindings : Bindings) (v : Value) : Value :=
  v.mapStrings fun s => (bindings.lookup s).getD s

inductive FileLine (α : Type) where
  | blank
  /-- The trace line schema cannot read the line. -/
  | malformed
  | line (l : α)

/-- A line of a trace file as the wire writes it: null when blank, `"malformed"`, or the line. -/
instance {α : Type} [ToValue α] : ToValue (FileLine α) := ⟨fun
  | .blank => .null
  | .malformed => .str "malformed"
  | .line l => ToValue.toValue l⟩

instance {α : Type} [FromValue α] : FromValue (FileLine α) := ⟨fun
  | .null => pure .blank
  | .str "malformed" => pure .malformed
  | v => .line <$> FromValue.fromValue v⟩

/-- The lines before the first malformed line, `none` for blank lines, and the number of that line, from 1. -/
def untilMalformed {α : Type} : List (FileLine α) → List (Option α) × Option Nat
  | [] => ([], none)
  | .blank :: ls => (untilMalformed ls).map (none :: ·) (·.map (· + 1))
  | .malformed :: _ => ([], some 1)
  | .line l :: ls => (untilMalformed ls).map (some l :: ·) (·.map (· + 1))

/-- The name of an operation line in a trace, the one place that joins a screen and its control. -/
def operationName (screen control : String) : String := s!"{screen}.{control}"

/-- The screen and the control that the name of an operation line joins. -/
def operationParts (name : String) : String × String :=
  match name.splitOn "." with
  | screen :: control :: _ => (screen, control)
  | parts => (parts.headD "", "")

/--
A trace line as a violation names it: an answer or unsubscribe line by its `to`, and any other line by its name and
id.
-/
inductive Subject where
  | reply (type to : String)
  | named (type : String) (name : Option String) (id : String)
deriving Repr

derive_wire Subject untagged

def Subject.of (l : TraceLine) : Subject :=
  match l.body with
  | .answer _ _ to _ | .unsubscribe _ _ to => .reply l.body.type to
  | _ => .named l.body.type l.body.name? l.body.id

end Tazuna.Data
