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

/--
The body of a trace line. Every line has `dir` and `id`, `type` decides the other fields, and the `dir` of a time or
restart line is "in".
-/
inductive TraceLine.Body where
  | command (dir : Dir) (id : String) (name : String) (input : Value)
  | query (dir : Dir) (id : String) (name : String) (input : Value)
  | subscribe (dir : Dir) (id : String) (name : String) (input : Value)
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
  | .command _ _ name _ | .query _ _ name _ | .subscribe _ _ name _ | .event _ _ name _ _ | .operation _ _ name _ _ => some name
  | .answer .. | .unsubscribe .. | .time .. | .restart .. => none

def TraceLine.Body.to? : TraceLine.Body → Option String
  | .answer _ _ to _ | .unsubscribe _ _ to => some to
  | _ => none

def TraceLine.Body.resultOf? : TraceLine.Body → Option String
  | .event _ _ _ _ resultOf => resultOf
  | _ => none

/-- One line of a trace file, as an implementation writes it for `tazuna verify`. -/
structure TraceLine where
  time : DateTime
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

end Tazuna.Data
