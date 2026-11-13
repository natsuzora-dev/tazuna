import Tazuna.Data.Answer
import Tazuna.Data.Time

namespace Tazuna.Data

inductive Dir where
  | «in»
  | out
deriving DecidableEq, Repr, Inhabited

derive_wire Dir

/--
The identity of a deadline of an active state. `instance` is the resource of the chart instance or copy that holds
the deadline: the chart name, `name(2)` for the second opening of a screen, or `owner@map[key]` for a copy.
-/
structure DeadlineId where
  «instance» : String
  state : String
  name : String
deriving DecidableEq, Repr, Inhabited

derive_wire DeadlineId

inductive InDir where
  | «in»
deriving DecidableEq, Repr, Inhabited

derive_wire InDir

/--
The body of a trace line. Every line has `dir` and `id`, `type` decides the other fields, and the `dir` of a time or
restart line is "in".
-/
inductive TraceLine.Body where
  | command (dir : Dir) (id : Option String) (name : String) (input : Value)
  | query (dir : Dir) (id : Option String) (name : String) (input : Value)
  | subscribe (dir : Dir) (id : Option String) (name : String) (input : Value)
  | answer (dir : Dir) (id : Option String) (to : String) (answer : Answer)
  | unsubscribe (dir : Dir) (id : Option String) (to : String)
  | event (dir : Dir) (id : Option String) (name : String) (payload : Value) (resultOf : Option String)
  | operation (dir : Dir) (id : Option String) (name : String) (payload : Option Value)
  | unacceptedOperation (dir : Dir) (id : Option String) (name : String) (payload : Option Value)
  | time (dir : InDir) (id : Option String)
  | restart (dir : InDir) (id : Option String)
deriving DecidableEq, Repr, Inhabited

derive_wire TraceLine.Body tag "type" after dir skip_serializing_none

def TraceLine.Body.dir : TraceLine.Body → Dir
  | .command dir .. | .query dir .. | .subscribe dir .. | .answer dir .. | .unsubscribe dir .. | .event dir ..
  | .operation dir .. | .unacceptedOperation dir .. => dir
  | .time .in _ | .restart .in _ => .in

def TraceLine.Body.id : TraceLine.Body → Option String
  | .command _ id .. | .query _ id .. | .subscribe _ id .. | .answer _ id .. | .unsubscribe _ id .. | .event _ id ..
  | .operation _ id .. | .unacceptedOperation _ id .. | .time _ id | .restart _ id => id

def TraceLine.Body.name? : TraceLine.Body → Option String
  | .command _ _ name _ | .query _ _ name _ | .subscribe _ _ name _ | .event _ _ name _ _ | .operation _ _ name _
  | .unacceptedOperation _ _ name _ => some name
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
  /--
  On an `in` line, the deadlines that fire first in the ties during the input, in firing order, which only test's
  search writes. A tie starts when two or more deadlines are due at the earliest due time; from then until no deadline
  is due at that time, each deadline that fires at that time is the next entry (InvalidInput.deadlineNotNext), and
  after the entries, the first due in entry order.
  -/
  deadlineOrder : Option (List DeadlineId)
  after : Option (List String)
  created : Option (List String)
deriving DecidableEq, Repr, Inhabited

derive_wire TraceLine flatten body skip_serializing_none

/-- Each createKey value of a snapshot (`created`), with the value of a compared trace that stands for it. -/
abbrev Bindings := List (String × String)

/-- `v` with each string that `bindings` binds replaced by its bound value. -/
def Bindings.rename (bindings : Bindings) (v : Value) : Value :=
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

end Tazuna.Data
