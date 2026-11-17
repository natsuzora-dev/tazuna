import Tazuna.Data.Time
import Tazuna.Spec.Structure

/-! This module defines the notes that the semantic run sends to the instrumentation. -/

namespace Tazuna.Service

open Tazuna.Data

inductive RecordPart where
  | keys (entity : String)
  | record (entity key : String)
  | field (entity : String) (key : Option String) (name : String)
deriving DecidableEq, Repr, Inhabited

def RecordPart.name : RecordPart → String
  | .keys entity => s!"keys:{entity}"
  | .record entity key => s!"record:{entity}#{key}"
  | .field entity (some key) name => s!"field:{entity}#{key}.{name}"
  | .field entity none name => s!"field:{entity}.{name}"

/-- A copy of map state `map`, made for the item whose key is `itemKey`. -/
structure Copy where
  map : String
  itemKey : Value
deriving DecidableEq, Repr, Inhabited

derive_wire Copy

structure Who where
  chart : Spec.Ref
  copy : Option Copy := none
deriving DecidableEq, Repr, Inhabited

derive_wire Who

/-- An event that a machine receives: the key of its `receives` and the event's payload. -/
structure Received where
  key : String
  payload : Value
deriving DecidableEq, Repr, Inhabited

derive_wire Received

/--
A step as the internal queue and the search name it: by its definition and what tells it apart from another step of
that definition, so that two steps with equal names are interchangeable. `state` of a command or answer is the sending
state (none for an automation).
-/
inductive StepName where
  | start (who : Who)
  | receive (who : Who) (received : List Received)
  | always (who : Who)
  | onDone (who : Who)
  | opensDone (who : Who) (state key : String)
  | activities (who : Who) (state : String)
  | deadline (who : Who) (state name : String)
  | reaction (automation event : Spec.Ref) (payload : Value)
  | command (command : Spec.Ref) (sender : Who) (state : Option String)
  | answer (command : Spec.Ref) (sender : Who) (state : Option String)
deriving DecidableEq, Repr, Inhabited

derive_wire StepName tag "kind"

def StepName.isDeadline : StepName → Bool
  | .deadline .. => true
  | _ => false

def StepName.definition : StepName → Spec.Ref
  | .start w | .receive w _ | .always w | .onDone w | .opensDone w _ _ | .activities w _ | .deadline w _ _ => w.chart
  | .reaction a _ _ => a
  | .command _ sender _ | .answer _ sender _ => sender.chart

structure RegionPair where
  first : Nat
  second : Nat
  firstRef : Spec.TransitionRef
  secondRef : Spec.TransitionRef
  state : String
deriving DecidableEq, Repr, Inhabited

structure RegionCheck where
  chart : Spec.Ref
  pairs : List RegionPair
  halted : Bool
deriving DecidableEq, Repr, Inhabited

inductive Note where
  /-- The event lines that step `step` wrote from line `start`, in groups of the lengths `groups`. -/
  | events (step start : Nat) (groups : List Nat)
  /-- The record parts that `definition` read without asking Functions. -/
  | read (definition : Spec.Ref) (parts : List RecordPart)
  | stepBegins (step : Nat) (name : StepName) (startedResource : Option String)
  | stepEnds
  /-- The evaluation of the always transitions of `owner` and its copies before and after the work of the open step. -/
  | settlesAround (owner : String)
  /-- A read by the open step of whether instances or copies, by resource, are in the given states. -/
  | readStates (states : List (String × String))
  | wroteState (resource state : String)
  | wroteCopies (resource map : String)
  | wroteShown (resource slot : String)
  | transitionPart (part : Nat)
  | microstepEnds (check : RegionCheck)
  /-- The start of the checks and subscription answers after message `message` (afterMessage), which no step runs. -/
  | afterMessageBegins (message : Nat)
  | afterMessageEnds
deriving DecidableEq, Repr, Inhabited

/--
A monad that receives the notes of a run. `note` returns nothing, so the semantic result does not depend on who
listens.
-/
class MonadNote (m : Type → Type) where
  note : Note → m Unit

instance : MonadNote Id where
  note _ := pure ()

end Tazuna.Service
