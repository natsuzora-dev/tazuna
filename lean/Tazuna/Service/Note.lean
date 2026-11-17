import Tazuna.Data.Time
import Tazuna.Syntax.Structure

/-! This module defines the notes that the semantic run sends to the instrumentation. -/

namespace Tazuna.Semantics

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
  chart : Syntax.Ref
  copy : Option Copy := none
deriving DecidableEq, Repr, Inhabited

derive_wire Who

inductive StepName where
  | start (who : Who)
  | receive (who : Who) (keys : List String)
  | always (who : Who)
  | onDone (who : Who)
  | opensDone (who : Who) (key : String)
  | activities (who : Who) (state : String)
  | deadline (who : Who) (name : String)
  | reaction (automation : Syntax.Ref)
  | command (command : Syntax.Ref) (sender : Who)
  | answer (command : Syntax.Ref) (sender : Who)
deriving DecidableEq, Repr, Inhabited

derive_wire StepName tag "kind"

def StepName.isDeadline : StepName → Bool
  | .deadline .. => true
  | _ => false

def StepName.definition : StepName → Syntax.Ref
  | .start w | .receive w _ | .always w | .onDone w | .opensDone w _ | .activities w _ | .deadline w _ => w.chart
  | .reaction a => a
  | .command _ sender | .answer _ sender => sender.chart

structure RegionPair where
  first : Nat
  second : Nat
  firstRef : Syntax.TransitionRef
  secondRef : Syntax.TransitionRef
  state : String
deriving DecidableEq, Repr, Inhabited

structure RegionCheck where
  chart : Syntax.Ref
  pairs : List RegionPair
  halted : Bool
deriving DecidableEq, Repr, Inhabited

inductive Note where
  /-- The event lines that step `step` wrote from line `start`, in groups of the lengths `groups`. -/
  | events (step start : Nat) (groups : List Nat)
  /-- The record parts that `definition` read without asking Functions. -/
  | read (definition : Syntax.Ref) (parts : List RecordPart)
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
deriving DecidableEq, Repr, Inhabited

/--
A monad that receives the notes of a run. `note` returns nothing, so the semantic result does not depend on who
listens.
-/
class MonadNote (m : Type → Type) where
  note : Note → m Unit

instance : MonadNote Id where
  note _ := pure ()

end Tazuna.Semantics
