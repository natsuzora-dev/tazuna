import Tazuna.Data.Time
import Tazuna.Data.Trace
import Tazuna.Service.Step
import Tazuna.Service.Uncovered

/-! This module defines the notes that the semantic run sends to the instrumentation. -/

namespace Tazuna.Service

open Tazuna.Data

inductive RecordPart where
  | keys (entity : String)
  | record (entity key : String)
  | field (entity : String) (key : Option String) (name : String)
deriving DecidableEq, Repr, Inhabited

/-- A value that steps read and write. Being in a state also stands for the copy set of a map state. -/
inductive ValueKey where
  | record (part : RecordPart)
  | context (id : InstanceId) (field : String)
  | state (id : InstanceId) (state : String)
  | shown (id : InstanceId) (slot : String)
deriving DecidableEq, Repr, Inhabited

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
  /-- The record parts that `definition` read without asking Functions. -/
  | read (definition : Spec.Ref) (parts : List RecordPart)
  | stepBegins (step : Nat) (name : StepName) (started : Option InstanceId)
  | stepEnds
  /--
  The arrival of a message of a tie in step `step`, whose processing outside any step (such as its decide) belongs to
  that step, until arrivalEnds.
  -/
  | arrivalBegins (step : Nat) (name : StepName)
  | arrivalEnds
  /-- The evaluation of the always transitions of `owner` and its copies before and after the work of the open step. -/
  | settlesAround (owner : InstanceId)
  /-- A read by the open step of whether instances or copies are in the given states. -/
  | readStates (states : List (InstanceId × String))
  | wroteState (id : InstanceId) (state : String)
  | wroteCopies (id : InstanceId) (map : String)
  | wroteShown (id : InstanceId) (slot : String)
  | transitionPart (part : Nat)
  | microstepEnds (check : RegionCheck)
  /-- The start of the checks and subscription answers after message `message` (afterMessage), which no step runs. -/
  | afterMessageBegins (message : Nat)
  | afterMessageEnds
  /-- The run reached `part`, which `test --coverage` then does not report. -/
  | reached (part : Uncovered)
  /--
  A tazuna bug: the run reached a state that the semantics never reaches for a spec that its types accept, and goes on
  as if it had not. A listener that runs tazuna stops the run, as rustc stops on an internal compiler error.
  -/
  | bug (message : String)
deriving DecidableEq, Repr, Inhabited

/--
A monad that receives the notes of a run. `note` returns nothing, so the semantic result does not depend on who
listens; a listener can only stop the run, on a bug.
-/
class MonadNote (m : Type → Type) where
  note : Note → m Unit

instance : MonadNote Id where
  note _ := pure ()

/--
The value that a lookup in the structure or the service finds, which a checked spec guarantees: a lookup that finds
nothing notes a bug and goes on with `default`.
-/
def expectFound {m : Type → Type} {α : Type} [Monad m] [MonadNote m] [Inhabited α] (what : String) : Option α → m α
  | some a => pure a
  | none => do MonadNote.note (.bug s!"no {what}"); pure default

end Tazuna.Service
