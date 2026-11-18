import Tazuna.Data.Time
import Tazuna.Service.Step

/-! This module defines the notes that the semantic run sends to the instrumentation. -/

namespace Tazuna.Service

open Tazuna.Data

inductive RecordPart where
  | keys (entity : String)
  | record (entity key : String)
  | field (entity : String) (key : Option String) (name : String)
deriving DecidableEq, Repr, Inhabited

/--
The channel that an `out` line travels on, seen from its sender (Sim's Message.sameChannel, whose receiver a trace line
does not name): a request and its end travel to the request's receiver on the request's own channel, the answers to a
received request travel back to its sender, and events travel to their receivers on the channel of their `resultOf`,
or on the sender's channel when they name none. A line that no sender writes `out` travels on none.
-/
inductive Channel where
  | request (id : String)
  | answers (request : String)
  | events (resultOf : Option String)
deriving DecidableEq, Repr

derive_wire Channel tag "kind"

/--
A value that steps read and write. Being in a state also stands for the copy set of a map state, and a channel for the
order of the lines on it.
-/
inductive ValueKey where
  | record (part : RecordPart)
  | context (id : InstanceId) (field : String)
  | state (id : InstanceId) (state : String)
  | shown (id : InstanceId) (slot : String)
  | channel (c : Channel)
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
  /-- The event lines that step `step` wrote from line `start`, in groups of the lengths `groups`. -/
  | events (step start : Nat) (groups : List Nat)
  /-- The record parts that `definition` read without asking Functions. -/
  | read (definition : Spec.Ref) (parts : List RecordPart)
  | stepBegins (step : Nat) (name : StepName) (started : Option InstanceId)
  | stepEnds
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
