import Tazuna.Ir.Time
import Tazuna.Ir.Trace
import Tazuna.Semantics.Service.Step
import Tazuna.Semantics.Service.Uncovered

/-! This module defines the notes that the semantic run sends to the instrumentation. -/

namespace Tazuna.Semantics.Service

open Tazuna.Ir

inductive RecordPart where
  | keys (entity : String)
  | record (entity : String) (key : Value)
  | field (entity : String) (key : Option Value) (name : String)
deriving DecidableEq, Repr, Inhabited

structure RegionPair where
  first : Nat
  second : Nat
  firstRef : Ir.TransitionRef
  secondRef : Ir.TransitionRef
  state : String
deriving DecidableEq, Repr, Inhabited

structure RegionCheck where
  chart : Ir.Ref
  pairs : List RegionPair
  halted : Bool
deriving DecidableEq, Repr, Inhabited

inductive Note where
  | transitionPart (part : Nat)
  | microstepEnds (check : RegionCheck)
  /-- The run reached `part`, which `verify --coverage` then does not report. -/
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

end Tazuna.Semantics.Service
