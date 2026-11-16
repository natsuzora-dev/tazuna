import Tazuna.Data.Group
import Tazuna.Data.Time
import Tazuna.Syntax.Structure

namespace Tazuna.Sim

open Tazuna.Data

/--
What the simulation of a scenario reports about the scenario. `scenarioLine` is the line of When, from 0. A message is
named by its sender, its receiver, and the sender's id of it.
-/
inductive Report where
  /-- No fact matches the handle `fact` that the line names. -/
  | unresolvedReference (scenarioLine : Nat) (fact : Value)
  /-- Several facts, `candidates`, match the handle `fact`; the handle must name content that tells them apart. -/
  | ambiguousReference (scenarioLine : Nat) (fact : Value) (candidates : List Value)
  /-- The line reads the output of the answer to `fact`, which has no answer with an output by then. -/
  | missingOutput (scenarioLine : Nat) (fact : Value)
  /-- The line reads the field at `path` of `value`, which has none. -/
  | missingField (scenarioLine : Nat) (path : List String) (value : Value)
  /-- The written value `value` is not of the form that the line needs. -/
  | malformedValue (scenarioLine : Nat) (value : Value)
  /-- A running service sent a message to `service`, which Given does not list. -/
  | unlistedService (scenarioLine : Option Nat) (service : String)
  /-- Given writes no record of the single-entity `entity` of the running service `service`. -/
  | missingRecord (service entity : String)
  /-- The line needs `service` to take part in another way than Given says: running, external, or the own service. -/
  | wrongRole (scenarioLine : Nat) (service : String)
  /-- The line delivers, loses or answers `message`, which is not in flight. -/
  | notInFlight (scenarioLine : Nat) (message : Value)
  /-- The line delivers `message` again, which was not delivered. -/
  | notDelivered (scenarioLine : Nat) (message : Value)
  /-- The line delivers `message` while the earlier `earlier` on the same channel is in flight. -/
  | overtaking (scenarioLine : Nat) (message earlier : Value)
  /-- No message in flight from the running peer `peer` to the own service is the line's. -/
  | unpairedPeerLine (scenarioLine : Nat) (peer : String)
  /-- The messages `candidates` in flight from the running peer `peer` are all the line's; their content must differ. -/
  | ambiguousPeerLine (scenarioLine : Nat) (peer : String) (candidates : List Value)
  /-- The clock line's time `at` is not later than `now`. -/
  | notLater (scenarioLine : Nat) («at» now : Time)
  /-- A written value has the form of a key `key` of `entity` that no running service has created. -/
  | uncreatedKey (scenarioLine : Nat) (key : String) (entity : Syntax.Ref)
  /-- The screen instance `screen` that the line operates is not the one that takes operations of its screen. -/
  | unoperableScreen (scenarioLine : Nat) (screen : String)
  /-- The running peer's answer `actual`, which the line delivers, is not the line's `expected`. -/
  | differentPeerAnswer (scenarioLine : Nat) (expected actual : Value)
  /-- The message `message` is undelivered at the end, and no inFlight line covers its channel. -/
  | leftInFlight (message : Value)
  /-- The expectation `expectation` of Then, from 0, states `expected`, and the run gave `actual`. -/
  | unmetExpectation (expectation : Nat) (expected actual : Value)
deriving Repr, Inhabited

local instance : ToValue Time := ⟨fun t => .str (renderTime t)⟩

derive_group Report

/-- Whether the report stops the simulation: a line that cannot take place does. -/
def Report.halts : Report → Bool
  | .differentPeerAnswer .. | .leftInFlight .. | .unmetExpectation .. => false
  | _ => true

end Tazuna.Sim
