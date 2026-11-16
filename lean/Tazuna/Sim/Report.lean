import Tazuna.Data.Group
import Tazuna.Data.Time
import Tazuna.Syntax.Structure

namespace Tazuna.Sim

open Tazuna.Data

/--
What the simulation of a scenario reports about the scenario. `scenarioLine` is the line of When, from 0. A message is
named by its sender, its receiver, and the sender's id of it.

Given is checked first, and each of its reports is given; after any of them, nothing begins. A report of a line of When
stops the simulation, unless `halts` says otherwise, since later lines may depend on what the line did. An expectation
of Then never stops the others: each is evaluated, and what it reports belongs to it alone.
-/
inductive Report where
  /-- Given lists `service` as a peer more than once, or lists the own service as a peer. -/
  | repeatedPeer (service : String)
  /--
  The own service exchanges messages with `service` (its definitions name the other's, or `service` is a spec service
  whose definitions name the own service's), and Given does not list it as run, external or skip.
  -/
  | unlistedPeer (service : String)
  /--
  Given writes a record of `entity` of the running service `service` that is no entity of it, that has a key for a
  single entity or none for a keyed one, or that does not match the entity's schema.
  -/
  | invalidRecord (service entity : String) (key : Option String)
  /-- The record of `entity` clashes with an earlier record of Given: the same key, or the same unique values. -/
  | duplicateRecord (service entity : String) (key : Option String)
  /--
  The invariant `invariant` of the record of `entity` with `key`, or of the service when `entity` is none, fails on
  Given's records of `service`; `invariant` is none when the invariant throws.
  -/
  | brokenGivenInvariant (service : String) (entity key invariant : Option String)
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
  /-- The line fails `message`, which is no request: only a request has an answer that can tell its sender. -/
  | unfailable (scenarioLine : Nat) (message : Value)
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
  /-- No message is undelivered at the end on the channel that the inFlight line covers. -/
  | unusedInFlight (scenarioLine : Nat)
  /-- The offered expectation `expectation` names the line `scenarioLine`, which is no look line. -/
  | notLook (expectation scenarioLine : Nat)
  /-- The expectation `expectation` of Then, from 0, states `expected`, and the run gave `actual`. -/
  | unmetExpectation (expectation : Nat) (expected actual : Value)
deriving Repr, Inhabited

local instance : ToValue Time := ⟨fun t => .str (renderTime t)⟩

derive_group Report

/-- Whether the report of a line stops the simulation: a line that cannot take place does. -/
def Report.halts : Report → Bool
  | .differentPeerAnswer .. | .leftInFlight .. | .unusedInFlight .. | .unmetExpectation .. | .notLook .. => false
  | .repeatedPeer .. | .unlistedPeer .. | .invalidRecord .. | .duplicateRecord .. | .brokenGivenInvariant .. => false
  | .missingRecord .. => false
  | _ => true

end Tazuna.Sim
