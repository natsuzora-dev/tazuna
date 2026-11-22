import Tazuna.Scenario.Then

namespace Tazuna.Scenario

open Tazuna.Data

/-- A record of a Given: a keyed record has its `key`, a single-entity record none. -/
structure GivenRecord where
  entity : String
  key : Option String
  value : Value
deriving DecidableEq, Repr, Inhabited

derive_wire GivenRecord skip_serializing_none

/-- How a service that exchanges messages with the own service takes part. -/
inductive Peer where
  /-- Its spec runs from `records` and checks every line it takes part in. -/
  | run (records : List GivenRecord)
  /-- An external service: the scenario writes its answers and events, which its contract checks. -/
  | external
  /-- The service exists but does not run, and messages to it are not delivered. -/
  | skip (because : String)
deriving DecidableEq, Repr, Inhabited

derive_wire Peer tag "role"

structure PeerEntry where
  service : String
  peer : Peer
deriving DecidableEq, Repr, Inhabited

derive_wire PeerEntry flatten peer

/-- The arrangement: every running service begins at `start`, the own service from `records`. -/
structure Given where
  start : Time
  records : List GivenRecord
  peers : List PeerEntry
deriving Repr, Inhabited

derive_wire Given

end Tazuna.Scenario

namespace Tazuna

open Tazuna.Data Tazuna.Scenario

/-- A scenario of the own service `service`: Given, the lines of When, and the expectations of Then. -/
structure Scenario where
  service : String
  given : Given
  lines : List Line
  expectations : List Expectation
deriving Repr, Inhabited

derive_wire Scenario

end Tazuna
