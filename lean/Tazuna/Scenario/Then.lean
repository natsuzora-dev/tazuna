import Tazuna.Scenario.Line

namespace Tazuna.Scenario

open Tazuna.Data

/-- A request that the own service sent: its kind, its target, and its input. -/
structure SentRequest where
  kind : RequestType
  target : Syntax.Ref
  input : Template
deriving DecidableEq, Repr, Inhabited

derive_wire SentRequest

/-- An event that the own service emitted. -/
structure EmittedEvent where
  event : Syntax.Ref
  payload : Template
deriving DecidableEq, Repr, Inhabited

derive_wire EmittedEvent

/-- An expectation of Then: an externally observable fact of the own service, about a line. -/
inductive Expectation where
  /-- Every answer that the own service gave to the request of line `line`, in order. -/
  | answered (line : Nat) (answers : List Template)
  /-- The events, listed by a contract, that the own service emitted while line `line` was processed, as a bag. -/
  | emitted (line : Nat) (events : List EmittedEvent)
  /--
  The requests that the own service sent while line `line` was processed, and the subscriptions, each named by the
  request that opened it, that the own service ended then, each as a bag.
  -/
  | requested (line : Nat) (requests : List SentRequest) (ends : List Fact)
  /--
  Whether the screen that the look line `look` looked at offers `control` with `payload` at that point: `offered` is
  true for offered and false for not offered.
  -/
  | offered (look : Nat) (control : String) (payload : Option Template) (offered : Bool)
deriving DecidableEq, Repr, Inhabited

derive_wire Expectation tag "type" skip_serializing_none

end Tazuna.Scenario
