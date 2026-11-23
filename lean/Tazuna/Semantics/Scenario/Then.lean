import Tazuna.Semantics.Scenario.Line

namespace Tazuna.Semantics.Scenario

open Tazuna.Ir

/-- A request that the own service sent: its kind, its target, and its input. -/
structure SentRequest where
  kind : RequestType
  target : Ir.Ref
  input : Template
deriving BEq, Repr, Inhabited

derive_wire SentRequest

/-- An event that the own service emitted. -/
structure EmittedEvent where
  event : Ir.Ref
  payload : Template
deriving BEq, Repr, Inhabited

derive_wire EmittedEvent

/-- An expectation of Then: an externally observable fact about a line. -/
inductive Expectation where
  /--
  Every answer that the receiver of the request of line `line` gave to it, in order: the own service's, or a running
  peer's when the client or an external peer sent the request to it.
  -/
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
deriving BEq, Repr, Inhabited

derive_wire Expectation tag "type" skip_serializing_none

def Expectation.line : Expectation → Nat
  | .answered line _ | .emitted line _ | .requested line _ _ | .offered line _ _ _ => line

def Expectation.written : Expectation → List Template
  | .answered _ answers => answers
  | .emitted _ events => events.map (·.payload)
  | .requested _ requests _ => requests.map (·.input)
  | .offered _ _ payload _ => payload.toList

/-- The picks of the expectation's handles and of the handles that its written values read, at any depth. -/
def Expectation.picks (e : Expectation) : List Template :=
  (match e with
    | .requested _ _ ends => ends.flatMap Fact.picks
    | _ => []) ++ e.written.flatMap Template.picks

end Tazuna.Semantics.Scenario
