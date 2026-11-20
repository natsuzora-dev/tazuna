import Tazuna.Scenario.Line

namespace Tazuna.Scenario

open Tazuna.Data

/--
An entry of a Then `requested`, in written order: a request that the own service sent, with its kind, target, and
input, or the end of the subscription that the request `subscription` opened.
-/
inductive Requested where
  | sent (kind : RequestType) (target : Spec.Ref) (input : Template)
  | ended (subscription : Fact)
deriving BEq, Repr, Inhabited

derive_wire Requested untagged

def Requested.sent? : Requested → Option (RequestType × Spec.Ref × Template)
  | .sent kind target input => some (kind, target, input)
  | .ended _ => none

def Requested.ended? : Requested → Option Fact
  | .sent .. => none
  | .ended subscription => some subscription

/-- An event that the own service emitted. -/
structure EmittedEvent where
  event : Spec.Ref
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
  The requests that the own service sent while line `line` was processed, and the subscriptions that it ended then,
  as written. The requests and the ends are each a bag.
  -/
  | requested (line : Nat) (requests : List Requested)
  /--
  Whether the screen that the look line `look` looked at offers `control` with `payload` at that point: `offered` is
  true for offered and false for not offered.
  -/
  | offered (look : Nat) (control : String) (payload : Option Template) (offered : Bool)
deriving BEq, Repr, Inhabited

derive_wire Expectation tag "type" skip_serializing_none

def Expectation.line : Expectation → Nat
  | .answered line _ | .emitted line _ | .requested line _ | .offered line _ _ _ => line

def Expectation.written : Expectation → List Template
  | .answered _ answers => answers
  | .emitted _ events => events.map (·.payload)
  | .requested _ requests => requests.filterMap fun r => r.sent?.map (·.2.2)
  | .offered _ _ payload _ => payload.toList

/-- The picks of the expectation's handles and of the handles that its written values read, at any depth. -/
def Expectation.picks (e : Expectation) : List Template :=
  (match e with
    | .requested _ requests => (requests.filterMap (·.ended?)).flatMap Fact.picks
    | _ => []) ++ e.written.flatMap Template.picks

end Tazuna.Scenario
