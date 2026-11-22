import Tazuna.Scenario.Ref

namespace Tazuna.Scenario

open Tazuna.Data

/--
A line of a scenario's When, in written order. The sender is named by the line: the client and the user are outside
every service, a peer is named by its service, and the receiver is the owner of the definition written or the sender of
the request answered.

A line of a peer only states what the peer sends, a message in flight: what an external peer sends is the line's, and
what a running peer sends is its run's, which must equal the line. Every message between running services reaches its
receiver only by a line of the network.
-/
inductive Line where
  /--
  A request to `target`'s service from the client, which reaches its running receiver directly, or from the peer
  `peer`, in flight. With `sameIdAs`, the client's request has the id of the request of that line.
  -/
  | request (peer : Option String) (kind : RequestType) (target : Spec.Ref) (input : Template)
      (sameIdAs : Option Nat)
  /--
  The end of the subscription that line `subscription` opened: from the client, which reaches its receiver directly, or
  from the peer `peer`, in flight.
  -/
  | unsubscribe (peer : Option String) (subscription : Nat)
  /-- The client sends the request of line `line` again with the same id. -/
  | resend (line : Nat)
  /-- The user operates `control` of the screen instance `screen`. -/
  | operate (screen : Fact) (control : String) (payload : Template)
  /-- The user looks at the screen instance `screen`; Then states what it offers at this point. -/
  | look (screen : Fact)
  /--
  The peer `peer` answers the request `request`, which it received: an external peer once, or each time for a
  subscription, and a running peer as its run did.
  -/
  | answer (peer : String) (request : Fact) (answer : Template)
  /--
  The peer `peer` emits `event`, the result of the request `resultOf` or of none, to every running service that
  receives it.
  -/
  | emit (peer : String) (event : Spec.Ref) (payload : Template) (resultOf : Option Fact)
  /-- The external peer `peer` never answers the request `request`, which it received. -/
  | leaveUnanswered (peer : String) (request : Fact)
  /-- The network delivers the message `message` to its receiver. -/
  | deliver (message : Fact)
  /-- The network delivers the delivered message `message` again, with the same id. -/
  | redeliver (message : Fact)
  /-- The network loses the message `message`: its receiver never gets it, and nothing tells its sender. -/
  | lose (message : Fact)
  /--
  The network fails to deliver the request `message`: its receiver never gets it, and its sender gets the transport's
  answer, rejected as unavailable.
  -/
  | refuse (message : Fact)
  /-- The message `message` is undelivered at the end. -/
  | leaveInFlight (message : Fact)
  /--
  The clock advances to `time`, and every running service fires its deadlines due by then; a tie of a service is
  internal to it (chooseDeadline).
  -/
  | «at» (time : Time)
  /-- The host restarts the own service, which reopens its screens as new instances. -/
  | restart
deriving Repr, Inhabited

derive_wire Line tag "type" skip_serializing_none

/-- The values that the line writes: a request's input, an operation's payload, an answer, an event's payload. -/
def Line.written : Line → List Template
  | .request _ _ _ input _ => [input]
  | .operate _ _ payload => [payload]
  | .answer _ _ a => [a]
  | .emit _ _ payload _ => [payload]
  | _ => []

/-- The handles that the line names. -/
def Line.facts : Line → List Fact
  | .operate f _ _ | .look f | .answer _ f _ | .leaveUnanswered _ f | .deliver f | .redeliver f | .lose f | .refuse f
  | .leaveInFlight f => [f]
  | .emit _ _ _ resultOf => resultOf.toList
  | _ => []

/-- The picks of the line's handles and of the handles that its written values read, at any depth. -/
def Line.picks (l : Line) : List Template :=
  l.facts.flatMap Fact.picks ++ l.written.flatMap Template.picks

end Tazuna.Scenario
