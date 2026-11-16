import Tazuna.Scenario.Ref

namespace Tazuna.Scenario

open Tazuna.Data

inductive RequestType where
  | command
  | query
  | subscribe
deriving DecidableEq, Repr, Inhabited

derive_wire RequestType

/-- The deadline `deadline` of the running service `service`. -/
structure OrderEntry where
  service : String
  deadline : DeadlineId
deriving DecidableEq, Repr, Inhabited

derive_wire OrderEntry

/--
A line of a scenario's When, in written order. The sender is named by the line: the client and the user are outside
every service, a peer is named by its service, and the receiver is the owner of the definition written or the sender of
the request answered.
-/
inductive Line where
  /--
  A request to `target`'s service from the client, or from the running peer `peer`, whose run must have sent it. With
  `sameIdAs`, the request has the id of the request of that line.
  -/
  | request (peer : Option String) (kind : RequestType) (target : Syntax.Ref) (input : Template)
      (sameIdAs : Option Nat)
  /-- The end of the subscription that line `subscription` opened, from the client or the running peer `peer`. -/
  | unsubscribe (peer : Option String) (subscription : Nat)
  /-- The client sends the request of line `line` again with the same id. -/
  | resend (line : Nat)
  /-- The user operates `control` of the screen instance `screen`. -/
  | operate (screen : Fact) (control : String) (payload : Template)
  /-- The user looks at the screen instance `screen`; Then states what it offers at this point. -/
  | look (screen : Fact)
  /--
  The peer `peer` answers the request `request`: an external peer gives the answer, and a running peer's answer, which
  its run gave, is delivered and must be `answer`. A request in flight to a running peer never reaches its run, and the
  answer must be unavailable.
  -/
  | answer (peer : String) (request : Fact) (answer : Template)
  /--
  The peer `peer` emits `event`, the result of the request `resultOf` or of none: an external peer emits it to every
  running service that receives it, and a running peer's event, which its run emitted, is delivered to the own service.
  -/
  | emit (peer : String) (event : Syntax.Ref) (payload : Template) (resultOf : Option Fact)
  /-- The external peer `peer` never answers the request `request`. -/
  | leaveUnanswered (peer : String) (request : Fact)
  /-- The network delivers the message `message` to its running receiver. -/
  | deliver (message : Fact)
  /-- The network delivers the delivered message `message` again, with the same id. -/
  | redeliver (message : Fact)
  /-- The network loses the message `message`. -/
  | lose (message : Fact)
  /--
  The messages on the channel of `message`, either way between its sender and its receiver, that are undelivered at the
  end are in flight.
  -/
  | inFlight (message : Fact)
  /--
  The clock advances to `time`, and every running service fires its deadlines due by then; in a tie of a service, the
  next entry of `order` for that service names the deadline that fires.
  -/
  | «at» (time : DateTime) (order : List OrderEntry)
  /-- The host restarts the own service. -/
  | restart
deriving Repr, Inhabited

derive_wire Line tag "type" skip_serializing_none

end Tazuna.Scenario
