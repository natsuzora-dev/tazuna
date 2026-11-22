import Tazuna.Data.Group
import Tazuna.Data.Time
import Tazuna.Spec.Structure

namespace Tazuna.Sim

open Tazuna.Data

/--
What the simulation of a scenario reports about the scenario. `scenarioLine` is the line of When, from 0. A message is
named by its sender, its receiver, the sender's id of it, and its origin: the line, or the startup, whose processing
sent it.

Given is checked first, and each of its violations is given. After any of them, nothing begins. A violation of a line of
When stops the simulation, unless `halts` says otherwise, since later lines may depend on what the line did. An
expectation of Then never stops the others: each is evaluated, and what it reports belongs to it alone.
-/
inductive InvalidScenario where
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
  /--
  Given's record of `entity` with `key` of the running service `service` holds `written`, of the form of a key of
  `created` that a running service creates: a created key exists only once the run creates it.
  -/
  | writtenGivenKey (service entity : String) (key : Option String) (written : String) (created : Spec.Ref)
  /-- The record of `entity` clashes with an earlier record of Given: the same key, or the same unique values. -/
  | duplicateRecord (service entity : String) (key : Option String)
  /--
  The invariant `invariant` of the record of `entity` with `key`, or of the service when `entity` is none, fails on
  Given's records of `service`. `invariant` is none when the invariant throws.
  -/
  | brokenGivenInvariant (service : String) (entity key invariant : Option String)
  /-- No fact matches the handle `fact` that the line names. -/
  | unresolvedReference (scenarioLine : Nat) (fact : Value)
  /--
  The facts `candidates` that match the handle `fact` differ, so the line cannot act on each alike. The handle must name
  content that tells them apart. Equal messages are not ambiguous: a line acts on each of them.
  -/
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
  /-- The external peer's line emits `event`, which no running service's definitions receive. -/
  | unreceivedEvent (scenarioLine : Nat) (event : Spec.Ref)
  /-- The line refuses `message`, which is no request: only a request has an answer that can tell its sender. -/
  | unrefusable (scenarioLine : Nat) (message : Value)
  /-- The line needs `service` to take part in another way than Given says: running, external, or the own service. -/
  | wrongRole (scenarioLine : Nat) (service : String)
  /-- The line delivers, loses or refuses `message`, or a running peer's line states it, and it is not in flight. -/
  | notInFlight (scenarioLine : Nat) (message : Value)
  /--
  The line delivers `message` again, or its external receiver answers it or leaves it unanswered, and no line delivered
  it.
  -/
  | notDelivered (scenarioLine : Nat) (message : Value)
  /--
  The external peer answers the request `message` again, or leaves it unanswered after answering it. It is no
  subscription and has its answer.
  -/
  | repeatedAnswer (scenarioLine : Nat) (message : Value)
  /--
  The peer's line emits an event whose resultOf names the request `fact`, which `peer` did not receive: no line
  delivered it to `peer`.
  -/
  | unreceivedRequest (scenarioLine : Nat) (peer : String) (fact : Value)
  /--
  The line delivers `message` while `earlier`, which must arrive first (one channel, and not events of independent
  steps), is in flight. To deliver `message`, lose or refuse `earlier` first.
  -/
  | overtaking (scenarioLine : Nat) (message earlier : Value)
  /-- No message in flight from the running peer `peer` to the own service is the line's. -/
  | unpairedPeerLine (scenarioLine : Nat) (peer : String)
  /-- The clock line's time `at` is not later than `now`. -/
  | notLater (scenarioLine : Nat) («at» now : Time)
  /--
  A written value holds `key`, of the form of a key of `entity` that a running service creates: a scenario names a
  created key only through a handle.
  -/
  | writtenKey (scenarioLine : Nat) (key : String) (entity : Spec.Ref)
  /-- The line writes `created()` outside a running peer's request, answer or event, or in a handle's pick. -/
  | misplacedCreated (scenarioLine : Nat)
  /-- The running peer's answer `actual`, which the line delivers, is not the line's `expected`. -/
  | differentPeerAnswer (scenarioLine : Nat) (expected actual : Value)
  /-- The message `message` is undelivered at the end, and no leaveInFlight line names it. -/
  | leftInFlight (message : Value)
  /-- The message that the leaveInFlight line names is not undelivered at the end. -/
  | unusedInFlight (scenarioLine : Nat)
  /-- The leaveInFlight line names `message`, which an earlier leaveInFlight line names. -/
  | repeatedInFlight (scenarioLine : Nat) (message : Value)
  /-- The external peer received the request `message`, and no line answers it or leaves it unanswered. -/
  | awaitingAnswer (message : Value)
  /-- The offered expectation `expectation` names the line `scenarioLine`, which is no look line. -/
  | notALook (expectation scenarioLine : Nat)
  /--
  The emitted expectation `expectation` cannot fail: no contract lists an event of the own service, so what it compares
  is empty by construction.
  -/
  | vacuousExpectation (expectation : Nat)
  /-- The expectation `expectation` of Then, from 0, states `expected`, and the run gave `actual`. -/
  | unmetExpectation (expectation : Nat) (expected actual : Value)
deriving Repr, Inhabited


derive_group InvalidScenario

/--
Whether the report stops the simulation, which a line's report does when the scenario as written describes no run, or
not one run, from that line on: the line names what does not exist, or several things; states a message, delivery, or
time that cannot occur at that point (a malformed answer, a second answer, an overtaking delivery, an earlier time);
states again what an earlier line stated; or writes what only the run decides (a created key, `created()` out of
place). differentPeerAnswer
compares a message that did occur, so it stops nothing; the violations of Given end the simulation before any line, and
those of the end and of Then come after every line.
-/
def InvalidScenario.halts : InvalidScenario → Bool
  | .differentPeerAnswer .. | .leftInFlight .. | .unusedInFlight .. | .awaitingAnswer .. | .unmetExpectation ..
  | .notALook .. | .vacuousExpectation .. => false
  | .repeatedPeer .. | .unlistedPeer .. | .invalidRecord .. | .duplicateRecord .. | .brokenGivenInvariant .. => false
  | .missingRecord .. | .writtenGivenKey .. => false
  | _ => true

/--
Whether no spec that `tazuna check` passes can produce the violation: the DSL's types reject what it reports, check
reports it first as a Malformed kind, or only test's own step-order search writes the input that it checks. The
simulation keeps such kinds as the validation of its input, which tazuna's own data scenarios reach without types or
check. Explain leaves them out.
-/
def InvalidScenario.internal : InvalidScenario → Bool
  | .repeatedPeer .. | .missingRecord .. | .malformedValue .. | .unrefusable .. | .notALook .. | .misplacedCreated ..
  | .writtenKey .. | .writtenGivenKey .. => true
  | .unlistedPeer .. | .invalidRecord .. | .duplicateRecord .. | .brokenGivenInvariant .. | .unresolvedReference ..
  | .ambiguousReference .. | .missingOutput .. | .missingField .. | .unlistedService .. | .unreceivedEvent ..
  | .wrongRole .. | .notInFlight .. | .notDelivered .. | .repeatedAnswer .. | .unreceivedRequest .. | .overtaking ..
  | .unpairedPeerLine .. | .notLater .. | .differentPeerAnswer .. | .leftInFlight .. | .unusedInFlight ..
  | .repeatedInFlight .. | .awaitingAnswer .. | .vacuousExpectation .. | .unmetExpectation .. => false

end Tazuna.Sim
