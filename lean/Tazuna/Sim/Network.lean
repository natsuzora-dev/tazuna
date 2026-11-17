import Tazuna.Scenario.Given
import Tazuna.Sim.Participant
import Tazuna.Sim.InvalidScenario

/-!
The world of a simulation: the running services, each with its state, and the network, a list of messages that each
running service sent to another service. A message stays in flight until a line delivers or loses it.
-/

namespace Tazuna.Sim

open Tazuna.Data Tazuna.Service
open Tazuna.Scenario (Origin)

/-- How a service takes part in a simulation. -/
inductive Role where
  | own
  | run
  | external
  | skip
deriving DecidableEq, Repr, Inhabited

def Role.running : Role → Bool
  | .own | .run => true
  | _ => false

inductive Status where
  | inFlight
  | delivered
  | lost
  /-- The external receiver never answers the request. -/
  | unanswered
  /-- The receiver does not run, so the message is not delivered. -/
  | discarded
deriving DecidableEq, Repr, Inhabited

/--
A message: the line `body` that `sender` wrote with id `id` while `origin` was processed. `channel` is the request whose
channel carries it, by its receiver's id: a request's own, an answer's or an end's request, an event's resultOf, or none
for an event without resultOf. Messages between the same sender and receiver on the same channel arrive in sending
order (FIFO), as a connection delivers them.
-/
structure Message where
  sender : String
  receiver : String
  id : String
  body : LineBody
  origin : Origin
  channel : Option String
  status : Status
deriving Repr, Inhabited

/-- The message as a report names it: its sender, its receiver, the sender's id of it, and what caused it. -/
def Message.describe (m : Message) : Value :=
  .obj [("sender", .str m.sender), ("receiver", .str m.receiver), ("id", .str m.id), ("origin", ToValue.toValue m.origin)]

def Message.sameChannel (m n : Message) : Bool :=
  m.sender == n.sender && m.receiver == n.receiver && m.channel == n.channel

/--
The lines `from` to `to` (exclusive) that `service` wrote while `origin` was processed, and the steps `stepsFrom` to
`stepsTo` (exclusive) that it took.
-/
structure Span where
  origin : Origin
  service : String
  «from» : Nat
  to : Nat
  stepsFrom : Nat
  stepsTo : Nat
deriving Repr, Inhabited

/-- The screen instance `resource` of chart `chart` of `service` that opened while `origin` was processed. -/
structure Opened where
  origin : Origin
  service : String
  chart : String
  resource : String
deriving Repr, Inhabited

/--
The request that the client or a peer line `line` sent: its receiver, the receiver's id of it, and the place of its
`in` line in the receiver's trace.
-/
structure Sent where
  line : Nat
  receiver : String
  id : String
  position : Nat
deriving Repr, Inhabited

structure World where
  now : Time
  roles : List (String × Role)
  /-- The running services, the own service first. -/
  services : List (String × Service)
  states : List (String × State)
  messages : Array Message := #[]
  spans : List Span := []
  opened : List Opened := []
  sent : List Sent := []
  /-- The message that each line carried, by line. -/
  carried : List (Nat × Nat) := []
  /-- The messages that leaveInFlight lines name: the line, and the message. -/
  leftInFlight : List (Nat × Nat) := []
  /-- The number of messages of each definition that each external peer sent, by `<peer>.<name>`: their ids count. -/
  counts : List (String × Nat) := []
  violations : List InvalidScenario := []
  halted : Option InvalidScenario := none
  /--
  The steps that the internal queue of `service` takes first while `origin` is processed, as State.stepOrder: the
  order of steps that test's search runs, which no line writes.
  -/
  stepOrders : List (Origin × String × List StepName) := []
  /--
  The message that each handle of a group of `requests` names, by group (Fact.group?): handle `j` names the group's
  message at place `j` of the list, counted in sending order. A group without an entry has each handle name the message
  at its own place. The assignment that test's search runs, which no line writes.
  -/
  assignments : List (Scenario.Fact × List Nat) := []
deriving Inhabited

def World.state (w : World) (service : String) : State := (w.states.lookup service).getD {}

def World.role (w : World) (service : String) : Option Role := w.roles.lookup service

/-- Whether no later line takes place: the simulation or a running service halted. -/
def World.stopped (w : World) : Bool := w.halted.isSome || w.states.any (·.2.halted.isSome)

def World.report (w : World) (r : InvalidScenario) : World :=
  if r.halts then { w with halted := some r } else { w with violations := w.violations ++ [r] }

/-- The world with `r`, which stops nothing: a report of Given or of an expectation of Then. -/
def World.note (w : World) (r : InvalidScenario) : World := { w with violations := w.violations ++ [r] }

def World.setStatus (w : World) (k : Nat) (status : Status) : World :=
  { w with messages := w.messages.modify k fun m => { m with status } }

def screensOf (s : State) : List (String × String) :=
  (s.machines.filter (·.chart.screen)).map fun i => (i.chart.name, i.resource)

/-- The service that the request `id` of the lines `lines` went to. -/
def targetOf (service : String) (lines : Array Line) (id : String) : Option String :=
  lines.toList.findSome? fun l =>
    match l.dir, l.body with
    | .out, .command name _ | .out, .query name _ | .out, .subscribe name _ =>
      if l.id == id then some (Spec.Ref.ofTraceName service name).service else none
    | _, _ => none

/-- The world with a message from `sender` to `receiver`, kept in flight, discarded, or reported as unlisted. -/
def World.post (w : World) (o : Origin) (sender receiver : String) (l : Line) (channel : Option String) : World :=
  let line := match o with
    | .line i => some i
    | .startup => none
  match w.role receiver with
  | none => w.report (.unlistedService line receiver)
  | some role =>
    let status := if role == .skip then .discarded else .inFlight
    let msg : Message := { sender, receiver, id := l.id, body := l.body, origin := o, channel, status }
    { w with messages := w.messages.push msg }

/--
The world with the messages that the `out` lines `lines` of `service` send: a request to another service, an end of a
subscription, an answer to another service, and an event to each running service that receives it.
-/
def World.route (w : World) (o : Origin) (service : String) (lines : List Line) : World :=
  lines.foldl (init := w) fun w l =>
    if l.dir != .out || w.stopped then w else
    let own := receivedId service l.id
    match l.body with
    | .command name _ | .query name _ | .subscribe name _ =>
      let target := (Spec.Ref.ofTraceName service name).service
      if target == service then w else w.post o service target l (some own)
    | .unsubscribe to =>
      match targetOf service (w.state service).lines to with
      | some target => w.post o service target l (some (receivedId service to))
      | none => w
    | .answer to _ =>
      match senderOf? to with
      | some requester => w.post o service requester l (some to)
      | none => w
    | .event name _ resultOf =>
      w.services.foldl (init := w) fun w (r, st) =>
        if r != service && st.receives.contains (nameIn service r name) then w.post o service r l resultOf else w
    | _ => w

/--
A monad that is told whose processing runs, so that what the processing notes belongs to that running service: an
instrumented simulation keeps one Collect per participant. Any other monad ignores it.
-/
class MonadActing (m : Type → Type) where
  acting {α : Type} (service : String) (x : m α) : m α

instance (priority := low) {m : Type → Type} : MonadActing m := ⟨fun _ x => x⟩

/-- The state after a processing that took the steps of `order` first, with the entries it left unused reported. -/
def checkStepOrder (s : State) : State :=
  let t := { s with stepOrder := [] }
  if s.halted.isNone && !s.stepOrder.isEmpty then t.report (.invalidInput (.unusedStepOrder s.stepOrder)) else t

/-- The keyed entity of a running participant whose key form `<participant>/<e>-<n>` the string `x` has. -/
def World.keyEntity? (w : World) (x : String) : Option Spec.Ref :=
  w.services.findSome? fun (owner, st) =>
    (st.entities.find? fun e => !st.singles.contains e && Spec.isKeyOf s!"{owner}/{e}" x).map st.ref

/--
The least string, in code-point order, of the `out` lines `sent` and the records `records` that has a running
participant's key form (keyEntity?) and that no running participant created, with the entity: a spec computed it.
-/
def World.computedKey? (w : World) (sent : List Line) (records : Records) : Option (String × Spec.Ref) :=
  let strings := (sent.filter (·.dir == .out)).flatMap (·.body.content.strings) ++
    records.flatMap fun r => r.key.toList ++ r.value.strings
  let made := w.states.flatMap fun (_, s) => s.created.map (·.2)
  let computed := strings.filter fun x => !made.contains x && (w.keyEntity? x).isSome
  ((computed.mergeSort fun a b => decide (a ≤ b)).head?).bind fun x => (w.keyEntity? x).map (x, ·)

/--
The world with the computed key (computedKey?) that `service` sent in `sent` or holds in `records` reported, unless the
world halted already: one cause, one report.
-/
def World.checkComputed (w : World) (service : String) (sent : List Line) (records : Records) : World :=
  if w.halted.isSome then w else
  match w.computedKey? sent records with
  | some (key, entity) => w.report (.computedKey service key entity)
  | none => w

/--
The world after `service` processes what `f` gives it while `origin` is processed, taking first the steps of its entry
of `stepOrders`, which the processing uses up: its state, the span of lines and steps it wrote, the screens that opened, and the messages it sent.
Under `reopen`, as after a restart, every screen open after it opened anew.
-/
def World.act {m : Type → Type} [Monad m] [MonadActing m] (w : World) (fsOf : String → Functions m) (o : Origin)
    (service : String) (f : Service → Functions m → State → m State) (reopen : Bool := false) : m World := do
  match w.services.lookup service with
  | none => pure w
  | some st =>
    let s := w.state service
    let before := s.lines.size
    let stepsFrom := s.steps.size
    let screens := screensOf s
    let order := (w.stepOrders.find? fun (o', q, _) => o' == o && q == service).map (·.2.2)
    let t ← MonadActing.acting service (f st (fsOf service) { s with stepOrder := order.getD [] })
    let t := if order.isSome then checkStepOrder t else t
    let opened := ((screensOf t).filter fun x => reopen || !screens.contains x).map fun (chart, resource) =>
      { origin := o, service, chart, resource : Opened }
    let span : Span := { origin := o, service, «from» := before, to := t.lines.size, stepsFrom, stepsTo := t.steps.size }
    let w := { w with states := w.states.map fun (q, x) => if q == service then (q, t) else (q, x),
                      spans := w.spans ++ [span], opened := w.opened ++ opened,
                      stepOrders := w.stepOrders.filter fun (o', q, _) => !(o' == o && q == service) }
    let sent := (t.lines.extract before t.lines.size).toList
    pure ((w.route o service sent).checkComputed service sent t.records)

/-- The world after the message `k` arrives at its running receiver while `origin` is processed. -/
def World.deliver {m : Type → Type} [Monad m] [MonadNote m] [MonadActing m] (w : World) (fsOf : String → Functions m)
    (o : Origin) (k : Nat) : m World :=
  match w.messages[k]? with
  | none => pure w
  | some msg =>
    (w.setStatus k .delivered).act fsOf o msg.receiver fun st fs s => arriveFrom st fs s msg.sender msg.id msg.body

end Tazuna.Sim
