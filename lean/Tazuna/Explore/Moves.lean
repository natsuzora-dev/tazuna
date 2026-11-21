import Tazuna.Explore.Enabled
import Tazuna.Spec.Domains
import Tazuna.Sim.Run

/-!
The moves that explore appends after a scenario's lines, all facing the own service. Enumeration has two layers: the
slots that the world enables (slots), and the moves that values fill each slot with (fill).
-/

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Spec.Domains Tazuna.Service Tazuna.Sim Tazuna.Scenario

/-- The lines of one step of explore, which a path appends together: a message stated and the line delivering it. -/
abbrev Move := List Scenario.Line

/-- A kind of move that the world enables, before values fill it. -/
inductive Slot where
  /-- The external receiver of `message` answers it; `awaiting` is the own service's pending request it answers. -/
  | answer (awaiting : Awaiting) (message : Message)
  /-- The clock moves to `time`. -/
  | «at» (time : Time)
  /-- The user operates an open screen as `operation` allows. -/
  | operate (operation : Operation)
  /-- The client ends the subscription that line `line` opened. -/
  | unsubscribe (line : Nat)
  /-- The client sends a request to the own command or query `definition`, and for a query also subscribes to it. -/
  | request (definition : Spec.Ref) (query : Bool)
  /-- The external peer `peer` emits `event`, which the own service receives. -/
  | emit (peer : String) (event : Spec.Ref)
  | restart
deriving Inhabited

/-- What explore reads besides the world: the scenario, the lines so far, and the own service's declared domains. -/
structure Explored where
  sc : Scenario
  lines : List Scenario.Line
  domains : List Spec.Domain

def Explored.own (x : Explored) : String := x.sc.service

/-- The world that explore reads at the explored path `x`: the scenario run from `start` with the path's lines. -/
def Explored.world {m : Type → Type} [Monad m] [MonadNote m] [MonadActing m] (spec : Spec.Structure)
    (fsOf : String → Functions m) (start : World) (x : Explored) : m World :=
  execute spec fsOf start { x.sc with lines := x.lines }

def Explored.externals (x : Explored) : List String :=
  x.sc.given.peers.filterMap fun p => if p.peer == .external then some p.service else none

/-- Whether the own service sent an end of the subscription `id`. -/
def ended (w : World) (own : String) (id : LineId) : Bool :=
  (w.state own).lines.toList.any fun l => l.dir == .out && match l.body with
    | .unsubscribe to => to == id
    | _ => false

def isRequest (msg : Message) : Bool :=
  match msg.body with
  | .command .. | .query .. | .subscribe .. => true
  | _ => false

/-- Whether `msg` is the own service's request `id` to an external peer, which has not answered it for good. -/
def awaits (w : World) (own : String) (id : LineId) (msg : Message) : Bool :=
  msg.sender == own && msg.id == id && (msg.status == .inFlight || msg.status == .delivered) &&
    w.role msg.receiver == some .external && isRequest msg

def isUnsubscribeOf (i : Nat) : Scenario.Line → Bool
  | .unsubscribe _ j => j == i
  | _ => false

/-- Whether line `l`, at `i` of `lines`, opened a client subscription to the own service that no line ended. -/
def openSubscription (own : String) (lines : List Scenario.Line) (l : Scenario.Line) (i : Nat) : Bool :=
  match l with
  | .request none .subscribe target _ _ => target.service == own && !lines.any (isUnsubscribeOf i)
  | _ => false

/-- The clock lines one millisecond before and at the next deadline, not before now. -/
def times (w : World) (e : Enabled) : List Time :=
  match e.nextDeadline with
  | none => []
  | some d => [d - 1, d].filter (w.now ≤ ·)

/--
The slots after `w`: an answer to each request the own service awaits from an external peer, the clock just before and
at the next deadline, each operation of an open screen, the end of each client subscription, a request to each own
command and query, each event of an external peer that the own service receives, and a restart. A running peer's
messages stay as the scenario left them.
-/
def slots (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) (e : Enabled) : List Slot :=
  let own := x.own
  (e.awaiting.filterMap fun a =>
      if ended w own a.id then none else (w.messages.toList.find? (awaits w own a.id)).map (.answer a)) ++
    (times w e).map .at ++
    e.operations.map .operate ++
    (x.lines.zipIdx.filterMap fun (l, i) => if openSubscription own x.lines l i then some (.unsubscribe i) else none) ++
    spec.definitions.filterMap (fun d =>
      if d.service != own then none else match d.body with
        | .command _ => some (.request d.ref false)
        | .query _ => some (.request d.ref true)
        | _ => none) ++
    spec.definitions.filterMap (fun d => match d.body with
      | .event _ => if x.externals.contains d.service && st.receives.contains d.ref then some (.emit d.service d.ref)
        else none
      | _ => none) ++
    [.restart]

def literal (v : Value) : Template := { value := v }

/-- The handle of the request that `msg` carries, naming its whole input. -/
def requestFact? (msg : Message) : Option Fact :=
  match msg.body with
  | .command target input => some (.request msg.origin .command target (some (literal input)))
  | .query target input => some (.request msg.origin .query target (some (literal input)))
  | .subscribe target input => some (.request msg.origin .subscribe target (some (literal input)))
  | _ => none

/-- The answer that rejects a request with `kind`, naming `reason`. -/
def rejectedAnswer (kind : RejectionKind) (reason : Option String) : Value :=
  ToValue.toValue (Answer.rejected { kind, reason })

/-- The answer that a fulfilled query or accepted command gives with `output`, written only when it has one. -/
def answerOf (query : Bool) (hasOutput : Bool) (output : Value) : Value :=
  if query then .obj [("result", .str "fulfilled"), ("output", output)]
  else if hasOutput then .obj [("result", .str "accepted"), ("output", output)]
  else .obj [("result", .str "accepted")]

/-- The move that answers `request` with `answer`, delivering the request first when `delivering`. -/
def answerMove (receiver : String) (request : Fact) (answer : Value) (delivering : Bool) (k : Nat) : Move :=
  if delivering then [.deliver request, .answer receiver request (literal answer), .deliver (.line (k + 1))]
  else [.answer receiver request (literal answer), .deliver (.line k)]

def requestMoves (definition : Spec.Ref) (query : Bool) (v : Value) : List Move :=
  if query then [[.request none .query definition (literal v) none], [.request none .subscribe definition (literal v) none]]
  else [[.request none .command definition (literal v) none]]

def emitMove (own peer : String) (event : Spec.Ref) (k : Nat) (v : Value) : Move :=
  [.emit peer event (literal v) none, .deliver (.event (.line k) event none (some own))]

variable {m : Type → Type} [Monad m] [MonadNote m]

/-- The `explore()` of `service`, which load guarantees for a service with scenarios (Malformed.missingExplore). -/
def exploreOf (spec : Spec.Structure) (service : String) : m Spec.Explore :=
  expectFound s!"explore of {service}" (spec.explores.find? (·.service == service))

def requestOf (msg : Message) : m Fact := expectFound s!"request of {msg.id.text}" (requestFact? msg)

/-- How a command or query answers: fulfilled when it is a query, else accepted, with output when it has an output. -/
structure AnswerShape where
  query : Bool
  output : Option Value
deriving Inhabited

def targetOf (st : Service) (target : Spec.Ref) : m AnswerShape := do
  match ← expectFound s!"definition {repr target}" (st.body? target) with
  | .command c => pure { query := false, output := c.output }
  | .query q => pure { query := true, output := q.output }
  | _ => do MonadNote.note (.bug s!"{repr target} is no command or query"); pure default

def openedOf (x : Explored) (w : World) (o : Operation) : m Sim.Opened :=
  expectFound s!"opening of {repr o.id}" (w.opened.reverse.find? fun s => s.service == x.own && s.id == o.id)

/--
The tree of `schema` under the declared domains (rootTree). Check reports a node of a move schema that no domain names
and whose type is not finite (Illegal.undeclaredDomain), so an undeclared schema here is a bug.
-/
def Explored.tree (st : Service) (x : Explored) (schema : Schema) : m Tree :=
  match st.schemaOf schema with
  | none => do MonadNote.note (.bug s!"no schema {repr schema}"); pure default
  | some json =>
    match rootTree (domainOf x.domains schema) json with
    | .ok t => pure t
    | .error paths => do MonadNote.note (.bug s!"no domain of {repr schema} at {repr paths}"); pure default

/--
The values of `schema` that explore may write: its JSON Schema has no node that no domain names and whose type is not
finite, and the declared domains and the finite types admit the value (Admitted).
-/
def Explored.Admits (st : Service) (x : Explored) (schema : Schema) (v : Value) : Prop :=
  ∃ json t, st.schemaOf schema = some json ∧ rootTree (domainOf x.domains schema) json = .ok t ∧
    Admitted (domainOf x.domains schema) (defsOf json) json [] v

/-- The rejections of kind `kind`: one per reason in `reasons` for requires, which decodedAnswer checks, else one. -/
def rejections (reasons : List String) (kind : RejectionKind) : List Value :=
  if kind == .requires then reasons.map (rejectedAnswer kind ∘ some) else [rejectedAnswer kind none]

/--
The answers to a request: each output that the output tree gives (one answer without output when the target has none),
then the rejections of each kind in `kinds` that does not blame the sender (blamesSender), since the own service checks
the input of each request and gives it an id it never used (explored_sent_ids_distinct), a requires rejection once per
reason in `reasons`.
-/
def answers (query : Bool) (outputs : Option Tree) (kinds : List RejectionKind) (reasons : List String) : List Value :=
  (match outputs with
    | none => [answerOf query false (.obj [])]
    | some t => t.values.map (answerOf query true)) ++
  (kinds.filter (!·.blamesSender)).flatMap (rejections reasons)

/--
The moves that values fill `slot` with: for an answer, one per value of the target's output tree, then the rejections
that the target may give (answers); for a request, an operation without offers, and an event, one per value of the
schema's tree; for an operation with offers, one per offered payload.
-/
def fill (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) : Slot → m (List Move)
  | .answer a msg => do
    let request ← requestOf msg
    let target : Spec.Ref := { service := a.target, name := a.name }
    let shape ← targetOf st target
    let outputs ← match shape.output with
      | none => pure none
      | some _ => some <$> x.tree st (.output target)
    pure ((answers shape.query outputs (spec.rejectionKinds x.own target) (spec.rejectionReasons target)).map fun answer =>
      answerMove msg.receiver request answer (msg.status == .inFlight) x.lines.length)
  | .at t => pure [[.at { text := renderTime t, time := t }]]
  | .operate o => do
    let opened ← openedOf x w o
    let screen := st.ref o.screen
    let payloads ← match o.payloads with
      | some ps => pure ps
      | none => do pure (← x.tree st (.control screen o.control)).values
    pure (payloads.map fun p => [.operate (.screen opened.origin screen) o.control (literal p)])
  | .unsubscribe i => pure [[.unsubscribe none i]]
  | .request d query => do pure ((← x.tree st (.input d)).values.flatMap (requestMoves d query))
  | .emit peer event => do pure ((← x.tree st (.payload event)).values.map (emitMove x.own peer event x.lines.length))
  | .restart => pure [[.restart]]

/-- The moves after `w`, which enables `e`: each slot filled, in slot order. -/
def moves (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) (e : Enabled) : m (List Move) := do
  pure (← (slots spec st x w e).mapM (fill spec st x w)).flatten

/--
The condition under which the world `w`, which enables `e`, enables a slot: an answer answers a request the own service
awaits from an external peer (the first message of it, since its ids are distinct: explored_sent_ids_distinct) and has
not ended, a clock move is one of `times`, an operation is one that `e` lists, an end names a client subscription that
no line ended, a request names an own command or query, an event is one that an external peer emits and the own service
receives.
-/
def Slot.Enabled (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) (e : Enabled) : Slot → Prop
  | .answer a msg => a ∈ e.awaiting ∧ w.messages.toList.find? (awaits w x.own a.id) = some msg ∧
      ended w x.own a.id = false
  | .at t => t ∈ times w e
  | .operate o => o ∈ e.operations
  | .unsubscribe i => ∃ l, (l, i) ∈ x.lines.zipIdx ∧ openSubscription x.own x.lines l i = true
  | .request r query => ∃ d ∈ spec.definitions, d.ref = r ∧ d.service = x.own ∧
      ((∃ c, d.body = .command c) ∧ query = false ∨ (∃ q, d.body = .query q) ∧ query = true)
  | .emit peer event => ∃ d ∈ spec.definitions, d.ref = event ∧ d.service = peer ∧ (∃ b, d.body = .event b) ∧
      x.externals.contains peer = true ∧ st.receives.contains event = true
  | .restart => True

/-- The shape of a move that fills a slot: the lines it appends, with only the written values open. -/
def Slot.Realizes (x : Explored) : Slot → Move → Prop
  | .answer _ msg, mv => ∃ request answer delivering, mv = answerMove msg.receiver request answer delivering x.lines.length
  | .at t, mv => mv = [.at { text := renderTime t, time := t }]
  | .operate o, mv => ∃ screen payload, mv = [.operate screen o.control (literal payload)]
  | .unsubscribe i, mv => mv = [.unsubscribe none i]
  | .request r query, mv => ∃ v, mv ∈ requestMoves r query v
  | .emit peer event, mv => ∃ v, mv = emitMove x.own peer event x.lines.length v
  | .restart, mv => mv = [.restart]

/--
The moves that fill a slot, with the values that the declared domains and the finite types admit (Explored.Admits): an
answer with an output that the output schema admits (or without output, for a target without one) or a rejection of a
kind that the target may give and that does not blame the sender (explored_sent_ids_distinct), a requires rejection
with a reason that the target lists; an operation with an offered payload, or one that the control's schema admits when
the operation lists no offers; a request with an input and an event with a payload that their schemas admit.
-/
def Slot.Fills (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) : Slot → Move → Prop
  | .answer a msg, mv =>
    let target : Spec.Ref := { service := a.target, name := a.name }
    let shape := Id.run (targetOf st target)
    ∃ answer, mv = answerMove msg.receiver (Id.run (requestOf msg)) answer (msg.status == .inFlight) x.lines.length ∧
      ((shape.output = none ∧ answer = answerOf shape.query false (.obj [])) ∨
        (shape.output.isSome ∧ ∃ o, x.Admits st (.output target) o ∧ answer = answerOf shape.query true o) ∨
        ∃ k ∈ spec.rejectionKinds x.own target, k.blamesSender = false ∧
          answer ∈ rejections (spec.rejectionReasons target) k)
  | .at t, mv => mv = [.at { text := renderTime t, time := t }]
  | .operate o, mv => ∃ p,
      (match o.payloads with
        | some ps => p ∈ ps
        | none => x.Admits st (.control (st.ref o.screen) o.control) p) ∧
      mv = [.operate (.screen (Id.run (openedOf x w o)).origin (st.ref o.screen)) o.control (literal p)]
  | .unsubscribe i, mv => mv = [.unsubscribe none i]
  | .request r query, mv => ∃ v, x.Admits st (.input r) v ∧ mv ∈ requestMoves r query v
  | .emit peer event, mv => ∃ v, x.Admits st (.payload event) v ∧ mv = emitMove x.own peer event x.lines.length v
  | .restart, mv => mv = [.restart]

end Tazuna.Explore
