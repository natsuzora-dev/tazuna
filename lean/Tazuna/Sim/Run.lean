import Tazuna.Sim.Given
import Tazuna.Sim.Resolve

/-!
The forward run of a scenario: every running service begins at the start from its Given records, each line of When
takes place in written order, and then the undelivered messages and the expectations of Then are checked. Nothing
waits for a later line, and nothing is searched.
-/

namespace Tazuna.Sim

open Tazuna.Data Tazuna.Semantics
open Tazuna.Scenario (Fact Origin Template RequestType Expectation GivenRecord Peer)

variable {m : Type → Type} [Monad m] [MonadNote m] [MonadActing m]

def World.attempt {α : Type} (w : World) (r : Except Report α) (k : α → m World) : m World :=
  match r with
  | .error e => pure (w.report e)
  | .ok a => k a

def World.resolving {α : Type} (w : World) (r : ExceptT Report m α) (k : α → m World) : m World := do
  match ← r.run with
  | .error e => pure (w.report e)
  | .ok a => k a

/-- The answer with its output as the simulation compares it for the output of `target`. -/
def comparedAnswer (fs : Functions m) (target : String) (a : Answer) : m Value := do
  match a with
  | .accepted (some o) => pure (ToValue.toValue (Answer.accepted (some (← comparedOr fs (.output target) o))))
  | .fulfilled o => pure (ToValue.toValue (Answer.fulfilled (← comparedOr fs (.output target) o)))
  | a => pure (ToValue.toValue a)

/-- The written answer `v` as the simulation compares it, or as it is when it is no answer. -/
def comparedAnswerValue (fs : Functions m) (target : String) (v : Value) : m Value := do
  match (FromValue.fromValue v : Except String Answer) with
  | .ok a => comparedAnswer fs target a
  | .error _ => pure v

/-- The first string of `v` of the form `<participant>/<key>` of a key of an entity of a running participant. -/
def World.writtenKey? (w : World) (v : Value) : Option (String × Syntax.Ref) :=
  v.strings.findSome? fun x =>
    match x.splitOn "/" with
    | [owner, key] =>
      (w.services.lookup owner).bind fun st =>
        (st.entities.find? fun e => !st.singles.contains e && Syntax.isKeyOf e key).map fun e => (x, st.ref e)
    | _ => none

/--
What the values that a line or an expectation of `line` writes report: `created()` that is not `allowed` at the top or
that a pick writes, or a created key written as a literal.
-/
def World.checkWritten (w : World) (line : Nat) (written picks : List Template) (allowed : Bool) : Option Report :=
  if picks.any (·.created) || (!allowed && written.any (·.created)) then some (.misplacedCreated line)
  else ((written ++ picks).findSome? fun t => w.writtenKey? t.value).map fun (key, e) => .writtenKey line key e

def requestName? : LineBody → Option String
  | .command name _ | .query name _ | .subscribe name _ => some name
  | _ => none

/-- The world with what the line `i` processed by `service` wrote first as an `in` line recorded as its request. -/
def World.recordSent (w : World) (i : Nat) (service : String) (before : Nat) : World :=
  match ((w.state service).lines.toList.zipIdx.drop before).find? (·.1.dir == .in) with
  | some (l, position) => { w with sent := w.sent ++ [{ line := i, receiver := service, id := l.id, position }] }
  | none => w

def requestOf (type : RequestType) (name : String) (id : Option String) (v : Value) :
    Service → Functions m → State → m State :=
  fun st fs s => match type with
    | .command => send st fs s name id v
    | .query => call st fs s name id v
    | .subscribe => subscribe st fs s name id v

def bodyOf (type : RequestType) (name : String) (v : Value) : LineBody :=
  match type with
  | .command => .command name v
  | .query => .query name v
  | .subscribe => .subscribe name v

/-- The world after the client's request of line `i`, with the id of the request of line `sameIdAs`, if any. -/
def World.clientRequest (w : World) (fsOf : String → Functions m) (i : Nat) (type : RequestType)
    (target : Syntax.Ref) (input : Template) (sameIdAs : Option Nat) : m World := do
  let receiver := target.service
  if !((w.role receiver).any (·.running)) then return w.report (.wrongRole i receiver)
  w.resolving (w.fill fsOf i input) fun v => do
    let given ← match sameIdAs with
      | none => pure (some none)
      | some j => pure ((w.sentBy j).map (some ·.id))
    let some id := given | return w.report (.unresolvedReference i (ToValue.toValue (Fact.line (sameIdAs.getD 0))))
    let before := (w.state receiver).lines.size
    let w ← w.act fsOf (.line i) receiver (requestOf type target.name id v)
    pure (w.recordSent i receiver before)

/-- The world with the message `k` carried by line `i`. -/
def World.carry (w : World) (i k : Nat) : World := { w with carried := w.carried ++ [(i, k)] }

/-- The world with the message that the external peer's line `i` sends, in flight to its running receiver. -/
def World.stated (w : World) (i : Nat) (msg : Message) : World :=
  if !((w.role msg.receiver).any (·.running)) then w.report (.wrongRole i msg.receiver)
  else { w with messages := w.messages.push msg }.carry i w.messages.size

/-- The world with the next id of the messages of `name` that the external peer `peer` sends. -/
def World.nextId (w : World) (peer name : String) : World × String :=
  let key := s!"{peer}.{name}"
  let n := (w.counts.lookup key).getD 0 + 1
  ({ w with counts := (key, n) :: w.counts.filter (·.1 != key) }, s!"{name}#{n}")

/--
Whether the running peer's message carries `actual` equal to the line's `expected`, compared for `schema` of the peer,
where each created hole of `t` holds a key that the peer created and no handle names.
-/
def World.sameValue (w : World) (fs : Functions m) (schema : Schema) (peer : String) (t : Template)
    (expected actual : Value) : m Bool := do
  let e := markCreated t expected
  let masked := w.maskCreated peer t expected actual
  pure ((← comparedOr fs schema e).canonical == (← comparedOr fs schema masked).canonical)

/--
The message in flight from the running peer `peer` that the line `i` states, among those that `fits` accepts and no
earlier line stated: of each channel the oldest, which FIFO delivers first; the only such one, or the report of none or
of several channels.
-/
def World.peerMessage (w : World) (i : Nat) (peer : String) (fits : Message → m Bool) : m (Except Report Nat) := do
  let found ← w.messages.toList.zipIdx.filterM fun (msg, k) =>
    if msg.status == .inFlight && msg.sender == peer && !w.carried.any (·.2 == k) then fits msg else pure false
  let oldest := found.filter fun (msg, k) => !found.any fun (n, j) => j < k && n.sameChannel msg
  pure (match oldest with
    | [(_, k)] => .ok k
    | [] => .error (.unpairedPeerLine i peer)
    | several => .error (.ambiguousPeerLine i peer (several.map (·.1.describe))))

/--
The world after the message `k` reaches its receiver by line `i`: a running receiver processes it, and a request that
it processes is recorded as the request of each line that carried it.
-/
def World.deliverCarried (w : World) (fsOf : String → Functions m) (i k : Nat) : m World := do
  let w := w.carry i k
  let some msg := w.messages[k]? | return w
  if !((w.role msg.receiver).any (·.running)) then return w.setStatus k .delivered
  let before := (w.state msg.receiver).lines.size
  let w ← w.deliver fsOf (.line i) k
  if (requestName? msg.body).isNone then return w
  let carriers := (w.carried.filter (·.2 == k)).map (·.1)
  pure (carriers.foldl (init := w) fun w l => if (w.sentBy l).isSome then w else w.recordSent l msg.receiver before)

/--
The world after line `i` delivers the in-flight message `k`, unless an earlier message on its channel is in flight,
which FIFO delivers first.
-/
def World.deliverInOrder (w : World) (fsOf : String → Functions m) (i k : Nat) : m World :=
  match w.messages[k]? with
  | none => pure w
  | some msg =>
    match (w.messages.toList.take k).find? fun n => n.status == .inFlight && n.sameChannel msg with
    | some earlier => pure (w.report (.overtaking i msg.describe earlier.describe))
    | none => w.deliverCarried fsOf i k

/-- The id by which a peer names the request that the handle `fact` of line `i` names. -/
def World.requestId (w : World) (fsOf : String → Functions m) (i : Nat) (fact : Fact) : ExceptT Report m String :=
  match fact with
  | .line j =>
    match w.sentBy j with
    | some s => pure s.id
    | none => throw (.unresolvedReference i (ToValue.toValue fact))
  | _ => do
    let k ← w.messageOf fsOf i fact
    match w.messages[k]? with
    | some msg => pure (receivedId msg.sender msg.id)
    | none => throw (.unresolvedReference i (ToValue.toValue fact))

def offeredAt (st : Service) (fs : Functions m) (s : State) (o : Opened) (control : String) (payload : Value) :
    m Bool := do
  match ← fs.parse (.control o.chart control) payload with
  | .ok (some decoded) =>
    match ← acceptsOperation fs st s o.chart control decoded with
    | .ok (.ok top) => pure (top.resource == o.resource)
    | _ => pure false
  | _ => pure false

/--
The running service after the deadlines due by `time` fire, ties ordered by `order`, and the clock's time line arrives,
as the input that verify gives the implementation.
-/
def fireTo (time : Time) (order : List DeadlineId) : Service → Functions m → State → m State :=
  fun st fs s => do
    let s ← fireDue st fs time Limit.dueDeadlines.max none
      { s with deadlineOrder := order, tieOrderRequired := true }
    let s := { s.checkDeadlineOrder with now := max s.now time, tieOrderRequired := false }
    pure (if s.halted.isSome then s else (s.write .in none .time).1)

/-- Whether an answer to the request `to` from `sender` is among the messages. -/
def World.answered (w : World) (sender to : String) : Bool :=
  w.messages.any fun n => n.sender == sender && n.channel == some to && match n.body with
    | .answer .. => true
    | _ => false

/-- The world after line `i` of the scenario of the own service `own`, which `expectations` follow. -/
def World.take (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line)
    (expectations : List Expectation) (i : Nat) : Scenario.Line → m World
  | .request none type target input sameIdAs => w.clientRequest fsOf i type target input sameIdAs
  | .request (some peer) type target input _ => do
    match w.role peer with
    | some .external =>
      w.resolving (w.fill fsOf i input) fun v => do
        let name := target.traceName peer
        let (w, id) := w.nextId peer target.name
        pure (w.stated i { sender := peer, receiver := target.service, id, body := bodyOf type name v,
                           origin := .line i, channel := some (receivedId peer id), status := .inFlight })
    | some .run =>
      w.resolving (w.fill fsOf i input) fun v => do
        let name := target.traceName peer
        let fits (msg : Message) : m Bool :=
          if msg.body.requestType? == some type && requestName? msg.body == some name &&
              msg.receiver == target.service then
            w.sameValue (fsOf peer) (.input name) peer input v ((msg.body.value?).getD .null)
          else pure false
        match ← w.peerMessage i peer fits with
        | .error e => pure (w.report e)
        | .ok k => pure (w.carry i k)
    | _ => pure (w.report (.wrongRole i peer))
  | .unsubscribe none subscription => do
    let some s := w.sentBy subscription
      | return w.report (.unresolvedReference i (ToValue.toValue (Fact.line subscription)))
    w.act fsOf (.line i) s.receiver fun st fs t => endSubscription st fs t s.id
  | .unsubscribe (some p) subscription =>
    w.resolving (w.messageOf fsOf i (.line subscription)) fun k => do
      let some sub := w.messages[k]? | return w
      match w.role p with
      | some .external =>
        let (w, id) := w.nextId p "unsubscribe"
        pure (w.stated i { sender := p, receiver := sub.receiver, id, body := .unsubscribe sub.id, origin := .line i,
                           channel := some (receivedId p sub.id), status := .inFlight })
      | some .run =>
        let fits (msg : Message) : m Bool := pure (msg.receiver == sub.receiver && match msg.body with
          | .unsubscribe to => to == sub.id
          | _ => false)
        match ← w.peerMessage i p fits with
        | .error e => pure (w.report e)
        | .ok k => pure (w.carry i k)
      | _ => pure (w.report (.wrongRole i p))
  | .resend j =>
    match lines[j]? with
    | some (.request none type target input _) => w.clientRequest fsOf i type target input (some j)
    | _ => pure (w.report (.unresolvedReference i (ToValue.toValue (Fact.line j))))
  | .operate screen control payload =>
    w.attempt (w.screenOf i screen) fun o => do
      if w.role o.service != some .own then return w.report (.wrongRole i o.service)
      w.resolving (w.fill fsOf i payload) fun v => do
        if let .ok top := (w.state o.service).accepting o.chart then
          if top.resource != o.resource then return w.report (.unoperableScreen i o.resource)
        w.act fsOf (.line i) o.service fun st fs s => operate st fs s o.chart control v
  | .look screen =>
    w.attempt (w.screenOf i screen) fun o => do
      let some st := w.services.lookup o.service | return w.report (.wrongRole i o.service)
      expectations.zipIdx.foldlM (init := w) fun w (e, k) =>
        match e with
        | .offered look control payload _ =>
          if look != i || w.stopped then pure w else
          w.resolving ((payload.map (w.fill fsOf i)).getD (pure (.obj []))) fun v => do
            let found ← offeredAt st (fsOf o.service) (w.state o.service) o control v
            pure { w with looked := w.looked ++ [(k, found)] }
        | _ => pure w
  | .answer peer request answer =>
    w.resolving (w.messageOf fsOf i request) fun k => do
      let some msg := w.messages[k]? | return w
      if msg.receiver != peer then return w.report (.unresolvedReference i (ToValue.toValue request))
      let to := receivedId msg.sender msg.id
      match w.role peer with
      | some .external =>
        if msg.status != .delivered then return w.report (.notDelivered i msg.describe)
        if w.answered peer to && msg.body.requestType? != some .subscribe then
          return w.report (.repeatedAnswer i msg.describe)
        w.resolving (w.fill fsOf i answer) fun v => do
          let .ok (a : Answer) := FromValue.fromValue v | return w.report (.malformedValue i v)
          let (w, id) := w.nextId peer "answer"
          pure (w.stated i { sender := peer, receiver := msg.sender, id, body := .answer to a, origin := .line i,
                             channel := some to, status := .inFlight })
      | some .run =>
        match w.messages.toList.zipIdx.find? fun (n, j) =>
            n.status == .inFlight && n.sender == peer && n.receiver == msg.sender && !w.carried.any (·.2 == j) &&
              match n.body with
              | .answer t _ => t == to
              | _ => false with
        | none => pure (w.report (.unpairedPeerLine i peer))
        | some (reply, j) =>
          w.resolving (w.fill fsOf i answer) fun v => do
            let actual := match reply.body with
              | .answer _ a => a
              | _ => .accepted none
            let fs := fsOf peer
            let target := (msg.target?.map (·.traceName peer)).getD ""
            let shown ← comparedAnswerValue fs target (w.maskCreated peer answer v (ToValue.toValue actual))
            let expected ← comparedAnswerValue fs target (markCreated answer v)
            let w := if expected.canonical == shown.canonical then w
              else w.report (.differentPeerAnswer i expected shown)
            pure (w.carry i j)
      | _ => pure (w.report (.wrongRole i peer))
  | .emit peer event payload resultOf => do
    let resultId : ExceptT Report m (Option String) := match resultOf with
      | none => pure none
      | some f => some <$> w.requestId fsOf i f
    w.resolving resultId fun resultId =>
    w.resolving (w.fill fsOf i payload) fun v => do
      match w.role peer with
      | some .external =>
        let (w, id) := w.nextId peer event.name
        let body : LineBody := .event event.name v resultId
        let receivers := w.services.filter fun (r, st) => st.receives.contains (event.traceName r)
        if receivers.isEmpty then return w.report (.unreceivedEvent i event)
        pure (receivers.foldl (init := w) fun w (r, _) =>
          w.stated i { sender := peer, receiver := r, id, body, origin := .line i, channel := resultId,
                       status := .inFlight })
      | some .run =>
        let fits (msg : Message) : m Bool :=
          match msg.body with
          | .event n x r =>
            if msg.receiver == own && Syntax.Ref.ofTraceName peer n == event && r == resultId then
              w.sameValue (fsOf peer) (.payload n) peer payload v x
            else pure false
          | _ => pure false
        match ← w.peerMessage i peer fits with
        | .error e => pure (w.report e)
        | .ok k => pure (w.carry i k)
      | _ => pure (w.report (.wrongRole i peer))
  | .leaveUnanswered peer request =>
    w.resolving (w.messageOf fsOf i request) fun k => do
      let some msg := w.messages[k]? | return w
      if w.role peer != some .external || msg.receiver != peer then return w.report (.wrongRole i peer)
      if msg.status != .delivered then return w.report (.notDelivered i msg.describe)
      pure (w.setStatus k .unanswered)
  | .deliver message =>
    w.resolving (w.messageOf fsOf i message) fun k => do
      let some msg := w.messages[k]? | return w
      if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
      w.deliverInOrder fsOf i k
  | .redeliver message =>
    w.resolving (w.messageOf fsOf i message) fun k => do
      let some msg := w.messages[k]? | return w
      if msg.status != .delivered then return w.report (.notDelivered i msg.describe)
      w.deliverCarried fsOf i k
  | .lose message =>
    w.resolving (w.messageOf fsOf i message) fun k => do
      let some msg := w.messages[k]? | return w
      if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
      pure (w.setStatus k .lost)
  | .fail message =>
    w.resolving (w.messageOf fsOf i message) fun k => do
      let some msg := w.messages[k]? | return w
      if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
      if requestName? msg.body |>.isNone then return w.report (.unfailable i msg.describe)
      let to := receivedId msg.sender msg.id
      let reply : Message := { sender := msg.receiver, receiver := msg.sender, id := s!"answer:{to}",
                               body := .answer to (.rejected { kind := .unavailable }), origin := .line i,
                               channel := some to, status := .inFlight }
      let w := w.setStatus k .lost
      let w := { w with messages := w.messages.push reply }
      w.deliverCarried fsOf i w.messages.size.pred
  | .inFlight message =>
    w.resolving (w.messageOf fsOf i message) fun k =>
      pure { w with inFlight := w.inFlight ++ [(i, k)] }
  | .at time order => do
    if time.time ≤ w.now then return w.report (.notLater i time.time w.now)
    if let some e := order.find? fun e => !((w.role e.service).any (·.running)) then
      return w.report (.wrongRole i e.service)
    let w ← w.services.foldlM (init := w) fun w (service, _) =>
      if w.stopped then pure w else
      w.act fsOf (.line i) service (fireTo time.time ((order.filter (·.service == service)).map (·.deadline)))
    pure { w with now := time.time }
  | .restart => w.act fsOf (.line i) own restart (reopen := true)

/--
The world after line `i`, unless the values it writes report: a running peer's request, answer and event may write
`created()`.
-/
def World.line (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line)
    (expectations : List Expectation) (i : Nat) (l : Scenario.Line) : m World :=
  let allowed := match l with
    | .request (some p) .. | .answer p .. | .emit p .. => w.role p == some .run
    | _ => false
  match w.checkWritten i l.written l.picks allowed with
  | some r => pure (w.report r)
  | none => w.take fsOf own lines expectations i l

/--
The world with each message left in flight reported, unless an inFlight line names it, each inFlight line whose message
is not left in flight reported, and each request that an external peer received and neither answers nor leaves
unanswered reported.
-/
def World.checkEnd (w : World) : World :=
  let indexed := w.messages.toList.zipIdx
  let w := indexed.foldl (init := w) fun w (msg, k) =>
    if msg.status == .inFlight && !w.inFlight.any (·.2 == k) then w.report (.leftInFlight msg.describe) else w
  let w := w.inFlight.foldl (init := w) fun w (i, k) =>
    if (w.messages[k]?.map (·.status)) == some .inFlight then w else w.report (.unusedInFlight i)
  indexed.foldl (init := w) fun w (msg, _) =>
    if msg.status == .delivered && w.role msg.receiver == some .external && (requestName? msg.body).isSome &&
        !w.answered msg.receiver (receivedId msg.sender msg.id) then w.report (.awaitingAnswer msg.describe)
    else w

/-- The values in canonical form, in a bag's order: by their canonical JSON. -/
def bag (vs : List Value) : List Value := vs.mergeSort fun a b => decide (a.canonical ≤ b.canonical)

/-- The actual and expected values of the expectation `e`, which Then compares. -/
def World.compared (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line) (k : Nat)
    (e : Expectation) : ExceptT Report m (Option (Value × Value)) := do
  let some st := w.services.lookup own | return none
  let fs := fsOf own
  let comparedOr (fs : Functions m) (schema : Schema) (v : Value) : ExceptT Report m Value :=
    ExceptT.lift (comparedOr fs schema v)
  let comparedAnswer (fs : Functions m) (target : String) (a : Answer) : ExceptT Report m Value :=
    ExceptT.lift (comparedAnswer fs target a)
  let comparedAnswerValue (fs : Functions m) (target : String) (v : Value) : ExceptT Report m Value :=
    ExceptT.lift (comparedAnswerValue fs target v)
  match e with
  | .answered line answers =>
    let some s := w.sentBy line | throw (.unresolvedReference line (ToValue.toValue (Fact.line line)))
    let lines := (w.state s.receiver).lines
    let target := ((lines[s.position]?).bind (requestName? ·.body)).getD ""
    let rfs := fsOf s.receiver
    let actual ← (w.answersOf s).mapM (comparedAnswer rfs target)
    let expected ← (← answers.mapM (w.fill fsOf line)).mapM (comparedAnswerValue rfs target)
    pure (some (.arr expected, .arr actual))
  | .emitted line events =>
    let actual ← ((w.spanLines (.line line) own).filterMap fun l => match l.dir, l.body with
      | .out, .event name payload _ =>
        if (st.structure.contractsListing (st.refOf name)).isEmpty then none else some (name, payload)
      | _, _ => none).mapM fun (name, payload) => do
        let compared ← comparedOr fs (.payload name) payload
        pure (Value.obj [("event", ToValue.toValue (st.refOf name)), ("payload", compared)])
    let expected ← events.mapM fun ev => do
      let compared ← comparedOr fs (.payload (ev.event.traceName own)) (← w.fill fsOf line ev.payload)
      pure (Value.obj [("event", ToValue.toValue ev.event), ("payload", compared)])
    pure (some (.arr (bag expected), .arr (bag actual)))
  | .requested line requests ends =>
    let span := w.spanLines (.line line) own
    let actualEnds := span.filterMap fun l => match l.dir, l.body with
      | .out, .unsubscribe to => some (Value.str to)
      | _, _ => none
    let endIds ← ends.mapM fun f => do
      let k ← w.messageOf fsOf line f
      pure (Value.str ((w.messages[k]?.map (·.id)).getD ""))
    let actual ← (span.filterMap fun l =>
      match l.dir, l.body with
      | .out, .command name input => some (RequestType.command, name, input)
      | .out, .query name input => some (.query, name, input)
      | .out, .subscribe name input => some (.subscribe, name, input)
      | _, _ => none).mapM fun (type, name, input) => do
        pure (Value.obj [("kind", ToValue.toValue type), ("target", ToValue.toValue (st.refOf name)),
          ("input", ← comparedOr fs (.input name) input)])
    let expected ← requests.mapM fun r => do
      let v ← w.fill fsOf line r.input
      pure (Value.obj [("kind", ToValue.toValue r.kind), ("target", ToValue.toValue r.target),
        ("input", ← comparedOr fs (.input (r.target.traceName own)) v)])
    pure (some (.obj [("requests", .arr (bag expected)), ("ends", .arr (bag endIds))],
      .obj [("requests", .arr (bag actual)), ("ends", .arr (bag actualEnds))]))
  | .offered look _ _ offered =>
    match lines[look]? with
    | some (.look _) => pure ((w.looked.lookup k).map fun found => (.bool offered, .bool found))
    | _ => throw (.notLook k look)

/--
The world with each expectation of Then compared, unless the values it writes report; what one reports never stops the
others.
-/
def World.expect (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line)
    (expectations : List Expectation) : m World :=
  expectations.zipIdx.foldlM (init := w) fun w (e, k) => do
    if let some r := w.checkWritten e.line e.written e.picks false then return w.note r
    match ← (w.compared fsOf own lines k e).run with
    | .error r => pure (w.note r)
    | .ok none => pure w
    | .ok (some (expected, actual)) =>
      pure (if expected.canonical == actual.canonical then w else w.note (.unmetExpectation k expected actual))

/-- The world after every running service begins and the lines take place, until one stops it. -/
def World.walk (w : World) (fsOf : String → Functions m) (sc : Scenario) : m World := do
  let w ← w.services.foldlM (init := w) fun w (s, _) =>
    if w.stopped then pure w else w.act fsOf .begin s begin
  sc.lines.zipIdx.foldlM (init := w) fun w (l, i) =>
    if w.stopped then pure w else w.line fsOf sc.service sc.lines sc.expectations i l

/--
The world after the lines of the scenario take place from `start`, as `simulate` runs them, without checking the end
and Then: explore appends lines to a scenario this way, so what the appended lines leave in flight is no mistake.
-/
def walk (j : Syntax.Structure) (fsOf : String → Functions m) (start : World) (sc : Scenario) : m World := do
  let w ← start.given j fsOf sc
  if !w.reports.isEmpty then return w
  w.walk fsOf sc

/--
The world after the scenario runs from `start`, each running service asking `fsOf` its spec's functions: Given is
checked and the records placed, every running service begins, the lines take place, and the end and Then are checked.
-/
def simulate (j : Syntax.Structure) (fsOf : String → Functions m) (start : World) (sc : Scenario) : m World := do
  let w ← start.given j fsOf sc
  if !w.reports.isEmpty then return w
  let w ← w.walk fsOf sc
  if w.stopped then return w
  w.checkEnd.expect fsOf sc.service sc.lines sc.expectations

end Tazuna.Sim
