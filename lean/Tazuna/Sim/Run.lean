import Tazuna.Sim.Given
import Tazuna.Sim.Resolve

/-!
The forward run of a scenario: every running service begins at the start from its Given records, each line of When
takes place in written order, and then the undelivered messages and the expectations of Then are checked. Nothing
waits for a later line, and nothing is searched.
-/

namespace Tazuna.Sim

open Tazuna.Data Tazuna.Service
open Tazuna.Scenario (Fact Origin Template RequestType Expectation GivenRecord Peer)

variable {m : Type → Type} [Monad m] [MonadNote m] [MonadActing m]

def World.attempt {α : Type} (w : World) (r : Except InvalidScenario α) (k : α → m World) : m World :=
  match r with
  | .error e => pure (w.report e)
  | .ok a => k a

def World.resolving {α : Type} (w : World) (r : ExceptT InvalidScenario m α) (k : α → m World) : m World := do
  match ← r.run with
  | .error e => pure (w.report e)
  | .ok a => k a

/--
The answer with its output as the simulation compares it for the output of `target`, as it is when no request names a
target.
-/
def comparedAnswer (fs : Functions m) (target : Option Spec.Ref) (a : Answer) : m Value := do
  match a, target with
  | .accepted (some o), some t => pure (ToValue.toValue (Answer.accepted (some (← comparedOr fs (.output t) o))))
  | .fulfilled o, some t => pure (ToValue.toValue (Answer.fulfilled (← comparedOr fs (.output t) o)))
  | a, _ => pure (ToValue.toValue a)

/-- The written answer `v` as the simulation compares it, or as it is when it is no answer. -/
def comparedAnswerValue (fs : Functions m) (target : Option Spec.Ref) (v : Value) : m Value := do
  match (FromValue.fromValue v : Except String Answer) with
  | .ok a => comparedAnswer fs target a
  | .error _ => pure v

/--
What the values that a line or an expectation of `line` writes report: `created()` that is not `allowed` at the top or
that a pick writes, or a created key written as a literal.
-/
def World.checkWritten (w : World) (line : Nat) (written picks : List Template) (allowed : Bool) : Option InvalidScenario :=
  if picks.any (·.created) || (!allowed && written.any (·.created)) then some (.misplacedCreated line)
  else ((written ++ picks).findSome? fun t => w.writtenKey? t.value).map fun (key, e) => .writtenKey line key e

def requestTarget? : LineBody → Option Spec.Ref
  | .command r _ | .query r _ | .subscribe r _ => some r
  | _ => none

/--
The world with what the line `i` processed by `service` wrote first as an `in` line recorded as its request, unless the
line has that request already.
-/
def World.recordSent (w : World) (i : Nat) (service : String) (before : Nat) : World :=
  match ((w.state service).lines.toList.zipIdx.drop before).find? (·.1.dir == .in) with
  | some (l, position) =>
    if w.sent.any fun s => s.line == i && s.receiver == service && s.id == l.id then w
    else { w with sent := w.sent ++ [{ line := i, receiver := service, id := l.id, position }] }
  | none => w

/-- The places `ks`, in sending order, in the order that line `i` acts on them (World.deliveryOrders). -/
def World.inOrder (w : World) (i : Nat) (ks : List Nat) : List Nat :=
  match w.deliveryOrders.lookup i with
  | some order => if order.length == ks.length then order.filterMap (ks[·]?) else ks
  | none => ks

/--
The world after `f` takes each of `xs` in turn with its place, from 0, until the world stops or a report is added: a
line that names several messages acts on each, and stops at the first report as a line with one does.
-/
def World.forEach {α : Type} (w : World) (xs : List α) (f : World → α → Nat → m World) : m World :=
  xs.zipIdx.foldlM (init := w) fun v (x, n) =>
    if v.stopped || v.violations.length != w.violations.length then pure v else f v x n

def requestOf (type : RequestType) (target : Spec.Ref) (id : Option LineId) (v : Value) :
    Service → Functions m → State → m State :=
  fun st fs s => match type with
    | .command => send st fs s target id v
    | .query => call st fs s target id v
    | .subscribe => subscribe st fs s target id v

def bodyOf (type : RequestType) (target : Spec.Ref) (v : Value) : LineBody :=
  match type with
  | .command => .command target v
  | .query => .query target v
  | .subscribe => .subscribe target v

/-- The world after the client's request of line `i`, with the id of the request of line `sameIdAs`, if any. -/
def World.clientRequest (w : World) (fsOf : String → Functions m) (i : Nat) (type : RequestType)
    (target : Spec.Ref) (input : Template) (sameIdAs : Option Nat) : m World := do
  let receiver := target.service
  if !((w.role receiver).any (·.running)) then return w.report (.wrongRole i receiver)
  w.resolving (w.fill fsOf i input) fun v => do
    let given ← match sameIdAs with
      | none => pure (some none)
      | some j => pure ((w.sentBy j).head?.map (some ·.id))
    let some id := given | return w.report (.unresolvedReference i (ToValue.toValue (Fact.line (sameIdAs.getD 0))))
    let before := (w.state receiver).lines.size
    let w ← w.act fsOf { origin := .line i } receiver (requestOf type target id v)
    pure (w.recordSent i receiver before)

/-- The world with the message `k` carried by line `i`. -/
def World.carry (w : World) (i k : Nat) : World := { w with carried := w.carried ++ [(i, k)] }

/-- The world with the message that the external peer's line `i` sends, in flight to its running receiver. -/
def World.stated (w : World) (i : Nat) (msg : Message) : World :=
  if !((w.role msg.receiver).any (·.running)) then w.report (.wrongRole i msg.receiver)
  else { w with messages := w.messages.push msg }.carry i w.messages.size

/-- The world with the next id of the messages of `name` that the external peer `peer` sends. -/
def World.nextId (w : World) (peer name : String) : World × LineId :=
  let key := (peer, name)
  let n := (w.counts.lookup key).getD 0 + 1
  ({ w with counts := (key, n) :: w.counts.filter (·.1 != key) }, .own s!"{name}#{n}")

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
The message in flight from the running peer `peer` that the line `i` states: the first in sending order that `fits`
accepts and no earlier line stated, or the report of none. Every message that `fits` accepts is equal to the line once
the keys that the peer created are masked, so the line cannot tell them apart, and the first stands for each.
-/
def World.peerMessage (w : World) (i : Nat) (peer : String) (fits : Message → m Bool) : m (Except InvalidScenario Nat) := do
  let found ← w.messages.toList.zipIdx.filterM fun (msg, k) =>
    if msg.status == .inFlight && msg.sender == peer && !w.carried.any (·.2 == k) then fits msg else pure false
  pure (match found with
    | (_, k) :: _ => .ok k
    | [] => .error (.unpairedPeerLine i peer))

/--
The world after the message `k` reaches its receiver by line `i`, as the line's delivery `n`: a running receiver
processes it, and a request that it processes is recorded as a request of each line that carried it.
-/
def World.deliverCarried (w : World) (fsOf : String → Functions m) (i n k : Nat) : m World := do
  let w := w.carry i k
  let some msg := w.messages[k]? | return w
  if !((w.role msg.receiver).any (·.running)) then return w.setStatus k .delivered
  let before := (w.state msg.receiver).lines.size
  let w ← w.deliver fsOf { origin := .line i, delivery := n } k
  if (requestTarget? msg.body).isNone then return w
  let carriers := (w.carried.filter (·.2 == k)).map (·.1)
  pure (carriers.foldl (init := w) fun w l => w.recordSent l msg.receiver before)

/--
The world after line `i` delivers the in-flight message `k` as its delivery `n`, unless an earlier message in flight must
arrive before it (World.precedes), which FIFO delivers first.
-/
def World.deliverInOrder (w : World) (fsOf : String → Functions m) (i n k : Nat) : m World :=
  match w.messages[k]? with
  | none => pure w
  | some msg =>
    match (w.messages.toList.take k).find? fun n => n.status == .inFlight && w.precedes n msg with
    | some earlier => pure (w.report (.overtaking i msg.describe earlier.describe))
    | none => w.deliverCarried fsOf i n k

/--
The ids by which `peer` names the requests that the handle `fact` of line `i` names, which a line delivered to `peer`.
-/
def World.requestIds (w : World) (fsOf : String → Functions m) (i : Nat) (peer : String) (fact : Fact) :
    ExceptT InvalidScenario m (List LineId) :=
  match fact with
  | .line j =>
    match w.sentBy j with
    | [] => throw (.unresolvedReference i (ToValue.toValue fact))
    | sents =>
      if sents.all (·.receiver == peer) then pure (sents.map (·.id))
      else throw (.unreceivedRequest i peer (ToValue.toValue fact))
  | _ => do
    let ks ← w.messagesOf fsOf i fact
    ks.mapM fun k =>
      match w.messages[k]? with
      | some msg =>
        if msg.receiver == peer && (msg.status == .delivered || msg.status == .unanswered) then
          pure (receivedId msg.sender msg.id)
        else throw (.unreceivedRequest i peer (ToValue.toValue fact))
      | none => throw (.unresolvedReference i (ToValue.toValue fact))

def offeredAt (st : Service) (fs : Functions m) (s : State) (o : Opened) (control : String) (payload : Value) :
    m Bool := do
  match ← fs.parse (.control (st.ref o.id.chart) control) payload with
  | .ok (some decoded) =>
    match ← acceptsOperation fs st s o.id control decoded with
    | .ok (.ok _) => pure true
    | _ => pure false
  | _ => pure false

/--
The running service after the deadlines due by `time` fire and the clock's time line arrives, as the input that verify
gives the implementation. A subscription answer that the new time changes is sent after the time line.
-/
def fireTo (time : Time) : Service → Functions m → State → m State :=
  fun st fs s => do
    let s ← fireDue st fs time Limit.dueDeadlines.max none s
    let s := { s with now := max s.now time }
    if s.halted.isSome then pure s else publish st fs (s.write .in none .time).1

/-- Whether an answer to the request `to` from `sender` is among the messages. -/
def World.answered (w : World) (sender : String) (to : LineId) : Bool :=
  w.messages.any fun n => n.sender == sender && n.channel == some to && match n.body with
    | .answer .. => true
    | _ => false

/-- The world after line `i` of the scenario of the own service `own`. -/
def World.take (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line) (i : Nat) :
    Scenario.Line → m World
  | .request none type target input sameIdAs => w.clientRequest fsOf i type target input sameIdAs
  | .request (some peer) type target input _ => do
    match w.role peer with
    | some .external =>
      w.resolving (w.fill fsOf i input) fun v => do
        let (w, id) := w.nextId peer target.name
        pure (w.stated i { sender := peer, receiver := target.service, id, body := bodyOf type target v,
                           origin := .line i, channel := some (receivedId peer id), status := .inFlight })
    | some .run =>
      w.resolving (w.fill fsOf i input) fun v => do
        let fits (msg : Message) : m Bool :=
          if msg.body.requestType? == some type && requestTarget? msg.body == some target &&
              msg.receiver == target.service then
            w.sameValue (fsOf peer) (.input target) peer input v ((msg.body.value?).getD .null)
          else pure false
        match ← w.peerMessage i peer fits with
        | .error e => pure (w.report e)
        | .ok k => pure (w.carry i k)
    | _ => pure (w.report (.wrongRole i peer))
  | .unsubscribe none subscription => do
    let some s := (w.sentBy subscription).head?
      | return w.report (.unresolvedReference i (ToValue.toValue (Fact.line subscription)))
    w.act fsOf { origin := .line i } s.receiver fun st fs t => endSubscription st fs t s.id
  | .unsubscribe (some p) subscription =>
    w.resolving (w.messagesOf fsOf i (.line subscription)) fun ks => w.forEach (w.inOrder i ks) fun w k _ => do
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
      w.resolving (w.fill fsOf i payload) fun v =>
        w.act fsOf { origin := .line i } o.service fun st fs s => operate st fs s o.id control v
  | .look screen =>
    w.attempt (w.screenOf i screen) fun o =>
      pure (if (w.services.lookup o.service).isNone then w.report (.wrongRole i o.service) else w)
  | .answer peer request answer =>
    w.resolving (w.messagesOf fsOf i request) fun ks => w.forEach (w.inOrder i ks) fun w k _ => do
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
            let target := msg.target?
            let shown ← comparedAnswerValue fs target (w.maskCreated peer answer v (ToValue.toValue actual))
            let expected ← comparedAnswerValue fs target (markCreated answer v)
            let w := if expected.canonical == shown.canonical then w
              else w.report (.differentPeerAnswer i expected shown)
            pure (w.carry i j)
      | _ => pure (w.report (.wrongRole i peer))
  | .emit peer event payload resultOf => do
    let resultIds : ExceptT InvalidScenario m (List (Option LineId)) := match resultOf with
      | none => pure [none]
      | some f => (·.map some) <$> w.requestIds fsOf i peer f
    w.resolving resultIds fun resultIds =>
    w.resolving (w.fill fsOf i payload) fun v => w.forEach resultIds fun w resultId _ => do
      match w.role peer with
      | some .external =>
        let (w, id) := w.nextId peer event.name
        let body : LineBody := .event event v resultId
        let receivers := w.services.filter fun (_, st) => st.receives.contains event
        if receivers.isEmpty then return w.report (.unreceivedEvent i event)
        pure (receivers.foldl (init := w) fun w (r, _) =>
          w.stated i { sender := peer, receiver := r, id, body, origin := .line i, channel := resultId,
                       status := .inFlight })
      | some .run =>
        let fits (msg : Message) : m Bool :=
          match msg.body with
          | .event e x r =>
            if msg.receiver == own && e == event && r == resultId then
              w.sameValue (fsOf peer) (.payload e) peer payload v x
            else pure false
          | _ => pure false
        match ← w.peerMessage i peer fits with
        | .error e => pure (w.report e)
        | .ok k => pure (w.carry i k)
      | _ => pure (w.report (.wrongRole i peer))
  | .leaveUnanswered peer request =>
    w.resolving (w.messagesOf fsOf i request) fun ks => w.forEach (w.inOrder i ks) fun w k _ => do
      let some msg := w.messages[k]? | return w
      if w.role peer != some .external || msg.receiver != peer then return w.report (.wrongRole i peer)
      if msg.status != .delivered then return w.report (.notDelivered i msg.describe)
      if w.answered peer (receivedId msg.sender msg.id) && msg.body.requestType? != some .subscribe then
        return w.report (.repeatedAnswer i msg.describe)
      pure (w.setStatus k .unanswered)
  | .deliver message =>
    w.resolving (w.messagesOf fsOf i message) fun ks => w.forEach (w.inOrder i ks) fun w k n => do
      let some msg := w.messages[k]? | return w
      if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
      w.deliverInOrder fsOf i n k
  | .redeliver message =>
    w.resolving (w.messagesOf fsOf i message) fun ks => w.forEach (w.inOrder i ks) fun w k n => do
      let some msg := w.messages[k]? | return w
      if msg.status != .delivered then return w.report (.notDelivered i msg.describe)
      if !((w.role msg.receiver).any (·.running)) then return w.report (.wrongRole i msg.receiver)
      w.deliverCarried fsOf i n k
  | .lose message =>
    w.resolving (w.messagesOf fsOf i message) fun ks => w.forEach (w.inOrder i ks) fun w k _ => do
      let some msg := w.messages[k]? | return w
      if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
      pure (w.setStatus k .lost)
  | .refuse message =>
    w.resolving (w.messagesOf fsOf i message) fun ks => w.forEach (w.inOrder i ks) fun w k n => do
      let some msg := w.messages[k]? | return w
      if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
      if requestTarget? msg.body |>.isNone then return w.report (.unrefusable i msg.describe)
      let to := receivedId msg.sender msg.id
      let reply : Message := { sender := msg.receiver, receiver := msg.sender, id := .own s!"answer:{msg.id.text}",
                               body := .answer to (.rejected { kind := .unavailable }), origin := .line i,
                               channel := some to, status := .inFlight }
      let w := w.setStatus k .lost
      let w := { w with messages := w.messages.push reply }
      w.deliverCarried fsOf i n w.messages.size.pred
  | .leaveInFlight message =>
    w.resolving (w.messagesOf fsOf i message) fun ks => w.forEach (w.inOrder i ks) fun w k _ => do
      let some msg := w.messages[k]? | return w
      if w.leftInFlight.any (·.2 == k) then return w.report (.repeatedInFlight i msg.describe)
      pure { w with leftInFlight := w.leftInFlight ++ [(i, k)] }
  | .at time => do
    if time.time ≤ w.now then return w.report (.notLater i time.time w.now)
    let w ← w.services.foldlM (init := w) fun w (service, _) =>
      if w.stopped then pure w else
      w.act fsOf { origin := .line i } service (fireTo time.time)
    pure { w with now := time.time }
  | .restart => w.act fsOf { origin := .line i } own restart (reopen := true)

/--
The world after line `i`, unless the values it writes report: a running peer's request, answer and event may write
`created()`.
-/
def World.line (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line) (i : Nat)
    (l : Scenario.Line) : m World :=
  let allowed := match l with
    | .request (some p) .. | .answer p .. | .emit p .. => w.role p == some .run
    | _ => false
  match w.checkWritten i l.written l.picks allowed with
  | some r => pure (w.report r)
  | none => w.take fsOf own lines i l

/--
What the look line `i` finds for each offered expectation of `expectations` on it, by expectation: whether the screen
offers the control with the payload at that point, or the report of the payload. Then reads it, and no line does, so a
payload that reports stops nothing.
-/
def World.found (w : World) (fsOf : String → Functions m) (expectations : List Expectation) (i : Nat) :
    Scenario.Line → m (List (Nat × Except InvalidScenario Bool))
  | .look screen =>
    match w.screenOf i screen with
    | .error _ => pure []
    | .ok o =>
      match w.services.lookup o.service with
      | none => pure []
      | some st =>
        expectations.zipIdx.filterMapM fun (e, k) =>
          match e with
          | .offered look control payload _ =>
            if look != i then pure none else do
            match ← ((payload.map (w.fill fsOf i)).getD (pure (.obj []))).run with
            | .error r => pure (some (k, .error r))
            | .ok v => pure (some (k, .ok (← offeredAt st (fsOf o.service) (w.state o.service) o control v)))
          | _ => pure none
  | _ => pure []

/--
The world with each message left in flight reported, unless an leaveInFlight line names it, each leaveInFlight line whose message
is not left in flight reported, and each request that an external peer received and neither answers nor leaves
unanswered reported.
-/
def World.checkEnd (w : World) : World :=
  let indexed := w.messages.toList.zipIdx
  let w := indexed.foldl (init := w) fun w (msg, k) =>
    if msg.status == .inFlight && !w.leftInFlight.any (·.2 == k) then w.report (.leftInFlight msg.describe) else w
  let w := w.leftInFlight.foldl (init := w) fun w (i, k) =>
    if (w.messages[k]?.map (·.status)) == some .inFlight then w else w.report (.unusedInFlight i)
  indexed.foldl (init := w) fun w (msg, _) =>
    if msg.status == .delivered && w.role msg.receiver == some .external && (requestTarget? msg.body).isSome &&
        !w.answered msg.receiver (receivedId msg.sender msg.id) then w.report (.awaitingAnswer msg.describe)
    else w

/-- The values in canonical form, in a bag's order: by their canonical JSON. -/
def bag (vs : List Value) : List Value := vs.mergeSort fun a b => decide (a.canonical ≤ b.canonical)

/-- The actual and expected values of the expectation `e`, which Then compares, with what the look lines `found`. -/
def World.compared (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line)
    (found : List (Nat × Except InvalidScenario Bool)) (k : Nat) (e : Expectation) :
    ExceptT InvalidScenario m (Option (Value × Value)) := do
  let some st := w.services.lookup own | return none
  let fs := fsOf own
  let comparedOr (fs : Functions m) (schema : Schema) (v : Value) : ExceptT InvalidScenario m Value :=
    ExceptT.lift (comparedOr fs schema v)
  let comparedAnswer (fs : Functions m) (target : Option Spec.Ref) (a : Answer) : ExceptT InvalidScenario m Value :=
    ExceptT.lift (comparedAnswer fs target a)
  let comparedAnswerValue (fs : Functions m) (target : Option Spec.Ref) (v : Value) :
      ExceptT InvalidScenario m Value :=
    ExceptT.lift (comparedAnswerValue fs target v)
  match e with
  | .answered line answers =>
    let some s := (w.sentBy line).head? | throw (.unresolvedReference line (ToValue.toValue (Fact.line line)))
    let lines := (w.state s.receiver).lines
    let target := (lines[s.position]?).bind (requestTarget? ·.body)
    let rfs := fsOf s.receiver
    let actual ← (w.answersOf s).mapM (comparedAnswer rfs target)
    let expected ← (← answers.mapM (w.fill fsOf line)).mapM (comparedAnswerValue rfs target)
    pure (some (.arr expected, .arr actual))
  | .emitted line events =>
    let actual ← ((w.spanLines (.line line) own).filterMap fun l => match l.dir, l.body with
      | .out, .event event payload _ =>
        if (st.structure.contractsListing event).isEmpty then none else some (event, payload)
      | _, _ => none).mapM fun (event, payload) => do
        let compared ← comparedOr fs (.payload event) payload
        pure (Value.obj [("event", ToValue.toValue event), ("payload", compared)])
    let expected ← events.mapM fun ev => do
      let compared ← comparedOr fs (.payload ev.event) (← w.fill fsOf line ev.payload)
      pure (Value.obj [("event", ToValue.toValue ev.event), ("payload", compared)])
    pure (some (.arr (bag expected), .arr (bag actual)))
  | .requested line requests ends =>
    let span := w.spanLines (.line line) own
    let actualEnds := span.filterMap fun l => match l.dir, l.body with
      | .out, .unsubscribe to => some (Value.str to.text)
      | _, _ => none
    let endIds := (← ends.mapM fun f => do
      let ks ← w.messagesOf fsOf line f
      pure (ks.map fun k => Value.str ((w.messages[k]?.map (·.id.text)).getD ""))).flatten
    let actual ← (span.filterMap fun l =>
      match l.dir, l.body with
      | .out, .command r input => some (RequestType.command, r, input)
      | .out, .query r input => some (.query, r, input)
      | .out, .subscribe r input => some (.subscribe, r, input)
      | _, _ => none).mapM fun (type, r, input) => do
        pure (Value.obj [("kind", ToValue.toValue type), ("target", ToValue.toValue r),
          ("input", ← comparedOr fs (.input r) input)])
    let expected ← requests.mapM fun r => do
      let v ← w.fill fsOf line r.input
      pure (Value.obj [("kind", ToValue.toValue r.kind), ("target", ToValue.toValue r.target),
        ("input", ← comparedOr fs (.input r.target) v)])
    pure (some (.obj [("requests", .arr (bag expected)), ("ends", .arr (bag endIds))],
      .obj [("requests", .arr (bag actual)), ("ends", .arr (bag actualEnds))]))
  | .offered look _ _ offered =>
    match lines[look]? with
    | some (.look _) =>
      match found.lookup k with
      | some (.ok offers) => pure (some (.bool offered, .bool offers))
      | some (.error r) => throw r
      | none => pure none
    | _ => throw (.notALook k look)

/--
The world with each expectation of Then compared, unless the values it writes report; what one reports never stops the
others.
-/
def World.expect (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line)
    (expectations : List Expectation) (found : List (Nat × Except InvalidScenario Bool)) : m World :=
  expectations.zipIdx.foldlM (init := w) fun w (e, k) => do
    if let some r := w.checkWritten e.line e.written e.picks false then return w.note r
    match ← (w.compared fsOf own lines found k e).run with
    | .error r => pure (w.note r)
    | .ok none => pure w
    | .ok (some (expected, actual)) =>
      pure (if expected.canonical == actual.canonical then w else w.note (.unmetExpectation k expected actual))

/-- The world after the line `l` at `i` of the scenario, unless an earlier line or the startup stopped the simulation. -/
def World.step (w : World) (fsOf : String → Functions m) (sc : Scenario) (l : Scenario.Line) (i : Nat) : m World :=
  if w.stopped then pure w else w.line fsOf sc.service sc.lines i l

/--
The world after the line `l` at `i`, as `step` leaves it, with what the line found for Then added to `found`: Then
reads the world before the line, and the line does not read Then.
-/
def World.stepFinding (fsOf : String → Functions m) (sc : Scenario) (wf : World × List (Nat × Except InvalidScenario Bool))
    (l : Scenario.Line) (i : Nat) : m (World × List (Nat × Except InvalidScenario Bool)) := do
  let (w, found) := wf
  if w.stopped then return (w, found)
  let more ← w.found fsOf sc.expectations i l
  pure (← w.step fsOf sc l i, found ++ more)

/-- The world after every running service begins, until one stops it. -/
def World.beginAll (w : World) (fsOf : String → Functions m) : m World :=
  w.services.foldlM (init := w) fun w (s, _) => if w.stopped then pure w else w.act fsOf { origin := .startup } s begin

/-- The world after every running service begins and the lines take place, until one stops it. -/
def World.execute (w : World) (fsOf : String → Functions m) (sc : Scenario) : m World := do
  let w ← w.beginAll fsOf
  sc.lines.zipIdx.foldlM (init := w) fun w (l, i) => w.step fsOf sc l i

/--
The world after the lines of the scenario take place from `start`, as `simulate` runs them, without checking the end
and Then: explore appends lines to a scenario this way, so what the appended lines leave in flight is no mistake.
-/
def execute (j : Spec.Structure) (fsOf : String → Functions m) (start : World) (sc : Scenario) : m World := do
  let w ← start.given j fsOf sc
  if !w.violations.isEmpty then return w
  w.execute fsOf sc

/--
`w` after its run ends, unless it stopped: each running service checks the ensures of the commands that assumed peers
accepted.
-/
def World.ended (w : World) (fsOf : String → Functions m) : m World := do
  if w.stopped then return w
  let states ← w.states.mapM fun (q, s) => do
    match w.services.lookup q with
    | some _ => pure (q, ← checkResults (fsOf q) s)
    | none => pure (q, s)
  pure { w with states }

/--
The world after the scenario runs from `start`, each running service asking `fsOf` its spec's functions: Given is
checked and the records placed, every running service begins, the lines take place, the run ends, and the end and
Then are checked.
-/
def simulate (j : Spec.Structure) (fsOf : String → Functions m) (start : World) (sc : Scenario) : m World := do
  let w ← start.given j fsOf sc
  if !w.violations.isEmpty then return w
  let w ← w.beginAll fsOf
  let wf ← sc.lines.zipIdx.foldlM (init := (w, [])) fun wf (l, i) => World.stepFinding fsOf sc wf l i
  let w ← wf.1.ended fsOf
  if w.stopped then return w
  w.checkEnd.expect fsOf sc.service sc.lines sc.expectations wf.2

end Tazuna.Sim
