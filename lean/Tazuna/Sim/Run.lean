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

variable {m : Type → Type} [Monad m] [MonadNote m]

def World.attempt {α : Type} (w : World) (r : Except Report α) (k : α → m World) : m World :=
  match r with
  | .error e => pure (w.report e)
  | .ok a => k a

/-- `v` as the simulation compares it for `schema` (Functions.unordered), or as it is when it does not match it. -/
def comparedOr (fs : Functions m) (schema : Schema) (v : Value) : m Value := do
  match ← fs.unordered schema v with
  | .ok c => pure c
  | .error _ => pure v

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

/--
The first string of `v` of the form `<participant>/<key>` of a createKey value of an entity of `st` that no running
service has created.
-/
def World.uncreated (w : World) (st : Service) (v : Value) : Option (String × String) :=
  let created := w.states.flatMap fun (_, s) => s.created.map (·.2)
  v.strings.findSome? fun x =>
    if created.contains x then none
    else match x.splitOn "/" with
      | [owner, key] =>
        if (w.services.lookup owner).isNone then none
        else (st.entities.find? fun e => !st.singles.contains e && Syntax.isKeyOf e key).map (x, ·)
      | _ => none

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
    | .subscribe => subscribe st fs s name id v none

/-- The world after the client's request of line `i`, with the id of the request of line `sameIdAs`, if any. -/
def World.clientRequest (w : World) (fsOf : String → Functions m) (i : Nat) (type : RequestType)
    (target : Syntax.Ref) (input : Template) (sameIdAs : Option Nat) : m World := do
  let receiver := target.service
  if !((w.role receiver).any (·.running)) then return w.report (.wrongRole i receiver)
  let some st := w.services.lookup receiver | return w.report (.wrongRole i receiver)
  w.attempt (w.fill i input) fun v => do
    if let some (key, entity) := w.uncreated st input.value then
      return w.report (.uncreatedKey i key (st.ref entity))
    let given ← match sameIdAs with
      | none => pure (some none)
      | some j => pure ((w.sentBy j).map (some ·.id))
    let some id := given | return w.report (.unresolvedReference i (ToValue.toValue (Fact.line (sameIdAs.getD 0))))
    let before := (w.state receiver).lines.size
    let w ← w.act fsOf (.line i) receiver (requestOf type target.name id v)
    pure (w.recordSent i receiver before)

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
The message in flight from the running peer `peer` that is the line `i`'s, among those that `fits` accepts: of each
channel the oldest, which FIFO delivers first; the only such one, or the report of none or of several channels.
-/
def World.peerMessage (w : World) (i : Nat) (peer : String) (fits : Message → m Bool) : m (Except Report Nat) := do
  let found ← w.messages.toList.zipIdx.filterM fun (msg, _) =>
    if msg.status == .inFlight && msg.sender == peer then fits msg else pure false
  let oldest := found.filter fun (msg, k) => !found.any fun (n, j) => j < k && n.sameChannel msg
  pure (match oldest with
    | [(_, k)] => .ok k
    | [] => .error (.unpairedPeerLine i peer)
    | several => .error (.ambiguousPeerLine i peer (several.map (·.1.describe))))

/-- The world after the message `k` that line `i` carried is delivered, with the line's request recorded. -/
def World.deliverCarried (w : World) (fsOf : String → Functions m) (i k : Nat) : m World := do
  let w := { w with carried := w.carried ++ [(i, k)] }
  match w.messages[k]? with
  | none => pure w
  | some msg =>
    let before := (w.state msg.receiver).lines.size
    let w ← w.deliver fsOf (.line i) k
    pure (match msg.body with
      | .command .. | .query .. | .subscribe .. => w.recordSent i msg.receiver before
      | _ => w)

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
def World.requestId (w : World) (i : Nat) (fact : Fact) : Except Report String :=
  match fact with
  | .line j =>
    match w.sentBy j with
    | some s => .ok s.id
    | none => .error (.unresolvedReference i (ToValue.toValue fact))
  | _ => do
    let k ← w.messageOf i fact
    match w.messages[k]? with
    | some msg => .ok (receivedId msg.sender msg.id)
    | none => .error (.unresolvedReference i (ToValue.toValue fact))

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
    let s := { s.checkOrderUsed with now := max s.now time, tieOrderRequired := false }
    pure (if s.halted.isSome then s else (s.writeInput none .time).1)

/-- The world after line `i` of the scenario of the own service `own`, which `expectations` follow. -/
def World.line (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line)
    (expectations : List Expectation) (i : Nat) : Scenario.Line → m World
  | .request none type target input sameIdAs => w.clientRequest fsOf i type target input sameIdAs
  | .request (some peer) type target input sameIdAs => do
    match w.role peer with
    | some .external => w.clientRequest fsOf i type target input sameIdAs
    | some .run =>
      w.attempt (w.fill i input) fun v => do
        let name := target.traceName peer
        let fits (msg : Message) : m Bool :=
          let typed := match type, msg.body with
            | .command, .command n x | .query, .query n x | .subscribe, .subscribe n x =>
              if n == name then some x else none
            | _, _ => none
          match typed with
          | some x => if msg.receiver == target.service then
              w.sameValue (fsOf peer) (.input name) peer input v x else pure false
          | none => pure false
        match ← w.peerMessage i peer fits with
        | .error e => pure (w.report e)
        | .ok k => w.deliverInOrder fsOf i k
    | _ => pure (w.report (.wrongRole i peer))
  | .unsubscribe peer subscription => do
    let some s := w.sentBy subscription
      | return w.report (.unresolvedReference i (ToValue.toValue (Fact.line subscription)))
    let direct := w.act fsOf (.line i) s.receiver fun st fs t => endSubscription st fs t (.id s.id)
    match peer with
    | none => direct
    | some p =>
      match w.role p with
      | some .external => direct
      | some .run =>
        let fits (msg : Message) : m Bool := pure (msg.receiver == s.receiver && match msg.body with
          | .unsubscribe to => receivedId p to == s.id
          | _ => false)
        match ← w.peerMessage i p fits with
        | .error e => pure (w.report e)
        | .ok k => w.deliverInOrder fsOf i k
      | _ => pure (w.report (.wrongRole i p))
  | .resend j =>
    match lines[j]? with
    | some (.request none type target input _) => w.clientRequest fsOf i type target input (some j)
    | _ => pure (w.report (.unresolvedReference i (ToValue.toValue (Fact.line j))))
  | .operate screen control payload =>
    w.attempt (w.screenOf i screen) fun o => do
      if w.role o.service != some .own then return w.report (.wrongRole i o.service)
      w.attempt (w.fill i payload) fun v => do
        if let .ok top := (w.state o.service).accepting o.chart then
          if top.resource != o.resource then return w.report (.unoperableScreen i o.resource)
        w.act fsOf (.line i) o.service fun st fs s => operate st fs s o.chart control v true
  | .look screen =>
    w.attempt (w.screenOf i screen) fun o => do
      let some st := w.services.lookup o.service | return w.report (.wrongRole i o.service)
      expectations.zipIdx.foldlM (init := w) fun w (e, k) =>
        match e with
        | .offered look control payload _ =>
          if look != i || w.stopped then pure w else
          w.attempt ((payload.map (w.fill i)).getD (.ok (.obj []))) fun v => do
            let found ← offeredAt st (fsOf o.service) (w.state o.service) o control v
            pure { w with looked := w.looked ++ [(k, found)] }
        | _ => pure w
  | .answer peer request answer =>
    w.attempt (w.messageOf i request) fun k => do
      let some msg := w.messages[k]? | return w
      if msg.receiver != peer then return w.report (.unresolvedReference i (ToValue.toValue request))
      let to := receivedId msg.sender msg.id
      match w.role peer with
      | some .external =>
        if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
        w.attempt (w.fill i answer) fun v => do
          let .ok (a : Answer) := FromValue.fromValue v | return w.report (.malformedValue i v)
          let reply : Message := { sender := peer, receiver := msg.sender, id := s!"answer:{to}",
                                   body := .answer to a, origin := .line i, channel := some to, status := .inFlight }
          let w := w.setStatus k .delivered
          let w := { w with messages := w.messages.push reply }
          w.deliverCarried fsOf i w.messages.size.pred
      | some .run =>
        match w.messages.toList.zipIdx.find? fun (n, _) =>
            n.status == .inFlight && n.sender == peer && n.receiver == msg.sender && match n.body with
              | .answer t _ => t == to
              | _ => false with
        | none => pure (w.report (.unpairedPeerLine i peer))
        | some (reply, j) =>
          w.attempt (w.fill i answer) fun v => do
            let actual := match reply.body with
              | .answer _ a => a
              | _ => .accepted none
            let fs := fsOf peer
            let target := (msg.target?.map (·.traceName peer)).getD ""
            let written := markCreated answer v
            let shown ← comparedAnswerValue fs target (w.maskCreated peer answer v (ToValue.toValue actual))
            let expected ← comparedAnswerValue fs target written
            let w := if expected.canonical == shown.canonical then w
              else w.report (.differentPeerAnswer i expected shown)
            w.deliverInOrder fsOf i j
      | _ => pure (w.report (.wrongRole i peer))
  | .emit peer event payload resultOf => do
    let resultId ← match resultOf with
      | none => pure (.ok none)
      | some f => pure ((w.requestId i f).map some)
    w.attempt resultId fun resultId =>
    w.attempt (w.fill i payload) fun v => do
      match w.role peer with
      | some .external =>
        let key := s!"{peer}.{event.name}"
        let n := (w.emitted.lookup key).getD 0 + 1
        let w := { w with emitted := (key, n) :: w.emitted.filter (·.1 != key) }
        let body : LineBody := .event event.name v resultId
        w.services.foldlM (init := w) fun w (r, st) => do
          if w.stopped || !st.received.contains (event.traceName r) then return w
          let msg : Message := { sender := peer, receiver := r, id := s!"{event.name}#{n}", body, origin := .line i,
                                 channel := resultId, status := .inFlight }
          let w := { w with messages := w.messages.push msg }
          w.deliverCarried fsOf i w.messages.size.pred
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
        | .ok k => w.deliverInOrder fsOf i k
      | _ => pure (w.report (.wrongRole i peer))
  | .leaveUnanswered peer request =>
    w.attempt (w.messageOf i request) fun k => do
      let some msg := w.messages[k]? | return w
      if w.role peer != some .external || msg.receiver != peer then return w.report (.wrongRole i peer)
      if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
      pure (w.setStatus k .unanswered)
  | .deliver message =>
    w.attempt (w.messageOf i message) fun k => do
      let some msg := w.messages[k]? | return w
      if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
      if !((w.role msg.receiver).any (·.running)) then return w.report (.wrongRole i msg.receiver)
      w.deliverInOrder fsOf i k
  | .redeliver message =>
    w.attempt (w.messageOf i message) fun k => do
      let some msg := w.messages[k]? | return w
      if msg.status != .delivered then return w.report (.notDelivered i msg.describe)
      w.deliverCarried fsOf i k
  | .lose message =>
    w.attempt (w.messageOf i message) fun k => do
      let some msg := w.messages[k]? | return w
      if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
      pure (w.setStatus k .lost)
  | .fail message =>
    w.attempt (w.messageOf i message) fun k => do
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
    w.attempt (w.messageOf i message) fun k => do
      let some msg := w.messages[k]? | return w
      pure { w with inFlight := w.inFlight ++ [(i, msg.sender, msg.receiver, msg.channel)] }
  | .at time order => do
    if time.time ≤ w.now then return w.report (.notLater i time.time w.now)
    if let some e := order.find? fun e => !((w.role e.service).any (·.running)) then
      return w.report (.wrongRole i e.service)
    let w ← w.services.foldlM (init := w) fun w (service, _) =>
      if w.stopped then pure w else
      w.act fsOf (.line i) service (fireTo time.time ((order.filter (·.service == service)).map (·.deadline)))
    pure { w with now := time.time }
  | .restart => w.act fsOf (.line i) own restart

/-- Whether the inFlight entry covers the message: it is on the entry's channel, either way. -/
def covers (entry : Nat × String × String × Option String) (msg : Message) : Bool :=
  let (_, a, b, c) := entry
  c == msg.channel && ((a, b) == (msg.sender, msg.receiver) || (a, b) == (msg.receiver, msg.sender))

/--
The world with each message left in flight reported, unless an inFlight line covers its channel, and each inFlight line
that covers no message left in flight reported.
-/
def World.checkEnd (w : World) : World :=
  let left := w.messages.toList.filter (·.status == .inFlight)
  let w := left.foldl (init := w) fun w msg =>
    if w.inFlight.any (covers · msg) then w else w.report (.leftInFlight msg.describe)
  w.inFlight.foldl (init := w) fun w entry =>
    if left.any (covers entry) then w else w.report (.unusedInFlight entry.1)

/-- The values in canonical form, in a bag's order: by their canonical JSON. -/
def bag (vs : List Value) : List Value := vs.mergeSort fun a b => decide (a.canonical ≤ b.canonical)

/-- The actual and expected values of the expectation `e`, which Then compares. -/
def World.compared (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line) (k : Nat)
    (e : Expectation) : m (Except Report (Option (Value × Value))) := do
  let some st := w.services.lookup own | return .ok none
  let fs := fsOf own
  match e with
  | .answered line answers =>
    let some s := w.sentBy line | return .error (.unresolvedReference line (ToValue.toValue (Fact.line line)))
    let lines := (w.state s.receiver).lines
    let target := ((lines[s.position]?).bind (requestName? ·.body)).getD ""
    let rfs := fsOf s.receiver
    let actual ← (w.answersOf s).mapM (comparedAnswer rfs target)
    match answers.mapM (w.fill line) with
    | .error r => pure (.error r)
    | .ok vs =>
      let expected ← vs.mapM (comparedAnswerValue rfs target)
      pure (.ok (some (.arr expected, .arr actual)))
  | .emitted line events =>
    let actual ← ((w.spanLines (.line line) own).filterMap fun l => match l.dir, l.body with
      | .out, .event name payload _ =>
        if (st.structure.contractsListing (st.refOf name)).isEmpty then none else some (name, payload)
      | _, _ => none).mapM fun (name, payload) => do
        let compared ← comparedOr fs (.payload name) payload
        pure (Value.obj [("event", ToValue.toValue (st.refOf name)), ("payload", compared)])
    match events.mapM fun ev => (w.fill line ev.payload).map (ev.event, ·) with
    | .error r => pure (.error r)
    | .ok filled =>
      let expected ← filled.mapM fun (ref, v) => do
        let compared ← comparedOr fs (.payload (ref.traceName own)) v
        pure (Value.obj [("event", ToValue.toValue ref), ("payload", compared)])
      pure (.ok (some (.arr (bag expected), .arr (bag actual))))
  | .requested line requests ends =>
    let span := w.spanLines (.line line) own
    let actualEnds := span.filterMap fun l => match l.dir, l.body with
      | .out, .unsubscribe to => some (Value.str to)
      | _, _ => none
    let expectedEnds := ends.mapM fun f => (w.messageOf line f).map fun k =>
      Value.str ((w.messages[k]?.map (·.id)).getD "")
    let actual ← (span.filterMap fun l =>
      match l.dir, l.body with
      | .out, .command name input => some (RequestType.command, name, input)
      | .out, .query name input => some (.query, name, input)
      | .out, .subscribe name input => some (.subscribe, name, input)
      | _, _ => none).mapM fun (type, name, input) => do
        pure (Value.obj [("kind", ToValue.toValue type), ("target", ToValue.toValue (st.refOf name)),
          ("input", ← comparedOr fs (.input name) input)])
    match requests.mapM fun r => (w.fill line r.input).map (r, ·), expectedEnds with
    | .error r, _ | _, .error r => pure (.error r)
    | .ok filled, .ok endIds =>
      let expected ← filled.mapM fun (r, v) => do
        pure (Value.obj [("kind", ToValue.toValue r.kind), ("target", ToValue.toValue r.target),
          ("input", ← comparedOr fs (.input (r.target.traceName own)) v)])
      pure (.ok (some (.obj [("requests", .arr (bag expected)), ("ends", .arr (bag endIds))],
        .obj [("requests", .arr (bag actual)), ("ends", .arr (bag actualEnds))])))
  | .offered look _ _ offered =>
    match lines[look]? with
    | some (.look _) => pure (.ok ((w.looked.lookup k).map fun found => (.bool offered, .bool found)))
    | _ => pure (.error (.notLook k look))

/-- The world with each expectation of Then compared; what one reports never stops the others. -/
def World.expect (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line)
    (expectations : List Expectation) : m World :=
  expectations.zipIdx.foldlM (init := w) fun w (e, k) => do
    match ← w.compared fsOf own lines k e with
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
