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

/-- `v` in the canonical form of `schema`, or as it is when it does not match the schema. -/
def canonicalOr (fs : Functions m) (schema : Schema) (v : Value) : m Value := do
  match ← fs.canonical schema v with
  | .ok c => pure c
  | .error _ => pure v

/-- The answer with its output in the canonical form of the output of `target`. -/
def canonicalAnswer (fs : Functions m) (target : String) (a : Answer) : m Value := do
  match a with
  | .accepted (some o) => pure (ToValue.toValue (Answer.accepted (some (← canonicalOr fs (.output target) o))))
  | .fulfilled o => pure (ToValue.toValue (Answer.fulfilled (← canonicalOr fs (.output target) o)))
  | a => pure (ToValue.toValue a)

/-- The first string of `v` of the form of a key of an entity of `st` that no running service has created. -/
def World.uncreated (w : World) (st : Service) (v : Value) : Option (String × String) :=
  let created := w.states.flatMap fun (_, s) => s.created.map (·.2)
  v.strings.findSome? fun x =>
    if created.contains x then none
    else (st.entities.find? fun e => !st.singles.contains e && Syntax.isKeyOf e x).map (x, ·)

/-- The world with what the line `i` processed by `service` wrote first as an `in` line recorded as its request. -/
def World.recordSent (w : World) (i : Nat) (service : String) (before : Nat) : World :=
  match ((w.state service).lines.extract before).toList.find? (·.dir == .in) with
  | some l => { w with sent := w.sent ++ [{ line := i, receiver := service, id := l.id }] }
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

/-- Whether the message carries a value equal to `expected` in the canonical form of `schema` of its sender. -/
def sameValue (fs : Functions m) (schema : Schema) (created : List (List String)) (expected actual : Value) :
    m Bool := do
  pure ((← canonicalOr fs schema (withCreated created expected actual)).canonical == actual.canonical)

/--
The message in flight from the running peer `peer` to `receiver` that is the line `i`'s, among those that `fits`
accepts: the only one, or the report of none or several.
-/
def World.peerMessage (w : World) (i : Nat) (peer : String) (fits : Message → m Bool) : m (Except Report Nat) := do
  let found ← w.messages.toList.zipIdx.filterM fun (msg, _) =>
    if msg.status == .inFlight && msg.sender == peer then fits msg else pure false
  pure (match found with
    | [(_, k)] => .ok k
    | [] => .error (.unpairedPeerLine i peer)
    | several => .error (.ambiguousPeerLine i peer (several.map (·.1.describe))))

/-- The world after the message `k` that line `i` carried is delivered, with the line's request recorded. -/
def World.deliverCarried (w : World) (fsOf : String → Functions m) (i k : Nat) : m World := do
  let w := { w with carried := w.carried ++ [(i, k)] }
  match w.messages[k]? with
  | none => pure w
  | some msg =>
    let w ← w.deliver fsOf (.line i) k
    pure (match msg.body with
      | .command .. | .query .. | .subscribe .. =>
        { w with sent := w.sent ++ [{ line := i, receiver := msg.receiver, id := receivedId msg.sender msg.id }] }
      | _ => w)

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

/-- The world after the deadlines due by `time` of the running service fire, ties ordered by `order`. -/
def fireTo (time : Time) (order : List DeadlineId) : Service → Functions m → State → m State :=
  fun st fs s => do
    let s ← fireDue st fs time Limit.dueDeadlines.max none
      { s with deadlineOrder := order, tieOrderRequired := true }
    pure { s.checkOrderUsed with now := max s.now time, tieOrderRequired := false }

/-- The world after line `i` of the scenario of the own service `own`, which `expectations` follow. -/
def World.line (w : World) (fsOf : String → Functions m) (own : String) (lines : List Scenario.Line)
    (expectations : List Expectation) (i : Nat) : Scenario.Line → m World
  | .request none type target input sameIdAs => w.clientRequest fsOf i type target input sameIdAs
  | .request (some peer) type target input _ => do
    if w.role peer != some .run then return w.report (.wrongRole i peer)
    w.attempt (w.fill i input) fun v => do
      let name := target.traceName peer
      let fits (msg : Message) : m Bool :=
        let typed := match type, msg.body with
          | .command, .command n x | .query, .query n x | .subscribe, .subscribe n x => if n == name then some x else none
          | _, _ => none
        match typed with
        | some x => if msg.receiver == target.service then
            sameValue (fsOf peer) (.input name) (createdPaths input) v x else pure false
        | none => pure false
      match ← w.peerMessage i peer fits with
      | .error e => pure (w.report e)
      | .ok k => w.deliverCarried fsOf i k
  | .unsubscribe peer subscription => do
    let some s := w.sentBy subscription
      | return w.report (.unresolvedReference i (ToValue.toValue (Fact.line subscription)))
    match peer with
    | none => w.act fsOf (.line i) s.receiver fun st fs t => endSubscription st fs t (.id s.id)
    | some p =>
      if w.role p != some .run then return w.report (.wrongRole i p)
      let fits (msg : Message) : m Bool := pure (msg.receiver == s.receiver && match msg.body with
        | .unsubscribe to => receivedId p to == s.id
        | _ => false)
      match ← w.peerMessage i p fits with
      | .error e => pure (w.report e)
      | .ok k => w.deliverCarried fsOf i k
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
      let target := ((msg.target?.map (·.traceName msg.sender)).getD "")
      match w.role peer with
      | some .external =>
        if msg.status != .inFlight then return w.report (.notInFlight i msg.describe)
        w.attempt (w.fill i answer) fun v => do
          let .ok (a : Answer) := FromValue.fromValue v | return w.report (.malformedValue i v)
          let to := receivedId msg.sender msg.id
          let reply : Message := { sender := peer, receiver := msg.sender, id := s!"answer:{to}",
                                   body := .answer to a, origin := .line i, channel := some to, status := .inFlight }
          let w := w.setStatus k .delivered
          let w := { w with messages := w.messages.push reply }
          w.deliverCarried fsOf i w.messages.size.pred
      | some .run =>
        let to := receivedId msg.sender msg.id
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
            let fs := fsOf msg.sender
            let shown ← canonicalAnswer fs target actual
            let expected ← match (FromValue.fromValue (withCreated (createdPaths answer) v shown) :
                Except String Answer) with
              | .ok a => canonicalAnswer fs target a
              | .error _ => pure v
            let w := if expected.canonical == shown.canonical then w
              else w.report (.differentPeerAnswer i expected shown)
            w.deliverCarried fsOf i j
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
              sameValue (fsOf peer) (.payload n) (createdPaths payload) v x
            else pure false
          | _ => pure false
        match ← w.peerMessage i peer fits with
        | .error e => pure (w.report e)
        | .ok k => w.deliverCarried fsOf i k
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
      match (w.messages.toList.take k).find? fun n => n.status == .inFlight && n.sameChannel msg with
      | some earlier => pure (w.report (.overtaking i msg.describe earlier.describe))
      | none => w.deliverCarried fsOf i k
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
  | .inFlight message =>
    w.attempt (w.messageOf i message) fun k => do
      let some msg := w.messages[k]? | return w
      pure { w with inFlight := w.inFlight ++ [(msg.sender, msg.receiver, msg.channel)] }
  | .at time order => do
    if time.time ≤ w.now then return w.report (.notLater i time.time w.now)
    let w ← w.services.foldlM (init := w) fun w (service, _) =>
      if w.stopped then pure w else
      w.act fsOf (.line i) service (fireTo time.time ((order.filter (·.service == service)).map (·.deadline)))
    pure { w with now := time.time }
  | .restart => w.act fsOf (.line i) own restart

/-- The world with each message left in flight reported, unless an inFlight line covers its channel. -/
def World.checkEnd (w : World) : World :=
  w.messages.foldl (init := w) fun w msg =>
    if msg.status == .inFlight && !w.inFlight.contains (msg.sender, msg.receiver, msg.channel) then
      w.report (.leftInFlight msg.describe)
    else w

def requestName? : LineBody → Option String
  | .command name _ | .query name _ | .subscribe name _ => some name
  | _ => none

/-- The values in canonical form, in a bag's order: by their canonical JSON. -/
def bag (vs : List Value) : List Value := vs.mergeSort fun a b => decide (a.canonical ≤ b.canonical)

def World.lineSpan (w : World) (service : String) (line : Nat) : List Semantics.Line :=
  let lines := (w.state service).lines
  w.spans.flatMap fun sp =>
    if sp.origin == .line line && sp.service == service then (lines.extract sp.from sp.to).toList else []

/-- The actual and expected values of the expectation `e`, which Then compares. -/
def World.compared (w : World) (fsOf : String → Functions m) (own : String) (k : Nat) (e : Expectation) :
    m (Except Report (Option (Value × Value))) := do
  let some st := w.services.lookup own | return .ok none
  let fs := fsOf own
  match e with
  | .answered line answers =>
    let some s := w.sentBy line | return .error (.unresolvedReference line (ToValue.toValue (Fact.line line)))
    let lines := (w.state s.receiver).lines
    let target := (lines.toList.findSome? fun l => if l.dir == .in && l.id == s.id then requestName? l.body else none).getD ""
    let rfs := fsOf s.receiver
    let actual ← (lines.toList.filterMap fun l => match l.body with
      | .answer t a => if l.dir == .out && t == s.id then some a else none
      | _ => none).mapM (canonicalAnswer rfs target)
    match answers.mapM (w.fill line) with
    | .error r => pure (.error r)
    | .ok vs =>
      let expected ← vs.mapM fun v => match (FromValue.fromValue v : Except String Answer) with
        | .ok a => canonicalAnswer rfs target a
        | .error _ => pure v
      pure (.ok (some (.arr expected, .arr actual)))
  | .emitted line events =>
    let actual := (w.lineSpan own line).filterMap fun l => match l.dir, l.body with
      | .out, .event name payload _ =>
        if (st.structure.contractsListing (st.refOf name)).isEmpty then none
        else some (Value.obj [("event", ToValue.toValue (st.refOf name)), ("payload", payload)])
      | _, _ => none
    match events.mapM fun ev => (w.fill line ev.payload).map (ev.event, ·) with
    | .error r => pure (.error r)
    | .ok filled =>
      let expected ← filled.mapM fun (ref, v) => do
        pure (Value.obj [("event", ToValue.toValue ref), ("payload", ← canonicalOr fs (.payload (ref.traceName own)) v)])
      pure (.ok (some (.arr (bag expected), .arr (bag actual))))
  | .requested line requests =>
    let actual := (w.lineSpan own line).filterMap fun l =>
      let entry (type : RequestType) (name : String) (input : Value) :=
        some (Value.obj [("kind", ToValue.toValue type), ("target", ToValue.toValue (st.refOf name)), ("input", input)])
      match l.dir, l.body with
      | .out, .command name input => entry .command name input
      | .out, .query name input => entry .query name input
      | .out, .subscribe name input => entry .subscribe name input
      | _, _ => none
    match requests.mapM fun r => (w.fill line r.input).map (r, ·) with
    | .error r => pure (.error r)
    | .ok filled =>
      let expected ← filled.mapM fun (r, v) => do
        pure (Value.obj [("kind", ToValue.toValue r.kind), ("target", ToValue.toValue r.target),
          ("input", ← canonicalOr fs (.input (r.target.traceName own)) v)])
      pure (.ok (some (.arr (bag expected), .arr (bag actual))))
  | .offered _ _ _ offered =>
    pure (.ok ((w.looked.lookup k).map fun found => (.bool offered, .bool found)))

def World.expect (w : World) (fsOf : String → Functions m) (own : String) (expectations : List Expectation) :
    m World :=
  expectations.zipIdx.foldlM (init := w) fun w (e, k) => do
    if w.stopped then return w
    match ← w.compared fsOf own k e with
    | .error r => pure (w.report r)
    | .ok none => pure w
    | .ok (some (expected, actual)) =>
      pure (if expected.canonical == actual.canonical then w else w.report (.unmetExpectation k expected actual))

def rowsOf (records : List GivenRecord) : Records :=
  records.map fun r => { entity := r.entity, key := r.key, value := r.value }

/--
The world before the begin: the roles that Given lists, and each running service with its Given records at the start,
or why the Lean model does not cover a service.
-/
def World.start (j : Syntax.Structure) (sc : Scenario) : Except String World := do
  let peers := sc.given.peers.map fun p => (p.service, p.peer)
  let roles := (sc.service, Role.own) :: peers.map fun (s, p) => (s, match p with
    | .run _ => Role.run
    | .external => .external
    | .skip _ => .skip)
  let running := (sc.service, sc.given.records) :: peers.filterMap fun (s, p) => match p with
    | .run records => some (s, records)
    | _ => none
  let services ← running.mapM fun (s, _) => do pure (s, ← j.service s)
  let now := sc.given.start.time
  pure { now, roles, services, states := running.map fun (s, records) => (s, { now, records := rowsOf records }) }

/-- The world after the scenario runs from `start`, each running service asking `fsOf` its spec's functions. -/
def simulate (fsOf : String → Functions m) (start : World) (sc : Scenario) : m World := do
  let missing := start.services.flatMap fun (s, st) => (missingSingles st (start.state s).records).map (s, ·)
  if let (s, e) :: _ := missing then return start.report (.missingRecord s e)
  let w ← start.services.foldlM (init := start) fun w (s, _) =>
    if w.stopped then pure w else w.act fsOf .begin s begin
  let w ← sc.lines.zipIdx.foldlM (init := w) fun w (l, i) =>
    if w.stopped then pure w else w.line fsOf sc.service sc.lines sc.expectations i l
  if w.stopped then return w
  w.checkEnd.expect fsOf sc.service sc.expectations

end Tazuna.Sim
