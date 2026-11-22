import Tazuna.Service.Input
import Tazuna.Sim.Network

/-!
The state of a world that explore merges paths by. Two worlds with equal fingerprints are taken to report alike on
every later path of the same length, up to what the second world's own path reported already (Search's Congruent),
which guarantees.md assumes; Search states what merging keeps under that assumption.

The fingerprint leaves out the records of what happened: the trace (apart from what later lines and the end of the run
read of it), violations, steps, the message count, and the violations already reported, which only stop a run from
reporting one twice. The internal queue and each instance's awaitingOnDone are empty after an input that completed. Each
service keeps the counts of its line ids and created keys, which decide the ids and keys of later lines and records. The
requests sent, with what arrived of each, are a set, since the end of the run checks them as one. The copies of a map
state follow their owner, in the order of their keys; a closed copy that no map state lists is left out, since a run
reads from it only that it is closed. The deadlines stay in entry order, which orders the deadlines due at one time.
-/

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service Tazuna.Sim

namespace Fingerprint

/-- `vs` in the order of their canonical texts. -/
def byText (vs : List Value) : List Value := vs.mergeSort fun a b => decide (a.canonical ≤ b.canonical)

/-- How many of `names` each name is, in name order. -/
def countsOf (names : List String) : Value :=
  .arr ((names.eraseDups.mergeSort (· ≤ ·)).map fun n => .arr [.str n, ToValue.toValue (names.count n)])

/-- How many distinct numbers of `all` are below `n`: only the order of turns and of counts is read. -/
def rank (all : List Nat) (n : Nat) : Nat := ((all.filter (· < n)).eraseDups).length

def bodyValue : LineBody → Value
  | .command t v => .arr [.str "command", ToValue.toValue t, v]
  | .query t v => .arr [.str "query", ToValue.toValue t, v]
  | .subscribe t v => .arr [.str "subscribe", ToValue.toValue t, v]
  | .event e p r => .arr [.str "event", ToValue.toValue e, p, ToValue.toValue r]
  | .answer to a => .arr [.str "answer", ToValue.toValue to, ToValue.toValue a]
  | .unsubscribe to => .arr [.str "unsubscribe", ToValue.toValue to]
  | .time => .arr [.str "time"]
  | .restart => .arr [.str "restart"]
  | .operation s c n p => .arr [.str "operation", ToValue.toValue s, .str c, ToValue.toValue n, ToValue.toValue p]

def requesterValue : Requester → Value
  | .automation a => .arr [.str a]
  | .state m n | .slot m n => .arr [ToValue.toValue m, .str n]

/-- Whether a line answers or ends the request `id`. -/
def answersOrEnds (id : LineId) (l : Line) : Bool :=
  match l.body with
  | .answer to _ | .unsubscribe to => to == id
  | _ => false

variable {m : Type → Type} [Monad m] [MonadNote m]

/--
The pending requests and, for each, what the end of the run reads of the trace: the time of its request line, the order
of the number of input lines before it, and whether a line answers or ends it; then the queued work.
-/
def requestsValue (s : State) : m Value := do
  let lines := s.lines.toList
  let traced ← s.pending.mapM fun p => do
    let (l, i) ← expectFound s!"request line of {p.id.text}"
      (lines.zipIdx.find? fun (l, _) => l.dir == .out && l.id == p.id)
    pure (p, l.time, (lines.take i).countP (·.dir == .in))
  let turns := s.pending.map (·.turn)
  let inputs := traced.map (·.2.2)
  pure (.obj [("pending", .arr (traced.map fun (p, time, before) =>
      .arr [ToValue.toValue p.id, ToValue.toValue p.activity.ref, requesterValue p.requester, p.input, .bool p.stale,
        ToValue.toValue (rank turns p.turn), ToValue.toValue time, ToValue.toValue (rank inputs before),
        .bool (lines.any (answersOrEnds p.id))])),
    ("queued", .arr (s.queued.map fun q => .arr [ToValue.toValue q.machine, .str q.state, .bool q.stale]))])

def instanceValue (i : Instance) : Value :=
  .obj [("id", ToValue.toValue i.id), ("entered", .arr (i.entered.map fun (n, t) => .arr [.str n, ToValue.toValue t])),
    ("context", i.context), ("held", .arr (i.held.map fun (n, v) => .arr [.str n, v])), ("input", i.input),
    ("lastChildren", .arr (i.lastChildren.map fun (n, cs) => .arr [.str n, ToValue.toValue cs])),
    ("shown", .arr (i.shown.map fun (n, v) => .arr [.str n, v])), ("closed", .bool i.closed)]

/-- Each machine and screen instance, with the copies of each of its map states in the order of their keys. -/
def machinesValue (s : State) : Value :=
  .arr (s.machines.map fun i => .arr [instanceValue i, .arr (i.copyKeys.map fun (map, keys) =>
    .arr [.str map, .arr (keys.filterMap fun k => (s.copies.find? (·.id == .copy i.id map k)).map instanceValue)])])

/-- The rows of each entity, in entity order, each row with its key in key order. -/
def recordsValue (records : Records) : Value :=
  .arr (((records.map (·.entity)).eraseDups.mergeSort (· ≤ ·)).map fun e =>
    .arr [.str e, .arr (((records.filter (·.entity == e)).mergeSort fun a b => decide (a.key.getD "" ≤ b.key.getD "")).map
      fun r => .arr [ToValue.toValue r.key, r.value])])

def exchangeValue (e : Exchange) : Value :=
  .arr [ToValue.toValue e.id, ToValue.toValue e.target, .str e.sender, e.input, ToValue.toValue e.answers,
    .arr (e.events.map fun (r, v) => .arr [ToValue.toValue r, v])]

end Fingerprint

variable {m : Type → Type} [Monad m] [MonadNote m]

open Fingerprint in
/-- The state of one running service that explore merges paths by. -/
def serviceFingerprint (s : State) : m Value := do
  pure (.obj [("now", ToValue.toValue s.now), ("lineCounts", countsOf (s.lines.toList.map (·.body.idName s.service))),
    ("keyCounts", countsOf s.createdEntities), ("records", recordsValue s.records), ("requests", ← requestsValue s),
    ("deadlines", .arr (s.deadlines.map fun d =>
      .arr [ToValue.toValue d.machine, .str d.state, .str d.name, ToValue.toValue d.time])),
    ("subscriptions", .arr (s.subscriptions.map fun u =>
      .arr [ToValue.toValue u.id, .arr [.str u.query, u.input], ToValue.toValue u.last])),
    ("machines", machinesValue s), ("stack", ToValue.toValue s.stack),
    ("commandAnswers", .arr (byText (s.commandAnswers.map fun (id, request, answer) =>
      .arr [ToValue.toValue id, .str request.name, request.input, ToValue.toValue answer]))),
    ("deliveries", .arr (byText (s.deliveries.map ToValue.toValue))),
    ("exchanges", .arr (byText (s.exchanges.map exchangeValue))), ("started", .bool s.started)])

open Fingerprint in
/--
The state of a world that explore merges paths by: the time, each running service's state, and the messages in flight.
All halted worlds are one, since explore extends none of them.
-/
def worldFingerprint (w : World) : m String := do
  if w.halted.isSome || w.states.any (·.2.halted.isSome) then return "halted"
  let states ← w.states.mapM fun (n, s) => do pure (Value.arr [.str n, ← serviceFingerprint s])
  pure (Value.arr [ToValue.toValue w.now, .arr states,
    .arr (w.messages.toList.filterMap fun m =>
      if m.status == .inFlight then some (.arr [.str m.sender, .str m.receiver, bodyValue m.body]) else none)]).canonical

end Tazuna.Explore
