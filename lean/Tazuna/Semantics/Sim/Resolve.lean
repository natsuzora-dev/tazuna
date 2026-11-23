import Tazuna.Semantics.Sim.Network

/-!
A line's handles name facts by content; each resolves to the messages of the world that it names, all equal, or is
reported.
-/

namespace Tazuna.Semantics.Sim

open Tazuna.Ir Tazuna.Semantics.Service
open Tazuna.Semantics.Scenario (Fact Origin ValueRef Template Fill Part)

/-- The field of `v` at `path`; an array element's path entry is its index. -/
def valueAt? (v : Value) : List String → Option Value
  | [] => some v
  | k :: ks =>
    let next := match v with
      | .obj fs => fs.lookup k
      | .arr xs => k.toNat?.bind (xs[·]?)
      | _ => none
    next.bind (valueAt? · ks)

/-- `v` with the field at `path` set to `x`, adding the object fields on the way that `v` lacks. -/
def setValueAt (v x : Value) : List String → Value
  | [] => x
  | k :: ks =>
    match v with
    | .obj fs =>
      if (fs.lookup k).isSome then .obj (fs.map fun (n, w) => if n == k then (n, setValueAt w x ks) else (n, w))
      else .obj (fs ++ [(k, setValueAt (.obj []) x ks)])
    | .arr xs =>
      match k.toNat? with
      | some i => .arr (xs.modify i (setValueAt · x ks))
      | none => v
    | _ => .obj [(k, setValueAt (.obj []) x ks)]

variable {m : Type → Type} [Monad m]

/-- `v` as the simulation compares it for `schema` (Functions.unordered), or as it is when it does not match it. -/
def comparedOr (fs : Functions m) (schema : Schema) (v : Value) : m Value := do
  match ← fs.unordered schema v with
  | .ok c => pure c
  | .error _ => pure v

/-- Whether `v` has each field of `pick`, at any depth, equal, as the simulation compares values of `schema`. -/
def picks (fs : Functions m) (schema : Schema) (pick : Option Value) (v : Value) : m Bool := do
  match pick with
  | none => pure true
  | some p => pure ((← comparedOr fs schema (v.overlay p)).canonical == (← comparedOr fs schema v).canonical)

def _root_.Tazuna.Semantics.Service.LineBody.value? : LineBody → Option Value
  | .command _ v _ | .query _ v _ | .subscribe _ v _ | .event _ v _ => some v
  | _ => none

def _root_.Tazuna.Semantics.Service.LineBody.target? : LineBody → Option Ir.Ref
  | .command r .. | .query r .. | .subscribe r .. => some r
  | _ => none

def _root_.Tazuna.Semantics.Service.LineBody.requestType? : LineBody → Option Scenario.RequestType
  | .command .. => some .command
  | .query .. => some .query
  | .subscribe .. => some .subscribe
  | _ => none

def Message.target? (m : Message) : Option Ir.Ref :=
  match m.body with
  | .command r .. | .query r .. | .subscribe r .. => some r
  | _ => none

def Message.event? (m : Message) : Option Ir.Ref :=
  match m.body with
  | .event r _ _ => some r
  | _ => none

/--
The running end of the message, and the schema of the value that the message carries in its names: a request's input,
an event's payload. The sender is that end when it runs, and the receiver otherwise.
-/
def World.schemaOf? (w : World) (msg : Message) : Option (String × Schema) :=
  let side := if (w.role msg.sender).any (·.running) then msg.sender else msg.receiver
  match msg.body with
  | .command r .. | .query r .. | .subscribe r .. => some (side, .input r)
  | .event r _ _ => some (side, .payload r)
  | _ => none

/-- The requests that the client or a peer line `line` sent, or that the line delivered, in the order it did. -/
def World.sentBy (w : World) (line : Nat) : List Sent := w.sent.filter (·.line == line)

def ofExcept {α : Type} : Except InvalidScenario α → ExceptT InvalidScenario m α
  | .ok a => pure a
  | .error e => throw e

/-- `found`, or the report of none for the handle `fact` of line `i`. -/
def nonEmpty {α : Type} (i : Nat) (fact : Fact) : List α → Except InvalidScenario (List α)
  | [] => .error (.unresolvedReference i (ToValue.toValue fact))
  | ks => .ok ks

/-- The report that the messages `ks` that the handle `fact` of line `i` names differ. -/
def World.ambiguous (w : World) (i : Nat) (fact : Fact) (ks : List Nat) : InvalidScenario :=
  .ambiguousReference i (ToValue.toValue fact) (ks.filterMap (w.messages[·]?) |>.map (·.describe))

/-- The content of message `k` as the schema of its running end compares it, if it carries a value. -/
def World.comparedContent? (w : World) (fsOf : String → Functions m) (k : Nat) : m (Option String) := do
  let some msg := w.messages[k]? | return none
  match w.schemaOf? msg, msg.body.value? with
  | some (side, schema), some v => return some (← (comparedOr (fsOf side) schema v : m Value)).canonical
  | _, _ => return none

/--
The messages `found` that the handle `fact` of line `i` names, which must be equal: a line cannot tell them apart. Of
those on one channel, it takes the oldest still in flight, or else the first, as FIFO delivers them in sending order.
-/
def World.alikeMessages (w : World) (fsOf : String → Functions m) (i : Nat) (fact : Fact) (found : List Nat) :
    ExceptT InvalidScenario m (List Nat) := do
  let found ← ofExcept (nonEmpty i fact found)
  let keys ← found.mapM fun k => (w.comparedContent? fsOf k : m (Option String))
  if !keys.all (· == keys.head?.join) then throw (w.ambiguous i fact found)
  let inFlight (k : Nat) := (w.messages[k]?).any (·.status == .inFlight)
  let sameChannel (k j : Nat) := match w.messages[k]?, w.messages[j]? with
    | some a, some b => a.sameChannel b
    | _, _ => false
  pure (found.filter fun k =>
    let peers := found.filter (sameChannel k)
    k == ((peers.find? inFlight).getD (peers.headD k)))

/-- The screen instance that the handle `fact` of line `i` names. -/
def World.screenOf (w : World) (i : Nat) (fact : Fact) : Except InvalidScenario Opened :=
  let unresolved : Except InvalidScenario Opened := .error (.unresolvedReference i (ToValue.toValue fact))
  match fact with
  | .screen o ref =>
    match w.opened.filter fun s => s.origin == o && s.service == ref.service && s.id.chart == ref.name with
    | [s] => .ok s
    | [] => unresolved
    | found => .error (.ambiguousReference i (ToValue.toValue fact)
        (found.map (ToValue.toValue ·.id)))
  | _ => unresolved

/-- The lines that `service` wrote while `origin` was processed. -/
def World.spanLines (w : World) (o : Origin) (service : String) : List Service.Line :=
  let lines := (w.state service).lines
  w.spans.flatMap fun sp => if sp.origin == o && sp.service == service then (lines.extract sp.from sp.to).toList else []

/--
The answers that the receiver of the request `s` gave to it, from its `in` line up to the receiver's next `in` line with
its id: a resent request has its own answers.
-/
def World.answersOf (w : World) (s : Sent) : List Answer :=
  let after := (w.state s.receiver).lines.toList.zipIdx.drop (s.position + 1)
  let next := (after.find? fun (l, _) => l.dir == .in && l.id == s.id).map (·.2)
  after.filterMap fun (l, n) =>
    match l.body with
    | .answer t a => if l.dir == .out && t == s.id && next.all (n < ·) then some a else none
    | _ => none

/--
The first of `values`, the raw and compared values that the handle `fact` of line `i` reads, when the compared values are
all equal, or the report of none or of a difference.
-/
def alike (i : Nat) (fact : Fact) (missing : InvalidScenario) : List (Value × Value) → Except InvalidScenario Value
  | [] => .error missing
  | (v, c) :: rest =>
    if rest.all (·.2.canonical == c.canonical) then .ok v
    else .error (.ambiguousReference i (ToValue.toValue fact) (v :: rest.map (·.1)))

mutual
/--
The messages, in sending order, that the handle `fact` of line `i` names. A pick's value is filled as the line fills its
values, and compared with the message's as the schema of its sender compares them. The requests and events that one
handle names must be equal as that schema compares them; a line acts on each.
-/
def World.messagesOf (w : World) (fsOf : String → Functions m) (i : Nat) (fact : Fact) :
    ExceptT InvalidScenario m (List Nat) := do
  let indexed := w.messages.toList.zipIdx
  let matching (p : Message → Bool) := indexed.filterMap fun (msg, k) => if p msg then some k else none
  let picked (p : Message → Bool) (pick : Option Value) : ExceptT InvalidScenario m (List Nat) := do
    let found ← indexed.filterM fun (msg, _) => do
      if !p msg then return false
      match w.schemaOf? msg, msg.body.value? with
      | some (side, schema), some v => (picks (fsOf side) schema pick v : m Bool)
      | _, _ => pure false
    pure (found.map (·.2))
  match fact with
  | .request o kind target input =>
    let pick ← match input with
      | some t => some <$> w.fill fsOf i t
      | none => pure none
    w.alikeMessages fsOf i fact (← picked (fun msg => msg.origin == o && msg.body.requestType? == some kind &&
      msg.target? == some target) pick)
  | .event o event payload receiver =>
    let pick ← match payload with
      | some t => some <$> w.fill fsOf i t
      | none => pure none
    w.alikeMessages fsOf i fact (← picked (fun msg => msg.origin == o && msg.event? == some event &&
      receiver.all (· == msg.receiver)) pick)
  | .answer o to =>
    let sents := w.sentBy to
    let each := sents.map fun s => matching fun msg => msg.origin == o && msg.sender == s.receiver &&
      match msg.body with
      | .answer t _ => t == s.id
      | _ => false
    if each.any (·.length > 1) then throw (w.ambiguous i fact each.flatten)
    ofExcept (nonEmpty i fact each.flatten)
  | .«end» o subscription =>
    let subs ← w.messagesOf fsOf i subscription
    let each := subs.filterMap (w.messages[·]?) |>.map fun sub =>
      matching fun msg => msg.origin == o && msg.sender == sub.sender && msg.receiver == sub.receiver &&
        match msg.body with
        | .unsubscribe to => to == sub.id
        | _ => false
    if each.any (·.length > 1) then throw (w.ambiguous i fact each.flatten)
    ofExcept (nonEmpty i fact each.flatten)
  | .line j => ofExcept (nonEmpty i fact (w.carried.filterMap fun (l, k) => if l == j then some k else none))
  | .screen .. => throw (.unresolvedReference i (ToValue.toValue fact))
termination_by 2 * sizeOf fact
decreasing_by all_goals (simp_wf; omega)

/--
The value of the part `part` of the requests that the handle `fact` of line `i` names, which must be equal: of a line's
requests or of requests that a running service sent, their input and the output of the first answer to each; of
answers, the output of the one answer that the receiver of each of the line's requests gave to it while the answers'
origin was processed, which names each answer of a subscription by the line that caused it; of answers that a line
states, their output.
-/
def World.partOf (w : World) (fsOf : String → Functions m) (i : Nat) (fact : Fact) (part : Part) :
    ExceptT InvalidScenario m Value := do
  let missing : InvalidScenario := .missingOutput i (ToValue.toValue fact)
  let compared (side : String) (schema : Option Schema) (v : Value) : m Value :=
    match schema with
    | some s => comparedOr (fsOf side) s v
    | none => pure v
  let viaMessages : ExceptT InvalidScenario m Value := do
    let ks ← w.messagesOf fsOf i fact
    let values ← ks.filterMapM fun k => do
      let some msg := w.messages[k]? | return none
      let side := ((w.schemaOf? msg).map (·.1)).getD msg.sender
      let v? := match msg.body, part with
        | .answer _ a, .output => a.output?
        | _, .input => msg.body.value?
        | _, .output => ((w.state msg.sender).lines.toList.findSome? fun l =>
            match l.dir, l.body with
            | .in, .answer t a => if t == msg.id then some a else none
            | _, _ => none).bind (·.output?)
      let schema := match part with
        | .input => (w.schemaOf? msg).map (·.2)
        | .output => msg.target?.map Schema.output
      match v? with
      | some v => return some (v, ← compared side schema v)
      | none => return none
    if values.length != ks.length then throw missing
    ofExcept (alike i fact missing values)
  match fact, part with
  | .line j, _ =>
    match w.sentBy j with
    | [] => viaMessages
    | sents =>
      let values ← sents.filterMapM fun s => do
        let request := (w.state s.receiver).lines[s.position]?
        let v? := match part with
          | .input => request.bind (·.body.value?)
          | .output => (w.answersOf s).head?.bind (·.output?)
        let schema := request.bind (·.body.target?) |>.map fun r => match part with
          | .input => Schema.input r
          | .output => Schema.output r
        match v? with
        | some v => return some (v, ← compared s.receiver schema v)
        | none => return none
      if values.length != sents.length then throw missing
      ofExcept (alike i fact missing values)
  | .answer o to, .output =>
    match w.sentBy to with
    | [] => throw (.unresolvedReference i (ToValue.toValue fact))
    | sents =>
      let each := sents.map fun s => (w.spanLines o s.receiver).filterMap fun l => match l.dir, l.body with
        | .out, .answer t a => if t == s.id then some a else none
        | _, _ => none
      if each.any (·.isEmpty) then throw (.unresolvedReference i (ToValue.toValue fact))
      if each.any (·.length > 1) then
        throw (.ambiguousReference i (ToValue.toValue fact) (each.flatten.map ToValue.toValue))
      let outputs := each.flatten.filterMap (·.output?)
      if outputs.length != sents.length then throw missing
      ofExcept (alike i fact missing (outputs.map fun v => (v, v)))
  | _, _ => viaMessages
termination_by 2 * sizeOf fact + 1

def World.observed (w : World) (fsOf : String → Functions m) (i : Nat) : ValueRef →
    ExceptT InvalidScenario m Value
  | { fact, part, path } => do
    let v ← w.partOf fsOf i fact part
    match valueAt? v path with
    | some x => pure x
    | none => throw (.missingField i path v)
termination_by r => 2 * sizeOf r
decreasing_by simp_wf; omega

/-- The template's value with each referenced hole filled; a created hole keeps the written value. -/
def World.fill (w : World) (fsOf : String → Functions m) (i : Nat) : Template → ExceptT InvalidScenario m Value
  | { value, holes } =>
    holes.attach.foldlM (init := value) fun v ⟨h, _mem⟩ =>
      match h with
      | { path, fill := .ref r } => do pure (setValueAt v (← w.observed fsOf i r) path)
      | { fill := .created, .. } => pure v
termination_by t => 2 * sizeOf t
decreasing_by have := List.sizeOf_lt_of_mem _mem; simp only [Scenario.Hole.mk.sizeOf_spec, Scenario.Fill.ref.sizeOf_spec] at this; simp_wf; omega
end

/-- What a created hole holds when the simulation compares: a key that the peer created and that no handle names. -/
def createdMark : String := "<created>"

/-- `v` with createdMark at the place of each created hole of `t`. -/
def markCreated (t : Template) (v : Value) : Value :=
  t.holes.foldl (init := v) fun v h => if h.fill == .created then setValueAt v (.str createdMark) h.path else v

/--
`actual` with createdMark in place of each key that `peer` created and that no handle of `t` names in `filled`, its
value: a written literal never stands for a created key.
-/
def World.maskCreated (w : World) (peer : String) (t : Template) (filled actual : Value) : Value :=
  let named := t.holes.flatMap fun h => match h.fill with
    | .ref _ => ((valueAt? filled h.path).map (·.strings)).getD []
    | .created => []
  let created := (w.state peer).created.map (·.2)
  actual.mapStrings fun x => if created.contains x && !named.contains x then createdMark else x

end Tazuna.Semantics.Sim
