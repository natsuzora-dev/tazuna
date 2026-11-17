import Tazuna.Sim.Network

/-! A line's handles name facts by content; each resolves to exactly one fact of the world, or is reported. -/

namespace Tazuna.Sim

open Tazuna.Data Tazuna.Service
open Tazuna.Scenario (Fact Origin ValueRef Template Fill Part)

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

local instance {α : Type} : Inhabited (ExceptT InvalidScenario m α) := ⟨throw default⟩

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

def _root_.Tazuna.Service.LineBody.value? : LineBody → Option Value
  | .command _ v | .query _ v | .subscribe _ v | .event _ v _ => some v
  | _ => none

def _root_.Tazuna.Service.LineBody.requestType? : LineBody → Option Scenario.RequestType
  | .command .. => some .command
  | .query .. => some .query
  | .subscribe .. => some .subscribe
  | _ => none

def Message.target? (m : Message) : Option Spec.Ref :=
  match m.body with
  | .command name _ | .query name _ | .subscribe name _ => some (Spec.Ref.ofTraceName m.sender name)
  | _ => none

def Message.event? (m : Message) : Option Spec.Ref :=
  match m.body with
  | .event name _ _ => some (Spec.Ref.ofTraceName m.sender name)
  | _ => none

/--
The running end of the message, and the schema of the value that the message carries in its names: a request's input,
an event's payload. The sender is that end when it runs, and the receiver otherwise.
-/
def World.schemaOf? (w : World) (msg : Message) : Option (String × Schema) :=
  let side := if (w.role msg.sender).any (·.running) then msg.sender else msg.receiver
  match msg.body with
  | .command name _ | .query name _ | .subscribe name _ => some (side, .input (nameIn msg.sender side name))
  | .event name _ _ => some (side, .payload (nameIn msg.sender side name))
  | _ => none

def World.sentBy (w : World) (line : Nat) : Option Sent := w.sent.find? (·.line == line)

/-- The only one of `found`, or the report of none or several for the handle `fact` of line `i`. -/
def World.only (w : World) (i : Nat) (fact : Fact) : List Nat → Except InvalidScenario Nat
  | [k] => .ok k
  | [] => .error (.unresolvedReference i (ToValue.toValue fact))
  | ks => .error (.ambiguousReference i (ToValue.toValue fact) (ks.filterMap (w.messages[·]?) |>.map (·.describe)))

def ofExcept {α : Type} : Except InvalidScenario α → ExceptT InvalidScenario m α
  | .ok a => pure a
  | .error e => throw e

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

mutual
/--
The message that the handle `fact` of line `i` names. A pick's value is filled as the line fills its values, and
compared with the message's as the schema of its sender compares them. The handles of `requests` name only requests
equal as that schema compares them: the scenario cannot tell them apart, so which handle names which is no line's.
-/
partial def World.messageOf (w : World) (fsOf : String → Functions m) (i : Nat) (fact : Fact) :
    ExceptT InvalidScenario m Nat := do
  let indexed := w.messages.toList.zipIdx
  let matching (p : Message → Bool) := indexed.filterMap fun (msg, k) => if p msg then some k else none
  let picked (p : Message → Bool) (pick : Option Template) : ExceptT InvalidScenario m (List Nat) := do
    let pick ← pick.mapM (w.fill fsOf i)
    let found ← indexed.filterM fun (msg, _) => do
      if !p msg then return false
      match w.schemaOf? msg, msg.body.value? with
      | some (side, schema), some v => (picks (fsOf side) schema pick v : m Bool)
      | _, _ => pure false
    pure (found.map (·.2))
  match fact with
  | .request o kind target input =>
    ofExcept (w.only i fact (← picked (fun msg => msg.origin == o && msg.body.requestType? == some kind &&
      msg.target? == some target) input))
  | .requests _ _ _ _ h =>
    let found ← w.requestsOf fsOf i fact
    let place := ((w.assignments.lookup (fact.group?.getD fact)).bind (·[h]?)).getD h
    match found[place]? with
    | some k => pure k
    | none => throw (.unresolvedReference i (ToValue.toValue fact))
  | .event o event payload receiver =>
    ofExcept (w.only i fact (← picked (fun msg => msg.origin == o && msg.event? == some event &&
      receiver.all (· == msg.receiver)) payload))
  | .answer o to =>
    match w.sentBy to with
    | none => throw (.unresolvedReference i (ToValue.toValue fact))
    | some s =>
      ofExcept (w.only i fact (matching fun msg => msg.origin == o && msg.sender == s.receiver && match msg.body with
        | .answer t _ => t == s.id
        | _ => false))
  | .«end» o subscription =>
    let k ← w.messageOf fsOf i subscription
    let some sub := w.messages[k]? | throw (.unresolvedReference i (ToValue.toValue fact))
    ofExcept (w.only i fact (matching fun msg => msg.origin == o && msg.sender == sub.sender &&
      msg.receiver == sub.receiver && match msg.body with
        | .unsubscribe to => to == sub.id
        | _ => false))
  | .line j => ofExcept (w.only i fact (w.carried.filterMap fun (l, k) => if l == j then some k else none))
  | .screen .. => throw (.unresolvedReference i (ToValue.toValue fact))

/--
The messages, in sending order, of the group of the handle `fact` of `requests` of line `i`: the requests that `request`
with the same fields names, which must be equal as the schema of their sender compares them.
-/
partial def World.requestsOf (w : World) (fsOf : String → Functions m) (i : Nat) (fact : Fact) :
    ExceptT InvalidScenario m (List Nat) := do
  let .requests o kind target input _ := fact | throw (.unresolvedReference i (ToValue.toValue fact))
  let pick ← input.mapM (w.fill fsOf i)
  let found ← w.messages.toList.zipIdx.filterMapM fun (msg, k) => do
    if !(msg.origin == o && msg.body.requestType? == some kind && msg.target? == some target) then return none
    match w.schemaOf? msg, msg.body.value? with
    | some (side, schema), some v =>
      if ← (picks (fsOf side) schema pick v : m Bool) then
        return some (k, (← (comparedOr (fsOf side) schema v : m Value)).canonical)
      else return none
    | _, _ => return none
  if !found.all (·.2 == (found.head?.map (·.2)).getD "") then
    throw (.ambiguousReference i (ToValue.toValue fact) (found.filterMap (w.messages[·.1]?) |>.map (·.describe)))
  pure (found.map (·.1))

/--
The value of the part `part` of the request that the handle `fact` of line `i` names: of a line's request or of a
request that a running service sent, its input and the output of the first answer to it; of an answer, the output of the
one answer that the receiver of the line's request gave to it while the answer's origin was processed, which names
each answer of a subscription by the line that caused it; of an answer that a line states, its output.
-/
partial def World.partOf (w : World) (fsOf : String → Functions m) (i : Nat) (fact : Fact) (part : Part) :
    ExceptT InvalidScenario m Value := do
  let missing : ExceptT InvalidScenario m Value := throw (.missingOutput i (ToValue.toValue fact))
  let present : Option Value → ExceptT InvalidScenario m Value
    | some v => pure v
    | none => missing
  let viaMessage : ExceptT InvalidScenario m Value := do
    let k ← w.messageOf fsOf i fact
    let some msg := w.messages[k]? | missing
    match msg.body, part with
    | .answer _ a, .output => present a.output?
    | _, .input => present msg.body.value?
    | _, .output => present (((w.state msg.sender).lines.toList.findSome? fun l =>
        match l.dir, l.body with
        | .in, .answer t a => if t == msg.id then some a else none
        | _, _ => none).bind (·.output?))
  match fact, part with
  | .line j, _ =>
    match w.sentBy j with
    | some s =>
      match part with
      | .input => present (((w.state s.receiver).lines[s.position]?).bind (·.body.value?))
      | .output => present ((w.answersOf s).head?.bind (·.output?))
    | none => viaMessage
  | .answer o to, .output =>
    match w.sentBy to with
    | none => throw (.unresolvedReference i (ToValue.toValue fact))
    | some s =>
      match (w.spanLines o s.receiver).filterMap fun l => match l.dir, l.body with
          | .out, .answer t a => if t == s.id then some a else none
          | _, _ => none with
      | [a] => present a.output?
      | [] => throw (.unresolvedReference i (ToValue.toValue fact))
      | several => throw (.ambiguousReference i (ToValue.toValue fact) (several.map ToValue.toValue))
  | _, _ => viaMessage

partial def World.observed (w : World) (fsOf : String → Functions m) (i : Nat) (r : ValueRef) :
    ExceptT InvalidScenario m Value := do
  let v ← w.partOf fsOf i r.fact r.part
  match valueAt? v r.path with
  | some x => pure x
  | none => throw (.missingField i r.path v)

/-- The template's value with each referenced hole filled; a created hole keeps the written value. -/
partial def World.fill (w : World) (fsOf : String → Functions m) (i : Nat) (t : Template) :
    ExceptT InvalidScenario m Value :=
  t.holes.foldlM (init := t.value) fun v h =>
    match h.fill with
    | .ref r => do pure (setValueAt v (← w.observed fsOf i r) h.path)
    | .created => pure v
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

end Tazuna.Sim
