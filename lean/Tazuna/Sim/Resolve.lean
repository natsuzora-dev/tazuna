import Tazuna.Sim.Network

/-! A line's handles name facts by content; each resolves to exactly one fact of the world, or is reported. -/

namespace Tazuna.Sim

open Tazuna.Data Tazuna.Semantics
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

/-- Whether `v` has each field of `pick`, at any depth, equal. -/
def picks (pick : Option Value) (v : Value) : Bool :=
  pick.all fun p => (v.overlay p).canonical == v.canonical

/-- The input of a request line, or the payload of an event line. -/
def _root_.Tazuna.Semantics.LineBody.value? : LineBody → Option Value
  | .command _ v | .query _ v | .subscribe _ v | .event _ v _ => some v
  | _ => none

/-- The target of a message that is a request. -/
def Message.target? (m : Message) : Option Syntax.Ref :=
  match m.body with
  | .command name _ | .query name _ | .subscribe name _ => some (Syntax.Ref.ofTraceName m.sender name)
  | _ => none

/-- The event of a message that is an event. -/
def Message.event? (m : Message) : Option Syntax.Ref :=
  match m.body with
  | .event name _ _ => some (Syntax.Ref.ofTraceName m.sender name)
  | _ => none

def World.sentBy (w : World) (line : Nat) : Option Sent := w.sent.find? (·.line == line)

/-- The only one of `found`, or the report of none or several for the handle `fact` of line `i`. -/
def World.only (w : World) (i : Nat) (fact : Fact) : List Nat → Except Report Nat
  | [k] => .ok k
  | [] => .error (.unresolvedReference i (ToValue.toValue fact))
  | ks => .error (.ambiguousReference i (ToValue.toValue fact) (ks.filterMap (w.messages[·]?) |>.map (·.describe)))

/-- The message that the handle `fact` of line `i` names. -/
def World.messageOf (w : World) (i : Nat) (fact : Fact) : Except Report Nat :=
  let indexed := w.messages.toList.zipIdx
  let matching (p : Message → Bool) := indexed.filterMap fun (m, k) => if p m then some k else none
  match fact with
  | .request o target input =>
    w.only i fact (matching fun m => m.origin == o && m.target? == some target && picks input ((m.body.value?).getD .null))
  | .event o event payload receiver =>
    w.only i fact (matching fun m => m.origin == o && m.event? == some event &&
      picks payload ((m.body.value?).getD .null) && receiver.all (· == m.receiver))
  | .answer o to =>
    match w.sentBy to with
    | none => .error (.unresolvedReference i (ToValue.toValue fact))
    | some s =>
      w.only i fact (matching fun m => m.origin == o && m.sender == s.receiver && match m.body with
        | .answer t _ => t == s.id
        | _ => false)
  | .line j => w.only i fact (w.carried.filterMap fun (l, k) => if l == j then some k else none)
  | .screen .. => .error (.unresolvedReference i (ToValue.toValue fact))

/-- The screen instance that the handle `fact` of line `i` names. -/
def World.screenOf (w : World) (i : Nat) (fact : Fact) : Except Report Opened :=
  let unresolved : Except Report Opened := .error (.unresolvedReference i (ToValue.toValue fact))
  match fact with
  | .screen o ref =>
    match w.opened.filter fun s => s.origin == o && s.service == ref.service && s.chart == ref.name with
    | [s] => .ok s
    | [] => unresolved
    | found => .error (.ambiguousReference i (ToValue.toValue fact) (found.map fun s => .str s.resource))
  | _ => unresolved

/-- The value of the `in` or `out` line `id` of `lines`, or of the first answer in direction `dir` to request `id`. -/
def lineValue? (lines : Array Line) (id : String) : Option Value :=
  lines.toList.findSome? fun l => if l.dir == .in && l.id == id then l.body.value? else none

def firstAnswer? (lines : Array Line) (dir : Dir) (to : String) : Option Answer :=
  lines.toList.findSome? fun l =>
    match l.body with
    | .answer t a => if l.dir == dir && t == to then some a else none
    | _ => none

/-- The value of the part `part` of the request that the handle `fact` of line `i` names. -/
def World.partOf (w : World) (i : Nat) (fact : Fact) (part : Part) : Except Report Value := do
  let missing : Except Report Value := .error (.missingOutput i (ToValue.toValue fact))
  let viaMessage : Except Report Value := do
    let k ← w.messageOf i fact
    let some m := w.messages[k]? | missing
    match part with
    | .input => match m.body.value? with
      | some v => pure v
      | none => missing
    | .output => match (firstAnswer? (w.state m.sender).lines .in m.id).bind (·.output?) with
      | some v => pure v
      | none => missing
  match fact with
  | .line j =>
    match w.sentBy j with
    | some s =>
      let lines := (w.state s.receiver).lines
      match part with
      | .input => match lineValue? lines s.id with
        | some v => pure v
        | none => missing
      | .output => match (firstAnswer? lines .out s.id).bind (·.output?) with
        | some v => pure v
        | none => missing
    | none => viaMessage
  | _ => viaMessage

def World.observed (w : World) (i : Nat) (r : ValueRef) : Except Report Value := do
  let v ← w.partOf i r.fact r.part
  match valueAt? v r.path with
  | some x => pure x
  | none => .error (.missingField i r.path v)

/-- The template's value with each referenced hole filled; a created hole keeps the written value. -/
def World.fill (w : World) (i : Nat) (t : Template) : Except Report Value :=
  t.holes.foldlM (init := t.value) fun v h =>
    match h.fill with
    | .ref r => do pure (setValueAt v (← w.observed i r) h.path)
    | .created => pure v

/-- The paths of the template's created holes. -/
def createdPaths (t : Template) : List (List String) :=
  t.holes.filterMap fun h => if h.fill == .created then some h.path else none

/-- `expected` with the value of `actual` at each of `paths`, which the scenario does not write. -/
def withCreated (paths : List (List String)) (expected actual : Value) : Value :=
  paths.foldl (init := expected) fun v p =>
    match valueAt? actual p with
    | some x => setValueAt v x p
    | none => v

end Tazuna.Sim
