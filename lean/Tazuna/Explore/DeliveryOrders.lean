import Tazuna.Explore.StepOrders

/-!
The delivery-order search: a line that names several equal messages acts on each, in sending order by default. Nothing
outside tells which arrives first, so the search executes the scenario again with the line acting on them in every other
order, and compares each running service's outcome (ChoiceDependent.deliveryOrder), as TLA+ checks every value of a
nondeterministic choice.
-/

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service

/-- The sequences of `h` distinct numbers below `n`, in lexicographic order. -/
def injections (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | h + 1 => (injections n h).flatMap fun p => ((List.range n).filter (!p.contains ·)).map (p ++ [·])

/-- The definition that the message carries: its request's or event's, or that of the request that it answers or ends. -/
def definitionOf? (w : Sim.World) (msg : Sim.Message) : Option Spec.Ref :=
  let requested (to : LineId) := w.messages.toList.findSome? fun r =>
    if Sim.receivedId r.sender r.id == to then r.body.target? else none
  match msg.body with
  | .command r _ | .query r _ | .subscribe r _ | .event r _ _ => some r
  | .answer to _ => requested to
  | .unsubscribe to => requested (Sim.receivedId msg.sender to)
  | _ => none

/-- A line that acts on several messages in turn: the line, the number of messages, and the definition they carry. -/
structure Delivering where
  line : Nat
  count : Nat
  definition : Spec.Ref

/-- The lines of the execution that delivered several messages to a running receiver, each with its messages counted. -/
def Execution.delivering (executed : Execution) : List Delivering :=
  let w := executed.world
  let lines := (w.spans.filterMap fun sp => match sp.turn with
    | { origin := .line i, delivery := _ + 1 } => some i
    | _ => none).eraseDups
  lines.filterMap fun i =>
    let carried := w.carried.filterMap fun (l, k) => if l == i then w.messages[k]? else none
    (carried.findSome? (definitionOf? w)).map fun definition => { line := i, count := carried.length, definition }

/--
`lines`, the trace lines of the running service `service` in `w`, with the lines of each delivery of line `line` that it
processed put back at the place of its message, counted in sending order (`order` gives the place of each delivery):
equal messages that it processed in another order then compare by the message that each delivery took.
-/
def putBack {α : Type} (w : Sim.World) (service : String) (line : Nat) (order : List Nat) (lines : List α) : List α :=
  let spans := w.spans.filter fun sp => sp.service == service && sp.turn.origin == .line line
  match spans.head?, spans.getLast? with
  | some first, some last =>
    if !(spans.zip spans.tail).all fun (a, b) => a.to == b.from then lines else
    let placed := (spans.map fun sp => ((order[sp.turn.delivery]?).getD sp.turn.delivery, sp)).mergeSort
      fun a b => decide (a.1 ≤ b.1)
    lines.take first.from ++ placed.flatMap (fun (_, sp) => (lines.drop sp.from).take (sp.to - sp.from)) ++
      lines.drop last.to
  | _, _ => lines

/-- The outcome of `st` in the execution of the delivery order `order` of line `line`, its deliveries put back (putBack). -/
def Execution.putBackOutcome (w : Execution) (st : Service) (line : Nat) (order : List Nat) : Outcome :=
  let o := w.outcome st
  { o with lines := putBack w.world st.service line order o.lines }

/-- A delivery order of a line that the search ran, and the violation it found, if any. -/
structure DeliveryOrderTried where
  scenarioLine : Nat
  order : List Nat
  found : Option ChoiceDependent
deriving Repr, Inhabited

derive_wire DeliveryOrderTried serialize_only

/-- What the search of a scenario's delivery orders did: each order it ran in turn, and what it reports. -/
structure DeliveryOrderSearch where
  tried : List DeliveryOrderTried := []
  found : List ChoiceDependent := []
deriving Repr, Inhabited

section

variable {m : Type → Type} [Monad m]

/--
The search of the delivery orders of each line of `base`, the scenario executed in sending order, that delivered several
messages to a running receiver (Execution.delivering); `executeWith` executes the scenario with a delivery order. Each
other order of a line's messages is executed and compared with `base` for each running service, its deliveries put back
(putBack), until one differs, which is the line's one violation, or until deliveryOrderLimit orders of the line ran with
more left (searchLimit).
-/
def deliveryOrderSearch (compareFor : String → Compare m) (executeWith : List (Nat × List Nat) → m Execution)
    (base : Execution) : m DeliveryOrderSearch :=
  base.delivering.foldlM (init := {}) fun r d => do
    let searched ← (injections d.count d.count).drop 1 |>.foldlM (init := ({} : DeliveryOrderSearch)) fun r order => do
      if !r.found.isEmpty then return r
      if r.tried.length == deliveryOrderLimit then
        return { r with found := [.searchLimit d.definition deliveryOrderLimit] }
      let alternative ← executeWith [(d.line, order)]
      let outcomes := base.world.services.map fun (service, st) =>
        (service, base.outcome st, alternative.putBackOutcome st d.line order)
      let found ← deliveryOrder compareFor d.definition d.line order outcomes
      return { tried := r.tried ++ [{ scenarioLine := d.line, order, found }], found := found.toList }
    return { tried := r.tried ++ searched.tried, found := r.found ++ searched.found }

end

end Tazuna.Explore
