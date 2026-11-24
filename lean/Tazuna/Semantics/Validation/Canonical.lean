import Tazuna.Ir.Reads
import Tazuna.Semantics.Validation.NonCanonical

namespace Tazuna.Semantics.Validation.Canonical

open Tazuna.Ir
open Tazuna.Ir

/--
Whether the machine has one state, no context, and nothing to wait for, and turns one event into one command.
-/
def stateless (c : Chart) : Bool :=
  let waits := c.states.any fun st =>
    !st.deadlines.isEmpty || st.activities.any (· matches .calls ..) ||
      st.transitions.any (·.trigger matches .calls .. | .sends .. | .opens ..)
  c.receives.length == 1 && c.commands.length == 1 && c.queries.isEmpty && c.states.length ≤ 1 &&
    (schemaProperties c.context).isEmpty && !waits

def statelessMachines (s : Structure) : List NonCanonical :=
  s.definitions.filterMap fun d =>
    match d.body with
    | .machine c => if stateless c then some (.statelessMachine d.ref) else none
    | _ => none

/-- Whether `t` leads to its source state or a descendant of it. -/
def withinSource (c : Chart) (t : Transition) : Bool :=
  match t.source, t.target with
  | some source, some target => c.tree.isDescendant target source
  | _, _ => false

/--
The violation of a transition whose `reenter` is written exactly when it leads within its source. SCXML defaults
such a transition to external, and XState v5 to `reenter: false`. The defaults disagree, so the spec states it.
-/
def reenterOf (d : Ref) (t : Transition) : NonCanonical :=
  let ref : TransitionRef := { state := t.source, trigger := t.trigger, index := t.index }
  match t.reenter, t.source with
  | none, _ => .missingReenter d ref
  | some _, none => .reenterOnRoot d ref
  | some _, some _ => .reenterOutsideSource d ref

def reenters (s : Structure) : List NonCanonical :=
  s.definitions.flatMap fun d =>
    match d.chart? with
    | none => []
    | some c =>
      (c.on ++ c.states.flatMap (·.transitions)).filterMap fun t =>
        if t.reenter.isSome == withinSource c t then none else some (reenterOf d.ref t)

def onRejected (definition : Ref) (arrives : Bool) («at» : OnRejectedAt) : NonCanonical :=
  if arrives then .missingOnRejected definition «at» else .unreachableOnRejected definition «at»

/-- Whether an automation's command may be rejected with `unavailable`, which `onRejected: []` ignores. -/
def automationArrives (s : Structure) (service : String) (a : AutomationBody) : Bool :=
  (s.rejectionKinds service a.command).contains .unavailable

def automations (s : Structure) : List NonCanonical :=
  s.definitions.filterMap fun d =>
    match d.body with
    | .automation a =>
      if automationArrives s d.service a == a.onRejected then none
      else some (onRejected d.ref (automationArrives s d.service a) .automation)
    | _ => none

/-- A calls or sends of a state: the trigger of its `onRejected`, its target, and whether it writes `onRejected`. -/
def requestOf : Activity → Option (Trigger × Ref × Bool)
  | .calls name r written => some (.calls name .onRejected, r, written)
  | .sends name r written => some (.sends name .onRejected, r, written)
  | _ => none

/-- A state that calls or sends writes `onRejected` exactly when an answer may be rejected. -/
def states (s : Structure) : List NonCanonical :=
  s.definitions.flatMap fun d =>
    match d.chart? with
    | none => []
    | some c =>
      c.states.flatMap fun st =>
        st.activities.filterMap fun a =>
          (requestOf a).bind fun (trigger, r, written) =>
            let arrives := !(s.rejectionKinds d.service r).isEmpty
            if arrives == written then none else some (onRejected d.ref arrives (.request st.name trigger))

/--
Each binds of a command or automation with the bodies that receive it as `bound`, as Program.toFunctions pairs them
under withBound: a command's requires, ensures and decide, and an automation's guard and react.
-/
def boundReaders (p : Program) : List (Conditions × List Expr) :=
  let conditions (l : List Conditions) (d : Ref) := (l.filter (·.definition == d)).flatMap (·.conditions.map (·.body))
  let fns (l : List Fn) (d : Ref) := (l.filter (·.definition == d)).map (·.body)
  p.binding.map (fun c => (c, conditions p.requirement c.definition ++ conditions p.ensures c.definition ++
    fns p.decide c.definition)) ++
  p.automationBinding.map (fun c => (c, conditions p.automationGuard c.definition ++ fns p.react c.definition))

/-- Whether one of `bodies` reads the binding `name` of `bound`, or reads `bound` as a whole. -/
def readsBinding (bodies : List Expr) (name : String) : Bool :=
  bodies.any fun e => match argReads .bound e with
    | none => true
    | some fields => fields.contains name

/-- The bindings that none of the bodies receiving them reads. Before conversion the program is empty, so none. -/
def unreadBindings (s : Structure) : List NonCanonical :=
  (boundReaders s.program).flatMap fun x =>
    x.1.conditions.filterMap fun b =>
      if readsBinding x.2 b.name then none else some (.unreadBinding x.1.definition b.name)

/-- The NonCanonical violations that the structure shows. -/
def check (s : Structure) : List NonCanonical :=
  statelessMachines s ++ reenters s ++ automations s ++ states s ++ unreadBindings s

end Tazuna.Semantics.Validation.Canonical
