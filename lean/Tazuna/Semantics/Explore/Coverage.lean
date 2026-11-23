import Tazuna.Semantics.Service.Uncovered

/-!
The coverage targets of a spec: the parts that `verify --coverage` reports when no trace's replay reached them (Note.reached),
and that `generate` seeks inputs for. An external service's definitions are no target: no replay runs them, as verify
checks an external service's trace against its contract instead.
-/

namespace Tazuna.Semantics.Explore

open Tazuna.Ir Tazuna.Semantics.Service

/--
A target and the target that a run reaches first on the way to it, if any: a run reaches an answer of a request only
after the request, and a binding or condition only after the earlier one passed.
-/
structure Target where
  part : Uncovered
  after : Option Uncovered := none

/--
The targets of a command or query of a spec service: its request, and its answers, which are a success and a rejection
by each binding and each requires.
-/
def requestTargets (d : Ir.Definition) : List Target :=
  let parts (binds requires : List String) :=
    let request := Uncovered.request d.ref
    let answers := .successAnswer d.ref :: binds.map (.bindsRejection d.ref) ++ requires.map (.requiresRejection d.ref)
    { part := request } :: answers.map ({ part := ·, after := some request })
  match d.body with
  | .command c => parts c.binds c.requires
  | .query q => parts [] q.requires
  | _ => []

/-- The targets of an automation: a run of it, and both outcomes of each binding and guard condition that a run evaluates. -/
def automationTargets (d : Ir.Definition) : List Target :=
  match d.body with
  | .automation a =>
    let chain := a.binds.map (fun b => (Uncovered.automationBindingValue d.ref b, Uncovered.automationBindingNull d.ref b)) ++
      a.guard.map fun c => (Uncovered.automationGuard d.ref c true, Uncovered.automationGuard d.ref c false)
    let automation := Uncovered.automation d.ref
    { part := automation } :: chain.zipIdx.flatMap fun ((passed, failed), k) =>
      let after := if k == 0 then automation else ((chain[k - 1]?).map (·.1)).getD automation
      [{ part := passed, after := some after }, { part := failed, after := some after }]
  | _ => []

/--
The targets of a machine or screen: each state other than a history state, after its parent's entry (a top state after
the chart's start, the entry of its initial state), and each transition, with a false evaluation of each guard
condition, after the entry of its state (the chart's start for a transition of the whole chart).
-/
def chartTargets (d : Ir.Definition) : List Target :=
  match d.body with
  | .machine c | .screen c =>
    let started := Uncovered.state d.ref c.initial
    let transitions (after : Uncovered) (ts : List Ir.Transition) : List Target := ts.flatMap fun t =>
      let ref : Ir.TransitionRef := { state := t.source, trigger := t.trigger, index := t.index }
      ({ part := .transition d.ref ref, after := some after } : Target) ::
        t.guards.map ({ part := .guardFalse d.ref ref ·, after := some after })
    let states := c.states.flatMap fun s =>
      let after := match s.parent with
        | none => if s.name == c.initial then none else some started
        | some p => some (.state d.ref p)
      let history := match s.type with
        | .history => true
        | _ => false
      (if history then [] else [{ part := .state d.ref s.name, after }]) ++ transitions (.state d.ref s.name) s.transitions
    transitions started c.on ++ states
  | _ => []

/-- The coverage targets of the spec services' definitions: requests, then automations, then charts. -/
def targets (spec : Ir.Structure) : List Target :=
  let own := spec.definitions.filter fun d => !(spec.services.find? (·.name == d.ref.service)).any (·.external)
  own.flatMap requestTargets ++ own.flatMap automationTargets ++ own.flatMap chartTargets

/--
What `verify --coverage` reports: each target that no run reached, once the runs reached the target before it, so that
an unreached request hides its answers.
-/
def uncovered (spec : Ir.Structure) (reached : List Uncovered) : List Uncovered :=
  ((targets spec).filter fun t => !reached.contains t.part && t.after.all reached.contains).map (·.part)

end Tazuna.Semantics.Explore
