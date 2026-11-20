import Tazuna.Service.Uncovered

/-!
What `test --coverage` reports: the parts of the spec that no scenario's run and no explored path reached, given the
parts that they reached (Note.reached).
-/

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service

/--
The unreached parts of a command or query: its request, or once a request reached it, the answers of a spec service's
command or query, which are a success and a rejection by each binding and each requires.
-/
def requestsUncovered (reached : List Uncovered) (d : Spec.Definition) : List Uncovered :=
  let parts (rejects : Option (List RejectionKind)) (binds requires : List String) :=
    let request := Uncovered.request d.ref
    let answers := if rejects.isSome then [] else
      .successAnswer d.ref :: binds.map (.bindsRejection d.ref) ++ requires.map (.requiresRejection d.ref)
    (if reached.contains request then answers else [request]).filter (!reached.contains ·)
  match d.body with
  | .command c => parts c.rejects c.binds c.requires
  | .query q => parts q.rejects [] q.requires
  | _ => []

/--
The unreached parts of an automation: a run of it, or once one reached it, both outcomes of each binding and guard
condition that a run evaluated, which needs the earlier one to have passed.
-/
def automationUncovered (reached : List Uncovered) (d : Spec.Definition) : List Uncovered :=
  match d.body with
  | .automation a =>
    let chain := a.binds.map (fun b => (Uncovered.automationBindingValue d.ref b, Uncovered.automationBindingNull d.ref b)) ++
      a.guard.map fun c => (Uncovered.automationGuard d.ref c true, Uncovered.automationGuard d.ref c false)
    let evaluated := chain.zipIdx.filter fun (_, k) => k == 0 || (chain[k - 1]?.any fun (passed, _) => reached.contains passed)
    let outcomes := evaluated.flatMap fun ((passed, failed), _) => [passed, failed]
    let automation := Uncovered.automation d.ref
    (if reached.contains automation then outcomes else [automation]).filter (!reached.contains ·)
  | _ => []

/--
The unreached parts of a machine or screen: each state other than a history state whose parent some run entered (the
chart for a top state, once it started), and each transition, with a false evaluation of each guard condition, of the
chart once it started and of each state that some run entered.
-/
def chartUncovered (reached : List Uncovered) (d : Spec.Definition) : List Uncovered :=
  match d.body with
  | .machine c | .screen c =>
    let entered (state : String) := reached.contains (.state d.ref state)
    let started := entered c.initial
    let transitions (ts : List Spec.Transition) : List Uncovered := ts.flatMap fun t =>
      let ref : Spec.TransitionRef := { state := t.source, trigger := t.trigger, index := t.index }
      .transition d.ref ref :: t.guards.map (.guardFalse d.ref ref)
    let states := c.states.flatMap fun s =>
      let parentEntered := match s.parent with
        | none => started || s.name == c.initial
        | some p => entered p
      let history := match s.type with
        | .history => true
        | _ => false
      (if history || !parentEntered then [] else [.state d.ref s.name]) ++
        (if entered s.name then transitions s.transitions else [])
    ((if started then transitions c.on else []) ++ states).filter (!reached.contains ·)
  | _ => []

/-- What `test --coverage` reports, by definition: requests, then automations, then charts. -/
def uncovered (spec : Spec.Structure) (reached : List Uncovered) : List Uncovered :=
  spec.definitions.flatMap (requestsUncovered reached) ++ spec.definitions.flatMap (automationUncovered reached) ++
    spec.definitions.flatMap (chartUncovered reached)

end Tazuna.Explore
