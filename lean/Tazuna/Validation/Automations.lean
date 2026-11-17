import Tazuna.Validation.Illegal

namespace Tazuna.Validation.Automations

open Tazuna.Data
open Tazuna.Spec

/--
An automation that sends a command to its own service. `index` is its position among those automations, in definition
order.
-/
structure Automation where
  index : Nat
  ref : Ref
  receives : Option Ref
  command : Option Ref

def automations (s : Structure) : List Automation :=
  (s.definitions.filterMap fun d =>
    match d.body with
    | .automation receives command _ _ =>
      if (command.map (·.service)) == some d.service then some (d.ref, receives, command) else none
    | _ => none).zipIdx.map fun ((ref, receives, command), index) => { index, ref, receives, command }

/--
The chains from `last` back to the automation at `start`, each automation receiving an event that the command of the
one before emits. `chain` holds the automations after the start so far. Only automations defined after the start and
not yet in the chain (`rest`) are followed, so that each cycle is found once, from its first automation.
-/
def walk (s : Structure) (as : List Automation) (start : Nat) (rest : List Nat) (last : Automation)
    (chain : List Ref) : List (List Ref) :=
  (s.emitsOf last.command).flatMap fun emitted =>
    (as.filter fun n => sameRef n.receives emitted).flatMap fun n =>
      if n.index == start then [chain]
      else if _h : start < n.index ∧ n.index ∈ rest then walk s as start (rest.erase n.index) n (chain ++ [n.ref])
      else []
termination_by rest.length
decreasing_by exact List.length_erase_of_mem _h.2 ▸ Nat.sub_lt (List.length_pos_of_mem _h.2) Nat.one_pos

def check (s : Structure) : List Illegal :=
  let as := automations s
  as.flatMap fun a => (walk s as a.index ((as.map (·.index)).erase a.index) a []).map (.automationCycle a.ref)

end Tazuna.Validation.Automations
