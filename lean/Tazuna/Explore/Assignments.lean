import Tazuna.Explore.StepOrders

/-!
The assignment search: it executes a scenario again with every other assignment of the handles of its `requests` groups to
their equal messages, and compares each execution's outcome with the execution in which each handle names the message at its own
place (ChoiceDependent.assignment), as TLA+ checks every value of a nondeterministic choice.
-/

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service
open Tazuna.Scenario (Fact)

/-- A group of handles of `requests`: its group (Fact.group?), the line that first names it, and its handles named. -/
structure HandleGroup where
  group : Fact
  line : Nat
  handles : Nat

/--
The groups of handles of `requests` that the lines and expectations of `sc` name, in the order they first name them,
each with handles up to the greatest that is named.
-/
def handleGroups (sc : Scenario) : List HandleGroup :=
  let named := (sc.lines.zipIdx.flatMap fun (l, i) => l.named.map (·, i)) ++
    sc.expectations.flatMap fun e => e.named.map (·, e.line)
  named.foldl (init := []) fun groups (f, i) =>
    match f, f.group? with
    | .requests _ _ _ _ h, some g =>
      if groups.any (·.group == g) then
        groups.map fun x => if x.group == g then { x with handles := max x.handles (h + 1) } else x
      else groups ++ [{ group := g, line := i, handles := h + 1 }]
    | _, _ => groups

/-- The sequences of `h` distinct numbers below `n`, in lexicographic order. -/
def injections (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | h + 1 => (injections n h).flatMap fun p => ((List.range n).filter (!p.contains ·)).map (p ++ [·])

/--
Every assignment of the groups, each group with `size` messages: its handles to distinct places below `size`, in
lexicographic order, the first group's first. The first assignment has each handle at its own place, when every group
has as many messages as handles, and there is none otherwise.
-/
def assignmentsOf : List (HandleGroup × Nat) → List (List (Fact × List Nat))
  | [] => [[]]
  | (g, size) :: rest => (injections size g.handles).flatMap fun a => (assignmentsOf rest).map ((g.group, a) :: ·)

def targetOf : Fact → Spec.Ref
  | .requests _ _ target _ _ => target
  | _ => default

/-- The assignment as the violation writes it. -/
def assignedOf (a : List (Fact × List Nat)) : List Assigned :=
  a.map fun (g, handles) => { target := targetOf g, handles }

/-- An assignment that the search ran, and the violation it found, if any. -/
structure AssignmentTried where
  assigned : List Assigned
  found : Option ChoiceDependent
deriving Repr, Inhabited

derive_wire AssignmentTried serialize_only

/-- What the search of a scenario's assignments did: each assignment it ran in turn, and what it reports. -/
structure AssignmentSearch where
  tried : List AssignmentTried := []
  found : List ChoiceDependent := []
deriving Repr, Inhabited

section

variable {m : Type → Type} [Monad m]

/-- The number of messages of the group `g` in the world `w`, or 0 when its handle reports. -/
def groupSize (fsOf : String → Functions m) (w : Sim.World) (g : HandleGroup) : m Nat := do
  match ← (w.requestsOf fsOf g.line g.group).run with
  | .ok found => pure found.length
  | .error _ => pure 0

/--
The search of the assignments of the handle groups `groups` of a scenario, from `base`, the scenario executed with each
handle at its own place; `sizeOf` gives the number of messages of a group in `base`, and `executeWith` executes the scenario
with an assignment. Each other assignment is executed and compared with `base` for each running service, until one
differs, which is the one violation it reports, or until assignmentLimit assignments ran with more left (searchLimit).
-/
def assignmentSearch (compareFor : String → Compare m) (sizeOf : HandleGroup → m Nat)
    (executeWith : List (Fact × List Nat) → m Execution) (base : Execution) (groups : List HandleGroup) : m AssignmentSearch := do
  if groups.isEmpty then return {}
  let sized ← groups.mapM fun g => do pure (g, ← sizeOf g)
  let first := ((groups.head?).map (targetOf ·.group)).getD default
  (assignmentsOf sized).drop 1 |>.foldlM (init := {}) fun r a => do
    if !r.found.isEmpty then return r
    if r.tried.length == assignmentLimit then return { r with found := [.searchLimit first assignmentLimit] }
    let alternative ← executeWith a
    let changed := (a.zip sized).find? fun ((_, handles), (g, _)) => handles != List.range g.handles
    let definition := (changed.map (targetOf ·.2.1.group)).getD first
    let outcomes := base.world.services.map fun (service, st) => (service, base.outcome st, alternative.outcome st)
    let found ← assignment compareFor definition (assignedOf a) outcomes
    return { tried := r.tried ++ [{ assigned := assignedOf a, found }], found := found.toList }

end

end Tazuna.Explore
