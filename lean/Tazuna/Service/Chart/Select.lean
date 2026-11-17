import Tazuna.Service.State

/-! This module selects transitions as SCXML selectTransitions and removeConflictingTransitions do. -/

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def choose (st : Service) (s : State) (i : Instance) (extra : Extra) :
    List Transition → m (Except Fault (Option Transition))
  | [] => pure (.ok none)
  | t :: rest =>
    if t.guarded then do
      match ← fs.guard (s.scopeOf i t.source) s.records t extra with
      | .error e => pure (.error (issueViolation st (st.ref i.chart.name) e))
      | .ok true => pure (.ok (some t))
      | .ok false => choose st s i extra rest
    else pure (.ok (some t))

def firstLevel (st : Service) (s : State) (extra : Extra) : List (Instance × List Transition) →
    m (Except Fault (Option (String × Transition)))
  | [] => pure (.ok none)
  | (i, ts) :: rest => do
    MonadNote.note (.readStates ((ts.head?.bind (·.source)).map (i.resource, ·)).toList)
    match ← choose fs st s i extra ts with
    | .error v => pure (.error v)
    | .ok (some t) => pure (.ok (some (i.resource, t)))
    | .ok none => firstLevel st s extra rest

/--
Whether an event with `payload` reaches copy `c`. As in BPMN correlation, the payload's key fields choose the copies
that an event reaches.
-/
def reaches (st : Service) (c : Instance) (payload : Value) : m (Except Fault Bool) := do
  match c.copyOf with
  | none => pure (.ok true)
  | some co =>
    match ← fs.copyKey c.chart.name co.map payload with
    | .error e => pure (.error (issueViolation st (st.ref c.chart.name) e))
    | .ok none => pure (.ok true)
    | .ok (some none) => pure (.ok false)
    | .ok (some (some k)) => pure (.ok (k == co.encodedKey))

def reachedCopies (st : Service) (s : State) (top : Instance) (payload : Value) :
    m (Except Fault (List String)) :=
  top.copyResources.foldlM (init := .ok []) fun acc c => do
    match acc, s.machine? c with
    | .ok found, some ci =>
      match ← reaches fs st ci payload with
      | .error v => pure (.error v)
      | .ok reached => pure (.ok (if reached then found ++ [c] else found))
    | acc, _ => pure acc

/-- The states that transition `c` exits, by resource, including the states of copies of exited map states. -/
def State.exitKeys (s : State) (c : String × Transition) : List (String × String) :=
  match s.machine? c.1 with
  | none => []
  | some i =>
    (i.chart.exitsOf i.active c.2).flatMap fun n =>
      (c.1, n) :: (i.copyKeysOf n).flatMap fun k =>
        let cr := copyName i.resource n k
        ((s.machine? cr).map fun ci => ci.active.map (cr, ·)).getD []

/--
The enabled transitions without conflicts (SCXML removeConflictingTransitions): of two transitions whose exit sets
overlap, the one from the inner state is kept, and if neither is inner, the earlier one.
-/
def State.removeConflicts (s : State) (c : Chart) (enabled : List (String × Transition)) : List (String × Transition) :=
  let tree := c.tree
  enabled.foldl (fun kept t₁ =>
    let exits := s.exitKeys t₁
    let overlapping := kept.filter fun t₂ => (s.exitKeys t₂).any (· ∈ exits)
    if overlapping.any fun t₂ => !tree.isInside t₁.2.source t₂.2.source then kept
    else kept.filter (· ∉ overlapping) ++ [t₁]) []

/-- The leaves of `top` in document order, where the atomic states of reached copies replace their map state. -/
def leavesOf (s : State) (top : Instance) (reached : List String) : List (String × Option String) :=
  let topLeaves := top.chart.tree.leaves top.active
  let copyLeaves := reached.filterMap fun h => (s.machine? h).map fun ci => (h, ci.chart.tree.leaves ci.active)
  let atomic := fun (h, n) =>
    if h == top.resource then n ∈ topLeaves && !(top.copyKeysOf n).any (copyName top.resource n · ∈ reached)
    else (copyLeaves.lookup h).any (n ∈ ·)
  let found := top.documentOrder.filter atomic
  if found.isEmpty then [(top.resource, none)] else found.map fun (h, n) => (h, some n)

def eventLeaves (st : Service) (s : State) (top : Instance) (payload : Value) :
    m (Except Fault (List (String × Option String))) := do
  pure ((← reachedCopies fs st s top payload).map (leavesOf s top))

/--
The levels from the leaf to the root, each with its transitions on `trigger`. For a copy's leaf, the owner `top` chooses
at the levels of the map state and its ancestors.
-/
def levelsOf (top holder : Instance) (trigger : Spec.Trigger) (leaf : Option String) : List (Instance × List Transition) :=
  let path := match leaf with
    | none => []
    | some n => top.chart.tree.pathOf n
  (path.zipIdx.reverse.map fun (n, k) => (if k < holder.depth then top else holder, top.chart.transitionsAt (some n) trigger)) ++
  [(top, top.chart.transitionsAt none trigger)]

/--
The first transition on `trigger` (`.on key` or `.always`) whose guard holds, walking from the leaf to the root.
-/
def pick (st : Service) (s : State) (top : Instance) (trigger : Spec.Trigger) (extra : Extra)
    (l : String × Option String) : m (Except Fault (Option (String × Transition))) :=
  match s.machine? l.1 with
  | none => pure (.ok none)
  | some holder => firstLevel fs st s extra (levelsOf top holder trigger l.2)

/--
The transitions that the leaves select, without conflicts (SCXML selectTransitions and selectEventlessTransitions).
As in SCXML, a parallel state handles an event if any region selects a transition.
-/
def select (st : Service) (s : State) (top : Instance) (trigger : Spec.Trigger) (extra : Extra)
    (leaves : List (String × Option String)) :
    m (Except Fault (List (String × Transition))) := do
  let found ← leaves.foldlM (init := (.ok [] : Except Fault (List (String × Transition))))
    fun acc l => do
    match acc with
    | .error v => pure (.error v)
    | .ok enabled =>
      match ← pick fs st s top trigger extra l with
      | .error v => pure (.error v)
      | .ok none => pure (.ok enabled)
      | .ok (some c) => pure (.ok (if enabled.contains c then enabled else enabled ++ [c]))
  pure (found.map (s.removeConflicts top.chart))

end

end Tazuna.Service
