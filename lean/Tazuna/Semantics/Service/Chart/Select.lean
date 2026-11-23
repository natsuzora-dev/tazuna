import Tazuna.Semantics.Service.State

/-! This module selects transitions as SCXML selectTransitions and removeConflictingTransitions do. -/

namespace Tazuna.Semantics.Service

open Tazuna.Ir

variable {m : Type → Type}

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def choose (st : Service) (s : State) (i : Instance) (extra : Extra) :
    List Transition → m (Except Fault (Option Transition))
  | [] => pure (.ok none)
  | t :: rest => do
    match ← firstFalse (fs.guard (s.scopeOf i t.source) s.records t · extra) t.guards with
    | .error e => pure (.error (issueViolation (st.ref i.chart.name) e))
    | .ok none => pure (.ok (some t))
    | .ok (some c) =>
      MonadNote.note (.reached (.guardFalse (st.ref i.chart.name) t.ref c))
      choose st s i extra rest

def firstLevel (st : Service) (s : State) (extra : Extra) : List (Instance × List Transition) →
    m (Except Fault (Option (InstanceId × Transition)))
  | [] => pure (.ok none)
  | (i, ts) :: rest => do
    match ← choose fs st s i extra ts with
    | .error v => pure (.error v)
    | .ok (some t) => pure (.ok (some (i.id, t)))
    | .ok none => firstLevel st s extra rest

/-- The copies of a map state that an event reaches by the key fields of its payload, as in BPMN correlation. -/
inductive CopyTarget where
  /-- The payload lacks one of the key fields, so it reaches every copy. -/
  | everyCopy
  /-- The key fields fail the key schema, so it reaches no copy. -/
  | noCopy
  /-- The copy whose item key is `key`: the key fields as parse writes them, as `items` writes a copy's key. -/
  | copy (key : Value)

/-- The copies of the map state `map` of `chart` that an event with `payload` reaches. -/
def copyKey (st : Service) (chart : Chart) (map : String) (payload : Value) : m (Except Issue CopyTarget) := do
  let state ← expectFound s!"map state {map} of {chart.name}" ((chart.state? map).bind (·.spec.type.map?))
  match (Ir.schemaProperties state.key).mapM fun f => (payload.field? f).map (f, ·) with
  | none => pure (.ok .everyCopy)
  | some fields =>
    let schema := .mapKey (st.ref chart.name) map
    pure ((← fs.parseSorted st schema (.obj fields)).map fun
      | none => .noCopy
      | some key => .copy key)

/-- Whether an event with `payload` reaches copy `c`. -/
def reaches (st : Service) (c : Instance) (payload : Value) : m (Except Fault Bool) := do
  match c.id.map? with
  | none => pure (.ok true)
  | some map =>
    match ← copyKey fs st c.chart map payload with
    | .error e => pure (.error (issueViolation (st.ref c.chart.name) e))
    | .ok .everyCopy => pure (.ok true)
    | .ok .noCopy => pure (.ok false)
    | .ok (.copy k) => pure (.ok (c.id.key? == some k))

def reachedCopies (st : Service) (s : State) (top : Instance) (payload : Value) :
    m (Except Fault (List InstanceId)) :=
  top.copyIds.foldlM (init := .ok []) fun acc c => do
    match acc, s.machine? c with
    | .ok found, some ci =>
      match ← reaches fs st ci payload with
      | .error v => pure (.error v)
      | .ok reached => pure (.ok (if reached then found ++ [c] else found))
    | acc, _ => pure acc

/-- The states that transition `c` exits, by resource, including the states of copies of exited map states. -/
def State.exitKeys (s : State) (c : InstanceId × Transition) : List (InstanceId × String) :=
  match s.machine? c.1 with
  | none => []
  | some i =>
    (i.chart.exitsOf i.active c.2).flatMap fun n =>
      (c.1, n) :: (i.copyKeysOf n).flatMap fun k =>
        let cr := InstanceId.copy i.id n k
        ((s.machine? cr).map fun ci => ci.active.map (cr, ·)).getD []

/--
The enabled transitions without conflicts (SCXML removeConflictingTransitions): of two transitions whose exit sets
overlap, the one from the inner state is kept, and if neither is inner, the earlier one.
-/
def State.removeConflicts (s : State) (c : Chart) (enabled : List (InstanceId × Transition)) : List (InstanceId × Transition) :=
  let tree := c.tree
  enabled.foldl (fun kept t₁ =>
    let exits := s.exitKeys t₁
    let overlapping := kept.filter fun t₂ => (s.exitKeys t₂).any (· ∈ exits)
    if overlapping.any fun t₂ => !tree.isInside t₁.2.source t₂.2.source then kept
    else kept.filter (· ∉ overlapping) ++ [t₁]) []

/-- The leaves of `top` in document order, where the atomic states of reached copies replace their map state. -/
def leavesOf (s : State) (top : Instance) (reached : List InstanceId) : List (InstanceId × Option String) :=
  let topLeaves := top.chart.tree.leaves top.active
  let copyLeaves := reached.filterMap fun h => (s.machine? h).map fun ci => (h, ci.chart.tree.leaves ci.active)
  let atomic := fun (h, n) =>
    if h == top.id then n ∈ topLeaves && !(top.copyKeysOf n).any (InstanceId.copy top.id n · ∈ reached)
    else (copyLeaves.lookup h).any (n ∈ ·)
  let found := top.documentOrder.filter atomic
  if found.isEmpty then [(top.id, none)] else found.map fun (h, n) => (h, some n)

def eventLeaves (st : Service) (s : State) (top : Instance) (payload : Value) :
    m (Except Fault (List (InstanceId × Option String))) := do
  pure ((← reachedCopies fs st s top payload).map (leavesOf s top))

/--
The levels from the leaf to the root, each with its transitions on `trigger`. For a copy's leaf, the owner `top` chooses
at the levels of the map state and its ancestors.
-/
def levelsOf (top holder : Instance) (trigger : Ir.Trigger) (leaf : Option String) : List (Instance × List Transition) :=
  let path := match leaf with
    | none => []
    | some n => top.chart.tree.pathOf n
  (path.zipIdx.reverse.map fun (n, k) => (if k < holder.depth then top else holder, top.chart.transitionsAt (some n) trigger)) ++
  [(top, top.chart.transitionsAt none trigger)]

/--
The first transition on `trigger` (`.on key` or `.always`) whose guard holds, walking from the leaf to the root.
-/
def pick (st : Service) (s : State) (top : Instance) (trigger : Ir.Trigger) (extra : Extra)
    (l : InstanceId × Option String) : m (Except Fault (Option (InstanceId × Transition))) :=
  match s.machine? l.1 with
  | none => pure (.ok none)
  | some holder => firstLevel fs st s extra (levelsOf top holder trigger l.2)

/--
The transitions that the leaves select, without conflicts (SCXML selectTransitions and selectEventlessTransitions).
As in SCXML, a parallel state handles an event if any region selects a transition.
-/
def select (st : Service) (s : State) (top : Instance) (trigger : Ir.Trigger) (extra : Extra)
    (leaves : List (InstanceId × Option String)) :
    m (Except Fault (List (InstanceId × Transition))) := do
  let found ← leaves.foldlM (init := (.ok [] : Except Fault (List (InstanceId × Transition))))
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

end Tazuna.Semantics.Service
