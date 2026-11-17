import Tazuna.Data.List
import Tazuna.Spec.Structure

namespace Tazuna.Service

open Tazuna.Data Tazuna.Spec

/--
A transition of a chart. `source` is the declaring state, or `none` for the machine's own `on`. `source`, `keys`, and
`index` locate the guard and assign that Functions evaluates.
-/
structure Transition where
  source : Option String
  keys : List String
  index : Nat
  target : Option String
  /-- Whether the transition has a guard. An unguarded transition holds without asking Functions. -/
  guarded : Bool
  reenter : Bool
deriving DecidableEq, Repr, Inhabited

def Transition.ref (t : Transition) : TransitionRef := { state := t.source, keys := t.keys, index := t.index }

/--
An activity of a state. `target` is the trace name, as seen from the service, of the receiving definition (the opened
screen for opens), and `service` and `name` identify that definition. calls and sends send a request on each entry,
opens opens a child screen, and shows is a query subscribed while the screen is open. `own` is whether the activity is
an own-service command, which the internal queue processes without trace lines; requests to other services write a
request line and await an answer.
-/
structure Activity where
  keyword : String
  key : String
  target : String
  service : String
  name : String
  own : Bool
  /-- Whether the opened screen blocks operations on other screens while it is open. -/
  modal : Bool := false
deriving DecidableEq, Repr, Inhabited

def Activity.ref (a : Activity) : Ref := { service := a.service, name := a.name }

/-- A control of a screen. `hasPayload` is whether its payload schema has fields. -/
structure Control where
  name : String
  hasPayload : Bool
deriving DecidableEq, Repr, Inhabited

structure ChartState where
  name : String
  /-- The names from the root's child down to the state. -/
  path : List String
  parent : Option String
  kind : StateKind
  initial : Option String
  children : List String
  /-- The activities in the order calls, sends, shows, opens. -/
  activities : List Activity
  transitions : List Transition
  offers : List (String × Spec.Offer) := []
deriving Repr, Inhabited

def ChartState.shape (st : ChartState) : Shape :=
  { name := st.name, path := st.path, parent := st.parent, initial := st.initial, children := st.children, kind := st.kind,
    targets := st.transitions.filterMap (·.target) }

structure Chart where
  name : String
  /-- The rank among the spec's definitions; own-service commands are processed in sender-definition order. -/
  order : Nat
  initial : String
  on : List Transition
  /-- The states in document order. -/
  states : List ChartState
  shaped : chartTree (states.map (·.shape)) initial (on.filterMap (·.target)) = true := by decide
  /-- The key of each `receives` and the trace name of the event that it receives. -/
  receives : List (String × String)
  screen : Bool := false
  /-- Whether another screen's opens opens the chart. -/
  opened : Bool := false
  offers : List (String × Spec.Offer) := []
  controls : List Control := []
deriving Repr

instance : Inhabited Chart :=
  ⟨{ name := "", order := 0, initial := "s", on := [], receives := [],
     states := [{ name := "s", path := ["s"], parent := none, kind := .atomic, initial := none, children := [],
                  activities := [], transitions := [] }] }⟩

namespace Chart

variable (c : Chart)

def state? (n : String) : Option ChartState := c.states.find? (·.name == n)

def tree : Tree := { states := c.states.map (·.shape), shaped := stateTree_of_chartTree c.shaped }

def transitionsAt (source : Option String) (keys : List String) : List Transition :=
  match source with
  | none => c.on.filter (·.keys == keys)
  | some n => (((c.state? n).map (·.transitions)).getD []).filter (·.keys == keys)

theorem find?_shape (n : String) : c.tree.state? n = (c.state? n).map (·.shape) := by
  simp only [Tree.state?, tree, state?, List.find?_map]
  rfl

end Chart

end Tazuna.Service

namespace Tazuna.Spec

open Tazuna.Data Tazuna.Service

def Transition.toExec (t : Transition) : Service.Transition :=
  { source := t.source, keys := t.keys, index := t.index, target := t.target, guarded := t.guarded,
    reenter := t.reenters }

theorem Transition.targets_toExec (ts : List Transition) :
    (ts.map Transition.toExec).filterMap (·.target) = ts.filterMap (·.target) := by
  simp only [List.filterMap_map]
  rfl

/-- The executable form of an activity. Only a sends to the activity's own service is `own`. -/
def Activity.toExec (service : String) : Activity → Except String Service.Activity
  | .calls key (some r) =>
    pure { keyword := "calls", key, target := r.traceName service, service := r.service, name := r.name, own := false }
  | .sends key (some r) =>
    pure { keyword := "sends", key, target := r.traceName service, service := r.service, name := r.name,
           own := r.service == service }
  | .shows key (some r) =>
    pure { keyword := "shows", key, target := r.traceName service, service := r.service, name := r.name, own := false }
  | .opens key (some r) modal =>
    pure { keyword := "opens", key, target := r.traceName service, service := r.service, name := r.name, own := false,
           modal }
  | .calls key none | .sends key none | .shows key none | .opens key none _ =>
    throw s!"the activity {key}, which names no definition, is outside the Lean model"

/-- The executable form of a chart. -/
def Chart.toExec (c : Chart) (service name : String) (order : Nat) (screen opened : Bool) :
    Except String Service.Chart := do
  let toState (st : State) : Except String ChartState := do
    pure { name := st.name, path := st.path, parent := st.parent, kind := st.kind, initial := st.initial,
           children := st.children, activities := ← st.activities.mapM (Activity.toExec service),
           transitions := st.transitions.map Transition.toExec, offers := st.offers }
  let ⟨states, shaped⟩ ← match h : c.states.mapM toState with
    | .error e => (throw e : Except String _)
    | .ok states =>
      pure (⟨states, by
        rw [mapM_ok_map toState ChartState.shape State.shape (fun a b hb => by
          simp only [toState, bind, Except.bind, pure, Except.pure] at hb
          split at hb
          · cases hb
          · cases hb; simp only [ChartState.shape, State.shape, Transition.targets_toExec]) c.states states h,
          Transition.targets_toExec]
        exact c.shaped⟩ :
        { states : List ChartState // chartTree (states.map (·.shape)) c.initial ((c.on.map Transition.toExec).filterMap (·.target)) = true })
  let receives ← c.receives.mapM fun
    | (key, some r) => pure (key, r.traceName service)
    | (key, none) => throw s!"the chart {name} receives {key}, which is no event"
  pure { name, order, initial := c.initial, on := c.on.map Transition.toExec, states, shaped, receives, screen, opened,
         offers := c.offers,
         controls := c.controls.map fun (n, payload) =>
           { name := n, hasPayload := payload.any fun schema => !(schemaProperties schema).isEmpty } }

end Tazuna.Spec
