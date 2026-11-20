import Tazuna.Data.List
import Tazuna.Spec.Structure

namespace Tazuna.Service

open Tazuna.Data Tazuna.Spec

/--
A transition of a chart. `source` is the declaring state, or `none` for the machine's own `on`. `source`, `trigger`,
and `index` locate the guard and assign that Functions evaluates.
-/
structure Transition where
  source : Option String
  trigger : Trigger
  index : Nat
  target : Option String
  /-- The guard's conditions, in order. A transition without any holds without asking Functions. -/
  guards : List String
  reenter : Bool
deriving DecidableEq, Repr, Inhabited

derive_wire Transition

def Transition.ref (t : Transition) : TransitionRef := { state := t.source, trigger := t.trigger, index := t.index }

/--
An activity of a state and the definition that it names. calls and sends send a request on each entry, opens opens a
child screen, and shows is a query subscribed while the screen is open.
-/
inductive Activity where
  | calls (key : String) (target : Ref)
  | sends (key : String) (target : Ref)
  | shows (key : String) (target : Ref)
  /-- `modal` is whether the opened screen blocks operations on other screens while it is open. -/
  | opens (key : String) (target : Ref) (modal : Bool)
deriving DecidableEq, Repr, Inhabited

derive_wire Tazuna.Service.Activity tag "keyword"

def Activity.key : Activity → String
  | .calls key _ | .sends key _ | .shows key _ | .opens key _ _ => key

def Activity.ref : Activity → Ref
  | .calls _ r | .sends _ r | .shows _ r | .opens _ r _ => r

/--
Whether the activity is an own-service command of `service`, which the internal queue processes without trace lines;
requests to other services write a request line and await an answer.
-/
def Activity.isOwn (service : String) : Activity → Bool
  | .sends _ r => r.service == service
  | _ => false

/-- Whether the activity opens a screen that blocks operations on other screens while it is open. -/
def Activity.isModal : Activity → Bool
  | .opens _ _ modal => modal
  | _ => false

def Activity.isShows : Activity → Bool
  | .shows .. => true
  | _ => false

/-- The trigger of the transitions that take an answer to a calls or sends, rejected or not. -/
def Activity.answerTrigger? (rejected : Bool) : Activity → Option Trigger
  | .calls key _ => some (.calls key (if rejected then .onRejected else .onFulfilled))
  | .sends key _ => some (.sends key (if rejected then .onRejected else .onAccepted))
  | .shows .. | .opens .. => none

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
  /-- Whether the state has parameters (`held`), which the edge that enters it fills. -/
  hasParameters : Bool := false
  deadlines : List Spec.Deadline := []
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
  /-- The key of each `receives` and the event that it receives. -/
  receives : List (String × Spec.Ref)
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

def transitionsAt (source : Option String) (trigger : Spec.Trigger) : List Transition :=
  match source with
  | none => c.on.filter (·.trigger == trigger)
  | some n => (((c.state? n).map (·.transitions)).getD []).filter (·.trigger == trigger)

theorem find?_shape (n : String) : c.tree.state? n = (c.state? n).map (·.shape) := by
  simp only [Tree.state?, tree, state?, List.find?_map]
  rfl

end Chart

def Transition.ofSpec (t : Spec.Transition) : Transition :=
  { source := t.source, trigger := t.trigger, index := t.index, target := t.target, guards := t.guards,
    reenter := t.reenters }

theorem Transition.targets_ofSpec (ts : List Spec.Transition) :
    (ts.map Transition.ofSpec).filterMap (·.target) = ts.filterMap (·.target) := by
  simp only [List.filterMap_map]
  rfl

/-- The executable form of an activity. -/
def Activity.ofSpec : Spec.Activity → Activity
  | .calls key r _ => .calls key r
  | .sends key r _ => .sends key r
  | .shows key r => .shows key r
  | .opens key r modal => .opens key r modal

def ChartState.ofSpec (st : Spec.State) : ChartState :=
  { name := st.name, path := st.path, parent := st.parent, kind := st.kind, initial := st.initial,
    children := st.children, activities := st.activities.map Activity.ofSpec,
    transitions := st.transitions.map Transition.ofSpec, offers := st.offers, hasParameters := st.hasParameters,
    deadlines := st.deadlines }

/-- The executable form of a chart. -/
def Chart.ofSpec (c : Spec.Chart) (name : String) (order : Nat) (screen opened : Bool) : Chart :=
  { name, order, initial := c.initial, on := c.on.map Transition.ofSpec, states := c.states.map ChartState.ofSpec,
    shaped := by
      have h : (c.states.map ChartState.ofSpec).map (·.shape) = c.states.map (·.shape) := by
        simp only [List.map_map]
        congr 1
        funext st
        simp only [Function.comp, ChartState.shape, Spec.State.shape, ChartState.ofSpec, Transition.targets_ofSpec]
      rw [h, Transition.targets_ofSpec]
      exact c.shaped,
    receives := c.receives, screen, opened, offers := c.offers,
    controls := c.controls.map fun (n, payload) =>
      { name := n, hasPayload := payload.any fun schema => !(schemaProperties schema).isEmpty } }

end Tazuna.Service
