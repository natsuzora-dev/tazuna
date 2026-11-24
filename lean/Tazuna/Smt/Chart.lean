import Tazuna.Smt.State
import Tazuna.Ir.Reads
import Tazuna.Semantics.Service.Chart.Config

/-!
The configurations of a machine and its microsteps, for the induction of its invariants. The control is concrete: each
configuration that some transition can reach from the initial one is a list of active states, and each microstep is a
transition from a configuration with the states it exits and enters, as Service.microstep computes them. The data is
symbolic: the context fields that the invariants and guards depend on, the payload or answer that the transition
takes, the records and the time. These encodings carry no proof; prove replays each answer that it reports in the
semantics.
-/

namespace Tazuna.Smt

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Eval Tazuna.Semantics.Service

/-- What a transition takes besides the state: an event's payload, a command's or query's output, or a rejection. -/
inductive Taken where
  | none
  | payload (schema : Schema)
  | output (schema : Schema)
  | rejection

/-- A microstep from configuration `source`: `transition`, tried after `earlier` on its trigger, and what it takes. -/
structure Edge where
  source : Nat
  earlier : List Service.Transition
  transition : Service.Transition
  taken : Taken
  target : Nat
  /-- The states that the microstep exits, in exit order, and enters, in entry order. -/
  exits : List String
  entries : List String

/-- A machine's configurations, the first the initial one, which starting enters as `initialEntries`, and its edges. -/
structure ChartModel where
  chart : Service.Chart
  configs : Array (List String)
  edges : List Edge

/-- The configurations that a settled machine is never in: some active state has an always transition without a guard. -/
def ChartModel.transient (m : ChartModel) : List Nat :=
  ((List.range m.configs.size).filter fun k => m.edges.any fun e =>
    e.source == k && e.transition.trigger == .always && e.transition.guards.isEmpty && e.target != k)

/-- Why the chart has no model, or none. -/
def unsupported (c : Service.Chart) : Option String :=
  if c.screen then some "a screen"
  else if c.states.any (·.spec.kind != .plain) then some "a parallel, final, history or map state"
  else if c.states.any (·.spec.hasParameters) then some "a state with parameters (held)"
  else none

/-- The configuration after `t` from `active`, and the states it exits and enters, as Service.microstep finds them. -/
def chartStep (c : Service.Chart) (active : List String) (t : Service.Transition) : List String × List String × List String :=
  match t.target with
  | none => (active, [], [])
  | some target =>
    let exits := c.exitsOf active t
    let rest := active.filter (· ∉ exits)
    let entries := c.tree.entrySet rest 0 target
    (c.tree.entryOrder (rest ++ entries), exits, entries)

/-- The states that starting enters, in entry order, which are the initial configuration. -/
def initialEntries (c : Service.Chart) : List String := c.tree.entrySet [] 0 c.initial

/--
The transitions that the semantics tries on `trigger` from `active`, in order: those of the leaf, then of each ancestor,
then the chart's own (Select.levelsOf), for an event or an always; those of one state for a deadline or an answer.
-/
def candidates (c : Service.Chart) (active : List String) : List (Ir.Trigger × Taken × List Service.Transition) :=
  let levels (trigger : Ir.Trigger) : List Service.Transition :=
    let path := match (c.tree.leaves active).head? with
      | some leaf => c.tree.pathOf leaf
      | none => []
    path.reverse.flatMap (fun n => c.transitionsAt (some n) trigger) ++ c.transitionsAt none trigger
  let events := c.receives.map fun (key, event) => (Ir.Trigger.on key, Taken.payload (.payload event), levels (.on key))
  let always := [(Ir.Trigger.always, Taken.none, levels .always)]
  let own := active.flatMap fun n => match c.state? n with
    | none => []
    | some cs =>
      let deadlines := cs.spec.deadlines.map fun d =>
        (Ir.Trigger.after d.name, Taken.none, c.transitionsAt (some n) (.after d.name))
      let answers := cs.activities.flatMap fun a => match a with
        | .sends key target =>
          [(.sends key .onAccepted, .output (.output target)), (.sends key .onRejected, .rejection)]
        | .calls key target =>
          [(.calls key .onFulfilled, .output (.output target)), (.calls key .onRejected, .rejection)]
        | _ => []
      deadlines ++ answers.map fun (trigger, taken) => (trigger, taken, c.transitionsAt (some n) trigger)
  events ++ always ++ own

/-- The model of `c`: its configurations from the initial one and its edges, or why it has none. -/
def ChartModel.of (c : Service.Chart) : Except String ChartModel := do
  if let some why := unsupported c then throw s!"prove does not encode {why} yet"
  let initial := c.tree.entryOrder (initialEntries c)
  let mut configs : Array (List String) := #[initial]
  let mut edges : List Edge := []
  let mut next := 0
  while next < configs.size do
    let active := configs[next]!
    for (_, taken, ts) in candidates c active do
      for (t, k) in ts.zipIdx do
        let (post, exits, entries) := chartStep c active t
        let target ← match configs.findIdx? (· == post) with
          | some i => pure i
          | none => do configs := configs.push post; pure (configs.size - 1)
        edges := edges ++ [{ source := next, earlier := ts.take k, transition := t, taken, target, exits, entries }]
    next := next + 1
  pure { chart := c, configs, edges }

/-- Whether each state of `c` is in `active`, as the `active` argument holds it. -/
def activeVal (c : Service.Chart) (active : List String) : SVal :=
  .obj (c.states.map fun s => (s.spec.name, .scalar (.lit (.val (.bool (s.spec.name ∈ active))))))

/-- The symbolic state of a machine: its encoded context fields and its active states. -/
structure SMachine where
  context : List (String × Term)
  active : List String

/-- The arguments of a machine's expression, with what its transition takes. -/
def SMachine.env (m : SMachine) (c : Service.Chart) (records : SRecords) (now : Term) (taken : Option (Arg × SVal)) : SEnv :=
  { records,
    args := fun a => match a with
      | .context => some (.json (SJson.ofTerms m.context))
      | .active => some (activeVal c m.active)
      | .input => some (.json [])
      | .shown | .held => some (.obj [])
      | .now => some (.scalar (.mkInt now))
      | _ => taken.bind fun (b, v) => if a == b then some v else none }

def SVal.isScalar : SVal → Bool
  | .scalar _ => true
  | .ite _ a b => a.isScalar && b.isScalar
  | _ => false

/-- The functions of a site of chart `c`. -/
def siteOf (svc : Service) (p : Program) (c : Service.Chart) (s : Site) : Option (List Condition) :=
  (p.chart.find? fun f => f.chart == svc.ref c.name && f.site == s).map (·.functions)

/-- The assign sites of chart `c`. -/
def assignSites (svc : Service) (p : Program) (c : Service.Chart) : List (List Condition) :=
  p.chart.filterMap fun f =>
    if f.chart != svc.ref c.name then none else match f.site with
      | .transitionAssign _ | .entryAssign _ | .exitAssign _ => some f.functions
      | _ => none

/--
The context fields that the invariants and guards depend on: those they read, and those that an assign of such a field
reads. An assign of any other field changes nothing they evaluate, so the encoding leaves those fields out.
-/
def relevantContext (svc : Service) (p : Program) (c : Service.Chart) (fields : List String) : List String := Id.run do
  let reads (e : Expr) : List String := (argReads .context e).getD fields
  let roots := p.chart.filter (fun f => f.chart == svc.ref c.name && match f.site with
    | .invariants | .guards _ => true
    | _ => false) |>.flatMap fun f => f.functions.flatMap (reads ·.body)
  let assigns := (assignSites svc p c).flatten
  let mut relevant := fields.filter (· ∈ roots)
  for _ in [0:fields.length + 1] do
    let more := assigns.filter (·.name ∈ relevant) |>.flatMap (reads ·.body)
    relevant := fields.filter fun f => f ∈ relevant || f ∈ more
  return relevant

/-- The terms that hold when a transition's guards all hold, and when one of them throws before one fails (choose). -/
def guardTerms (env : SEnv) (conditions : List Condition) (guards : List String) : Except String (Term × Term) := do
  let mut ok := tt
  let mut halted := ff
  for g in guards do
    let some c := conditions.find? (·.name == g) | throw s!"no IR of the guard {g}"
    let (v, e) ← seval env [] c.body
    halted := .or halted (.and ok e)
    ok := conj [ok, .not e, v.truthy]
  return (ok, halted)

/--
The machine after the assign `fields` runs: each relevant field that it writes takes its value, all read from the
context before it, and the term that holds when one of those throws.
-/
def SMachine.assign (m : SMachine) (env : SEnv) (fields : List Condition) : Except String (SMachine × Term) := do
  let mut written := []
  let mut err := ff
  for f in fields do
    if (m.context.lookup f.name).isNone then continue
    let (v, e) ← seval env [] f.body
    if !v.isScalar then throw s!"an assign of {f.name} that may be no scalar"
    written := written ++ [(f.name, v.scalarOf.1)]
    err := .or err e
  pure ({ m with context := m.context.map fun (n, t) => (n, (written.lookup n).getD t) }, err)

/--
A microstep's symbolic result: the machine after it, the term that holds when it halts, and the fit of that term, which
reads the context's schema.
-/
structure Moved where
  machine : SMachine
  halted : Term
  fit : Fit

/--
The machine after `exits`, the assign of `transition` and `entries`, in the order of Service.microstep: each exit's
assign before the state leaves, and each entry's assign after the state is active. An assign halts when it throws, or
when the context it writes fails its schema (contextMismatch); the encoding checks the fields that the machine holds.
-/
def SMachine.move (m : SMachine) (svc : Service) (p : Program) (c : Service.Chart) (records : SRecords) (now : Term)
    (taken : Option (Arg × SVal)) (transition : Option Service.Transition) (exits entries : List String) : Except String Moved := do
  let mut m := m
  let mut halted := ff
  let mut fit := Fit.exact
  let props := propertiesWith ((svc.schemaOf (.context (svc.ref c.name))).getD (.obj []))
  let site (s : Site) : List Condition := (siteOf svc p c s).getD []
  let assigns := exits.map (fun n => (some n, false, site (.exitAssign n))) ++
    (transition.map fun t => (none, false, site (.transitionAssign t.ref))).toList ++
    entries.map fun n => (some n, true, site (.entryAssign n))
  for (state, entering, fields) in assigns do
    if entering then m := { m with active := m.active ++ state.toList }
    let (m', e) ← m.assign (m.env c records now taken) fields
    m := if entering then m' else { m' with active := m'.active.filter (some · != state) }
    let fits := if fields.isEmpty then [] else props.filterMap fun pr => (m.context.lookup pr.1).map (fieldHolds · pr)
    halted := disj [halted, e, .not (conj (fits.map (·.term)))]
    fit := Fit.all ([fit] ++ fits.map (·.fit))
  -- A halt that the terms miss, or one that they add, decides a microstep wrongly either way.
  pure { machine := { m with active := c.tree.entryOrder m.active }, halted,
         fit := if fit == .exact then .exact else .loose }

/-- The rejection kinds as the `kind` of a rejection holds them. -/
def rejectionKinds : List String :=
  ["invalid-input", "reused-id", "not-found", "requires", "already-exists", "unavailable"]

/--
What a transition takes, as the argument that holds it: the fields of a payload or output that `reads` read, each a
variable named after `pre`, or a rejection's kind; and their facts. A field left out makes the facts inexact, since
replay then takes the value without it.
-/
def takenOf (svc : Service) (pre : String) (reads : List Expr) : Taken → Except String (Option (Arg × SVal) × Facts)
  | .none => pure (none, Facts.none)
  | .rejection =>
    let kind := valVar s!"{pre}.kind"
    pure (some (.rejection, .json (SJson.ofTerms [("kind", kind)])),
      { vars := [(s!"{pre}.kind", .val)], asserts := [disj (rejectionKinds.map fun k => .eq kind (.mkStr (strLit k)))],
        fit := .exact })
  | .payload schema => fields .payload schema
  | .output schema => if (svc.schemaOf schema).isNone then pure (none, Facts.none) else fields .output schema
where
  fields (arg : Arg) (schema : Schema) : Except String (Option (Arg × SVal) × Facts) := do
    let props := propertiesWith ((svc.schemaOf schema).getD (.obj []))
    let read : Option (List String) := reads.foldl (fun acc e => do pure ((← acc) ++ (← argReads arg e))) (some [])
    if read.isNone && ((svc.schemaOf schema).bind (·.field? "properties")).isNone then
      throw s!"a read of the whole {repr arg} that is no object"
    let kept := props.filter fun (f, _, _) => read.all (f ∈ ·)
    let terms := kept.map fun pr => (pr.1, propertyVar s!"{pre}.{pr.1}" pr)
    let holds := kept.map fun pr => fieldHolds (((terms.lookup pr.1).map (·.1)).getD undefT) pr
    pure (some (arg, .json (SJson.ofTerms (terms.map fun (f, t, _) => (f, t)))),
      { vars := terms.flatMap (·.2.2), asserts := holds.map (·.term),
        fit := (Fit.all (holds.map (·.fit))).join (.of (kept.length == props.length) true) })

/-- The term that holds when the invariant `c` of the machine fails, or throws, in `env`. -/
def chartFails (env : SEnv) (c : Condition) : Except String Term := do
  let (v, e) ← seval env [] c.body
  pure (Term.or e (.not v.truthy))

end Tazuna.Smt
