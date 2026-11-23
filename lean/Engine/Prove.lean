import Engine.Run
import Tazuna.Smt.Script
import Tazuna.Smt.State
import Tazuna.Smt.Chart
import Tazuna.Smt.Pair

/-!
prove: the base case and the inductive step of each invariant of each spec service, within the service's bounds, and
from any state where they hold, that every ensures of a command or query holds and that no command leaves a ref
dangling. The engine answers in two requests, since TS runs Z3: `proveQueries` gives the SMT-LIB scripts, and `prove`
reads Z3's answers to them, replays each counterexample in the semantics, and gives one result per property.
-/

namespace Tazuna.Engine

open Tazuna.Data Tazuna.Service Tazuna.Smt

/--
What prove checks: an invariant of an entity's records, a machine or screen, or the service (which names itself); an
ensures of a command or query; that a ref field of an entity never names a missing record; or that the order of two
steps that can be pending together, such as two automations that react to one event, changes no outcome; or that a
response of an entity is met in time.
-/
inductive Property where
  | invariant (definition : Spec.Ref) (name : String)
  | response (definition : Spec.Ref) (name : String)
  | ensures (definition : Spec.Ref) (name : String)
  | danglingRef (definition : Spec.Ref) (field : String)
  | stepOrder (definition : Spec.Ref) (other : Spec.Ref)
deriving BEq, Repr, Inhabited

derive_wire Property tag "kind"

def Property.definition : Property → Spec.Ref
  | .invariant d _ | .response d _ | .ensures d _ | .danglingRef d _ | .stepOrder d _ => d

/--
A state within the bounds where every invariant holds, and a command after which the property fails, or a query whose
answer fails its ensures.
-/
structure Counterexample where
  /-- The records, by entity: a keyed entity's as a list, a single entity's as its record. -/
  given : Value
  /-- The time of the state, which invariants read as `now`. -/
  clock : Int
  /-- The command and its input and time, none for the initial state. -/
  command : Option String
  /-- The query and its input, which it answers at the time of the state. -/
  query : Option String := none
  input : Option Value
  now : Option Int
  /-- The machine's active states and context before the transition, none for starting it. -/
  machine : Option Value := none
  /-- The machine's transition and what it takes, such as an event's payload, none for starting it. -/
  transition : Option Value := none
  taken : Option Value := none
  /-- The violations that the semantics reports on replaying the case. -/
  violations : List Violation
deriving Inhabited

derive_wire Counterexample serialize_only skip_serializing_none

inductive Verdict where
  | proved
  | counterexample (case : Counterexample)
  | undecided (reason : String)

derive_wire Verdict tag "kind" serialize_only

/-- What prove found of one property, within the bound of creating at most `creates` records of each keyed entity. -/
structure ProveResult where
  service : String
  property : Property
  creates : List (String × Nat)
  verdict : Verdict
  /-- What the verdict assumes of the runs beyond the spec, which a response's counterexample states. -/
  assumes : Option String := none

derive_wire ProveResult serialize_only skip_serializing_none

/-- The units of Z3's resource counter that each query may use: several seconds on a laptop, over 200 times the most that a todo query uses. -/
def proveRlimit : Nat := 20000000

/-- Where an invariant is checked: on each record of an entity, on a single entity's record, or on all records. -/
inductive Holder where
  | keyed (entity : String)
  | single (entity : String)
  | service

structure Checked where
  ref : Property
  holder : Holder
  condition : Ir.Condition

/-- The invariants of the entities and the service `st`. -/
def invariantsOf (st : Service) (p : Ir.Program) : List Checked :=
  let entity := st.entities.flatMap fun e =>
    (Smt.invariantsOf st p e).map fun c =>
      { ref := .invariant (st.ref e) c.name,
        holder := if st.singles.contains e then .single e else .keyed e, condition := c }
  let service := (serviceInvariantsOf st p).map fun c =>
    { ref := .invariant (st.ref st.service) c.name, holder := .service, condition := c }
  entity ++ service

/--
The responses of the entities of `st`, each checked as the invariant that its `when` implies its `expect` at every
visible state, which prove proves of a response instead of its observer (responseVerdict).
-/
def responsesOf (st : Service) (p : Ir.Program) : List Checked :=
  st.entities.flatMap fun e =>
    let expects := ((p.responseExpect.find? (·.definition == st.ref e)).map (·.conditions)).getD []
    let whens := ((p.responseWhen.find? (·.definition == st.ref e)).map (·.conditions)).getD []
    whens.map fun w =>
      let expect := ((expects.find? (·.name == w.name)).map (·.body)).getD (.lit (.bool true))
      { ref := .response (st.ref e) w.name, holder := if st.singles.contains e then .single e else .keyed e,
        condition := { name := w.name, body := .or (.not w.body) expect } }

/--
The induction of a machine's or screen's invariants: its model, the context fields that the encoding holds, and the
context it starts with, or why it has none.
-/
structure ChartCase where
  chart : Chart
  invariants : List Ir.Condition
  model : Except String ChartModel
  relevant : List String
  /-- The schema of each relevant context field and whether the context must hold it, as propertiesWith gives them. -/
  props : List (String × Value × Bool)
  /-- Whether the encoding leaves out some context fields, which replay then takes as they start. -/
  sliced : Bool
  initial : Except String Value

def chartCaseOf (st : Service) (fs : Functions IO) (c : Chart) : IO (Option ChartCase) := do
  let p := st.structure.program
  let invariants := (siteOf st p c .invariants).getD []
  if invariants.isEmpty then return none
  let all := propertiesWith ((st.schemaOf (.context (st.ref c.name))).getD (.obj []))
  let fields := all.map (·.1)
  let relevant := relevantContext st p c fields
  let initial := (← initialContextOf fs st c.name (.obj [])).mapError fun f => s!"the initial context fails: {repr f}"
  return some { chart := c, invariants, model := ChartModel.of c, relevant,
                props := all.filter (·.1 ∈ relevant), sliced := relevant.length < fields.length, initial }

/-- The conditions of `definition` in a Program list. -/
def conditionsOf (list : List Ir.Conditions) (definition : Spec.Ref) : List Ir.Condition :=
  ((list.find? (·.definition == definition)).map (·.conditions)).getD []

/-- The ref fields of `st` whose target is one of its keyed entities: the entity, the field and the target. -/
def ownRefs (st : Service) : List (String × String × String) :=
  st.references.filter fun (_, _, target) => st.entities.contains target && !st.singles.contains target

/-- The term that holds when `c` fails, or throws, at the time `now` on some record of `r` that it is checked on. -/
def failsOn (r : SRecords) (now : Term) (c : Checked) : Except String Term := do
  let fails (env : SEnv) : Except String Term := do
    let (v, e) ← seval env [] c.condition.body
    pure (Term.or e (.not v.truthy))
  match c.holder with
  | .keyed e => do
    let terms ← (r.slotsOf e).mapM fun s => do pure (Term.and s.live (← fails (recordEnv s.fields now)))
    pure (disj terms)
  | .single e => fails (recordEnv ((r.singles.lookup e).getD []) now)
  | .service => fails (recordsEnv r now)

/-- The time of a state, `clock`, an instant as every time is (Time.inRange). -/
def clockFacts : Facts :=
  { vars := [("clock", .int)],
    asserts := [.le (intLit (-maxInstant)) (.var "clock" .int), .le (.var "clock" .int) (intLit maxInstant)] }

def clockT : Term := .var "clock" .int

def nowT : Term := .var "now" .int

/-- A time after the state's, which a response reads when time passes with no message. -/
def laterT : Term := .var "later" .int

/-- The time of a step, `now`, an instant no earlier than the state's time. -/
def nowFacts : Facts :=
  { vars := [("now", .int)], asserts := [.le (intLit (-maxInstant)) nowT, .le nowT (intLit maxInstant), .le clockT nowT] }

/--
The initial records: no record of a keyed entity, and each single entity's record of its schema defaults. A default that
no term holds, such as an array, is a variable, which makes the facts inexact.
-/
def initialOf (st : Service) : SRecords × Facts := Id.run do
  let mut facts : Facts := {}
  let mut singles := []
  for e in st.singles do
    let defaults := defaultsOf (entitySchema st e)
    let mut fields := []
    for f in Ir.fieldsOf st e do
      match defaults.field? f with
      | none => fields := fields ++ [(f, undefT)]
      | some v =>
        match litTerm v with
        | .ok l => fields := fields ++ [(f, l)]
        | .error _ =>
          fields := fields ++ [(f, valVar s!"init.{e}.{f}")]
          facts := facts ++ { vars := [(s!"init.{e}.{f}", .val)], exact := false }
    singles := singles ++ [(e, fields)]
  pure ({ keyed := (st.entities.filter (!st.singles.contains ·)).map (·, []), singles }, facts)

/-- One service's symbolic induction: its state, and the step of each command, or why the step has no encoding. -/
structure Induction where
  st : Service
  creates : List (String × Nat)
  pre : SRecords
  /-- The facts of `pre` and of its time `clock`. -/
  facts : Facts
  /-- That every encoded invariant holds of `pre`. -/
  holds : Term
  steps : List (String × Except String Step)
  /-- The answer of each query, or why it has no encoding. -/
  answers : List (String × Except String Answered)
  checked : List Checked
  /-- The responses, which the induction checks but, unlike `checked`, does not assume. -/
  responses : List Checked
  charts : List ChartCase
  /-- Each pair of steps that can be pending together, with its two orders, or why they have no encoding. -/
  pairs : List (Pair × Except String Orders)
  /-- Why the service has no induction, such as missing bounds. -/
  blocked : Option String

def inductionOf (j : Spec.Structure) (service : String) : IO Induction := do
  let st ← Service.ofStructure j service
  let p := j.program
  let checked := invariantsOf st p
  let fs := p.toFunctions st fun _ => pure ()
  let charts ← st.charts.filterMapM (chartCaseOf st fs)
  let keyed := st.entities.filter (!st.singles.contains ·)
  let bounds := (j.bounds.find? (·.service == service)).map (·.creates)
  let creates := bounds.getD []
  let pre := SRecords.named st creates "pre"
  let used := pre.keyed.map fun (e, slots) => (e, (List.range slots.length).map (usedVar "pre" e))
  let holds := conj (checked.filterMap fun c => (failsOn pre clockT c).toOption.map .not)
  let blocked := if bounds.isNone && !keyed.isEmpty then some "the service has no bounds()" else none
  pure { st, creates, pre, facts := pre.facts st "pre" ++ clockFacts, holds,
         steps := st.commands.map fun c => (c, stepOf st p pre clockT used c),
         answers := (st.queries.filter fun q => !(conditionsOf p.queryEnsures (st.ref q)).isEmpty).map fun q =>
           (q, answerOf st p pre clockT q),
         checked, responses := responsesOf st p, charts, blocked,
         pairs := (pairsOf st).map fun pair => (pair, ordersOf st p pre used nowT pair) }

/-- The property of a pair: that the order of its two steps changes no outcome. -/
def pairProperty (st : Service) (pair : Pair) : Property := .stepOrder (st.ref pair.first.name) (st.ref pair.second.name)

/--
A step of a machine's induction: starting it, or a microstep of one of its edges. A command changes no machine, and an
invariant reads only the machine's context and active states, so no command can fail one. The semantics checks the
invariants after the same steps (checkChart).
-/
inductive ChartStep where
  | start
  | edge (index : Nat)
deriving BEq

/-- A query of the induction: whether the initial records fail an invariant, a step can leave the encoding, a step can
fail a property, or a query's answer can fail one of its ensures. -/
inductive Asked where
  | base (property : Property)
  | gap (command : String)
  | fails (command : String) (property : Property)
  | answer (query : String) (property : Property)
  | chart (property : Property) (step : ChartStep)
  /-- Whether a step of a pair can leave the encoding, and whether the pair's two orders can differ. -/
  | pairGap (property : Property)
  | pairDiffers (property : Property)
  /-- Whether time passing alone, with no message, can fail a response's `when` implies `expect`. -/
  | tick (property : Property)

def Induction.query (x : Induction) (step : Step) (goal : Term) : Query :=
  { vars := x.facts.vars ++ step.facts.vars,
    asserts := x.facts.asserts ++ [x.holds] ++ step.facts.asserts ++ [step.accepted, .not step.beyond, goal] }

/-- The properties that a step of `command` can fail, each with the term that holds when the step fails it. -/
def Induction.stepGoals (x : Induction) (command : String) (step : Step) : List (Property × Except String Term) :=
  let p := x.st.structure.program
  (x.checked.map fun ch => (ch.ref, failsOn step.post step.now ch)) ++
    ((conditionsOf p.ensures (x.st.ref command)).map fun c =>
      (Property.ensures (x.st.ref command) c.name, step.ensuresFails c)) ++
    ((ownRefs x.st).map fun (e, field, target) =>
      (Property.danglingRef (x.st.ref e) field, .ok (step.post.dangling e field target)))

/--
That each encoded context field of `m` fits its schema. The semantics checks the context after each assign
(contextMismatch) and halts when it does not fit, so every context that a step starts from fits, and a step whose
context does not fit halts instead of failing an invariant.
-/
def ChartCase.fits (cc : ChartCase) (m : SMachine) : List Holds :=
  cc.props.filterMap fun pr => (m.context.lookup pr.1).map (fieldHolds · pr)

/-- The machine of `cc` in `active` before a step, each encoded context field a variable of its schema. -/
def ChartCase.pre (cc : ChartCase) (active : List String) : SMachine × Facts :=
  let m : SMachine := { context := cc.relevant.map fun f => (f, valVar s!"ctx.{f}"), active }
  let fits := cc.fits m
  (m, { vars := cc.relevant.map fun f => (s!"ctx.{f}", Ty.val), asserts := fits.map (·.term),
        exact := fits.all (·.exact), complete := fits.all (·.complete) })

/--
The expressions of the chart of `cc` that the encoding evaluates: its invariants, its guards, and its assigns of the
relevant context fields. Their reads of a payload or output decide which fields the encoding holds.
-/
def ChartCase.expressions (cc : ChartCase) (st : Service) : List Ir.Expr :=
  st.structure.program.chart.filter (·.chart == st.ref cc.chart.name) |>.flatMap fun f =>
    match f.site with
    | .invariants | .guards _ => f.functions.map (·.body)
    | .transitionAssign _ | .entryAssign _ | .exitAssign _ =>
      (f.functions.filter (·.name ∈ cc.relevant)).map (·.body)
    | _ => []

/-- That every invariant of the machine holds in `env`. -/
def chartHolds (env : SEnv) (invariants : List Ir.Condition) : Except String Term := do
  pure (conj (← invariants.mapM fun c => do pure (Term.not (← chartFails env c))))

/--
The queries of the induction of the invariant `k` of `cc`, each with whether its facts are exact and complete: starting
the machine with any records, and each edge from a state where every invariant holds.
-/
def Induction.chartQueries (x : Induction) (cc : ChartCase) (k : Ir.Condition) :
    Except String (List (ChartStep × Query × Bool × Bool)) := do
  let m ← cc.model
  let initial ← cc.initial
  let st := x.st
  let p := st.structure.program
  let c := cc.chart
  let startContext ← cc.relevant.mapM fun f => do
    pure (f, ← match initial.field? f with
      | some v => litTerm v
      | none => pure undefT)
  let started ← ({ context := startContext, active := [] } : SMachine).move st p c x.pre clockT none none [] (initialEntries c)
  let startFails ← chartFails (started.machine.env c x.pre clockT none) k
  let startFits := cc.fits started.machine
  let start : ChartStep × Query × Bool × Bool :=
    (.start, { vars := x.facts.vars,
               asserts := x.facts.asserts ++ [x.holds, .not started.halted] ++ startFits.map (·.term) ++ [startFails] },
     x.facts.exact && !cc.sliced && startFits.all (·.exact), x.facts.complete && startFits.all (·.complete))
  let guardsOf (t : Service.Transition) : List Ir.Condition := (siteOf st p c (.guards t.ref)).getD []
  let edges ← m.edges.zipIdx.mapM fun (e, i) => do
    let (pre, ctxFacts) := cc.pre (m.configs[e.source]!)
    let (taken, takenFacts) ← takenOf st "tk" (cc.expressions st) e.taken
    let env := pre.env c x.pre nowT taken
    let holdsPre ← chartHolds (pre.env c x.pre clockT none) cc.invariants
    let earlier ← e.earlier.mapM fun t => do
      let (ok, halted) ← guardTerms env (guardsOf t) t.guards
      pure (Term.and (.not ok) (.not halted))
    let (ok, halted) ← guardTerms env (guardsOf e.transition) e.transition.guards
    let moved ← pre.move st p c x.pre nowT taken (some e.transition) e.exits e.entries
    let fails ← chartFails (moved.machine.env c x.pre nowT none) k
    let postFits := cc.fits moved.machine
    let facts := x.facts ++ nowFacts ++ ctxFacts ++ takenFacts
    let q : Query :=
      { vars := facts.vars,
        asserts := facts.asserts ++ [x.holds, holdsPre] ++ earlier ++ [ok, .not halted, .not moved.halted] ++
          postFits.map (·.term) ++ [fails] }
    pure ((ChartStep.edge i, q, facts.exact && !cc.sliced && postFits.all (·.exact),
      facts.complete && postFits.all (·.complete)) : ChartStep × Query × Bool × Bool)
  pure ([start] ++ edges)

/--
The queries of an induction, in order: the base case of each encoded invariant, then each command's gap query and one
per property it can fail, then one per ensures of each query, then those of each machine's invariants.
-/
def Induction.queries (x : Induction) : List (Asked × Query) :=
  if x.blocked.isSome then [] else
  let (init, initFacts) := initialOf x.st
  let facts := clockFacts ++ initFacts
  let p := x.st.structure.program
  (x.checked.filterMap fun ch => (failsOn init clockT ch).toOption.map fun fails =>
    (Asked.base ch.ref, { vars := facts.vars, asserts := facts.asserts ++ [fails] })) ++
  (x.steps.flatMap fun (c, step) =>
    match step with
    | .error _ => []
    | .ok step =>
      (Asked.gap c, x.query step step.gap) ::
        (x.stepGoals c step).filterMap fun (prop, goal) => goal.toOption.map fun fails =>
          (.fails c prop, x.query step (.and (.not step.gap) fails))) ++
  (x.answers.flatMap fun (q, answered) =>
    match answered with
    | .error _ => []
    | .ok a => (conditionsOf p.queryEnsures (x.st.ref q)).filterMap fun c => (a.ensuresFails x.pre c).toOption.map
      fun fails => (.answer q (.ensures (x.st.ref q) c.name),
        { vars := x.facts.vars ++ a.facts.vars, asserts := x.facts.asserts ++ [x.holds] ++ a.facts.asserts ++ [a.answered, fails] })) ++
  (x.charts.flatMap fun cc => cc.invariants.flatMap fun k =>
    ((x.chartQueries cc k).toOption.getD []).map fun (step, q, _) =>
      (Asked.chart (.invariant (x.st.ref cc.chart.name) k.name) step, q)) ++
  (x.responses.flatMap fun r =>
    let held := (failsOn x.pre clockT r).toOption.map Term.not
    ((failsOn init clockT r).toOption.map fun fails =>
      (Asked.base r.ref, { vars := facts.vars, asserts := facts.asserts ++ [fails] })).toList ++
    (x.steps.filterMap fun (c, step) => do
      let step ← step.toOption
      let fails ← (failsOn step.post step.now r).toOption
      pure (.fails c r.ref, x.query step (.and ((held.getD ff)) (.and (.not step.gap) fails)))) ++
    ((failsOn x.pre laterT r).toOption.map fun fails =>
      (Asked.tick r.ref, { vars := x.facts.vars ++ [("later", .int)],
                           asserts := x.facts.asserts ++ [x.holds, held.getD ff, .le clockT laterT, fails] })).toList) ++
  x.pairs.flatMap fun (pair, orders) => match orders with
    | .error _ => []
    | .ok o =>
      let prop := pairProperty x.st pair
      let facts := x.facts ++ nowFacts ++ o.facts
      let ask (goal : List Term) : Query := { vars := facts.vars, asserts := facts.asserts ++ [x.holds, o.within] ++ goal }
      [(.pairGap prop, ask [o.gap]), (.pairDiffers prop, ask [.not o.gap, o.differ])]

/-- The own spec services of the structure, in order. -/
def specServices (j : Spec.Structure) : List String := (j.services.filter (!·.external)).map (·.name)

def proveQueriesOf (j : Spec.Structure) : IO (List String) := do
  let inductions ← (specServices j).mapM (inductionOf j)
  pure (inductions.flatMap fun x => x.queries.map fun (_, q) => q.script proveRlimit)

/-- The records of a state by entity, as the counterexample's Given shows them. -/
def givenOf (st : Service) (records : Records) : Value :=
  .obj (st.entities.map fun e =>
    let rows := records.filter (·.entity == e)
    if st.singles.contains e then (e, ((rows.head?).map (·.value)).getD .null)
    else (e, .arr (rows.map (·.value))))

/-- Whether `c` fails in `env`, as the semantics evaluates it. -/
def failsConcrete (env : Ir.Env) (c : Ir.Condition) : Bool :=
  match (Ir.firstFailing env [c]).run' with
  | (.ok none, _) => false
  | _ => true

/-- Whether `faults` report `c` failing, or throwing, on the record `key` of an entity. -/
def reports (st : Service) (c : Checked) (command : String) (fault : Fault) : Bool :=
  match c.holder, fault with
  | .keyed e, .failedEntityInvariant d _ _ cmd | .single e, .failedSingleInvariant d _ cmd =>
    d == st.ref e && cmd == st.ref command
  | .keyed e, .exception (some d) | .single e, .exception (some d) => d == st.ref e
  | .service, .failedServiceInvariant _ cmd => cmd == st.ref command
  | .service, .exception none => true
  | _, _ => false

/-- The records that the step writes, as the semantics writes them, or none when it rejects or halts before. -/
def writtenBy (st : Service) (fs : Functions IO) (records : Records) (now : Time) (name : String) (input : Value) :
    IO (Option (Records × List Fault)) := do
  match ← evaluate st fs records now name input with
  | .accepted written _ violations => pure (some (written, violations))
  | .halted violations =>
    -- The halt is a fault such as a throw in ensures; the records the step writes are those decide's events write.
    match ← fs.decide name input records now with
    | .ok decided => pure (some (applyAll st records (orderedGroups decided decided.flatten).flatten, violations))
    | .error _ => pure none
  | .rejected _ => pure none

/-- Whether `c` fails at the time `now` on some record of `records` that it is checked on, as the semantics evaluates it. -/
def failsIn (st : Service) (c : Checked) (records : Records) (now : Time) : Bool :=
  let env (args : List (Ir.Arg × Ir.Val)) : Ir.Env :=
    { fields := Ir.fieldsOf st, args := Ir.argsOf (args ++ [(.now, Ir.instant now)]), records }
  match c.holder with
  | .keyed e | .single e => records.any fun r => r.entity == e && failsConcrete (env [(.record, .json r.value)]) c.condition
  | .service => failsConcrete (env []) c.condition

/-- Whether a fault of an ensures of `definition` reports `name` failing, or a throw. -/
def failedEnsures (definition : Spec.Ref) (name : String) : Fault → Bool
  | .failedEnsures d c => d == definition && c == name
  | .exception (some d) => d == definition
  | _ => false

/-- Whether the semantics shows that `command`, which wrote `written` at `now` and reported `faults`, fails `prop`. -/
def Induction.failedAfter (x : Induction) (command : String) (now : Time) (written : Records) (faults : List Fault) :
    Property → Bool
  | .invariant d name => match x.checked.find? (·.ref == .invariant d name) with
    | some c => failsIn x.st c written now && faults.any (reports x.st c command)
    | none => false
  | .ensures d name => faults.any (failedEnsures d name)
  | .danglingRef d field => faults.any fun
    | .danglingRef d' _ f _ cmd | .danglingSingleRef d' f _ cmd => d' == d && f == field && cmd == x.st.ref command
    | _ => false
  | .stepOrder .. | .response .. => false

/-- The records of a model's state, or why the state is none that the induction assumes. -/
def Induction.stateOf (x : Induction) (M : Model) : Except String (Records × Value × Int) := do
  let records := (x.pre.conc M).filter fun r => x.st.entities.contains r.entity
  let clock := (M "clock").toInt
  if let some b := x.checked.find? (failsIn x.st · records clock) then
    throw s!"the case's state fails {repr b.ref}, which the induction assumes"
  let fits (r : Row) : Bool := match Data.parse (entitySchema x.st r.entity) r.value with
    | some (.ok (.ok _)) => true
    | _ => false
  if let some r := records.find? (!fits ·) then throw s!"the case's record of {r.entity} is outside its schema"
  pure (records, givenOf x.st records, clock)

/-- The result of the replay of a model of a fails query: the counterexample, or why the model is no case of it. -/
def replayStep (x : Induction) (fs : Functions IO) (M : Model) (command : String) (step : Step) (prop : Property) :
    IO (Except String Counterexample) := do
  let input := Value.obj (present M step.input)
  let now := (M "now").toInt
  match x.stateOf M with
  | .error why => return .error why
  | .ok (pre, given, clock) =>
  match ← writtenBy x.st fs pre now command input with
  | none => return .error "the semantics rejects the case's command"
  | some (written, faults) =>
    if !x.failedAfter command now written faults prop then
      return .error "the semantics keeps the property after the case's command"
    return .ok { given, clock, command := some command, input := some input, now := some now,
                 violations := faults.map (·.toViolation) }

/--
The response faults that the semantics reports when time passes the due of the obligation that `r` opens on `records`
at `now`, as the observer of a service with no automation and no chart sees it: nothing changes the records before then.
-/
def missedAfter (x : Induction) (fs : Functions IO) (records : Records) (now : Time) (r : Checked) : IO (List Fault) := do
  let s ← observeResponses x.st fs { service := x.st.service, records, now, started := true }
  let mine (o : Obligation) := x.st.ref o.entity == r.ref.definition && .response (x.st.ref o.entity) o.response == r.ref
  let some o := s.obligations.find? mine | return []
  pure ((s.passTime x.st (o.due + 1)).violations.filterMap fun
    | .fault f@(.missedResponse ..) => some f
    | _ => none)

/-- The replay of a model of a response's fails or tick query: the counterexample, or why the model is no case of it. -/
def replayResponse (x : Induction) (fs : Functions IO) (M : Model) (r : Checked) (command : Option (String × Step)) :
    IO (Except String Counterexample) := do
  match x.stateOf M with
  | .error why => return .error why
  | .ok (pre, given, clock) =>
  match command with
  | none =>
    let later := (M "later").toInt
    let missed ← missedAfter x fs pre later r
    if missed.isEmpty then return .error "the semantics opens no obligation as time passes"
    return .ok { given, clock, command := none, input := none, now := some later, violations := missed.map (·.toViolation) }
  | some (c, step) =>
    let input := Value.obj (present M step.input)
    let now := (M "now").toInt
    match ← writtenBy x.st fs pre now c input with
    | none => return .error "the semantics rejects the case's command"
    | some (written, faults) =>
      let missed ← missedAfter x fs written now r
      if missed.isEmpty then return .error "the semantics opens no obligation after the case's command"
      return .ok { given, clock, command := some c, input := some input, now := some now,
                   violations := (faults ++ missed).map (·.toViolation) }

/-- The progress that a response's verdict assumes of the runs, which the spec does not state. -/
def progressAssumption : String :=
  "enabled internal steps run, in-flight messages arrive unless a line loses them, and an external service answers " ++
    "only as its deadlines fire; no client sends anything"

/-- The result of the replay of a model of an answer query: the counterexample, or why the model is no case of it. -/
def replayAnswer (x : Induction) (fs : Functions IO) (M : Model) (query : String) (a : Answered) (name : String) :
    IO (Except String Counterexample) := do
  let input := Value.obj (present M a.input)
  match x.stateOf M with
  | .error why => return .error why
  | .ok (pre, given, clock) =>
  let failed := failedEnsures (x.st.ref query) name
  let case (faults : List Fault) : Counterexample :=
    { given, clock, command := none, query := some query, input := some input, now := none,
      violations := faults.map (·.toViolation) }
  match ← resolveChecked x.st fs { now := clock, service := x.st.service, records := pre } query input with
  | .answered _ faults => return if faults.any failed then .ok (case faults) else .error "the semantics keeps the ensures"
  | .halted fault => return if failed fault then .ok (case [fault]) else .error "the semantics halts the case's query"

/--
The replay of a model of a base query: the initial records, the single entities' records of their schema defaults, at the
model's time, or why `c` holds of them.
-/
def replayBase (x : Induction) (M : Model) (c : Checked) : Except String Counterexample :=
  let records : Records := x.st.singles.map fun e =>
    { entity := e, key := none, value := defaultsOf (entitySchema x.st e) }
  let clock := (M "clock").toInt
  if failsIn x.st c records clock then
    .ok { given := givenOf x.st records, clock, command := none, input := none, now := none, violations := [] }
  else .error "the semantics keeps the invariant of the initial records"

/-- The rejection kind that the kind `text` names, as `rejectionKinds` lists them. -/
def rejectionKindOf (text : String) : RejectionKind :=
  match text with
  | "invalid-input" => .invalidInput
  | "reused-id" => .reusedId
  | "not-found" => .notFound
  | "requires" => .requires
  | "already-exists" => .alreadyExists
  | _ => .unavailable

/-- What a transition takes under `M`, as the semantics passes it, and as the counterexample shows it. -/
def takenIn (M : Model) (taken : Taken) (sym : Option (Ir.Arg × SVal)) : Extra × Option Value :=
  match taken, sym with
  | .payload _, some (_, .json fields) => let v := Value.obj (present M fields); (.payload v, some v)
  | .output _, some (_, .json fields) => let v := Value.obj (present M fields); (.output v, some v)
  | .rejection, _ =>
    let kind := ((M "tk.kind").toScalar.toValue?).bind fun | .str k => some k | _ => none
    let r : Rejection := { kind := rejectionKindOf (kind.getD "") }
    (.rejection r, some (ToValue.toValue r))
  | _, _ => (.none, none)

/--
The replay of a model of a machine's query in the semantics: starting the machine, or the microstep of an edge, from the
model's records and machine, after which the semantics must report the invariant `k`.
-/
def replayChart (x : Induction) (fs : Functions IO) (cc : ChartCase) (k : Ir.Condition) (step : ChartStep) (M : Model) :
    IO (Except String Counterexample) := do
  let st := x.st
  let c := cc.chart
  let .ok m := cc.model | return .error "the machine has no model"
  let .ok initial := cc.initial | return .error "the machine has no initial context"
  match x.stateOf M with
  | .error why => return .error why
  | .ok (records, given, clock) =>
  let id := InstanceId.top c.name
  let base : State := { service := st.service, records, now := clock, started := true }
  let failing (s : State) (cond : Ir.Condition) : Bool := match s.machine? id with
    | some i => failsConcrete { fields := Ir.fieldsOf st, args := Ir.scopeArgs st (s.scopeOf i none) .none,
                                records := s.records } cond
    | none => false
  let context : Value := match initial with
    | .obj fields => .obj (fields.filter (·.1 ∉ cc.relevant) ++ present M (cc.relevant.map fun f => (f, valVar s!"ctx.{f}")))
    | v => v
  let machineIn (config : Nat) : State × Value :=
    let active := m.configs[config]!
    ({ base with machines := [{ chart := c, id, context, entered := active.map (·, clock) }] },
     .obj [("active", .arr (active.map .str)), ("context", context)])
  let reported (s : State) : Except String (List Violation) :=
    if !failing s k then .error "the semantics keeps the invariant after the case's step"
    else .ok (s.violations.map (·.toViolation))
  let assumed (s : State) : Bool := cc.invariants.all (!failing s ·)
  match step with
  | .start =>
    let s ← startInstance st fs base c
    if s.halted.isSome then return .error "the semantics halts on starting the machine"
    let r ← checkChart fs st id (← enter fs st 0 id [c.initial] ⟨s, {}⟩)
    if r.halted then return .error "the semantics halts on entering the initial states"
    return (reported r.state).map fun violations =>
      { given, clock, command := none, input := none, now := none, violations }
  | .edge i =>
    let some e := m.edges[i]? | return .error "no such edge"
    let (s, machine) := machineIn e.source
    if !assumed s then return .error "the case's machine fails an invariant, which the induction assumes"
    let now := (M "now").toInt
    let s := { s with now }
    let sym := ((takenOf st "tk" (cc.expressions st) e.taken).toOption.map (·.1)).join
    let (extra, taken) := takenIn M e.taken sym
    let some inst := s.machine? id | return .error "the machine is missing"
    match ← choose fs st s inst extra (e.earlier ++ [e.transition]) with
    | .ok (some t) => if t != e.transition then return .error "the semantics chooses another transition"
    | _ => return .error "the semantics chooses no transition"
    let r ← microstep fs st 0 id [(id, e.transition)] extra ⟨s, {}⟩
    if r.halted then return .error "the semantics halts in the case's microstep"
    return (reported r.state).map fun violations =>
      { given, clock, command := none, input := none, now := some now, machine := some machine,
        transition := some (ToValue.toValue e.transition.ref), taken, violations }

/-- The records as one canonical text, which two orders compare: the order of rows is not part of the state. -/
def recordsText (records : Records) : List String :=
  (records.map fun r => s!"{r.entity} {repr r.key} {r.value.canonical}").toArray.qsort (· < ·) |>.toList

/--
The replay of a model of a pair's query in the semantics: both automations react to the decoded payload, the first
then the second, and their commands run in both orders from the decoded records. The two orders must differ in the
records or in which commands the service accepts.
-/
def replayPair (x : Induction) (fs : Functions IO) (pair : Pair) (o : Orders) (M : Model) :
    IO (Except String Counterexample) := do
  let st := x.st
  match x.stateOf M with
  | .error why => return .error why
  | .ok (records, given, clock) =>
  let now := (M "now").toInt
  let payload := Value.obj (present M o.payload)
  let react (a : Automation) (created : List String) : IO (Option (Value × List String)) := do
    for b in a.binds do
      unless (← fs.automationBinding a.name b payload records now) matches .ok true do return none
    for g in a.guard do
      unless (← fs.automationGuard a.name g payload records now) matches .ok true do return none
    let keys := ({ service := st.service, createdEntities := created } : State).nextKeys
    match ← fs.react a.name payload records now keys with
    | .ok (input, made) => pure (some (input, created ++ made))
    | .error _ => pure none
  let some (first, created) ← react pair.first [] | return .error s!"{pair.first.name} does not react in the semantics"
  let some (second, _) ← react pair.second created | return .error s!"{pair.second.name} does not react in the semantics"
  let run (rs : Records) (a : Automation) (input : Value) : IO (Records × Bool) := do
    match ← evaluate st fs rs now a.sends.ref.name input with
    | .accepted written _ _ => pure (written, true)
    | _ => pure (rs, false)
  let (r1, a1) ← run records pair.first first
  let (r12, b1) ← run r1 pair.second second
  let (r2, b2) ← run records pair.second second
  let (r21, a2) ← run r2 pair.first first
  if recordsText r12 == recordsText r21 && a1 == a2 && b1 == b2 then
    return .error "the semantics gives the same records and answers in both orders"
  let outcome (rs : Records) (x y : Bool) : Value :=
    .obj [("records", givenOf st rs), ("accepted", .obj [(pair.first.name, .bool x), (pair.second.name, .bool y)])]
  let firstStep := StepName.command pair.first.sends (.automation pair.first.name) first
  let secondStep := StepName.command pair.second.sends (.automation pair.second.name) second
  let found := Explore.ChoiceDependent.stepOrder (st.ref pair.first.name) firstStep secondStep [firstStep, secondStep]
    [secondStep, firstStep] (.state (outcome r12 a1 b1) (outcome r21 a2 b2))
  return .ok { given, clock, command := none, input := none, now := some now, taken := some payload,
               violations := [found.toViolation] }

/--
The verdict of a solver's answer, from the replay of its model when it is sat. `exact` and `complete` are those of the
query's facts (Facts): an unsat answer proves the property only when the facts are complete.
-/
def verdictOf (answer : Smt.Answer) (exact complete : Bool) (replay : Model → IO (Except String Counterexample))
    (what : String) : IO (Option Verdict) := do
  match answer with
  | .unsat =>
    if complete then pure none
    else pure (some (.undecided s!"no case {what} among the values that the encoding holds, which leave out some values of a schema, such as decimals"))
  | .unknown why => pure (some (.undecided s!"{what}: {why}"))
  | .sat values =>
    match ← replay (Smt.Answer.model values) with
    | .ok case => pure (some (.counterexample case))
    | .error why =>
      if exact then throw (IO.userError s!"prove's encoding disagrees with the semantics {what}: {why}")
      pure (some (.undecided s!"the solver's case {what} is outside what the encoding states exactly: {why}"))

def Induction.results (x : Induction) (answers : List (Asked × Smt.Answer)) : IO (List ProveResult) := do
  let fs := x.st.structure.program.toFunctions x.st fun _ => pure ()
  let p := x.st.structure.program
  let result (prop : Property) (verdict : Verdict) : ProveResult :=
    { service := x.st.service, property := prop, creates := x.creates, verdict }
  let chartProps := x.charts.flatMap fun cc => cc.invariants.map fun k => (cc, k, Property.invariant (x.st.ref cc.chart.name) k.name)
  let ensures := x.st.commands.flatMap fun c => (conditionsOf p.ensures (x.st.ref c)).map fun e =>
    (c, Property.ensures (x.st.ref c) e.name)
  let queryEnsures := x.answers.flatMap fun (q, _) => (conditionsOf p.queryEnsures (x.st.ref q)).map fun e =>
    (q, e, Property.ensures (x.st.ref q) e.name)
  let dangling := (ownRefs x.st).map fun (e, field, _) => Property.danglingRef (x.st.ref e) field
  if let some why := x.blocked then
    return ((x.checked.map (·.ref)) ++ ensures.map (·.2) ++ queryEnsures.map (·.2.2) ++ dangling ++
      x.responses.map (·.ref)).map
      (result · (.undecided why)) ++ chartProps.map (fun (_, _, prop) => result prop (.undecided why)) ++
        x.pairs.map fun (pair, _) => result (pairProperty x.st pair) (.undecided why)
  let (init, initFacts) := initialOf x.st
  let gapOf (c : String) : Option String := answers.findSome? fun
    | (.gap c', .sat _) => if c' == c then
        some s!"the command {c} can write a value that the encoding does not hold, such as a record outside its schema"
      else none
    | (.gap c', .unknown why) => if c' == c then some s!"whether the command {c} stays within the encoding is unknown: {why}"
      else none
    | _ => none
  -- A property that steps can fail: proved when no step of `commands` can.
  let afterSteps (prop : Property) (commands : List String) : IO Verdict := do
    for c in commands do
      match x.steps.lookup c with
      | some (.error why) => return .undecided s!"the command {c} has no encoding: {why}"
      | some (.ok step) =>
        if let some (_, .error why) := (x.stepGoals c step).find? (·.1 == prop) then
          return .undecided s!"the property has no encoding: {why} (in {c})"
        if let some why := gapOf c then return .undecided why
      | none => pure ()
    for c in commands do
      let some (.ok step) := x.steps.lookup c | continue
      for (asked, a) in answers do
        let .fails c' prop' := asked | continue
        if c' != c || prop' != prop then continue
        let replay := (replayStep x fs · c step prop)
        if let some v ← verdictOf a (x.facts.exact && step.facts.exact) (x.facts.complete && step.facts.complete) replay
            s!"after {c}" then
          return v
    return .proved
  let invariants ← x.checked.mapM fun ch => do
    match failsOn init clockT ch with
    | .error why => return result ch.ref (.undecided s!"the invariant has no encoding: {why}")
    | .ok _ => pure ()
    let base : Option Smt.Answer := answers.findSome? fun
      | (.base ref, a) => if ref == ch.ref then some a else none
      | _ => none
    if let some a := base then
      let replay (M : Model) : IO (Except String Counterexample) := pure (replayBase x M ch)
      if let some v ← verdictOf a initFacts.exact initFacts.complete replay "of the initial records" then return result ch.ref v
    return result ch.ref (← afterSteps ch.ref x.st.commands)
  let commandEnsures ← ensures.mapM fun (c, prop) => do pure (result prop (← afterSteps prop [c]))
  let answered ← queryEnsures.mapM fun (q, e, prop) => do
    match x.answers.lookup q with
    | some (.error why) => return result prop (.undecided s!"the query {q} has no encoding: {why}")
    | some (.ok a) =>
      match a.ensuresFails x.pre e with
      | .error why => return result prop (.undecided s!"the property has no encoding: {why}")
      | .ok _ => pure ()
      for (asked, ans) in answers do
        let .answer q' prop' := asked | continue
        if q' != q || prop' != prop then continue
        if let some v ← verdictOf ans false (x.facts.complete && a.facts.complete) (replayAnswer x fs · q a e.name) s!"of {q}" then return result prop v
      return result prop .proved
    | none => return result prop (.undecided s!"the query {q} has no encoding")
  let refs ← dangling.mapM fun prop => do pure (result prop (← afterSteps prop x.st.commands))
  let charts ← chartProps.mapM fun (cc, k, prop) => do
    match x.chartQueries cc k with
    | .error why => return result prop (.undecided s!"the invariant has no encoding: {why}")
    | .ok queries =>
    for (step, _, exact, complete) in queries do
      let answer := answers.findSome? fun
        | (.chart prop' step', a) => if prop' == prop && step' == step then some a else none
        | _ => none
      let some a := answer | continue
      let what := match step with
        | .start => "on starting the machine"
        | .edge i => s!"in the machine's microstep {i}"
      if let some v ← verdictOf a exact complete (replayChart x fs cc k step ·) what then return result prop v
    return result prop .proved
  let find (asked : Asked → Bool) : Option Smt.Answer := answers.findSome? fun (a, v) => if asked a then some v else none
  let pairs ← x.pairs.mapM fun (pair, orders) => do
    let prop := pairProperty x.st pair
    match orders with
    | .error why => return result prop (.undecided s!"the pair has no encoding: {why}")
    | .ok o =>
    match find (fun | .pairGap p' => p' == prop | _ => false) with
    | some (.sat _) => return result prop (.undecided "a step of the pair can write a value that the encoding does not hold")
    | some (.unknown why) => return result prop (.undecided s!"whether the pair stays within the encoding is unknown: {why}")
    | _ => pure ()
    let facts := x.facts ++ nowFacts ++ o.facts
    let some a := find (fun | .pairDiffers p' => p' == prop | _ => false) | return result prop (.undecided "the pair was not asked")
    match ← verdictOf a facts.exact facts.complete (replayPair x fs pair o ·) "between the two orders" with
    | some v => return result prop v
    | none => return result prop .proved
  -- A response: proved when `when` implies `expect` at every visible state, so no obligation ever opens; else a case
  -- in a service with no automation and no chart, which nothing internal can repair, misses it.
  let internal := !x.st.automations.isEmpty || !x.st.charts.isEmpty
  let responses ← x.responses.mapM fun r => do
    let done (v : Verdict) : ProveResult := match v with
      | .counterexample _ => { result r.ref v with assumes := some progressAssumption }
      | _ => result r.ref v
    match failsOn init clockT r with
    | .error why => return done (.undecided s!"the response has no encoding: {why}")
    | .ok _ => pure ()
    for (c, step) in x.steps do
      match step with
      | .error why => return done (.undecided s!"the command {c} has no encoding: {why}")
      | .ok step =>
        if let .error why := failsOn step.post step.now r then return done (.undecided s!"the response has no encoding: {why} (in {c})")
        if let some why := gapOf c then return done (.undecided why)
    let unmet := "its when can hold without its expect at a visible state, and the service's automations or charts may meet its expect later; prove proves a response only when its when implies its expect"
    if let some a := find (fun | .base p' => p' == r.ref | _ => false) then
      if let .sat _ := a then return done (.undecided s!"its when can hold without its expect in the initial records")
      if let some v ← verdictOf a initFacts.exact initFacts.complete (fun _ => pure (.error "")) "of the initial records" then
        return done v
    for (asked, a) in answers do
      let command : Option (Option (String × Step)) := match asked with
        | .fails c p' => if p' == r.ref then (x.steps.lookup c).bind (·.toOption) |>.map fun s => some (c, s) else none
        | .tick p' => if p' == r.ref then some none else none
        | _ => none
      let some command := command | continue
      if let .sat _ := a then
        if internal then return done (.undecided unmet)
      let exact := x.facts.exact && (command.map (·.2.facts.exact)).getD true
      let complete := x.facts.complete && (command.map (·.2.facts.complete)).getD true
      if let some v ← verdictOf a exact complete (replayResponse x fs · r command) "of the response" then return done v
    return done .proved
  pure (invariants ++ commandEnsures ++ answered ++ refs ++ charts ++ pairs ++ responses)

/-- The results of each property of each spec service, from Z3's answers to proveQueriesOf's scripts, in order. -/
def proveOf (j : Spec.Structure) (answers : List String) : IO (List ProveResult) := do
  let inductions ← (specServices j).mapM (inductionOf j)
  let mut rest := answers
  let mut results := []
  for x in inductions do
    let asked := x.queries.map (·.1)
    let mine := asked.zip (rest.take asked.length |>.map Smt.Answer.read)
    rest := rest.drop asked.length
    results := results ++ (← x.results mine)
  pure results

end Tazuna.Engine
