import Engine.Run
import Tazuna.Smt.Script
import Tazuna.Smt.State
import Tazuna.Smt.Chart
import Tazuna.Smt.Pair
import Tazuna.Smt.Chain
import Tazuna.Semantics.Service.ChoiceDependent

/-!
prove: the base case and the inductive step of each invariant of each spec service, within the service's bounds, and
from any state where they hold, that every ensures of a command or query holds and that no command leaves a ref
dangling. TS runs Z3, so the engine asks it for the outputs on every SMT-LIB script in one `solve`, then replays each
counterexample in the semantics and gives one result per property.
-/

namespace Tazuna.Engine

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Smt

/-- The sender of an own command: an automation, or the activity `key` of `state` of the chart `definition`. -/
inductive CommandSender where
  | automation (definition : Ir.Ref)
  | activity (definition : Ir.Ref) (state key : String)
deriving BEq, Repr, Inhabited

derive_wire CommandSender tag "kind"

def CommandSender.definition : CommandSender → Ir.Ref
  | .automation d | .activity d .. => d

/--
What prove checks: an invariant of an entity's records, a machine or screen, or the service (which names itself); an
ensures of a command or query; that a ref field of an entity never names a missing record; that the order of two own
commands that can wait in one round changes no outcome; that the order of two deadlines due at one time, or of two
messages that arrive at once, changes no outcome; that the order of other steps that no line orders changes no outcome,
which prove names but does not compare yet; or that a response of an entity is met in time.
-/
inductive Property where
  | invariant (definition : Ir.Ref) (name : String)
  | response (definition : Ir.Ref) (name : String)
  | ensures (definition : Ir.Ref) (name : String)
  | danglingRef (definition : Ir.Ref) (field : String)
  | stepOrder (first : CommandSender) (second : CommandSender)
  /-- The deadline `name` of `state` of the chart `definition`, and the deadline `otherName` of `otherState` of `other`. -/
  | deadlineTie (definition : Ir.Ref) (state name : String) (other : Ir.Ref) (otherState otherName : String)
  /-- Two messages from other services: events that the service receives, or answers to the requests named. -/
  | arrivalTie (definition : Ir.Ref) (other : Ir.Ref)
  /-- The events of one event group of the command `definition` that the machine or automation `receiver` takes. -/
  | groupOrder (definition : Ir.Ref) (receiver : Ir.Ref)
  /-- The deadline `name` of `state` of the chart `definition`, and the message `other` from another service that
  arrives when it is due. -/
  | deadlineArrivalTie (definition : Ir.Ref) (state name : String) (other : Ir.Ref)
deriving BEq, Repr, Inhabited

derive_wire Property tag "kind"

def Property.definition : Property → Ir.Ref
  | .stepOrder s _ => s.definition
  | .invariant d _ | .response d _ | .ensures d _ | .danglingRef d _ | .deadlineTie d .. | .arrivalTie d _
  | .groupOrder d _ | .deadlineArrivalTie d .. => d

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
  /-- The caller of the command or query. -/
  caller : Option Caller := none
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

/--
What a verdict assumes beyond the spec: a property that prove did not prove, which a proof assumed of the state it starts
from; or the progress of runs, which a response's counterexample assumes.
-/
inductive Assumed where
  | unproved (property : Property)
  | progress (runs : String)

derive_wire Assumed tag "kind" serialize_only

/--
What prove found of one property, within the bounds of creating at most `creates` records of each keyed entity and of
at most `items` items in each array or Bag of an input, payload or answer.
-/
structure ProveResult where
  service : String
  property : Property
  creates : List (String × Nat)
  items : Nat
  verdict : Verdict
  /-- What the verdict assumes beyond the spec; a proof that assumes none holds outright. -/
  assumes : List Assumed

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
    -- missingBodies stops prove before a when lacks its expect.
    whens.filterMap fun w => (expects.find? (·.name == w.name)).map fun x =>
      { ref := .response (st.ref e) w.name, holder := if st.singles.contains e then .single e else .keyed e,
        condition := { name := w.name, body := .or (.not w.body) x.body } }

/--
The induction of a machine's or screen's invariants: its model, the context fields that the encoding holds, and the
context it starts with, or why it has none.
-/
structure ChartCase where
  chart : Service.Chart
  invariants : List Ir.Condition
  model : Except String ChartModel
  relevant : List String
  /-- The schema of each relevant context field and whether the context must hold it, as propertiesWith gives them. -/
  props : List (String × Value × Bool)
  /-- Whether the encoding leaves out some context fields, which replay then takes as they start. -/
  sliced : Bool
  initial : Except String Value

def chartCaseOf (st : Service) (fs : Functions IO) (c : Service.Chart) : IO (Option ChartCase) := do
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
def conditionsOf (list : List Ir.Conditions) (definition : Ir.Ref) : List Ir.Condition :=
  ((list.find? (·.definition == definition)).map (·.conditions)).getD []

/--
The bodies that the structure names for the service `service` and its program lacks: an ensures of a command or query, a
response's `when` or `expect`, or the invariants of an entity or of the service, which TS writes for every one, none or
empty. Each is a converter bug, which prove and generate stop at instead of reading the missing body as true or absent.
-/
def missingBodies (j : Ir.Structure) (service : String) : List String :=
  let p := j.program
  let names (list : List Ir.Conditions) (d : Ir.Ref) : Option (List String) :=
    (list.find? (·.definition == d)).map (·.conditions.map (·.name))
  let lacks (what : String) (list : List Ir.Conditions) (d : Ir.Ref) (expected : List String) : List String :=
    if names list d == some expected then [] else [s!"{what} of {d.name}"]
  let lacksAny (what : String) (list : List Ir.Conditions) (d : Ir.Ref) : List String :=
    if (names list d).isSome then [] else [s!"{what} of {d.name}"]
  (j.definitions.filter (·.service == service)).flatMap (fun d => match d.body with
    | .command c => lacks "the ensures" p.ensures d.ref c.ensures
    | .query q => lacks "the ensures" p.queryEnsures d.ref q.ensures
    | .entity e =>
      lacksAny "the invariants" p.invariant d.ref ++
        lacks "the response whens" p.responseWhen d.ref (e.responses.map (·.name)) ++
        lacks "the response expects" p.responseExpect d.ref (e.responses.map (·.name))
    | _ => []) ++
  lacksAny "the invariants" p.serviceInvariant { service, name := service }

/-- The structure's own spec service `service`, which stops when its program lacks a body that the structure names. -/
def specService (j : Ir.Structure) (service : String) : IO Service := do
  let missing := missingBodies j service
  if !missing.isEmpty then throw (IO.userError s!"the program lacks {", ".intercalate missing}")
  Service.ofStructure j service

/--
Why prove and generate cannot bound the service `st`: it has keyed entities and no `bounds()`, or its `bounds()` give
no creates bound for one of them, which plain JS lets through the TS type. Reading a missing bound as zero would leave
the entity without records, so every property over it would hold.
-/
def unbounded (j : Ir.Structure) (st : Service) : Option String :=
  let keyed := st.entities.filter (!st.singles.contains ·)
  match (j.bounds.find? (·.service == st.service)).map (·.creates) with
  | none => if keyed.isEmpty then none else some "the service has no bounds()"
  | some creates => (keyed.find? (creates.lookup · |>.isNone)).map fun e =>
    s!"the bounds() of the service give no creates bound for the entity {e}"

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


/-- A time after the state's, which a response reads when time passes with no message. -/
def laterT : Term := .var "later" .int

/--
The initial records: no record of a keyed entity, and each single entity's record of its schema defaults. A default that
no term holds, such as an array, is a variable, which makes the facts inexact.
-/
def initialOf (st : Service) : SRecords × Facts := Id.run do
  let mut facts := Facts.none
  let mut singles := []
  for e in st.singles do
    let defaults := defaultsOf (entitySchema st e)
    let mut fields := []
    for f in Eval.fieldsOf st e do
      match defaults.field? f with
      | none => fields := fields ++ [(f, undefT)]
      | some v =>
        match litTerm v with
        | .ok l => fields := fields ++ [(f, l)]
        | .error _ =>
          fields := fields ++ [(f, valVar s!"init.{e}.{f}")]
          facts := facts ++ { vars := [(s!"init.{e}.{f}", .val)], asserts := [], fit := .over }
    singles := singles ++ [(e, fields)]
  pure ({ keyed := (st.entities.filter (!st.singles.contains ·)).map (·, []), singles, keyFields := st.keyFields }, facts)

/-- One service's symbolic induction: its state, and the step of each command, or why the step has no encoding. -/
structure Induction where
  st : Service
  creates : List (String × Nat)
  pre : SRecords
  /-- The facts of `pre` and of its time `clock`. -/
  facts : Facts
  /-- What the induction assumes of `pre`: that every encoded invariant holds, and that no own ref dangles (SRecords.alive). -/
  holds : Term
  steps : List (String × Except String Step)
  /-- The answer of each query, or why it has no encoding. -/
  answers : List (String × Except String Answered)
  checked : List Checked
  /-- The responses, which the induction checks but, unlike `checked`, does not assume. -/
  responses : List Checked
  charts : List ChartCase
  /-- Each pair of steps that no line orders, with its two orders, or why prove does not compare them. -/
  unordered : List (Unordered × Except String TieOrders)
  /-- Why the service has no induction, such as missing bounds. -/
  blocked : Option String

def inductionOf (j : Ir.Structure) (service : String) : IO Induction := do
  let st ← specService j service
  let p := j.program
  let checked := invariantsOf st p
  let fs := Eval.Program.toFunctions p st fun _ => pure ()
  let charts ← st.charts.filterMapM (chartCaseOf st fs)
  let creates := Ir.createsOf j.bounds service
  let pre := SRecords.named st creates "pre"
  let used := pre.usedVars "pre"
  let holds := conj (checked.filterMap (fun c => (failsOn pre clockT c).toOption.map .not) ++ [pre.alive st])
  let blocked := unbounded j st
  pure { st, creates, pre, facts := pre.facts st "pre" ++ clockFacts, holds,
         steps := st.commands.map fun c => (c, stepOf st p pre used c),
         answers := (st.queries.filter fun q => !(conditionsOf p.queryEnsures (st.ref q)).isEmpty).map fun q =>
           (q, answerOf st p pre clockT q),
         checked, responses := responsesOf st p, charts, blocked,
         unordered := (unorderedOf st).map fun u => (u, match u with
           | .sends a b => (sendOrders st p pre used nowT a b).mapError (s!"the pair has no encoding: {·}")
           | .tie t => (tieOrders st p pre used nowT t).mapError (s!"the tie has no encoding: {·}")
           | .deadlineArrival .. =>
             .error "prove does not compare yet a deadline with a message from another service that arrives when it is due"
           | .group .. =>
             .error "prove does not compare yet the orders in which one machine takes the events of one event group") }

/-- The property of a pair of steps that no line orders: that their order changes no outcome. -/
def unorderedProperty (st : Service) : Unordered → Property
  | .sends a b => .stepOrder (senderOf a) (senderOf b)
  | .tie (.deadlines a b) => .deadlineTie (st.ref a.chart) a.state a.name (st.ref b.chart) b.state b.name
  | .tie (.arrivals a b) => .arrivalTie a.ref b.ref
  | .deadlineArrival d a => .deadlineArrivalTie (st.ref d.chart) d.state d.name a.ref
  | .group c chart => .groupOrder (st.ref c) (st.ref chart)
where
  senderOf : SenderRef → CommandSender
    | .automation a => .automation (st.ref a)
    | .activity c n k => .activity (st.ref c) n k

/--
A step of a machine's induction: starting it, or a microstep of one of its edges. A command changes no machine, and an
invariant reads only the machine's context and active states, so no command can fail one. The semantics checks the
invariants after the same steps (checkChart).
-/
inductive ChartStep where
  | start
  | edge (index : Nat)
deriving BEq

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
        fit := Fit.all (fits.map (·.fit)) })

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
The queries of the induction of the invariant `k` of `cc`, each with the fit of its facts: starting
the machine with any records, and each edge from a state where every invariant holds.
-/
def Induction.chartQueries (x : Induction) (cc : ChartCase) (k : Ir.Condition) :
    Except String (List (ChartStep × Query × Fit)) := do
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
  let start : ChartStep × Query × Fit :=
    (.start, { vars := x.facts.vars,
               asserts := x.facts.asserts ++ [x.holds, .not started.halted] ++ startFits.map (·.term) ++ [startFails] },
     Fit.all ([x.facts.fit, .of (!cc.sliced) true, started.fit] ++ startFits.map (·.fit)))
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
    pure ((ChartStep.edge i, q, Fit.all ([facts.fit, .of (!cc.sliced) true, moved.fit] ++ postFits.map (·.fit))) :
      ChartStep × Query × Fit)
  pure ([start] ++ edges)

/-- The own spec services of the structure, in order. -/
def specServices (j : Ir.Structure) : List String := (j.services.filter (!·.external)).map (·.name)

/-- The records of a state by entity, as the counterexample's Given shows them. -/
def givenOf (st : Service) (records : Records) : Value :=
  .obj (st.entities.map fun e =>
    let rows := records.filter (·.entity == e)
    if st.singles.contains e then (e, ((rows.head?).map (·.value)).getD .null)
    else (e, .arr (rows.map (·.value))))

/-- Whether `c` fails in `env`, as the semantics evaluates it. -/
def failsConcrete (env : Eval.Env) (c : Ir.Condition) : Bool :=
  match (Eval.firstFailing env [c]).run' with
  | (.ok none, _) => false
  | _ => true

/-- Whether `faults` report `c` failing, or throwing, on the record `key` of an entity. -/
def reports (st : Service) (c : Checked) (command : String) (fault : Fault) : Bool :=
  match c.holder, fault with
  | .keyed e, .failedEntityInvariant d _ _ cmd | .single e, .failedSingleInvariant d _ cmd =>
    d == st.ref e && cmd == st.ref command
  | .keyed e, .exception (some d) | .single e, .exception (some d) | .keyed e, .notOnly (some d)
  | .single e, .notOnly (some d) => d == st.ref e
  | .service, .failedServiceInvariant _ cmd => cmd == st.ref command
  | .service, .exception none | .service, .notOnly none => true
  | _, _ => false

/-- The caller whose fields a model gives `fields`, none when they hold no caller. -/
def callerIn (M : Model) (fields : List (String × Term)) : Option Caller :=
  (FromValue.fromValue (.obj (present M fields)) : Except String Caller).toOption

/-- The records that the step writes, as the semantics writes them, or none when it rejects or halts before. -/
def writtenBy (st : Service) (fs : Functions IO) (records : Records) (now : Time) (name : String) (input : Value)
    (caller : Caller) : IO (Option (Records × List Fault)) := do
  match ← evaluate st fs records now name input caller with
  | .accepted written _ violations => pure (some (written, violations))
  | .halted violations =>
    -- The halt is a fault such as a throw in ensures; the records the step writes are those decide's events write.
    match ← fs.decide name input caller records now with
    | .ok decided => pure (some (applyAll st records (orderedGroups decided decided.flatten).flatten, violations))
    | .error _ => pure none
  | .rejected _ => pure none

/-- Whether `c` fails at the time `now` on some record of `records` that it is checked on, as the semantics evaluates it. -/
def failsIn (st : Service) (c : Checked) (records : Records) (now : Time) : Bool :=
  let env (args : List (Ir.Arg × Eval.Val)) : Eval.Env :=
    { fields := Eval.fieldsOf st, args := Eval.argsOf (args ++ [(.now, Eval.instant now)]), records }
  match c.holder with
  | .keyed e | .single e => records.any fun r => r.entity == e && failsConcrete (env [(.record, .json r.value)]) c.condition
  | .service => failsConcrete (env []) c.condition

/-- Whether a fault of an ensures of `definition` reports `name` failing, or a throw. -/
def failedEnsures (definition : Ir.Ref) (name : String) : Fault → Bool
  | .failedEnsures d c => d == definition && c == name
  | .exception (some d) | .notOnly (some d) => d == definition
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
  | .stepOrder .. | .deadlineTie .. | .arrivalTie .. | .groupOrder .. | .deadlineArrivalTie .. | .response .. => false

/-- The records of a model's state, or why the state is none that the induction assumes. -/
def Induction.stateOf (x : Induction) (M : Model) : Except String (Records × Value × Int) := do
  let records := (x.pre.conc M).filter fun r => x.st.entities.contains r.entity
  let clock := (M "clock").toInt
  if let some b := x.checked.find? (failsIn x.st · records clock) then
    throw s!"the case's state fails {repr b.ref}, which the induction assumes"
  let fits (r : Row) : Bool := match Semantics.parse (entitySchema x.st r.entity) r.value with
    | some (.ok (.ok _)) => true
    | _ => false
  if let some r := records.find? (!fits ·) then throw s!"the case's record of {r.entity} is outside its schema"
  pure (records, givenOf x.st records, clock)

/-- The result of the replay of a model of a fails query: the counterexample, or why the model is no case of it. -/
def replayStep (x : Induction) (fs : Functions IO) (M : Model) (command : String) (step : Step) (prop : Property) :
    IO (Except String Counterexample) := do
  let input := Value.obj (SJson.concFields M step.input)
  let now := (M "now").toInt
  let some caller := callerIn M step.caller | return .error "the case's caller is no caller"
  match x.stateOf M with
  | .error why => return .error why
  | .ok (pre, given, clock) =>
  match ← writtenBy x.st fs pre now command input caller with
  | none => return .error "the semantics rejects the case's command"
  | some (written, faults) =>
    if !x.failedAfter command now written faults prop then
      return .error "the semantics keeps the property after the case's command"
    return .ok { given, clock, command := some command, input := some input, caller := some caller, now := some now,
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
    let input := Value.obj (SJson.concFields M step.input)
    let now := (M "now").toInt
    let some caller := callerIn M step.caller | return .error "the case's caller is no caller"
    match ← writtenBy x.st fs pre now c input caller with
    | none => return .error "the semantics rejects the case's command"
    | some (written, faults) =>
      let missed ← missedAfter x fs written now r
      if missed.isEmpty then return .error "the semantics opens no obligation after the case's command"
      return .ok { given, clock, command := some c, input := some input, caller := some caller, now := some now,
                   violations := (faults ++ missed).map (·.toViolation) }

/-- The progress that a response's verdict assumes of the runs, which the spec does not state. -/
def progressAssumption : String :=
  "enabled internal steps run, in-flight messages arrive unless a line loses them, and an external service answers " ++
    "only as its deadlines fire; no client sends anything"

/-- The result of the replay of a model of an answer query: the counterexample, or why the model is no case of it. -/
def replayAnswer (x : Induction) (fs : Functions IO) (M : Model) (query : String) (a : Answered) (name : String) :
    IO (Except String Counterexample) := do
  let input := Value.obj (SJson.concFields M a.input)
  let some caller := callerIn M a.caller | return .error "the case's caller is no caller"
  match x.stateOf M with
  | .error why => return .error why
  | .ok (pre, given, clock) =>
  let failed := failedEnsures (x.st.ref query) name
  let case (faults : List Fault) : Counterexample :=
    { given, clock, command := none, query := some query, input := some input, caller := some caller, now := none,
      violations := faults.map (·.toViolation) }
  match ← resolveChecked x.st fs { now := clock, service := x.st.service, records := pre } query input caller with
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
  | .payload _, some (_, .json fields) => let v := Value.obj (SJson.concFields M fields); (.payload v, some v)
  | .output _, some (_, .json fields) => let v := Value.obj (SJson.concFields M fields); (.output v, some v)
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
  let base : Service.State := { service := st.service, records, now := clock, started := true }
  let failing (s : Service.State) (cond : Ir.Condition) : Bool := match s.machine? id with
    | some i => failsConcrete { fields := Eval.fieldsOf st, args := Eval.scopeArgs st (s.scopeOf i none) .none,
                                records := s.records } cond
    | none => false
  let context : Value := match initial with
    | .obj fields => .obj (fields.filter (·.1 ∉ cc.relevant) ++ present M (cc.relevant.map fun f => (f, valVar s!"ctx.{f}")))
    | v => v
  let machineIn (config : Nat) : Service.State × Value :=
    let active := m.configs[config]!
    ({ base with machines := [{ chart := c, id, context, entered := active.map (·, clock) }] },
     .obj [("active", .arr (active.map .str)), ("context", context)])
  let reported (s : Service.State) : Except String (List Violation) :=
    if !failing s k then .error "the semantics keeps the invariant after the case's step"
    else .ok (s.violations.map (·.toViolation))
  let assumed (s : Service.State) : Bool := cc.invariants.all (!failing s ·)
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

/-- The records in a canonical order, which two orders compare: the order of rows is not part of the state. -/
def sortedRecords (records : Records) : Records :=
  records.mergeSort fun a b => decide (s!"{a.entity} {repr a.key} {a.value.canonical}" ≤ s!"{b.entity} {repr b.key} {b.value.canonical}")

/-- The deadlines of the machine `id` that wait, each as its state, name and time, in a canonical order. -/
def deadlinesOf (id : InstanceId) (deadlines : List Service.Deadline) : Value :=
  .arr (((deadlines.filter (·.machine == id)).map fun d =>
    Value.obj [("state", .str d.state), ("name", .str d.name), ("time", ToValue.toValue d.time)]).mergeSort
    fun a b => decide (a.canonical ≤ b.canonical))

/-- The out lines that `s` wrote after its first `from` lines, without their ids, in canonical order: what two orders compare. -/
def outsOf (s : Service.State) («from» : Nat) : List Value :=
  ((s.lines.extract «from» s.lines.size).toList.filterMap fun l =>
    if l.dir != .out then none else match l.body with
      | .command t v _ => some (.obj [("command", ToValue.toValue t), ("input", v)])
      | .query t v _ => some (.obj [("query", ToValue.toValue t), ("input", v)])
      | .event e v _ => some (.obj [("event", ToValue.toValue e), ("payload", v)])
      | b => some (.obj [("line", .str (repr b).pretty)])).mergeSort fun a b => decide (a.canonical ≤ b.canonical)

/-- Whether `target` is a query, which a fulfilled answer answers, rather than a command. -/
def isQuery (st : Service) (target : Ir.Ref) : Bool :=
  (st.structure.definitions.find? (·.ref == target)).any fun d => d.body matches .query _

/-- The string that the value term `t` holds under `M`, or the empty string. -/
def kindText (M : Model) (t : Term) : String := match t.denote M with
  | .val (.str k) => k
  | _ => ""

/--
The replay of a model of a pair's or tie's query in the semantics, from the decoded records and machines: the two own
commands wait in one round, and the queue takes one then the other and the other way, each input from the decoded
payload, input or state; the two deadlines fire one after the other at the model's time, as the clock fires deadlines due
at one time in the order they stand; or the two messages arrive one after the other. Each deadline of an active state
waits at its decoded time. The two orders must differ in whether the service halts, in the records, in a machine's
active states, context, deadlines or requests that wait, or in the lines it writes out.
-/
def replayUnordered (x : Induction) (fs : Functions IO) (u : Unordered) (o : TieOrders) (M : Model) :
    IO (Except String Counterexample) := do
  let st := x.st
  match x.stateOf M with
  | .error why => return .error why
  | .ok (records, given, clock) =>
  let now := (M "now").toInt
  let mut machines := []
  let mut deadlines : List Service.Deadline := []
  let mut shown := []
  for c in st.charts do
    let .ok m := ChartModel.of c | return .error s!"the chart {c.name} has no model"
    let .ok initial ← initialContextOf fs st c.name (.obj []) | return .error s!"the initial context of {c.name} fails"
    let fields := (contextProps st c.name).map fun pr => (pr.1, ctxVar c.name pr.1)
    let context : Value := match initial with
      | .obj fs => .obj (fs.filter (·.1 ∉ fields.map (·.1)) ++ present M fields)
      | v => v
    let active := m.configs[(M s!"cfg.{c.name}").toInt.toNat]?.getD []
    let armed := (deadlinesIn c).filter (active.contains ·.1)
    machines := machines ++ [({ chart := c, id := .top c.name, context, entered := active.map (·, clock) } : Instance)]
    deadlines := deadlines ++ armed.map fun (n, d) =>
      { time := (M s!"dl.{c.name}.{n}.{d}").toInt, order := 0, machine := .top c.name, state := n, name := d, armedBy := 0 }
    shown := shown ++ [(c.name, Value.obj [("active", .arr (active.map .str)), ("context", context),
      ("deadlines", deadlinesOf (.top c.name) deadlines)])]
  let base : Service.State :=
    { service := st.service, records, now := clock, started := true, machines,
      deadlines := deadlines.zipIdx.map fun (d, i) => { d with order := i + 3 }, deadlineCount := deadlines.length + 2 }
  -- What a later message can see of a state: its records, and each machine's active states, context, deadlines and
  -- requests to other services that wait, then the lines that the order wrote, each in a canonical order.
  let outcome (s : Service.State) : Value :=
    let requests (i : Instance) : Value := .arr ((s.pending.filterMap fun p => match p.requester with
      | .state id state => if id == i.id && !p.stale then
          some (Value.obj [("state", .str state), ("key", .str p.activity.key), ("input", p.input)]) else none
      | _ => none).mergeSort fun a b => decide (a.canonical ≤ b.canonical))
    .obj [("halted", .bool s.halted.isSome), ("records", givenOf st (sortedRecords s.records)),
          ("machines", .obj (s.machines.map fun i => (i.chart.name, .obj [
            ("active", .arr ((i.active.mergeSort (· ≤ ·)).map .str)), ("context", i.context),
            ("deadlines", deadlinesOf i.id s.deadlines), ("requests", requests i)]))),
          ("outputs", .arr (outsOf s base.lines.size))]
  let same (a b : Service.State) : Bool :=
    (a.halted.isSome && b.halted.isSome) || (outcome a).canonical == (outcome b).canonical
  let answerOf (target : Ir.Ref) (g : Given) : Ir.Answer :=
    let output := Value.obj (present M g.fields)
    if Term.holds M g.accepted then
      if isQuery st target then .fulfilled output else .accepted (if g.fields.isEmpty then none else some output)
    else
      .rejected { kind := rejectionKindOf (kindText M g.kind) }
  let pendingOf (target : Ir.Ref) (id : String) : Option Pending := do
    let activity : Service.Activity := if isQuery st target then .calls target.name target else .sends target.name target
    match requesterOf st target with
    | .ok (.state chart state key) =>
      let activity := (((st.charts.find? (·.name == chart)).bind (·.state? state)).bind
        (·.activities.find? (·.key == key))).getD activity
      pure { id := .own id, activity, requester := .state (.top chart) state, input := .obj [], turn := 0 }
    | .ok (.automation name) =>
      let activity := ((st.automations.find? (·.name == name)).map (·.sends)).getD activity
      pure { id := .own id, activity, requester := .automation name, input := .obj [], turn := 0 }
    | .error _ => none
  let react (s : Service.State) (a : Automation) (payload : Value) : IO (Option (Service.State × Value)) := do
    for b in a.binds do
      unless (← fs.automationBinding a.name b payload s.records s.now) matches .ok true do return none
    for g in a.guard do
      unless (← fs.automationGuard a.name g payload s.records s.now) matches .ok true do return none
    match ← fs.react a.name payload s.records s.now s.nextKeys with
    | .ok (input, keys) => pure (some (s.createKeys keys, input))
    | .error _ => pure none
  -- The command that `sender` sends, its input as `sending` gives it, waiting in the round of `s`.
  let sentOf (s : Service.State) (sender : SenderRef) (sending : Sending) :
      IO (Option (Service.State × Sent × StepName)) := do
    let inputOf (computed : IO (Option (Service.State × Value))) : IO (Option (Service.State × Value)) :=
      match sending with
      | .input fields => pure (some (s, .obj (present M fields)))
      | _ => computed
    match sender with
    | .automation name =>
      let some a := st.automations.find? (·.name == name) | return none
      let payload := match sending with
        | .payload fields => Value.obj (present M fields)
        | _ => .obj []
      let some (s, input) ← inputOf (react s a payload) | return none
      return some (s, { order := a.order, requester := .automation name, activity := a.sends, serial := none, input,
                        cause := 0 }, .command a.sends (.automation name) input)
    | .activity chart state key =>
      let some i := s.machine? (.top chart) | return none
      let some act := ((i.chart.state? state).map (·.activities.find? (·.key == key))).join | return none
      let computed : IO (Option (Service.State × Value)) := do
        match ← fs.input (s.scopeOf i (some state)) s.records act s.nextKeys with
        | .ok (input, keys) => pure (some (s.createKeys keys, input))
        | .error _ => pure none
      let some (s, input) ← inputOf computed | return none
      let (s, serial) := s.startQueued (.top chart) state
      return some (s, { order := i.chart.order, requester := .state (.top chart) state, activity := act,
                        serial := some serial, input, cause := 0 }, .command act (.state (.top chart) state) input)
  let (steps, taken, s1, s2) ← match u with
    | .sends a b =>
      let s := { base with now }
      let some (s, sa, na) ← sentOf s a (o.sendings.getD 0 .computed) | return .error "the first command is not sent in the semantics"
      let some (s, sb, nb) ← sentOf s b (o.sendings.getD 1 .computed) | return .error "the second command is not sent in the semantics"
      let run (commands : List Sent) := drain st fs Limit.messageWork.max s { commands }
      pure ((na, nb), some (Value.obj [("first", sa.input), ("second", sb.input)]),
        ← run [sa, sb], ← run [sb, sa])
    | .deadlineArrival .. | .group .. => return .error "prove does not compare the pair"
    | .tie (.deadlines a b) =>
      let deadline (d : DeadlineRef) (order : Nat) : Service.Deadline :=
        { time := now, order, machine := .top d.chart, state := d.state, name := d.name, armedBy := 0 }
      let others := base.deadlines.filter fun d => !(d.machine == .top a.chart && d.state == a.state && d.name == a.name) &&
        !(d.machine == .top b.chart && d.state == b.state && d.name == b.name)
      let run (ds : List Service.Deadline) := fireDue st fs now Limit.dueDeadlines.max
        { base with deadlines := ds ++ others }
      pure ((StepName.deadline (.top a.chart) a.state a.name, StepName.deadline (.top b.chart) b.state b.name), none,
        ← run [deadline a 1, deadline b 2], ← run [deadline b 2, deadline a 1])
    | .tie (.arrivals a b) =>
      let s := { base with now }
      let ga := o.given.getD 0 {}
      let gb := o.given.getD 1 {}
      let shownOf (arrival : Arrival) (g : Given) : Value := match arrival with
        | .event _ => .obj (present M g.fields)
        | .answer target => ToValue.toValue (answerOf target g)
      -- Each answer's request waits from the start, as the state's requester sent it before.
      let pending := ([(a, "a"), (b, "b")].filterMap fun (arrival, id) => match arrival with
        | .answer target => (pendingOf target id).map ((id, ·))
        | .event _ => none)
      let s := { s with pending := pending.map (·.2) }
      let arrive (s : Service.State) (arrival : Arrival) (id : String) (g : Given) : IO Service.State :=
        match arrival, pending.lookup id with
        | .answer target, some p => answerRequest st fs s none p (answerOf target g)
        | .answer _, none => pure s
        | .event e, _ => receive st fs s e (.received e.service id) (.obj (present M g.fields)) none
      pure ((StepName.arrival a.ref s!"{a.ref.service}/a", StepName.arrival b.ref s!"{b.ref.service}/b"),
        some (Value.obj [("first", shownOf a ga), ("second", shownOf b gb)]),
        ← arrive (← arrive s a "a" ga) b "b" gb, ← arrive (← arrive s b "b" gb) a "a" ga)
  if same s1 s2 then return .error "the semantics ends the same in both orders"
  let found := ChoiceDependent.stepOrder (unorderedProperty st u).definition steps.1 steps.2 (outcome s1)
    (outcome s2)
  return .ok { given, clock, command := none, input := none, now := some now, machine := some (.obj shown), taken,
               violations := [found.toViolation] }

/--
The verdict of a solver's answer, from the replay of its model when it is sat. `fit` is that of the query's facts: an
unsat answer proves the property only when they are complete, and a replay that disagrees is a bug only when they are
precise.
-/
def verdictOf (answer : Smt.Answer) (fit : Fit) (replay : Model → IO (Except String Counterexample))
    (what : String) : IO (Option Verdict) := do
  match answer with
  | .unsat =>
    if fit.complete then pure none
    else pure (some (.undecided s!"no case {what} among the values that the encoding holds, which leave out some values of a schema, such as decimals"))
  | .unknown why => pure (some (.undecided s!"{what}: {why}"))
  | .sat values =>
    match ← replay (Smt.Answer.model values) with
    | .ok case => pure (some (.counterexample case))
    | .error why =>
      if fit.precise then throw (IO.userError s!"prove's encoding disagrees with the semantics {what}: {why}")
      pure (some (.undecided s!"the solver's case {what} is outside what the encoding states exactly: {why}"))

/-- A query that a property's verdict needs: its script, and the verdict that its answer gives, none when the answer leaves the property standing. -/
structure Obligation where
  script : String
  decide : Smt.Answer → IO (Option Verdict)

def Obligation.of (q : Query) (decide : Smt.Answer → IO (Option Verdict)) : Obligation :=
  { script := q.script proveRlimit, decide }

/-- How prove decides a property: with no query, or by its obligations in order, proved when every answer leaves it standing. -/
inductive Plan where
  | decided (verdict : Verdict)
  | asks (obligations : List Obligation)

/-- The plan of `checks` in order: the first that decides with no query, or else all their obligations. -/
def Plan.all (checks : List (Except Verdict (List Obligation))) : Plan :=
  match checks.mapM id with
  | .error v => .decided v
  | .ok obligations => .asks obligations.flatten

/-- The verdict that an answer gives when only unsat leaves the property standing. -/
def withinEncoding (what : String) : Smt.Answer → IO (Option Verdict)
  | .unsat => pure none
  | .sat _ => pure (some (.undecided what))
  | .unknown why => pure (some (.undecided s!"whether {what} is unknown: {why}"))

/-- Each property of the induction, in result order, and how prove decides it. -/
def Induction.plans (x : Induction) : List (Property × Plan) := Id.run do
  let fs := Eval.Program.toFunctions x.st.structure.program x.st fun _ => pure ()
  let p := x.st.structure.program
  let chartProps := x.charts.flatMap fun cc => cc.invariants.map fun k => (cc, k, Property.invariant (x.st.ref cc.chart.name) k.name)
  let ensures := x.st.commands.flatMap fun c => (conditionsOf p.ensures (x.st.ref c)).map fun e =>
    (c, Property.ensures (x.st.ref c) e.name)
  let queryEnsures := x.answers.flatMap fun (q, a) => (conditionsOf p.queryEnsures (x.st.ref q)).map fun e =>
    (q, a, e, Property.ensures (x.st.ref q) e.name)
  let dangling := (ownRefs x.st).map fun (e, field, _) => Property.danglingRef (x.st.ref e) field
  let props := x.checked.map (·.ref) ++ ensures.map (·.2) ++ queryEnsures.map (·.2.2.2) ++ dangling ++
    chartProps.map (·.2.2) ++ x.unordered.map (unorderedProperty x.st ·.1) ++ x.responses.map (·.ref)
  if let some why := x.blocked then return props.map (·, .decided (.undecided why))
  let (init, initFacts) := initialOf x.st
  let initQuery (fails : Term) : Query :=
    let facts := clockFacts ++ initFacts
    { vars := facts.vars, asserts := facts.asserts ++ [fails] }
  let encoded (c : String) : Except Verdict Step := match x.steps.lookup c with
    | some (.ok step) => pure step
    | some (.error why) => throw (.undecided s!"the command {c} has no encoding: {why}")
    | none => throw (.undecided s!"the command {c} has no step")
  let gap (c : String) (step : Step) : Obligation := .of (x.query step step.gap)
    (withinEncoding s!"the command {c} can write a value that the encoding does not hold, such as a record outside its schema")
  let afterSteps (prop : Property) (commands : List String) : Plan := Plan.all <| (commands.map fun c => do
      let step ← encoded c
      match (x.stepGoals c step).lookup prop with
      | some (.ok fails) =>
        let replay := (replayStep x fs · c step prop)
        pure [gap c step, .of (x.query step (.and (.not step.gap) fails)) fun a =>
          verdictOf a (x.facts ++ step.facts).fit replay s!"after {c}"]
      | some (.error why) => throw (.undecided s!"the property has no encoding: {why} (in {c})")
      | none => throw (.undecided s!"the command {c} has no goal for the property"))
  let invariants := x.checked.map fun ch =>
    (ch.ref, match failsOn init clockT ch with
      | .error why => .decided (.undecided s!"the invariant has no encoding: {why}")
      | .ok fails =>
        let base := Obligation.of (initQuery fails) fun a =>
          verdictOf a initFacts.fit (fun M => pure (replayBase x M ch)) "of the initial records"
        match afterSteps ch.ref x.st.commands with
        | .decided v => .decided v
        | .asks obligations => .asks (base :: obligations))
  let commandEnsures := ensures.map fun (c, prop) => (prop, afterSteps prop [c])
  let answered := queryEnsures.map fun (q, answered, e, prop) =>
    (prop, match answered with
      | .error why => .decided (.undecided s!"the query {q} has no encoding: {why}")
      | .ok a =>
        match a.ensuresFails x.pre e with
        | .error why => .decided (.undecided s!"the property has no encoding: {why}")
        | .ok fails =>
          .asks [.of { vars := x.facts.vars ++ a.facts.vars,
                       asserts := x.facts.asserts ++ [x.holds] ++ a.facts.asserts ++ [a.answered, fails] } fun ans =>
            verdictOf ans (x.facts ++ a.facts).fit (replayAnswer x fs · q a e.name) s!"of {q}"])
  let refs := dangling.map fun prop => (prop, afterSteps prop x.st.commands)
  let charts := chartProps.map fun (cc, k, prop) =>
    (prop, match x.chartQueries cc k with
      | .error why => .decided (.undecided s!"the invariant has no encoding: {why}")
      | .ok queries => .asks (queries.map fun (step, q, fit) =>
        let what := match step with
          | .start => "on starting the machine"
          | .edge i => s!"in the machine's microstep {i}"
        .of q fun a => verdictOf a fit (replayChart x fs cc k step ·) what))
  -- Two orders start from a state where every machine invariant holds too, as the induction of each assumes them all.
  let machinesHold := conj (x.charts.filterMap fun cc => do
    let .ok m := cc.model | none
    let context := (contextProps x.st cc.chart.name).map fun pr => (pr.1, ctxVar cc.chart.name pr.1)
    pure (conj (m.configs.toList.zipIdx.map fun (active, k) =>
      let env := ({ context, active } : SMachine).env cc.chart x.pre clockT none
      match chartHolds env cc.invariants with
      | .ok holds => Term.or (.not (.eq (cfgVar cc.chart.name) (intLit (Int.ofNat k)))) holds
      | .error _ => tt)))
  let unordered := x.unordered.map fun (u, orders) =>
    let noun := match u with
      | .sends .. => "pair"
      | _ => "tie"
    (unorderedProperty x.st u, match orders with
      | .error why => .decided (.undecided why)
      | .ok o =>
        let facts := x.facts ++ nowFacts ++ o.facts
        let ask (goal : List Term) : Query :=
          { vars := facts.vars,
            asserts := facts.asserts ++ [x.holds, machinesHold, o.pre, .not o.first.beyond, .not o.second.beyond] ++ goal }
        let cut := Term.or o.first.cut o.second.cut
        let gap := Term.or o.first.gap o.second.gap
        -- The chains leave out faults, such as a failing invariant after a command, which other properties report.
        -- One query asks for both reasons to leave the pair or tie undecided, and the model tells which it found.
        let beyondFollowed := s!"a message of the {noun} can take more than {chainLimit} steps, past what prove follows"
        .asks [.of (ask [.or cut gap]) (fun
                 | .unsat => pure none
                 | .sat values => pure (some (.undecided (if cut.holds (Smt.Answer.model values) then beyondFollowed
                     else s!"a step of the {noun} can write a value that the encoding does not hold")))
                 | .unknown why => pure (some (.undecided s!"whether the {noun} stays within what prove follows is unknown: {why}"))),
               .of (ask [.not cut, .not gap, o.first.differ o.second]) fun a =>
                 verdictOf a (facts.fit.join .over) (replayUnordered x fs u o ·) "between the two orders"])
  -- A response: proved when `when` implies `expect` at every visible state, so no obligation ever opens; else a case
  -- in a service with no automation and no chart, which nothing internal can repair, misses it.
  let internal := !x.st.automations.isEmpty || !x.st.charts.isEmpty
  let unmet := "its when can hold without its expect at a visible state, and the service's automations or charts may meet its expect later; prove proves a response only when its when implies its expect"
  let responses := x.responses.map fun r =>
    let noEncoding {α : Type} (why : String) : Except Verdict α := throw (.undecided s!"the response has no encoding: {why}")
    let case (fit : Fit) (command : Option (String × Step)) (a : Smt.Answer) : IO (Option Verdict) := do
      if let .sat _ := a then
        if internal then return some (.undecided unmet)
      verdictOf a fit (replayResponse x fs · r command) "of the response"
    (r.ref, Plan.all <|
      (x.steps.map fun (c, _) => do
        let step ← encoded c
        if let .error why := failsOn step.post step.now r then noEncoding s!"{why} (in {c})"
        pure [gap c step]) ++
      [do
        let .ok initFails := failsOn init clockT r | noEncoding "on the initial records"
        let .ok heldFails := failsOn x.pre clockT r | noEncoding "on a state"
        let .ok laterFails := failsOn x.pre laterT r | noEncoding "after time passes"
        let held := Term.not heldFails
        let base := Obligation.of (initQuery initFails) fun a => do
          if let .sat _ := a then return some (.undecided "its when can hold without its expect in the initial records")
          verdictOf a initFacts.fit (fun _ => pure (.error "")) "of the initial records"
        let steps ← x.steps.mapM fun (c, _) => do
          let step ← encoded c
          let .ok fails := failsOn step.post step.now r | noEncoding s!"after {c}"
          pure (Obligation.of (x.query step (.and held (.and (.not step.gap) fails)))
            (case (x.facts ++ step.facts).fit (some (c, step))))
        let tick := Obligation.of { vars := x.facts.vars ++ [("later", .int)],
                                    asserts := x.facts.asserts ++ [x.holds, held, .le clockT laterT, laterFails] }
          (case x.facts.fit none)
        pure ([base] ++ steps ++ [tick])])
  return invariants ++ commandEnsures ++ answered ++ refs ++ charts ++ unordered ++ responses

/--
The properties that the queries of `prop` assume of the state they start from, as an induction assumes them (holds):
every encoded invariant of the records and every own ref's danglingRef; a machine's invariant also its machine's; and a
tie or pair every machine's.
-/
def Induction.assumed (x : Induction) : Property → List Property
  | .invariant d _ =>
    records ++ ((x.charts.find? (x.st.ref ·.chart.name == d)).map chartInvariants).getD []
  | .ensures .. | .danglingRef .. | .response .. => records
  | .stepOrder .. | .deadlineTie .. | .arrivalTie .. =>
    records ++ (x.charts.filter (·.model matches .ok _)).flatMap chartInvariants
  | .groupOrder .. | .deadlineArrivalTie .. => []
where
  records := (x.checked.filter (failsOn x.pre clockT · |>.toOption.isSome)).map (·.ref) ++
    (ownRefs x.st).map fun (e, field, _) => .danglingRef (x.st.ref e) field
  chartInvariants (cc : ChartCase) := cc.invariants.map (.invariant (x.st.ref cc.chart.name) ·.name)

/--
The result of each property of each spec service, asking `solve` once for the solver's output on the script of every
obligation. Every obligation needs its own answer: one missing is an internal error, never a proof. A proof that
assumes a property which prove did not prove lists it in `assumes`, since the proof holds only if that property does.
-/
def proveOf (j : Ir.Structure) (solve : List String → IO (List String)) : IO (List ProveResult) := do
  let all := (← (specServices j).mapM (inductionOf j)).map fun x => (x, x.plans)
  let scripts := (all.flatMap fun (_, plans) => plans.flatMap fun
    | (_, .asks obligations) => obligations.map (·.script)
    | (_, .decided _) => []).eraseDups
  let outputs ← solve scripts
  if outputs.length != scripts.length then
    throw (IO.userError s!"prove got {outputs.length} solver outputs for {scripts.length} scripts")
  let answers : Std.HashMap String String := (scripts.zip outputs).foldl (fun m (k, v) => m.insert k v) {}
  all.flatMapM fun (x, plans) => do
  let verdicts ← plans.mapM fun (prop, plan) => do
    let verdict ← match plan with
      | .decided v => pure v
      | .asks obligations => do
        let mut verdict := Verdict.proved
        for o in obligations do
          let some output := answers.get? o.script | throw (IO.userError "prove has no solver output for an obligation")
          if let some v ← o.decide (Smt.Answer.read output) then
            verdict := v
            break
        pure verdict
    pure (prop, verdict)
  let proved (p : Property) : Bool := verdicts.any fun (q, v) => q == p && v matches .proved
  pure (verdicts.map fun (prop, verdict) =>
    let assumes := match prop, verdict with
      | .response .., .counterexample _ => [.progress progressAssumption]
      | _, .proved => ((x.assumed prop).filter (!proved ·)).map .unproved
      | _, _ => []
    { service := x.st.service, property := prop, creates := x.creates,
      items := Ir.itemsOf x.st.structure.bounds x.st.service, verdict, assumes })

end Tazuna.Engine
