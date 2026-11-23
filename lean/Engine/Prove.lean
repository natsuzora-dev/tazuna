import Engine.Run
import Tazuna.Smt.Script
import Tazuna.Smt.State

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
ensures of a command or query; or that a ref field of an entity never names a missing record.
-/
inductive Property where
  | invariant (definition : Spec.Ref) (name : String)
  | ensures (definition : Spec.Ref) (name : String)
  | danglingRef (definition : Spec.Ref) (field : String)
deriving BEq, Repr, Inhabited

derive_wire Property tag "kind"

def Property.definition : Property → Spec.Ref
  | .invariant d _ | .ensures d _ | .danglingRef d _ => d

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

derive_wire ProveResult serialize_only

/-- The milliseconds that Z3 may take on each query. -/
def proveTimeout : Nat := 10000

/-- Where an invariant is checked: on each record of an entity, on a single entity's record, or on all records. -/
inductive Holder where
  | keyed (entity : String)
  | single (entity : String)
  | service

structure Checked where
  ref : Property
  holder : Holder
  condition : Ir.Condition

/-- The invariants of `st` that prove checks, and those of its charts, which it leaves undecided. -/
def invariantsOf (st : Service) (p : Ir.Program) : List Checked × List Property :=
  let entity := st.entities.flatMap fun e =>
    (Smt.invariantsOf st p e).map fun c =>
      { ref := .invariant (st.ref e) c.name,
        holder := if st.singles.contains e then .single e else .keyed e, condition := c }
  let service := (serviceInvariantsOf st p).map fun c =>
    { ref := .invariant (st.ref st.service) c.name, holder := .service, condition := c }
  let charts := p.chart.filter (fun f => f.chart.service == st.service && f.site == .invariants) |>.flatMap fun f =>
    f.functions.map fun c => Property.invariant f.chart c.name
  (entity ++ service, charts)

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

/-- The time of a state, `clock`, a safe integer as every time is. -/
def clockFacts : Facts :=
  { vars := [("clock", .int)],
    asserts := [.le (intLit (-safeInteger)) (.var "clock" .int), .le (.var "clock" .int) (intLit safeInteger)] }

def clockT : Term := .var "clock" .int

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
  charts : List Property
  /-- Why the service has no induction, such as missing bounds. -/
  blocked : Option String

def inductionOf (j : Spec.Structure) (service : String) : IO Induction := do
  let st ← Service.ofStructure j service
  let p := j.program
  let (checked, charts) := invariantsOf st p
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
         checked, charts, blocked }

/-- A query of the induction: whether the initial records fail an invariant, a step can leave the encoding, a step can
fail a property, or a query's answer can fail one of its ensures. -/
inductive Asked where
  | base (property : Property)
  | gap (command : String)
  | fails (command : String) (property : Property)
  | answer (query : String) (property : Property)

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
The queries of an induction, in order: the base case of each encoded invariant, then each command's gap query and one
per property it can fail, then one per ensures of each query.
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
  x.answers.flatMap fun (q, answered) =>
    match answered with
    | .error _ => []
    | .ok a => (conditionsOf p.queryEnsures (x.st.ref q)).filterMap fun c => (a.ensuresFails x.pre c).toOption.map
      fun fails => (.answer q (.ensures (x.st.ref q) c.name),
        { vars := x.facts.vars ++ a.facts.vars, asserts := x.facts.asserts ++ [x.holds] ++ a.facts.asserts ++ [a.answered, fails] })

/-- The own spec services of the structure, in order. -/
def specServices (j : Spec.Structure) : List String := (j.services.filter (!·.external)).map (·.name)

def proveQueriesOf (j : Spec.Structure) : IO (List String) := do
  let inductions ← (specServices j).mapM (inductionOf j)
  pure (inductions.flatMap fun x => x.queries.map fun (_, q) => q.script proveTimeout)

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

/-- The verdict of a solver's answer, from the replay of its model when it is sat. -/
def verdictOf (answer : Smt.Answer) (exact : Bool) (replay : Model → IO (Except String Counterexample)) (what : String) :
    IO (Option Verdict) := do
  match answer with
  | .unsat => pure none
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
  let charts := x.charts.map (result · (.undecided "prove does not encode machine and screen states yet"))
  let ensures := x.st.commands.flatMap fun c => (conditionsOf p.ensures (x.st.ref c)).map fun e =>
    (c, Property.ensures (x.st.ref c) e.name)
  let queryEnsures := x.answers.flatMap fun (q, _) => (conditionsOf p.queryEnsures (x.st.ref q)).map fun e =>
    (q, e, Property.ensures (x.st.ref q) e.name)
  let dangling := (ownRefs x.st).map fun (e, field, _) => Property.danglingRef (x.st.ref e) field
  if let some why := x.blocked then
    return ((x.checked.map (·.ref)) ++ ensures.map (·.2) ++ queryEnsures.map (·.2.2) ++ dangling).map
      (result · (.undecided why)) ++ charts
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
        if let some v ← verdictOf a (x.facts.exact && step.facts.exact) (replayStep x fs · c step prop) s!"after {c}" then
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
      if let some v ← verdictOf a initFacts.exact replay "of the initial records" then return result ch.ref v
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
        if let some v ← verdictOf ans false (replayAnswer x fs · q a e.name) s!"of {q}" then return result prop v
      return result prop .proved
    | none => return result prop (.undecided s!"the query {q} has no encoding")
  let refs ← dangling.mapM fun prop => do pure (result prop (← afterSteps prop x.st.commands))
  pure (invariants ++ commandEnsures ++ answered ++ refs ++ charts)

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
