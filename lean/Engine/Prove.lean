import Engine.Run
import Tazuna.Smt.Script
import Tazuna.Smt.State

/-!
prove: the base case and the inductive step of each invariant of each spec service, within the service's bounds. The
engine answers in two requests, since TS runs Z3: `proveQueries` gives the SMT-LIB scripts, and `prove` reads Z3's
answers to them, replays each counterexample in the semantics, and gives one result per invariant.
-/

namespace Tazuna.Engine

open Tazuna.Data Tazuna.Service Tazuna.Smt

/-- An invariant: a condition of an entity's records, of a machine or screen, or of the service, which names itself. -/
structure InvariantRef where
  definition : Spec.Ref
  name : String
deriving Repr, Inhabited

derive_wire InvariantRef

/-- A state within the bounds where every invariant holds, and a command after which the invariant fails. -/
structure Counterexample where
  /-- The records, by entity: a keyed entity's as a list, a single entity's as its record. -/
  given : Value
  /-- The command and its input and time, none for the initial state. -/
  command : Option String
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

/-- What prove found of one invariant, within the bound of creating at most `creates` records of each keyed entity. -/
structure ProveResult where
  service : String
  invariant : InvariantRef
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
  ref : InvariantRef
  holder : Holder
  condition : Ir.Condition

/-- The invariants of `st` that prove checks, and those of its charts, which it leaves undecided. -/
def invariantsOf (st : Service) (p : Ir.Program) : List Checked × List InvariantRef :=
  let entity := st.entities.flatMap fun e =>
    (Smt.invariantsOf st p e).map fun c =>
      { ref := { definition := st.ref e, name := c.name },
        holder := if st.singles.contains e then .single e else .keyed e, condition := c }
  let service := (serviceInvariantsOf st p).map fun c =>
    { ref := { definition := st.ref st.service, name := c.name }, holder := .service, condition := c }
  let charts := p.chart.filter (fun f => f.chart.service == st.service && f.site == .invariants) |>.flatMap fun f =>
    f.functions.map fun c => ({ definition := f.chart, name := c.name } : InvariantRef)
  (entity ++ service, charts)

/-- The term that holds when `c` fails, or throws, on some record of `r` that it is checked on. -/
def failsOn (r : SRecords) (c : Checked) : Except String Term := do
  let fails (env : SEnv) : Except String Term := do
    let (v, e) ← seval env [] c.condition.body
    pure (Term.or e (.not v.truthy))
  match c.holder with
  | .keyed e => do
    let terms ← (r.slotsOf e).mapM fun s => do pure (Term.and s.live (← fails (recordEnv s.fields)))
    pure (disj terms)
  | .single e => fails (recordEnv ((r.singles.lookup e).getD []))
  | .service => fails { records := r }

/-- One service's symbolic induction: its state, and the step of each command, or why the step has no encoding. -/
structure Induction where
  st : Service
  creates : List (String × Nat)
  pre : SRecords
  facts : Facts
  /-- That every encoded invariant holds of `pre`. -/
  holds : Term
  steps : List (String × Except String Step)
  checked : List Checked
  charts : List InvariantRef
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
  let holds := conj ((checked.map fun c => (do
      match c.holder with
      | .keyed e => do
        let terms ← (pre.slotsOf e).mapM fun s => do pure (Term.or (.not s.live) (← allHold (recordEnv s.fields) [c.condition]))
        pure (conj terms)
      | .single e => allHold (recordEnv ((pre.singles.lookup e).getD [])) [c.condition]
      | .service => allHold { records := pre } [c.condition] : Except String Term)).filterMap (·.toOption))
  let blocked := if bounds.isNone && !keyed.isEmpty then some "the service has no bounds()" else none
  pure { st, creates, pre, facts := pre.facts st "pre", holds,
         steps := st.commands.map fun c => (c, stepOf st p pre used c), checked, charts, blocked }

/-- A query of the induction: whether a step can leave the encoding, or fail an invariant. -/
inductive Asked where
  | gap (command : String)
  | fails (command : String) (invariant : InvariantRef)

def Induction.query (x : Induction) (step : Step) (goal : Term) : Query :=
  { vars := x.facts.vars ++ step.facts.vars,
    asserts := x.facts.asserts ++ [x.holds] ++ step.facts.asserts ++ [step.accepted, .not step.beyond, goal] }

/-- The queries of an induction, in order: each command's gap query, then one per encoded invariant. -/
def Induction.queries (x : Induction) : List (Asked × Query) :=
  if x.blocked.isSome then [] else
  x.steps.flatMap fun (c, step) =>
    match step with
    | .error _ => []
    | .ok step =>
      (Asked.gap c, x.query step step.gap) ::
        x.checked.filterMap fun ch => match failsOn step.post ch with
          | .ok fails => some (.fails c ch.ref, x.query step (.and (.not step.gap) fails))
          | .error _ => none

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

/-- Whether `c` fails on the record `value`, as the semantics evaluates it. -/
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

/-- The result of the replay of a model of a fails query: the counterexample, or why the model is no case of it. -/
def replayFails (x : Induction) (fs : Functions IO) (M : Model) (command : String) (step : Step) (c : Checked) :
    IO (Except String Counterexample) := do
  let records := x.pre.conc M
  let input := Value.obj (present M step.input)
  let now := (M "now").toInt
  let pre := records.filter fun r => (x.st.entities.contains r.entity)
  let env (value : Value) : Ir.Env := { fields := Ir.fieldsOf x.st, args := Ir.argsOf [(.record, .json value)] }
  let given := givenOf x.st records
  -- The state must be one where every invariant holds, as the induction assumes.
  let broken := x.checked.find? fun ch => match ch.holder with
    | .keyed e | .single e => pre.any fun r => r.entity == e && failsConcrete (env r.value) ch.condition
    | .service => failsConcrete { fields := Ir.fieldsOf x.st, records := pre } ch.condition
  if let some b := broken then return .error s!"the case's state fails {b.ref.name}, which the induction assumes"
  let fits (r : Row) : Bool := match Data.parse (entitySchema x.st r.entity) r.value with
    | some (.ok (.ok _)) => true
    | _ => false
  if let some r := pre.find? (!fits ·) then return .error s!"the case's record of {r.entity} is outside its schema"
  match ← writtenBy x.st fs pre now command input with
  | none => return .error "the semantics rejects the case's command"
  | some (written, faults) =>
    let failing := match c.holder with
      | .keyed e | .single e => written.any fun r => r.entity == e && failsConcrete (env r.value) c.condition
      | .service => failsConcrete { fields := Ir.fieldsOf x.st, records := written } c.condition
    if !failing || !faults.any (reports x.st c command) then
      return .error "the semantics keeps the invariant after the case's command"
    return .ok { given, command := some command, input := some input, now := some now,
                 violations := faults.map (·.toViolation) }

/-- The base case: whether `c` holds of the initial records, the single entities' records of their schema defaults. -/
def baseCase (x : Induction) : Option Counterexample :=
  let records : Records := x.st.singles.map fun e =>
    { entity := e, key := none, value := defaultsOf (entitySchema x.st e) }
  let fails (c : Checked) : Bool := match c.holder with
    | .keyed _ => false
    | .single e => records.any fun r => r.entity == e &&
        failsConcrete { fields := Ir.fieldsOf x.st, args := Ir.argsOf [(.record, .json r.value)] } c.condition
    | .service => failsConcrete { fields := Ir.fieldsOf x.st, records } c.condition
  let failing := x.checked.filter fails
  if failing.isEmpty then none
  else some { given := givenOf x.st records, command := none, input := none, now := none, violations := [] }

def Induction.results (x : Induction) (answers : List (Asked × Smt.Answer)) : IO (List ProveResult) := do
  let fs := x.st.structure.program.toFunctions x.st fun _ => pure ()
  let result (ref : InvariantRef) (verdict : Verdict) : ProveResult :=
    { service := x.st.service, invariant := ref, creates := x.creates, verdict }
  let charts := x.charts.map (result · (.undecided "prove does not encode machine and screen states yet"))
  if let some why := x.blocked then
    return (x.checked.map (result ·.ref (.undecided why))) ++ charts
  let unencoded := x.steps.findSome? fun (c, step) => match step with
    | .error why => some s!"the command {c} has no encoding: {why}"
    | .ok _ => none
  let gap := answers.findSome? fun
    | (.gap c, .sat _) => some s!"the command {c} can write a value that the encoding does not hold, such as a record outside its schema"
    | (.gap c, .unknown why) => some s!"whether the command {c} stays within the encoding is unknown: {why}"
    | _ => none
  let entries ← x.checked.mapM fun ch => do
    if let some case := baseCase { x with checked := [ch] } then
      return result ch.ref (.counterexample case)
    let unencodable := x.steps.findSome? fun (c, step) => match step with
      | .ok s => match failsOn s.post ch with
        | .error why => some s!"the invariant has no encoding: {why} (in {c})"
        | .ok _ => none
      | .error _ => none
    if let some why := unencoded <|> unencodable then return result ch.ref (.undecided why)
    if let some why := gap then return result ch.ref (.undecided why)
    let mine := answers.filterMap fun
      | (.fails c ref, a) => if ref.definition == ch.ref.definition && ref.name == ch.ref.name then some (c, a) else none
      | _ => none
    for (c, a) in mine do
      match a with
      | .sat values =>
        let some (.ok step) := x.steps.lookup c | continue
        match ← replayFails x fs (Smt.Answer.model values) c step ch with
        | .ok case => return result ch.ref (.counterexample case)
        | .error why =>
          if x.facts.exact && step.facts.exact then
            throw (IO.userError s!"prove's encoding disagrees with the semantics on {ch.ref.name} after {c}: {why}")
          return result ch.ref (.undecided s!"the solver's case after {c} is outside what the encoding states exactly: {why}")
      | .unknown why => return result ch.ref (.undecided s!"after {c}: {why}")
      | .unsat => pure ()
    return result ch.ref .proved
  pure (entries ++ charts)

/-- The results of each invariant of each spec service, from Z3's answers to proveQueriesOf's scripts, in order. -/
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
