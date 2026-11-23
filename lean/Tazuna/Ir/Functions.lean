import Tazuna.Ir.Eval
import Tazuna.Data.Parse
import Tazuna.Explore.Instrument

/-!
The Functions that the engine runs a spec with (Program.toFunctions). The arguments of each spec function are those
that the TS DSL passes it for the same question.
-/

namespace Tazuna.Ir

open Tazuna.Data Tazuna.Service Tazuna.Explore

/-- The arguments of a spec function that receives only `passed`; any other name is `undefined`. -/
def argsOf (passed : List (Arg × Val)) (a : Arg) : Val := (passed.lookup a).getD .undef

/-- An instant as a spec function's `now` holds it: milliseconds since the epoch. -/
def instant (t : Time) : Val := .json (.num ⟨t, 0⟩)

/--
The event list that a command's ensures reads on a request's results: each event as `{ kind: "emit", payload }`. TS
also passes the event's definition, which IR cannot read.
-/
def emitted (events : List Emit) : Value :=
  .arr (events.map fun e => .obj [("kind", .str "emit"), ("payload", e.payload)])

/--
The arguments of a function of a machine or screen, as TS builds them for `scope`: the context with the copy's fields
over the owner's, whether each state of the chart is active, the shown slots, the held parameters, the copy's key, and
the cause `extra`.
-/
def scopeArgs (st : Service) (scope : Scope) (extra : Extra) : Arg → Val :=
  let chart := st.chart? scope.machine
  let copiedStates := match chart, scope.id.map? with
    | some c, some map => c.tree.descendants map
    | _, _ => []
  let context := match scope.copy with
    | some c => scope.context.merge c.context
    | none => scope.context
  let copiedFields := match scope.copy with
    | some { context := .obj fields, .. } => fields.map (·.1)
    | _ => []
  let active := .obj (((chart.map (·.states)).getD []).map fun s => (s.spec.name, .bool (s.spec.name ∈ scope.active)))
  let holder : Holder := if scope.copy.isSome then .copy else .owner
  argsOf ([(.context, .tracked (.context copiedFields) context), (.input, .json scope.input),
      (.shown, .tracked .shown (.obj scope.shown)), (.active, .tracked (.active copiedStates) active),
      (.held, .tracked (.held holder scope.state) scope.held), (.now, instant scope.now)] ++
    (scope.copy.map fun c => (Arg.key, Val.json c.key)).toList ++
    match extra with
    | .none => []
    | .payload v => [(.payload, .json v)]
    | .output v => [(.output, .json v)]
    | .rejection r => [(.rejection, .json (.obj [("kind", ToValue.toValue r.kind)]))])

/-- The site of the input of `activity` written in `state`. -/
def inputSite (state : String) : Activity → Site
  | .calls key _ => .input state "calls" key
  | .sends key _ => .input state "sends" key
  | .shows key _ => .input state "shows" key
  | .opens key _ _ => .input state "opens" key

def Transition.ref (t : Transition) : Spec.TransitionRef := { state := t.source, trigger := t.trigger, index := t.index }

/-- The value of `body` in `env`, as TS's encoding writes it. -/
def valueIn (env : Env) (body : Expr) : EvalM Value := do answerOf env (← eval env [] body)

/-- The values of an array that a function made, such as the offers' payloads or a map state's items. -/
def valuesOf (env : Env) (v : Val) : EvalM (List Value) := do
  match ← answerOf env v with
  | .arr vs => pure vs
  | _ => thrown

def valuesIn (env : Env) (body : Expr) : EvalM (List Value) := do valuesOf env (← eval env [] body)

/-- The field names of the objects of `schema`, in its order. -/
def propertiesOf (st : Service) (schema : Schema) : List String :=
  match (st.schemaOf schema).bind (·.field? "properties") with
  | some (.obj properties) => properties.map (·.1)
  | _ => []

/-- The field names of an entity of the service, in its schema's order. -/
def fieldsOf (st : Service) (entity : String) : List String := propertiesOf st (.record (st.ref entity))

/-- The site of the assign of `a`. -/
def assignSite : Assignment → Site
  | .transition t => .transitionAssign t.ref
  | .entry state => .entryAssign state
  | .exit state => .exitAssign state

/--
`base` with `assigned` spread over it, as JS `{ ...base, ...assigned }` builds it: a field of both keeps its place with
the assigned value, and the other assigned fields follow in order.
-/
def spread (base : Value) (assigned : List (String × Val)) : Val :=
  let own := match base with
    | .obj fields => fields.map fun (name, v) => (name, (assigned.lookup name).getD (.json v))
    | _ => []
  .obj (own ++ assigned.filter fun (name, _) => !(own.any (·.1 == name)))

/-- `x` in `env` with `bound`, which TS computes from every binds value before a requires or guard reads it. -/
def withBound {α : Type} (env : Env) (binds : List Condition) (x : Env → EvalM α) : EvalM α := do
  let values ← bound env binds
  x { env with args := fun a => if a == .bound then values else env.args a }

/-- The stop at a question that the program and the schemas leave unanswered. -/
def unanswered {α : Type} (question : String) : IO α :=
  throw (IO.userError s!"the spec has no IR or schema for {question}")

/-- The answer of a parse, which throws only in a codec, and a check rejects codecs (Restricted.schema). -/
def thrownBy {α : Type} (schema : Schema) : ParseM α → Except Issue α
  | .ok a => .ok a
  | .error () => .error (.thrown (some schema))

/--
The functions of the running service `st` whose program is `p`: each spec function evaluated from its IR, which hands
what the evaluation read to `read`, and each structural question (parse, unordered, comparable, defaults) answered from
`st`'s JSON Schemas by Data.Parse. A question that neither answers is a bug of the converter or of check, which reports
every function outside the IR.
-/
def Program.toFunctions (p : Program) (st : Service) (read : Trace → IO Unit) : Functions IO :=
  let evaluated {ε α : Type} (question : String) : Option (Except ε α × Trace) → IO (Except ε α)
    | some (answer, trace) => do read trace; pure answer
    | none => unanswered question
  let json (schema : Schema) : Option Value := (st.schemaOf schema).map rootSchema |>.filter supported
  let all (gs : List Conditions) (definition : Spec.Ref) : Option (List Condition) :=
    (gs.find? (·.definition == definition)).map (·.conditions)
  let named (gs : List Conditions) (definition : Spec.Ref) (name : String) : Option Condition :=
    (all gs definition).bind (·.find? (·.name == name))
  let binds (gs : List Conditions) (definition : Spec.Ref) : List Condition := (all gs definition).getD []
  let site (chart : String) (s : Site) : Option (List Condition) :=
    (p.chart.find? fun f => f.chart == st.ref chart && f.site == s).map (·.functions)
  let one (chart : String) (s : Site) : Option Expr := (site chart s).bind (·.head?.map (·.body))
  let chartEnv (scope : Scope) (records : Records) (extra : Extra := .none) : Env :=
    { fields := fieldsOf st, args := scopeArgs st scope extra, records }
  let holds (env : Env) (c : Condition) : EvalM Bool := do pure (truthy (← eval env [] c.body))
  let nonNull (env : Env) (c : Condition) : EvalM Bool := do
    match ← eval env [] c.body with
    | .undef | .json .null => pure false
    | _ => pure true
  { parse := fun schema value => do
      let some parsed := (st.schemaOf schema).bind (Data.parse · value) | unanswered s!"parse of {repr schema}"
      pure ((thrownBy schema parsed).map (·.toOption))
    unordered := fun schema value => do
      let some j := json schema | unanswered s!"unordered of {repr schema}"
      pure (thrownBy schema (unorderedBy j value))
    comparable := fun query answer => do
      let output := Schema.output (st.ref query)
      let j := (st.schemaOf output).map rootSchema
      if !(j.all supported) then unanswered s!"comparable of {query}"
      pure (thrownBy output (comparableText j (ToValue.toValue answer)))
    defaults := fun schema => do
      let some j := json schema | unanswered s!"defaults of {repr schema}"
      pure (.ok (defaultsOf j))
    inputRequirement := fun target c input => evaluated "inputRequirement" <|
      (named p.inputRequirement target c).map fun cond =>
        (holds { fields := fieldsOf st, args := argsOf [(.input, .json input)] } cond).run'
    resultEnsures := fun target c input output events => evaluated "resultEnsures" <|
      (named p.resultEnsures target c).map fun cond =>
        let read := if (st.«structure».schemaOf (.output target)).isSome then output else none
        let list := match st.«structure».body? target with
          | some (.command _) => some (emitted events)
          | _ => none
        let args := argsOf [(.input, .json input), (.output, .ofOption read), (.events, .ofOption list)]
        let (answer, trace) := ((fun h => if h then Ensured.holds else .fails) <$> holds { args, hidden := true } cond).run'
        (if trace.readHidden then .ok .readsRecords else answer, trace)
    invariant := fun entity record now => evaluated "invariant" <|
      (all p.invariant (st.ref entity)).map fun cs =>
        (firstFailing { fields := fieldsOf st, args := argsOf [(.record, .json record), (.now, instant now)] } cs).run'
    closeEnsures := fun screen input output => evaluated "closeEnsures" <|
      (all p.closeEnsures (st.ref screen)).map fun cs =>
        (firstFailing { fields := fieldsOf st, args := argsOf [(.input, .json input), (.output, .json output)] } cs).run'
    binding := fun name b input records now => evaluated "binding" <|
      (named p.binding (st.ref name) b).map fun c =>
        (nonNull { fields := fieldsOf st, args := argsOf [(.input, .json input), (.now, instant now)], records } c).run'
    requirement := fun name c input records now => evaluated "requirement" <|
      (named p.requirement (st.ref name) c).map fun cond =>
        let env := { fields := fieldsOf st, args := argsOf [(.input, .json input), (.now, instant now)], records }
        (withBound env (binds p.binding (st.ref name)) (holds · cond)).run'
    ensures := fun name input before after _ => evaluated "ensures" <|
      (all p.ensures (st.ref name)).map fun cs =>
        let args := argsOf [(.input, .json input)]
        -- As TS's firstFailing, which builds the arguments only when there is a condition.
        let checked : EvalM (Option String) :=
          if cs.isEmpty then pure none
          else withBound { fields := fieldsOf st, args, records := before } (binds p.binding (st.ref name)) fun env =>
            firstFailing { env with records := after } cs
        checked.run'
    queryEnsures := fun name input output records => evaluated "queryEnsures" <|
      (all p.queryEnsures (st.ref name)).map fun cs =>
        (firstFailing { fields := fieldsOf st, args := argsOf [(.input, .json input), (.output, .json output)], records } cs).run'
    serviceInvariant := fun records now => evaluated "serviceInvariant" <|
      (all p.serviceInvariant (st.ref st.service)).map fun cs =>
        let (answer, trace) := (firstFailing { fields := fieldsOf st, args := argsOf [(.now, instant now)], records } cs).run'
        let answer := answer.mapError fun
          | .thrown schema => schema
          | _ => none
        (answer, trace)
    automationBinding := fun name b payload records now => evaluated "automationBinding" <|
      (named p.automationBinding (st.ref name) b).map fun c =>
        (nonNull { fields := fieldsOf st, args := argsOf [(.payload, .json payload), (.now, instant now)], records } c).run'
    automationGuard := fun name c payload records now => evaluated "automationGuard" <|
      (named p.automationGuard (st.ref name) c).map fun cond =>
        let env := { fields := fieldsOf st, args := argsOf [(.payload, .json payload), (.now, instant now)], records }
        (withBound env (binds p.automationBinding (st.ref name)) (holds · cond)).run'
    resolve := fun name input records now => evaluated "resolve" <|
      (p.resolve.find? (·.definition == st.ref name)).map fun f =>
        let env := { fields := fieldsOf st, args := argsOf [(.input, .json input), (.now, instant now)], records }
        (valueIn env f.body).run'
    decide := fun name input records now => evaluated "decide" <|
      (p.decide.find? (·.definition == st.ref name)).map fun f =>
        let env := { fields := fieldsOf st, args := argsOf [(.input, .json input), (.now, instant now)], records }
        let emitted (env : Env) : Val → EvalM Emit
          | .emit event payload => do pure { event, payload := ← answerOf env payload }
          | _ => thrown
        let decided : EvalM (List (List Emit)) := withBound env (binds p.binding (st.ref name)) fun env => do
          match ← eval env [] f.body with
          | .list items => items.mapM fun
            | .list group => group.mapM (emitted env)
            | e => do pure [← emitted env e]
          | _ => thrown
        decided.run'
    react := fun name payload records now keys => evaluated "react" <|
      (p.react.find? (·.definition == st.ref name)).map fun f =>
        let env := { fields := fieldsOf st, args := argsOf [(.payload, .json payload), (.now, instant now)], records, keys }
        let given : EvalM (Value × List String) := withBound env (binds p.automationBinding (st.ref name)) fun env => do
          pure (← valueIn env f.body, (← get).created)
        given.run'
    chartInvariant := fun scope records => evaluated "chartInvariant" <|
      (site scope.machine .invariants).map fun cs => (firstFailing (chartEnv scope records) cs).run'
    guard := fun scope records t c extra => evaluated "guard" <|
      ((site scope.machine (.guards t.ref)).bind (·.find? (·.name == c))).map fun cond =>
        (holds (chartEnv scope records extra) cond).run'
    deadlineAt := fun scope records name => evaluated "deadlineAt" <|
      (scope.state.bind fun s => one scope.machine (.deadline s name)).map fun body =>
        let time : EvalM (Option Time) := do
          pure ((integer? (← eval (chartEnv scope records) [] body)).filter isSafeInteger)
        time.run'
    items := fun scope records => evaluated "items" <|
      (scope.state.bind fun s => one scope.machine (.items s)).map fun body =>
        (valuesIn (chartEnv scope records) body).run'
    offers := fun scope records control => evaluated "offers" <|
      (one scope.machine (.offers scope.state control)).map fun body =>
        (valuesIn (chartEnv scope records) body).run'
    showInput := fun scope records a => evaluated "showInput" <|
      (scope.state.bind fun s => one scope.machine (inputSite s a)).map fun body =>
        (valueIn (chartEnv scope records) body).run'
    input := fun scope records a keys => evaluated "input" <|
      (scope.state.bind fun s => one scope.machine (inputSite s a)).map fun body =>
        let given : EvalM (Value × List String) := do
          pure (← valueIn { chartEnv scope records with keys } body, (← get).created)
        given.run'
    held := fun scope records n edge extra =>
      let entry : Entry := match edge with
        | .transition t => .transition t.ref
        | .initial parent => .initial parent
      evaluated "held" <| (site scope.machine (.held entry n)).map fun params =>
        let env := chartEnv scope records extra
        let values : EvalM Value := do
          answerOf env (.obj (← params.mapM fun c => do pure (c.name, ← eval env [] c.body)))
        values.run'
    assign := fun scope records a extra keys => evaluated "assign" <|
      (site scope.machine (assignSite a)).map fun fields =>
        let env := { chartEnv scope records extra with keys }
        let copyFields := match scope.id.map? with
          | some map => propertiesOf st (.mapContext (st.ref scope.machine) map)
          | none => []
        let assigned : EvalM (Value × Option Value × List String) := do
          let values ← fields.mapM fun c => do pure (c.name, ← eval env [] c.body)
          let (own, outer) := values.partition (·.1 ∈ copyFields)
          let copy ← match scope.copy with
            | some c => some <$> answerOf env (spread c.context own)
            | none => pure none
          let context ← answerOf env (spread scope.context outer)
          touch fun a => { a with assigned := a.assigned ++ own.map (Holder.copy, ·.1) ++ outer.map (Holder.owner, ·.1) }
          pure (context, copy, (← get).created)
        assigned.run'
    initialContext := fun machine input => evaluated "initialContext" <|
      (one machine .initialContext).map fun body =>
        (valueIn { fields := fieldsOf st, args := argsOf [(.input, .json input)] } body).run'
    close := fun scope records => evaluated "close" <|
      (one scope.machine .close).map fun body => (valueIn (chartEnv scope records) body).run' }

/-- What the latest evaluation read: the record parts and the chart values, which Instrument collects. -/
structure LastRead where
  parts : List RecordPart := []
  access : Access := {}

/-- The functions of the running service `st`: Program.toFunctions of its program, which leaves what each read in `last`. -/
def functionsOf (st : Service) (last : IO.Ref LastRead) : Functions IO :=
  st.structure.program.toFunctions st fun trace => last.set { parts := trace.parts, access := trace.access }

/-- What Instrument reads besides Functions, from `last`. -/
def instrumentOf (last : IO.Ref LastRead) : InstrumentFunctions IO :=
  { lastReads := do pure (← last.get).parts, lastAccess := do pure (← last.get).access }

end Tazuna.Ir
