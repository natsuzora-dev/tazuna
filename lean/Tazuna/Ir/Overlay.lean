import Tazuna.Ir.Eval

/-!
The Functions of the migration to IR: a callback evaluates in Lean when the program holds IR for it, and otherwise
answers as the functions beneath do. The arguments are those that TS passes the spec function for the same question.
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
What a caller does with an answer that Lean evaluated: `answered callback (answer, trace) beneath` gives the answer,
where `trace` is what the evaluation read and `beneath` asks the functions beneath the same question.
-/
abbrev Answered (m : Type → Type) :=
  {ε α : Type} → [BEq ε] → [BEq α] → [Repr ε] → [Repr α] →
    String → Except ε α × Trace → m (Except ε α) → m (Except ε α)

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

/-- `fs` with each callback that `p` holds IR for evaluated in Lean, handed to `answered`. -/
def Program.overlay {m : Type → Type} [Monad m] (p : Program) (st : Service) (answered : Answered m)
    (fs : Functions m) : Functions m :=
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
  { fs with
    inputRequirement := fun target c input =>
      match named p.inputRequirement target c with
      | some cond => answered "inputRequirement" (holds { fields := fieldsOf st, args := argsOf [(.input, .json input)] } cond).run'
          (fs.inputRequirement target c input)
      | none => fs.inputRequirement target c input
    resultEnsures := fun target c input output events =>
      match named p.resultEnsures target c with
      | none => fs.resultEnsures target c input output events
      | some cond =>
        let read := if (st.«structure».schemaOf (.output target)).isSome then output else none
        let list := match st.«structure».body? target with
          | some (.command _) => some (emitted events)
          | _ => none
        let args := argsOf [(.input, .json input), (.output, .ofOption read), (.events, .ofOption list)]
        let (answer, trace) := ((fun h => if h then Ensured.holds else .fails) <$> holds { args, hidden := true } cond).run'
        answered "resultEnsures" (if trace.readHidden then .ok .readsRecords else answer, trace)
          (fs.resultEnsures target c input output events)
    invariant := fun entity record =>
      match all p.invariant (st.ref entity) with
      | none => fs.invariant entity record
      | some cs => answered "invariant" (firstFailing { fields := fieldsOf st, args := argsOf [(.record, .json record)] } cs).run'
          (fs.invariant entity record)
    closeEnsures := fun screen input output =>
      match all p.closeEnsures (st.ref screen) with
      | none => fs.closeEnsures screen input output
      | some cs => answered "closeEnsures"
          (firstFailing { fields := fieldsOf st, args := argsOf [(.input, .json input), (.output, .json output)] } cs).run'
          (fs.closeEnsures screen input output)
    binding := fun name b input records now =>
      match named p.binding (st.ref name) b with
      | none => fs.binding name b input records now
      | some c => answered "binding"
          (nonNull { fields := fieldsOf st, args := argsOf [(.input, .json input), (.now, instant now)], records } c).run'
          (fs.binding name b input records now)
    requirement := fun name c input records now =>
      match named p.requirement (st.ref name) c with
      | none => fs.requirement name c input records now
      | some cond =>
        let env := { fields := fieldsOf st, args := argsOf [(.input, .json input), (.now, instant now)], records }
        answered "requirement" (withBound env (binds p.binding (st.ref name)) (holds · cond)).run'
          (fs.requirement name c input records now)
    ensures := fun name input before after now =>
      match all p.ensures (st.ref name) with
      | none => fs.ensures name input before after now
      | some cs =>
        let args := argsOf [(.input, .json input)]
        -- As TS's firstFailing, which builds the arguments only when there is a condition.
        let checked : EvalM (Option String) :=
          if cs.isEmpty then pure none
          else withBound { fields := fieldsOf st, args, records := before } (binds p.binding (st.ref name)) fun env =>
            firstFailing { env with records := after } cs
        answered "ensures" checked.run' (fs.ensures name input before after now)
    queryEnsures := fun name input output records =>
      match all p.queryEnsures (st.ref name) with
      | none => fs.queryEnsures name input output records
      | some cs => answered "queryEnsures"
          (firstFailing { fields := fieldsOf st, args := argsOf [(.input, .json input), (.output, .json output)], records } cs).run'
          (fs.queryEnsures name input output records)
    serviceInvariant := fun records =>
      match all p.serviceInvariant (st.ref st.service) with
      | none => fs.serviceInvariant records
      | some cs =>
        let (answer, trace) := (firstFailing { fields := fieldsOf st, records } cs).run'
        let answer := answer.mapError fun
          | .thrown schema => schema
          | _ => none
        answered "serviceInvariant" (answer, trace) (fs.serviceInvariant records)
    automationBinding := fun name b payload records now =>
      match named p.automationBinding (st.ref name) b with
      | none => fs.automationBinding name b payload records now
      | some c => answered "automationBinding"
          (nonNull { fields := fieldsOf st, args := argsOf [(.payload, .json payload), (.now, instant now)], records } c).run'
          (fs.automationBinding name b payload records now)
    automationGuard := fun name c payload records now =>
      match named p.automationGuard (st.ref name) c with
      | none => fs.automationGuard name c payload records now
      | some cond =>
        let env := { fields := fieldsOf st, args := argsOf [(.payload, .json payload), (.now, instant now)], records }
        answered "automationGuard" (withBound env (binds p.automationBinding (st.ref name)) (holds · cond)).run'
          (fs.automationGuard name c payload records now)
    resolve := fun name input records now =>
      match p.resolve.find? (·.definition == st.ref name) with
      | none => fs.resolve name input records now
      | some f =>
        let env := { fields := fieldsOf st, args := argsOf [(.input, .json input), (.now, instant now)], records }
        answered "resolve" (valueIn env f.body).run' (fs.resolve name input records now)
    decide := fun name input records now =>
      match p.decide.find? (·.definition == st.ref name) with
      | none => fs.decide name input records now
      | some f =>
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
        answered "decide" decided.run' (fs.decide name input records now)
    react := fun name payload records now keys =>
      match p.react.find? (·.definition == st.ref name) with
      | none => fs.react name payload records now keys
      | some f =>
        let env := { fields := fieldsOf st, args := argsOf [(.payload, .json payload), (.now, instant now)], records, keys }
        let given : EvalM (Value × List String) := withBound env (binds p.automationBinding (st.ref name)) fun env => do
          pure (← valueIn env f.body, (← get).created)
        answered "react" given.run' (fs.react name payload records now keys)
    chartInvariant := fun scope records =>
      match site scope.machine .invariants with
      | none => fs.chartInvariant scope records
      | some cs => answered "chartInvariant" (firstFailing (chartEnv scope records) cs).run'
          (fs.chartInvariant scope records)
    guard := fun scope records t c extra =>
      match (site scope.machine (.guards t.ref)).bind (·.find? (·.name == c)) with
      | none => fs.guard scope records t c extra
      | some cond => answered "guard" (holds (chartEnv scope records extra) cond).run'
          (fs.guard scope records t c extra)
    deadlineAt := fun scope records name =>
      match scope.state.bind fun s => one scope.machine (.deadline s name) with
      | none => fs.deadlineAt scope records name
      | some body =>
        let time : EvalM (Option Time) := do
          pure ((integer? (← eval (chartEnv scope records) [] body)).filter isSafeInteger)
        answered "deadlineAt" time.run' (fs.deadlineAt scope records name)
    items := fun scope records =>
      match scope.state.bind fun s => one scope.machine (.items s) with
      | none => fs.items scope records
      | some body => answered "items" (valuesIn (chartEnv scope records) body).run'
          (fs.items scope records)
    offers := fun scope records control =>
      match one scope.machine (.offers scope.state control) with
      | none => fs.offers scope records control
      | some body => answered "offers" (valuesIn (chartEnv scope records) body).run'
          (fs.offers scope records control)
    showInput := fun scope records a =>
      match scope.state.bind fun s => one scope.machine (inputSite s a) with
      | none => fs.showInput scope records a
      | some body => answered "showInput" (valueIn (chartEnv scope records) body).run'
          (fs.showInput scope records a)
    input := fun scope records a keys =>
      match scope.state.bind fun s => one scope.machine (inputSite s a) with
      | none => fs.input scope records a keys
      | some body =>
        let given : EvalM (Value × List String) := do
          pure (← valueIn { chartEnv scope records with keys } body, (← get).created)
        answered "input" given.run' (fs.input scope records a keys)
    held := fun scope records n edge extra =>
      let entry : Entry := match edge with
        | .transition t => .transition t.ref
        | .initial parent => .initial parent
      match site scope.machine (.held entry n) with
      | none => fs.held scope records n edge extra
      | some params =>
        let env := chartEnv scope records extra
        let values : EvalM Value := do
          answerOf env (.obj (← params.mapM fun c => do pure (c.name, ← eval env [] c.body)))
        answered "held" values.run' (fs.held scope records n edge extra)
    assign := fun scope records a extra keys =>
      match site scope.machine (assignSite a) with
      | none => fs.assign scope records a extra keys
      | some fields =>
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
        answered "assign" assigned.run' (fs.assign scope records a extra keys)
    initialContext := fun machine input =>
      match one machine .initialContext with
      | none => fs.initialContext machine input
      | some body => answered "initialContext"
          (valueIn { fields := fieldsOf st, args := argsOf [(.input, .json input)] } body).run'
          (fs.initialContext machine input)
    close := fun scope records =>
      match one scope.machine .close with
      | none => fs.close scope records
      | some body => answered "close" (valueIn (chartEnv scope records) body).run'
          (fs.close scope records) }

end Tazuna.Ir
