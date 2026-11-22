import Tazuna.Ir.Eval

/-!
The Functions of the migration to IR: a callback evaluates in Lean when the program holds IR for it, and otherwise
answers as the functions beneath do. The arguments are those that TS passes the spec function for the same question.
-/

namespace Tazuna.Ir

open Tazuna.Data Tazuna.Service

/-- The arguments of a spec function that receives only `passed`; any other name is `undefined`. -/
def argsOf (passed : List (Arg × Val)) (a : Arg) : Val := (passed.lookup a).getD .undef

/-- An instant as a spec function's `now` holds it, in its JSON text. -/
def instant (t : Time) : Val := .json (.str (renderTime t))

/--
The event list that a command's ensures reads on a request's results: each event as `{ kind: "emit", payload }`. TS
also passes the event's definition, which IR cannot read.
-/
def emitted (events : List Emit) : Value :=
  .arr (events.map fun e => .obj [("kind", .str "emit"), ("payload", e.payload)])

/--
What a caller does with an answer that Lean evaluated: `answered callback (answer, parts) beneath` gives the answer,
where `parts` are the parts of the records that the evaluation read and `beneath` asks the functions beneath the same
question.
-/
abbrev Answered (m : Type → Type) :=
  {ε α : Type} → [BEq ε] → [BEq α] → [Repr ε] → [Repr α] →
    String → Except ε α × List RecordPart → m (Except ε α) → m (Except ε α)

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
  let holds (env : Env) (c : Condition) : EvalM Bool := do pure (truthy (← eval env [] c.body))
  let nonNull (env : Env) (c : Condition) : EvalM Bool := do
    match ← eval env [] c.body with
    | .undef | .json .null => pure false
    | _ => pure true
  { fs with
    inputRequirement := fun target c input =>
      match named p.inputRequirement target c with
      | some cond => answered "inputRequirement" (holds { args := argsOf [(.input, .json input)] } cond).run'
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
        answered "resultEnsures"
          ((fun h => if h then Ensured.holds else .fails) <$> holds { args } cond).run'
          (fs.resultEnsures target c input output events)
    invariant := fun entity record =>
      match all p.invariant (st.ref entity) with
      | none => fs.invariant entity record
      | some cs => answered "invariant" (firstFailing { args := argsOf [(.record, .json record)] } cs).run'
          (fs.invariant entity record)
    closeEnsures := fun screen input output =>
      match all p.closeEnsures (st.ref screen) with
      | none => fs.closeEnsures screen input output
      | some cs => answered "closeEnsures"
          (firstFailing { args := argsOf [(.input, .json input), (.output, .json output)] } cs).run'
          (fs.closeEnsures screen input output)
    binding := fun name b input records now =>
      match named p.binding (st.ref name) b with
      | none => fs.binding name b input records now
      | some c => answered "binding"
          (nonNull { args := argsOf [(.input, .json input), (.now, instant now)], records } c).run'
          (fs.binding name b input records now)
    requirement := fun name c input records now =>
      match named p.requirement (st.ref name) c with
      | none => fs.requirement name c input records now
      | some cond =>
        let env := { args := argsOf [(.input, .json input), (.now, instant now)], records }
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
          else withBound { args, records := before } (binds p.binding (st.ref name)) fun env =>
            firstFailing { env with records := after } cs
        answered "ensures" checked.run' (fs.ensures name input before after now)
    queryEnsures := fun name input output records =>
      match all p.queryEnsures (st.ref name) with
      | none => fs.queryEnsures name input output records
      | some cs => answered "queryEnsures"
          (firstFailing { args := argsOf [(.input, .json input), (.output, .json output)], records } cs).run'
          (fs.queryEnsures name input output records)
    serviceInvariant := fun records =>
      match all p.serviceInvariant (st.ref st.service) with
      | none => fs.serviceInvariant records
      | some cs =>
        let (answer, parts) := (firstFailing { records } cs).run'
        let answer := answer.mapError fun
          | .thrown schema => schema
          | _ => none
        answered "serviceInvariant" (answer, parts) (fs.serviceInvariant records)
    automationBinding := fun name b payload records now =>
      match named p.automationBinding (st.ref name) b with
      | none => fs.automationBinding name b payload records now
      | some c => answered "automationBinding"
          (nonNull { args := argsOf [(.payload, .json payload), (.now, instant now)], records } c).run'
          (fs.automationBinding name b payload records now)
    automationGuard := fun name c payload records now =>
      match named p.automationGuard (st.ref name) c with
      | none => fs.automationGuard name c payload records now
      | some cond =>
        let env := { args := argsOf [(.payload, .json payload), (.now, instant now)], records }
        answered "automationGuard" (withBound env (binds p.automationBinding (st.ref name)) (holds · cond)).run'
          (fs.automationGuard name c payload records now) }

end Tazuna.Ir
