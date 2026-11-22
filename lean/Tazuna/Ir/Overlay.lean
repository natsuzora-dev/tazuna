import Tazuna.Ir.Eval

/-!
The Functions of the migration to IR: a callback evaluates in Lean when the program holds IR for it, and otherwise
answers as the functions beneath do. The arguments are those that TS passes the spec function for the same question.
-/

namespace Tazuna.Ir

open Tazuna.Data Tazuna.Service

/-- The arguments of a spec function that receives only `passed`; any other name is `undefined`. -/
def argsOf (passed : List (Arg × Val)) (a : Arg) : Val := (passed.lookup a).join

/--
The event list that a command's ensures reads on a request's results: each event as `{ kind: "emit", payload }`. TS
also passes the event's definition, which IR cannot read.
-/
def emitted (events : List Emit) : Value :=
  .arr (events.map fun e => .obj [("kind", .str "emit"), ("payload", e.payload)])

/--
`fs` with each callback that `p` holds IR for evaluated in Lean, after `evaluated`: the caller's note that this answer
read no record, which every expression of this subset of the IR holds to.
-/
def Program.overlay {m : Type → Type} [Monad m] (p : Program) (st : Service) (evaluated : m Unit) (fs : Functions m) :
    Functions m :=
  let run {α : Type} (x : Except Issue α) : m (Except Issue α) := do
    evaluated
    pure x
  let named (cs : List Condition) (definition : Spec.Ref) (name : String) :=
    cs.find? fun c => c.definition == definition && c.name == name
  let all (cs : List Condition) (definition : Spec.Ref) := cs.filter (·.definition == definition)
  { fs with
    inputRequirement := fun target c input =>
      match named p.requires target c with
      | some c => run (truthy <$> eval (argsOf [(.input, some input)]) [] c.body)
      | none => fs.inputRequirement target c input
    resultEnsures := fun target c input output events =>
      match named p.ensures target c with
      | none => fs.resultEnsures target c input output events
      | some c =>
        let output := if (st.«structure».schemaOf (.output target)).isSome then output else none
        let events := match st.«structure».body? target with
          | some (.command _) => some (emitted events)
          | _ => none
        let args := argsOf [(.input, some input), (.output, output), (.events, events)]
        run ((fun v => if truthy v then .holds else .fails) <$> eval args [] c.body)
    invariant := fun entity record =>
      match all p.invariants (st.ref entity) with
      | [] => fs.invariant entity record
      | cs => run (firstFailing (argsOf [(.record, some record)]) cs)
    closeEnsures := fun screen input output =>
      match all p.closeEnsures (st.ref screen) with
      | [] => fs.closeEnsures screen input output
      | cs => run (firstFailing (argsOf [(.input, some input), (.output, some output)]) cs) }

end Tazuna.Ir
