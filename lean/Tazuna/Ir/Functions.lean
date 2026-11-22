import Tazuna.Ir.Overlay
import Tazuna.Data.Parse
import Tazuna.Explore.Instrument

/-!
The Functions that the engine runs a spec with: each spec function evaluated from the IR that the structure's program
holds, and each structural question (parse, unordered, comparable, defaults) answered from the structure's JSON
Schemas by Data.Parse. A question that neither answers is a bug of the converter or of check, which reports every
function outside the IR.
-/

namespace Tazuna.Ir

open Tazuna.Data Tazuna.Service Tazuna.Explore

/-- What the latest evaluation read: the record parts and the chart values, which Instrument collects. -/
structure LastRead where
  parts : List RecordPart := []
  access : Access := {}

/-- The stop at a question that the program and the schemas leave unanswered. -/
def unanswered {α : Type} (question : String) : IO α :=
  throw (IO.userError s!"the spec has no IR or schema for {question}")

/-- Functions that answer no question. -/
def unansweredFunctions : Functions IO where
  parse _ _ := unanswered "parse"
  unordered _ _ := unanswered "unordered"
  binding _ _ _ _ _ := unanswered "binding"
  requirement _ _ _ _ _ := unanswered "requirement"
  inputRequirement _ _ _ := unanswered "inputRequirement"
  decide _ _ _ _ := unanswered "decide"
  ensures _ _ _ _ _ := unanswered "ensures"
  queryEnsures _ _ _ _ := unanswered "queryEnsures"
  resultEnsures _ _ _ _ _ := unanswered "resultEnsures"
  invariant _ _ := unanswered "invariant"
  serviceInvariant _ := unanswered "serviceInvariant"
  chartInvariant _ _ := unanswered "chartInvariant"
  resolve _ _ _ _ := unanswered "resolve"
  automationBinding _ _ _ _ _ := unanswered "automationBinding"
  automationGuard _ _ _ _ _ := unanswered "automationGuard"
  react _ _ _ _ _ := unanswered "react"
  comparable _ _ := unanswered "comparable"
  initialContext _ _ := unanswered "initialContext"
  guard _ _ _ _ _ := unanswered "guard"
  assign _ _ _ _ _ := unanswered "assign"
  input _ _ _ _ := unanswered "input"
  held _ _ _ _ _ := unanswered "held"
  deadlineAt _ _ _ := unanswered "deadlineAt"
  offers _ _ _ := unanswered "offers"
  showInput _ _ _ := unanswered "showInput"
  items _ _ := unanswered "items"
  defaults _ := unanswered "defaults"
  close _ _ := unanswered "close"
  closeEnsures _ _ _ := unanswered "closeEnsures"

/-- The answer of a parse, which throws only in a codec, and a check rejects codecs (Restricted.schema). -/
def thrownBy {α : Type} (schema : Schema) : ParseM α → Except Issue α
  | .ok a => .ok a
  | .error () => .error (.thrown (some schema))

/-- `fs` with the structural questions answered by Data.Parse from the JSON Schemas of `st`'s structure. -/
def structural (st : Service) (fs : Functions IO) : Functions IO :=
  let json (schema : Schema) : Option Value := (st.schemaOf schema).map rootSchema |>.filter supported
  { fs with
    parse := fun schema value => do
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
      pure (.ok (defaultsOf j)) }

/--
The functions of the running service `st`: its program's IR and its schemas. Each evaluation leaves what it read in
`last`.
-/
def functionsOf (st : Service) (last : IO.Ref LastRead) : Functions IO :=
  let answered : Answered IO := fun _ (answer, trace) _ => do
    last.set { parts := trace.parts, access := trace.access }
    pure answer
  structural st (st.structure.program.overlay st answered unansweredFunctions)

/-- What Instrument reads besides Functions, from `last`. -/
def instrumentOf (last : IO.Ref LastRead) : InstrumentFunctions IO :=
  { lastReads := do pure (← last.get).parts, lastAccess := do pure (← last.get).access }

end Tazuna.Ir
