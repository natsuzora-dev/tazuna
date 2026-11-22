import Engine.Run
import Tazuna.Verify.External

/-!
What the CLI's verify command asks of the engine: a trace compared with its snapshot, and an external service's trace
checked against its contract, with the values read by their schemas and the contract's conditions evaluated as IR.
-/

namespace Tazuna.Engine

open Tazuna.Data Tazuna.Service Tazuna.Verify

/-- A finding as a report writes it: a violation with its line, or an `after`, which only test compares. -/
instance : ToValue Verify.Finding := ⟨fun
  | .mismatch m => ToValue.toValue m
  | .uncomparable u => ToValue.toValue u
  | .after line subject snapshot trace =>
    .obj [("after", .obj [("line", ToValue.toValue line), ("subject", ToValue.toValue subject),
      ("snapshot", ToValue.toValue snapshot), ("trace", ToValue.toValue trace)])]⟩

/-- Whether a finding is a violation of verify, which compares no `after`. -/
def _root_.Tazuna.Verify.Finding.isViolation : Verify.Finding → Bool
  | .after .. => false
  | _ => true

/-- The violations of `trace` against `snapshot`, by line, and the pairs of each binding that the comparison ends with. -/
def verifyTrace (spec : Spec.Structure) (service : String) (snapshot : List (Option TraceLine))
    (trace : List (FileLine TraceLine)) : IO (List Verify.Finding × List (List (String × String))) := do
  let compared ← Verify.verifyLines spec service (readIn spec) snapshot trace id
  let byLine := compared.findings.mergeSort fun a b => decide (a.line ≤ b.line)
  pure (byLine.filter (·.isViolation), compared.bindings.map (·.strings))

/-- The value of an Except that stops the engine on an Issue, as a spec function's throw stopped TS. -/
def orStop {α : Type} (what : String) : Except Issue α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what} stopped on {repr e}")

/--
checkExternal, and on the lines that it finds nothing on, the checks that read schemas and the contract's conditions:
each event's payload, and each answer that answers a send of its request: the request's input, which only a rejection
may answer when it fails the schema, the requires on the input, the output, and a command's ensures with all its
result events, which may come before or after the answer.
-/
def verifyExternal (spec : Spec.Structure) (service : String) (trace : List (FileLine TraceLine)) :
    IO (List Verify.Finding) := do
  let st ← Service.ofStructure spec service
  let last ← IO.mkRef {}
  let fs := Ir.functionsOf st last
  let (lines, cut) := comparedLines .in trace
  let structural := checkLines spec service lines 1 [] ++ (exchanges spec service lines).flatMap (checkExchange spec service)
  let found := structural ++ (cut.map .uncomparable).toList
  let flagged := found.map (·.line)
  let numbered := (lines.zipIdx 1).filterMap fun (l, i) => l.map (i, ·)
  let mut more : List Verify.Finding := []
  let mut emitted : List (Nat × Emit) := []
  for (i, l) in numbered do
    let .event .out _ name payload _ := l.body | continue
    let some event := spec.named service (some name) ["event"] | continue
    if flagged.contains i then continue
    match ← orStop "the payload check" (← fs.parseOutside st (.payload event.ref) payload) with
    | some p => emitted := emitted ++ [(i, { event := event.ref, payload := p })]
    | none => more := more ++ [.mismatch (.eventPayloadSchema i event.ref)]
  for x in exchanges spec service lines do
    let target := x.definition.ref
    let input := match (numbered.lookup x.line).map (·.body) with
      | some (.command _ _ _ v) | some (.query _ _ _ v) => v
      | _ => .null
    let parsedInput ← orStop "the input check" (← fs.parseOutside st (.input target) input)
    let (requires, ensures) := (spec.conditionsOf? target).getD ([], [])
    let sentBefore (line : Nat) := 1 + (x.resends.filter (· < line)).length
    let mut answered := 0
    for (line, answer) in x.answers do
      if answered >= sentBefore line then continue
      answered := answered + 1
      if flagged.contains line then continue
      -- An answer without the output that its target declares fails the output schema.
      let output : Option (Option Value) := match answer with
        | .rejected _ => none
        | .accepted o => if spec.hasOutput target then some o else none
        | .fulfilled o => if spec.hasOutput target then some (some o) else none
      let parsedOutput ← match output with
        | some (some o) => some <$> orStop "the output check" (← fs.parseOutside st (.output target) o)
        | some none => pure (some none)
        | none => pure none
      let rejected := answer matches .rejected _
      if parsedInput.isNone && !rejected then more := more ++ [.mismatch (.requestInputSchema line x.id target)]
      if let some decodedInput := parsedInput then
        let failedRequires ← orStop "the requires" (← firstFalse (fs.inputRequirement target · decodedInput) requires)
        let outputFails := parsedOutput matches some none
        let results := x.events.filterMap fun (j, _) => emitted.lookup j
        let failedEnsures ←
          if rejected || failedRequires.isSome || outputFails then pure none
          else orStop "the ensures" (← firstFalse (fun n => do
            pure ((← fs.resultEnsures target n decodedInput (parsedOutput.join) results).map Ensured.passes)) ensures)
        if let some broken := Spec.assumptionMismatch answer failedRequires failedEnsures then
          more := more ++ [.mismatch (.assumption line x.id target broken)]
      if parsedOutput matches some none then
        more := more ++ [.mismatch (.assumption line x.id target .answerOutputSchema)]
  let all := (found ++ more).mergeSort fun a b => decide (a.line ≤ b.line)
  pure (all.filter (·.isViolation))

end Tazuna.Engine
