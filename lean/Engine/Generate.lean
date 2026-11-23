import Engine.Prove
import Engine.Verify
import Tazuna.Explore.Coverage

/-!
generate: for each coverage target of a spec service that a request reaches, the shortest sequence of requests from the
initial state that reaches it, and the run of each sequence as the spec's trace lines, which an implementation's tests
can feed in. The solver finds each sequence by unrolling prove's command steps from the initial records with increasing
depth; the semantics then runs it, and what the run reaches decides which targets it covers, as concolic testing runs
the solver's inputs concretely. Sequences whose targets other sequences cover are dropped.

TS runs Z3, so one request goes back and forth: given the solver's outputs on the scripts asked so far, in order, the
engine answers with the next scripts, or with the result once no target waits for an answer.
-/

namespace Tazuna.Engine

open Tazuna.Data Tazuna.Service Tazuna.Smt Tazuna.Explore

/-- What generate found of a target. -/
inductive Outcome where
  /-- A kept input's run reaches the target; `input` names the input. -/
  | reached (input : String)
  /-- No sequence of at most `depth` requests from the initial state reaches the target. -/
  | notReached (depth : Nat)
  /-- No state within the bounds lets the target's request reach it, so no run reaches it at any depth. -/
  | unreachable
  /-- The encoding cannot seek the target, such as a chart's, or cannot decide it. -/
  | notEncodable (reason : String)

derive_wire Outcome tag "kind" serialize_only

structure TargetOutcome where
  target : Violation
  outcome : Outcome

derive_wire TargetOutcome serialize_only

/-- An input of a spec service: the trace lines of its run, which the file `<service>/<name>.jsonl` holds. -/
structure GeneratedInput where
  service : String
  name : String
  lines : List TraceLine

derive_wire GeneratedInput serialize_only

structure Generation where
  targets : List TargetOutcome
  inputs : List GeneratedInput

derive_wire Generation serialize_only

/-- The name of the input that seeks `part`, a target that a request reaches. -/
def inputName : Uncovered → Option String
  | .request d => some s!"{d.name}.request"
  | .successAnswer d => some s!"{d.name}.successAnswer"
  | .bindsRejection d b => some s!"{d.name}.bindsRejection.{b}"
  | .requiresRejection d c => some s!"{d.name}.requiresRejection.{c}"
  | _ => none

/-- The definition of a target. -/
def _root_.Tazuna.Service.Uncovered.ref : Uncovered → Spec.Ref
  | .request d | .successAnswer d | .bindsRejection d _ | .requiresRejection d _ | .automation d
  | .automationBindingValue d _ | .automationBindingNull d _ | .automationGuard d _ _ | .transition d _
  | .guardFalse d _ _ | .state d _ => d

/-- That every check before the one named `name` passes, and that one fails without throwing; none when no check has the name. -/
def rejectedBy (checks : List Check) (name : String) : Option Term := do
  let k ← checks.findIdx? (·.name == name)
  let c ← checks[k]?
  pure (conj ((checks.take k).map (fun c => .and (.not c.throws) c.passes) ++ [.not c.throws, .not c.passes]))

/-- The term that holds when a command's step reaches `part`. -/
def stepGoal (step : Step) : Uncovered → Option Term
  | .request _ => some tt
  | .successAnswer _ => some step.accepted
  | .bindsRejection _ b => (rejectedBy step.binds b).map (.and step.refs)
  | .requiresRejection _ c =>
    (rejectedBy step.requires c).map fun t =>
      conj ([step.refs] ++ step.binds.map (fun b => .and (.not b.throws) b.passes) ++ [t])
  | _ => none

/-- The term that holds when a query's answer reaches `part`. -/
def answerGoal (a : Answered) : Uncovered → Option Term
  | .request _ => some tt
  | .successAnswer _ => some a.answered
  | .requiresRejection _ c => rejectedBy a.requires c
  | _ => none

/--
The time of the `i`th request, at or after the one before, a safe integer as every time is. The initial state's time is
0, the epoch: nothing reads it but the order of the times after it.
-/
def timeVar (i : Nat) : Term := if i == 0 then intLit 0 else .var s!"time{i}" .int

def timeFacts (i : Nat) : Facts :=
  if i == 0 then {} else
  { vars := [(s!"time{i}", .int)], asserts := [.le (timeVar (i - 1)) (timeVar i), .le (timeVar i) (intLit safeInteger)] }

def selVar (i : Nat) : Term := .var s!"s{i}.sel" .int

/-- The requests before the last one: the state after them, and each one's input of each command, which a model decodes. -/
structure Unrolled where
  facts : Facts
  state : Stepped
  inputs : List (List (List (String × Term)))

/--
The initial state of `st` within `creates`: no record in any slot, and each single entity's record of its schema
defaults (initialOf).
-/
def initialState (st : Service) (creates : List (String × Nat)) : Stepped × Facts :=
  let (init, facts) := initialOf st
  let keyed := (st.entities.filter (!st.singles.contains ·)).map fun e =>
    (e, (List.range ((creates.lookup e).getD 0)).map fun _ =>
      ({ live := ff, key := .lit (.str ""), fields := (Ir.fieldsOf st e).map (·, undefT) } : Slot))
  ({ records := { init with keyed }, used := keyed.map fun (e, slots) => (e, slots.map fun _ => ff) },
   facts ++ timeFacts 0)

/--
`n` accepted commands of `commands` from `init`: at each, the selector `s<i>.sel` picks a command, whose input fits its
schema, which the bounds and the encoding hold, and the state after it is named `s<i>.`.
-/
def unroll (st : Service) (p : Ir.Program) (commands : List String) (init : Stepped × Facts) (n : Nat) :
    Except String Unrolled := do
  let mut u : Unrolled := { facts := init.2, state := init.1, inputs := [] }
  for i in (List.range n).map (· + 1) do
    let mut facts := timeFacts i
    let mut options := []
    let mut inputs := []
    let mut merged : Option Stepped := none
    for (c, j) in commands.zipIdx do
      let (input, inputFacts) := Smt.inputOf st c s!"s{i}.{c}.in"
      let step ← stepWith st p u.state.records u.state.used c input (timeVar i) s!"s{i}.{c}."
      facts := facts ++ { inputFacts with asserts := [] } ++ step.facts
      let chosen := Term.eq (selVar i) (intLit j)
      options := options ++ [conj ([chosen] ++ inputFacts.asserts ++ [step.accepted, .not step.beyond, .not step.gap])]
      inputs := inputs ++ [input]
      let after : Stepped := { records := step.post, used := step.used }
      merged := some (match merged with
        | none => after
        | some m => .ite chosen after m)
    let some m := merged | throw "the service has no command"
    let (named, defs) := (m.named s!"s{i}.").run []
    facts := facts ++ { vars := [(s!"s{i}.sel", .int)] ++ defs.map fun (x, ty, _) => (x, ty),
                        asserts := defs.map (fun (x, ty, t) => .eq (.var x ty) t) ++ [disj options] }
    u := { facts := u.facts ++ facts, state := named, inputs := u.inputs ++ [inputs] }
  pure u

/--
The last request of a sequence: the query whose model is the sequence, whether its facts are complete (Facts), and the
request's line, made from a model.
-/
structure Last where
  query : Query
  complete : Bool
  line : Model → TraceLine

/-- A request line in, with the id `<name>#<n>` as a scenario's lines have. -/
def requestLine (query : Bool) (time : Int) (name : String) (n : Nat) (input : Value) : TraceLine :=
  let id := s!"{name}#{n}"
  { time, after := none, created := none,
    body := if query then .query .in id name input else .command .in id name input }

/-- One spec service's search: its commands that the encoding steps, and the target of each of its requests. -/
structure Search where
  st : Service
  creates : List (String × Nat)
  depth : Nat
  /-- The commands that a client sends and whose steps the encoding holds, which a sequence's earlier requests choose from. -/
  commands : List String
  /-- The service's targets, each with why the encoding cannot seek it, if it cannot. -/
  targets : List (Uncovered × Option String)

def searchOf (j : Spec.Structure) (depth : Option Nat) (service : String) : IO Search := do
  let st ← Service.ofStructure j service
  let p := j.program
  let bounds := (j.bounds.find? (·.service == service)).map (·.creates)
  let creates := bounds.getD []
  let keyed := st.entities.filter (!st.singles.contains ·)
  let init := initialState st creates
  let blocked := if bounds.isNone && !keyed.isEmpty then some "the service has no bounds()" else none
  let stepError (c : String) : Option String :=
    match stepWith st p init.1.records init.1.used c (Smt.inputOf st c "x").1 (timeVar 0) "x." with
    | .ok _ => none
    | .error why => some why
  -- A client sends what the service's contract lists, as an app's router serves it; without a contract, any request.
  let sendable (name : String) : Bool :=
    !j.contracts.any (·.service == service) || (j.contractsListing (st.ref name)).contains service
  let commands := st.commands.filter fun c => sendable c && (stepError c).isNone
  let mine := (targets j).filter (·.part.ref.service == service)
  let reason (part : Uncovered) : Option String :=
    let d := part.ref
    if (inputName part).isNone then some "generate seeks only the targets of requests to commands and queries"
    else if !sendable d.name then some "the service's contract does not list the request, so no client sends it"
    else if let some why := blocked then some why
    else if st.commands.contains d.name then (stepError d.name).map (s!"the command has no encoding: {·}")
    else match answerOf st p init.1.records (timeVar 0) d.name "x" with
      | .ok _ => none
      | .error why => some s!"the query has no encoding: {why}"
  pure { st, creates, commands, targets := mine.map fun t => (t.part, reason t.part),
         depth := depth.getD (creates.foldl (· + ·.2) 0 + 1) }

/-- The last request of a sequence of `n + 1` from the state `u.state`, which reaches `part`. -/
def Search.last (x : Search) (u : Unrolled) (part : Uncovered) (n : Nat) : Except String Last := do
  let p := x.st.structure.program
  let d := part.ref
  let i := n + 1
  let now := timeVar i
  if x.st.commands.contains d.name then
    let (input, inputFacts) := Smt.inputOf x.st d.name s!"s{i}.{d.name}.in"
    let step ← stepWith x.st p u.state.records u.state.used d.name input now s!"s{i}.{d.name}."
    let some goal := stepGoal step part | throw "no goal"
    let facts := u.facts ++ timeFacts i ++ inputFacts ++ step.facts
    pure { query := { vars := facts.vars, asserts := facts.asserts ++ [goal] }, complete := facts.complete,
           line := fun M => requestLine false (M s!"time{i}").toInt d.name 1 (.obj (present M input)) }
  else
    let a ← answerOf x.st p u.state.records now d.name s!"s{i}.{d.name}.in"
    let some goal := answerGoal a part | throw "no goal"
    let facts := u.facts ++ timeFacts i ++ a.facts
    pure { query := { vars := facts.vars, asserts := facts.asserts ++ [goal] }, complete := facts.complete,
           line := fun M => requestLine true (M s!"time{i}").toInt d.name 1 (.obj (present M a.input)) }

/-- Whether any state within the bounds, every record within its schema, lets the request of `part` reach it. -/
def Search.anyState (x : Search) (part : Uncovered) : Except String (Query × Bool) := do
  let p := x.st.structure.program
  let pre := SRecords.named x.st x.creates "pre"
  let used := pre.keyed.map fun (e, slots) => (e, (List.range slots.length).map (usedVar "pre" e))
  let facts := pre.facts x.st "pre" ++ clockFacts ++ nowFacts
  let d := part.ref
  let (goal, more) ← if x.st.commands.contains d.name then do
      let (input, inputFacts) := Smt.inputOf x.st d.name
      let step ← stepWith x.st p pre used d.name input nowT ""
      pure ((stepGoal step part).getD ff, inputFacts ++ step.facts)
    else do
      let a ← answerOf x.st p pre clockT d.name
      pure ((answerGoal a part).getD ff, a.facts)
  let all := facts ++ more
  pure ({ vars := all.vars, asserts := all.asserts ++ [goal] }, all.complete)

/-- The lines of a sequence from a model of its depth-`n + 1` query: the earlier requests, then the last. -/
def Search.lines (x : Search) (u : Unrolled) (last : Last) (M : Model) : List TraceLine := Id.run do
  let mut counts : List (String × Nat) := []
  let mut lines := []
  for (inputs, k) in u.inputs.zipIdx do
    let i := k + 1
    let j := (M s!"s{i}.sel").toInt.toNat
    let c := x.commands[j]!
    let n := (counts.lookup c).getD 0 + 1
    counts := (c, n) :: counts.filter (·.1 != c)
    lines := lines ++ [requestLine false (M s!"time{i}").toInt c n (.obj (present M inputs[j]!))]
  let l := last.line M
  let name := l.body.name?.getD ""
  let n := (counts.lookup name).getD 0 + 1
  let id := s!"{name}#{n}"
  let body := match l.body with
    | .command dir _ name input => .command dir id name input
    | .query dir _ name input => .query dir id name input
    | b => b
  pure (lines ++ [{ l with body }])

/-- Why an unsat answer over facts that are not complete decides nothing. -/
def incomplete : String :=
  "no sequence reaches it among the values that the encoding holds, which leave out some values of a schema, such as decimals"

/--
Where a target's search stands: still sought, with whether every unsat answer so far was over complete facts, found at a
depth, with the lines of its sequence, or done without one.
-/
inductive Status where
  | pending (complete : Bool)
  | found (lines : List TraceLine)
  | done (outcome : Outcome)

/--
The searches of each spec service after the solver's outputs `answers`, in order: each round asks the targets still
pending at the next depth, from 1 up to the service's depth, then whether any state lets the request of each target
still pending reach it. Either the next round's scripts, or every target's status.
-/
def searchAll (searches : List Search) (answers : List String) :
    Except (List String) (List (Search × List (Uncovered × Status))) := Id.run do
  let mut rest := answers
  let mut all := []
  for x in searches do
    let p := x.st.structure.program
    let init := initialState x.st x.creates
    let mut statuses : List (Uncovered × Status) := x.targets.map fun (part, why) =>
      (part, match why with
        | some r => .done (.notEncodable r)
        | none => .pending true)
    for n in List.range x.depth do
      let pending := statuses.filterMap fun (part, s) => if s matches .pending _ then some part else none
      if pending.isEmpty || (n > 0 && x.commands.isEmpty) then break
      let u := unroll x.st p x.commands init n
      let lasts := pending.map fun part => (part, u.bind fun u => (x.last u part n).map (u, ·))
      let asked := lasts.filterMap fun (_, l) => l.toOption
      if rest.length < asked.length then return .error (asked.map fun (_, l) => l.query.script proveRlimit)
      let mut outputs := rest.take asked.length
      rest := rest.drop asked.length
      for (part, l) in lasts do
        let before := match statuses.lookup part with
          | some (.pending c) => c
          | _ => true
        let status : Status := match l with
          | .error why => .done (.notEncodable s!"the sequence has no encoding: {why}")
          | .ok (u, last) =>
            let answer := Smt.Answer.read (outputs.headD "")
            match answer with
            | .sat values => .found (x.lines u last (Smt.Answer.model values))
            | .unsat => .pending (before && last.complete)
            | .unknown why => .done (.notEncodable why)
        if l.isOk then outputs := outputs.drop 1
        statuses := statuses.map fun (q, s) => if q == part then (q, status) else (q, s)
    let pending := statuses.filterMap fun (part, s) => if s matches .pending _ then some part else none
    let asked := pending.filterMap fun part => (x.anyState part).toOption.map (part, ·)
    if rest.length < asked.length then return .error (asked.map fun (_, q, _) => q.script proveRlimit)
    let outputs := rest.take asked.length
    rest := rest.drop asked.length
    statuses := statuses.map fun (part, s) =>
      match s, asked.findIdx? (·.1 == part) with
      | .pending complete, some k =>
        let anyComplete := ((asked[k]?).map (·.2.2)).getD false
        (part, .done (match Smt.Answer.read (outputs.getD k "") with
          | .unsat => if anyComplete then .unreachable else .notEncodable incomplete
          | _ => if complete then .notReached x.depth else .notEncodable incomplete))
      | .pending complete, none => (part, .done (if complete then .notReached x.depth else .notEncodable incomplete))
      | s, _ => (part, s)
    all := all ++ [(x, statuses)]
  return .ok all

/--
The run of `inputs`, the `in` lines of a sequence, from the initial state of `service` at the time `time`: the spec's
trace lines, and the targets that the run reaches.
-/
def runInputs (spec : Spec.Structure) (service : String) (time : Time) (inputs : List TraceLine) :
    IO (List TraceLine × List Uncovered) := do
  let st ← Service.ofStructure spec service
  let last ← IO.mkRef {}
  let fs := instrument st (Ir.functionsOf st last) (Ir.instrumentOf last)
  let run : ReplayM State := do
    let mut s ← begin st fs { now := time, service, records := [] }
    for l in inputs do
      if s.halted.isSome then break
      s ← takeIn spec st fs [] s l { l with value := none }
    if s.halted.isNone then s ← checkExchanges st fs s
    pure s
  let (s, c) ← run.run {}
  pure ((specLines service s).filterMap id, c.reached)

/-- A sequence that the solver found for a target, and its run. -/
structure Candidate where
  service : String
  name : String
  part : Uncovered
  lines : List TraceLine
  covers : List Uncovered

/--
The candidates left after dropping, shortest first, each whose targets the others left cover. A tie keeps the order of
the targets.
-/
def reduce (candidates : List Candidate) : List Candidate := Id.run do
  let order := (candidates.zipIdx.toArray.qsort fun (a, i) (b, k) =>
    a.lines.length < b.lines.length || (a.lines.length == b.lines.length && i < k)).toList.map (·.2)
  let mut kept := List.range candidates.length
  for i in order do
    let others := kept.filter (· != i)
    let covered (u : Uncovered) := others.any fun k => (candidates[k]?).any (·.covers.contains u)
    if ((candidates[i]?).map (·.covers.all covered)).getD false then kept := others
  return kept.filterMap (candidates[·]?)

/-- The own spec services' searches, after the solver's outputs `answers`: the next scripts, or the result. -/
def generateOf (j : Spec.Structure) (depth : Option Nat) (answers : List String) :
    IO (Except (List String) Generation) := do
  let searches ← (specServices j).mapM (searchOf j depth)
  match searchAll searches answers with
  | .error scripts => return .error scripts
  | .ok all =>
  let mut candidates := []
  for (x, statuses) in all do
    let targets := x.targets.map (·.1)
    for (part, s) in statuses do
      let .found lines := s | continue
      let time := ((lines.head?).map (·.time)).getD 0
      let (run, reached) ← runInputs j x.st.service time lines
      candidates := candidates ++ [{ service := x.st.service, name := (inputName part).getD "", part, lines := run,
                                     covers := reached.filter targets.contains : Candidate }]
  let kept := reduce candidates
  let outcomes := all.flatMap fun (x, statuses) => statuses.map fun (part, s) =>
    let outcome := match kept.find? (·.covers.contains part), s with
      | some c, _ => .reached c.name
      | none, .done o => o
      | none, .found _ =>
        .notEncodable ("the run of the solver's sequence does not reach it: a step that the encoding leaves out, " ++
          "such as an automation's, a chart's or a deadline's, changed the run")
      | none, .pending _ => .notReached x.depth
    ({ target := part.toViolation, outcome } : TargetOutcome)
  return .ok { targets := outcomes,
               inputs := kept.map fun c => { service := c.service, name := c.name, lines := c.lines } }

end Tazuna.Engine
