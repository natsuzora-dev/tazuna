import Engine.Prove
import Engine.Verify
import Tazuna.Explore.Coverage
import Std.Data.HashMap

/-!
generate: for each coverage target of a spec service, the shortest sequence of inputs from the initial state that the
search finds to reach it, and the run of each sequence as the spec's trace lines, which an implementation's tests can
feed in. The search is concolic: the semantics runs every input concretely from the initial state, breadth first, and
what each run reaches decides which targets it covers. The solver is asked one input at a time, at a concrete state: a
request's input that takes a branch of the request (a rejection, or a path through its decide when it accepts), or the
payload of an event or the output of an answer that the service receives. Sequences whose targets other sequences cover
are dropped.

TS runs Z3, so one request goes back and forth: given the solver's outputs on the scripts asked so far, in order, the
engine answers with the next scripts, or with the result once no search waits for an answer.
-/

namespace Tazuna.Engine

open Tazuna.Data Tazuna.Service Tazuna.Smt Tazuna.Explore

/-- What generate found of a target. -/
inductive Outcome where
  /-- A kept input's run reaches the target; `input` names the input. -/
  | reached (input : String)
  /-- No run of at most `depth` inputs that the search tried reaches the target. -/
  | notReached (depth : Nat)
  /-- No state within the bounds lets the target's request reach it, so no run reaches it at any depth. -/
  | unreachable
  /-- No run reached the target, and the encoding could not ask the solver for its request's input. -/
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

def triggerName : Spec.Trigger → String
  | .on key => s!"on.{key}"
  | .after deadline => s!"after.{deadline}"
  | .always => "always"
  | .onDone => "onDone"
  | .calls key .onFulfilled => s!"calls.{key}.onFulfilled"
  | .calls key .onRejected => s!"calls.{key}.onRejected"
  | .sends key .onAccepted => s!"sends.{key}.onAccepted"
  | .sends key .onRejected => s!"sends.{key}.onRejected"
  | .opens key => s!"opens.{key}"

def transitionName (t : Spec.TransitionRef) : String :=
  s!"{t.state.getD "chart"}.{triggerName t.trigger}.{t.index}"

/-- The name of the input found first for `part`, which names its file. -/
def inputName : Uncovered → String
  | .request d => s!"{d.name}.request"
  | .successAnswer d => s!"{d.name}.successAnswer"
  | .bindsRejection d b => s!"{d.name}.bindsRejection.{b}"
  | .requiresRejection d c => s!"{d.name}.requiresRejection.{c}"
  | .automation d => s!"{d.name}.automation"
  | .automationBindingValue d b => s!"{d.name}.bindingValue.{b}"
  | .automationBindingNull d b => s!"{d.name}.bindingNull.{b}"
  | .automationGuard d c met => s!"{d.name}.guard.{c}.{met}"
  | .transition d t => s!"{d.name}.transition.{transitionName t}"
  | .guardFalse d t c => s!"{d.name}.guardFalse.{transitionName t}.{c}"
  | .state d s => s!"{d.name}.state.{s}"

/-- The definition of a target. -/
def _root_.Tazuna.Service.Uncovered.ref : Uncovered → Spec.Ref
  | .request d | .successAnswer d | .bindsRejection d _ | .requiresRejection d _ | .automation d
  | .automationBindingValue d _ | .automationBindingNull d _ | .automationGuard d _ _ | .transition d _
  | .guardFalse d _ _ | .state d _ => d

/-- Whether a request reaches `part`, so that the solver can seek it through the request's input. -/
def _root_.Tazuna.Service.Uncovered.ofRequest : Uncovered → Bool
  | .request _ | .successAnswer _ | .bindsRejection .. | .requiresRejection .. => true
  | _ => false

/-- That every check before the one named `name` passes, and that one fails without throwing; none when no check has the name. -/
def rejectedBy (checks : List Check) (name : String) : Option Term := do
  let k ← checks.findIdx? (·.name == name)
  let c ← checks[k]?
  pure (conj ((checks.take k).map (fun c => .and (.not c.throws) c.passes) ++ [.not c.throws, .not c.passes]))

/-- The term that holds when a command's step reaches `part`. -/
def stepGoal (step : Step) : Uncovered → Option Term
  | .request _ => some tt
  | .successAnswer _ => some step.accepted
  | .bindsRejection _ b => (rejectedBy step.binds b).map (conj [step.admitted, step.refs, ·])
  | .requiresRejection _ c =>
    (rejectedBy step.requires c).map fun t =>
      conj ([step.admitted, step.refs] ++ step.binds.map (fun b => .and (.not b.throws) b.passes) ++ [t])
  | _ => none

/-- The term that holds when a query's answer reaches `part`. -/
def answerGoal (a : Answered) : Uncovered → Option Term
  | .request _ => some tt
  | .successAnswer _ => some a.answered
  | .requiresRejection _ c => (rejectedBy a.requires c).map (.and a.admitted)
  | _ => none

/-- The term that holds when a command's step accepts along a path through its decide, within the bounds and the encoding. -/
def advancing (step : Step) : List Term :=
  step.paths.map fun path => conj [step.accepted, .not step.beyond, .not step.gap, path]

/-- A record field's value as a term: a date by its day number, as propertyVar holds a date; any other a scalar literal. -/
def fieldTerm (schema : Value) (f : String) (v : Option Value) : Except String Term :=
  match v with
  | none => pure undefT
  | some v =>
    let date := ((propertiesWith schema).find? (·.1 == f)).any (isDateSchema ·.2.1)
    match date, v with
    | true, .str label =>
      match parseDate? label with
      | some day => pure (.mkStr (.dateLabel (intLit day)))
      | none => litTerm v
    | _, _ => litTerm v

/--
The records `records` as terms within `creates`: each keyed entity's records in key order in live slots, then a free slot
for each record it may still create beyond `created`; and which slots are used.
-/
def recordTerms (st : Service) (creates created : List (String × Nat)) (records : Records) :
    Except String (SRecords × List (String × List Term)) := do
  let fieldsOfRow (e : String) (value : Value) : Except String (List (String × Term)) :=
    (Ir.fieldsOf st e).mapM fun f => do pure (f, ← fieldTerm (entitySchema st e) f (value.field? f))
  let keyedEntities := st.entities.filter (!st.singles.contains ·)
  let keyed ← keyedEntities.mapM fun e => do
    let rows := (records.filter (·.entity == e)).mergeSort fun a b => decide (a.keyText ≤ b.keyText)
    let names := st.keyFieldsOf e
    let live ← rows.mapM fun r => do
      let key ← match names, r.key with
        | [_], some (.str k) => do pure (SlotKey.text (.strOf (← litTerm (.str k))))
        | [_], _ => throw "a key that is no string"
        | _, _ => pure (SlotKey.fields names)
      pure ({ live := tt, key, fields := ← fieldsOfRow e r.value } : Slot)
    let free := (creates.lookup e).getD 0 - (created.lookup e).getD 0
    let emptyKey := match names with
      | [_] => SlotKey.text (.lit (.str ""))
      | _ => .fields names
    let empty : Slot := { live := ff, key := emptyKey, fields := (Ir.fieldsOf st e).map (·, undefT) }
    pure (e, live ++ (List.range free).map fun _ => empty)
  let singles ← st.singles.mapM fun e => do
    let value := ((records.find? (·.entity == e)).map (·.value)).getD (.obj [])
    pure (e, ← fieldsOfRow e value)
  let used := keyed.map fun (e, slots) => (e, slots.map (·.live))
  pure ({ keyed, singles }, used)

/-- A request line in from `caller`, with the id `<name>#<n>` as a scenario's lines have. -/
def requestLine (query : Bool) (time : Int) (name : String) (n : Nat) (input : Value) (caller : Caller) : TraceLine :=
  let id := s!"{name}#{n}"
  { time, after := none, created := none,
    body := if query then .query .in id name input caller else .command .in id name input caller }

/--
That a client's request to `st` comes from a caller other than `st` itself: the service sends its own requests from its
automations and charts, which the semantics runs, so a client that claims to be the service stands for no sender.
-/
def fromOutside (st : Service) (caller : List (String × Term)) : Facts :=
  { asserts := [.not (.eq ((caller.lookup "service").getD undefT) (.mkStr (strLit st.service)))] }

/-- The number of `in` lines of `inputs` whose id is `<name>#<n>`, plus one: the number of the next. -/
def nextNumber (inputs : List TraceLine) (name : String) : Nat :=
  inputs.countP (fun l => (l.body.id.splitOn "#").head? == some name) + 1

/--
An input that the search may take at a state: a line, or a line that a model of a query gives, with the target the
query seeks if it seeks one, or the target whose query the encoding could not build, and why.
-/
inductive Want where
  | line (l : TraceLine)
  | solve (q : Query) (line : Model → TraceLine) (seeks : Option Uncovered)
  | broken (seeks : Uncovered) (why : String)

/-- The query of `facts` with `goal`. -/
def queryOf (facts : Facts) (goal : Term) : Query := { vars := facts.vars, asserts := facts.asserts ++ [goal] }

/-- That an answer's output `output` to the request of `target` with `input` meets the target's ensures, as its contract promises. -/
def promised (st : Service) (input : Value) (target : Spec.Ref) (output : List (String × Term)) : Except String Term := do
  let env : SEnv := { args := fun
    | .input => (jsonLit input).toOption.map .ofJson
    | .output => some (.json (SJson.ofTerms output))
    | _ => none }
  let ensures := ((st.structure.program.resultEnsures.find? (·.definition == target)).map (·.conditions)).getD []
  let held ← ensures.mapM fun c => do
    let (v, e) ← seval env [] c.body
    pure (Term.and (.not e) v.truthy)
  pure (conj held)

/-- One spec service's search. -/
structure Search where
  spec : Spec.Structure
  st : Service
  creates : List (String × Nat)
  /-- Why the service cannot grow, if it cannot: keyed entities without bounds(). -/
  blocked : Option String
  depth : Nat
  /-- The commands and queries that a client sends. -/
  sendable : List String
  targets : List Uncovered

def searchOf (j : Spec.Structure) (depth : Option Nat) (service : String) : IO Search := do
  let st ← Service.ofStructure j service
  let bounds := (j.bounds.find? (·.service == service)).map (·.creates)
  let creates := bounds.getD []
  let keyed := st.entities.filter (!st.singles.contains ·)
  -- A client sends a request whose callers list someone outside the service (fromOutside).
  let fromClients (name : String) : Bool :=
    ((st.requirements.lookup name).map (·.callers)).getD [] |>.any (· != .service service)
  pure { spec := j, st, creates, depth := depth.getD (creates.foldl (· + ·.2) 0 + 1),
         blocked := if bounds.isNone && !keyed.isEmpty then some "the service has no bounds()" else none,
         sendable := (st.commands ++ st.queries).filter fromClients,
         targets := ((targets j).filter (·.part.ref.service == service)).map (·.part) }

/-- A state of the search: the semantics' state after `inputs`, what the run collected, and the records it created per entity. -/
structure Node where
  state : State
  collect : Collect
  inputs : List TraceLine
  created : List (String × Nat)

/--
The state that the search merges nodes by: what decides every later run, leaving out the trace, the ids that name lines,
and the violations.
-/
def fingerprint (n : Node) : String :=
  let s := n.state
  let r {α : Type} [Repr α] (a : α) : String := toString (repr a)
  let inst (i : Instance) := "|".intercalate [r i.id, r i.entered, r i.context, r i.held, r i.input, r i.lastChildren,
    r i.shown, r i.closed, r i.copyKeys, r i.awaitingOnDone]
  let records := s.records.mergeSort fun a b => decide (a.entity < b.entity ∨ (a.entity = b.entity ∧ a.keyText ≤ b.keyText))
  "#".intercalate [r s.now, r records, r (s.machines.map inst), r (s.copies.map inst),
    r (s.deadlines.map fun d => (d.time, d.machine, d.state, d.name)), r (s.pending.map fun p => (p.activity, p.input, p.stale)),
    r (s.queued.map fun q => (q.machine, q.state, q.stale)), r (s.subscriptions.map fun u => (u.query, u.input, u.last)),
    r s.stack, r s.obligations, r s.createdEntities, r s.started, r n.created]

/-- The inputs that the search tries at `n` while the targets `open_` are not reached. -/
def Search.wants (x : Search) (fs : Functions ReplayM) (n : Node) (open_ : List Uncovered) : ReplayM (List Want) := do
  let st := x.st
  let p := st.structure.program
  let s := n.state
  let now := intLit s.now
  let mut wants : List Want := []
  let terms := recordTerms st x.creates n.created s.records
  -- Requests: each target of the request still open, and each path through a command's decide that accepts.
  for name in x.sendable do
    let all := open_.filter fun t => t.ofRequest && t.ref.name == name
    -- Any input to the request reaches its request target, so the solver seeks only its answers.
    let mine := all.filter (!· matches .request _)
    let id := nextNumber n.inputs name
    let isQuery := st.queries.contains name
    let line (input caller : List (String × Term)) (M : Model) :=
      requestLine isQuery s.now name id (.obj (present M input)) ((callerIn M caller).getD (.service ""))
    match terms with
    | .error why => wants := wants ++ all.map (.broken · s!"the state's records have no encoding: {why}")
    | .ok (pre, used) =>
    if isQuery then
      match answerOf st p pre now name "in" with
      | .error why => wants := wants ++ all.map (.broken · s!"the query has no encoding: {why}")
      | .ok a =>
        let facts := a.facts ++ fromOutside st a.caller
        wants := wants ++ mine.filterMap fun t =>
          (answerGoal a t).map fun g => .solve (queryOf facts g) (line a.input a.caller) (some t)
    else
      let (input, inputFacts) := inputOf st name "in"
      let (caller, callerFacts) := callerVars "in.caller"
      match stepWith st p pre used name input caller now "s." with
      | .error why => wants := wants ++ all.map (.broken · s!"the command has no encoding: {why}")
      | .ok step =>
        let facts := inputFacts ++ callerFacts ++ fromOutside st caller ++ step.facts
        wants := wants ++
          mine.filterMap (fun t => (stepGoal step t).map fun g => .solve (queryOf facts g) (line input caller) (some t)) ++
          (advancing step).map fun g => .solve (queryOf facts g) (line input caller) none
  -- Answers to the service's requests that wait: an output within the schema, and each rejection the target may give.
  for pd in s.pending.filter (!·.stale) do
    let target := pd.activity.ref
    let query := (st.structure.body? target) matches some (.query _)
    let id := s!"{target.service}/answer#{nextNumber n.inputs s!"{target.service}/answer"}"
    let answerLine (a : Data.Answer) : TraceLine := { time := s.now, after := none, created := none, body := .answer .in id pd.id.text a }
    if st.structure.hasOutput target then
      let (output, facts) := objectOf st (.output target) "out"
      wants := wants ++ [.solve (queryOf facts ((promised st pd.input target output).toOption.getD tt))
        (fun M => answerLine (if query then .fulfilled (.obj (present M output)) else .accepted (some (.obj (present M output))))) none]
    else wants := wants ++ [.line (answerLine (if query then .fulfilled (.obj []) else .accepted none))]
    for kind in (st.structure.rejectionKinds st.service target).filter (!·.blamesSender) do
      let reasons := if kind == .requires then (st.structure.rejectionReasons target).map some else [none]
      wants := wants ++ reasons.map fun reason => .line (answerLine (.rejected { kind, reason }))
  -- Events of other services that the service receives: any payload, and one that takes each branch of each automation.
  for event in st.receives do
    let some (.event _) := st.structure.body? event | continue
    let name := s!"{event.service}.{event.name}"
    let id := s!"{event.service}/{event.name}#{nextNumber n.inputs s!"{event.service}/{event.name}"}"
    let (payload, facts) := objectOf st (.payload event) "pay"
    let line (M : Model) : TraceLine :=
      { time := s.now, after := none, created := none, body := .event .in id name (.obj (present M payload)) none }
    let mut goals := [(facts, tt)]
    if let .ok (pre, used) := terms then
      for a in st.automations.filter (·.receives == event) do
        let .ok r := reactionOf st p pre now (.json (SJson.ofTerms payload)) a "r" | continue
        let base := facts ++ r.facts
        goals := goals ++ [(base, .not r.fires)]
        if a.sends.isOwn st.service then
          match stepWith st p pre used a.sends.ref.name r.input (callerTerms (.service st.service)) now "rs." with
          | .ok step => goals := goals ++ (advancing step).map fun g => (base ++ step.facts, conj [r.fires, r.valid, g])
          | .error _ => goals := goals ++ [(base, r.fires)]
        else goals := goals ++ [(base, r.fires)]
    wants := wants ++ goals.map fun (f, g) => .solve (queryOf f g) line none
  -- Operations of the open screens: each offered payload, or any payload within the control's schema.
  for resource in s.stack.eraseDups do
    let .ok ops ← operationsOf fs st s resource | continue
    for op in ops do
      let name := s!"{op.screen}.{op.control}"
      let line (payload : Value) : TraceLine :=
        { time := s.now, after := none, created := none,
          body := .operation .in s!"operation#{nextNumber n.inputs "operation"}" name (s.nthOpen resource) (some payload) }
      match op.payloads with
      | some ps => wants := wants ++ ps.map (.line ∘ line)
      | none =>
        let (payload, facts) := objectOf st (.control (st.ref op.screen) op.control) "op"
        wants := wants ++ [.solve (queryOf facts tt) (fun M => line (.obj (present M payload))) none]
  -- A restart of the service process, which keeps the durable state.
  wants := wants ++ [.line { time := s.now, after := none, created := none, body := .restart .in s!"restart#{nextNumber n.inputs "restart"}" }]
  -- Time: the clock moves to the next deadline.
  if let some t := (s.deadlines.map (·.time)).filter (s.now ≤ ·) |>.min? then
    wants := wants ++ [.line { time := t, after := none, created := none, body := .time .in s!"time#{nextNumber n.inputs "time"}" }]
  pure wants

/-- The solver's outputs so far, by script, and the outputs not yet read. -/
structure Solved where
  cache : Std.HashMap String String := {}
  rest : List String

/-- A search that stops with the scripts it needs next when the outputs run out. -/
abbrev SolveM := ExceptT (List String) (StateT Solved IO)

/-- The solver's answers to `queries`, asking for the scripts that no output answers yet. -/
def solveAll (queries : List Query) : SolveM (List Smt.Answer) := do
  let scripts := queries.map (·.script proveRlimit)
  let s ← get
  let missing := (scripts.filter (!s.cache.contains ·)).eraseDups
  if s.rest.length < missing.length then throw missing
  set { cache := (missing.zip s.rest).foldl (fun c (k, v) => c.insert k v) s.cache, rest := s.rest.drop missing.length : Solved }
  let cache := (← get).cache
  pure ((queries.zip scripts).map fun (q, script) =>
    let text := cache.getD script ""
    -- With no variable, the script asks for no model.
    if q.vars.isEmpty && (text.trimAscii.toString.startsWith "sat") then .sat [] else Smt.Answer.read text)

/-- The records created by moving from `before` to `after`: the keys of each entity that `after` holds and `before` does not. -/
def createdBetween (before after : Records) (created : List (String × Nat)) : List (String × Nat) :=
  let fresh := after.filter fun r => r.key.isSome && !before.any fun b => b.entity == r.entity && b.key == r.key
  let entities := (created.map (·.1) ++ fresh.map (·.entity)).eraseDups
  entities.map fun e => (e, (created.lookup e).getD 0 + fresh.countP (·.entity == e))

/-- What one service's search found: the inputs that first reached each target, and why some request targets could not be sought. -/
structure Found where
  first : List (Uncovered × List TraceLine)
  /-- The request targets that some query sought, and those whose queries the encoding could not build, with why. -/
  sought : List Uncovered
  broken : List (Uncovered × String)

/--
The breadth-first search of `x` from its initial state, `x.depth` inputs deep: each layer's nodes, whose fingerprint no
earlier node had, try their wants, and each input that the semantics takes without halting or a violation and that
stays within the bounds leads to a node of the next layer.
-/
def Search.run (x : Search) : SolveM Found := do
  let st := x.st
  let last ← IO.mkRef {}
  let fs := instrument st (Ir.functionsOf st last) (Ir.instrumentOf last)
  let (s0, c0) ← (begin st fs { now := 0, service := st.service, records := [] }).run {}
  let mut found : Found := { first := (c0.reached.filter x.targets.contains).map (·, []), sought := [], broken := [] }
  let mut frontier : List Node := [{ state := s0, collect := c0, inputs := [], created := [] }]
  let mut seen : Std.HashMap String Unit := {}
  for _ in List.range x.depth do
    let open_ := x.targets.filter fun t => !found.first.any (·.1 == t)
    if open_.isEmpty || frontier.isEmpty then break
    let mut layer := []
    for n in frontier do
      let fp := fingerprint n
      if seen.contains fp || n.state.halted.isSome then continue
      seen := seen.insert fp ()
      let (wants, _) ← (x.wants fs n open_).run n.collect
      layer := layer ++ [(n, wants)]
    let queries := layer.flatMap fun (_, ws) => ws.filterMap fun | .solve q _ _ => some q | _ => none
    let answers ← solveAll queries
    let mut k := 0
    let mut next := []
    for (n, wants) in layer do
      let mut tried : List TraceLine := []
      for w in wants do
        let line? := match w with
          | .line l => some l
          | .solve _ line _ => match answers[k]? with
            | some (.sat values) => some (line (Smt.Answer.model values))
            | _ => none
          | .broken .. => none
        if let .solve _ _ (some t) := w then found := { found with sought := found.sought ++ [t] }
        if let .broken t why := w then found := { found with broken := found.broken ++ [(t, why)] }
        if w matches .solve .. then k := k + 1
        let some l := line? | continue
        if tried.contains l then continue
        tried := tried ++ [l]
        let s := n.state
        let ins (s : State) := s.lines.toList.countP (·.dir == .in)
        let (s', c') ← (takeIn x.spec st fs [] s l { l with value := none }).run n.collect
        if ins s' == ins s || s'.halted.isSome || s'.violations.length != s.violations.length ||
          c'.violations.length != n.collect.violations.length then continue
        let (ended, _) ← (checkExchanges st fs s').run c'
        if ended.violations.length != s'.violations.length then continue
        let created := createdBetween s.records s'.records n.created
        if created.any fun (e, c) => c > (x.creates.lookup e).getD 0 then continue
        let inputs := n.inputs ++ [l]
        let fresh := c'.reached.filter fun t => x.targets.contains t && !found.first.any (·.1 == t)
        -- The target that the query sought comes first, so that the input is named after it.
        let sought := match w with
          | .solve _ _ (some t) => if fresh.contains t then [t] else []
          | _ => []
        found := { found with first := found.first ++ (sought ++ fresh.filter (!sought.contains ·)).map (·, inputs) }
        next := next ++ [{ state := s', collect := c', inputs, created : Node }]
    frontier := next
  pure found

/--
Whether any state within the bounds, every record within its schema, lets the request of `part` from any caller that
its target takes reach it: the service's own automations and charts send too.
-/
def Search.anyState (x : Search) (part : Uncovered) : Except String (Query × Bool) := do
  let p := x.st.structure.program
  let pre := SRecords.named x.st x.creates "pre"
  let used := pre.keyed.map fun (e, slots) => (e, (List.range slots.length).map (usedVar "pre" e))
  let facts := pre.facts x.st "pre" ++ clockFacts ++ nowFacts
  let d := part.ref
  let (goal, more) ← if x.st.commands.contains d.name then do
      let (input, inputFacts) := Smt.inputOf x.st d.name
      let (caller, callerFacts) := callerVars
      let step ← stepWith x.st p pre used d.name input caller nowT ""
      pure ((stepGoal step part).getD ff, inputFacts ++ callerFacts ++ step.facts)
    else do
      let a ← answerOf x.st p pre clockT d.name
      pure ((answerGoal a part).getD ff, a.facts)
  let all := facts ++ more
  pure ({ vars := all.vars, asserts := all.asserts ++ [goal] }, all.complete)

/-- The run of `inputs` from the initial state of `service`: the spec's trace lines, and the targets that the run reaches. -/
def runInputs (spec : Spec.Structure) (service : String) (inputs : List TraceLine) : IO (List TraceLine × List Uncovered) := do
  let st ← Service.ofStructure spec service
  let last ← IO.mkRef {}
  let fs := instrument st (Ir.functionsOf st last) (Ir.instrumentOf last)
  let run : ReplayM State := do
    let mut s ← begin st fs { now := 0, service, records := [] }
    for l in inputs do
      s ← takeIn spec st fs [] s l { l with value := none }
    checkExchanges st fs s
  let (s, c) ← run.run {}
  pure ((specLines service s).filterMap id, c.reached)

/-- A sequence that the search found for a target, and its run. -/
structure Candidate where
  service : String
  name : String
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
  let searched : SolveM (List (Search × Found × List (Uncovered × Smt.Answer × Bool))) := searches.mapM fun x => do
    let found ← x.run
    let unreached := x.targets.filter fun t => t.ofRequest && !found.first.any (·.1 == t)
    let asked := unreached.filterMap fun t => (x.anyState t).toOption.map (t, ·)
    let answers ← solveAll (asked.map (·.2.1))
    pure (x, found, (asked.zip answers).map fun ((t, _, complete), a) => (t, a, complete))
  let (result, _) ← searched.run.run { rest := answers }
  match result with
  | .error scripts => return .error scripts
  | .ok all =>
  let mut candidates := []
  for (x, found, _) in all do
    let mut paths : List (List TraceLine) := []
    for (part, inputs) in found.first do
      if inputs.isEmpty || paths.contains inputs then continue
      paths := paths ++ [inputs]
      let (lines, reached) ← runInputs j x.st.service inputs
      candidates := candidates ++ [{ service := x.st.service, name := inputName part, lines,
                                     covers := reached.filter x.targets.contains : Candidate }]
  let kept := reduce candidates
  let outcomes := all.flatMap fun (x, found, proofs) => x.targets.map fun part =>
    let outcome := match kept.find? (fun c => c.service == x.st.service && c.covers.contains part), proofs.find? (·.1 == part) with
      | some c, _ => .reached c.name
      | none, some (_, .unsat, true) => .unreachable
      | none, _ =>
        match x.blocked, found.broken.lookup part with
        | some why, _ => .notEncodable why
        | none, some why => if found.sought.contains part then .notReached x.depth else .notEncodable why
        | none, none => .notReached x.depth
    ({ target := part.toViolation, outcome } : TargetOutcome)
  return .ok { targets := outcomes,
               inputs := kept.map fun c => { service := c.service, name := c.name, lines := c.lines } }

end Tazuna.Engine
