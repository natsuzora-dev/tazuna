import Engine.Prove
import Engine.Verify
import Tazuna.Semantics.Instrument.Coverage
import Std.Data.HashMap

/-!
generate: for each coverage target of a spec service, the shortest sequence of inputs from the initial state that the
search finds to reach it, and the run of each sequence as the spec's trace lines, which an implementation's tests can
feed in. The search is concolic: the semantics runs every input concretely from the initial state, breadth first, and
what each run reaches decides which targets it covers. The solver is asked one input at a time, at a concrete state: a
request's input that takes a branch of the request (a rejection, or a path through its decide when it accepts), or the
payload of an event or the output of an answer that the service receives. Sequences whose targets other sequences cover
are dropped.

TS runs Z3, so the search asks it through `solve` mid-run and goes on with the outputs.
-/

namespace Tazuna.Engine

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Smt Tazuna.Semantics.Instrument

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

/--
What generate found of a target, within the bounds of creating at most `creates` records of each keyed entity and of at
most `items` items in each array or Bag of an input, payload or answer that the solver picks.
-/
structure TargetOutcome where
  target : Violation
  creates : List (String × Nat)
  items : Nat
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

def triggerName : Ir.Trigger → String
  | .on key => s!"on.{key}"
  | .after deadline => s!"after.{deadline}"
  | .always => "always"
  | .onDone => "onDone"
  | .calls key .onFulfilled => s!"calls.{key}.onFulfilled"
  | .calls key .onRejected => s!"calls.{key}.onRejected"
  | .sends key .onAccepted => s!"sends.{key}.onAccepted"
  | .sends key .onRejected => s!"sends.{key}.onRejected"
  | .opens key => s!"opens.{key}"

def transitionName (t : Ir.TransitionRef) : String :=
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
def _root_.Tazuna.Semantics.Service.Uncovered.ref : Uncovered → Ir.Ref
  | .request d | .successAnswer d | .bindsRejection d _ | .requiresRejection d _ | .automation d
  | .automationBindingValue d _ | .automationBindingNull d _ | .automationGuard d _ _ | .transition d _
  | .guardFalse d _ _ | .state d _ => d

/-- Whether a request reaches `part`, so that the solver can seek it through the request's input. -/
def _root_.Tazuna.Semantics.Service.Uncovered.ofRequest : Uncovered → Bool
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

/--
The records `records` as terms within `creates`: each keyed entity's records in key order in live slots, then a free slot
for each record it may still create beyond `created`; and which slots are used.
-/
def recordTerms (st : Service) (creates created : List (String × Nat)) (records : Records) :
    Except String (SRecords × List (String × List Term)) := do
  let fieldsOfRow (e : String) (value : Value) : Except String (List (String × Term)) :=
    (Eval.fieldsOf st e).mapM fun f => do pure (f, ← fieldTerm (entitySchema st e) f (value.field? f))
  let keyedEntities := st.entities.filter (!st.singles.contains ·)
  let keyed ← keyedEntities.mapM fun e => do
    let rows := (records.filter (·.entity == e)).mergeSort fun a b => decide (a.keyText ≤ b.keyText)
    let names := st.keyFieldsOf e
    let live ← rows.mapM fun r => do
      pure ({ live := tt, key := .of names, fields := ← fieldsOfRow e r.value } : Slot)
    let free := (creates.lookup e).getD 0 - (created.lookup e).getD 0
    let empty : Slot := { live := ff, key := .of names, fields := (Eval.fieldsOf st e).map (·, undefT) }
    pure (e, live ++ (List.range free).map fun _ => empty)
  let singles ← st.singles.mapM fun e => do
    let value := ((records.find? (·.entity == e)).map (·.value)).getD (.obj [])
    pure (e, ← fieldsOfRow e value)
  let used := keyed.map fun (e, slots) => (e, slots.map (·.live))
  pure ({ keyed, singles, keyFields := st.keyFields }, used)

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
  { vars := [], asserts := [.not (.eq ((caller.lookup "service").getD undefT) (.mkStr (strLit st.service)))], fit := .exact }

/-- The number of `in` lines of `inputs` whose id is `<name>#<n>`, plus one: the number of the next. -/
def nextNumber (inputs : List TraceLine) (name : String) : Nat :=
  inputs.countP (fun l => (l.body.id.splitOn "#").head? == some name) + 1

/--
An input that the search may take at a state: a line, or a line that a model of the first satisfiable of some queries
gives, with the target the queries seek if they seek one, or the target whose query the encoding could not build, and why.
-/
inductive Want where
  | line (l : TraceLine)
  | solve (qs : List Query) (line : Model → TraceLine) (seeks : Option Uncovered)
  | broken (seeks : Uncovered) (why : String)

/-- The query of `facts` with `goal`. -/
def queryOf (facts : Facts) (goal : Term) : Query := { vars := facts.vars, asserts := facts.asserts ++ [goal] }

/-- That an answer's output `output` to the request of `target` with `input` meets the target's ensures, as its contract promises. -/
def promised (st : Service) (input : Value) (target : Ir.Ref) (output : List (String × SJson)) : Except String Term := do
  let env : SEnv := { args := fun
    | .input => (jsonLit input).toOption.map .ofJson
    | .output => some (.json output)
    | _ => none }
  let ensures := ((st.structure.program.resultEnsures.find? (·.definition == target)).map (·.conditions)).getD []
  let held ← ensures.mapM fun c => do
    let (v, e) ← seval env [] c.body
    pure (Term.and (.not e) v.truthy)
  pure (conj held)

/-- A value of a chart function's arguments as a symbolic value: JSON as literals, none for records. -/
def svalOfVal : Eval.Val → Option SVal
  | .undef => some (.scalar undefT)
  | .json v | .tracked _ v => (jsonLit v).toOption.map .ofJson
  | _ => none

/--
For an answer `output` to the shows slot `slot` of the screen instance `i`, the term of each offers of a control that
holds when the answer makes it list a payload, with the screen's other arguments as they are: the operations that the
answer opens, which the search seeks as it seeks each branch of an automation that an event reaches.
-/
def offerGoals (fs : Functions ReplayM) (st : Service) (s : Service.State) (i : Instance) (slot : String)
    (output : List (String × SJson)) : ReplayM (List Term) := do
  let p := st.structure.program
  let mut goals := []
  for control in i.chart.controls do
    let .ok found ← offeringStates fs st s i control.name (.obj []) | continue
    for (holder, state, o) in appliedOffers i control.name found do
      let .listed := o | continue
      let some f := p.chart.find? fun f => f.chart == st.ref i.chart.name && f.site == .offers state control.name
        | continue
      let some body := f.functions.head? | continue
      let scope := s.scopeOf holder state
      let shown := (scope.shown.filter (·.1 != slot)).filterMap fun (k, v) => (jsonLit v).toOption.map (k, ·)
      let args (a : Ir.Arg) : Option SVal :=
        if a == .shown then some (.json (shown ++ [(slot, .obj output)])) else svalOfVal (Eval.scopeArgs st scope .none a)
      let .ok (offers, err) := seval { args } [] body.body | continue
      let (size, notSized) := offers.size {}
      let (n, notScalar) := size.scalarOf
      goals := goals ++ [conj [.not err, .not notSized, .not notScalar, .lt (intLit 0) (.intOf n)]]
  pure goals

/-- One spec service's search. -/
structure Search where
  spec : Ir.Structure
  st : Service
  creates : List (String × Nat)
  /-- Why the service cannot grow, if it cannot: keyed entities without bounds(). -/
  blocked : Option String
  depth : Nat
  /-- The commands and queries that a client sends. -/
  sendable : List String
  targets : List Uncovered

def searchOf (j : Ir.Structure) (depth : Option Nat) (service : String) : IO Search := do
  let st ← specService j service
  let creates := Ir.createsOf j.bounds service
  let fromClients (name : String) : Bool :=
    ((st.requirements.lookup name).map (·.callers)).getD [] |>.any (· != .service service)
  let requested := ((st.charts.flatMap fun c => c.states.flatMap (·.activities)) ++ st.automations.map (·.sends)).filterMap
    fun a => if a matches .opens .. || a.ref.service == service then none else some a.ref.service
  let read := creates ++ requested.eraseDups.flatMap (Ir.createsOf j.bounds)
  pure { spec := j, st, creates, depth := depth.getD (read.foldl (· + ·.2) 0 + 1),
         blocked := unbounded j st,
         sendable := (st.commands ++ st.queries).filter fromClients,
         targets := ((targets j).filter (·.part.ref.service == service)).map (·.part) }

/-- A state of the search: the semantics' state after `inputs`, what the run collected, and the records it created per entity. -/
structure Node where
  state : Service.State
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
  for name in x.sendable do
    let all := open_.filter fun t => t.ofRequest && t.ref.name == name
    let mine := all.filter (!· matches .request _)
    let id := nextNumber n.inputs name
    let isQuery := st.queries.contains name
    let line (input : List (String × SJson)) (caller : List (String × Term)) (M : Model) :=
      requestLine isQuery s.now name id (.obj (SJson.concFields M input)) ((callerIn M caller).getD (.service ""))
    match terms with
    | .error why => wants := wants ++ all.map (.broken · s!"the state's records have no encoding: {why}")
    | .ok (pre, used) =>
    if isQuery then
      match answerOf st p pre now name "in" with
      | .error why => wants := wants ++ all.map (.broken · s!"the query has no encoding: {why}")
      | .ok a =>
        let facts := a.facts ++ fromOutside st a.caller
        wants := wants ++ mine.filterMap fun t =>
          (answerGoal a t).map fun g => .solve [queryOf facts g] (line a.input a.caller) (some t)
    else
      let (input, inputFacts) := inputOf st name "in"
      let (caller, callerFacts) := callerVars "in.caller"
      match stepWith st p pre used name input caller now "s." with
      | .error why => wants := wants ++ all.map (.broken · s!"the command has no encoding: {why}")
      | .ok step =>
        let facts := inputFacts ++ callerFacts ++ fromOutside st caller ++ step.facts
        let refFields := ((st.requirements.lookup name).map (·.refs)).getD []
        let inputFields := propertiesWith ((st.schemaOf (.input (st.ref name))).getD (.obj []))
        let mayBeNullish (field : String) := match inputFields.find? (·.1 == field) with
          | some (_, s, required) => !required || s.field? "x-tazuna-nullable" == some (.bool true)
          | none => true
        let pinned : List (List Term × Bool) := refFields.filterMap fun (field, target) =>
          match input.lookup field, pre.keyed.lookup target.name with
          | some (.scalar v), some slots =>
            let live := slots.filterMap fun sl => match sl.live, sl.key with
              | .lit (.bool true), .field f => some (.eq v ((sl.fields.lookup f).getD undefT))
              | _, _ => none
            some (live, mayBeNullish field || slots.any fun sl => !(sl.live matches .lit _))
          | _, _ => none
        let pins := pinned.flatMap (·.1)
        let noRecord := if pinned.all (·.2) then [Term.not (disj pins)] else []
        let creates := disj (step.used.flatMap fun (e, post) =>
          (((used.lookup e).getD []).zip post).filterMap fun (u, p) => if u == ff then some p else none)
        wants := wants ++
          mine.filterMap (fun t => (stepGoal step t).map fun g => .solve [queryOf facts g] (line input caller) (some t)) ++
          (advancing step).flatMap fun g =>
            if pins.isEmpty then
              [.solve ((if creates == ff then [] else [queryOf facts (.and g creates)]) ++ [queryOf facts g]) (line input caller) none]
            else (pins ++ noRecord).map fun pin => .solve [queryOf facts (.and g pin)] (line input caller) none
  for pd in s.pending.filter (!·.stale) do
    let target := pd.activity.ref
    let query := (st.structure.body? target) matches some (.query _)
    let id := s!"{target.service}/answer#{nextNumber n.inputs s!"{target.service}/answer"}"
    let answerLine (a : Ir.Answer) : TraceLine := { time := s.now, after := none, created := none, body := .answer .in id pd.id.text a }
    if st.structure.hasOutput target then
      let (output, facts) := objectOf st (.output target) "out"
      let promise := (promised st pd.input target output).toOption.getD tt
      let line (M : Model) := answerLine (if query then .fulfilled (.obj (SJson.concFields M output))
        else .accepted (some (.obj (SJson.concFields M output))))
      let opens ← match pd.requester with
        | .slot m slot => match s.machine? m with
          | some i => offerGoals fs st s i slot output
          | none => pure []
        | _ => pure []
      wants := wants ++ (tt :: opens).map fun g => .solve [queryOf facts (.and promise g)] line none
    else wants := wants ++ [.line (answerLine (if query then .fulfilled (.obj []) else .accepted none))]
    for kind in (st.structure.rejectionKinds st.service target).filter (!·.blamesSender) do
      let reasons := if kind == .requires then (st.structure.rejectionReasons target).map some else [none]
      wants := wants ++ reasons.map fun reason => .line (answerLine (.rejected { kind, reason }))
  for event in st.receives do
    let some (.event _) := st.structure.body? event | continue
    let name := s!"{event.service}.{event.name}"
    let id := s!"{event.service}/{event.name}#{nextNumber n.inputs s!"{event.service}/{event.name}"}"
    let (payload, facts) := objectOf st (.payload event) "pay"
    let line (M : Model) : TraceLine :=
      { time := s.now, after := none, created := none, body := .event .in id name (.obj (SJson.concFields M payload)) none }
    let mut goals := [(facts, tt)]
    if let .ok (pre, used) := terms then
      for a in st.automations.filter (·.receives == event) do
        let .ok r := reactionOf st p pre now (.json payload) a "r" | continue
        let base := facts ++ r.facts
        goals := goals ++ [(base, .not r.fires)]
        if a.sends.isOwn st.service then
          match stepWith st p pre used a.sends.ref.name (SJson.ofTerms r.input) (callerTerms (.service st.service)) now "rs." with
          | .ok step => goals := goals ++ (advancing step).map fun g => (base ++ step.facts, conj [r.fires, r.valid, g])
          | .error _ => goals := goals ++ [(base, r.fires)]
        else goals := goals ++ [(base, r.fires)]
    wants := wants ++ goals.map fun (f, g) => .solve [queryOf f g] line none
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
        wants := wants ++ [.solve [queryOf facts tt] (fun M => line (.obj (SJson.concFields M payload))) none]
  wants := wants ++ [.line { time := s.now, after := none, created := none, body := .restart .in s!"restart#{nextNumber n.inputs "restart"}" }]
  if let some t := (s.deadlines.map (·.time)).filter (s.now ≤ ·) |>.min? then
    wants := wants ++ [.line { time := t, after := none, created := none, body := .time .in s!"time#{nextNumber n.inputs "time"}" }]
  pure wants

/-- A search that asks the solver through the function it reads, and keeps the solver's output on each script asked so far. -/
abbrev SolveM := ReaderT (List String → IO (List String)) (StateT (Std.HashMap String String) IO)

/-- The solver's answers to `queries`, asking it for the scripts that no earlier output answers. -/
def solveAll (queries : List Query) : SolveM (List Smt.Answer) := do
  let scripts := queries.map (·.script proveRlimit)
  let missing := (scripts.filter (!(← get).contains ·)).eraseDups
  if !missing.isEmpty then
    let outputs ← (← read) missing
    if outputs.length != missing.length then throw (IO.userError s!"the solver gave {outputs.length} outputs for {missing.length} scripts")
    modify fun cache => (missing.zip outputs).foldl (fun c (k, v) => c.insert k v) cache
  let cache ← get
  pure ((queries.zip scripts).map fun (q, script) =>
    let text := cache.getD script ""
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
  let fs ← instrumentedFunctions st
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
    let queries := layer.flatMap fun (_, ws) => ws.flatMap fun | .solve qs _ _ => qs | _ => []
    let answers ← solveAll queries
    let mut k := 0
    let mut next := []
    for (n, wants) in layer do
      let mut tried : List TraceLine := []
      for w in wants do
        let line? := match w with
          | .line l => some l
          | .solve qs line _ => ((answers.drop k).take qs.length).findSome? fun
            | Smt.Answer.sat values => some (line (Smt.Answer.model values))
            | _ => none
          | .broken .. => none
        if let .solve _ _ (some t) := w then found := { found with sought := found.sought ++ [t] }
        if let .broken t why := w then found := { found with broken := found.broken ++ [(t, why)] }
        if let .solve qs _ _ := w then k := k + qs.length
        let some l := line? | continue
        if tried.contains l then continue
        tried := tried ++ [l]
        let s := n.state
        let ins (s : Service.State) := s.lines.toList.countP (·.dir == .in)
        let (s', c') ← (takeIn x.spec st fs [] s l { l with value := none }).run n.collect
        if ins s' == ins s || s'.halted.isSome || s'.violations.length != s.violations.length ||
          c'.violations.length != n.collect.violations.length then continue
        let (ended, _) ← (checkExchanges st fs s').run c'
        if ended.violations.length != s'.violations.length then continue
        let created := createdBetween s.records s'.records n.created
        if created.any fun (e, c) => c > (x.creates.lookup e).getD 0 then continue
        let inputs := n.inputs ++ [l]
        let fresh := c'.reached.filter fun t => x.targets.contains t && !found.first.any (·.1 == t)
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
  let used := pre.usedVars "pre"
  let facts := pre.facts x.st "pre" ++ clockFacts ++ nowFacts
  let d := part.ref
  let (goal, more) ← if x.st.commands.contains d.name then do
      let (input, inputFacts) := Smt.inputOf x.st d.name
      let (caller, callerFacts) := callerVars
      let step ← stepWith x.st p pre used d.name input caller nowT ""
      let some goal := stepGoal step part | throw "the command's step has no goal for the target"
      pure (goal, inputFacts ++ callerFacts ++ step.facts)
    else do
      let a ← answerOf x.st p pre clockT d.name
      let some goal := answerGoal a part | throw "the query's answer has no goal for the target"
      pure (goal, a.facts)
  let all := facts ++ more
  pure ({ vars := all.vars, asserts := all.asserts ++ [goal] }, all.fit.complete)

/-- The run of `inputs` from the initial state of `service`: the spec's trace lines, and the targets that the run reaches. -/
def runInputs (spec : Ir.Structure) (service : String) (inputs : List TraceLine) : IO (List TraceLine × List Uncovered) := do
  let st ← Service.ofStructure spec service
  let fs ← instrumentedFunctions st
  let run : ReplayM Service.State := do
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

/-- The own spec services' searches, asking `solve` for the solver's output on each script, in order. -/
def generateOf (j : Ir.Structure) (depth : Option Nat) (solve : List String → IO (List String)) : IO Generation := do
  let searches ← (specServices j).mapM (searchOf j depth)
  let searched : SolveM (List (Search × Found × List (Uncovered × Smt.Answer × Bool))) := searches.mapM fun x => do
    let found ← x.run
    let unreached := x.targets.filter fun t => t.ofRequest && !found.first.any (·.1 == t)
    let asked := unreached.filterMap fun t => (x.anyState t).toOption.map (t, ·)
    let answers ← solveAll (asked.map (·.2.1))
    pure (x, found, (asked.zip answers).map fun ((t, _, complete), a) => (t, a, complete))
  let (all, _) ← (searched.run solve).run {}
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
    ({ target := part.toViolation, creates := x.creates, items := Ir.itemsOf j.bounds x.st.service, outcome } :
      TargetOutcome)
  return { targets := outcomes,
           inputs := kept.map fun c => { service := c.service, name := c.name, lines := c.lines } }

end Tazuna.Engine
