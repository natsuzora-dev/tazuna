import Tazuna.Smt.Chart
import Tazuna.Smt.Pair
import Std.Data.HashSet

/-!
The chain of one message: the steps that a due deadline or an arriving event causes within its message, in the order of
Service.drain. The control is concrete and the data symbolic: each choice that data decides, such as which transition a
guard lets through or whether a command accepts, splits the chain into paths, each with the term that holds when the
message takes it. The chain follows at most `chainLimit` steps of a message; a path with steps left past them is cut,
and prove asks whether any cut path can be taken. These encodings carry no proof; prove replays each answer that it
reports in the semantics.
-/

namespace Tazuna.Smt

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Eval Tazuna.Semantics.Service

/--
The steps of one message that prove follows, each work item, own command or sending of entered states' activities one
step, as Service.drain counts them, and each always round of a settle one more. As CBMC and Kani unwind a loop only to
the bound they are given and then check that no run goes further (the unwinding assertion), a message that can take
more steps leaves its tie undecided, never proved. The longest chain of the todo sample takes 6 steps (at a bound of 5
its ties are cut, at 6 none is), and 8 leaves two to spare; a path can split at each step, so a larger bound costs
time on every spec.
-/
def chainLimit : Nat := 8

/-- What an out line carries: a request to another service, or an event. -/
inductive OutKind where
  | command
  | query
  | event
deriving DecidableEq, Repr

/--
A line that a message writes out, the term that holds when it does, and its fields. `id` names where the chain wrote
it, which the paths that split after it share.
-/
structure Out where
  id : String
  guard : Term
  kind : OutKind
  definition : Ir.Ref
  fields : List (String × Term)

/--
A fault that a message raises and that no other property reports, the term that holds when it does: an automation's own
command rejected (Fault.rejectedAutomationCommand), which does not halt. `id` names where the chain raised it, as an out
line's does.
-/
structure Raised where
  id : String
  guard : Term
  automation : String
  rejection : Rejection

/-- An `after` deadline of a state: whether it waits, and when it is due. -/
structure Armed where
  state : String
  name : String
  waits : Term
  time : Term

/--
The request of a state's activity to another service: whether one that the chain sent awaits its answer, and its input.
Until the chain sends one, the request is whatever the state held before, the same in every order.
-/
structure Request where
  state : String
  key : String
  sent : Term
  input : List (String × Term)

/--
A machine in a chain, the whole of its state that decides the service's later messages: the configurations of the
chart's model that it can be in and the term of which one it is, its context, its deadlines and its requests to other
services; and the states that it exited so far. A path fixes one configuration only when a step reads it, so that paths
that differ only in a machine's configuration join, and the steps that do not read it are followed once.
-/
structure Mach where
  configs : List Nat
  config : Term
  context : List (String × Term)
  deadlines : List Armed := []
  requests : List Request := []
  exited : List String := []

def Mach.fixed? (m : Mach) : Option Nat := match m.configs with
  | [k] => some k
  | _ => none

/-- The machine after it exited `states`: their deadlines taken away and their requests stale. -/
def Mach.leave (m : Mach) (states : List String) : Mach :=
  { m with exited := m.exited ++ states,
           deadlines := m.deadlines.map fun d => if states.contains d.state then { d with waits := ff } else d,
           requests := m.requests.map fun r => if states.contains r.state then { r with sent := ff } else r }

/-- `t` where `c` holds, else `e`, each datum joined. -/
def Mach.ite (c : Term) (t e : Mach) : Mach :=
  let fields (a b : List (String × Term)) : List (String × Term) :=
    ((a.map (·.1)) ++ b.map (·.1)).eraseDups.map fun f => (f, iteT c ((a.lookup f).getD undefT) ((b.lookup f).getD undefT))
  { e with configs := (e.configs ++ t.configs).eraseDups.mergeSort, config := iteT c t.config e.config,
           context := fields t.context e.context,
           deadlines := e.deadlines.map fun d => match t.deadlines.find? (fun x => x.state == d.state && x.name == d.name) with
             | some x => { d with waits := iteT c x.waits d.waits, time := iteT c x.time d.time }
             | none => d,
           requests := e.requests.map fun r => match t.requests.find? (fun x => x.state == r.state && x.key == r.key) with
             | some x => { r with sent := iteT c x.sent r.sent, input := fields x.input r.input }
             | none => r }

/--
That two machines differ in a way that a later message can see: their configurations, a context field, whether a
deadline waits or when it is due, or whether a request that the chain sent waits or its input.
-/
def Mach.differ (a b : Mach) : Term :=
  let fieldsDiffer (x y : List (String × Term)) : Term :=
    disj (((x.map (·.1)) ++ y.map (·.1)).eraseDups.map fun f =>
      .not (.eq ((x.lookup f).getD undefT) ((y.lookup f).getD undefT)))
  disj ([.not (.eq a.config b.config), fieldsDiffer a.context b.context] ++
    (a.deadlines.zip b.deadlines).map (fun (d, e) =>
      .or (.not (.eq d.waits e.waits)) (conj [d.waits, e.waits, .not (.eq d.time e.time)])) ++
    (a.requests.zip b.requests).map fun (r, q) =>
      .or (.not (.eq r.sent q.sent)) (conj [r.sent, q.sent, fieldsDiffer r.input q.input]))

/-- The sender of an own command: a state's `sends`, with the place in its machine's exits when it sent, or an automation. -/
inductive Sender where
  | state (chart state key : String) (exitsBefore : Nat)
  | automation (name : String)

/-- An own command that waits in the internal queue, as Sent: its sender's rank, sender, command, input and whether the input fits its schema. -/
structure Waiting where
  order : Nat
  sender : Sender
  command : String
  input : List (String × Term)
  valid : Term

/-- A work item of the internal queue, as Work. -/
inductive Job where
  /-- A deadline of a state that fires, the work that starts a deadline's message. -/
  | deadline (chart state name : String)
  /-- A machine's evaluation, with the event that it takes, if any: the term that holds when it is emitted, its key and payload. -/
  | receive (chart : String) (event : Option (Term × String × List (String × Term)))
  | react (automation : Automation) (guard : Term) (payload : List (String × Term))
  /-- The answer to a state's own command. -/
  | answered (sender : Sender) (accepted : Bool)
  /-- The answer from another service to the request of a state's activity `key`, and what its transition takes. -/
  | replied (chart state key : String) (accepted : Bool) (taken : Option (Arg × SVal))

/-- A path of a chain: the term that holds when the run takes it, and the state of the service and of its message. -/
structure Path where
  name : String
  pc : Term
  records : SRecords
  used : List (String × List Term)
  machines : List (String × Mach) := []
  outs : List Out := []
  faults : List Raised := []
  jobs : List Job := []
  round : List Waiting := []
  commands : List Waiting := []
  entered : List (String × String) := []
  steps : Nat := 0
  halted : Bool := false
  /-- That the message has steps left past chainLimit. -/
  cut : Bool := false
  gap : Term := ff
  beyond : Term := ff
  /-- The facts of the path's variables, each group under the unique name of the step that made it, which forks share. -/
  facts : List (String × Facts) := []
  fresh : Nat := 0

/-- What a chain reads of the service: the spec, each chart's model, and the time of the message. -/
structure ChainEnv where
  st : Service
  p : Program
  models : List (String × ChartModel)
  now : Term

def cfgVar (chart : String) : Term := .var s!"cfg.{chart}" .int

def ctxVar (chart field : String) : Term := valVar s!"ctx.{chart}.{field}"

/-- When the deadline `name` of `state` of `chart` is due, as a state holds it before a message. -/
def dlVar (chart state name : String) : Term := .var s!"dl.{chart}.{state}.{name}" .int

/-- The term that holds when a machine of `chart` is in a configuration with `state` active. -/
def activeIn (models : List (String × ChartModel)) (chart state : String) : Term := match models.lookup chart with
  | some m => disj ((m.configs.toList.zipIdx.filter (·.1.contains state)).map fun (_, k) =>
      Term.eq (cfgVar chart) (intLit (Int.ofNat k)))
  | none => ff

/-- The context fields of `chart` with their schemas, as propertiesWith gives them. -/
def contextProps (st : Service) (chart : String) : List (String × Value × Bool) :=
  propertiesWith ((st.schemaOf (.context (st.ref chart))).getD (.obj []))

/-- The deadlines of the states of `c`, each as its state and name. -/
def deadlinesIn (c : Service.Chart) : List (String × String) :=
  c.states.flatMap fun cs => cs.spec.deadlines.map (cs.spec.name, ·.name)

/--
The facts of the machines of a state: each chart's configuration a variable among its model's configurations, each
context field a variable that fits its schema, as the semantics checks after each assign, and each deadline due after
the message, since one due at its time would tie with it, except those in `due`, which fall due at it.
-/
def machineFacts (ce : ChainEnv) (due : List (String × String × String) := []) : Facts :=
  ce.models.foldl (fun f (c, m) =>
    let holds := (contextProps ce.st c).map fun pr => fieldHolds (ctxVar c pr.1) pr
    let deadlines := deadlinesIn m.chart
    f ++ { vars := [(s!"cfg.{c}", .int)] ++ (contextProps ce.st c).map (fun pr => (s!"ctx.{c}.{pr.1}", Ty.val)) ++
             deadlines.map fun (n, d) => (s!"dl.{c}.{n}.{d}", Ty.int),
           asserts := [.le (intLit 0) (cfgVar c), .lt (cfgVar c) (intLit m.configs.size)] ++ holds.map (·.term) ++
             deadlines.map fun (n, d) => (if due.contains (c, n, d) then Term.eq else Term.lt) ce.now (dlVar c n d),
           fit := Fit.all (holds.map (·.fit)) }) Facts.none

/-- `a ∧ b`, without the literals that decide it, so that a path that no run takes has `ff` as its term. -/
def andT (a b : Term) : Term :=
  if a == ff || b == ff then ff else if a == tt then b else if b == tt then a else .and a b

def notT (a : Term) : Term := if a == tt then ff else if a == ff then tt else .not a

namespace Path

def fork (x : Path) (c : Term) (tag : String) : Path := { x with pc := andT x.pc c, name := s!"{x.name}{tag}" }

/-- The paths of `x` after a step that ends as `o`: accepted, rejected, and halted. -/
def after (x : Path) (o : StepEnd) : Path × Path × Path :=
  let halts := o.halted.term
  (x.fork (andT o.accepted (notT halts)) "a", x.fork (andT (notT o.accepted) (notT halts)) "r",
   { x.fork halts "h" with halted := true })

/-- A name for the path's next variables, and the path that has used it. -/
def next (x : Path) : String × Path := (s!"{x.name}.{x.fresh}.", { x with fresh := x.fresh + 1 })

def mach? (x : Path) (chart : String) : Option Mach := x.machines.lookup chart

/-- The machine of `chart` with the one configuration that the path fixes, none while it can be in several. -/
def fixed? (x : Path) (chart : String) : Option (Mach × Nat) := do
  let m ← x.mach? chart
  pure (m, ← m.fixed?)

def setMach (x : Path) (chart : String) (m : Mach) : Path :=
  { x with machines := x.machines.filter (·.1 != chart) ++ [(chart, m)] }

/-- The path counting one more step of its message, cut when the step would pass chainLimit. -/
def step (x : Path) : Path := if x.steps < chainLimit then { x with steps := x.steps + 1 } else { x with cut := true }

def stopped (x : Path) : Bool := x.halted || x.cut

end Path

/--
Each machine of a state, in any configuration of its model, as machineFacts names it: each deadline of an active state
waits, and each request is the one that the state held.
-/
def startMachines (ce : ChainEnv) : List (String × Mach) :=
  ce.models.map fun (c, m) =>
    (c, { configs := List.range m.configs.size, config := cfgVar c,
          context := (contextProps ce.st c).map (fun pr => (pr.1, ctxVar c pr.1)),
          deadlines := (deadlinesIn m.chart).map fun (n, d) =>
            { state := n, name := d, waits := activeIn ce.models c n, time := dlVar c n d },
          requests := m.chart.states.flatMap fun cs => cs.activities.filterMap fun a => match a with
            | .calls .. | .sends .. =>
              if a.isOwn ce.st.service then none else some { state := cs.spec.name, key := a.key, sent := ff, input := [] }
            | _ => none })

/--
The paths in which `chart` is in each configuration where `matters` says the work can change it, and one where it is in
none of them, which leaves its configuration open.
-/
def touch (ce : ChainEnv) (x : Path) (chart : String) (matters : ChartModel → Nat → Bool) : Except String (List Path) := do
  let some mach := x.mach? chart | throw s!"no machine {chart}"
  if mach.fixed?.isSome then return [x]
  let some m := ce.models.lookup chart | throw s!"no model of {chart}"
  let (read, unread) := mach.configs.partition (matters m)
  if read.isEmpty then return [x]
  let isConfig (k : Nat) : Term := .eq mach.config (intLit (Int.ofNat k))
  let touched := read.map fun k =>
    (x.fork (isConfig k) s!"c{k}").setMach chart { mach with configs := [k], config := intLit (Int.ofNat k) }
  let rest := if unread.isEmpty then [] else
    [(x.fork (conj (read.map (notT ∘ isConfig))) "c").setMach chart { mach with configs := unread }]
  pure (touched ++ rest)

/-- The input of an activity or a react as scalar fields, or why it has none. -/
def scalarFields : SVal → Except String (List (String × Term) × Term)
  | .obj fields => pure (fields.map (fun (f, v) => (f, v.scalarOf.1)), disj (fields.map (·.2.scalarOf.2)))
  | .json fields => pure (fields.map (fun (f, j) => (f, (SVal.ofJson j).scalarOf.1)),
      disj (fields.map fun (_, j) => (SVal.ofJson j).scalarOf.2))
  | _ => throw "an input that is no object literal"

/-- That `input` fits the input schema of `target`, which its receiver otherwise rejects as invalid input. -/
def inputFits (st : Service) (target : Ir.Ref) (input : List (String × Term)) : Holds :=
  let fits := (propertiesWith ((st.schemaOf (.input target)).getD (.obj []))).map fun pr =>
    fieldHolds ((input.lookup pr.1).getD undefT) pr
  { term := conj (fits.map (·.term)), fit := Fit.all (fits.map (·.fit)) }

/--
The paths after the microstep of `chart` by the first of `edges` whose guards hold, in order, as `choose` takes it: one
path per edge, and one that halts when a guard or an assign throws; and the path where no edge is taken.
-/
def take (ce : ChainEnv) (x : Path) (chart : String) (edges : List Edge) (taken : Option (Arg × SVal)) :
    Except String (List Path × Path) := do
  let some (mach, config) := x.fixed? chart | throw s!"no fixed configuration of {chart}"
  let some model := ce.models.lookup chart | throw s!"no model of {chart}"
  let c := model.chart
  let pre : SMachine := { context := mach.context, active := model.configs[config]! }
  let env := pre.env c x.records ce.now taken
  let mut before := tt
  let mut halts := ff
  let mut out := []
  for (e, i) in edges.zipIdx do
    let (ok, halted) ← guardTerms env ((siteOf ce.st ce.p c (.guards e.transition.ref)).getD []) e.transition.guards
    halts := .or halts (andT before halted)
    let moved ← pre.move ce.st ce.p c x.records ce.now taken (some e.transition) e.exits e.entries
    let y := (x.fork (conj [before, ok, notT halted]) s!"e{i}").setMach chart
      { mach.leave e.exits with configs := [e.target], config := intLit (Int.ofNat e.target),
                                context := moved.machine.context }
    let y := { y with facts := y.facts ++ [(s!"{y.name}.fit", { Facts.none with fit := moved.fit })] }
    out := out ++ [{ y.fork moved.halted "h" with halted := true },
                   ← enterAll ce (y.fork (notT moved.halted) "") chart moved.machine e.entries]
    before := conj [before, notT ok, notT halted]
  pure (out ++ [{ x.fork halts "g" with halted := true }], x.fork (andT before (notT halts)) "z")
where
  /-- The path after `chart` entered `entries`: each deadline armed, which must fall after the message, and each state with activities queued to send them. -/
  enterAll (ce : ChainEnv) (x : Path) (chart : String) (m : SMachine) (entries : List String) : Except String Path := do
    let some model := ce.models.lookup chart | throw s!"no model of {chart}"
    let c := model.chart
    entries.foldlM (init := x) fun x n => do
      let some cs := c.state? n | pure x
      if cs.activities.any fun a => a matches .shows .. || a matches .opens .. then
        throw "a state that shows or opens"
      let armed ← cs.spec.deadlines.mapM fun d => match d.time with
        | .delay ms => pure (d.name, .add ce.now (intLit (ms.getD 0)), if ms.any (0 < ·) then ff else tt)
        | .at => do
          let some f := ((siteOf ce.st ce.p c (.deadline n d.name)).getD []).head? | throw s!"no IR of the at of {d.name}"
          let (v, err) ← seval (m.env c x.records ce.now none) [] f.body
          let (t, notScalar) := v.scalarOf
          pure (d.name, .intOf t, disj [err, notScalar, .not (.isInt t), .le (.intOf t) ce.now])
      let some mach := x.mach? chart | throw s!"no machine {chart}"
      let deadlines := mach.deadlines.map fun a => if a.state != n then a else
        match armed.find? (·.1 == a.name) with
        | some (_, time, _) => { a with waits := tt, time }
        | none => a
      let entered := if cs.activities.isEmpty then x.entered
        else x.entered.filter (· != (chart, n)) ++ [(chart, n)]
      pure { x.setMach chart { mach with deadlines } with
             gap := disj ([x.gap] ++ armed.map (andT x.pc ·.2.2)), entered }

/-- The paths of `paths` that some run can take. -/
def live (paths : List Path) : List Path := paths.filter (·.pc != ff)

/-- The paths after `x` takes `edges` and each path that moved settles by `next`. -/
def takeThen (ce : ChainEnv) (x : Path) (chart : String) (edges : List Edge) (taken : Option (Arg × SVal))
    (next : Path → Except String (List Path)) : Except String (List Path) := do
  let (moved, idle) ← take ce x chart edges taken
  pure ((← (live moved).flatMapM fun y => if y.stopped then pure [y] else next y) ++ live [idle])

/-- The edges of the model of `chart` from configuration `k` on `trigger`, from the state `source` when it is some. -/
def edgesOn (model : ChartModel) (k : Nat) (trigger : Ir.Trigger) (source : Option String := none) : List Edge :=
  model.edges.filter fun e => e.source == k && e.transition.trigger == trigger && (source.all (e.transition.source == some ·))

/-- The paths after `chart` settles: its always transitions, round by round, until none is taken (Service.settle). -/
def settle (ce : ChainEnv) (chart : String) : Nat → Path → Except String (List Path)
  | fuel, x => do
    if x.stopped then return [x]
    let some (_, config) := x.fixed? chart | return [x]
    let some model := ce.models.lookup chart | throw s!"no model of {chart}"
    let edges := edgesOn model config .always
    if edges.isEmpty then return [x]
    let (moved, idle) ← take ce x chart edges none
    let moved := live moved
    match fuel with
    | 0 => pure (moved.map ({ · with cut := true }) ++ live [idle])
    | fuel + 1 => pure ((← moved.flatMapM fun y => settle ce chart fuel y.step) ++ live [idle])

/-- The paths after each of `paths` goes on by `f`. -/
def andThen (paths : List Path) (f : Path → Except String (List Path)) : Except String (List Path) :=
  (live paths).flatMapM fun x => if x.stopped then pure [x] else f x

/-- The paths after the deadline `name` of `state` of `chart` fires, settled before and after (Service.fire). -/
def fireDeadline (ce : ChainEnv) (x : Path) (chart state name : String) : Except String (List Path) := do
  let matters (m : ChartModel) (k : Nat) := (m.configs[k]!).contains state || !(edgesOn m k .always).isEmpty
  let paths ← andThen (← touch ce x chart matters) (settle ce chart chainLimit)
  andThen paths fun x => do
    let some (mach, config) := x.fixed? chart | return [x]
    let some model := ce.models.lookup chart | throw s!"no model of {chart}"
    -- Exiting the state took its deadline away, even when the state was entered again.
    if mach.exited.contains state || !(model.configs[config]!).contains state then return [x]
    let fired := mach.deadlines.map fun d => if d.state == state && d.name == name then { d with waits := ff } else d
    takeThen ce (x.setMach chart { mach with deadlines := fired }) chart (edgesOn model config (.after name) (some state))
      none (settle ce chart chainLimit)

/--
The paths after the answer to the request of activity `key` of `state`, settled before and after (Service.handle): an
answer to an own command, whose rejection kind each path names, or one from another service that takes `reply`.
-/
def answer (ce : ChainEnv) (x : Path) (chart state key : String) (exitsBefore : Nat) (accepted : Bool)
    (reply : Option (Option (Arg × SVal)) := none) : Except String (List Path) := do
  let matters (m : ChartModel) (k : Nat) := (m.configs[k]!).contains state || !(edgesOn m k .always).isEmpty
  let paths ← andThen (← touch ce x chart matters) (settle ce chart chainLimit)
  andThen paths fun x => do
    let some (mach, config) := x.fixed? chart | return [x]
    let some model := ce.models.lookup chart | throw s!"no model of {chart}"
    if (mach.exited.drop exitsBefore).contains state || !(model.configs[config]!).contains state then return [x]
    let calls := ((model.chart.state? state).map (·.activities.any fun
      | .calls k _ => k == key
      | _ => false)).getD false
    let trigger := if calls then Ir.Trigger.calls key (if accepted then .onFulfilled else .onRejected)
      else .sends key (if accepted then .onAccepted else .onRejected)
    let (taken, x) ← match reply with
      | some taken => pure (taken, x)
      | none =>
        let (pre, x) := x.next
        let (taken, facts) ← if accepted then pure (none, Facts.none) else do
          let (t, f) ← takenOf ce.st s!"{pre}tk" [] .rejection
          -- An invalid input halts the sender before any transition (rejectedInput?), so the kind is another one.
          pure (t, { f with asserts := f.asserts ++ [.not (.eq (valVar s!"{pre}tk.kind") (.mkStr (strLit "invalid-input")))] })
        pure (taken, { x with facts := x.facts ++ [(pre, facts)] })
    takeThen ce x chart (edgesOn model config trigger (some state)) taken (settle ce chart chainLimit)

/-- The work that the events of an accepted command cause (commandWork): each machine's evaluation, then each automation's reaction. -/
def commandWork (ce : ChainEnv) (emitted : List (Term × Ir.Ref × List (String × Term))) : Except String (List Job) := do
  let machines ← ce.models.mapM fun (c, m) => do
    let received := emitted.filterMap fun (g, e, payload) =>
      (m.chart.receives.find? (·.2 == e)).map fun (key, _) => (g, key, payload)
    if 1 < received.length then throw s!"a command that emits several events that {c} receives"
    pure (Job.receive c received.head?)
  let reactions ← ce.st.automations.filterMapM fun a => do
    let received := emitted.filter (·.2.1 == a.receives)
    if 1 < received.length then throw s!"a command that emits several events that {a.name} receives"
    pure (received.head?.map fun (g, _, payload) => Job.react a g payload)
  pure (machines ++ reactions)

/-- The paths after the own command `w` runs (Service.processCommand), its answer queued for a state that sent it. -/
def runCommand (ce : ChainEnv) (x : Path) (w : Waiting) : Except String (List Path) := do
  let (names, x) := x.next
  let step ← stepWith ce.st ce.p x.records x.used w.command (SJson.ofTerms w.input) (callerTerms (.service ce.st.service))
    ce.now names
  let x := { x with facts := x.facts ++ [(names, { step.facts with fit := step.facts.fit.join step.halted.fit })] }
  -- A command rejected as invalid input is the sender's fault, which halts (rejectedInput?).
  let (ok, rejected, halted) := x.after { accepted := andT w.valid step.accepted,
                                          halted := { step.halted with term := .or (notT w.valid) step.halted.term } }
  -- An automation's rejected command is a fault that does not halt (automationAnswer), and nothing waits for it; a
  -- state's waits for the answer.
  let rejected := match w.sender with
    | .state .. => { rejected with jobs := rejected.jobs ++ [.answered w.sender false] }
    | .automation a => { rejected with faults := rejected.faults ++ step.rejections.zipIdx.map fun ((g, r), i) =>
        { id := s!"{names}f{i}", guard := andT rejected.pc g, automation := a, rejection := r } }
  let answered (accepted : Bool) : List Job := match w.sender with
    | .state .. => [.answered w.sender accepted]
    | .automation _ => []
  let ok := { ok with records := step.post, used := step.used,
                      gap := .or ok.gap (.and ok.pc step.gap), beyond := .or ok.beyond (.and ok.pc step.beyond),
                      outs := ok.outs ++ step.emitted.zipIdx.map fun (((g, e, payload) : Term × Ir.Ref × List (String × Term)), (i : Nat)) =>
                        ({ id := s!"{names}{i}", guard := .and ok.pc g, kind := .event, definition := e,
                           fields := payload } : Out) }
  let work ← commandWork ce step.emitted
  let any := disj (step.emitted.map (·.1))
  let some_ := ok.fork any "w"
  let none_ := ok.fork (notT any) "q"
  let accepted := if step.emitted.isEmpty then [{ ok with jobs := ok.jobs ++ answered true }]
    else [{ some_ with jobs := some_.jobs ++ work ++ answered true }, { none_ with jobs := none_.jobs ++ answered true }]
  pure (live ([halted, rejected] ++ accepted))

/-- The paths after the automation `a` reacts to `payload` when the guard `g` holds (Service.workBody). -/
def react (ce : ChainEnv) (x : Path) (a : Automation) (g : Term) (payload : List (String × Term)) :
    Except String (List Path) := do
  let (names, x) := x.next
  let r ← reactionOf ce.st ce.p x.records ce.now (.json (SJson.ofTerms payload)) a names
  if !r.facts.vars.isEmpty then throw s!"{a.name} creates a key, which prove does not follow in a chain yet"
  let x := { x with facts := x.facts ++ [(names, r.facts)] }
  let (fires, skips, halted) := x.after { accepted := andT g r.ending.accepted,
                                          halted := { r.ending.halted with term := andT g r.ending.halted.term } }
  let fires := { fires with gap := .or fires.gap (.and fires.pc r.gap) }
  let fired := if a.sends.isOwn ce.st.service then
      { fires with round := fires.round ++ [({ order := a.order, sender := .automation a.name, command := a.sends.ref.name,
                                               input := r.input, valid := r.valid } : Waiting)] }
    else { fires with outs := fires.outs ++ [({ id := names, guard := fires.pc, kind := .command,
                                                definition := a.sends.ref, fields := r.input } : Out)] }
  pure (live [fired, skips, halted])

/-- The paths after a machine's evaluation: settled, then the event it takes, if any, then settled (Service.receiveWork). -/
def receive (ce : ChainEnv) (x : Path) (chart : String) (event : Option (Term × String × List (String × Term))) :
    Except String (List Path) := do
  let matters (m : ChartModel) (k : Nat) :=
    !(edgesOn m k .always).isEmpty || event.any fun (_, key, _) => !(edgesOn m k (.on key)).isEmpty
  let paths ← andThen (← touch ce x chart matters) (settle ce chart chainLimit)
  match event with
  | none => pure paths
  | some (g, key, payload) =>
    andThen paths fun x => do
      let some (_, config) := x.fixed? chart | return [x]
      let some model := ce.models.lookup chart | throw s!"no model of {chart}"
      let taken := some (Arg.payload, SVal.json (SJson.ofTerms payload))
      let dispatched ← takeThen ce (x.fork g "d") chart (edgesOn model config (.on key)) taken
        (settle ce chart chainLimit)
      pure (dispatched ++ live [x.fork (notT g) "u"])

/--
The path with the input of the activity `a` of state `n` of `chart`, whose configuration the path fixes, computed as
Service.request computes it: a throw, or an input that is no object of scalars, leaves what the encoding holds.
-/
def activityInput (ce : ChainEnv) (x : Path) (chart n : String) (a : Service.Activity) :
    Except String (Path × List (String × Term)) := do
  let some (mach, config) := x.fixed? chart | throw s!"no fixed configuration of {chart}"
  let some model := ce.models.lookup chart | throw s!"no model of {chart}"
  let c := model.chart
  let m : SMachine := { context := mach.context, active := model.configs[config]! }
  let keyword := match a with
    | .calls .. => "calls"
    | _ => "sends"
  let (input, notScalar) ← match ((siteOf ce.st ce.p c (.input n keyword a.key)).getD []).head? with
    | some f => do
      let (v, err) ← seval (m.env c x.records ce.now none) [] f.body
      let (fields, notScalar) ← scalarFields v
      pure (fields, .or err notScalar)
    | none => pure ([], ff)
  pure ({ x with gap := .or x.gap (.and x.pc notScalar) }, input)

/-- The path with the fit of whether `input` fits the input schema of `a`'s target, and the own command that waits for it. -/
def ownWaiting (ce : ChainEnv) (x : Path) (order : Nat) (sender : Sender) (a : Service.Activity)
    (input : List (String × Term)) : Path × Waiting :=
  let fits := inputFits ce.st a.ref input
  let (key, x) := x.next
  ({ x with facts := x.facts ++ [(key, { Facts.none with fit := fits.fit })] },
   { order, sender, command := a.ref.name, input, valid := fits.term })

/-- The paths after the states that the message entered send their activities (Service.sendEntered), as one step. -/
def sendEntered (ce : ChainEnv) (x : Path) : Except String Path := do
  let charts := x.entered.map (·.1) |>.eraseDups
  let ordered := charts.flatMap fun c => match ce.models.lookup c with
    | some m => (m.chart.states.map (·.spec.name)).filterMap fun n => if x.entered.contains (c, n) then some (c, n) else none
    | none => []
  ordered.foldlM (init := { x with entered := [] }) fun x (chart, n) => do
    let some (mach, config) := x.fixed? chart | throw s!"no fixed configuration of {chart}"
    let some model := ce.models.lookup chart | pure x
    if !(model.configs[config]!).contains n then return x
    let c := model.chart
    let some cs := c.state? n | pure x
    cs.activities.foldlM (init := x) fun x a => do
      let (x, input) ← activityInput ce x chart n a
      if a.isOwn ce.st.service then
        let (x, w) := ownWaiting ce x c.order (.state chart n a.key mach.exited.length) a input
        pure { x with round := x.round ++ [w] }
      else
        let kind := match a with
          | .calls .. => OutKind.query
          | _ => .command
        let (id, x) := x.next
        let some mach := x.mach? chart | throw s!"no machine {chart}"
        let requests := mach.requests.map fun r =>
          if r.state == n && r.key == a.key then { r with sent := tt, input } else r
        pure { x.setMach chart { mach with requests } with
               outs := x.outs ++ [{ id, guard := x.pc, kind, definition := a.ref, fields := input }] }

/-- `ws` in sender-definition order, equal ranks in sending order (sortSent). -/
def sortWaiting (ws : List Waiting) : List Waiting := ws.mergeSort fun a b => decide (a.order ≤ b.order)

/-- The path after the next item of its internal queue runs, as Service.drain takes it: work in arrival order, then own commands, then the activities of the entered states, each a step. -/
def stepQueue (ce : ChainEnv) (x : Path) : Except String (List Path) := do
  match x.jobs with
  | job :: rest =>
    let x := { x with jobs := rest }.step
    if x.cut then return [x]
    match job with
    | .deadline chart state name => fireDeadline ce x chart state name
    | .receive chart event => receive ce x chart event
    | .react a g payload => react ce x a g payload
    | .answered (.state chart state key exitsBefore) accepted => answer ce x chart state key exitsBefore accepted
    | .answered (.automation _) _ => pure [x]
    | .replied chart state key accepted taken => answer ce x chart state key 0 accepted (some taken)
  | [] =>
    match x.commands ++ sortWaiting x.round with
    | w :: rest =>
      let x := { x with commands := rest, round := [] }.step
      if x.cut then return [x]
      runCommand ce x w
    | [] =>
      let x := x.step
      if x.cut then return [x]
      pure [← sendEntered ce x]

def Path.idle (x : Path) : Bool := x.jobs.isEmpty && x.commands.isEmpty && x.round.isEmpty && x.entered.isEmpty

def Sender.shape : Sender → String
  | .state c s k e => s!"state {c} {s} {k} {e}"
  | .automation a => s!"automation {a}"

def Waiting.shape (w : Waiting) : String := s!"{w.order} {w.sender.shape} {w.command} {w.input.map (·.1)}"

def Job.shape : Job → String
  | .deadline c s n => s!"deadline {c} {s} {n}"
  | .receive c e =>
    let fields : List String := match e with
      | some (_, _, p) => p.map Prod.fst
      | none => []
    s!"receive {c} {e.map (·.2.1)} {fields}"
  | .react a _ p => s!"react {a.name} {p.map (·.1)}"
  | .answered s ok => s!"answered {s.shape} {ok}"
  | .replied c s k ok _ => s!"replied {c} {s} {k} {ok}"

/-- The charts whose states the internal queue names: a state that sent an own command, or entered with activities to send. -/
def Path.pinned (x : Path) : List String :=
  let sender : Sender → List String
    | .state c .. => [c]
    | .automation _ => []
  x.entered.map (·.1) ++ (x.round ++ x.commands).flatMap (sender ·.sender) ++
    x.jobs.flatMap fun
      | .answered s _ => sender s
      | .replied c .. => [c]
      | _ => []

/--
What two paths must share to be joined: whether they halted or were cut, each machine's exits, the configuration of
each machine whose states the queue names, and the shape of the internal queue.
-/
def Path.control (x : Path) : String :=
  if x.halted || x.cut then s!"{x.halted} {x.cut}" else
  let pinned := x.pinned
  let machines := (x.machines.map fun (c, m) => (c, if pinned.contains c then m.fixed? else none, m.exited)).mergeSort
    fun a b => decide (a.1 ≤ b.1)
  s!"{machines} {if x.idle then 0 else x.steps} {x.jobs.map (·.shape)} {x.round.map (·.shape)} " ++
    s!"{x.commands.map (·.shape)} {x.entered}"

def iteFields (c : Term) (a b : List (String × Term)) : List (String × Term) :=
  a.map fun (f, t) => (f, iteT c t ((b.lookup f).getD t))

def Waiting.join (c : Term) (a b : Waiting) : Waiting :=
  { a with input := iteFields c a.input b.input, valid := iteT c a.valid b.valid }

def Job.join (c : Term) : Job → Job → Job
  | .receive ch (some (g, k, p)), .receive _ (some (h, _, q)) => .receive ch (some (iteT c g h, k, iteFields c p q))
  | .react a g p, .react _ h q => .react a (iteT c g h) (iteFields c p q)
  | j, _ => j

/-- `a` with `b` joined in, which has the same control and a disjoint term: each datum `b`'s where `b`'s term holds. -/
def Path.absorb (a b : Path) : Path :=
  let c := b.pc
  let pick (x y : Term) : Term := iteT c y x
  let keys : Std.HashSet String := a.facts.foldl (fun s (k, _) => s.insert k) ∅
  -- An out line's guard holds only on the paths that wrote it, so one from before the paths split is kept once.
  let ids : Std.HashSet String := a.outs.foldl (fun s o => s.insert o.id) ∅
  let raised : Std.HashSet String := a.faults.foldl (fun s f => s.insert f.id) ∅
  { a with pc := Term.or a.pc b.pc, records := SRecords.ite c b.records a.records,
           used := a.used.map fun (e, us) => (e, (us.zip ((b.used.lookup e).getD [])).map fun (x, y) => pick x y),
           machines := a.machines.map fun (m, x) => (m, Mach.ite c ((b.mach? m).getD x) x),
           outs := a.outs ++ b.outs.filter (!ids.contains ·.id),
           faults := a.faults ++ b.faults.filter (!raised.contains ·.id),
           jobs := (b.jobs.zip a.jobs).map fun (y, x) => y.join c x,
           round := (b.round.zip a.round).map fun (y, x) => y.join c x,
           commands := (b.commands.zip a.commands).map fun (y, x) => y.join c x,
           gap := Term.or a.gap b.gap, beyond := Term.or a.beyond b.beyond,
           facts := a.facts ++ b.facts.filter (!keys.contains ·.1) }

/--
One path for `x` and `rest`, which have the same control and disjoint terms. Each datum that differs among them is
a variable, so that later joins nest variables and the terms stay small; one that does not stays as it is.
-/
def Path.joinAll (x : Path) (rest : List Path) : Path :=
  if rest.isEmpty then x else
  let j := rest.foldl Path.absorb x
  let name := x.name ++ "m"
  let ((joined, machines), defs) := (do
    let joined ← ({ records := j.records, used := j.used } : Stepped).named name
    let machines ← j.machines.mapM fun (m, x) => do
      let fields (p : String) (fs : List (String × Term)) : Named (List (String × Term)) :=
        fs.mapM fun (f, t) => do pure (f, ← nameValue s!"{p}.{f}" t)
      pure (m, { x with config := ← nameAs s!"{name}.cfg.{m}" .int x.config,
                        context := ← fields s!"{name}.ctx.{m}" x.context,
                        deadlines := ← x.deadlines.mapM fun d => do
                          let p := s!"{name}.dl.{m}.{d.state}.{d.name}"
                          pure { d with waits := ← nameAs s!"{p}.waits" .bool d.waits, time := ← nameAs p .int d.time },
                        requests := ← x.requests.mapM fun r => do
                          let p := s!"{name}.rq.{m}.{r.state}.{r.key}"
                          pure { r with sent := ← nameAs p .bool r.sent, input := ← fields p r.input } })
    pure (joined, machines) : Named (Stepped × List (String × Mach))).run []
  let named : Facts := { vars := defs.map fun (x, ty, _) => (x, ty),
                         asserts := defs.map fun (x, ty, t) => .eq (.var x ty) t, fit := .exact }
  { j with name, records := joined.records, used := joined.used, machines, facts := j.facts ++ [(name, named)] }

/-- `paths` with the paths of equal control joined, so that the steps after them are followed once. -/
def merge (paths : List Path) : List Path :=
  let groups := paths.foldl (fun (acc : Array (String × Path × Array Path)) x =>
    let k := x.control
    match acc.findIdx? (·.1 == k) with
    | some i => acc.modify i fun (k, first, rest) => (k, first, rest.push x)
    | none => acc.push (k, x, #[])) #[]
  groups.toList.map fun (_, first, rest) => first.joinAll rest.toList

/-- The paths after the internal queues of `paths` run out (Service.drain), at most `fuel` steps, the paths of equal control joined after each step. -/
def drain (ce : ChainEnv) : Nat → List Path → Except String (List Path)
  | 0, paths => pure (paths.map fun x => if x.stopped || x.idle then x else { x with cut := true })
  | fuel + 1, paths => do
    let (rest, busy) := paths.partition fun x => x.stopped || x.idle
    if busy.isEmpty then return paths
    let stepped := rest ++ live (← busy.flatMapM (stepQueue ce))
    let merged := merge stepped
    drain ce fuel merged

/-- How a message can start: the term that holds when it does, and its first work, or that the service halts on it. -/
structure Start where
  cond : Term := tt
  jobs : List Job := []
  halts : Bool := false

/--
The paths after a message that starts in one of `starts`, counted from no step. Of the states each machine exited, only
those in `watched` matter after the message: a later deadline of them no longer fires, and a later answer to their
request is stale.
-/
def message (ce : ChainEnv) (watched : List (String × String)) (paths : List Path) (starts : List Start) :
    Except String (List Path) := do
  let (stopped, going) := paths.partition (·.stopped)
  let begun := live (going.flatMap fun x => starts.zipIdx.map fun (b, i) =>
    { x.fork b.cond s!"s{i}" with jobs := b.jobs, steps := 0, halted := b.halts })
  let ended := (← drain ce (2 * chainLimit + 2) begun).map fun x =>
    { x with machines := x.machines.map fun (c, m) => (c, { m with exited := m.exited.filter fun n => watched.contains (c, n) }) }
  pure (merge (stopped ++ ended))

/-- The work that an event from another service causes on arrival (Service.deliver): each machine that receives it, then each automation. -/
def arrivalWork (ce : ChainEnv) (event : Ir.Ref) (payload : List (String × Term)) : List Job :=
  ce.models.filterMap (fun (c, m) => (m.chart.receives.find? (·.2 == event)).map fun (key, _) =>
      Job.receive c (some (tt, key, payload))) ++
    (ce.st.automations.filter (·.receives == event)).map fun a => .react a tt payload

/-- The facts of `paths`, each group once, since forks share the groups from before they split. -/
def factsOf (paths : List Path) : Facts :=
  (paths.foldl (fun (seen, f) x => x.facts.foldl (fun (seen, f) (k, g) =>
    if seen.contains k then (seen, f) else (seen.insert k, f ++ g)) (seen, f)) ((∅ : Std.HashSet String), Facts.none)).2

/-- What an order of two messages ends with, over all its paths. -/
structure Ending where
  records : SRecords
  /-- Each machine's state, which decides the service's later messages as records do. -/
  machines : List (String × Mach)
  halted : Term
  outs : List Out
  faults : List Raised
  gap : Term
  beyond : Term
  /-- That a message of the order has steps left past chainLimit. -/
  cut : Term
  facts : Facts

/-- The items that `of` gives of `paths`, each `id` once, since forks share the items from before they split. -/
def onceEach {α : Type} (paths : List Path) (of : Path → List α) (id : α → String) : List α :=
  (paths.foldl (fun (seen, items) x => (of x).foldl (fun (seen, items) i =>
    if seen.contains (id i) then (seen, items) else (seen.insert (id i), items ++ [i])) (seen, items))
    ((∅ : Std.HashSet String), ([] : List α))).2

def Ending.of (start : SRecords) (machines : List (String × Mach)) (paths : List Path) : Ending :=
  let finished := paths.filter (!·.cut)
  let mach (x : Path) (c : String) (m : Mach) : Mach := (x.mach? c).getD m
  { records := finished.foldr (fun x r => .ite x.pc x.records r) start,
    machines := machines.map fun (c, m) => (c, finished.foldr (fun x t => Mach.ite x.pc (mach x c m) t) m),
    halted := disj ((finished.filter (·.halted)).map (·.pc)),
    outs := onceEach finished (·.outs) (·.id),
    faults := onceEach finished (·.faults) (·.id),
    gap := disj (finished.map fun x => .and x.pc x.gap),
    beyond := disj (finished.map fun x => .and x.pc x.beyond),
    cut := disj ((paths.filter (·.cut)).map (·.pc)),
    facts := factsOf paths }

/-- How many out lines of `outs` equal `o` where they are written. -/
def countOf (outs : List Out) (o : Out) : Term :=
  let same (x : Out) : Term :=
    let names := (x.fields.map (·.1) ++ o.fields.map (·.1)).eraseDups
    conj (names.map fun f => .eq ((x.fields.lookup f).getD undefT) ((o.fields.lookup f).getD undefT))
  (outs.filter fun x => x.kind == o.kind && x.definition == o.definition).foldl
    (fun n x => .add n (.ite (.and x.guard (same x)) (intLit 1) (intLit 0))) (intLit 0)

/-- How many faults of `faults` are `f`'s fault where they are raised. -/
def raisedCount (faults : List Raised) (f : Raised) : Term :=
  (faults.filter fun x => x.automation == f.automation && x.rejection == f.rejection).foldl
    (fun n x => .add n (.ite x.guard (intLit 1) (intLit 0))) (intLit 0)

/--
That two orders end differently: one halts and the other does not, or neither halts and their records, machines
(Mach.differ), out lines or raised faults differ.
-/
def Ending.differ (a b : Ending) : Term :=
  let outsDiffer := disj ((a.outs ++ b.outs).map fun o => .and o.guard (.not (.eq (countOf a.outs o) (countOf b.outs o))))
  let faultsDiffer := disj ((a.faults ++ b.faults).map fun f =>
    .and f.guard (.not (.eq (raisedCount a.faults f) (raisedCount b.faults f))))
  let machinesDiffer := disj ((a.machines.zip b.machines).map fun ((_, c), (_, d)) => c.differ d)
  .or (.not (.eq a.halted b.halted))
    (conj [.not a.halted, .not b.halted, disj [.not (a.records.same b.records), machinesDiffer, outsDiffer, faultsDiffer]])

/-- A deadline of a state of a chart. -/
structure DeadlineRef where
  chart : String
  state : String
  name : String
deriving DecidableEq

/-- A message from another service that can arrive at the service: an event that it receives, or an answer to a request that it sends. -/
inductive Arrival where
  | event (ref : Ir.Ref)
  | answer (target : Ir.Ref)
deriving DecidableEq

def Arrival.ref : Arrival → Ir.Ref
  | .event r | .answer r => r

/--
Two messages that no line orders: two deadlines due at one time, which the clock fires one after the other, or two
messages that arrive at once, which the network delivers in either order.
-/
inductive Tie where
  | deadlines (a b : DeadlineRef)
  | arrivals (a b : Arrival)

/-- Whether state `n` of `c` lies inside a map state, so that each copy of the map has its own deadlines. -/
def inMap (c : Service.Chart) (n : String) : Bool :=
  (((c.state? n).map (·.spec.path.dropLast)).getD []).any fun a => (c.state? a).any (·.spec.kind == .map)

/-- Who waits for the answer to a request to another service: a state's activity, or an automation. -/
inductive AnswerTo where
  | state (chart state key : String)
  | automation (name : String)

/-- The one requester in `st` of requests to `target`, or why there is none or more than one. -/
def requesterOf (st : Service) (target : Ir.Ref) : Except String AnswerTo := do
  let states := st.charts.flatMap fun c => c.states.flatMap fun cs => cs.activities.filterMap fun
    | .calls k r | .sends k r => if r == target then some (AnswerTo.state c.name cs.spec.name k) else none
    | _ => none
  let automations := (st.automations.filter (·.sends.ref == target)).map (AnswerTo.automation ·.name)
  match states ++ automations with
  | [r] => pure r
  | [] => throw s!"no requester of {target.service}.{target.name}"
  | _ => throw s!"an answer to {target.service}.{target.name}, which several states or automations request, so its requester is unknown"

/-- Whether state `a` of chart `ca` and state `b` of chart `cb` can be active at once: in two charts, or in one configuration of one chart. -/
def activeTogether (st : Service) (ca a cb b : String) : Bool :=
  if ca != cb then true
  else match (st.charts.find? (·.name == ca)).map ChartModel.of with
    | some (.ok m) => m.configs.any fun k => k.contains a && k.contains b
    | _ => true

def deadlinesOf (st : Service) : List DeadlineRef :=
  st.charts.flatMap fun c => c.states.flatMap fun cs =>
    cs.spec.deadlines.map fun d => ({ chart := c.name, state := cs.spec.name, name := d.name } : DeadlineRef)

/-- The messages from other services that can arrive at `st`: events that it receives, and answers to its requests. -/
def arrivalsOf (st : Service) : List Arrival :=
  let events := (st.receives.filter fun e =>
    st.automations.any (·.receives == e) || st.charts.any (·.receives.any (·.2 == e))).map Arrival.event
  let requested := (st.charts.flatMap fun c => c.states.flatMap (·.activities)).filterMap (fun a => match a with
      | .calls _ r | .sends _ r => if r.service != st.service then some (Arrival.answer r) else none
      | _ => none) ++
    (st.automations.filter (!·.sends.isOwn st.service)).map (Arrival.answer ·.sends.ref)
  (events ++ requested).eraseDups

/-- The pairs of `xs`, each once, each item with itself too. -/
def pairsWithSelf {α : Type} (xs : List α) : List (α × α) := xs.zipIdx.flatMap fun (a, i) => (xs.drop i).map (a, ·)

/--
The ties of `st`, each pair once: two deadlines that can be armed together (one deadline with itself only inside a map,
whose copies each arm it), and two arrivals, one with itself among them unless a state waits for it.
-/
def tiesOf (st : Service) : List Tie :=
  let together (a b : DeadlineRef) : Bool :=
    if a == b then (st.charts.find? (·.name == a.chart)).any (inMap · a.state)
    else activeTogether st a.chart a.state b.chart b.state
  -- A state waits for one answer at a time: entering it again makes the earlier request stale.
  let twice : Arrival → Bool
    | .answer r => match requesterOf st r with
      | .ok (.automation _) => true
      | _ => false
    | .event _ => true
  ((pairsWithSelf (deadlinesOf st)).filter (fun (a, b) => together a b)).map (fun (a, b) => Tie.deadlines a b) ++
    ((pairsWithSelf (arrivalsOf st)).filter fun (a, b) => a != b || twice a).map fun (a, b) => .arrivals a b

/--
What a message from another service carries, each a variable named after the message: an event's payload; or an
answer, whether it accepts, its output, and its rejection's kind.
-/
structure Given where
  fields : List (String × Term) := []
  accepted : Term := tt
  kind : Term := undefT

/-- A message from another service as a tie compares it: how it starts, what the state must hold for it, and what it carries. -/
structure Arriving where
  starts : List Start
  pre : Term := tt
  watched : List (String × String) := []
  given : Given
  facts : Facts

/--
The arrival `a` with its variables named after `x`. An answer arrives for a request that waits: the requesting state is
active, as leaving it makes the request stale. A rejection as invalid input, from a service that parsed the input
itself, is the requester's fault (rejectedInput?), on which the service halts. Any other rejection but `unavailable` of
an automation's command is a fault that does not halt (automationAnswer), which both orders raise alike, since each
takes the same answer.
-/
def arrivingOf (ce : ChainEnv) (a : Arrival) (x : String) : Except String Arriving := do
  let st := ce.st
  match a with
  | .event e =>
    let (fields, facts) := payloadOf e
    pure { starts := [{ jobs := arrivalWork ce e fields }], given := { fields }, facts }
  | .answer target =>
    let requester ← requesterOf st target
    let accepted := Term.var s!"{x}.accepted" .bool
    let kind := valVar s!"{x}.kind"
    let listed := (st.structure.rejectionKinds st.service target).map fun k => match ToValue.toValue k with
      | .str t => t
      | v => v.canonical
    let invalid := !st.structure.isAssumed target
    let kinds := listed ++ if invalid then ["invalid-input"] else []
    let isKind (k : String) : Term := .eq kind (.mkStr (strLit k))
    let rejection : Option (Arg × SVal) := some (.rejection, .json (SJson.ofTerms [("kind", kind)]))
    let output := if (st.schemaOf (.output target)).isSome then payloadOfSchema (.output target) else ([], Facts.none)
    let facts := { output.2 with vars := output.2.vars ++ [(s!"{x}.accepted", .bool), (s!"{x}.kind", .val)],
                                 asserts := output.2.asserts ++ [.or accepted (disj (kinds.map isKind))] }
    let outputTaken : Option (Arg × SVal) :=
      if output.1.isEmpty then none else some (.output, .json (SJson.ofTerms output.1))
    let faulted := if invalid then isKind "invalid-input" else ff
    let given : Given := { fields := output.1, accepted, kind }
    match requester with
    | .state chart state key =>
      pure { starts := [{ cond := accepted, jobs := [.replied chart state key true outputTaken] },
                        { cond := conj [.not accepted, .not faulted], jobs := [.replied chart state key false rejection] },
                        { cond := .and (.not accepted) faulted, halts := true }],
             pre := activeIn ce.models chart state, watched := [(chart, state)], given, facts }
    | .automation _ =>
      pure { starts := [{ cond := .not (.and (.not accepted) faulted) },
                        { cond := .and (.not accepted) faulted, halts := true }],
             given, facts }
where
  payloadOfSchema (schema : Schema) : List (String × Term) × Facts :=
    let props := propertiesWith ((ce.st.schemaOf schema).getD (.obj []))
    let terms := props.map fun pr => (pr.1, propertyVar s!"{x}.{pr.1}" pr)
    let holds := props.map fun pr => fieldHolds (((terms.lookup pr.1).map (·.1)).getD undefT) pr
    (terms.map fun (f, t, _) => (f, t),
     { vars := terms.flatMap (·.2.2), asserts := holds.map (·.term), fit := Fit.all (holds.map (·.fit)) })
  payloadOf (e : Ir.Ref) := payloadOfSchema (.payload e)

/--
What a sender's command takes in a pair's orders: the payload of the event that its automation reacts to, from which
the automation computes the input; an input of its own; or the input that its state computes when it enters.
-/
inductive Sending where
  | payload (fields : List (String × Term))
  | input (fields : List (String × Term))
  | computed

/-- A tie's two orders from one state: the first message then the second, and the second then the first. -/
structure TieOrders where
  facts : Facts
  /-- What the state must hold for the tie: every machine settled, each deadline's state active, and each requester of an
  answer. -/
  pre : Term
  first : Ending
  second : Ending
  /-- What each arriving message carries, none for a deadline. -/
  given : List Given
  /-- What each of two own commands takes, none for a tie. -/
  sendings : List Sending := []

def tieOrders (st : Service) (p : Program) (pre : SRecords) (used : List (String × List Term)) (now : Term) (tie : Tie) :
    Except String TieOrders := do
  let models ← st.charts.mapM fun c => do
    match ChartModel.of c with
    | .ok m => pure (c.name, m)
    | .error why => throw s!"{c.name}: {why}"
  let ce : ChainEnv := { st, p, models, now }
  -- A tie starts between messages, when every machine has settled.
  let settled := conj (models.flatMap fun (c, m) =>
    m.transient.map fun k => Term.not (.eq (cfgVar c) (intLit (Int.ofNat k))))
  let orders (watched : List (String × String)) (a b : List Start) : Except String (Ending × Ending) := do
    let run (name : String) (x y : List Start) : Except String Ending := do
      let paths ← message ce watched [{ name, pc := tt, records := pre, used, machines := startMachines ce }] x
      pure (Ending.of pre (startMachines ce) (← message ce watched paths y))
    pure (← run "o1" a b, ← run "o2" b a)
  match tie with
  | .deadlines a b =>
    let (first, second) ← orders [(a.chart, a.state), (b.chart, b.state)]
      [{ jobs := [.deadline a.chart a.state a.name] }] [{ jobs := [.deadline b.chart b.state b.name] }]
    pure { facts := machineFacts ce [(a.chart, a.state, a.name), (b.chart, b.state, b.name)] ++ first.facts ++ second.facts,
           pre := conj [settled, activeIn models a.chart a.state, activeIn models b.chart b.state], first, second,
           given := [] }
  | .arrivals a b =>
    let ga ← arrivingOf ce a "pa"
    let gb ← arrivingOf ce b "pb"
    let (first, second) ← orders (ga.watched ++ gb.watched) ga.starts gb.starts
    pure { facts := machineFacts ce ++ ga.facts ++ gb.facts ++ first.facts ++ second.facts,
           pre := conj [settled, ga.pre, gb.pre], first, second, given := [ga.given, gb.given] }

/-- An own command's sender: an automation, or the activity `key` of `state` of the chart `chart`. -/
inductive SenderRef where
  | automation (name : String)
  | activity (chart state key : String)
deriving DecidableEq

/-- The senders of `st`'s own commands, in definition order. -/
def sendersOf (st : Service) : List SenderRef :=
  (st.automations.filter (·.sends.isOwn st.service)).map (.automation ·.name) ++
    st.charts.flatMap fun c => c.states.flatMap fun cs =>
      (cs.activities.filter (·.isOwn st.service)).map (.activity c.name cs.spec.name ·.key)

/--
Whether only a deadline that fires enters state `n` of `c`: no start or entry enters it as an initial state, and every
transition into it or a state inside it fires on a deadline. Each deadline fires as its own message.
-/
def deadlineEntered (c : Service.Chart) (n : String) : Bool :=
  let path := ((c.state? n).map (·.spec.path)).getD []
  let inside (t : String) := (c.state? t).any fun s => path.isPrefixOf s.spec.path
  c.initial != n && !c.states.any (·.spec.initial == some n) && !c.states.any (·.spec.type matches .history) &&
    (c.on ++ c.states.flatMap (·.transitions)).all fun t => match t.target, t.trigger with
      | some _, .after _ => true
      | some target, _ => !inside target
      | none, _ => true

/-- The events that `e` emits inside a Bag, such as `records.Task.map((t) => emit(...))`, whose events are one group. -/
partial def groupedEvents : Expr → List Ir.Ref
  | .map .bag _ _ body => emitted body
  | e => (Expr.children e).flatMap groupedEvents
where
  emitted : Expr → List Ir.Ref
    | .emit event _ => [event]
    | e => (Expr.children e).flatMap emitted

/-- The events that `e` emits, once for each emit. -/
partial def emitsOf : Expr → List Ir.Ref
  | .emit event _ => [event]
  | e => (Expr.children e).flatMap emitsOf

/--
Whether the event `e` can occur twice in one message of `st`, and whether together with `f`: a command emits it inside a
Bag or at two emits, or it and `f` both; or an own command emits it, which the steps of any message can send.
-/
def occurs (st : Service) (e f : Ir.Ref) : Bool :=
  let decides := st.commands.filterMap fun c =>
    (st.structure.program.decide.find? (·.definition == st.ref c)).map (c, ·.body)
  let sent := (sendersOf st).filterMap fun
    | .automation a => (st.automations.find? (·.name == a)).map (·.sends.ref.name)
    | .activity c n k => (((st.charts.find? (·.name == c)).bind (·.state? n)).bind
        (·.activities.find? (·.key == k))).map (·.ref.name)
  decides.any (fun (c, body) =>
    let emits := emitsOf body
    (e == f && ((groupedEvents body).contains e || 1 < emits.count e)) || (e != f && emits.contains e && emits.contains f) ||
      (sent.contains c && (emits.contains e || emits.contains f)))

/--
Whether the own commands of `a` and `b` can wait in one round of the internal queue with no cause chain between them.
Two automations can when they react to one event, or when their events can occur in one message (`occurs`), each reacting to an event of a command of
the round, since no line orders two commands' events; an automation and a state's activity can unless only a deadline
enters the state, whose message every step of comes from. Two states' activities can when the states can be active together, except two
states that only deadlines enter, each its own message, and one state with itself, except inside a map.
-/
def shareRound (st : Service) : SenderRef → SenderRef → Bool
  | .automation a, .automation b => match st.automations.find? (·.name == a), st.automations.find? (·.name == b) with
    | some x, some y => (a != b && x.receives == y.receives) || occurs st x.receives y.receives
    | _, _ => true
  | .automation _, .activity c n _ | .activity c n _, .automation _ => !byDeadline c n
  | .activity ca a k, .activity cb b l =>
    if (ca != cb || (a == b && k == l)) && byDeadline ca a && byDeadline cb b then false
    else if ca == cb && a == b && k == l then (st.charts.find? (·.name == ca)).any (inMap · a)
    else activeTogether st ca a cb b
where
  byDeadline (c n : String) : Bool := (st.charts.find? (·.name == c)).any (deadlineEntered · n)

/--
Two steps that no line orders: two own commands that can wait in one round; two messages that tie; a deadline and a
message from another service that arrives when it is due; or the events of one event group of `command` that one
machine takes.
-/
inductive Unordered where
  | sends (a b : SenderRef)
  | tie (tie : Tie)
  | deadlineArrival (deadline : DeadlineRef) (arrival : Arrival)
  | group (command chart : String)

/--
Every pair of steps of `st` that no line orders, each once, so that no order passes unnamed: prove compares each one or
names it undecided.
-/
def unorderedOf (st : Service) : List Unordered :=
  let sends := ((pairsWithSelf (sendersOf st)).filter fun (a, b) => shareRound st a b).map fun (a, b) => Unordered.sends a b
  let waits (d : DeadlineRef) : Arrival → Bool
    | .answer r => match requesterOf st r with
      | .ok (.state chart state _) => activeTogether st d.chart d.state chart state
      | _ => true
    | .event _ => true
  let instants := (deadlinesOf st).flatMap fun d => ((arrivalsOf st).filter (waits d)).map (Unordered.deadlineArrival d)
  let groups := st.commands.flatMap fun c =>
    let events := (((st.structure.program.decide.find? (·.definition == st.ref c)).map (groupedEvents ·.body)).getD [])
    st.charts.filterMap fun ch => if ch.receives.any (events.contains ·.2) then some (Unordered.group c ch.name) else none
  sends ++ (tiesOf st).map .tie ++ instants ++ groups

/-- The variables of an object of `schema`, each named after `x`, and the facts that they fit it. -/
def objectVars (st : Service) (schema : Schema) (x : String) : List (String × Term) × Facts :=
  let props := propertiesWith ((st.schemaOf schema).getD (.obj []))
  let terms := props.map fun pr => (pr.1, propertyVar s!"{x}.{pr.1}" pr)
  let holds := props.map fun pr => fieldHolds (((terms.lookup pr.1).map (·.1)).getD undefT) pr
  (terms.map fun (f, t, _) => (f, t),
   { vars := terms.flatMap (·.2.2), asserts := holds.map (·.term), fit := Fit.all (holds.map (·.fit)) })

/-- A sender as a pair runs it: what the state must hold, the facts, what its command takes, and its waiting command on a path. -/
structure SenderRun where
  pre : Term := tt
  facts : Facts := Facts.none
  sending : Sending
  waiting : Path → Except String (Path × Waiting)

/--
The two orders of the own commands of `a` and `b`, waiting in one round, from one state: each command runs, then the
work it causes, as Service.drain takes them, to the end of the message. When a third own command can wait in the round,
the two may run after it and its work, from a state that their inputs were not computed from: an automation's reaction
then reads any records within the bounds, and a state's activity sends any input of its schema. Otherwise each input
comes from the state, as the automation's reaction or the state's activity computes it, and the state of an activity
is active.
-/
def sendOrders (st : Service) (p : Program) (pre : SRecords) (used : List (String × List Term)) (now : Term)
    (a b : SenderRef) : Except String TieOrders := do
  let models ← st.charts.mapM fun c => do
    match ChartModel.of c with
    | .ok m => pure (c.name, m)
    | .error why => throw s!"{c.name}: {why}"
  let ce : ChainEnv := { st, p, models, now }
  let settled := conj (models.flatMap fun (c, m) =>
    m.transient.map fun k => Term.not (.eq (cfgVar c) (intLit (Int.ofNat k))))
  let third := (sendersOf st).any fun c => c != a && c != b && shareRound st c a && shareRound st c b
  let runOf (s : SenderRef) (tag : String) : Except String SenderRun := do
    match s with
    | .automation name =>
      let some auto := st.automations.find? (·.name == name) | throw s!"no automation {name}"
      let waiting (input : List (String × Term)) (valid : Term) : Waiting :=
        { order := auto.order, sender := .automation name, command := auto.sends.ref.name, input, valid }
      let (payload, payloadFacts) := objectVars st (.payload auto.receives) tag
      if third then
        -- The reaction read the records of an earlier state of the round, any records within the bounds.
        let read := SRecords.named st (Ir.createsOf st.structure.bounds st.service) s!"{tag}.rd"
        let r ← reactionOf st p read now (.json (SJson.ofTerms payload)) auto s!"{tag}.r"
        if !r.facts.vars.isEmpty then throw s!"{auto.name} creates a key in a round with a third own command"
        let w := waiting r.input r.valid
        pure { pre := r.ending.accepted, facts := payloadFacts ++ read.facts st s!"{tag}.rd" ++ r.facts,
               sending := .input r.input, waiting := fun x => pure ({ x with gap := .or x.gap r.gap }, w) }
      else
        let r ← reactionOf st p pre now (.json (SJson.ofTerms payload)) auto s!"{tag}.r"
        let w := waiting r.input r.valid
        pure { pre := r.ending.accepted, facts := payloadFacts ++ r.facts, sending := .payload payload,
               waiting := fun x => pure ({ x with gap := .or x.gap r.gap }, w) }
    | .activity chart state key =>
      let some c := st.charts.find? (·.name == chart) | throw s!"no chart {chart}"
      let some act := ((c.state? state).map (·.activities.find? (·.key == key))).join | throw s!"no activity {key}"
      let sender := Sender.state chart state key 0
      if third then
        let (input, facts) := objectVars st (.input act.ref) tag
        pure { facts, sending := .input input, waiting := fun x => pure (ownWaiting ce x c.order sender act input) }
      else
        let waiting (x : Path) : Except String (Path × Waiting) := do
          let (x, input) ← activityInput ce x chart state act
          pure (ownWaiting ce x c.order sender act input)
        pure { pre := activeIn models chart state, sending := .computed, waiting }
  let ra ← runOf a "sa"
  let rb ← runOf b "sb"
  -- An activity's input reads its machine's configuration, so each path fixes it where the state is active.
  let charts := [a, b].filterMap fun
    | .activity chart state _ => if third then none else some (chart, state)
    | .automation _ => none
  let orders (name : String) (swap : Bool) : Except String Ending := do
    let start : Path := { name, pc := tt, records := pre, used, machines := startMachines ce }
    let starts ← charts.foldlM (init := [start]) fun paths (chart, state) => do
      let touched ← paths.flatMapM fun x => touch ce x chart fun m k => (m.configs[k]!).contains state
      pure (touched.filter fun x => (x.fixed? chart).any fun (_, k) =>
        ((models.lookup chart).map (·.configs[k]!.contains state)).getD false)
    let begun ← starts.mapM fun x => do
      let (x, wa) ← ra.waiting x
      let (x, wb) ← rb.waiting x
      pure { x with commands := if swap then [wb, wa] else [wa, wb] }
    pure (Ending.of pre (startMachines ce) (merge (← drain ce (2 * chainLimit + 2) (live begun))))
  let first ← orders "o1" false
  let second ← orders "o2" true
  pure { facts := machineFacts ce ++ ra.facts ++ rb.facts ++ first.facts ++ second.facts,
         pre := conj [settled, ra.pre, rb.pre], first, second, given := [], sendings := [ra.sending, rb.sending] }

end Tazuna.Smt
