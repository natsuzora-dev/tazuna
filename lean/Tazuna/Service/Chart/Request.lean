import Tazuna.Service.Chart.Queue
import Tazuna.Service.Contract

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

/--
The initial context of `chart` started with `input`: what its initialContext computes, with each field that it leaves
out taking its default, or the fault that an Issue means.
-/
def initialContextOf [Monad m] (fs : Functions m) (st : Service) (chart : String) (input : Value) :
    m (Except Fault Value) := do
  let definition := st.ref chart
  let fault := issueViolation definition (mismatch := fun _ => .initialContextSchema definition)
  match ← fs.initialContext chart input with
  | .error e => pure (.error (fault e))
  | .ok given =>
    match ← fs.defaults (.context definition) with
    | .error e => pure (.error (fault e))
    | .ok defaults =>
      match ← fs.normalize (.context definition) (defaults.merge given) with
      | .error e => pure (.error (fault e))
      | .ok none => pure (.error (.initialContextSchema definition))
      | .ok (some context) => pure (.ok context)

/-- The request line of a calls (a query) or of a sends (a command) to `target` with `input`. -/
def Activity.requestLine (a : Activity) (input : Value) : LineBody :=
  match a with
  | .calls .. => .query a.ref input
  | _ => .command a.ref input

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def request (st : Service) (step : Nat) (name : InstanceId) (state : String) (a : Activity) : Processing → m Processing :=
  withMachine name fun i r => do
    match ← fs.input (r.state.scopeOf i (some state)) r.state.records a r.state.nextKeys with
    | .error e => pure (r.report (.fault (issueViolation (st.ref i.chart.name) e)))
    | .ok (input, keys) =>
      let r : Processing := ⟨r.state.createKeys keys, r.queue⟩
      if a.isOwn st.service then
        let (s, serial) := r.state.startQueued name state
        let sent : Sent := { order := i.chart.order, requester := .state name state, activity := a, serial := some serial,
                             input, cause := step }
        pure ⟨s, { r.queue with round := r.queue.round ++ [sent] }⟩
      else
        pure ⟨r.state.await (a.requestLine input) (.state name state) a input, r.queue⟩

def openScreen (st : Service) (step : Nat) (name : InstanceId) (state : String) (a : Activity) : Processing → m Processing :=
  withMachine name fun i r => do
    match st.chart? a.ref.name with
    | none => pure r
    | some c =>
      match ← fs.input (r.state.scopeOf i (some state)) r.state.records a r.state.nextKeys with
      | .error e => pure (r.report (.fault (issueViolation (st.ref i.chart.name) e)))
      | .ok (raw, _) =>
      match ← fs.parse (.input (st.ref c.name)) raw with
      | .error e => pure (r.report (.fault (issueViolation (st.ref c.name) e)))
      | .ok none => pure (r.report (.fault (.inputSchema (st.ref i.chart.name) (st.ref c.name))))
      | .ok (some input) =>
      let rq ← expectFound s!"requirements of {c.name}" (st.requirements.lookup c.name)
      match ← firstFalse (fs.inputRequirement (st.ref c.name) · input) rq.requires with
      | .error e => pure (r.report (.fault (issueViolation (st.ref c.name) e)))
      | .ok (some condition) =>
        pure (r.report (.fault (.failedRequires (st.ref i.chart.name) (st.ref c.name) condition)))
      | .ok none =>
      match ← initialContextOf fs st c.name input with
      | .error fault => pure (r.report (.fault fault))
      | .ok context =>
        let id := InstanceId.opened c.name name state a.key
        let child : Instance := { chart := c, id, context, input, shown := c.slots.map (·, .null) }
        pure ⟨{ r.state with machines := r.state.machines.filter (·.id != id) ++ [child], stack := r.state.stack ++ [id] },
          { r.queue with tasks := r.queue.tasks ++ [.start id (some step)] }⟩

/--
The processing after state `state` starts activity `a`. `shows` does nothing here, since it subscribes after
evaluation.
-/
def activate (st : Service) (step : Nat) (name : InstanceId) (state : String) (a : Activity) : Processing → m Processing :=
  match a with
  | .opens .. => openScreen fs st step name state a
  | .shows .. => pure
  | .calls .. | .sends .. => request fs st step name state a

/--
The processing after the activities of entered state `e` start. Sending the activities is a new step, caused by the step
that entered the state and ordered after all earlier steps of the message.
-/
def activateEntered (st : Service) (e : InstanceId × String × Nat) : Processing → m Processing :=
  withMachine e.1 fun i r =>
    if i.closed || !i.isIn e.2.1 then pure r else
    match i.chart.state? e.2.1 with
    | none => pure r
    | some cs => do
      let (s, step) := r.state.newStep (.caused e.2.2) (barrier := true)
      MonadNote.note (.stepBegins step (.activities e.1 e.2.1) none)
      let r ← cs.activities.foldlM (fun r a => unlessHalted (activate fs st step e.1 e.2.1 a) r) ⟨s, r.queue⟩
      MonadNote.note .stepEnds
      pure r

/--
The entered states in send order: owners in the order that their entry records remain (re-entering moves a record to
the end), and within an owner, document order including copies.
-/
def sendOrder (s : State) (entered : List (InstanceId × String × Nat)) : List (InstanceId × String × Nat) :=
  (dedupe (entered.map (·.1.owner))).flatMap fun owner =>
    match s.machine? owner with
    | none => []
    | some o => o.documentOrder.filterMap fun (h, n) => entered.find? fun e => e.1 == h && e.2.1 == n

/--
The processing after the activities of the states that the message entered and that are still active start, at the end
of the macrostep (SCXML statesToInvoke).
-/
def sendEntered (st : Service) (r : Processing) : m Processing :=
  (sendOrder r.state r.queue.entered).foldlM (fun r e => activateEntered fs st e r)
    ⟨r.state, { r.queue with entered := [] }⟩

end

end Tazuna.Service
