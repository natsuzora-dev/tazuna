import Tazuna.Service.Chart.Queue
import Tazuna.Service.Contract

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

/-- The initial context of `chart` started with `input`, or the fault that an Issue of initialContext means. -/
def initialContextOf [Monad m] (fs : Functions m) (st : Service) (chart : String) (input : Value) :
    m (Except Fault Value) := do
  let definition := st.ref chart
  match ← fs.initialContext chart input with
  | .error e => pure (.error (issueViolation st definition e fun _ => .initialContextSchema definition))
  | .ok context => pure (.ok context)

/-- The request line of a calls (a query) or of a sends (a command) to `target` with `input`. -/
def Activity.requestLine (a : Activity) (target : String) (input : Value) : LineBody :=
  match a with
  | .calls .. => .query target input
  | _ => .command target input

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def request (st : Service) (step : Nat) (name state : String) (a : Activity) : Processing → m Processing :=
  withMachine name fun i r => do
    match ← fs.input (r.state.scopeOf i (some state)) r.state.records a r.state.nextKeys with
    | .error e => pure (r.report (.fault (issueViolation st (st.ref i.chart.name) e)))
    | .ok (input, keys) =>
      let r : Processing := ⟨r.state.createKeys keys, r.queue⟩
      if a.isOwn st.service then
        let (s, serial) := r.state.startQueued name state
        let sent : Sent := { order := i.chart.order, requester := .state name state, activity := a, serial := some serial,
                             input, cause := step }
        pure ⟨s, { r.queue with round := r.queue.round ++ [sent] }⟩
      else
        pure ⟨r.state.await (a.requestLine (st.traceNameOf a.ref) input) (.state name state) a input, r.queue⟩

def openScreen (st : Service) (step : Nat) (name state : String) (a : Activity) : Processing → m Processing :=
  withMachine name fun i r => do
    match st.chart? a.ref.name with
    | none => pure r
    | some c =>
      match ← fs.input (r.state.scopeOf i (some state)) r.state.records a r.state.nextKeys with
      | .error e => pure (r.report (.fault (issueViolation st (st.ref i.chart.name) e)))
      | .ok (raw, _) =>
      match ← fs.parse (.input c.name) raw with
      | .error e => pure (r.report (.fault (issueViolation st (st.ref c.name) e)))
      | .ok none => pure (r.report (.fault (.inputSchema (st.ref i.chart.name) (st.ref c.name))))
      | .ok (some input) =>
      match ← firstFalse (fs.inputRequirement c.name · input) (st.requirementsOf c.name).requires with
      | .error e => pure (r.report (.fault (issueViolation st (st.ref c.name) e)))
      | .ok (some condition) =>
        pure (r.report (.fault (.failedRequires (st.ref i.chart.name) (st.ref c.name) condition)))
      | .ok none =>
      match ← initialContextOf fs st c.name input with
      | .error fault => pure (r.report (.fault fault))
      | .ok context =>
        let opened := (r.state.machines.filter (·.chart.name == c.name)).length
        let resource := if opened == 0 then c.name else s!"{c.name}({opened + 1})"
        let child : Instance :=
          { chart := c, resource, context, input, shown := c.slots.map (·, .null),
            opener := some { parent := name, state, key := a.key, modal := a.isModal } }
        pure ⟨{ r.state with machines := r.state.machines ++ [child], stack := r.state.stack ++ [resource] },
          { r.queue with tasks := r.queue.tasks ++ [.start resource (some step)] }⟩

/--
The processing after state `state` starts activity `a`. `shows` does nothing here, since it subscribes after
evaluation.
-/
def activate (st : Service) (step : Nat) (name state : String) (a : Activity) : Processing → m Processing :=
  match a with
  | .opens .. => openScreen fs st step name state a
  | .shows .. => pure
  | .calls .. | .sends .. => request fs st step name state a

/--
The processing after the activities of entered state `e` start. Sending the activities is a new step, caused by the step
that entered the state and ordered after all earlier steps of the message.
-/
def activateEntered (st : Service) (e : String × String × Nat) : Processing → m Processing :=
  withMachine e.1 fun i r =>
    if i.closed || !i.isIn e.2.1 then pure r else
    match i.chart.state? e.2.1 with
    | none => pure r
    | some cs => do
      let (s, step) := r.state.newStep (some e.2.2) (barrier := true)
      MonadNote.note (.stepBegins step (.activities (s.who st e.1) e.2.1) none)
      let r ← cs.activities.foldlM (fun r a => unlessHalted (activate fs st step e.1 e.2.1 a) r) ⟨s, r.queue⟩
      MonadNote.note .stepEnds
      pure r

/--
The entered states in send order: owners in the order that their entry records remain (re-entering moves a record to
the end), and within an owner, document order including copies.
-/
def sendOrder (s : State) (entered : List (String × String × Nat)) : List (String × String × Nat) :=
  (dedupe (entered.map (s.ownerOf ·.1))).flatMap fun owner =>
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
