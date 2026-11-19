import Tazuna.Service.Chart.Exit

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def enterFinal (step : Nat) (name : InstanceId) (parent : String) (r : Processing) : Processing :=
  match r.state.machine? name with
  | none => r
  | some i =>
    let finished := i.chart.tree.finished i.active parent
    match i.awaitingOnDone with
    | some waiting => ⟨r.state.setMachine name fun i => { i with awaitingOnDone := some (waiting ++ finished) }, r.queue⟩
    | none =>
      ⟨r.state.setMachine name fun i => { i with awaitingOnDone := some finished },
       { r.queue with tasks := r.queue.tasks ++ [.onDone name step] }⟩

def closeFinal (st : Service) (step : Nat) (name : InstanceId) : Processing → m Processing :=
  withMachine name fun i r => do
    match ← fs.close (r.state.scopeOf i none) r.state.records with
    | .error e =>
      pure (r.report (.fault (issueViolation (st.ref i.chart.name) e fun _ =>
        .screenOutputSchema (st.ref i.chart.name))))
    | .ok (output, failed) =>
      let ensures := failed.toList.map (st.failedEnsures i.chart.name)
      let r ← endWith (exitOne fs st Limit.exitDepth.max) name ⟨r.state.reportAll ensures, r.queue⟩
      if r.halted then pure r else
      match i.id.opener? with
      | some (parent, state, key) =>
        let (s, serial) := r.state.startQueued parent state
        pure ⟨s, { r.queue with tasks := r.queue.tasks ++ [.opensDone parent state key output serial step] }⟩
      | none => pure r

end

end Tazuna.Service
