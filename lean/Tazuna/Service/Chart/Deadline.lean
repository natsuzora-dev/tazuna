import Tazuna.Service.State

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

/--
The state with the `after` deadlines of state `n` of instance `name` armed by step `step`. Each time is fixed now, as
XState and SCXML evaluate a delay when the state is entered: `now` plus the delay, or what `at` computes
(deadlineTime). A spec moves a deadline by entering its state again. A time that is no instant in whole milliseconds is a
fault of the `at` that computed it, since check accepts only a delay in whole milliseconds (Illegal.inexactDelay).
-/
def addDeadlines [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (step : Nat) (name : InstanceId) (n : String)
    (deadlines : List Spec.Deadline) (s : State) : m State :=
  match s.machine? name with
  | none => pure s
  | some i =>
    let add (s : State) (deadline : String) (computed : Except Issue (Option Time)) : State :=
      match computed with
      | .error e => s.report (.fault (issueViolation (st.ref i.chart.name) e))
      | .ok none => s.report (.fault (.atSchema (st.ref i.chart.name) n deadline))
      | .ok (some time) =>
        { s with deadlineCount := s.deadlineCount + 1,
                 deadlines := s.deadlines ++
                   [{ time, order := s.deadlineCount + 1, machine := name, state := n, name := deadline,
                      armedBy := step }] }
    deadlines.foldlM (fun s deadline =>
      if s.halted.isSome then pure s else
      match deadline.time with
      | .delay d => do
        let ms ← expectFound s!"delay in milliseconds of {deadline.name}" (d.bind Spec.Delay.ms?)
        pure (add s deadline.name (.ok (some (s.now + ms))))
      | .at =>
        add s deadline.name <$> (·.map (·.bind instantTime?)) <$>
          fs.deadlineTime (s.scopeOf i (some n)) s.records deadline.name) s

/-- The state without the deadline `t`, and whether `t` was still waiting. -/
def State.takeDeadline (s : State) (t : Deadline) : State × Bool :=
  ({ s with deadlines := s.deadlines.filter (·.order != t.order) }, s.deadlines.any (·.order == t.order))

end Tazuna.Service
