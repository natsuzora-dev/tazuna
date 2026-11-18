import Tazuna.Service.State

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

/--
The state with the `after` deadlines of state `n` of instance `name` armed by step `step`. Each time is fixed now, as
XState and SCXML evaluate a delay when the state is entered: a delay counts from now, and an `at` is computed from
current values once. A spec moves a deadline by entering its state again.
-/
def addDeadlines [Monad m] (st : Service) (fs : Functions m) (step : Nat) (name : InstanceId) (n : String)
    (deadlines : List (String × DeadlineTime)) (s : State) : m State :=
  match s.machine? name with
  | none => pure s
  | some i =>
    let add (s : State) (deadline : String) : Except Issue Time → State
      | .error e => s.report (.fault (issueViolation (st.ref i.chart.name) e))
      | .ok time =>
        { s with deadlineCount := s.deadlineCount + 1,
                 deadlines := s.deadlines ++
                   [{ time, order := s.deadlineCount + 1, machine := name, state := n, name := deadline,
                      armedBy := step }] }
    deadlines.foldlM (fun s (deadline, d) =>
      if s.halted.isSome then pure s else
      match d with
      | .delay delay => pure (add s deadline (.ok (s.now + delay)))
      | .atExpression => add s deadline <$> fs.deadlineAt (s.scopeOf i (some n)) s.records deadline) s

/-- The state without the deadline `t`, and whether `t` was still waiting. -/
def State.takeDeadline (s : State) (t : Deadline) : State × Bool :=
  ({ s with deadlines := s.deadlines.filter (·.order != t.order) }, s.deadlines.any (·.order == t.order))

end Tazuna.Service
