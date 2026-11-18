import Tazuna.Service.State

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

def addDeadlines (step : Nat) (name : InstanceId) (n : String) (deadlines : List (String × DeadlineTime)) (s : State) :
    State :=
  deadlines.foldl (fun s (deadline, d) =>
    { s with deadlineCount := s.deadlineCount + 1,
             deadlines := s.deadlines ++
               [{ time := (match d with | .delay delay => some (s.now + delay) | .atExpression => none),
                  fromAt := d == .atExpression, order := s.deadlineCount + 1, machine := name, state := n,
                  name := deadline, armedBy := step }] }) s

def rearm [Monad m] (st : Service) (fs : Functions m) (s : State) : m State :=
  s.deadlines.foldlM (fun s t =>
    if s.halted.isSome || !t.fromAt then pure s else
    match s.machine? t.machine with
    | none => pure s
    | some i => do
      match ← fs.deadlineAt (s.scopeOf i (some t.state)) s.records t.name with
      | .error e =>
        pure (s.report (.fault (issueViolation (st.ref i.chart.name) e)))
      | .ok time =>
        pure { s with deadlines := s.deadlines.map fun u =>
          if u.order == t.order && u.time != some time then { u with time := some time, timedIn := some s.messageCount }
          else u })
    s

/-- The state without the deadline `t`, and whether `t` was still waiting. -/
def State.takeDeadline (s : State) (t : Deadline) : State × Bool :=
  ({ s with deadlines := s.deadlines.filter (·.order != t.order) }, s.deadlines.any (·.order == t.order))

end Tazuna.Service
