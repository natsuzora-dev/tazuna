import Tazuna.Semantics.Service.State

namespace Tazuna.Semantics.Service

open Tazuna.Ir

variable {m : Type → Type}

/--
The state with the `after` deadlines of state `n` of instance `name` armed by step `step`. Each time is fixed now, as
XState and SCXML evaluate a delay when the state is entered: `now` plus the delay, or what `at` computes (deadlineAt).
A spec moves a deadline by entering its state again. Both times must be instants that the run's time holds
(Time.inRange): a delay past the range of an instant is deadlineOutOfRange, and an `at` that computes no such instant is atSchema.
check accepts only a delay in whole milliseconds (Illegal.inexactDelay), so the lookup of its length finds one
(deadlines_exact).
-/
def addDeadlines [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (step : Nat) (name : InstanceId) (n : String)
    (deadlines : List Ir.Deadline) (s : State) : m State :=
  match s.machine? name with
  | none => pure s
  | some i =>
    let arm (s : State) (deadline : String) (time : Time) : State :=
      { s with deadlineCount := s.deadlineCount + 1,
               deadlines := s.deadlines ++
                 [{ time, order := s.deadlineCount + 1, machine := name, state := n, name := deadline,
                    armedBy := step }] }
    let fault (s : State) (f : Fault) : State := s.report (.fault f)
    deadlines.foldlM (fun s deadline =>
      if s.halted.isSome then pure s else
      match deadline.time with
      | .delay d => do
        let ms ← expectFound s!"delay in milliseconds of {deadline.name}" d
        let time := s.now + ms
        pure (if time.inRange then arm s deadline.name time
          else fault s (.deadlineOutOfRange (st.ref i.chart.name) n deadline.name))
      | .at => do
        pure <| match ← fs.deadlineAt (s.scopeOf i (some n)) s.records deadline.name with
          | .error e => fault s (issueViolation (st.ref i.chart.name) e)
          | .ok computed => match computed.bind instantTime? with
            | some time => arm s deadline.name time
            | none => fault s (.atSchema (st.ref i.chart.name) n deadline.name)) s

/-- The state without the deadline `t`, and whether `t` was still waiting. -/
def State.takeDeadline (s : State) (t : Deadline) : State × Bool :=
  ({ s with deadlines := s.deadlines.filter (·.order != t.order) }, s.deadlines.any (·.order == t.order))

end Tazuna.Semantics.Service
