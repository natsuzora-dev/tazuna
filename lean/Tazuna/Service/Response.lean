import Tazuna.Service.Functions
import Tazuna.Service.State

/-!
The observer of bounded responses ("after P, Q within D", as Dwyer's response pattern bounds it). At each visible state,
the end of a message or a time that the clock reaches, a record whose `when` holds and whose `expect` does not opens an
obligation due `within` ms later, unless one is open; `expect` holding, or the record leaving, discharges it. Time passing
an obligation's due while it is open misses the response.
-/

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

/-- The state at time `t`, no earlier than its time, with each obligation due before `t` reported missed and dropped. -/
def State.passTime (st : Service) (s : State) (t : Time) : State :=
  let missed := s.obligations.filter (·.due < t)
  let s := s.reportAll (missed.map fun o => .missedResponse (st.ref o.entity) o.key o.response o.due)
  { s with now := max s.now t, obligations := s.obligations.filter (·.due ≥ t) }

/-- The obligations of the record `row` after its responses at `now` answered `answers`. -/
def respond (st : Service) (now : Time) (row : Row) (obligations : List Obligation)
    (answers : List (String × Bool × Bool)) : List Obligation :=
  answers.foldl (fun os (name, whenHolds, expectHolds) =>
    let mine (o : Obligation) := o.entity == row.entity && o.key == row.key && o.response == name
    if expectHolds then os.filter (!mine ·)
    else if whenHolds && !os.any mine then
      match (st.responsesOf row.entity).find? (·.name == name) with
      | some r => os ++ [{ entity := row.entity, key := row.key, response := name, due := now + r.within }]
      | none => os
    else os) obligations

/-- The state after its responses observe it as a visible state. -/
def observeResponses [Monad m] (st : Service) (fs : Functions m) (s : State) : m State :=
  if s.halted.isSome then pure s else
  let present (o : Obligation) := s.records.any fun r => r.entity == o.entity && r.key == o.key
  (s.records.filter fun r => !(st.responsesOf r.entity).isEmpty).foldlM (init := { s with obligations := s.obligations.filter present })
    fun s row => do
      match ← fs.responses row.entity row.value s.now with
      | .error e => pure (s.report (.fault (issueViolation (st.ref row.entity) e)))
      | .ok answers => pure { s with obligations := respond st s.now row s.obligations answers }

end Tazuna.Service
