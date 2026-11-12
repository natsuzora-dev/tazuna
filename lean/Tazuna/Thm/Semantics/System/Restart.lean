import Tazuna.Semantics.System.Restart
import Tazuna.Thm.Semantics.System.Input

namespace Tazuna.Thm.Semantics.System.Restart

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Semantics.Service.Records Tazuna.Thm.Semantics.System.Input

variable {st : Service} {fs : Functions Id} {s t : State}

theorem stop_writeInput (givenId : Option String) (body : LineBody) :
    (s.writeInput givenId body).1.stop = (s.stop.writeInput givenId body).1 := rfl

/--
The service begins again from the persisted part of the state: the records, the kept command answers and event
deliveries, the accepted external commands, and the createKey values, with no instance, deadline, awaited request, or
subscription of another service left.
-/
theorem restart_keeps :
    ∃ t, restart st fs s = begin st fs t ∧ t.started = false ∧ t.records = s.records ∧
      t.commandAnswers = s.commandAnswers ∧ t.eventDeliveries = s.eventDeliveries ∧ t.results = s.results ∧
      t.created = s.created ∧ t.machines = [] ∧ t.copies = [] ∧ t.stack = [] ∧ t.deadlines = [] ∧ t.pending = [] ∧
      t.queued = [] ∧ t.subscriptions = [] :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A restart reads nothing of the part of the state that it discards. -/
theorem restart_forgets (h : s.stop = t.stop) : restart st fs s = restart st fs t := by
  simp only [restart, stop_writeInput, h]

theorem restart_keysDistinct (h : KeysDistinct s.records) : KeysDistinct (restart st fs s).records :=
  begin_keysDistinct h

end Tazuna.Thm.Semantics.System.Restart
