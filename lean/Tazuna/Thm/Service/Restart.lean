import Tazuna.Service.Restart
import Tazuna.Thm.Service.Input

namespace Tazuna.Thm.Service.Restart

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Service.Records Tazuna.Thm.Service.Input

variable {st : Service} {fs : Functions Id} {s t : State}

theorem stop_write (givenId : Option String) (body : LineBody) :
    (s.write .in givenId body).1.stop = (s.stop.write .in givenId body).1 := rfl

/--
The service begins again from the persisted part of the state: the records, the kept command answers, the events and
answers that arrived, the accepted external commands, and the createKey values, with no instance, deadline, awaited
request, or subscription of another service left.
-/
theorem restart_keeps :
    ∃ t, restart st fs s = begin st fs t ∧ t.started = false ∧ t.records = s.records ∧
      t.commandAnswers = s.commandAnswers ∧ t.deliveries = s.deliveries ∧ t.takenAnswers = s.takenAnswers ∧
      t.results = s.results ∧ t.created = s.created ∧ t.machines = [] ∧ t.copies = [] ∧ t.stack = [] ∧
      t.deadlines = [] ∧ t.pending = [] ∧ t.queued = [] ∧ t.subscriptions = [] :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A restart reads nothing of the part of the state that it discards. -/
theorem restart_forgets (h : s.stop = t.stop) : restart st fs s = restart st fs t := by
  simp only [restart, stop_write, h]

theorem restart_keysDistinct (h : KeysDistinct s.records) : KeysDistinct (restart st fs s).records :=
  begin_keysDistinct h

end Tazuna.Thm.Service.Restart
