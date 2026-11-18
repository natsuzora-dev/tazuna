import Tazuna.Service.Restart
import Tazuna.Thm.Service.Input

namespace Tazuna.Thm.Service.Restart

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Service.Records Tazuna.Thm.Service.Input

variable {st : Service} {fs : Functions Id} {s t : State}

theorem stop_write (givenId : Option LineId) (body : LineBody) :
    (s.write .in givenId body).1.stop = (s.stop.write .in givenId body).1 := rfl

/-- The service begins again from the part of the state that it persists, with none of the part in its memory left. -/
theorem restart_keeps : ∃ t, restart st fs s = begin st fs t ∧ t.toDurable = s.toDurable ∧ t.toProcess = {} :=
  ⟨_, rfl, rfl, rfl⟩

/-- A restart reads nothing of the part of the state that it discards. -/
theorem restart_forgets (h : s.stop = t.stop) : restart st fs s = restart st fs t := by
  simp only [restart, stop_write, h]

end Tazuna.Thm.Service.Restart
