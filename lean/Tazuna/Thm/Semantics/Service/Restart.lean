import Tazuna.Semantics.Service.Restart
import Tazuna.Thm.Semantics.Service.Input
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Semantics.Service.Restart

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Service.Records Tazuna.Thm.Semantics.Service.Input

variable {st : Service} {fs : Functions Id} {s t : Service.State}

theorem stop_write (givenId : Option LineId) (body : LineBody) (w : EmittedOf .in body) (q : SenderOf .in body) (r : RequestOf .in body) :
    (s.write .in givenId body w q r).1.stop = (s.stop.write .in givenId body w q r).1 := rfl

/-- The service begins again from the part of the state that it persists, with none of the part in its memory left. -/
@[guarantee] theorem restart_keeps : ∃ t, restart st fs s = begin st fs t ∧ t.toDurable = s.toDurable ∧ t.toProcess = {} :=
  ⟨_, rfl, rfl, rfl⟩

/-- A restart reads nothing of the part of the state that it discards. -/
@[guarantee] theorem restart_forgets (h : s.stop = t.stop) : restart st fs s = restart st fs t := by
  simp only [restart, stop_write, h]

end Tazuna.Thm.Semantics.Service.Restart
