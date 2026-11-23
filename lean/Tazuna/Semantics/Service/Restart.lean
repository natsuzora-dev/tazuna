import Tazuna.Semantics.Service.Input

namespace Tazuna.Semantics.Service

open Tazuna.Ir

variable {m : Type → Type}

/-- The state when the service process stops, without the part that lives in its memory. -/
def State.stop (s : State) : State := { s with toProcess := {} }

/--
The state after a restart input. The process stops after the deadlines due by then fire, and the service begins again
as at the first input. Answers to the requests of the stopped process find no waiting request.
-/
def restart [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State :=
  begin st fs (s.write .in none .restart).1.stop

end Tazuna.Semantics.Service
