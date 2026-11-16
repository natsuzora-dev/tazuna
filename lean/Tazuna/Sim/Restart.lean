import Tazuna.Sim.Input

namespace Tazuna.Semantics

open Tazuna.Data

variable {m : Type → Type}

/--
The state when the service process stops, without the part that lives in its memory: the instances, copies, open
screens, deadlines, awaited requests, queued work, and the subscriptions that other services opened. As in the Raft
TLA+ spec's Restart, the persisted part stays: the records, the kept command answers and event deliveries, the accepted
external commands, the createKey values, and the trace.
-/
def State.stop (s : State) : State :=
  { s with started := false, machines := [], copies := [], stack := [], deadlines := [], pending := [], queued := [],
           subscriptions := [] }

/--
The state after a restart input. The process stops after the deadlines due by then fire, and the service begins again
as at the first input. Answers to the requests of the stopped process find no waiting request.
-/
def restart [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State :=
  begin st fs (s.writeInput none .restart).1.stop

end Tazuna.Semantics
