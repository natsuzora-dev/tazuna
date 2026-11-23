import Tazuna.Semantics.Value.Names
import Tazuna.Semantics.Service.Fault

namespace Tazuna.Semantics.Service

/--
An implementation limit. Exceeding a limit halts the run with the Fault named `exceeded` and the limit's name, such as
`exceededCommandDepth`.
-/
inductive Limit where
  /-- The depth of a chain of own-service commands. -/
  | commandDepth
  /-- The own-service commands in one message. -/
  | messageCommands
  /-- The always rounds in one settle. -/
  | alwaysRounds
  /-- The onDone selections in one onDone work. -/
  | onDoneSelections
  /-- The work items and commands in one message. -/
  | messageWork
  /-- The deadlines in one clock advance. -/
  | dueDeadlines
deriving DecidableEq, Repr, Inhabited

def Limit.max : Limit → Nat
  | .commandDepth => 100
  | .messageCommands => 1000
  | .alwaysRounds => 100
  | .onDoneSelections => 10000
  | .messageWork => 10000
  | .dueDeadlines => 1000

def Limit.name (l : Limit) : String := (constructorNames% Limit).getD l.ctorIdx ""

#guard (samples% Limit).all fun l =>
  (samples% Fault).any fun f => f.kind == s!"Fault.exceeded{l.name.capitalize}" && f.halts

end Tazuna.Semantics.Service
