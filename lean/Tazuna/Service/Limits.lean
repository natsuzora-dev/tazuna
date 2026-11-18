import Tazuna.Data.Names
import Tazuna.Service.Fault

namespace Tazuna.Service

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
  /-- The nesting depth of exits, through copies and screens that their parent's exit closes. -/
  | exitDepth
deriving DecidableEq, Repr, Inhabited

def Limit.max : Limit → Nat
  | .commandDepth => 100
  | .messageCommands => 10000
  | .alwaysRounds => 100
  | .onDoneSelections => 10000
  | .messageWork => 100000
  | .dueDeadlines => 10000
  | .exitDepth => 100

def Limit.name (l : Limit) : String := (constructorNames% Limit).getD l.ctorIdx ""

#guard (samples% Limit).all fun l =>
  (samples% Fault).any fun f => f.kind == s!"Fault.exceeded{l.name.capitalize}" && f.halts

end Tazuna.Service
