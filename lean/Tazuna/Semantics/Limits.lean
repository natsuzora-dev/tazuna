import Tazuna.Data.Names

namespace Tazuna.Semantics

/-- An implementation limit. Exceeding a limit halts the run with the Fault of the same name. -/
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

end Tazuna.Semantics
