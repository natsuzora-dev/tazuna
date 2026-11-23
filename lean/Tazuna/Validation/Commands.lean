import Tazuna.Validation.Illegal

namespace Tazuna.Validation.Commands

open Tazuna.Data
open Tazuna.Spec

def foreignEvents (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    match d.body with
    | .command c => c.emits.filterMap fun e => if e.service == d.service then none else some (.foreignEvent d.ref e)
    | _ => []

/-- Whether `key` is an array index of ECMA-262: the canonical decimal form of a whole number below 2^32 - 1. -/
def isArrayIndex (key : String) : Bool :=
  match key.toNat? with
  | some n => n < 2 ^ 32 - 1 && toString n == key
  | none => false

def indexReasons (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    ((s.rejectionReasons d.ref).filter isArrayIndex).map (.indexReason d.ref)

/-- The commands and queries that `d` sends: an automation's command, or a chart's commands and queries. -/
def sentBy (d : Definition) : List Ref :=
  match d.body with
  | .automation a => [a.command]
  | .machine c | .screen c => (c.commands ++ c.queries).map (·.2)
  | _ => []

/--
Whether `callers` take the requests of `d`: they list its service, or, when `d` is a screen, which sends as the user
that operates it (State.callerOf), an entity.
-/
def admitsSender (callers : List CallerType) (d : Definition) : Bool :=
  callers.contains (.service d.service) || (d.isScreen && callers.any (· matches .entity _))

def unlistedCallers (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    (sentBy d).filterMap fun r =>
      match s.callersOf? r with
      | some callers => if admitsSender callers d then none else some (.unlistedCaller d.ref r)
      | none => none

def check (s : Structure) : List Illegal := foreignEvents s ++ indexReasons s ++ unlistedCallers s

end Tazuna.Validation.Commands
