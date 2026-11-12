import Tazuna.Data.Wire

namespace Tazuna.Data

/-- The check that rejected a request. -/
inductive RejectionKind where
  | invalidInput
  | reusedId
  | notFound
  | requires
  | alreadyExists
  | unavailable
deriving DecidableEq, Repr, Inhabited

derive_wire RejectionKind rename_all "kebab-case"

/-- The rejection of a request. verify compares `kind`, not `reason`. -/
structure Rejection where
  kind : RejectionKind
  /-- The name of the binds value or the requires condition that failed. -/
  reason : Option String := none
deriving DecidableEq, Repr, Inhabited

derive_wire Rejection skip_serializing_none

/-- The answer to a request. A command is accepted or rejected, and a query is fulfilled or rejected. -/
inductive Answer where
  | accepted (output : Option Value)
  | fulfilled (output : Value)
  | rejected (rejection : Rejection)
deriving DecidableEq, Repr, Inhabited

derive_wire Answer tag "result" skip_serializing_none

def Answer.output? : Answer → Option Value
  | .accepted output => output
  | .fulfilled output => some output
  | .rejected _ => none

end Tazuna.Data
