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

/-- Whether the answer rejects its request as unavailable. -/
def Answer.unavailable : Answer → Bool
  | .rejected r => r.kind == .unavailable
  | _ => false

def Answer.mapOutput (f : Value → Value) : Answer → Answer
  | .accepted output => .accepted (output.map f)
  | .fulfilled output => .fulfilled (f output)
  | .rejected r => .rejected r

/-- Whether the received answer `a` carries the sent answer `b`, values compared by `agree`, rejections by kind. -/
def AnswerCarries (agree : Value → Value → Prop) : Answer → Answer → Prop
  | .accepted (some x), .accepted (some y) => agree x y
  | .accepted none, .accepted none => True
  | .fulfilled x, .fulfilled y => agree x y
  | .rejected r, .rejected q => r.kind = q.kind
  | _, _ => False

end Tazuna.Data
