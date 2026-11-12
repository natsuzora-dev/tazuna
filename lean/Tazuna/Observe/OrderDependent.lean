import Tazuna.Data.Group
import Tazuna.Semantics.Message

namespace Tazuna.Observe

open Tazuna.Data Tazuna.Semantics

/--
A result, found while the run evaluates, that depends on an order the spec does not fix. No OrderDependent violation
halts the run. `definition` is the query that orderAudit runs again with records in reverse key order, or the chart of
the conflicting transitions. In reversedException, an Issue stopped that second run of the query, the check of its
output or its comparable value.
-/
inductive OrderDependent where
  | reversedOutputSchema (definition : Syntax.Ref)
  | reversedException (definition : Syntax.Ref)
  | reversedRecords (definition : Syntax.Ref) (original reversed : Value)
  | bothAssign (definition : Syntax.Ref) (state : String) (first second : Syntax.TransitionRef) (field : String)
  | assignRead (definition : Syntax.Ref) (state : String) (writer reader : Syntax.TransitionRef) (field : String)
deriving DecidableEq, Repr, Inhabited

derive_group OrderDependent

def OrderDependent.toViolation (m : OrderDependent) : Violation :=
  { kind := m.kind, definition := m.definition, data := m.data }

end Tazuna.Observe
