import Tazuna.Spec.Domains
import Tazuna.Validation.Illegal

namespace Tazuna.Validation.Explores

open Tazuna.Data Tazuna.Spec Tazuna.Spec.Domains

/-- The nodes without a domain of the schemas that the explore `x`'s moves may carry. -/
def undeclared (s : Structure) (x : Explore) : List Illegal :=
  (moveSchemas s x.service).flatMap fun schema =>
    match schemaTree? s x schema with
    | some t => t.undeclaredPaths.map (.undeclaredDomain schema.owner x.service schema)
    | none => []

def check (s : Structure) : List Illegal := s.explores.flatMap (undeclared s)

end Tazuna.Validation.Explores
