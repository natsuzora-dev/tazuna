/-- Every kind of line the engine writes to stdout. test/e2e holds one case per kind, enumerated from `Kind.all`. -/
inductive Tazuna.Kind : Type

namespace Tazuna.Kind

/-- The name a line carries as its `kind`, such as `Illegal.wire_name`. -/
def name : Kind → String := fun k => nomatch k

def all : List Kind := []

theorem mem_all (k : Kind) : k ∈ all := nomatch k

end Tazuna.Kind
