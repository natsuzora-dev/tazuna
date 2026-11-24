/-- Every kind of line the engine writes to stdout. test/e2e holds one case per kind, enumerated from `Kind.all`. -/
inductive Tazuna.Kind : Type
  /-- The IR the launcher handed over does not load: a converter bug, reported with exit code 4. -/
  | invalidIr

namespace Tazuna.Kind

/-- The name a line carries as its `kind`, such as `Illegal.wireName`. -/
def name : Kind → String
  | invalidIr => "Internal.invalidIr"

def all : List Kind := [invalidIr]

theorem mem_all (k : Kind) : k ∈ all := by cases k; simp [all]

end Tazuna.Kind
