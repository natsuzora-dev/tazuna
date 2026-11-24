import Tazuna.Semantics.Rules

/-- Every kind of line the engine writes to stdout. test/e2e holds one case per kind, enumerated from `Kind.all`. -/
inductive Tazuna.Kind : Type
  /-- The IR the launcher handed over does not load: a converter bug, reported with exit code 4. -/
  | invalidIr
  /-- The spec's structure breaks a rule: the spec must change, exit code 1. -/
  | illegal (k : Tazuna.Ir.Illegal)

namespace Tazuna.Kind

/-- The name a line carries as its `kind`, such as `Illegal.wireName`. -/
def name : Kind → String
  | invalidIr => "Internal.invalidIr"
  | illegal k => "Illegal." ++ k.name

def all : List Kind := invalidIr :: Ir.Illegal.all.map illegal

theorem mem_all (k : Kind) : k ∈ all := by
  cases k with
  | invalidIr => simp [all]
  | illegal k => simp [all, Ir.Illegal.mem_all]

end Tazuna.Kind
