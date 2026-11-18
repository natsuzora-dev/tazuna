import Tazuna.Data.Wire

namespace Tazuna.Data

inductive EntryKind where
  | file
  | folder
  | other
deriving DecidableEq, Repr

derive_wire EntryKind

structure Entry where
  name : String
  kind : EntryKind
deriving DecidableEq, Repr

derive_wire Entry

/-- The name of a `<name>.jsonl` file. -/
def fileName (e : Entry) : Option String :=
  if e.kind = .file ∧ e.name.endsWith ".jsonl" then some (e.name.dropEnd 6).toString else none

structure Pairing (α : Type) where
  /-- The expected values whose name has a file, in their order. -/
  paired : List α
  /-- The expected values whose name has no file, in their order. -/
  missing : List α
  /-- The names of `<name>.jsonl` files that no expected name has, in the order of the entries. -/
  extra : List String
  /-- The names of the entries that are not `<name>.jsonl` files, in the order of the entries. -/
  unknown : List String
deriving Repr

def names (entries : List Entry) : List String := entries.filterMap fileName

/-- The pairing of the expected values, by `name`, with the `<name>.jsonl` files among the entries. -/
def pair {α : Type} (name : α → String) (expected : List α) (entries : List Entry) : Pairing α :=
  { paired := expected.filter fun x => name x ∈ names entries
    missing := expected.filter fun x => name x ∉ names entries
    extra := (names entries).filter fun n => n ∉ expected.map name
    unknown := (entries.filter fun e => (fileName e).isNone).map (·.name) }

end Tazuna.Data
