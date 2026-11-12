namespace Tazuna.Data

inductive EntryKind where
  | file
  | folder
  | other
deriving DecidableEq, Repr

structure Entry where
  name : String
  kind : EntryKind
deriving DecidableEq, Repr

/-- The name of a `<name>.jsonl` file. -/
def fileName (e : Entry) : Option String :=
  if e.kind = .file ∧ e.name.endsWith ".jsonl" then some (e.name.dropEnd 6).toString else none

structure Pairing where
  /-- The expected names that have a file, in their order. -/
  paired : List String
  /-- The expected names that have no file, in their order. -/
  missing : List String
  /-- The names of `<name>.jsonl` files that no expected name has, in the order of the entries. -/
  extra : List String
  /-- The names of the entries that are not `<name>.jsonl` files, in the order of the entries. -/
  unknown : List String
deriving Repr

def names (entries : List Entry) : List String := entries.filterMap fileName

/-- The pairing of the expected names with the `<name>.jsonl` files among the entries. -/
def pair (expected : List String) (entries : List Entry) : Pairing :=
  { paired := expected.filter fun n => n ∈ names entries
    missing := expected.filter fun n => n ∉ names entries
    extra := (names entries).filter fun n => n ∉ expected
    unknown := (entries.filter fun e => (fileName e).isNone).map (·.name) }

end Tazuna.Data
