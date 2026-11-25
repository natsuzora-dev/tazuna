import Tazuna.Linter.SilentDefault

/-! tazuna's own linters, one file per rule under `Tazuna/Linter/` (Mathlib's layout). Every module imports this one
through the modules without other tazuna imports, so each rule runs on every module during `lake build`, and
`--wfail` turns its warnings into errors. -/
