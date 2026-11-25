import Tazuna.Smt.EncodeExact
import Tazuna.Semantics.Reach
import Tazuna.Semantics.Rules

/-! What `check` establishes about a service and the sites `P` of its program, which every step theorem rests on: the
sites are told apart by name, every effect function of a machine or reaction is a record of one of them, machine keys
have the canonical order, and no query answers a function. -/

namespace Tazuna.Smt

open Tazuna.Ir

structure Checked (P : List AnySite) (T : List TypeDecl) (v : ServiceV) : Prop where
  sites : SitesUnique P
  reach : v.Reach P
  keys : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true
  outputs : ∀ x ∈ v.queries, x.output.isFn = false

theorem Checked.machines {P : List AnySite} {T : List TypeDecl} {v : ServiceV} (hk : Checked P T v) :
    ∀ m ∈ v.machines, m.Reach P := hk.reach.1

theorem Checked.reactions {P : List AnySite} {T : List TypeDecl} {v : ServiceV} (hk : Checked P T v) :
    ∀ x ∈ v.reactions, x.Reach P := hk.reach.2

end Tazuna.Smt
