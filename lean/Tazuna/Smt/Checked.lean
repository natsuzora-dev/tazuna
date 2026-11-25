import Tazuna.Smt.EncodeExact
import Tazuna.Semantics.Reach
import Tazuna.Semantics.Rules

/-! What `check` establishes about a service and the sites `P` of its program, which every step theorem rests on: the
sites are told apart by name, every effect function of a machine or reaction is a record of one of them, machine keys
have the canonical order, no query answers a function, the stored state holds no function, and no bound is negative,
so each bound's count is the bound. `check_ok` derives it from a check with no finding, so `prove` starts from these
facts rather than assuming them (parse, don't validate). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- No bound is negative. -/
def _root_.Tazuna.Ir.BoundsV.Nonneg {r : Ty} (b : BoundsV r) : Prop :=
  0 ≤ b.items ∧ 0 ≤ b.cascade ∧ 0 ≤ b.steps ∧ ∀ c ∈ b.creates, 0 ≤ c.atMost

structure Checked (P : List AnySite) (T : List TypeDecl) (v : ServiceV) : Prop where
  sites : SitesUnique P
  reach : v.Reach P
  keys : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true
  outputs : ∀ x ∈ v.queries, x.output.isFn = false
  stored : v.records.wire = true ∧ ∀ m ∈ v.machines, m.state.wire = true
  bounds : v.bounds.Nonneg

theorem Checked.machines {P : List AnySite} {T : List TypeDecl} {v : ServiceV} (hk : Checked P T v) :
    ∀ m ∈ v.machines, m.Reach P := hk.reach.1

theorem Checked.reactions {P : List AnySite} {T : List TypeDecl} {v : ServiceV} (hk : Checked P T v) :
    ∀ x ∈ v.reactions, x.Reach P := hk.reach.2

/-- A spec that passed check: its program's types and sites, the spec its root evaluates to, and what check
established of each service. -/
structure CheckedSpec where
  T : List TypeDecl
  P : List AnySite
  spec : SpecV
  checked : ∀ v ∈ spec.services, Checked P T v

theorem isFn_of_wire : (t : Ty) → t.wire = true → t.isFn = false
  | .fn .., h => by simp [Ty.wire] at h
  | .int, _ | .str, _ | .param _, _ | .date, _ | .id, _ | .list _, _ | .bag _, _ | .tuple _, _ | .adt .., _
  | .table .., _ | .dsl .., _ => rfl

theorem nilL {α : Type} {a b : List α} (h : a ++ b = []) : a = [] := (List.append_eq_nil_iff.1 h).1
theorem nilR {α : Type} {a b : List α} (h : a ++ b = []) : b = [] := (List.append_eq_nil_iff.1 h).2

theorem none_of_ite {α : Type} {c : Prop} [Decidable c] {x : α} (h : (if c then none else some x) = none) : c := by
  split at h
  · assumption
  · cases h

theorem not_of_ite {α : Type} {c : Prop} [Decidable c] {x : α} (h : (if c then some x else none) = none) : ¬c := by
  split at h
  · cases h
  · assumption

/-- A check with no finding establishes `Checked` of every service, at the sites of the program the spec came from:
each fact's failure would be a finding. -/
theorem check_ok {T : List TypeDecl} {P : List AnySite} {s : SpecV} {handles : List HandleSite} (hP : SitesUnique P)
    (hreach : ∀ v ∈ s.services, v.Reach P) (h : SpecV.illegal T s handles = []) : ∀ v ∈ s.services, Checked P T v := by
  intro v hv
  simp only [SpecV.illegal] at h
  have hs := List.flatMap_eq_nil_iff.1 (nilR (nilL (nilL h))) v hv
  have hneg := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL hs)))
  have hkeys := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL hs)))))
  have hstate := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL (nilL (nilL (nilL hs))))))))
  have hwire := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL hs)))))))))
  refine ⟨hP, hreach v hv, fun m hm => ?_, fun q hq => ?_, ⟨?_, fun m hm => ?_⟩, ⟨?_, ?_, ?_, fun c hc => ?_⟩⟩
  · simpa using none_of_ite (hkeys m hm)
  · exact isFn_of_wire _ (none_of_ite (hwire (q.name ++ " output", q.output)
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨q, hq, by simp⟩)))))
  · exact none_of_ite (hstate ("records", v.records) (by simp))
  · exact none_of_ite (hstate (m.name ++ " state", m.state) (List.mem_cons_of_mem _ (List.mem_map_of_mem hm)))
  · have := not_of_ite (hneg ("items", v.bounds.items) (by simp)); omega
  · have := not_of_ite (hneg ("cascade", v.bounds.cascade) (by simp)); omega
  · have := not_of_ite (hneg ("steps", v.bounds.steps) (by simp)); omega
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have := not_of_ite (hneg (_, v.bounds.creates[k].atMost) (List.mem_append_right _ (List.mem_map.2
      ⟨(v.bounds.creates[k], v.bounds.creates[k].reads (tableProbes T v.records)),
        List.mem_iff_getElem.2 ⟨k, by simpa using hk, by simp⟩, rfl⟩)))
    omega

end Tazuna.Smt
