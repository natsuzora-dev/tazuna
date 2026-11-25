import Tazuna.Smt.EncodeExact
import Tazuna.Semantics.Reach
import Tazuna.Semantics.Rules
import Tazuna.Smt.Instances

/-! What `check` establishes about a service and the sites `P` and effect sites `E` of its program, which every step
theorem rests on: the sites are told apart by name, every function the service keeps is a record of one of them, machine keys
have the canonical order, no query answers a function, the stored state holds no function, no bound is negative, so
each bound's count is the bound, and the state's types (records, instance tables, pending table) have SMT values
whose tables have plain keys. `check_ok` derives it from a check with no finding, so `prove` starts from these
facts rather than assuming them (parse, don't validate). -/

namespace Tazuna.Ir

mutual
/-- Whether a value of the type has an SMT value: data without functions or type variables, ADT 0 only as Bool. -/
def Ty.embeddable : Ty → Bool
  | .int | .str | .date | .id => true
  | .dsl k _ => k == .fresh
  | .adt 0 _ vs => (Tazuna.Smt.boolVs? vs).isSome
  | .adt (_ + 1) _ vs => Ty.embeddabless vs
  | .tuple ts => Ty.embeddables ts
  | .list t | .bag t => Ty.embeddable t
  | .table k v => Ty.embeddable k && Ty.embeddable v
  | .fn .. | .param _ => false
def Ty.embeddables : List Ty → Bool
  | [] => true
  | t :: ts => Ty.embeddable t && Ty.embeddables ts
def Ty.embeddabless : List (List Ty) → Bool
  | [] => true
  | ts :: vs => Ty.embeddables ts && Ty.embeddabless vs
end

end Tazuna.Ir

namespace Tazuna.Smt

open Tazuna.Ir

/-- No bound is negative. -/
def _root_.Tazuna.Ir.BoundsV.Nonneg {r : Ty} (b : BoundsV r) : Prop :=
  0 ≤ b.items ∧ 0 ≤ b.cascade ∧ 0 ≤ b.steps ∧ ∀ c ∈ b.creates, 0 ≤ c.atMost

/-- Whether the state's types, its events' and its callers' have SMT values and well-formedness terms: no function,
no type variable, ADT 0 only as Bool, and a plain key for every table but the pending table, whose keys are wire
ids. -/
def _root_.Tazuna.Ir.ServiceV.stateTys (v : ServiceV) : Bool :=
  let ok (t : Ty) := t.embeddable && t.plainKeys
  ok v.records && v.machines.all (ok ·.table) && ok (pendingEntry (shapes v)) && ok v.event && ok v.caller

structure Checked (P : List AnySite) (E : List AnyEffectSite) (T : List TypeDecl) (v : ServiceV) : Prop where
  sites : SitesUnique P
  reach : v.Reach P E
  keys : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true
  outputs : ∀ x ∈ v.queries, x.output.isFn = false
  stored : v.records.wire = true ∧ ∀ m ∈ v.machines, m.state.wire = true
  bounds : v.bounds.Nonneg
  sends : ∀ h ∈ v.sentHandles, v.lists h = true
  /-- Not a rule of check's: the loader builds every type of a program's values from the type table, whose ADT 0 is
  Bool, and the program from ground instances; check validates the result, so a loader bug is reported, not assumed. -/
  stateTys : v.stateTys = true

theorem Checked.machines {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} {v : ServiceV}
    (hk : Checked P E T v) : ∀ m ∈ v.machines, m.Reach P E := hk.reach.machines

theorem Checked.reactions {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} {v : ServiceV}
    (hk : Checked P E T v) : ∀ x ∈ v.reactions, x.Reach P E := hk.reach.reactions

mutual
theorem comparable_of_plain : (t : Ty) → t.plain = true → t.comparable = true
  | .int, _ | .date, _ | .str, _ | .id, _ => rfl
  | .tuple ts, h => comparables_of_plains ts h
  | .adt _ _ vs, h => comparabless_of_plainss vs h
  | .list _, h | .bag _, h | .table .., h | .fn .., h | .param _, h | .dsl .., h => by simp [Ty.plain] at h
theorem comparables_of_plains : (ts : List Ty) → Ty.plains ts = true → Ty.comparables ts = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.plains, Bool.and_eq_true] at h
    simp [Ty.comparables, comparable_of_plain t h.1, comparables_of_plains ts h.2]
theorem comparabless_of_plainss : (vs : List (List Ty)) → Ty.plainss vs = true → Ty.comparabless vs = true
  | [], _ => rfl
  | ts :: vs, h => by
    simp only [Ty.plainss, Bool.and_eq_true] at h
    simp [Ty.comparabless, comparables_of_plains ts h.1, comparabless_of_plainss vs h.2]
end

mutual
theorem comparable_of_embeddable : (t : Ty) → t.embeddable = true → t.comparable = true
  | .int, _ | .date, _ | .str, _ | .id, _ => rfl
  | .dsl k _, h => h
  | .adt 0 _ vs, h => by
    simp only [Ty.embeddable, Option.isSome_iff_exists] at h
    obtain ⟨⟨rfl⟩, _⟩ := h
    rfl
  | .adt (_ + 1) _ vs, h => comparabless_of_embeddabless vs h
  | .tuple ts, h => comparables_of_embeddables ts h
  | .list t, h | .bag t, h => comparable_of_embeddable t h
  | .table k v, h => by
    simp only [Ty.embeddable, Bool.and_eq_true] at h
    simp [Ty.comparable, comparable_of_embeddable k h.1, comparable_of_embeddable v h.2]
  | .fn _ _, h | .param _, h => by simp [Ty.embeddable] at h
theorem comparables_of_embeddables : (ts : List Ty) → Ty.embeddables ts = true → Ty.comparables ts = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.embeddables, Bool.and_eq_true] at h
    simp [Ty.comparables, comparable_of_embeddable t h.1, comparables_of_embeddables ts h.2]
theorem comparabless_of_embeddabless : (vs : List (List Ty)) → Ty.embeddabless vs = true → Ty.comparabless vs = true
  | [], _ => rfl
  | ts :: vs, h => by
    simp only [Ty.embeddabless, Bool.and_eq_true] at h
    simp [Ty.comparabless, comparables_of_embeddables ts h.1, comparabless_of_embeddabless vs h.2]
end

/-- A checked service's records are comparable: its records type is embeddable. -/
theorem Checked.recordsComparable {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} {v : ServiceV}
    (hk : Checked P E T v) : v.records.comparable = true := by
  have h := hk.stateTys
  simp only [ServiceV.stateTys, Bool.and_eq_true] at h
  exact comparable_of_embeddable _ h.1.1.1.1.1

/-- A checked service's machine keys and states are comparable: keys have the canonical order, and instance tables are
embeddable. -/
theorem Checked.machinesComparable {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} {v : ServiceV}
    (hk : Checked P E T v) : ∀ m ∈ v.machines, m.key.comparable = true ∧ m.state.comparable = true := fun m hm => by
  refine ⟨comparable_of_plain _ (Ty.plain_of_orderable _ (hk.keys m hm).1), ?_⟩
  have h := hk.stateTys
  simp only [ServiceV.stateTys, Bool.and_eq_true, List.all_eq_true] at h
  have hm' := (h.1.1.1.2 m hm)
  simp only [MachineV.table, instEntry, Ty.embeddable, Ty.embeddables, Bool.and_eq_true] at hm'
  exact comparable_of_embeddable _ hm'.1.2.1

/-- The handle has a literal name, and an external one is declared in each service's `declared`, as check's
unknownHandle rule compares them. -/
def _root_.Tazuna.Ir.HandleSite.Named (s : SpecV) (h : HandleSite) : Prop :=
  ∃ n, h.name = some n ∧ (!h.kind.startsWith "external" || s.services.all fun v =>
    v.declared.any fun (_, d) => d.kind == h.kind && d.name == n && (Ty.sames d.types h.types).isSome) = true

/-- A spec that passed check: its program, and what check established of each service of the spec the program's root
evaluates to and of each handle the program makes. -/
structure CheckedSpec where
  program : Program (.fn [] Ty.spec)
  checked : ∀ v ∈ (program.eval ()).services, Checked program.defs.sites program.defs.effectSites program.types v
  handles : ∀ h ∈ program.defs.handles, h.Named (program.eval ())

abbrev CheckedSpec.T (c : CheckedSpec) : List TypeDecl := c.program.types
abbrev CheckedSpec.P (c : CheckedSpec) : List AnySite := c.program.defs.sites
abbrev CheckedSpec.E (c : CheckedSpec) : List AnyEffectSite := c.program.defs.effectSites
abbrev CheckedSpec.spec (c : CheckedSpec) : SpecV := c.program.eval ()

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
theorem check_ok {T : List TypeDecl} {P : List AnySite} {E : List AnyEffectSite} {s : SpecV} {handles : List HandleSite}
    {captures : List (SiteId × List Ty)} (hP : SitesUnique P) (hreach : ∀ v ∈ s.services, v.Reach P E)
    (htys : ∀ v ∈ s.services, v.stateTys = true)
    (h : SpecV.illegal T s handles captures ServiceV.sentHandles = []) : ∀ v ∈ s.services, Checked P E T v := by
  intro v hv
  simp only [SpecV.illegal] at h
  have hs := List.flatMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL h))))) v hv
  have hsent := List.filterMap_eq_nil_iff.1 (List.flatMap_eq_nil_iff.1 (nilR (nilL h)) v hv)
  have hneg := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL hs))))
  have hkeys := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL (nilL hs))))))
  have hstate := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL hs)))))))))
  have hwire := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL hs))))))))))
  refine ⟨hP, hreach v hv, fun m hm => ?_, fun q hq => ?_, ⟨?_, fun m hm => ?_⟩, ⟨?_, ?_, ?_, fun c hc => ?_⟩,
    fun x hx => ?_, htys v hv⟩
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
  · have hu := hsent x hx
    cases hn : x.name with
    | none => simp [ServiceV.lists, hn]
    | some n =>
      simp only [hn] at hu
      cases hb : v.lists x
      · simp [hb] at hu
      · rfl

/-- A check with no finding names every handle by a literal and finds every external one declared. -/
theorem handles_ok {T : List TypeDecl} {s : SpecV} {handles : List HandleSite} {captures : List (SiteId × List Ty)}
    {sent : ServiceV → List HandleSite} (h : SpecV.illegal T s handles captures sent = []) :
    ∀ x ∈ handles, x.Named s := by
  intro x hx
  simp only [SpecV.illegal] at h
  have hu := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL h))) x hx
  cases hn : x.name with
  | none => simp [hn] at hu
  | some n =>
    refine ⟨n, hn, ?_⟩
    simp only [hn] at hu
    cases hb : (!x.kind.startsWith "external" || s.services.all fun v =>
      v.declared.any fun (_, d) => d.kind == x.kind && d.name == n && (Ty.sames d.types x.types).isSome)
    · simp only [hb] at hu; cases hu
    · rfl

end Tazuna.Smt
