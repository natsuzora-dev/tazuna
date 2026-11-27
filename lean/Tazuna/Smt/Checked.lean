import Tazuna.Smt.EncodeExact
import Tazuna.Semantics.Reach
import Tazuna.Semantics.Rules
import Tazuna.Smt.Instances
import Tazuna.Trace.Wire

/-! What `check` establishes about a service and the sites `P` and effect sites `E` of its program, which every step
theorem rests on: the sites are told apart by name, every function the service keeps is a record of one of them, machine keys
have the canonical order, no query answers a function, the stored state holds no function, no bound is negative and `steps` is at least 1, so
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

/-- No bound is negative, and `steps` is at least 1. -/
def _root_.Tazuna.Ir.BoundsV.Legal {r : Ty} (b : BoundsV r) : Prop :=
  0 ≤ b.items ∧ 0 ≤ b.cascade ∧ 1 ≤ b.steps ∧ ∀ c ∈ b.creates, 0 ≤ c.atMost

/-- Whether the state's types, its events' and its callers' have SMT values and well-formedness terms: no function,
no type variable, ADT 0 only as Bool, and a plain key for every table but the pending table, whose keys are wire
ids. -/
def _root_.Tazuna.Ir.ServiceV.stateTys (v : ServiceV) : Bool :=
  let ok (t : Ty) := t.embeddable && t.plainKeys
  ok v.records && v.machines.all (ok ·.table) && ok (pendingEntry (shapes v)) && ok v.event && ok v.caller

/-- The types whose values cross the wire into or out of the service: its caller, its event, its commands' inputs and
rejections, its queries' inputs and outputs, its subscriptions' events, and the inputs, outputs and rejections of what
it may request. -/
def _root_.Tazuna.Ir.ServiceV.wireTys (v : ServiceV) : List Ty :=
  v.caller :: v.event :: v.commands.flatMap (fun c => [c.input, c.rejection]) ++
    v.queries.flatMap (fun q => [q.input, q.output]) ++ v.subscribes.map (·.event) ++
    v.declared.flatMap fun (_, d) => match d with
      | .externalCommand _ i o j => [i, o, j]
      | .externalQuery _ i o _ => [i, o]
      | _ => []

/-- Whether every wire type has a wire form for each of its values (`Ty.encodes`) and the canonical order with `==`
as its equality, so a value written reads back as the same value. -/
def _root_.Tazuna.Ir.ServiceV.wireOk (T : List TypeDecl) (v : ServiceV) : Bool :=
  v.wireTys.all fun t => t.encodes T && t.ordered T && t.comparable

structure Checked (P : List AnySite) (E : List AnyEffectSite) (T : List TypeDecl) (v : ServiceV) : Prop where
  sites : SitesUnique P
  reach : v.Reach P E
  keys : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true
  outputs : ∀ x ∈ v.queries, x.output.isFn = false
  stored : v.records.wire = true ∧ ∀ m ∈ v.machines, m.state.wire = true
  bounds : v.bounds.Legal
  sends : ∀ h ∈ v.sentHandles, v.lists h = true
  /-- Not a rule of check's: the loader builds every type of a program's values from the type table, whose ADT 0 is
  Bool, and the program from ground instances; check validates the result, so a loader bug is reported, not assumed. -/
  stateTys : v.stateTys = true
  /-- Not a rule of check's either: check's wireType rule leaves no function or fresh-id source on the wire
  (`wireTys_wire`) and its tagLabel rule no field keyed `tag`, so only a loader bug breaks it. -/
  wire : v.wireOk T = true
  /-- No two commands or queries share a name, so an in line's name picks one. -/
  requests : (v.commands.map (·.name) ++ v.queries.map (·.name)).Nodup
  /-- No two subscriptions name one source's event, so an event line picks one. -/
  subscriptions : (v.subscribes.map fun sub => (sub.source, sub.name)).Nodup
  /-- No machine's `instances` gives a key at the initial records, which hold no instance. -/
  idle : ∀ m ∈ v.machines, m.instances.fn (v.init, ()) = []

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
  simp only [MachineV.table, Ty.embeddable, Bool.and_eq_true] at hm'
  exact comparable_of_embeddable _ hm'.1.2

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

theorem nodup_of_duplicates {l : List String} (h : duplicates l = []) : l.Nodup := by
  unfold duplicates at h
  have hf : l.filter (fun n => l.count n > 1) = [] := by
    cases e : l.filter (fun n => l.count n > 1) with
    | nil => rfl
    | cons a as => rw [e] at h; simp [List.eraseDups_cons] at h
  rw [List.nodup_iff_count]
  intro a
  by_cases ha : a ∈ l
  · have := List.filter_eq_nil_iff.1 hf a ha
    simp only [decide_eq_true_eq, Nat.not_lt] at this
    exact this
  · rw [List.count_eq_zero_of_not_mem ha]; omega

theorem nil_of_eraseDups {α : Type} [BEq α] {l : List α} (h : l.eraseDups = []) : l = [] := by
  cases l with
  | nil => rfl
  | cons a as => simp [List.eraseDups_cons] at h

/-- Check's wireType rule reads every type `ServiceV.wireTys` lists: a check with no finding leaves no function or
fresh-id source on the wire, so `Checked.wire` fails only for what the loader builds (type variables, the prelude's
Bool and Nil, a variant's keys and atoms), never for a user's spec. -/
theorem wireTys_wire {T : List TypeDecl} {s : SpecV} {handles : List HandleSite} {captures : List (SiteId × List Ty)}
    {sent : ServiceV → List HandleSite} (h : SpecV.illegal T s handles captures sent = []) :
    ∀ v ∈ s.services, ∀ t ∈ v.wireTys, t.wire = true := by
  intro v hv t ht
  simp only [SpecV.illegal] at h
  have h0 := nil_of_eraseDups h
  have htop := nilL h0
  have own : ∀ w ∈ s.services, ∀ what t, (what, t) ∈ [("caller", w.caller), ("event", w.event)] ++
      w.commands.flatMap (fun c => [(c.name ++ " input", c.input), (c.name ++ " rejection", c.rejection)]) ++
      w.queries.flatMap (fun q => [(q.name ++ " input", q.input), (q.name ++ " output", q.output)]) ++
      w.sources.map (fun (n, t) => (n ++ " event", t)) → t.wire = true := fun w hw what t hp => by
    have hs := nilL (List.flatMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL htop))))) w hw)
    have hwire := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL hs))))))))))
    exact none_of_ite (hwire (what, t) hp)
  simp only [ServiceV.wireTys, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map] at ht
  rcases ht with (((rfl | rfl | ⟨c, hc, ht⟩) | ⟨q, hq, ht⟩) | ⟨sub, hsub, rfl⟩) | ⟨⟨x, d⟩, hd, ht⟩
  · exact own v hv "caller" _ (by simp)
  · exact own v hv "event" _ (by simp)
  · rcases ht with rfl | rfl | ht
    · exact own v hv (c.name ++ " input") _ (by simp only [List.mem_append, List.mem_flatMap]; exact .inl (.inl (.inr ⟨c, hc, by simp⟩)))
    · exact own v hv (c.name ++ " rejection") _ (by simp only [List.mem_append, List.mem_flatMap]; exact .inl (.inl (.inr ⟨c, hc, by simp⟩)))
    · simp at ht
  · rcases ht with rfl | rfl | ht
    · exact own v hv (q.name ++ " input") _ (by simp only [List.mem_append, List.mem_flatMap]; exact .inl (.inr ⟨q, hq, by simp⟩))
    · exact own v hv (q.name ++ " output") _ (by simp only [List.mem_append, List.mem_flatMap]; exact .inl (.inr ⟨q, hq, by simp⟩))
    · simp at ht
  · -- A subscription's event is a source's, which its declaring service or external checks.
    have hs := nilL (List.flatMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL htop))))) v hv)
    have hunk := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL (nilL (nilL (nilL hs)))))))) sub hsub
    have hany := none_of_ite hunk
    obtain ⟨⟨n, u⟩, hm, hnu⟩ := List.any_eq_true.1 hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hnu
    obtain ⟨⟨e⟩, -⟩ := Option.isSome_iff_exists.1 hnu.2
    rw [← e]
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨w, hw, hm⟩ := List.mem_flatMap.1 hm
      obtain ⟨⟨n', u'⟩, hm', he⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact own w hw (n' ++ " event") _ (List.mem_append_right _ (List.mem_map.2 ⟨(n', u'), hm', rfl⟩))
    · obtain ⟨x, hx, hm⟩ := List.mem_flatMap.1 hm
      obtain ⟨d, hd, hdu⟩ := List.mem_filterMap.1 hm
      cases d with
      | source n' u' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hdu
        obtain ⟨rfl, rfl⟩ := hdu
        have hext := List.filter_eq_nil_iff.1 (List.map_eq_nil_iff.1 (nilR (nilL (nilL (List.flatMap_eq_nil_iff.1
          (nilR (nilL (nilL (nilL htop)))) x hx))))) _ hd
        simpa [DeclaredV.wireTypes, DeclaredV.types] using hext
      | _ => simp at hdu
  · have hdecl := List.filter_eq_nil_iff.1 (List.map_eq_nil_iff.1 (List.flatMap_eq_nil_iff.1 (nilR h0) v hv)) _ hd
    simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hdecl
    cases d with
    | externalCommand _ i o j =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      exact hdecl t (by simp [DeclaredV.wireTypes, DeclaredV.types, ht])
    | externalQuery _ i o _ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      exact hdecl t (by simp [DeclaredV.wireTypes, DeclaredV.types, ht])
    | _ => simp at ht

/-- A check with no finding establishes `Checked` of every service, at the sites of the program the spec came from:
each fact's failure would be a finding. -/
theorem check_ok {T : List TypeDecl} {P : List AnySite} {E : List AnyEffectSite} {s : SpecV} {handles : List HandleSite}
    {captures : List (SiteId × List Ty)} (hP : SitesUnique P) (hreach : ∀ v ∈ s.services, v.Reach P E)
    (htys : ∀ v ∈ s.services, v.stateTys = true) (hok : ∀ v ∈ s.services, v.wireOk T = true)
    (h : SpecV.illegal T s handles captures ServiceV.sentHandles = []) : ∀ v ∈ s.services, Checked P E T v := by
  intro v hv
  simp only [SpecV.illegal] at h
  replace h := nilL (nil_of_eraseDups h)
  have hs := nilL (List.flatMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL h))))) v hv)
  have hsent := List.filterMap_eq_nil_iff.1 (List.flatMap_eq_nil_iff.1 (nilR (nilL h)) v hv)
  have hneg := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL hs))))
  have hkeys := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL (nilL hs))))))
  have hstate := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL hs)))))))))
  have hwire := List.filterMap_eq_nil_iff.1 (nilR (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL hs))))))))))
  have hnames := nilR (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL hs)))))))))))
  have hinits := List.filterMap_eq_nil_iff.1 (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL (nilL hs))))))))))))
  refine ⟨hP, hreach v hv, fun m hm => ?_, fun q hq => ?_, ⟨?_, fun m hm => ?_⟩, ⟨?_, ?_, ?_, fun c hc => ?_⟩,
    fun x hx => ?_, htys v hv, hok v hv, ?_, ?_, fun m hm => ?_⟩
  · simpa using none_of_ite (hkeys m hm)
  · exact isFn_of_wire _ (none_of_ite (hwire (q.name ++ " output", q.output)
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨q, hq, by simp⟩)))))
  · exact none_of_ite (hstate ("records", v.records) (by simp))
  · exact none_of_ite (hstate (m.name ++ " state", m.state) (List.mem_cons_of_mem _ (List.mem_map_of_mem hm)))
  · have := not_of_ite (hneg ("others_at_most", v.bounds.items, 0) (by simp)); simp only at this; omega
  · have := not_of_ite (hneg ("cascade", v.bounds.cascade, 0) (by simp)); simp only at this; omega
  · have := not_of_ite (hneg ("steps", v.bounds.steps, 1) (by simp)); simp only at this; omega
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have := not_of_ite (hneg (_, v.bounds.creates[k].atMost, 0) (List.mem_append_right _ (List.mem_map.2
      ⟨(v.bounds.creates[k], v.bounds.creates[k].reads (tableProbes T v.records)),
        List.mem_iff_getElem.2 ⟨k, by simpa using hk, by simp⟩, rfl⟩)))
    simp only at this
    omega
  · have hu := hsent x hx
    cases hn : x.name with
    | none => simp [ServiceV.lists, hn]
    | some n =>
      simp only [hn] at hu
      cases hb : v.lists x
      · simp [hb] at hu
      · rfl
  · exact nodup_of_duplicates (nilL (List.map_eq_nil_iff.1 (nilL hnames)))
  · have h2 := nilR hnames
    split at h2
    · assumption
    · cases h2
  · have h := hinits m hm
    cases he : (m.instances.fn (v.init, ())).isEmpty
    · simp [he] at h
    · exact List.isEmpty_iff.1 he

/-- A check with no finding names every handle by a literal and finds every external one declared. -/
theorem handles_ok {T : List TypeDecl} {s : SpecV} {handles : List HandleSite} {captures : List (SiteId × List Ty)}
    {sent : ServiceV → List HandleSite} (h : SpecV.illegal T s handles captures sent = []) :
    ∀ x ∈ handles, x.Named s := by
  intro x hx
  simp only [SpecV.illegal] at h
  replace h := nilL (nil_of_eraseDups h)
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
