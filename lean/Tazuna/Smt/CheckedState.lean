import Tazuna.Smt.ServiceLayout
import Tazuna.Smt.Embed

/-! A checked service's state in its own layout: the well-formedness term of its symbolic state is always built
(`wf_ofService`), and a state embeds exactly when it fits its slots (`embedState_ofService`), with no hypothesis left
about the types: check establishes them (`Checked.stateTys`) and the layout holds their datatypes (`ofService_has`). -/

namespace Tazuna.Smt

open Tazuna.Ir

mutual
/-- A plain type with an SMT value compares by SMT-LIB's `=`. -/
theorem eqable_of_plain : (t : Ty) → t.embeddable = true → t.plain = true → t.eqable = true
  | .int, _, _ | .str, _, _ | .date, _, _ | .id, _, _ => rfl
  | .tuple ts, he, hp => by
    simp only [Ty.embeddable, Ty.plain, Ty.eqable] at he hp ⊢; exact eqables_of_plains ts he hp
  | .adt 0 _ vs, he, _ => by simpa [Ty.embeddable, Ty.eqable] using he
  | .adt (_ + 1) _ vs, he, hp => by
    simp only [Ty.embeddable, Ty.plain, Ty.eqable] at he hp ⊢; exact eqabless_of_plainss vs he hp
  | .list _, _, hp | .bag _, _, hp | .table .., _, hp | .fn .., _, hp | .param _, _, hp | .dsl .., _, hp => by
    simp [Ty.plain] at hp
theorem eqables_of_plains : (ts : List Ty) → Ty.embeddables ts = true → Ty.plains ts = true → Ty.eqables ts = true
  | [], _, _ => rfl
  | t :: ts, he, hp => by
    simp only [Ty.embeddables, Ty.plains, Ty.eqables, Bool.and_eq_true] at he hp ⊢
    exact ⟨eqable_of_plain t he.1 hp.1, eqables_of_plains ts he.2 hp.2⟩
theorem eqabless_of_plainss : (vs : List (List Ty)) → Ty.embeddabless vs = true → Ty.plainss vs = true →
    Ty.eqabless vs = true
  | [], _, _ => rfl
  | ts :: vs, he, hp => by
    simp only [Ty.embeddabless, Ty.plainss, Ty.eqabless, Bool.and_eq_true] at he hp ⊢
    exact ⟨eqables_of_plains ts he.1 hp.1, eqabless_of_plainss vs he.2 hp.2⟩
end

mutual
theorem plainKeys_of_plain : (t : Ty) → t.plain = true → t.plainKeys = true
  | .int, _ | .str, _ | .date, _ | .id, _ => rfl
  | .tuple ts, hp => by simp only [Ty.plain, Ty.plainKeys] at hp ⊢; exact plainKeyss_of_plains ts hp
  | .adt _ _ vs, hp => by simp only [Ty.plain, Ty.plainKeys] at hp ⊢; exact plainKeysss_of_plainss vs hp
  | .list _, hp | .bag _, hp | .table .., hp | .fn .., hp | .param _, hp | .dsl .., hp => by simp [Ty.plain] at hp
theorem plainKeyss_of_plains : (ts : List Ty) → Ty.plains ts = true → Ty.plainKeyss ts = true
  | [], _ => rfl
  | t :: ts, hp => by
    simp only [Ty.plains, Ty.plainKeyss, Bool.and_eq_true] at hp ⊢
    exact ⟨plainKeys_of_plain t hp.1, plainKeyss_of_plains ts hp.2⟩
theorem plainKeysss_of_plainss : (vs : List (List Ty)) → Ty.plainss vs = true → Ty.plainKeysss vs = true
  | [], _ => rfl
  | ts :: vs, hp => by
    simp only [Ty.plainss, Ty.plainKeysss, Bool.and_eq_true] at hp ⊢
    exact ⟨plainKeyss_of_plains ts hp.1, plainKeysss_of_plainss vs hp.2⟩
end

section
variable {L : Layout} {D : Dsl → List Ty → Prop}

theorem mapM_some_of {α β : Type} {f : α → Option β} {xs : List α} (h : ∀ x ∈ xs, (f x).isSome = true) :
    (xs.mapM f).isSome = true := by
  rw [mapM_isSome]; exact List.all_eq_true.2 h

mutual
/-- The well-formedness term of a value of a type with an SMT value and plain table keys is built wherever the layout
holds the type's datatypes. -/
theorem wfT_isSome : (t : Ty) → Layout.HasWith L D t → t.embeddable = true → t.plainKeys = true → (x : Term) →
    (wfT L t x).isSome = true
  | .int, _, _, _, _ | .str, _, _, _, _ | .date, _, _, _, _ => rfl
  | .id, hh, _, _, _ => by simp only [wfT, Option.isSome_map]; exact hh
  | .dsl k a, _, he, _, x => by
    simp only [Ty.embeddable, beq_iff_eq] at he; subst he; rfl
  | .adt 0 _ vs, _, he, _, _ => by simp only [Ty.embeddable] at he; simp [wfT, he]
  | .adt (i + 1) a vs, ⟨hvs, hf⟩, he, hk, x => by
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf
    simp only [Ty.embeddable, Ty.plainKeys] at he hk
    simp only [wfT, hd, Option.bind_some]
    exact wfAlts_isSome d 0 vs hvs he hk x
  | .tuple ts, ⟨hts, hf⟩, he, hk, x => by
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf
    simp only [Ty.embeddable, Ty.plainKeys] at he hk
    simp only [wfT, hd, Option.bind_some]
    exact wfFields_isSome d 0 ts hts he hk x 0
  | .bag t, ⟨ht, hf1, hf2⟩, he, hk, x => by
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 hf1
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf2
    simp only [Ty.embeddable, Ty.plainKeys] at he hk
    simp only [wfT, hd, hdt, Option.isSome_map]
    exact mapM_some_of fun sl _ => by rw [Option.isSome_map]; exact wfT_isSome t ht he hk _
  | .list t, ⟨ht, hf1, hf2⟩, he, hk, x => by
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 hf1
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf2
    simp only [Ty.embeddable, Ty.plainKeys] at he hk
    simp only [wfT, hd, hdt, Option.isSome_map]
    exact mapM_some_of fun sl _ => by rw [Option.isSome_map]; exact wfT_isSome t ht he hk _
  | .table k w, ⟨hk', hw, hf1, hf2⟩, he, hk, x => by
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 hf1
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf2
    simp only [Ty.embeddable, Ty.plainKeys, Bool.and_eq_true] at he hk
    have hkp := plainKeys_of_plain k hk.1
    simp only [wfT, hd, hdt, eqable_of_plain k he.1 hk.1, ite_true, Option.isSome_map]
    refine mapM_some_of fun sl _ => ?_
    rw [Option.isSome_map]
    obtain ⟨ck, hck⟩ := Option.isSome_iff_exists.1 (wfT_isSome k hk' he.1 hkp sl.2[0])
    obtain ⟨cw, hcw⟩ := Option.isSome_iff_exists.1 (wfT_isSome w hw he.2 hk.2 sl.2[1])
    simp [hck, hcw]
  | .fn .., _, he, _, _ | .param _, _, he, _, _ => by simp [Ty.embeddable] at he
theorem wfFields_isSome (d k : Nat) : (ts : List Ty) → Layout.HasWiths L D ts → Ty.embeddables ts = true →
    Ty.plainKeyss ts = true → (x : Term) → (j : Nat) → (wfFields L d k ts x j).isSome = true
  | [], _, _, _, _, _ => rfl
  | t :: ts, ⟨ht, hts⟩, he, hk, x, j => by
    simp only [Ty.embeddables, Ty.plainKeyss, Bool.and_eq_true] at he hk
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (wfT_isSome t ht he.1 hk.1 (.sel d k j x))
    simp only [wfFields, hc, Option.bind_some, Option.isSome_map]
    exact wfFields_isSome d k ts hts he.2 hk.2 x (j + 1)
theorem wfAlts_isSome (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Layout.HasWithss L D vs →
    Ty.embeddabless vs = true → Ty.plainKeysss vs = true → (x : Term) → (wfAlts L d k vs x).isSome = true
  | _, [], _, _, _, _ => rfl
  | k, fs :: vs, ⟨hfs, hvs⟩, he, hk, x => by
    simp only [Ty.embeddabless, Ty.plainKeysss, Bool.and_eq_true] at he hk
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (wfFields_isSome d k fs hfs he.1 hk.1 x 0)
    simp only [wfAlts, hc, Option.bind_some, Option.isSome_map]
    exact wfAlts_isSome d (k + 1) vs hvs he.2 hk.2 x
end

/-- The pending table's well-formedness term is built where its entries' is: its keys are wire ids. -/
theorem wfT_pending_isSome {e : Ty} {shs : List (PendingShape e)} (hh : Layout.HasWith L D (pendingTable shs))
    (he : (pendingEntry shs).embeddable = true) (hk : (pendingEntry shs).plainKeys = true) (x : Term) :
    (wfT L (pendingTable shs) x).isSome = true := by
  obtain ⟨-, hw, hf1, hf2⟩ := hh
  obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 hf1
  obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf2
  simp only [pendingTable] at hd hdt ⊢
  simp only [wfT, hd, hdt]
  simp only [Ty.eqable, ite_true, Option.isSome_map]
  refine mapM_some_of fun sl _ => ?_
  rw [Option.isSome_map]
  obtain ⟨cw, hcw⟩ := Option.isSome_iff_exists.1 (wfT_isSome _ hw he hk sl.2[1])
  simp [hcw]

theorem embeddable_pending {e : Ty} {shs : List (PendingShape e)} (he : (pendingEntry shs).embeddable = true) :
    (pendingTable shs).embeddable = true := by
  simp only [pendingTable, Ty.embeddable, Bool.and_eq_true]; exact ⟨rfl, he⟩

end

section
variable {G : List Ty} (defs : Defs G) {T : List TypeDecl} {v : ServiceV}

theorem stateTys_iff : v.stateTys = true ↔
    (v.records.embeddable = true ∧ v.records.plainKeys = true) ∧
      (∀ m ∈ v.machines, m.table.embeddable = true ∧ m.table.plainKeys = true) ∧
      (pendingEntry (shapes v)).embeddable = true ∧ (pendingEntry (shapes v)).plainKeys = true ∧
      (v.event.embeddable = true ∧ v.event.plainKeys = true) ∧ (v.caller.embeddable = true ∧ v.caller.plainKeys = true) := by
  simp [ServiceV.stateTys, and_assoc]

theorem wfMachines_isSome {L : Layout} : (ms : List (MachineV v.records v.event)) →
    (∀ m ∈ ms, L.Has m.table ∧ m.table.embeddable = true ∧ m.table.plainKeys = true) →
    (xs : PerMachine (fun _ => Term) ms) → (wfMachines L ms xs).isSome = true
  | [], _, .nil => rfl
  | m :: ms, hm, .cons x xs => by
    have h := hm m (by simp)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (wfT_isSome m.table h.1 h.2.1 h.2.2 x)
    simp only [wfMachines, hc, Option.bind_some, Option.isSome_map]
    exact wfMachines_isSome ms (fun m' h' => hm m' (by simp [h'])) xs

mutual
theorem sorted_of_embeddable : (t : Ty) → t.embeddable = true → t.sorted = true
  | .int, _ | .str, _ | .date, _ | .id, _ => rfl
  | .dsl k _, h => by simp only [Ty.embeddable, beq_iff_eq] at h; subst h; rfl
  | .adt 0 _ vs, h => by
    simp only [Ty.embeddable, Option.isSome_iff_exists] at h
    obtain ⟨⟨rfl⟩, -⟩ := h; rfl
  | .adt (_ + 1) _ vs, h => sortedss_of_embeddabless vs h
  | .tuple ts, h => sorteds_of_embeddables ts h
  | .list t, h | .bag t, h => sorted_of_embeddable t h
  | .table k w, h => by
    simp only [Ty.embeddable, Bool.and_eq_true] at h
    simp [Ty.sorted, sorted_of_embeddable k h.1, sorted_of_embeddable w h.2]
  | .fn .., h | .param _, h => by simp [Ty.embeddable] at h
theorem sorteds_of_embeddables : (ts : List Ty) → Ty.embeddables ts = true → Ty.sorteds ts = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.embeddables, Bool.and_eq_true] at h
    simp [Ty.sorteds, sorted_of_embeddable t h.1, sorteds_of_embeddables ts h.2]
theorem sortedss_of_embeddabless : (vs : List (List Ty)) → Ty.embeddabless vs = true → Ty.sortedss vs = true
  | [], _ => rfl
  | ts :: vs, h => by
    simp only [Ty.embeddabless, Bool.and_eq_true] at h
    simp [Ty.sortedss, sorteds_of_embeddables ts h.1, sortedss_of_embeddabless vs h.2]
end

theorem sortable_of_sorted : (t : Ty) → t.sorted = true → t.sortable = true
  | .fn .., h => by simp [Ty.sorted] at h
  | .int, h | .str, h | .date, h | .id, h | .param _, h | .list _, h | .bag _, h | .tuple _, h | .adt .., h
  | .table .., h | .dsl .., h => by simpa [Ty.sortable] using h

theorem sortable_of_embeddable (t : Ty) (h : t.embeddable = true) : t.sortable = true :=
  sortable_of_sorted t (sorted_of_embeddable t h)

/-- Every step type of a checked service has a sort, so its datatypes are in the service's layout. -/
theorem stepTys_has (hk : Checked defs.sites defs.effectSites T v) : ∀ t ∈ stepTys v, (Layout.ofService defs v).Has t := by
  obtain ⟨⟨her, -⟩, hms, hep, -, ⟨hee, -⟩, ⟨hec, -⟩⟩ := stateTys_iff.1 hk.stateTys
  have hsort : ∀ t ∈ stepTys v, t.sortable = true := by
    intro t ht
    simp only [stepTys, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ht
    rcases ht with ((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨m, hm, rfl⟩) | ⟨m, hm, rfl⟩
    · exact sortable_of_embeddable _ her
    · exact sortable_of_embeddable _ hee
    · exact sortable_of_embeddable _ hec
    · exact sortable_of_sorted _ (by simp [Ty.option, Ty.sorted, Ty.sorteds, Ty.sortedss, sorted_of_embeddable _ hee])
    · exact sortable_of_embeddable _ (embeddable_pending hep)
    · rfl
    · exact sortable_of_embeddable _ (hms m hm).1
    · have h := sorted_of_embeddable _ (hms m hm).1
      simp only [MachineV.table, Ty.sorted, Bool.and_eq_true] at h
      exact sortable_of_sorted _ (by simp [Ty.sorted, Ty.sorteds, h.1])
  exact fun t ht => ofService_has defs v t (List.mem_filter.2 ⟨List.mem_append_left _ (List.mem_append_left _ ht), hsort t ht⟩)

/-- The well-formedness term of a checked service's symbolic state is always built in its layout. -/
theorem wf_ofService (hk : Checked defs.sites defs.effectSites T v) (S : SymState v) :
    (S.wf (Layout.ofService defs v) (shapes v)).isSome = true := by
  have hs := stepTys_has defs hk
  obtain ⟨⟨her, hkr⟩, hms, hep, hkp, -⟩ := stateTys_iff.1 hk.stateTys
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1
    (wfT_isSome v.records (hs _ (by simp [stepTys])) her hkr S.records)
  obtain ⟨cp, hcp⟩ := Option.isSome_iff_exists.1
    (wfT_pending_isSome (hs _ (by simp [stepTys])) hep hkp S.pending)
  obtain ⟨cm, hcm⟩ := Option.isSome_iff_exists.1 (wfMachines_isSome v.machines
    (fun m hm => ⟨hs _ (by simp only [stepTys]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hm))), hms m hm⟩) S.machines)
  simp only [SymState.wf, wfPending, hc, hcp, hcm, Option.bind_some, Option.isSome_map, Option.isSome_some]

/-- A checked service's state embeds in its layout exactly when its records, pending table and instance tables fit
their slots: no assumption about the types is left. -/
theorem embedState_ofService (hk : Checked defs.sites defs.effectSites T v) (s : State v) (pv : PendingVal (shapes v))
    (hok : ∀ sm ∈ s.machines.toSigma, InstancesOk T sm.1 sm.2) :
    (embedState (Layout.ofService defs v) s pv).isSome ↔
      FitsV (Layout.ofService defs v) v.records (Ty.up _ v.records_data s.records) ∧
        FitsV (Layout.ofService defs v) (pendingTable (shapes v)) pv ∧
        MachinesFit (Layout.ofService defs v) s.machines := by
  have hs := stepTys_has defs hk
  obtain ⟨⟨her, -⟩, hms, hep, -, -⟩ := stateTys_iff.1 hk.stateTys
  exact embedState_iff T s pv (hs _ (by simp [stepTys])) her (hs _ (by simp [stepTys])) (embeddable_pending hep)
    (fun m hm => ⟨hs _ (by simp only [stepTys]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hm))), (hms m hm).1⟩) hok

/-- The service's layout holds every datatype a step script looks up once, so its step environment is found. -/
theorem stepEnv_ofService (hk : Checked defs.sites defs.effectSites T v) :
    ∃ senv, StepEnv.of (Layout.ofService defs v) (shapes v) = .ok senv := by
  have hs := stepTys_has defs hk
  have ho := find_of_has_option (e := v.event) (hs _ (by simp [stepTys]))
  have hp : (Layout.ofService defs v).Has (pendingTable (shapes v)) := hs _ (by simp [stepTys])
  obtain ⟨⟨dE, nE⟩, hE⟩ := Option.isSome_iff_exists.1 ho.1
  obtain ⟨⟨dopt, nopt⟩, hopt⟩ := Option.isSome_iff_exists.1 ho.2
  obtain ⟨⟨dP, nP⟩, hPE⟩ := Option.isSome_iff_exists.1 hp.2.1.2
  replace hPE : (Layout.ofService defs v).find? (pendingEntry (shapes v)) = some (dP, nP) := hPE
  obtain ⟨⟨dT, nT, dtT⟩, hT⟩ := collD_of_has_table hp
  unfold StepEnv.of
  split
  · exact ⟨_, rfl⟩
  all_goals simp_all [pendingTable]

/-- The service's layout holds the pending table, so the wire-id invariant's term is built. -/
theorem pendingBelowT_ofService (hk : Checked defs.sites defs.effectSites T v) (pending nextId : Term) :
    ∃ t, pendingBelowT (Layout.ofService defs v) (shapes v) pending nextId = .ok t := by
  have hp : (Layout.ofService defs v).Has (pendingTable (shapes v)) :=
    stepTys_has defs hk _ (by simp [stepTys])
  obtain ⟨x, hx⟩ := collD_of_has_table hp
  exact ⟨_, by simp only [pendingBelowT, pendingTable] at hx ⊢; rw [hx]; rfl⟩

end

end Tazuna.Smt
