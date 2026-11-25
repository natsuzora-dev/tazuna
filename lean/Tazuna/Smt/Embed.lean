import Tazuna.Smt.State
import Tazuna.Smt.Layout

/-! Embedding is exact: a value embeds exactly when every bag, list and table inside it has at most the slots its type
gets (`FitsV`), wherever the layout holds the type's datatypes (`Layout.HasWith`). With `decode_embed`, every value
within the slots is some model's, so a script with no model has no value within the bounds that breaks it: "no
model" means a bound is exceeded, never a gap in the encoding (Alloy's scope completeness). -/

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

section
variable (L : Layout)

mutual
/-- Every bag, list and table inside the value has at most the slots the layout gives its type. -/
def FitsV : (t : Ty) → t.den → Prop
  | .list t, xs => (show List t.den from xs).length ≤ L.count (.list t) ∧ ∀ x ∈ (show List t.den from xs), FitsV t x
  | .bag t, xs => (show List t.den from xs).length ≤ L.count (.bag t) ∧ ∀ x ∈ (show List t.den from xs), FitsV t x
  | .table k w, x => x.1.length ≤ L.count (.table k w) ∧ ∀ e ∈ x.1, FitsV k e.1 ∧ FitsV w e.2
  | .tuple ts, x => FitsVs ts x
  | .adt (_ + 1) _ vs, x => FitsAlts vs x
  | _, _ => True
def FitsVs : (ts : List Ty) → Ty.dens ts → Prop
  | [], _ => True
  | t :: ts, (x, xs) => FitsV t x ∧ FitsVs ts xs
def FitsAlts : (vs : List (List Ty)) → Ty.alts vs → Prop
  | [], _ => True
  | fs :: _, .inl x => FitsVs fs x
  | _ :: vs, .inr y => FitsAlts vs y
end

end

theorem mapM_isSome_iff {α β : Type} (f : α → Option β) : (xs : List α) → ((xs.mapM f).isSome ↔ ∀ x ∈ xs, (f x).isSome)
  | [] => by simp
  | x :: xs => by
    have ih := mapM_isSome_iff f xs
    rw [List.mapM_cons]
    cases hx : f x with
    | none => simp [hx]
    | some y => cases h : xs.mapM f <;> simp_all

theorem fillSlots_isSome (n w : Nat) (zs : List (List Val)) : (fillSlots n w zs).isSome ↔ zs.length ≤ n := by
  unfold fillSlots; split <;> simp_all

theorem count_of_find {L : Layout} {t : Ty} {d n : Nat} (h : L.find? t = some (d, n)) : L.count t = n := by
  simp [Layout.count, h]

theorem bind_fill_isSome {α : Type} (g : α → Option (List Val)) (xs : List α) (n w : Nat) (f : List (Bool × List Val) → Val) :
    (((xs.mapM g).bind (fillSlots n w)).map f).isSome ↔ (∀ x ∈ xs, (g x).isSome) ∧ xs.length ≤ n := by
  rw [Option.isSome_map]
  cases h : xs.mapM g with
  | none =>
    have : ¬ ∀ x ∈ xs, (g x).isSome := fun hs => by have := (mapM_isSome_iff g xs).2 hs; simp [h] at this
    simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    exact fun hs => absurd hs this
  | some zs =>
    have hl := mapM_some_length g xs zs h
    simp only [Option.bind_some, fillSlots_isSome, hl]
    exact ⟨fun hn => ⟨(mapM_isSome_iff g xs).1 (by simp [h]), hn⟩, fun hh => hh.2⟩

section
variable {L : Layout} {D : Dsl → List Ty → Prop}

mutual
/-- A value embeds exactly when its collections fit their slots, wherever the layout holds its type. -/
theorem embed_iff : (t : Ty) → Layout.HasWith L D t → t.embeddable = true → (x : t.den) →
    ((embedV L t x).isSome ↔ FitsV L t x)
  | .int, _, _, _ | .str, _, _, _ | .date, _, _, _ => by simp [embedV, FitsV]
  | .dsl k a, _, he, _ => by
    simp only [Ty.embeddable, beq_iff_eq] at he; subst he; simp [embedV, FitsV]
  | .id, hh, _, _ => by
    obtain ⟨⟨d, n⟩, hf⟩ := Option.isSome_iff_exists.1 hh
    simp [embedV, FitsV, hf]
  | .adt 0 a vs, _, he, x => by
    simp only [Ty.embeddable] at he
    obtain ⟨⟨rfl⟩, -⟩ := Option.isSome_iff_exists.1 he
    simp [embedV, FitsV]
  | .adt (i + 1) a vs, ⟨hs, hf⟩, he, x => by
    obtain ⟨⟨d, n⟩, hf⟩ := Option.isSome_iff_exists.1 hf
    simp only [embedV, hf, FitsV]
    exact embedAlts_iff d 0 vs hs he x
  | .tuple ts, ⟨hs, hf⟩, he, x => by
    obtain ⟨⟨d, n⟩, hf⟩ := Option.isSome_iff_exists.1 hf
    simp only [embedV, hf, FitsV, Option.isSome_map]
    exact embedVs_iff ts hs he x
  | .list t, ⟨ht, hp, hl⟩, he, xs => by
    obtain ⟨⟨d, n⟩, hl⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨⟨dt, m⟩, hp⟩ := Option.isSome_iff_exists.1 hp
    simp only [embedV, hl, hp, FitsV, count_of_find hl]
    refine (bind_fill_isSome (fun x => (embedV L t x).map ([·])) xs n 1 (slotsVal d dt)).trans ?_
    refine ⟨fun ⟨a, b⟩ => ⟨b, fun x hx => ?_⟩, fun ⟨a, b⟩ => ⟨fun x hx => ?_, a⟩⟩
    · exact (embed_iff t ht he x).1 (by simpa using a x hx)
    · simpa using (embed_iff t ht he x).2 (b x hx)
  | .bag t, ⟨ht, hp, hl⟩, he, xs => by
    obtain ⟨⟨d, n⟩, hl⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨⟨dt, m⟩, hp⟩ := Option.isSome_iff_exists.1 hp
    simp only [embedV, hl, hp, FitsV, count_of_find hl]
    refine (bind_fill_isSome (fun x => (embedV L t x).map ([·])) xs n 1 (slotsVal d dt)).trans ?_
    refine ⟨fun ⟨a, b⟩ => ⟨b, fun x hx => ?_⟩, fun ⟨a, b⟩ => ⟨fun x hx => ?_, a⟩⟩
    · exact (embed_iff t ht he x).1 (by simpa using a x hx)
    · simpa using (embed_iff t ht he x).2 (b x hx)
  | .table k w, ⟨hk, hw, hp, hl⟩, he, x => by
    simp only [Ty.embeddable, Bool.and_eq_true] at he
    obtain ⟨⟨d, n⟩, hl⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨⟨dt, m⟩, hp⟩ := Option.isSome_iff_exists.1 hp
    simp only [embedV, hl, hp, FitsV, count_of_find hl]
    refine (bind_fill_isSome (fun e => (embedV L k e.1).bind fun a => (embedV L w e.2).map fun b => [a, b]) x.1 n 2
      (slotsVal d dt)).trans ?_
    have hpair : ∀ e : k.den × w.den, (((embedV L k e.1).bind fun a => (embedV L w e.2).map fun b => [a, b]).isSome ↔
        FitsV L k e.1 ∧ FitsV L w e.2) := by
      intro e
      rw [← embed_iff k hk he.1 e.1, ← embed_iff w hw he.2 e.2]
      cases embedV L k e.1 <;> cases embedV L w e.2 <;> simp
    refine ⟨fun ⟨a, b⟩ => ⟨b, fun e he' => (hpair e).1 (a e he')⟩, fun ⟨a, b⟩ => ⟨fun e he' => (hpair e).2 (b e he'), a⟩⟩
  | .fn .., _, he, _ | .param _, _, he, _ => by simp [Ty.embeddable] at he
theorem embedVs_iff : (ts : List Ty) → Layout.HasWiths L D ts → Ty.embeddables ts = true → (x : Ty.dens ts) →
    ((embedVs L ts x).isSome ↔ FitsVs L ts x)
  | [], _, _, _ => by simp [embedVs, FitsVs]
  | t :: ts, ⟨ht, hts⟩, he, (x, xs) => by
    simp only [Ty.embeddables, Bool.and_eq_true] at he
    simp only [embedVs, FitsVs]
    rw [← embed_iff t ht he.1 x, ← embedVs_iff ts hts he.2 xs]
    cases embedV L t x <;> cases embedVs L ts xs <;> simp
theorem embedAlts_iff (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Layout.HasWithss L D vs →
    Ty.embeddabless vs = true → (x : Ty.alts vs) → ((embedAlts L d k vs x).isSome ↔ FitsAlts L vs x)
  | _, [], _, _, x => nomatch x
  | k, fs :: vs, ⟨hfs, _⟩, he, .inl x => by
    simp only [Ty.embeddabless, Bool.and_eq_true] at he
    simp only [embedAlts, FitsAlts, Option.isSome_map]
    exact embedVs_iff fs hfs he.1 x
  | k, _ :: vs, ⟨_, hvs⟩, he, .inr y => by
    simp only [Ty.embeddabless, Bool.and_eq_true] at he
    simp only [embedAlts, FitsAlts]
    exact embedAlts_iff d (k + 1) vs hvs he.2 y
end

end

section
variable {L : Layout} {v : ServiceV}

/-- Each machine's instance table fits its slots. -/
def MachinesFit (L : Layout) : {ms : List (MachineV v.records v.event)} → Step.Machines ms → Prop
  | _, .nil => True
  | m :: _, .cons insts sms =>
    (∀ h, FitsV L m.table (Ty.up _ m.table_data (m.tableOf insts h))) ∧ MachinesFit L sms

theorem embedMachines_iff (T : List TypeDecl) : {ms : List (MachineV v.records v.event)} → (sms : Step.Machines ms) →
    (∀ m ∈ ms, L.Has m.table ∧ m.table.embeddable = true) → (∀ sm ∈ sms.toSigma, InstancesOk T sm.1 sm.2) →
    ((embedMachines L sms).isSome ↔ MachinesFit L sms)
  | _, .nil, _, _ => by simp [embedMachines, MachinesFit]
  | m :: _, .cons insts sms, hm, hok => by
    have hu := (hok ⟨m, insts⟩ (by simp)).2
    have ih := embedMachines_iff T sms (fun m' h => hm m' (by simp [h])) (fun sm h => hok sm (by simp [h]))
    have e := embed_iff m.table (hm m (by simp)).1 (hm m (by simp)).2 (Ty.up _ m.table_data (m.tableOf insts hu))
    have hall : (∀ h, FitsV L m.table (Ty.up _ m.table_data (m.tableOf insts h))) ↔
        FitsV L m.table (Ty.up _ m.table_data (m.tableOf insts hu)) := ⟨fun f => f hu, fun f _ => f⟩
    simp only [embedMachines, MachinesFit]
    rw [dite_eq_left_of_eq_true (eq_true hu), hall, ← e, ← ih]
    cases embedV L m.table (Ty.up _ m.table_data (m.tableOf insts hu)) <;> cases embedMachines L sms <;> simp

/-- A state embeds exactly when its records, pending table and instance tables fit their slots, wherever the layout
holds their types: a state within the bounds always has an SMT value, so "no model" means a bound is exceeded. -/
theorem embedState_iff (T : List TypeDecl) {shs : List (PendingShape v.event)} (s : State v) (pv : PendingVal shs)
    (hr : L.Has v.records) (her : v.records.embeddable = true) (hp : L.Has (pendingTable shs))
    (hep : (pendingTable shs).embeddable = true) (hm : ∀ m ∈ v.machines, L.Has m.table ∧ m.table.embeddable = true)
    (hok : ∀ sm ∈ s.machines.toSigma, InstancesOk T sm.1 sm.2) :
    (embedState L s pv).isSome ↔
      FitsV L v.records (Ty.up _ v.records_data s.records) ∧ FitsV L (pendingTable shs) pv ∧ MachinesFit L s.machines := by
  have e1 := embed_iff v.records hr her (Ty.up _ v.records_data s.records)
  have e2 := embed_iff (pendingTable shs) hp hep pv
  have e3 := embedMachines_iff T s.machines hm hok
  simp only [embedState, embedPending]
  rw [← e1, ← e2, ← e3]
  cases embedV L v.records (Ty.up _ v.records_data s.records) <;>
    cases embedV L (pendingTable shs) pv <;> cases embedMachines L s.machines <;> simp

end

end Tazuna.Smt
