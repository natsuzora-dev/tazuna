import Tazuna.Thm.Verify.Complete.Values

/-!
The renaming of ids stays one-to-one: `Ids.use` and `Ids.join` only append to the bound ids, and never bind an id that
is bound or held by a block to a second id.
-/

namespace Tazuna.Thm.Verify.Complete.Ids

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Complete.Values

/-- The trace ids that the blocks hold. -/
def held (ids : Ids) : List String := ids.blocks.flatMap (·.trace)

/-- The bound ids are one-to-one, and the blocks hold distinct trace ids that are not bound. -/
structure IdsWf (ids : Ids) : Prop where
  oneToOne : OneToOne ids.bound
  nodup : (held ids).Nodup
  free : ∀ t ∈ held ids, ∀ u ∈ ids.bound, u.trace ≠ t

theorem IdsWf.empty : IdsWf {} := ⟨by simp [OneToOne], by simp [held], by simp [held]⟩

/-- `ids'` keeps the bound ids of `ids`. -/
def Grows (ids ids' : Ids) : Prop := ids.bound <+: ids'.bound

theorem eq_of_mem_flatMap_nodup {α β : Type} (f : α → List β) :
    ∀ {L : List α} {a b : α} {x : β}, (L.flatMap f).Nodup → a ∈ L → b ∈ L → x ∈ f a → x ∈ f b → a = b
  | [], _, _, _, _, ha, _, _, _ => absurd ha List.not_mem_nil
  | c :: L, a, b, x, hn, ha, hb, hxa, hxb => by
    simp only [List.flatMap_cons, List.nodup_append] at hn
    rcases List.mem_cons.mp ha with ea | ha' <;> rcases List.mem_cons.mp hb with eb | hb'
    · rw [ea, eb]
    · subst ea; exact absurd rfl (hn.2.2 x hxa x (List.mem_flatMap.mpr ⟨b, hb', hxb⟩))
    · subst eb; exact absurd rfl (hn.2.2 x hxb x (List.mem_flatMap.mpr ⟨a, ha', hxa⟩))
    · exact eq_of_mem_flatMap_nodup f hn.2.1 ha' hb' hxa hxb

theorem takes_iff {r : Renaming} {t : String} : r.takes t = true ↔ ∃ u ∈ r, u.trace = t := by
  simp [Renaming.takes]

theorem traceOf?_none_iff {r : Renaming} {s : String} : r.traceOf? s = none ↔ ∀ u ∈ r, u.snapshot ≠ s := by
  simp [Renaming.traceOf?, List.find?_eq_none]

theorem traceOf?_append_none {r : Renaming} {u : Use} (h : r.traceOf? u.snapshot = none) :
    (r ++ [u]).traceOf? u.snapshot = some u.trace := by
  simp only [Renaming.traceOf?, List.find?_append]
  rw [show r.find? (·.snapshot == u.snapshot) = none from by simpa using traceOf?_none_iff.mp h]
  simp

theorem oneToOne_append {r : Renaming} {u : Use} (h : OneToOne r) (hs : ∀ v ∈ r, v.snapshot ≠ u.snapshot)
    (ht : ∀ v ∈ r, v.trace ≠ u.trace) : OneToOne (r ++ [u]) := by
  intro a ha b hb
  simp only [List.mem_append, List.mem_singleton] at ha hb
  rcases ha with ha | rfl <;> rcases hb with hb | rfl
  · exact h a ha b hb
  · exact ⟨fun e => absurd e (hs a ha), fun e => absurd e (ht a ha)⟩
  · exact ⟨fun e => absurd e.symm (hs b hb), fun e => absurd e.symm (ht b hb)⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem sublist_flatMap {α β : Type} (f : α → List β) : ∀ {L : List α} {b : α}, b ∈ L → (f b).Sublist (L.flatMap f)
  | [], _, h => absurd h List.not_mem_nil
  | c :: L, b, h => by
    simp only [List.flatMap_cons]
    rcases List.mem_cons.mp h with e | h
    · subst e; exact List.sublist_append_left _ _
    · exact (sublist_flatMap f h).trans (List.sublist_append_right _ _)

theorem flatMap_erase_sublist (s t : String) : ∀ (bs : List Block),
    ((bs.map (fun b => if b.snapshot.contains s then
      { b with snapshot := b.snapshot.erase s, trace := b.trace.erase t } else b)).flatMap (·.trace)).Sublist
      (bs.flatMap (·.trace))
  | [] => List.Sublist.slnil
  | b :: bs => by
    simp only [List.map_cons, List.flatMap_cons]
    refine List.Sublist.append ?_ (flatMap_erase_sublist s t bs)
    split
    · exact List.erase_sublist
    · exact List.Sublist.refl _

theorem use_spec {ids ids' : Ids} {u : Use} (h : ids.use u = some ids') :
    Grows ids ids' ∧ ids'.bound.traceOf? u.snapshot = some u.trace ∧ (IdsWf ids → IdsWf ids') := by
  unfold Ids.use at h
  cases hs : ids.bound.traceOf? u.snapshot with
  | some t =>
    rw [hs] at h
    by_cases e : (t == u.trace) = true
    · simp only [e, ite_true, Option.some.injEq] at h
      subst h
      simp only [beq_iff_eq] at e
      exact ⟨List.prefix_refl _, by rw [hs, e], id⟩
    · simp [e] at h
  | none =>
    rw [hs] at h
    simp only at h
    have hns := traceOf?_none_iff.mp hs
    split at h
    · rename_i b hb
      split at h
      · rename_i ht
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨List.prefix_append _ _, traceOf?_append_none hs, fun w => ?_⟩
        have hbm : b ∈ ids.blocks := List.mem_of_find?_eq_some hb
        have hsb : b.snapshot.contains u.snapshot = true := by simpa using List.find?_some hb
        have htb : u.trace ∈ b.trace := by simpa using ht
        have hheld : u.trace ∈ held ids := List.mem_flatMap.mpr ⟨b, hbm, htb⟩
        have sub := flatMap_erase_sublist u.snapshot u.trace ids.blocks
        refine ⟨oneToOne_append w.oneToOne hns (fun v hv e => w.free _ hheld v hv e), w.nodup.sublist sub,
          fun x hx v hv => ?_⟩
        have hx' : x ∈ held ids := sub.subset hx
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact w.free x hx' v hv
        · intro e
          subst e
          obtain ⟨b', hb', hx⟩ := List.mem_flatMap.mp hx
          obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hb'
          split at hx
          · have hn : b₀.trace.Nodup := w.nodup.sublist (sublist_flatMap (·.trace) hb₀)
            simp [hn.mem_erase_iff] at hx
          · rename_i hc
            have := eq_of_mem_flatMap_nodup (·.trace) (show (ids.blocks.flatMap (·.trace)).Nodup from w.nodup)
              hb₀ hbm hx htb
            subst this
            exact hc hsb
      · cases h
    · split at h
      · cases h
      · rename_i hr
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨List.prefix_append _ _, traceOf?_append_none hs, fun w => ?_⟩
        have hnr : ∀ t ∈ held ids, t ≠ u.trace := fun t ht e => by
          subst e
          apply hr
          simp only [Ids.reserved, Bool.or_eq_true, List.any_eq_true]
          obtain ⟨b, hb, ht⟩ := List.mem_flatMap.mp ht
          exact .inr ⟨b, hb, by simpa using ht⟩
        have hnb : ∀ v ∈ ids.bound, v.trace ≠ u.trace := fun v hv e => by
          apply hr
          simp only [Ids.reserved, Bool.or_eq_true]
          exact .inl (takes_iff.mpr ⟨v, hv, e⟩)
        refine ⟨oneToOne_append w.oneToOne hns hnb, w.nodup, fun x hx v hv => ?_⟩
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact w.free x hx v hv
        · exact fun e => hnr x hx e.symm

theorem useIds_spec {ids ids' : Ids} {l sl : Nat} {a b : Option String} (h : ids.useIds l sl a b = some ids') :
    Grows ids ids' ∧ (∀ s, a = some s → ∃ t, b = some t ∧ ids'.bound.traceOf? s = some t) ∧ (a = none → b = none) ∧
      (IdsWf ids → IdsWf ids') := by
  unfold Ids.useIds at h
  split at h
  · obtain ⟨g, ht, w⟩ := use_spec h
    refine ⟨g, fun s hs => ?_, fun h => ?_, w⟩
    · cases Option.some.inj hs; exact ⟨_, rfl, ht⟩
    · cases h
  · cases h
    exact ⟨List.prefix_refl _, (fun _ h => nomatch h), fun _ => rfl, id⟩
  · cases h

theorem useOwn_spec {ids ids' : Ids} {l sl : Nat} {a b : Option String} (h : ids.useOwn l sl a b = some ids') :
    Grows ids ids' ∧ (∀ s t, a = some s → b = some t → ids'.bound.traceOf? s = some t) ∧
      (IdsWf ids → IdsWf ids') := by
  unfold Ids.useOwn at h
  split at h
  · obtain ⟨g, ht, w⟩ := use_spec h
    refine ⟨g, fun s t hs ht' => ?_, w⟩
    cases Option.some.inj hs; cases Option.some.inj ht'; exact ht
  · cases h
    refine ⟨List.prefix_refl _, fun s t hs ht => ?_, id⟩
    rename_i hn
    exact (hn s t hs ht).elim

theorem flatMap_modify {f : Block → Block} (x : String) (hf : ∀ b, (f b).trace = b.trace ++ [x]) :
    ∀ (bs : List Block) (i : Nat), i < bs.length → ((bs.modify i f).flatMap (·.trace)).Perm (x :: bs.flatMap (·.trace))
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | b :: bs, 0, _ => by
    simp only [List.modify_zero_cons, List.flatMap_cons, hf, List.append_assoc, List.singleton_append]
    exact List.perm_middle
  | b :: bs, i + 1, h => by
    simp only [List.modify_succ_cons, List.flatMap_cons]
    exact (List.Perm.append_left _ (flatMap_modify x hf bs i (by simpa using h))).trans List.perm_middle

theorem join_spec {ids ids' : Ids} {w : Nat} {l : Line} {u : Use} (h : ids.join w l u = some ids') :
    Grows ids ids' ∧ (IdsWf ids → IdsWf ids') := by
  unfold Ids.join at h
  split at h
  · obtain ⟨g, _, wf⟩ := use_spec h
    exact ⟨g, wf⟩
  · rename_i hk
    have hr : ids.reserved u.trace = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hk; exact hk.2
    have hnh : u.trace ∉ held ids := fun ht => by
      obtain ⟨b, hb, ht⟩ := List.mem_flatMap.mp ht
      simp only [Ids.reserved, Bool.or_eq_false_iff, List.any_eq_false] at hr
      exact hr.2 b hb (by simpa using ht)
    have hnb : ∀ v ∈ ids.bound, v.trace ≠ u.trace := fun v hv e => by
      simp only [Ids.reserved, Bool.or_eq_false_iff] at hr
      have := takes_iff.mpr ⟨v, hv, e⟩
      simp [hr.1] at this
    have finish : ∀ ids' : Ids, ids'.bound = ids.bound → (held ids').Perm (u.trace :: held ids) → Grows ids ids' ∧
        (IdsWf ids → IdsWf ids') := fun ids' hb hp => by
      refine ⟨by show ids.bound <+: ids'.bound; rw [hb]; exact List.prefix_refl _,
        fun wf => ⟨hb ▸ wf.oneToOne, ?_, fun x hx v hv => ?_⟩⟩
      · exact hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hnh, wf.nodup⟩)
      · rw [hb] at hv
        rcases List.mem_cons.mp (hp.subset hx) with rfl | hx
        · exact hnb v hv
        · exact wf.free x hx v hv
    split at h
    · rename_i i hi
      simp only [Option.some.injEq] at h
      subst h
      refine finish _ rfl ?_
      exact flatMap_modify u.trace (fun _ => rfl) ids.blocks i (List.findIdx?_eq_some_iff_getElem.mp hi).1
    · simp only [Option.some.injEq] at h
      subst h
      refine finish _ rfl ?_
      simp only [held, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.perm_append_singleton _ _

end Tazuna.Thm.Verify.Complete.Ids
