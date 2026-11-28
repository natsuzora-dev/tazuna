import Tazuna.Explore.Link
import Tazuna.Trace.ReplayOk
import Tazuna.Trace.WriteOk

/-! Related nodes move alike: from nodes `Link` relates, each input explore tries from the first has a related one it
tries from the second, and the two transitions show the same classes, fault and broken responses and reach related
nodes (`link_move`). -/

namespace Tazuna.Explore

open Tazuna.Ir Tazuna.Ir.Step

theorem perm_flatMap_congr {α β : Type} {f g : α → List β} :
    (xs : List α) → (∀ a ∈ xs, (f a).Perm (g a)) → (xs.flatMap f).Perm (xs.flatMap g)
  | [], _ => .refl _
  | x :: xs, h => by
    simp only [List.flatMap_cons]
    exact (h x List.mem_cons_self).append (perm_flatMap_congr xs fun a ha => h a (List.mem_cons_of_mem _ ha))

section Ids
variable {R : PBij}

mutual
theorem idsIn_rel : (t : Ty) → (x y : t.den0) → Ty.rel0 R t x y → Multi (IdV.Rel R) (idsIn t x) (idsIn t y)
  | .list t, _, _, h => Multi.flatMap (fun a b hab => idsIn_rel t a b hab) (Multi.of_forall2 h)
  | .bag t, _, _, h => Multi.flatMap (fun a b hab => idsIn_rel t a b hab) h
  | .table k v, _, _, h => Multi.flatMap (fun _ _ hab => (idsIn_rel k _ _ hab.1).append (idsIn_rel v _ _ hab.2)) h
  | .tuple ts, x, y, h => idssIn_rel ts x y h
  | .adt _ _ vs, x, y, h => idsAltsIn_rel vs x y h
  | .id, _, _, h => Multi.of_forall2 ⟨h, trivial⟩
  | .int, _, _, _ | .str, _, _, _ | .point _, _, _, _ | .fn .., _, _, _ | .param _, _, _, _ | .dsl .., _, _, _ =>
    Multi.nil
theorem idssIn_rel : (ts : List Ty) → (x y : (Ty.semsWith Dsl.base ts).1) →
    Ty.relsWith Dsl.base (Dsl.rel0 R) R ts x y → Multi (IdV.Rel R) (idssIn ts x) (idssIn ts y)
  | [], (), (), _ => Multi.nil
  | t :: ts, (x, xs), (y, ys), ⟨h, hs⟩ => (idsIn_rel t x y h).append (idssIn_rel ts xs ys hs)
theorem idsAltsIn_rel : (vs : List (List Ty)) → (x y : (Ty.semAltsWith Dsl.base vs).1) →
    Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs x y → Multi (IdV.Rel R) (idsAltsIn vs x) (idsAltsIn vs y)
  | [], x, _, _ => nomatch x
  | fs :: _, .inl x, .inl y, h => idssIn_rel fs x y h
  | _ :: vs, .inr x, .inr y, h => idsAltsIn_rel vs x y h
  | _ :: _, .inl _, .inr _, h | _ :: _, .inr _, .inl _, h => h.elim
end

variable (T : List TypeDecl)

mutual
theorem idsOf_perm : (t : Ty) → (x : t.den0) → (Trace.idsOf T t x).Perm (idsIn t x)
  | .list t, xs => by
    simp only [Trace.idsOf, idsIn]
    exact perm_flatMap_congr xs fun a _ => idsOf_perm t a
  | .bag t, xs => by
    simp only [Trace.idsOf, idsIn]
    exact ((List.mergeSort_perm _ _).flatMap_right _).trans (perm_flatMap_congr xs fun a _ => idsOf_perm t a)
  | .table k v, x => by
    simp only [Trace.idsOf, idsIn]
    exact ((List.mergeSort_perm _ _).flatMap_right _).trans
      (perm_flatMap_congr x.1 fun a _ => (idsOf_perm k a.1).append (idsOf_perm v a.2))
  | .tuple ts, x => idsOfs_perm ts x
  | .adt _ _ vs, x => idsOfAlts_perm vs x
  | .id, _ => .refl _
  | .int, _ | .str, _ | .point _, _ | .fn .., _ | .param _, _ | .dsl .., _ => .refl _
theorem idsOfs_perm : (ts : List Ty) → (x : (Ty.semsWith Dsl.base ts).1) → (Trace.idsOfs T ts x).Perm (idssIn ts x)
  | [], () => .refl _
  | t :: ts, (x, xs) => (idsOf_perm t x).append (idsOfs_perm ts xs)
theorem idsOfAlts_perm : (vs : List (List Ty)) → (x : (Ty.semAltsWith Dsl.base vs).1) →
    (Trace.idsOfAlts T vs x).Perm (idsAltsIn vs x)
  | [], x => nomatch x
  | fs :: _, .inl x => idsOfs_perm fs x
  | _ :: vs, .inr y => idsOfAlts_perm vs y
end

theorem idsOf_rel {t : Ty} {x y : t.den0} (h : Ty.rel0 R t x y) :
    Multi (IdV.Rel R) (Trace.idsOf T t x) (Trace.idsOf T t y) :=
  ((idsIn_rel t x y h).perm_left (idsOf_perm T t x).symm).perm_right (idsOf_perm T t y).symm

end Ids

section StateIds
variable {v : ServiceV} {R : Ren}

theorem machineIds_rel {r e : Ty} : {ms : List (MachineV r e)} → {l l' : Machines ms} → Machines.Ren R.ctr l l' →
    Multi (IdV.Rel R.ctr) (l.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => idsIn m.key i.key ++ idsIn m.state i.state)
      (l'.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => idsIn m.key i.key ++ idsIn m.state i.state)
  | [], .nil, .nil, _ => Multi.nil
  | _ :: _, .cons _ _, .cons _ _, h => by
    simp only [PerMachine.toSigma_cons, List.flatMap_cons]
    exact (Multi.flatMap (fun _ _ hab => (idsIn_rel _ _ _ hab.1).append (idsIn_rel _ _ _ hab.2))
      (Multi.of_forall2 h.1)).append (machineIds_rel h.2)

theorem pendingIds_rel {e : Ty} {p q : Pending e} (h : Pending.Rel R p q) :
    Multi (IdV.Rel R.ctr) (pendingIds p) (pendingIds q) := by
  obtain ⟨id, snd, ext, req⟩ := p
  obtain ⟨id', snd', ext', req'⟩ := q
  obtain ⟨-, hs, -, hr⟩ := h
  refine Multi.append ?_ ?_
  · cases hs with
    | machine n hk => cases hk with | mk hk => exact idsIn_rel _ _ _ hk
    | reaction n => exact Multi.nil
  · cases hr with
    | mk _ _ _ _ hv _ _ => exact idsIn_rel _ _ _ hv

theorem stateIds_rel {s s' : State v} (h : StateRen R s s') :
    Multi (IdV.Rel R.ctr) (stateIds s) (stateIds s') :=
  ((idsIn_rel _ _ _ h.1).append (machineIds_rel h.2.1)).append
    (Multi.flatMap (fun _ _ hab => pendingIds_rel hab) (Multi.of_forall2 h.2.2.1))

end StateIds

section Sorting
variable {R : PBij}

theorem contains_rel {l l' : List IdV} (h : Multi (IdV.Rel R) l l') {x x' : IdV} (hx : IdV.Rel R x x') :
    l.contains x = l'.contains x' := by
  simp only [List.contains_eq_any_beq]
  exact Multi.any_eq (fun a b hab => by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact IdV.rel_eq hx hab) h

theorem IdV.le_total (a b : IdV) : (IdV.le a b || IdV.le b a) = true := by
  cases a <;> cases b <;> simp only [IdV.le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.true_or, Bool.or_true]
  · omega
  · exact String.le_total _ _

theorem IdV.le_antisymm {a b : IdV} (h : IdV.le a b = true) (h' : IdV.le b a = true) : a = b := by
  cases a <;> cases b <;> simp only [IdV.le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    reduceCtorEq] at h h' ⊢
  · rename_i c i c' i'
    have : c = c' ∧ i = i' := by omega
    rw [this.1, this.2]
  · rename_i x y
    rw [Subtype.ext (String.le_antisymm h h')]

theorem IdV.le_trans {a b c : IdV} (h : IdV.le a b = true) (h' : IdV.le b c = true) : IdV.le a c = true := by
  cases a <;> cases b <;> cases c <;> simp only [IdV.le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, reduceCtorEq] at h h' ⊢
  · omega
  · exact String.le_trans h h'

theorem sort_perm_eq {l l' : List IdV} (h : l.Perm l') : l.mergeSort IdV.le = l'.mergeSort IdV.le :=
  List.Perm.eq_of_pairwise (le := fun a b => IdV.le a b = true) (fun _ _ _ _ => IdV.le_antisymm)
    (List.pairwise_mergeSort (le := IdV.le) (fun _ _ _ => IdV.le_trans) IdV.le_total l)
    (List.pairwise_mergeSort (le := IdV.le) (fun _ _ _ => IdV.le_trans) IdV.le_total l')
    (((List.mergeSort_perm _ _).trans h).trans (List.mergeSort_perm _ _).symm)

theorem forall2_eraseDups {α β : Type} [BEq α] [BEq β] {r : α → β → Prop}
    (hb : ∀ a b a' b', r a b → r a' b' → (a == a') = (b == b')) :
    (xs : List α) → (ys : List β) → Forall2 r xs ys → Forall2 r xs.eraseDups ys.eraseDups
  | [], [], _ => by simp only [List.eraseDups_nil]; trivial
  | a :: xs, b :: ys, ⟨hab, h⟩ => by
    rw [List.eraseDups_cons, List.eraseDups_cons]
    exact ⟨hab, forall2_eraseDups hb _ _ (forall2_filter (fun a' b' h' => by rw [hb _ _ _ _ h' hab]) h)⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim
termination_by xs => xs.length
decreasing_by simp only [List.length_cons]; have := List.length_filter_le (fun b => !b == a) xs; omega

theorem IdV.le_rel (hmo : R.Mono) {a b a' b' : IdV} (ha : IdV.Rel R a a') (hb : IdV.Rel R b b') :
    IdV.le a b = IdV.le a' b' := by
  rcases ha with ⟨s, rfl, rfl⟩ | ⟨c, c', i, hc, rfl, rfl⟩ <;> rcases hb with ⟨t, rfl, rfl⟩ | ⟨d, d', j, hd, rfl, rfl⟩
  · rfl
  · rfl
  · rfl
  · have := hmo hc hd
    rw [Bool.eq_iff_iff]
    simp only [IdV.le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rcases Nat.lt_trichotomy c d with h | rfl | h
    · rw [Nat.compare_eq_lt.2 h] at this
      have h' := Nat.compare_eq_lt.1 this.symm
      omega
    · rw [Nat.compare_eq_eq.2 rfl] at this
      have h' := Nat.compare_eq_eq.1 this.symm
      omega
    · rw [Nat.compare_eq_gt.2 h] at this
      have h' := Nat.compare_eq_gt.1 this.symm
      omega

/-- Related ids, sorted and deduplicated, relate item by item. -/
theorem sortIds_rel (hmo : R.Mono) {l l' : List IdV} (h : Multi (IdV.Rel R) l l') :
    Forall2 (IdV.Rel R) (sortIds l) (sortIds l') := by
  obtain ⟨zs, hz, hp⟩ := h
  have h1 := forall2_mergeSort (le := IdV.le) (le' := IdV.le) hz fun _ _ _ _ ha hb => IdV.le_rel hmo ha hb
  rw [sort_perm_eq hp] at h1
  exact forall2_eraseDups (fun _ _ _ _ ha hb => by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact IdV.rel_eq ha hb) _ _ h1

end Sorting

section Lists
variable {α β γ δ : Type} {r : α → β → Prop}

theorem forall2_zip_same {κ : Type} : (ks : List κ) → {xs : List α} → {ys : List β} → Forall2 r xs ys →
    Forall2 (fun p q => p.1 = q.1 ∧ r p.2 q.2) (ks.zip xs) (ks.zip ys)
  | [], _, _, _ => by simp only [List.zip_nil_left]; trivial
  | _ :: _, [], [], _ => by simp only [List.zip_nil_right]; trivial
  | k :: ks, _ :: _, _ :: _, ⟨h, hs⟩ => ⟨⟨rfl, h⟩, forall2_zip_same ks hs⟩
  | _ :: _, [], _ :: _, h | _ :: _, _ :: _, [], h => h.elim

theorem forall2_map2 {r' : γ → δ → Prop} {f : α → γ} {g : β → δ} (hfg : ∀ a b, r a b → r' (f a) (g b)) :
    {xs : List α} → {ys : List β} → Forall2 r xs ys → Forall2 r' (xs.map f) (ys.map g)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨hfg _ _ h, forall2_map2 hfg hs⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem forall2_map_mem {r' : γ → δ → Prop} {f : α → γ} {g : β → δ} :
    {xs : List α} → {ys : List β} → (∀ a ∈ xs, ∀ b, r a b → r' (f a) (g b)) → Forall2 r xs ys →
    Forall2 r' (xs.map f) (ys.map g)
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, hfg, ⟨h, hs⟩ =>
    ⟨hfg _ List.mem_cons_self _ h, forall2_map_mem (fun a ha b hab => hfg a (List.mem_cons_of_mem _ ha) b hab) hs⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

theorem forall2_refl_of {s : α → α → Prop} : (xs : List α) → (∀ a ∈ xs, s a a) → Forall2 s xs xs
  | [], _ => trivial
  | x :: xs, h => ⟨h x List.mem_cons_self, forall2_refl_of xs fun a ha => h a (List.mem_cons_of_mem _ ha)⟩

theorem forall2_filterMap {r' : γ → δ → Prop} {f : α → Option γ} {g : β → Option δ}
    (hfg : ∀ a b, r a b → Option.Rel r' (f a) (g b)) :
    {xs : List α} → {ys : List β} → Forall2 r xs ys → Forall2 r' (xs.filterMap f) (ys.filterMap g)
  | [], [], _ => trivial
  | a :: _, b :: _, ⟨h, hs⟩ => by
    have := hfg a b h
    simp only [List.filterMap_cons]
    revert this
    cases f a <;> cases g b <;> intro ho <;> cases ho
    · exact forall2_filterMap hfg hs
    · exact ⟨by assumption, forall2_filterMap hfg hs⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem seqs_rel {xs : List α} {ys : List β} (h : Forall2 r xs ys) :
    (n : Nat) → Forall2 (Forall2 r) (seqs xs n) (seqs ys n)
  | 0 => ⟨trivial, trivial⟩
  | n + 1 => ⟨trivial, forall2_flatMap2 (fun _ _ hab => forall2_map2 (fun _ _ h' => ⟨hab, h'⟩) (seqs_rel h n)) h⟩

theorem picks_rel (strict : Bool) : (xs : List α) → (ys : List β) → Forall2 r xs ys →
    (n : Nat) → Forall2 (Forall2 r) (picks strict xs n) (picks strict ys n)
  | _, _, _, 0 => by simp only [picks]; exact ⟨trivial, trivial⟩
  | [], [], _, _ + 1 => by simp only [picks]; exact ⟨trivial, trivial⟩
  | x :: xs, y :: ys, ⟨hxy, h⟩, n + 1 => by
    simp only [picks]
    refine forall2_append (forall2_map2 (fun _ _ h' => ⟨hxy, h'⟩) ?_) (picks_rel strict xs ys h (n + 1))
    cases strict
    · exact picks_rel false (x :: xs) (y :: ys) ⟨hxy, h⟩ n
    · exact picks_rel true xs ys h n
  | [], _ :: _, h, _ + 1 | _ :: _, [], h, _ + 1 => h.elim
termination_by xs _ _ n => (n, xs.length)

theorem pairsOf_rel {κ κ' ν ν' : Type} {rk : κ → κ' → Prop} {rv : ν → ν' → Prop} {vs : List ν} {vs' : List ν'}
    (hv : Forall2 rv vs vs') : {ks : List κ} → {ks' : List κ'} → Forall2 rk ks ks' →
    Forall2 (Forall2 fun e e' => rk e.1 e'.1 ∧ rv e.2 e'.2) (pairsOf vs ks) (pairsOf vs' ks')
  | [], [], _ => ⟨trivial, trivial⟩
  | _ :: _, _ :: _, ⟨hk, h⟩ => by
    simp only [pairsOf]
    exact forall2_flatMap2 (fun a b hab => forall2_map2 (fun _ _ h' => ⟨⟨hk, hab⟩, h'⟩) (pairsOf_rel hv h)) hv
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem pairwise_forall2 {p : α → α → Prop} {q : β → β → Prop} (hpq : ∀ a b a' b', r a b → r a' b' → (p a a' ↔ q b b')) :
    {xs : List α} → {ys : List β} → Forall2 r xs ys → (xs.Pairwise p ↔ ys.Pairwise q)
  | [], [], _ => by simp
  | a :: xs, b :: ys, ⟨hab, h⟩ => by
    simp only [List.pairwise_cons, pairwise_forall2 hpq h]
    refine and_congr_left fun _ => ⟨fun h' b' hb' => ?_, fun h' a' ha' => ?_⟩
    · obtain ⟨a', ha', hr⟩ := forall2_mem_right h b' hb'
      exact (hpq _ _ _ _ hab hr).1 (h' a' ha')
    · obtain ⟨b', hb', hr⟩ := forall2_mem_left h a' ha'
      exact (hpq _ _ _ _ hab hr).2 (h' b' hb')
  | [], _ :: _, h | _ :: _, [], h => h.elim

end Lists

section Domain
variable {v : ServiceV} {R : PBij} {d d' : Domain}

/-- Domains whose leaves relate by `R`. -/
structure DomRel (R : PBij) (d d' : Domain) : Prop where
  ints : d.ints = d'.ints
  strs : d.strs = d'.strs
  ids : Forall2 (IdV.Rel R) d.ids d'.ids
  instants : Forall2 (R.point .ms) d.instants d'.instants
  items : d.items = d'.items

mutual
theorem cands_rel (hd : DomRel R d d') : (t : Ty) → t.comparable = true →
    Forall2 (Ty.rel0 R t) (cands d t) (cands d' t)
  | .int, _ => by simp only [cands, hd.ints]; exact forall2_refl_of _ fun _ _ => rfl
  | .str, _ => by simp only [cands, hd.strs]; exact forall2_refl_of _ fun _ _ => rfl
  | .point .ms, _ => hd.instants
  | .point .day, _ => trivial
  | .id, _ => hd.ids
  | .list t, hc => by simp only [cands, hd.items]; exact seqs_rel (cands_rel hd t hc) _
  | .bag t, hc => by
    simp only [cands, hd.items]
    exact forall2_imp (fun _ _ h => Multi.of_forall2 h) (picks_rel false _ _ (cands_rel hd t hc) _)
  | .table k v, hc => by
    simp only [Ty.comparable, Bool.and_eq_true] at hc
    simp only [cands, hd.items]
    refine forall2_flatMap2 (fun ks ks' hks => forall2_filterMap (fun xs ys hxy => ?_)
      (pairsOf_rel (cands_rel hd v hc.2) hks)) (picks_rel true _ _ (cands_rel hd k hc.1) _)
    have hu : KeysUnique (Ty.semWith Dsl.base k).2 xs ↔ KeysUnique (Ty.semWith Dsl.base k).2 ys :=
      pairwise_forall2 (fun a b a' b' hab hab' => by
        have e1 : Ty.deq0 k a.1 a'.1 = Ty.deq0 k b.1 b'.1 := Ty.rel0_deq k hc.1 hab.1 hab'.1
        have e2 : Ty.deq0 k a'.1 a.1 = Ty.deq0 k b'.1 b.1 := Ty.rel0_deq k hc.1 hab'.1 hab.1
        unfold Ty.deq0 at e1 e2
        rw [e1, e2]) hxy
    by_cases h : KeysUnique (Ty.semWith Dsl.base k).2 xs
    · simp only [h, hu.1 h, ↓reduceDIte]
      exact .some (Multi.of_forall2 hxy)
    · simp only [h, mt hu.2 h, ↓reduceDIte]
      exact .none
  | .tuple ts, hc => candss_rel hd ts hc
  | .adt _ _ vs, hc => candAlts_rel hd vs hc
  | .fn .., hc => by simp [Ty.comparable] at hc
  | .param _, _ | .dsl .., _ => trivial
theorem candss_rel (hd : DomRel R d d') : (ts : List Ty) → Ty.comparables ts = true →
    Forall2 (Ty.relsWith Dsl.base (Dsl.rel0 R) R ts) (candss d ts) (candss d' ts)
  | [], _ => ⟨trivial, trivial⟩
  | t :: ts, hc => by
    simp only [Ty.comparables, Bool.and_eq_true] at hc
    simp only [candss]
    exact forall2_flatMap2 (fun a b hab => forall2_map2 (fun _ _ h => ⟨hab, h⟩) (candss_rel hd ts hc.2))
      (cands_rel hd t hc.1)
theorem candAlts_rel (hd : DomRel R d d') : (vs : List (List Ty)) → Ty.comparabless vs = true →
    Forall2 (Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs) (candAlts d vs) (candAlts d' vs)
  | [], _ => trivial
  | fs :: vs, hc => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    simp only [candAlts]
    exact forall2_append (forall2_map2 (f := Sum.inl) (g := Sum.inl) (fun _ _ h => h) (candss_rel hd fs hc.1))
      (forall2_map2 (f := Sum.inr) (g := Sum.inr) (fun _ _ h => h) (candAlts_rel hd vs hc.2))
end

end Domain

section Nodes
variable {T : List TypeDecl} {v : ServiceV} {R : Ren}

theorem newId_go_named (used : List String) : (fuel k : Nat) → ∃ s, newId.go used fuel k = .named s
  | 0, _ => ⟨_, rfl⟩
  | fuel + 1, k => by
    unfold newId.go
    dsimp only
    split
    · exact newId_go_named used fuel (k + 1)
    · split
      · exact ⟨_, rfl⟩
      · exact newId_go_named used fuel (k + 1)

theorem filterMap_named_eq {l l' : List IdV} (h : Forall2 (IdV.Rel R.ctr) l l') :
    l.filterMap IdV.nameOf = l'.filterMap IdV.nameOf := by
  induction l generalizing l' with
  | nil => cases l' <;> first | rfl | exact h.elim
  | cons a l ih =>
    cases l' with
    | nil => exact h.elim
    | cons b l' =>
      obtain ⟨hab, h⟩ := h
      rcases hab with ⟨s, rfl, rfl⟩ | ⟨c, c', i, -, rfl, rfl⟩
      · simp only [List.filterMap_cons, IdV.nameOf, ih h]
      · simp only [List.filterMap_cons, IdV.nameOf]; exact ih h

/-- Related nodes offer related ids, in the same order. -/
theorem ids_rel (hmo : R.ctr.Mono) {a b : Node v} (h : NodeRen R a b) : Forall2 (IdV.Rel R.ctr) a.ids b.ids := by
  have hs := sortIds_rel hmo (Multi.filter (p := IdV.isNamed) (q := IdV.isNamed)
    (fun x y hxy => by rcases hxy with ⟨s, rfl, rfl⟩ | ⟨c, c', i, -, rfl, rfl⟩ <;> rfl) (stateIds_rel h.state))
  have hheld := forall2_append h.shown hs
  unfold Node.ids
  simp only
  refine forall2_append hheld ⟨?_, trivial⟩
  unfold newId
  simp only
  rw [filterMap_named_eq hheld]
  obtain ⟨s, hs⟩ := newId_go_named ((b.shown ++ sortIds ((stateIds b.state).filter IdV.isNamed)).filterMap
    IdV.nameOf) _ 0
  rw [hs]
  exact .inl ⟨s, rfl, rfl⟩

theorem point_add {P : PBij} {a b : Int} (h : P.point .ms a b) (w : Int) : P.point .ms (a + w) (b + w) :=
  PBij.point_ms_of (by rw [PBij.point_ms_eq h]; omega)

theorem domainOf_rel (hmo : R.ctr.Mono) {a b : Node v} (h : NodeRen R a b) (sc : ScopeV) (kind name : String) :
    DomRel R.ctr (domainOf sc a kind name) (domainOf sc b kind name) :=
  ⟨rfl, rfl, ids_rel hmo h, ⟨h.state.2.2.2.1, forall2_map2 (fun w w' (e : w = w') => by
    subst e; exact point_add h.state.2.2.2.1 w) (forall2_refl_of sc.waits fun _ _ => rfl)⟩, rfl⟩

theorem timers_rel {records records' : v.records.den0} (hrec : Ty.rel0 R.ctr v.records records records') :
    {ms : List (MachineV v.records v.event)} → (∀ m ∈ ms, m.Equi) → {l l' : Machines ms} → Machines.Ren R.ctr l l' →
    Forall2 (R.ctr.point .ms)
      (l.toSigma.flatMap fun ⟨_, insts⟩ => insts.filterMap fun i => (timerOf records i).map (·.1))
      (l'.toSigma.flatMap fun ⟨_, insts⟩ => insts.filterMap fun i => (timerOf records' i).map (·.1))
  | [], _, .nil, .nil, _ => trivial
  | m :: _, hms, .cons _ _, .cons _ _, h => by
    simp only [PerMachine.toSigma_cons, List.flatMap_cons]
    refine forall2_append (forall2_filterMap (fun i i' hi => ?_) h.1)
      (timers_rel hrec (fun m' h' => hms m' (List.mem_cons_of_mem _ h')) h.2)
    have ht := timerAt_rel (hms m List.mem_cons_self) hrec hi.1 hi.2
    unfold timerOf
    revert ht
    generalize m.timerAt records i.key i.state = x
    generalize m.timerAt records' i'.key i'.state = y
    intro ht
    cases ht with
    | none => exact .none
    | some hxy => exact .some hxy.1

theorem eraseDups_sort_rel {P : PBij} {l l' : List Int} (h : Forall2 (P.point .ms) l l') :
    Forall2 (P.point .ms) ((l.mergeSort (· ≤ ·)).eraseDups) ((l'.mergeSort (· ≤ ·)).eraseDups) :=
  forall2_eraseDups (fun _ _ _ _ ha hb => PBij.point_beq ha hb) _ _
    (forall2_mergeSort h fun _ _ _ _ ha hb => by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]; exact (PBij.point_ms_iff ha hb).2.1)

/-- Related nodes move the clock to related times. -/
theorem clockTimes_rel (ho : Ordered T v) (sc : ScopeV) {a b : Node v} (h : NodeRen R a b) :
    Forall2 (R.ctr.point .ms) (clockTimes sc a) (clockTimes sc b) := by
  have hnow := h.state.2.2.2.1
  unfold clockTimes
  simp only
  refine eraseDups_sort_rel (forall2_map2 (fun x y hxy => ?_) (forall2_append
    (forall2_map2 (fun w w' (e : w = w') => by subst e; exact point_add hnow w)
      (forall2_refl_of sc.waits fun _ _ => rfl))
    (forall2_flatMap2 (f := fun d => [d, d + 1]) (g := fun d => [d, d + 1])
      (fun x y hxy => ⟨hxy, point_add hxy 1, trivial⟩) (forall2_append
      (timers_rel h.state.1 ho.equi.machines h.state.2.1) ?_))))
  · have e1 := PBij.point_ms_eq hnow
    have e2 := PBij.point_ms_eq hxy
    exact PBij.point_ms_of (by rw [e1, e2]; omega)
  · have hw := h.watch
    revert hw
    cases a.watch <;> cases b.watch <;> intro hw <;> cases hw
    · trivial
    · rename_i ws ws' hws
      refine forall2_flatMap2 (fun x y hxy => ?_) (forall2_zip_same v.responses hws)
      obtain ⟨hr, htrs⟩ := hxy
      rw [hr]
      exact forall2_map2 (fun e e' he => point_add he.2 _) htrs

end Nodes

section Inputs
variable {T : List TypeDecl} {v : ServiceV} {R : Ren}

theorem forall2_flatMap_same {α γ δ : Type} {r : γ → δ → Prop} {f : α → List γ} {g : α → List δ} :
    (xs : List α) → (∀ a ∈ xs, Forall2 r (f a) (g a)) → Forall2 r (xs.flatMap f) (xs.flatMap g)
  | [], _ => trivial
  | x :: xs, h => by
    simp only [List.flatMap_cons]
    exact forall2_append (h x List.mem_cons_self) (forall2_flatMap_same xs fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem forall2_flatMap_mem {α β γ δ : Type} {r : α → β → Prop} {r' : γ → δ → Prop} {f : α → List γ}
    {g : β → List δ} : {xs : List α} → {ys : List β} → (∀ a ∈ xs, ∀ b, r a b → Forall2 r' (f a) (g b)) →
    Forall2 r xs ys → Forall2 r' (xs.flatMap f) (ys.flatMap g)
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, hfg, ⟨h, hs⟩ => by
    simp only [List.flatMap_cons]
    exact forall2_append (hfg _ List.mem_cons_self _ h)
      (forall2_flatMap_mem (fun a ha b hab => hfg a (List.mem_cons_of_mem _ ha) b hab) hs)
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

theorem answerTy_comparable {o : Ty} {rj : Option Ty} (ho : o.comparable = true)
    (hj : ∀ j, rj = some j → j.comparable = true) : (answerTy o rj).comparable = true := by
  cases rj with
  | none => exact ho
  | some j => simp [answerTy, Ty.result, Ty.comparable, Ty.comparables, Ty.comparabless, ho, hj j rfl]

/-- Related nodes offer related inputs, in the same order. -/
theorem inputsOf_rel {P : List AnySite} {E : List AnyEffectSite} (chk : Smt.Checked P E T v) (ho : Ordered T v)
    (hmo : R.ctr.Mono) (sc : ScopeV) {a b : Node v} (ha : Inv P a.state) (h : NodeRen R a b) :
    Forall2 (Input.Ren R) (inputsOf sc a) (inputsOf sc b) := by
  have hw : ∀ t ∈ v.wireTys, t.comparable = true := fun t ht => (Trace.wire_ordered chk ht).2
  have hcaller := hw _ Trace.caller_wire
  unfold inputsOf
  simp only
  refine forall2_append (forall2_append (forall2_append (forall2_append ?_ ?_) ?_) ?_)
    (forall2_map2 (fun _ _ ht => Input.Ren.clock ht) (clockTimes_rel ho sc h))
  · refine forall2_flatMap_same _ fun i _ => ?_
    have hd := domainOf_rel hmo h sc "command" (v.commands.get i).name
    exact forall2_flatMap2 (r := Ty.rel0 R.ctr v.caller) (fun c c' hc => forall2_map2 (fun x x' hx => Input.Ren.command i hc hx)
      (cands_rel hd _ (hw _ (Trace.command_wire i)))) (cands_rel hd _ hcaller)
  · refine forall2_flatMap_same _ fun i _ => ?_
    have hd := domainOf_rel hmo h sc "query" (v.queries.get i).name
    exact forall2_flatMap2 (r := Ty.rel0 R.ctr v.caller) (fun c c' hc => forall2_map2 (fun x x' hx => Input.Ren.query i hc hx)
      (cands_rel hd _ (hw _ (Trace.query_wire i)))) (cands_rel hd _ hcaller)
  · refine forall2_flatMap_mem (fun p hp q hpq => ?_) h.state.2.2.1
    have htys := Trace.atShapes_tys (ha.shaped p hp)
    obtain ⟨id, snd, ext, req⟩ := p
    obtain ⟨id', snd', ext', req'⟩ := q
    obtain ⟨hid, -, -, hreq⟩ := hpq
    cases hreq with
    | mk name input output rejection hval hholds hon =>
      exact forall2_map2 (fun x x' hx => Input.Ren.answer hid (.mk hx)) (cands_rel (domainOf_rel hmo h sc _ name) _
        (answerTy_comparable (hw _ htys.2.1) fun j hj => hw _ (htys.2.2 j hj)))
  · refine forall2_flatMap_same _ fun i _ => ?_
    have hd := domainOf_rel hmo h sc "source" (v.subscribes.get i).name
    exact forall2_map2 (fun x x' hx => Input.Ren.event i hx) (cands_rel hd _ (hw _ (Trace.subscribe_wire i)))

end Inputs

section Moves
variable {T : List TypeDecl} {v : ServiceV} {R : Ren}

theorem altIndex_rel {P : PBij} : (vs : List (List Ty)) → {x y : (Ty.semAltsWith Dsl.base vs).1} →
    Ty.relAltsWith Dsl.base (Dsl.rel0 P) P vs x y → altIndex vs x = altIndex vs y
  | [], x, _, _ => nomatch x
  | _ :: _, .inl _, .inl _, _ => rfl
  | _ :: vs, .inr _, .inr _, h => by simp only [altIndex, altIndex_rel vs h]
  | _ :: _, .inl _, .inr _, h | _ :: _, .inr _, .inl _, h => h.elim

theorem variantOf_rel {P : PBij} : {t : Ty} → {x y : t.den0} → Ty.rel0 P t x y → variantOf T t x = variantOf T t y
  | .adt _ _ vs, _, _, h => by simp only [variantOf, altIndex_rel vs h]
  | .int, _, _, _ | .str, _, _, _ | .list _, _, _, _ | .tuple _, _, _, _ | .fn .., _, _, _ | .param _, _, _, _
  | .bag _, _, _, _ | .table .., _, _, _ | .point _, _, _, _ | .id, _, _, _ | .dsl .., _, _, _ => rfl

theorem classes_rel {x x' : Input v} (hx : Input.Ren R x x') {r r' : Result v} (hr : ResultRen R r r') :
    classes T v x r = classes T v x' r' := by
  obtain ⟨-, ho, hev, hout⟩ := hr
  unfold classes
  rw [forall2_map_eq _ (fun ev => OutClass.event (variantOf T v.event ev)) (fun _ _ h => by rw [variantOf_rel h]) hev,
    forall2_map_eq (fun o => OutClass.request o.external o.name) (fun o => OutClass.request o.external o.name)
      (fun _ _ h => by rw [h.2.1, h.2.2.1]) hout]
  congr 1
  revert ho
  cases r.outcome <;> cases r'.outcome <;> intro ho <;> cases ho <;> cases hx <;> try rfl
  all_goals first
    | (simp only [answerClasses]; done)
    | (rename_i h _ _ _ _ _ _ _; simp only [answerClasses, variantOf_rel h])

theorem timely_rel {s s' : State v} (hs : StateRen R s s') {t t' : Int} (ht : R.ctr.point .ms t t')
    (hms : ∀ m ∈ v.machines, m.Equi) : timely s t = timely s' t' := by
  unfold timely
  have key : ∀ {ms : List (MachineV v.records v.event)}, (∀ m ∈ ms, m.Equi) → ∀ {l l' : Machines ms},
      Machines.Ren R.ctr l l' →
      (l.toSigma.all fun ⟨_, insts⟩ => insts.all fun i => match timerOf s.records i with
        | some (d, _) => decide (t ≤ d) | none => true) =
      (l'.toSigma.all fun ⟨_, insts⟩ => insts.all fun i => match timerOf s'.records i with
        | some (d, _) => decide (t' ≤ d) | none => true) := by
    intro ms hms l l' hl
    induction ms with
    | nil => cases l; cases l'; rfl
    | cons m ms ih =>
      cases l with
      | cons x xs => cases l' with
        | cons y ys =>
          simp only [PerMachine.toSigma_cons, List.all_cons]
          rw [ih (fun m' h' => hms m' (List.mem_cons_of_mem _ h')) hl.2]
          congr 1
          refine forall2_all_eq (fun i i' hi => ?_) hl.1
          have htm := timerAt_rel (hms m List.mem_cons_self) hs.1 hi.1 hi.2
          unfold timerOf
          revert htm
          generalize m.timerAt s.records i.key i.state = a
          generalize m.timerAt s'.records i'.key i'.state = b
          intro htm
          cases htm with
          | none => rfl
          | some hab =>
            rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
            exact (PBij.point_ms_iff ht hab.1).2.1
  exact key hms hs.2.1

theorem timelyAt_rel {s s' : State v} (hs : StateRen R s s') {x x' : Input v} (hx : Input.Ren R x x')
    (hms : ∀ m ∈ v.machines, m.Equi) : timelyAt s x = timelyAt s' x' := by
  cases hx with
  | clock ht => exact timely_rel hs ht hms
  | _ => rfl

/-- Waiting triggers related by `R`. -/
abbrev TrigRel (R : PBij) (a b : v.event.den0 × Int) : Prop := Ty.rel0 R v.event a.1 b.1 ∧ R.point .ms a.2 b.2

theorem watchStep_rel (ho : Ordered T v) {resp : ResponseV v.records v.event} (hresp : resp ∈ v.responses)
    {m m' : Moment v.event} (ht : R.ctr.point .ms m.time m'.time) (hev : Forall2 (Ty.rel0 R.ctr v.event) m.events m'.events)
    {trs trs' : List (v.event.den0 × Int)} (htrs : Forall2 (TrigRel R.ctr) trs trs') :
    (watchStep resp m trs).1 = (watchStep resp m' trs').1 ∧
      Forall2 (TrigRel R.ctr) (watchStep resp m trs).2 (watchStep resp m' trs').2 := by
  have hself := (ho.equi.self R.ctr).responses resp hresp
  have hans : ∀ a a', Ty.rel0 R.ctr v.event a a' → resp.answers a m = resp.answers a' m' := fun a a' ha =>
    forall2_any (fun e e' he => toB_rel (hself.then_ (a, e, ()) (a', e', ()) ⟨ha, he, trivial⟩)) hev
  have hop : ∀ a a', Ty.rel0 R.ctr v.event a a' → resp.opens a = resp.opens a' := fun a a' ha =>
    toB_rel (hself.after (a, ()) (a', ()) ⟨ha, trivial⟩)
  have hlate : ∀ a b : v.event.den0 × Int, TrigRel R.ctr a b → decide (m.time > a.2 + (resp.withinNat : Int)) =
      decide (m'.time > b.2 + (resp.withinNat : Int)) := fun a b hab => by
    have e1 := PBij.point_ms_eq ht
    have e2 := PBij.point_ms_eq hab.2
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    omega
  unfold watchStep
  refine ⟨forall2_any (fun a b hab => hlate a b hab) htrs, forall2_append
    (forall2_filter (fun a b hab => by
      obtain ⟨e1, t1⟩ := a; obtain ⟨e2, t2⟩ := b
      simp only
      rw [hlate (e1, t1) (e2, t2) hab, hans _ _ hab.1]) htrs)
    (forall2_map2 (fun a b hab => ⟨hab, ht⟩) (forall2_filter (fun a b hab => by rw [hop _ _ hab, hans _ _ hab]) hev))⟩

theorem zipIdx_filter_eq {α β : Type} {r : (Bool × α) → (Bool × β) → Prop} (h1 : ∀ p q, r p q → p.1 = q.1) :
    {l : List (Bool × α)} → {l' : List (Bool × β)} → (k : Nat) → Forall2 r l l' →
    ((l.zipIdx k).filter (·.1.1)).map (·.2) = ((l'.zipIdx k).filter (·.1.1)).map (·.2)
  | [], [], _, _ => rfl
  | p :: l, q :: l', k, ⟨hpq, h⟩ => by
    simp only [List.zipIdx_cons, List.filter_cons, h1 p q hpq]
    split <;> simp only [List.map_cons, zipIdx_filter_eq h1 (k + 1) h]
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

theorem watchNext_rel (ho : Ordered T v) {a b : Node v} (h : NodeRen R a b) {x x' : Input v}
    (hx : Input.Ren R x x') {r r' : Result v} (hr : ResultRen R r r') :
    (watchNext a x r).1 = (watchNext b x' r').1 ∧ WatchRel R.ctr (watchNext a x r).2 (watchNext b x' r').2 := by
  have htime := timelyAt_rel h.state hx ho.equi.machines
  have hw := h.watch
  unfold watchNext
  revert hw
  cases a.watch <;> cases b.watch <;> intro hw <;> cases hw
  · exact ⟨rfl, .none⟩
  · rename_i ws ws' hws
    rw [htime]
    by_cases hc : timelyAt b.state x' = true
    · simp only [hc, ↓reduceIte]
      have hsteps : Forall2 (fun p q => p.1 = q.1 ∧ Forall2 (TrigRel R.ctr) p.2 q.2)
          ((v.responses.zip ws).map fun (resp, trs) => watchStep resp r.moment trs)
          ((v.responses.zip ws').map fun (resp, trs) => watchStep resp r'.moment trs) :=
        forall2_map_mem (fun p hp q hpq => by
          obtain ⟨resp, trs⟩ := p; obtain ⟨resp', trs'⟩ := q
          obtain ⟨hr1, hr2⟩ := hpq
          simp only at hr1 hr2 ⊢
          subst hr1
          exact watchStep_rel ho (List.of_mem_zip hp).1 hr.1.2.2.2.1 hr.2.2.1 hr2)
          (forall2_zip_same v.responses hws)
      exact ⟨zipIdx_filter_eq (fun _ _ h => h.1) 0 hsteps, .some (forall2_map2 (fun _ _ h => h.2) hsteps)⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨trivial, .none⟩

theorem shownIds_rel {r r' : Result v} (hr : ResultRen R r r') :
    Multi (IdV.Rel R.ctr) (r.shownIds T) (r'.shownIds T) := by
  obtain ⟨-, ho, hev, hout⟩ := hr
  unfold Result.shownIds
  refine Multi.append (Multi.append ?_ (Multi.flatMap (fun _ _ h => idsOf_rel T h) (Multi.of_forall2 hev)))
    (Multi.flatMap (fun o o' h => ?_) (Multi.of_forall2 hout))
  · revert ho
    cases r.outcome <;> cases r'.outcome <;> intro ho <;> cases ho <;> first | exact Multi.nil | skip
    all_goals (rename_i hw; exact idsOf_rel T hw)
  · obtain ⟨-, -, -, hw⟩ := h
    revert hw
    generalize o.input = w
    generalize o'.input = w'
    intro hw
    cases hw with | mk h => exact idsOf_rel T h

theorem shownNext_rel (hmo : R.ctr.Mono) {a b : Node v} (h : NodeRen R a b) {r r' : Result v}
    (hr : ResultRen R r r') : Forall2 (IdV.Rel R.ctr) (shownNext T a r) (shownNext T b r') :=
  sortIds_rel hmo (Multi.filter (fun _ _ hxy => contains_rel (stateIds_rel hr.1) hxy)
    ((Multi.of_forall2 h.shown).append (Multi.filter (fun x y hxy => by
      rcases hxy with ⟨s, rfl, rfl⟩ | ⟨c, c', i, -, rfl, rfl⟩ <;> rfl) (shownIds_rel hr))))

/-- Related nodes on related inputs show the same classes, the same fault and the same broken responses, and reach
related nodes. -/
theorem move_rel (ho : Ordered T v) (hmo : R.ctr.Mono) {a b : Node v} (h : NodeRen R a b) {x x' : Input v}
    (hx : Input.Ren R x x') :
    classes T v x (move T a x).result = classes T v x' (move T b x').result ∧
      (∀ f, (move T a x).result.outcome = .fault f ↔ (move T b x').result.outcome = .fault f) ∧
      (move T a x).broken = (move T b x').broken ∧ Option.Rel (NodeRen R) (move T a x).next (move T b x').next := by
  have hr := step_ren ho hmo h.state hx
  have hw := watchNext_rel ho h hx hr
  have hro := hr.2.1
  refine ⟨classes_rel hx hr, fun f => ?_, hw.1, ?_⟩
  · show (step T v a.state x).outcome = .fault f ↔ (step T v b.state x').outcome = .fault f
    revert hro
    cases (step T v a.state x).outcome <;> cases (step T v b.state x').outcome <;> intro hro <;> cases hro <;>
      simp
  · unfold move
    simp only
    revert hro hr hw
    generalize step T v a.state x = ra
    generalize step T v b.state x' = rb
    intro hr hw hro
    obtain ⟨st, oc, evs, out⟩ := ra
    obtain ⟨st', oc', evs', out'⟩ := rb
    dsimp only at hro ⊢
    cases oc <;> cases oc' <;>
      first | exact .none | exact .some ⟨hr.1, shownNext_rel hmo h hr, hw.2⟩ | (simp [Outcome.Ren] at hro)

theorem option_rel_mono {α β : Type} {r s : α → β → Prop} (h : ∀ a b, r a b → s a b) :
    {x : Option α} → {y : Option β} → Option.Rel r x y → Option.Rel s x y
  | _, _, .none => .none
  | _, _, .some hab => .some (h _ _ hab)

/-- From linked nodes, each input explore tries from the first has one it tries from the second whose transition shows
the same classes, fault and broken responses and reaches a linked node. -/
theorem link_move {P : List AnySite} {E : List AnyEffectSite} (chk : Smt.Checked P E T v) (ho : Ordered T v)
    (sc : ScopeV) {a b : Node v} (hl : Link a b) (ha : Inv P a.state) {x : Input v} (hx : x ∈ inputsOf sc a) :
    ∃ x' ∈ inputsOf sc b, classes T v x (move T a x).result = classes T v x' (move T b x').result ∧
      (∀ f, (move T a x).result.outcome = .fault f ↔ (move T b x').result.outcome = .fault f) ∧
      (move T a x).broken = (move T b x').broken ∧ Option.Rel Link (move T a x).next (move T b x').next := by
  obtain ⟨R, hmo, h⟩ := hl
  obtain ⟨x', hx', hxx⟩ := forall2_mem_left (inputsOf_rel chk ho hmo sc ha h) x hx
  obtain ⟨h1, h2, h3, h4⟩ := move_rel ho hmo h hxx
  exact ⟨x', hx', h1, h2, h3, option_rel_mono (fun _ _ hn => ⟨R, hmo, hn⟩) h4⟩

end Moves

end Tazuna.Explore
