import Tazuna.Semantics.Equivariance
import Tazuna.Semantics.Start
import Tazuna.Semantics.Diamond

/-! The step respects renaming. A state relates to another under a renaming `R` when its records, instances, pending
requests, applied events, out lines and waiting own effects relate under `R`, each collection as a multiset and wire
ids through `R.wire`. Running related effects from related states gives related states, under `R` with wire ids
extended to the requests the effects send, or a fault on both sides (`runOwn_rel`). This is what `Diamond.Simulates`
asks of the own cascade and of a clock line's timers (`Tazuna.Semantics.Interleave`). -/

namespace Tazuna.Ir

variable {R : PBij}

section Lists
variable {α β γ δ : Type}

theorem perm_map_multi {g : α → β} : {xs ys : List α} → (xs.map g).Perm (ys.map g) →
    Multi (fun a b => g a = g b) xs ys
  | [], ys, h => by
    have : ys = [] := by simpa using h.symm.eq_nil
    subst this; exact Multi.nil
  | x :: xs, ys, h => by
    have hm : g x ∈ ys.map g := h.mem_iff.1 List.mem_cons_self
    obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hm
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hy
    have h' : (xs.map g).Perm ((l1 ++ l2).map g) := by
      have h2 : (l1 ++ y :: l2).map g = l1.map g ++ g y :: l2.map g := by simp
      have := h.trans (h2 ▸ List.perm_middle (a := g y) (l₁ := l1.map g) (l₂ := l2.map g))
      rw [hyx, ← List.map_append] at this
      exact (List.perm_cons _).1 this
    obtain ⟨zs, hz, hp⟩ := perm_map_multi h'
    exact ⟨y :: zs, ⟨hyx.symm, hz⟩, (hp.cons y).trans List.perm_middle.symm⟩

theorem forall2_comp {r1 : α → β → Prop} {r2 : β → γ → Prop} :
    {xs : List α} → {ys : List β} → {zs : List γ} → Forall2 r1 xs ys → Forall2 r2 ys zs →
    Forall2 (fun a c => ∃ b, r1 a b ∧ r2 b c) xs zs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h⟩, ⟨h1', h'⟩ => ⟨⟨_, h1, h1'⟩, forall2_comp h h'⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ | _, [], _ :: _, _, h | _, _ :: _, [], _, h => h.elim

theorem Multi.comp {r1 : α → β → Prop} {r2 : β → γ → Prop} {xs : List α} {ys : List β} {zs : List γ} :
    Multi r1 xs ys → Multi r2 ys zs → Multi (fun a c => ∃ b, r1 a b ∧ r2 b c) xs zs
  | ⟨_, h1, hw⟩, ⟨_, h2, hu⟩ =>
    let ⟨us', hu', h2'⟩ := forall2_perm_left hw.symm h2
    ⟨us', forall2_comp h1 h2', hu'.symm.trans hu⟩

open Classical in
theorem dedupBy_map {f : α → α → Bool} {g : α → β} (hfg : ∀ a b, f a b = true ↔ g a = g b) (xs : List α) :
    (dedupBy f xs).map g = dedupBy (fun a b => decide (a = b)) (xs.map g) := by
  unfold dedupBy
  suffices ∀ acc : List α, (xs.foldl (fun ks k => if ks.any (f k) then ks else ks ++ [k]) acc).map g =
      (xs.map g).foldl (fun ks k => if ks.any (fun b => decide (k = b)) then ks else ks ++ [k]) (acc.map g) from
    this []
  induction xs with
  | nil => intro; rfl
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons]
    have e : (acc.map g).any (fun b => decide (g x = b)) = acc.any (f x) := by
      simp only [List.any_map, Function.comp_def]
      congr 1; funext a
      rw [Bool.eq_iff_iff, decide_eq_true_eq, hfg]
    rw [e]
    split
    · exact ih acc
    · rw [ih (acc ++ [x])]; simp

open Classical in
/-- Deduplicating reordered lists under an equivalence keeps one of each class on both sides. -/
theorem dedupBy_perm_multi {f : α → α → Bool} {g : α → β} (hfg : ∀ a b, f a b = true ↔ g a = g b) {xs ys : List α}
    (h : xs.Perm ys) : Multi (fun a b => f a b = true) (dedupBy f xs) (dedupBy f ys) := by
  have hp : ((dedupBy f xs).map g).Perm ((dedupBy f ys).map g) := by
    rw [dedupBy_map hfg, dedupBy_map hfg]
    exact dedupBy_perm (fun a b => decide_eq_true_iff) (h.map g)
  exact (perm_map_multi hp).imp fun a b e => (hfg a b).2 e

theorem forall2_dedupBy {r : α → β → Prop} {f : α → α → Bool} {f' : β → β → Bool}
    (hff : ∀ a b a' b', r a b → r a' b' → f a a' = f' b b') {xs : List α} {ys : List β} (h : Forall2 r xs ys) :
    Forall2 r (dedupBy f xs) (dedupBy f' ys) := by
  unfold dedupBy
  suffices ∀ {acc : List α} {acc' : List β}, Forall2 r acc acc' →
      Forall2 r (xs.foldl (fun ks k => if ks.any (f k) then ks else ks ++ [k]) acc)
        (ys.foldl (fun ks k => if ks.any (f' k) then ks else ks ++ [k]) acc') from this (acc := []) (acc' := []) trivial
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact fun h => h
    | cons => exact h.elim
  | cons x xs ih =>
    cases ys with
    | nil => exact h.elim
    | cons y ys =>
      intro acc acc' hacc
      simp only [List.foldl_cons]
      rw [forall2_any (fun a b hab => hff _ _ _ _ h.1 hab) hacc]
      split
      · exact ih h.2 hacc
      · exact ih h.2 (forall2_append hacc ⟨h.1, trivial⟩)

theorem listBeq_true {α : Type} {f : α → α → Bool} : {xs ys : List α} → listBeq f xs ys = true →
    Forall2 (fun a b => f a b = true) xs ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => by
    simp only [listBeq, Bool.and_eq_true] at h
    exact ⟨h.1, listBeq_true h.2⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [listBeq] at h

mutual
/-- On a comparable type, a value `==` to one related to `y` is itself related to `y`. -/
theorem Ty.rel0_deq_left : (t : Ty) → t.comparable = true → {x x1 y : t.den0} → t.deq0 x x1 = true →
    Ty.rel0 R t x1 y → Ty.rel0 R t x y
  | .int, _, _, _, _, e, h | .str, _, _, _, _, e, h | .date, _, _, _, _, e, h => by
    have e := beq_iff_eq.1 e
    exact e ▸ h
  | .id, _, x, x1, y, e, h => by
    revert x x1 y
    show ∀ x x1 y : IdV, decide (x = x1) = true → IdV.Rel R x1 y → IdV.Rel R x y
    intro x x1 y e h
    exact (of_decide_eq_true e) ▸ h
  | .param _, _, _, _, _, _, _ => trivial
  | .list t, hc, x, x1, y, e, h =>
    forall2_imp (fun _ _ ⟨_, hab, hbc⟩ => Ty.rel0_deq_left t hc hab hbc) (forall2_comp (listBeq_true e) h)
  | .bag t, hc, x, x1, y, e, h => by
    have hp := (bagBeq_iff (Ty.canon_iff t hc) x x1).1 e
    exact ((perm_map_multi hp).comp h).imp fun _ _ ⟨_, hab, hbc⟩ =>
      Ty.rel0_deq_left t hc ((Ty.canon_iff t hc _ _).2 hab) hbc
  | .table k v, hc, x, x1, y, e, h => by
    simp only [Ty.comparable, Bool.and_eq_true] at hc
    have hp := (tableBeq_iff (Ty.canon_iff k hc.1) (Ty.canon_iff v hc.2) x.2 x1.2).1 e
    exact ((perm_map_multi hp).comp h).imp fun _ _ ⟨_, hab, hbc⟩ => by
      simp only [Prod.mk.injEq] at hab
      exact ⟨Ty.rel0_deq_left k hc.1 ((Ty.canon_iff k hc.1 _ _).2 hab.1) hbc.1,
        Ty.rel0_deq_left v hc.2 ((Ty.canon_iff v hc.2 _ _).2 hab.2) hbc.2⟩
  | .tuple ts, hc, _, _, _, e, h => Ty.rels0_deq_left ts hc e h
  | .adt _ _ vs, hc, _, _, _, e, h => Ty.relAlts0_deq_left vs hc e h
  | .dsl k _, hc, x, x1, y, e, h => by
    cases k <;> simp [Ty.comparable] at hc
    revert x x1 y
    show ∀ x x1 y : Nat, (x == x1) = true → R.rel x1 y → R.rel x y
    intro x x1 y e h
    exact (beq_iff_eq.1 e) ▸ h
  | .fn .., hc, _, _, _, _, _ => by simp [Ty.comparable] at hc
theorem Ty.rels0_deq_left : (ts : List Ty) → Ty.comparables ts = true → {x x1 y : (Ty.semsWith Dsl.base ts).1} →
    (Ty.semsWith Dsl.base ts).2 x x1 = true → Ty.relsWith Dsl.base (Dsl.rel0 R) R ts x1 y →
    Ty.relsWith Dsl.base (Dsl.rel0 R) R ts x y
  | [], _, _, _, _, _, _ => trivial
  | t :: ts, hc, _, _, _, e, ⟨h1, h⟩ => by
    simp only [Ty.comparables, Bool.and_eq_true] at hc
    have e : (Ty.deq0 t _ _ && _) = true := e
    rw [Bool.and_eq_true] at e
    exact ⟨Ty.rel0_deq_left t hc.1 e.1 h1, Ty.rels0_deq_left ts hc.2 e.2 h⟩
theorem Ty.relAlts0_deq_left : (vs : List (List Ty)) → Ty.comparabless vs = true →
    {x x1 y : (Ty.semAltsWith Dsl.base vs).1} → (Ty.semAltsWith Dsl.base vs).2 x x1 = true →
    Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs x1 y → Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs x y
  | [], _, x, _, _, _, _ => nomatch x
  | fs :: _, hc, .inl _, .inl _, .inl _, e, h => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    exact Ty.rels0_deq_left fs hc.1 e h
  | _ :: vs, hc, .inr _, .inr _, .inr _, e, h => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    exact Ty.relAlts0_deq_left vs hc.2 e h
  | _ :: _, _, .inl _, .inr _, _, e, _ | _ :: _, _, .inr _, .inl _, _, e, _ => by
    simp [Ty.semAltsWith, Sem.sum] at e
  | _ :: _, _, .inl _, .inl _, .inr _, _, h | _ :: _, _, .inr _, .inr _, .inl _, _, h => h.elim
end

theorem Multi.cons_inv {r : α → β → Prop} {x : α} {xs : List α} {ys : List β} (h : Multi r (x :: xs) ys) :
    ∃ l1 y l2, ys = l1 ++ y :: l2 ∧ r x y ∧ Multi r xs (l1 ++ l2) := by
  obtain ⟨zs, hf, hz⟩ := h
  match zs, hf with
  | y :: zs', ⟨hxy, hf⟩ =>
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem (hz.mem_iff.1 List.mem_cons_self)
    exact ⟨l1, y, l2, rfl, hxy, zs', hf, (List.perm_cons y).1 (hz.trans List.perm_middle)⟩

theorem Multi.imp_mem {r r' : α → β → Prop} {xs : List α} {ys : List β}
    (hr : ∀ a ∈ xs, ∀ b ∈ ys, r a b → r' a b) : Multi r xs ys → Multi r' xs ys
  | ⟨zs, h, hz⟩ => ⟨zs, go h (fun a ha b hb => hr a ha b (hz.mem_iff.1 hb)), hz⟩
where
  go : {xs : List α} → {zs : List β} → Forall2 r xs zs → (∀ a ∈ xs, ∀ b ∈ zs, r a b → r' a b) → Forall2 r' xs zs
    | [], [], _, _ => trivial
    | _ :: _, _ :: _, ⟨h1, h⟩, hr => ⟨hr _ List.mem_cons_self _ List.mem_cons_self h1,
        go h fun a ha b hb => hr a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
    | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim

theorem Multi.filterMap {r : α → β → Prop} {r' : γ → δ → Prop} {f : α → Option γ} {g : β → Option δ}
    (hfg : ∀ a b, r a b → Option.Rel r' (f a) (g b)) {xs : List α} {ys : List β} :
    Multi r xs ys → Multi r' (xs.filterMap f) (ys.filterMap g)
  | ⟨zs, h, hz⟩ => ⟨zs.filterMap g, go h, hz.filterMap g⟩
where
  go : {xs : List α} → {zs : List β} → Forall2 r xs zs → Forall2 r' (xs.filterMap f) (zs.filterMap g)
    | [], [], _ => trivial
    | a :: _, b :: _, ⟨h1, h⟩ => by
      simp only [List.filterMap_cons]
      have := hfg a b h1
      revert this
      cases f a <;> cases g b <;> intro hr <;> cases hr
      · exact go h
      · exact ⟨by assumption, go h⟩
    | [], _ :: _, h | _ :: _, [], h => h.elim

theorem zipIdx_shift (l : List α) (k : Nat) : (l.zipIdx k).map (fun q => (q.1, q.2 + 1)) = l.zipIdx (k + 1) := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih => simp [List.zipIdx_cons, ih]

/-- Numbering lists related as multisets from any two bases relates the numbers by a partial bijection: the
renaming of wire ids that requests started in a different order need. -/
theorem Multi.zipIdx {r : α → β → Prop} : {xs : List α} → {ys : List β} → Multi r xs ys → (N N' : Nat) →
    ∃ τ : PBij, (∀ {i j}, τ.rel i j → N ≤ i ∧ N' ≤ j) ∧
      Multi (fun p q => r p.1 q.1 ∧ τ.rel p.2 q.2) (xs.zipIdx N) (ys.zipIdx N')
  | [], ys, h, _, _ => by
    have : ys = [] := List.eq_nil_of_length_eq_zero h.length_eq.symm
    subst this
    exact ⟨⟨fun _ _ => False, False.elim, False.elim⟩, False.elim, Multi.nil⟩
  | x :: xs, _, h, N, N' => by
    obtain ⟨l1, y, l2, rfl, hxy, hm⟩ := h.cons_inv
    obtain ⟨τ', hb', hm'⟩ := Multi.zipIdx hm (N + 1) N'
    let c := N' + l1.length
    let sh : Nat → Nat := fun j => if j < c then j else j + 1
    have sh_inj : ∀ {a b}, sh a = sh b → a = b := by intro a b; simp only [sh]; split <;> split <;> omega
    have sh_ne : ∀ j, sh j ≠ c := by intro j; simp only [sh]; split <;> omega
    refine ⟨⟨fun i j => (i = N ∧ j = c) ∨ ∃ j0, τ'.rel i j0 ∧ j = sh j0, ?_, ?_⟩, ?_, ?_⟩
    · rintro i j j' (⟨rfl, rfl⟩ | ⟨j0, h0, rfl⟩) (⟨_, rfl⟩ | ⟨j1, h1, rfl⟩)
      · rfl
      · exact absurd (hb' h1).1 (by omega)
      · exact absurd (hb' h0).1 (by omega)
      · rw [τ'.func h0 h1]
    · rintro i i' j (⟨rfl, rfl⟩ | ⟨j0, h0, rfl⟩) (⟨rfl, e⟩ | ⟨j1, h1, e⟩)
      · rfl
      · exact absurd e.symm (sh_ne j1)
      · exact absurd e (sh_ne j0)
      · exact τ'.inj h0 (sh_inj e ▸ h1)
    · rintro i j (⟨rfl, rfl⟩ | ⟨j0, h0, rfl⟩)
      · exact ⟨Nat.le_refl _, by omega⟩
      · have := hb' h0
        exact ⟨by omega, by simp only [sh]; split <;> omega⟩
    · have e1 : (l1 ++ y :: l2).zipIdx N' = l1.zipIdx N' ++ (y, c) :: l2.zipIdx (c + 1) := by
        simp [List.zipIdx_append, List.zipIdx_cons, c]
      have e2 : ((l1 ++ l2).zipIdx N').map (fun q => (q.1, sh q.2)) = l1.zipIdx N' ++ l2.zipIdx (c + 1) := by
        rw [List.zipIdx_append, List.map_append, ← zipIdx_shift]
        congr 1
        · conv => rhs; rw [← List.map_id (l1.zipIdx N')]
          refine List.map_congr_left fun q hq => ?_
          have := List.mem_zipIdx hq
          simp only [sh, id]
          split
          · rfl
          · omega
        · refine List.map_congr_left fun q hq => ?_
          have := List.mem_zipIdx hq
          simp only [sh]
          split
          · omega
          · rfl
      rw [List.zipIdx_cons, e1]
      refine (Multi.cons (b := (y, c)) ⟨hxy, .inl ⟨rfl, rfl⟩⟩ ?_).perm_right List.perm_middle.symm
      rw [← e2]
      have := hm'.map (f := id) (g := fun q => (q.1, sh q.2))
        (r' := fun p q => r p.1 q.1 ∧ ((p.2 = N ∧ q.2 = c) ∨ ∃ j0, τ'.rel p.2 j0 ∧ q.2 = sh j0))
        (fun p q h => ⟨h.1, .inr ⟨q.2, h.2, rfl⟩⟩)
      rwa [List.map_id] at this

end Lists

theorem Multi.mem_left {α β : Type} {r : α → β → Prop} {xs : List α} {ys : List β} (h : Multi r xs ys) {x : α}
    (hx : x ∈ xs) : ∃ y ∈ ys, r x y := by
  obtain ⟨zs, hf, hz⟩ := h
  obtain ⟨y, hy, hxy⟩ := forall2_mem_left hf x hx
  exact ⟨y, hz.mem_iff.1 hy, hxy⟩

theorem Multi.transport {α β γ δ : Type} {r : α → β → Prop} {W : α → γ → Prop} {W' : β → δ → Prop} {s : γ → δ → Prop}
    (hs : ∀ x y p q, r x y → W x p → W' y q → s p q) {xs : List α} {ys : List β} {ps : List γ} {qs : List δ}
    (h : Multi r xs ys) (hp : Forall2 W xs ps) (hq : Forall2 W' ys qs) : Multi s ps qs :=
  (((Multi.of_forall2 (forall2_flip hp)).comp h).comp (Multi.of_forall2 hq)).imp
    fun _ _ ⟨_, ⟨_, hp, hr⟩, hq⟩ => hs _ _ _ _ hr hp hq

/-- `R` with the wire ids below `N` and `N'` renamed as `R` renames them, and the ones from `N` and `N'` on as `τ`
does: the renaming after a step sends requests from the next ids `N` and `N'`. -/
def Ren.withWire (R : Ren) (N N' : Nat) (τ : PBij) (hτ : ∀ {i j}, τ.rel i j → N ≤ i ∧ N' ≤ j) : Ren where
  ctr := R.ctr
  wire := {
    rel := fun a b => (a < N ∧ b < N' ∧ R.wire.rel a b) ∨ τ.rel a b
    func := by
      rintro a b b' (⟨ha, _, h⟩ | h) (⟨_, _, h'⟩ | h')
      · exact R.wire.func h h'
      · exact absurd (hτ h').1 (by omega)
      · exact absurd (hτ h).1 (by omega)
      · exact τ.func h h'
    inj := by
      rintro a a' b (⟨_, hb, h⟩ | h) (⟨_, _, h'⟩ | h')
      · exact R.wire.inj h h'
      · exact absurd (hτ h').2 (by omega)
      · exact absurd (hτ h).2 (by omega)
      · exact τ.inj h h' }

namespace Step

section Rel
variable {r e : Ty}

/-- Instances related by `R`: their keys, states and timers. -/
def Instance.Rel (R : PBij) {m : MachineV r e} (i j : Instance m) : Prop :=
  Ty.rel0 R m.key i.key j.key ∧ Ty.rel0 R m.state i.state j.state ∧
    Option.Rel (fun a b => a.1 = b.1 ∧ Ty.rel0 R m.state a.2 b.2) i.timer j.timer

/-- No key twice among a machine's instances. -/
def KeysDistinct {m : MachineV r e} (l : List (Instance m)) : Prop :=
  l.Pairwise fun a b => m.key.deq0 a.key b.key = false

/-- A machine's instances related by `R`, as multisets: the canonical key order changes when keys are renamed. -/
def Insts.Rel (R : PBij) {m : MachineV r e} (l l' : List (Instance m)) : Prop :=
  Multi (Instance.Rel R) l l' ∧ KeysDistinct l ∧ KeysDistinct l'

def Machines.Rel (R : PBij) : {ms : List (MachineV r e)} → Machines ms → Machines ms → Prop
  | _, .nil, .nil => True
  | _, .cons l rest, .cons l' rest' => Insts.Rel R l l' ∧ Machines.Rel R rest rest'

/-- Started effects related by `R`, with their senders. -/
def Started.Rel (R : PBij) (x y : Sender × EffectV e) : Prop := Sender.Rel R x.1 y.1 ∧ EffectV.Rel R x.2 y.2

def Pending.Rel (R : Ren) (p q : Pending e) : Prop :=
  R.wire.rel p.id q.id ∧ Sender.Rel R.ctr p.sender q.sender ∧ p.external = q.external ∧
    RequestV.Rel R.ctr p.request q.request

end Rel

def OutLine.Rel (R : Ren) (o o' : OutLine) : Prop :=
  R.wire.rel o.id o'.id ∧ o.external = o'.external ∧ o.name = o'.name ∧ WireVal.Rel R.ctr o.input o'.input

variable {v : ServiceV}

/-- States related by `R`. Pending requests carry wire ids below the next one on each side, so a renaming extended to
the ids a step sends next agrees with `R` on them. -/
def StateRel (R : Ren) (s s' : State v) : Prop :=
  Ty.rel0 R.ctr v.records s.records s'.records ∧ Machines.Rel R.ctr s.machines s'.machines ∧
    Multi (Pending.Rel R) s.pending s'.pending ∧ s.now = s'.now ∧
    (∀ p ∈ s.pending, p.id < s.nextId) ∧ (∀ p ∈ s'.pending, p.id < s'.nextId)

/-- Steps in progress related by `R`: their states, and the applied events, out lines and waiting own effects as
multisets. -/
def Acc.Rel (R : Ren) (a a' : Acc v) : Prop :=
  StateRel R a.state a'.state ∧ Multi (Ty.rel0 R.ctr v.event) a.events a'.events ∧ Multi (OutLine.Rel R) a.out a'.out ∧
    (∀ o ∈ a.out, o.id < a.state.nextId) ∧ (∀ o ∈ a'.out, o.id < a'.state.nextId) ∧
    Multi (EffectV.Rel R.ctr) a.own a'.own

/-- What related runs from `a` and `a'` end in: a fault on both sides, or states related under a renaming that renames
counters as `R` does, having used as many counters and as many wire ids on each side. -/
def Lifted (R : Ren) (a a' : Acc v) (x x' : Except Fault (Acc v)) : Prop :=
  (Diamond.Faults x ∧ Diamond.Faults x') ∨ ∃ b b' R', x = .ok b ∧ x' = .ok b' ∧ R'.ctr = R.ctr ∧ Acc.Rel R' b b' ∧
    b.state.fresh + a'.state.fresh = b'.state.fresh + a.state.fresh ∧
    b.state.nextId + a'.state.nextId = b'.state.nextId + a.state.nextId

theorem Lifted.bind {R : Ren} {a a' : Acc v} {x x' : Except Fault (Acc v)} (h : Lifted R a a' x x')
    {f g : Acc v → Except Fault (Acc v)}
    (hfg : ∀ R' b b', R'.ctr = R.ctr → Acc.Rel R' b b' → Lifted R' b b' (f b) (g b')) :
    Lifted R a a' (x >>= f) (x' >>= g) := by
  rcases h with ⟨hx, hx'⟩ | ⟨b, b', R', rfl, rfl, hc, hr, hf, hn⟩
  · left
    cases x <;> cases x' <;> first | exact ⟨trivial, trivial⟩ | exact absurd hx id | exact absurd hx' id
  · rcases hfg R' b b' hc hr with ⟨h1, h2⟩ | ⟨c, c', R'', h1, h2, hc', hr', hf', hn'⟩
    · exact .inl ⟨h1, h2⟩
    · exact .inr ⟨c, c', R'', h1, h2, hc'.trans hc, hr', by omega, by omega⟩

theorem RequestV.ownerIn_rel {R : PBij} {e : Ty} {r r' : RequestV e} (h : RequestV.Rel R r r') (ds : List (String × DeclaredV)) :
    r.ownerIn ds = r'.ownerIn ds := by
  cases h; rfl

/-- An effect that is a request no external lists. -/
def Undeclared (ds : List (String × DeclaredV)) {e : Ty} (x : Sender × EffectV e) : Prop :=
  ∃ r, x.2 = .request r ∧ r.ownerIn ds = none

theorem start_undeclared (effs : List (Sender × EffectV v.event)) (h : ∃ x ∈ effs, Undeclared v.declared x) :
    ∀ a : Acc v, Diamond.Faults (start a effs) := by
  induction effs with
  | nil => obtain ⟨_, hx, _⟩ := h; nomatch hx
  | cons x rest ih =>
    intro a
    obtain ⟨snd, eff⟩ := x
    unfold start
    rw [List.foldlM_cons]
    by_cases hu : Undeclared v.declared (snd, eff)
    · obtain ⟨r, hr, hu⟩ := hu
      simp only at hr
      subst hr
      simp only [hu, bind, Except.bind]
      trivial
    · have h' : ∃ x ∈ rest, Undeclared v.declared x := by
        obtain ⟨x, hx, hux⟩ := h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd hux hu
        · exact ⟨x, hx, hux⟩
      cases eff with
      | request r' =>
        dsimp only
        split
        · trivial
        · exact ih h' _
      | command => exact ih h' _
      | query => exact ih h' _

theorem writes_of_declared (ds : List (String × DeclaredV)) {e : Ty} : (l : List (Sender × EffectV e)) → (N : Nat) →
    (∀ x ∈ l, x.2.isRequest = true ∧ ¬ Undeclared ds x) → ∃ ps, Forall2 (Writes ds) (l.zipIdx N) ps
  | [], _, _ => ⟨[], trivial⟩
  | (snd, eff) :: l, N, h => by
    obtain ⟨ps, hps⟩ := writes_of_declared ds l (N + 1) fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ⟨hreq, hd⟩ := h _ List.mem_cons_self
    cases eff with
    | request r =>
      cases ho : r.ownerIn ds with
      | none => exact absurd ⟨r, rfl, ho⟩ hd
      | some o => exact ⟨⟨N, snd, o, r⟩ :: ps, ⟨⟨r, o, rfl, ho, rfl⟩, hps⟩⟩
    | command | query => simp [EffectV.isRequest] at hreq

theorem Started.rel_isRequest {R : PBij} {e : Ty} {x y : Sender × EffectV e} (h : Started.Rel R x y) :
    x.2.isRequest = y.2.isRequest := by
  obtain ⟨_, ex⟩ := x
  obtain ⟨_, ey⟩ := y
  rcases h with ⟨_, h⟩
  cases h <;> rfl

theorem Started.rel_undeclared {R : PBij} {e : Ty} {ds : List (String × DeclaredV)} {x y : Sender × EffectV e}
    (h : Started.Rel R x y) : Undeclared ds x ↔ Undeclared ds y := by
  obtain ⟨_, ex⟩ := x
  obtain ⟨_, ey⟩ := y
  obtain ⟨_, h⟩ := h
  cases h with
  | request hrr =>
    constructor
    · rintro ⟨r, hr, hu⟩
      cases hr
      exact ⟨_, rfl, (RequestV.ownerIn_rel hrr ds) ▸ hu⟩
    · rintro ⟨r, hr, hu⟩
      cases hr
      exact ⟨_, rfl, (RequestV.ownerIn_rel hrr ds).symm ▸ hu⟩
  | command => constructor <;> rintro ⟨_, hr, _⟩ <;> cases hr
  | query => constructor <;> rintro ⟨_, hr, _⟩ <;> cases hr

theorem Pending.rel_line {R : Ren} {e : Ty} {p q : Pending e} (h : Pending.Rel R p q) : OutLine.Rel R p.line q.line := by
  obtain ⟨_, _, _, ⟨_, _, _, _, _, _, _⟩⟩ := p
  obtain ⟨_, _, _, ⟨_, _, _, _, _, _, _⟩⟩ := q
  obtain ⟨hid, _, hx, hr⟩ := h
  cases hr with
  | mk _ _ _ _ hv _ _ => exact ⟨hid, hx, rfl, .mk hv⟩

/-- Starting related effects from related steps either faults on both sides or writes related requests, under the
renaming extended to the wire ids each side sends. -/
theorem start_rel {R : Ren} {a a' : Acc v} (ha : Acc.Rel R a a') {effs effs' : List (Sender × EffectV v.event)}
    (he : Multi (Started.Rel R.ctr) effs effs') : Lifted R a a' (start a effs) (start a' effs') := by
  have hr := he.filter (p := (·.2.isRequest)) (q := (·.2.isRequest)) fun _ _ h => Started.rel_isRequest h
  by_cases hd : ∃ x ∈ reqsOf effs, Undeclared v.declared x
  · obtain ⟨x, hx, hu⟩ := hd
    obtain ⟨y, hy, hxy⟩ := hr.mem_left hx
    exact .inl ⟨start_undeclared effs ⟨x, (List.mem_filter.1 hx).1, hu⟩ a,
      start_undeclared effs' ⟨y, (List.mem_filter.1 hy).1, (Started.rel_undeclared hxy).1 hu⟩ a'⟩
  · have hd' : ¬ ∃ y ∈ reqsOf effs', Undeclared v.declared y := by
      rintro ⟨y, hy, hu⟩
      obtain ⟨x, hx, hxy⟩ := hr.flip.mem_left hy
      exact hd ⟨x, hx, (Started.rel_undeclared hxy).2 hu⟩
    have decl : ∀ {l : List (Sender × EffectV v.event)}, ¬ (∃ x ∈ reqsOf l, Undeclared v.declared x) →
        ∀ x ∈ reqsOf l, x.2.isRequest = true ∧ ¬ Undeclared v.declared x :=
      fun hn x hx => ⟨by simpa using (List.mem_filter.1 hx).2, fun hu => hn ⟨x, hx, hu⟩⟩
    obtain ⟨ps, hps⟩ := writes_of_declared v.declared (reqsOf effs) a.state.nextId (decl hd)
    obtain ⟨ps', hps'⟩ := writes_of_declared v.declared (reqsOf effs') a'.state.nextId (decl hd')
    rw [start_requests a effs ps hps, start_requests a' effs' ps' hps']
    obtain ⟨τ, hτ, hz⟩ := hr.zipIdx a.state.nextId a'.state.nextId
    let R' := R.withWire a.state.nextId a'.state.nextId τ hτ
    have hlen : (reqsOf effs).length = (reqsOf effs').length := hr.length_eq
    have hnew : Multi (Pending.Rel R') ps ps' := hz.transport (fun x y p q hxy hp hq => by
      obtain ⟨r, o, hxr, ho, rfl⟩ := hp
      obtain ⟨r', o', hyr, ho', rfl⟩ := hq
      obtain ⟨⟨snd, ex⟩, k⟩ := x
      obtain ⟨⟨snd', ey⟩, k'⟩ := y
      obtain ⟨⟨hs, he⟩, ht⟩ := hxy
      simp only at hxr hyr hs ht ⊢
      subst hxr hyr
      cases he with
      | request hrr =>
        refine ⟨.inr ht, hs, ?_, hrr⟩
        rw [RequestV.ownerIn_rel hrr] at ho
        exact Option.some.inj (ho.symm.trans ho')) hps hps'
    have hmem : ∀ {N : Nat} {l : List (Sender × EffectV v.event)} {qs : List (Pending v.event)},
        Forall2 (Writes v.declared) (l.zipIdx N) qs → ∀ p ∈ qs, N ≤ p.id ∧ p.id < N + l.length := by
      intro N l qs hw p hp
      obtain ⟨x, hx, r, o, _, _, rfl⟩ := forall2_mem_right hw p hp
      have := List.mem_zipIdx hx
      exact ⟨this.1, this.2.1⟩
    obtain ⟨⟨hrec, hmach, hpend, hnow, hb, hb'⟩, hev, hout, ho, ho', hown⟩ := ha
    have keep : ∀ {p q : Pending v.event}, p ∈ a.state.pending → q ∈ a'.state.pending → Pending.Rel R p q →
        Pending.Rel R' p q := fun hp hq ⟨hid, h2⟩ => ⟨.inl ⟨hb _ hp, hb' _ hq, hid⟩, h2⟩
    have keepO : ∀ {o o' : OutLine}, o ∈ a.out → o' ∈ a'.out → OutLine.Rel R o o' → OutLine.Rel R' o o' :=
      fun hp hq ⟨hid, h2⟩ => ⟨.inl ⟨ho _ hp, ho' _ hq, hid⟩, h2⟩
    refine .inr ⟨_, _, R', rfl, rfl, rfl, ⟨⟨hrec, hmach, ?_, hnow, ?_, ?_⟩, hev, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · exact (hpend.imp_mem fun _ hp _ hq h => keep hp hq h).append hnew
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact Nat.lt_of_lt_of_le (hb p hp) (Nat.le_add_right _ _)
      · exact (hmem hps p hp).2
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact Nat.lt_of_lt_of_le (hb' p hp) (Nat.le_add_right _ _)
      · exact (hmem hps' p hp).2
    · exact (hout.imp_mem fun _ hp _ hq h => keepO hp hq h).append
        (hnew.map fun _ _ h => Pending.rel_line h)
    · intro o hp
      rcases List.mem_append.1 hp with hp | hp
      · exact Nat.lt_of_lt_of_le (ho o hp) (Nat.le_add_right _ _)
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hp
        exact (hmem hps p hp').2
    · intro o hp
      rcases List.mem_append.1 hp with hp | hp
      · exact Nat.lt_of_lt_of_le (ho' o hp) (Nat.le_add_right _ _)
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hp
        exact (hmem hps' p hp').2
    · exact hown.append ((he.filter (p := (!·.2.isRequest)) (q := (!·.2.isRequest))
        fun _ _ h => by rw [Started.rel_isRequest h]).map fun _ _ h => h.2)
    · show a.state.fresh + a'.state.fresh = a'.state.fresh + a.state.fresh
      omega
    · show a.state.nextId + (reqsOf effs).length + a'.state.nextId = a'.state.nextId + (reqsOf effs').length + a.state.nextId
      omega

end Step

end Tazuna.Ir
