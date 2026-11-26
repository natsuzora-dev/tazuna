import Tazuna.Semantics.Equivariance
import Tazuna.Semantics.Start
import Tazuna.Semantics.Interleave

/-! The step respects renaming. A state relates to another under a renaming `R` when its records, instances, pending
requests, applied events, out lines and waiting own effects relate under `R`, each collection as a multiset and wire
ids through `R.wire`. Running related own effects from related states gives related states, under `R` with wire ids
extended to the requests the effects send, or a fault on both sides (`runOwn_rel`), so the own cascade respects the
equivalence the renamings generate (`ownSys_simulates`), which `Diamond.runs_agree` asks of it. -/

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

theorem eraseIdx_middle {α : Type} (y : α) (l2 : List α) : (l1 : List α) → (l1 ++ y :: l2).eraseIdx l1.length = l1 ++ l2
  | [] => rfl
  | x :: l1 => by simp [eraseIdx_middle y l2 l1]

theorem getElem_middle {α : Type} (y : α) (l2 : List α) : (l1 : List α) →
    (l1 ++ y :: l2)[l1.length]'(by simp) = y
  | [] => rfl
  | x :: l1 => by simp

/-- Taking an item out of one of two lists related as multisets, and its partner out of the other, leaves them
related. -/
theorem Multi.eraseIdx {α β : Type} {r : α → β → Prop} {xs : List α} {ys : List β} (h : Multi r xs ys) (i : Nat)
    (hi : i < xs.length) : ∃ j, ∃ hj : j < ys.length, r xs[i] ys[j] ∧ Multi r (xs.eraseIdx i) (ys.eraseIdx j) := by
  obtain ⟨l1, y, l2, rfl, hxy, hm⟩ := (h.perm_left (perm_eraseIdx xs i hi)).cons_inv
  exact ⟨l1.length, by simp, by rw [getElem_middle]; exact hxy, by rw [eraseIdx_middle]; exact hm⟩

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
    Multi (OwnEffectV.Rel R.ctr) a.own a'.own

/-- `W'` renames the wire ids below `N` and `N'` as `W` does. -/
def _root_.Tazuna.Ir.PBij.Extends (W W' : PBij) (N N' : Nat) : Prop := ∀ {i j}, i < N → j < N' → W.rel i j → W'.rel i j

/-- What related runs from `a` and `a'` end in: a fault on both sides, or states related under a renaming that renames
counters as `R` does and the wire ids that were in use as `R` does, having used as many counters and as many wire ids
on each side. -/
def Lifted (R : Ren) (a a' : Acc v) (x x' : Except Fault (Acc v)) : Prop :=
  (Diamond.Faults x ∧ Diamond.Faults x') ∨ ∃ b b' R', x = .ok b ∧ x' = .ok b' ∧ R'.ctr = R.ctr ∧ Acc.Rel R' b b' ∧
    a.state.fresh ≤ b.state.fresh ∧ b.state.fresh + a'.state.fresh = b'.state.fresh + a.state.fresh ∧
    b.state.nextId + a'.state.nextId = b'.state.nextId + a.state.nextId ∧ a.state.nextId ≤ b.state.nextId ∧
    R.wire.Extends R'.wire a.state.nextId a'.state.nextId

theorem Lifted.bind {R : Ren} {a a' : Acc v} {x x' : Except Fault (Acc v)} (h : Lifted R a a' x x')
    {f g : Acc v → Except Fault (Acc v)}
    (hfg : ∀ R' b b', R'.ctr = R.ctr → Acc.Rel R' b b' → Lifted R' b b' (f b) (g b')) :
    Lifted R a a' (x >>= f) (x' >>= g) := by
  rcases h with ⟨hx, hx'⟩ | ⟨b, b', R', rfl, rfl, hc, hr, hm, hf, hn, hl, hw⟩
  · left
    cases x <;> cases x' <;> first | exact ⟨trivial, trivial⟩ | exact absurd hx id | exact absurd hx' id
  · rcases hfg R' b b' hc hr with ⟨h1, h2⟩ | ⟨c, c', R'', h1, h2, hc', hr', hm', hf', hn', hl', hw'⟩
    · exact .inl ⟨h1, h2⟩
    · exact .inr ⟨c, c', R'', h1, h2, hc'.trans hc, hr', by omega, by omega, by omega, by omega,
        fun hi hj h => hw' (by omega) (by omega) (hw hi hj h)⟩

theorem Lifted.refl {R : Ren} {a a' : Acc v} (h : Acc.Rel R a a') : Lifted R a a' (.ok a) (.ok a') :=
  .inr ⟨a, a', R, rfl, rfl, rfl, h, Nat.le_refl _, by omega, by omega, Nat.le_refl _, fun _ _ h => h⟩

/-- A run from steps that differ from `a` and `a'` by having used `k` more counters each. -/
theorem Lifted.shift {R : Ren} {a a' a1 a1' : Acc v} {x x' : Except Fault (Acc v)} (h : Lifted R a1 a1' x x') (k : Nat)
    (hf : a1.state.fresh = a.state.fresh + k) (hf' : a1'.state.fresh = a'.state.fresh + k)
    (hn : a1.state.nextId = a.state.nextId) (hn' : a1'.state.nextId = a'.state.nextId) : Lifted R a a' x x' := by
  rcases h with h | ⟨b, b', R', h1, h2, hc, hr, hm, hf2, hn2, hl, hw⟩
  · exact .inl h
  · exact .inr ⟨b, b', R', h1, h2, hc, hr, by omega, by omega, by omega, by omega, by rw [← hn, ← hn']; exact hw⟩

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

theorem Started.rel_own {R : PBij} {e : Ty} {x y : Sender × EffectV e} (h : Started.Rel R x y) :
    Option.Rel (OwnEffectV.Rel R) x.2.own? y.2.own? := by
  obtain ⟨_, ex⟩ := x
  obtain ⟨_, ey⟩ := y
  rcases h with ⟨_, h⟩
  cases h with
  | request => exact .none
  | command => exact .some (.command _ _ _ _ ‹_› ‹_›)
  | query => exact .some (.query _ _ _ _ ‹_› ‹_›)

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
    refine .inr ⟨_, _, R', rfl, rfl, rfl, ⟨⟨hrec, hmach, ?_, hnow, ?_, ?_⟩, hev, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
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
    · exact hown.append (he.filterMap fun _ _ h => Started.rel_own h)
    · exact Nat.le_refl _
    · show a.state.fresh + a'.state.fresh = a'.state.fresh + a.state.fresh
      omega
    · show a.state.nextId + (reqsOf effs).length + a'.state.nextId = a'.state.nextId + (reqsOf effs').length + a.state.nextId
      omega
    · exact Nat.le_add_right _ _
    · exact fun hi hj h => .inl ⟨hi, hj, h⟩

end Step

theorem Ty.rel0_deq_right {t : Ty} (hc : t.comparable = true) {x y1 y : t.den0} (h : Ty.rel0 R t x y1)
    (e : t.deq0 y1 y = true) : Ty.rel0 R t x y :=
  Ty.rel0_inv.2 (Ty.rel0_deq_left t hc (Ty.deq0_symm hc e) (Ty.rel0_inv.1 h))

theorem Ty.deq0_refl {t : Ty} (hc : t.comparable = true) (x : t.den0) : t.deq0 x x = true :=
  (Ty.canon_iff t hc x x).2 rfl

mutual
/-- Every comparable value relates to itself with every name kept. -/
theorem Ty.rel0_refl : (t : Ty) → t.comparable = true → (x : t.den0) → Ty.rel0 PBij.refl t x x
  | .int, _, _ | .str, _, _ | .date, _, _ => rfl
  | .param _, _, _ => trivial
  | .id, _, .named _ => .inl ⟨_, rfl, rfl⟩
  | .id, _, .fresh _ _ => .inr ⟨_, _, _, rfl, rfl, rfl⟩
  | .list t, h, _ => forall2_refl_of fun y _ => Ty.rel0_refl t h y
  | .bag t, h, _ => Multi.of_forall2 (forall2_refl_of fun y _ => Ty.rel0_refl t h y)
  | .table k w, h, _ => by
    simp only [Ty.comparable, Bool.and_eq_true] at h
    exact Multi.of_forall2 (forall2_refl_of fun e _ => ⟨Ty.rel0_refl k h.1 e.1, Ty.rel0_refl w h.2 e.2⟩)
  | .tuple ts, h, x => Ty.rels0_refl ts h x
  | .adt _ _ vs, h, x => Ty.relAlts0_refl vs h x
  | .fn .., h, _ => by simp [Ty.comparable] at h
  | .dsl k _, h, _ => by
    simp only [Ty.comparable, beq_iff_eq] at h
    subst h; rfl
theorem Ty.rels0_refl : (ts : List Ty) → Ty.comparables ts = true → (x : (Ty.semsWith Dsl.base ts).1) →
    Ty.relsWith Dsl.base (Dsl.rel0 PBij.refl) PBij.refl ts x x
  | [], _, _ => trivial
  | t :: ts, h, x => by
    simp only [Ty.comparables, Bool.and_eq_true] at h
    exact ⟨Ty.rel0_refl t h.1 x.1, Ty.rels0_refl ts h.2 x.2⟩
theorem Ty.relAlts0_refl : (vs : List (List Ty)) → Ty.comparabless vs = true →
    (x : (Ty.semAltsWith Dsl.base vs).1) → Ty.relAltsWith Dsl.base (Dsl.rel0 PBij.refl) PBij.refl vs x x
  | [], _, x => nomatch x
  | fs :: _, h, .inl x => by
    simp only [Ty.comparabless, Bool.and_eq_true] at h
    exact Ty.rels0_refl fs h.1 x
  | _ :: vs, h, .inr x => by
    simp only [Ty.comparabless, Bool.and_eq_true] at h
    exact Ty.relAlts0_refl vs h.2 x
end

theorem forall2_find? {α β : Type} {r : α → β → Prop} {p : α → Bool} {q : β → Bool} (hpq : ∀ a b, r a b → p a = q b) :
    {xs : List α} → {ys : List β} → Forall2 r xs ys → Option.Rel r (xs.find? p) (ys.find? q)
  | [], [], _ => .none
  | a :: _, b :: _, ⟨hab, h⟩ => by
    simp only [List.find?_cons, hpq a b hab]
    split
    · exact .some hab
    · exact forall2_find? hpq h
  | [], _ :: _, h | _ :: _, [], h => h.elim

namespace Step

section Machine
variable {r e : Ty}

/-- A machine whose functions respect every renaming of counters, with a comparable key type. -/
structure _root_.Tazuna.Ir.MachineV.Equi (m : MachineV r e) : Prop where
  key : m.key.comparable = true
  self : ∀ R, m.Self R

theorem _root_.Tazuna.Ir.MachineV.Equi.effect {m : MachineV r e} (hm : m.Equi) (R : PBij) {xs ys}
    (h : Ty.rel0 R (.tuple [Ty.machineCtx m.key m.state r]) xs ys) :
    Ty.relV R (Ty.option (.dsl .effect [e])) (m.effect.apply xs) (m.effect.apply ys) :=
  EffectFun.apply_rel m.effect (hm.self R).effect h

theorem toB_rel {a b : Ty.bool.den0} (h : Ty.rel0 R Ty.bool a b) : toB a = toB b := by
  match a, b, h with
  | .inl _, .inl _, _ => rfl
  | .inr _, .inr _, _ => rfl

theorem broken_rel : {xs ys : Ty.rules.den0} → Ty.rel0 R Ty.rules xs ys → broken xs = broken ys
  | [], [], _ => rfl
  | (n, b, ()) :: xs, (n', b', ()) :: ys, ⟨⟨hn, hb, _⟩, h⟩ => by
    have hn : n = n' := hn
    subst hn
    have ih := broken_rel h
    unfold broken at ih ⊢
    erw [List.filterMap_cons, List.filterMap_cons, ih]
    dsimp only
    rw [toB_rel hb]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem timerAt_rel {st : Ty} (now : Int) {x y : (Ty.option (Ty.timer st)).den0}
    (h : Ty.rel0 R (Ty.option (Ty.timer st)) x y) :
    Option.Rel (fun a b => a.1 = b.1 ∧ Ty.rel0 R st a.2 b.2) (timerAt now x) (timerAt now y) := by
  match x, y, h with
  | .inl (.inl (d, t, ()), ()), .inl (.inl (d', t', ()), ()), ⟨⟨hd, ht, _⟩, _⟩ =>
    have hd : d = d' := hd
    subst hd
    exact .some ⟨rfl, ht⟩
  | .inr _, .inr _, _ => exact .none

theorem enter_rel {m : MachineV r e} (hm : m.Equi) {records records' : r.den0} (hrec : Ty.rel0 R r records records')
    (now : Int) {k k' : m.key.den0} (hk : Ty.rel0 R m.key k k') {st st' : m.state.den0}
    (hst : Ty.rel0 R m.state st st') :
    Instance.Rel R (enter m records now k st).1 (enter m records' now k' st').1 ∧
      Forall2 (Started.Rel R) (enter m records now k st).2 (enter m records' now k' st').2 := by
  have hctx : Ty.rel0 R (.tuple [Ty.machineCtx m.key m.state r]) (.inl (k, st, records, now, ()), ())
      (.inl (k', st', records', now, ()), ()) := ⟨⟨hk, hst, hrec, rfl, trivial⟩, trivial⟩
  refine ⟨⟨hk, hst, timerAt_rel now ((hm.self R).after _ _ hctx)⟩, ?_⟩
  have he := hm.effect R hctx
  simp only [enter]
  unfold MachineV.effectAt
  revert he
  generalize m.effect.apply (.inl (k, st, records, now, ()), ()) = x
  generalize m.effect.apply (.inl (k', st', records', now, ()), ()) = y
  intro he
  match x, y, he with
  | .inl (x, ()), .inl (y, ()), ⟨hxy, _⟩ => exact ⟨⟨.machine _ (.mk hk), hxy⟩, trivial⟩
  | .inr _, .inr _, _ => trivial

theorem find_rel {m : MachineV r e} (hm : m.Equi) {l l' : List (Instance m)} (hl : Insts.Rel R l l')
    {k k' : m.key.den0} (hk : Ty.rel0 R m.key k k') :
    Option.Rel (Instance.Rel R) (l.find? (m.key.deq0 k ·.key)) (l'.find? (m.key.deq0 k' ·.key)) := by
  obtain ⟨⟨zs, h, hz⟩, _, hd'⟩ := hl
  have h1 := forall2_find? (p := (m.key.deq0 k ·.key)) (q := (m.key.deq0 k' ·.key))
    (fun a b hab => Ty.rel0_deq m.key hm.key hk hab.1) h
  rwa [find?_perm_unique hz] at h1
  intro a ha b hb hpa hpb
  have hdz : KeysDistinct zs := hd'.perm hz.symm fun {x y} h => by
    cases e : m.key.deq0 y.key x.key
    · rfl
    · rw [Ty.deq0_symm hm.key e] at h; cases h
  have hab : m.key.deq0 a.key b.key = true := Ty.deq0_trans hm.key (Ty.deq0_symm hm.key hpa) hpb
  exact pairwise_eq_of hdz ha hb (fun h => by rw [h] at hab; cases hab)
    (fun h => by rw [Ty.deq0_symm hm.key hab] at h; cases h)


/-- What an instance's reaction to an event gives: the instance, and the effects it starts, in order. -/
def Reacted.Rel (R : PBij) {m : MachineV r e} (p q : Instance m × List (Sender × EffectV e)) : Prop :=
  Instance.Rel R p.1 q.1 ∧ Forall2 (Started.Rel R) p.2 q.2

theorem reactKey_rel {m : MachineV r e} (hm : m.Equi) {insts insts' : List (Instance m)} (hl : Insts.Rel R insts insts')
    {records records' : r.den0} (hrec : Ty.rel0 R r records records') (now : Int) {ev ev' : e.den0}
    (hev : Ty.rel0 R e ev ev') {k k' : m.key.den0} (hk : Ty.rel0 R m.key k k') :
    Reacted.Rel R (reactKey m insts records now ev k) (reactKey m insts' records' now ev' k') := by
  unfold reactKey
  have hf := find_rel hm hl hk
  revert hf
  generalize insts.find? _ = a
  generalize insts'.find? _ = b
  intro hf
  cases hf with
  | none => exact enter_rel hm hrec now hk (hm.self R).initial
  | @some i i' hi =>
    dsimp only
    have hon := (hm.self R).on (.inl (i.key, i.state, records, now, ()), ev, ()) (.inl (i'.key, i'.state, records', now, ()), ev', ())
      ⟨⟨hi.1, hi.2.1, hrec, rfl, trivial⟩, hev, trivial⟩
    revert hon
    generalize m.on.fn (.inl (i.key, i.state, records, now, ()), ev, ()) = x
    generalize m.on.fn (.inl (i'.key, i'.state, records', now, ()), ev', ()) = y
    intro hon
    match x, y, hon with
    | .inr (.inl (s, ())), .inr (.inl (s', ())), ⟨hs, _⟩ => exact enter_rel hm hrec now hi.1 hs
    | .inl (), .inl (), _ => exact ⟨hi, trivial⟩

theorem enter_key {m : MachineV r e} (records : r.den0) (now : Int) (k : m.key.den0) (st : m.state.den0) :
    (enter m records now k st).1.key = k := rfl

theorem reactKey_key {m : MachineV r e} (hm : m.Equi) (insts : List (Instance m)) (records : r.den0) (now : Int)
    (ev : e.den0) (k : m.key.den0) : m.key.deq0 (reactKey m insts records now ev k).1.key k = true := by
  unfold reactKey
  cases hf : insts.find? (m.key.deq0 k ·.key) with
  | none => exact Ty.deq0_refl hm.key k
  | some i =>
    have hki : m.key.deq0 k i.key = true := by simpa using List.find?_some hf
    dsimp only
    split <;> exact Ty.deq0_symm hm.key hki

theorem machineStep_rel (T : List TypeDecl) {m : MachineV r e} (hm : m.Equi) {records records' : r.den0}
    (hrec : Ty.rel0 R r records records') (now : Int) {ev ev' : e.den0} (hev : Ty.rel0 R e ev ev')
    {insts insts' : List (Instance m)} (hl : Insts.Rel R insts insts') :
    Insts.Rel R (machineStep T records now ev m insts).1 (machineStep T records' now ev' m insts').1 ∧
      Multi (Started.Rel R) (machineStep T records now ev m insts).2 (machineStep T records' now ev' m insts').2 := by
  have hb : Multi (Ty.rel0 R m.key) (m.instances.fn (records, ())) (m.instances.fn (records', ())) :=
    (hm.self R).instances _ _ ⟨hrec, trivial⟩
  have hd : Multi (Ty.rel0 R m.key) (dedupBy m.key.deq0 (m.instances.fn (records, ())))
      (dedupBy m.key.deq0 (m.instances.fn (records', ()))) := by
    obtain ⟨zs, h, hz⟩ := hb
    exact ((Multi.of_forall2 (forall2_dedupBy (f := m.key.deq0) (f' := m.key.deq0)
      (fun _ _ _ _ => Ty.rel0_deq m.key hm.key) h)).comp
      (dedupBy_perm_multi (Ty.canon_iff m.key hm.key) hz)).imp fun _ _ ⟨_, h1, h2⟩ => Ty.rel0_deq_right hm.key h1 h2
  have hs : Multi (Ty.rel0 R m.key) (Ty.sortBy T m.key (dedupBy m.key.deq0 (m.instances.fn (records, ()))))
      (Ty.sortBy T m.key (dedupBy m.key.deq0 (m.instances.fn (records', ())))) :=
    (hd.perm_left (List.mergeSort_perm _ _).symm).perm_right (List.mergeSort_perm _ _).symm
  have hr := hs.map (r' := Reacted.Rel R) (fun _ _ hk => reactKey_rel hm hl hrec now hev hk)
  have hdist : ∀ (rec : r.den0) (ev : e.den0) (l : List (Instance m)), KeysDistinct
      ((Ty.sortBy T m.key (dedupBy m.key.deq0 (m.instances.fn (rec, ())))).map (reactKey m l rec now ev) |>.map (·.1)) := by
    intro rec ev l
    have hp : (Ty.sortBy T m.key (dedupBy m.key.deq0 (m.instances.fn (rec, ())))).Pairwise
        fun a b => m.key.deq0 a b = false :=
      ((dedupBy_pairwise _ _).imp fun {a b} h => by
        cases e : m.key.deq0 a b
        · rfl
        · rw [Ty.deq0_symm hm.key e] at h; cases h).perm (List.mergeSort_perm _ _).symm fun {a b} h => by
          cases e : m.key.deq0 b a
          · rfl
          · rw [Ty.deq0_symm hm.key e] at h; cases h
    unfold KeysDistinct
    rw [List.map_map, List.pairwise_map]
    refine hp.imp fun {a b} h => ?_
    show m.key.deq0 (reactKey m l rec now ev a).1.key (reactKey m l rec now ev b).1.key = false
    cases e : m.key.deq0 (reactKey m l rec now ev a).1.key (reactKey m l rec now ev b).1.key
    · rfl
    · have := Ty.deq0_trans hm.key (Ty.deq0_symm hm.key (reactKey_key hm l rec now ev a))
        (Ty.deq0_trans hm.key e (reactKey_key hm l rec now ev b))
      rw [this] at h; cases h
  exact ⟨⟨hr.map fun _ _ h => h.1, hdist _ _ _, hdist _ _ _⟩, hr.flatMap fun _ _ h => Multi.of_forall2 h.2⟩

theorem reactMachines_rel (T : List TypeDecl) {records records' : r.den0} (hrec : Ty.rel0 R r records records')
    (now : Int) {ev ev' : e.den0} (hev : Ty.rel0 R e ev ev') : {ms : List (MachineV r e)} → (∀ m ∈ ms, m.Equi) →
    {l l' : Machines ms} → Machines.Rel R l l' →
    Machines.Rel R (reactMachines T records now ev l).1 (reactMachines T records' now ev' l').1 ∧
      Multi (Started.Rel R) (reactMachines T records now ev l).2 (reactMachines T records' now ev' l').2
  | [], _, .nil, .nil, _ => ⟨trivial, Multi.nil⟩
  | _ :: _, hms, .cons _ _, .cons _ _, h => by
    obtain ⟨hx, hrest⟩ := h
    have h1 := machineStep_rel T (hms _ List.mem_cons_self) hrec now hev hx
    have h2 := reactMachines_rel T hrec now hev (fun m h => hms m (List.mem_cons_of_mem _ h)) hrest
    simp only [reactMachines]
    exact ⟨⟨h1.1, h2.1⟩, h1.2.append h2.2⟩

end Machine

variable {v : ServiceV}

/-- A service whose functions respect every renaming of counters: its kept functions, the values they captured, the
callers it lists and its machines' initial states. Callers and machine keys and states are comparable, as check
requires. -/
structure _root_.Tazuna.Ir.ServiceV.Equivariant (v : ServiceV) : Prop where
  caller : v.caller.comparable = true
  keys : ∀ m ∈ v.machines, m.key.comparable = true
  states : ∀ m ∈ v.machines, m.state.comparable = true
  self : ∀ R, v.Self R

theorem _root_.Tazuna.Ir.ServiceV.Equivariant.machines (hv : v.Equivariant) : ∀ m ∈ v.machines, m.Equi :=
  fun m hm => ⟨hv.keys m hm, fun R => (hv.self R).machines m hm⟩

theorem react_rel (T : List TypeDecl) (hv : v.Equivariant) {R : Ren} {s s' : State v} (hs : StateRel R s s')
    {ev ev' : v.event.den0} (hev : Ty.rel0 R.ctr v.event ev ev') :
    StateRel R (react T s ev).1 (react T s' ev').1 ∧
      Multi (Started.Rel R.ctr) (react T s ev).2 (react T s' ev').2 := by
  obtain ⟨hrec, hmach, hpend, hnow, hb, hb'⟩ := hs
  have hrec' : Ty.rel0 R.ctr v.records (v.apply.fn (s.records, ev, ())) (v.apply.fn (s'.records, ev', ())) :=
    (hv.self R.ctr).apply _ _ ⟨hrec, hev, trivial⟩
  have hm := reactMachines_rel T hrec' s.now hev hv.machines hmach
  unfold react
  dsimp only
  rw [← hnow]
  refine ⟨⟨hrec', hm.1, hpend, rfl, hb, hb'⟩, hm.2.append (Multi.of_forall2 ?_)⟩
  have hx : ∀ x ∈ v.reactions, Forall2 (Started.Rel R.ctr)
      ((x.effectsAt ev (v.apply.fn (s.records, ev, ())) s.now).map (.reaction x.name, ·))
      ((x.effectsAt ev' (v.apply.fn (s'.records, ev', ())) s.now).map (.reaction x.name, ·)) := fun x hx =>
    forall2_map2 (fun _ _ h => ⟨.reaction x.name, h⟩)
      (EffectFun.apply_rel x.react ((hv.self R.ctr).reactions x hx) ⟨⟨hrec', rfl, trivial⟩, hev, trivial⟩)
  clear hm hpend
  revert hx
  induction v.reactions with
  | nil => intro; trivial
  | cons x xs ih =>
    intro hx
    simp only [List.flatMap_cons]
    exact forall2_append (hx x List.mem_cons_self) (ih fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem applyEvents_rel (T : List TypeDecl) (hv : v.Equivariant) : {evs evs' : List v.event.den0} → (R : Ren) →
    Forall2 (Ty.rel0 R.ctr v.event) evs evs' → {a a' : Acc v} → Acc.Rel R a a' →
    Lifted R a a' (applyEvents T a evs) (applyEvents T a' evs')
  | [], [], R, _, a, a', ha => Lifted.refl ha
  | ev :: evs, ev' :: evs', R, ⟨hev, h⟩, a, a', ha => by
    unfold applyEvents
    rw [List.foldlM_cons, List.foldlM_cons]
    have hr := react_rel T hv ha.1 hev
    obtain ⟨_, hevs, hout, ho, ho', hown⟩ := ha
    refine Lifted.bind ((start_rel (a := { a with state := (react T a.state ev).1, events := a.events ++ [ev] })
      (a' := { a' with state := (react T a'.state ev').1, events := a'.events ++ [ev'] })
      ⟨hr.1, hevs.append (Multi.cons hev Multi.nil), hout, ho, ho', hown⟩ hr.2).shift 0 rfl rfl rfl rfl) ?_
    intro R' b b' hc hb
    exact applyEvents_rel T hv R' (hc ▸ h) hb
  | [], _ :: _, _, h, _, _, _ | _ :: _, [], _, h, _, _, _ => h.elim

theorem _root_.Tazuna.Ir.Ty.origin_comparable {c : Ty} (h : c.comparable = true) :
    (Ty.origin c).comparable = true := by
  simp [Ty.origin, Ty.comparable, Ty.comparables, Ty.comparabless, h]

theorem rel0_outside {R : PBij} {c : Ty} {x y : c.den0} (h : Ty.rel0 R c x y) :
    Ty.rel0 R (Ty.origin c) (outside x) (outside y) := ⟨h, trivial⟩

theorem rel0_own {R : PBij} {c : Ty} : Ty.rel0 R (Ty.origin c) own own := ⟨⟩

theorem admit_rel (hv : v.Equivariant) {R : PBij} {i : Ty} {callers : List (Ty.origin v.caller).den0}
    (hcl : Ty.rel0 R (.list (Ty.origin v.caller)) callers callers) {accepts : Fun (Ty.fn [i] Ty.rules)}
    (hacc : Fun.Rel R accepts accepts) {c c' : (Ty.origin v.caller).den0} (hc : Ty.rel0 R (Ty.origin v.caller) c c') {x x' : i.den0}
    (hx : Ty.rel0 R i x x') : admit callers accepts c x = admit callers accepts c' x' := by
  unfold admit
  rw [forall2_any (q := (Ty.origin v.caller).deq0 c')
    (fun a b hab => Ty.rel0_deq (Ty.origin v.caller) (Ty.origin_comparable hv.caller) hc hab) hcl,
    broken_rel (hacc (x, ()) (x', ()) ⟨hx, trivial⟩)]

theorem okNil_rel {R : PBij} {j : Ty} : Ty.rel0 R (Ty.result Ty.nil j) okNil okNil := ⟨⟨⟩, trivial⟩

theorem lifted_error {R : Ren} {a a' : Acc v} {e e' : Fault} : Lifted R a a' (.error e) (.error e') :=
  .inl ⟨trivial, trivial⟩

theorem runCommand_rel (T : List TypeDecl) (hv : v.Equivariant) {R : Ren} {a a' : Acc v} (ha : Acc.Rel R a a')
    (hctr : R.ctr.rel a.state.fresh a'.state.fresh) {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands)
    {c c' : (Ty.origin v.caller).den0} (hc : Ty.rel0 R.ctr (Ty.origin v.caller) c c') {i i' : x.input.den0} (hi : Ty.rel0 R.ctr x.input i i')
    {f f' : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))} (hf : Fun.Rel R.ctr f f') :
    Lifted R a a' (runCommand T a x c i f) (runCommand T a' x c' i' f') := by
  obtain ⟨hcl, hacc, hdec, hens⟩ := (hv.self R.ctr).commands x hx
  unfold runCommand execCommand
  rw [admit_rel hv hcl hacc hc hi]
  cases admit x.callers x.accepts c' i' with
  | cons r rs => exact lifted_error
  | nil =>
    dsimp only
    have hcx : Ty.rel0 R.ctr (Ty.ctx v.records x.input v.caller) (ctx a.state a.state.records c i)
        (ctx a'.state a'.state.records c' i') := ⟨ha.1.1, hi, hc, ha.1.2.2.2.1, hctr, trivial⟩
    have hd := hdec (ctx a.state a.state.records c i, ()) (ctx a'.state a'.state.records c' i', ()) ⟨hcx, trivial⟩
    revert hd
    generalize x.decide.fn (ctx a.state a.state.records c i, ()) = d
    generalize x.decide.fn (ctx a'.state a'.state.records c' i', ()) = d'
    intro hd
    obtain ⟨hst, hevs0, hout, ho, ho', hown⟩ := ha
    have ha1 : Acc.Rel R { a with state := { a.state with fresh := a.state.fresh + 1 } }
        { a' with state := { a'.state with fresh := a'.state.fresh + 1 } } := ⟨hst, hevs0, hout, ho, ho', hown⟩
    match d, d', hd with
    | .inl (evs, ()), .inl (evs', ()), ⟨hevs, _⟩ =>
      dsimp only
      simp only [bind_assoc]
      refine Lifted.bind ((applyEvents_rel T hv R hevs ha1).shift 1 rfl rfl rfl rfl) ?_
      intro R' b b' hcr hb
      have hbr : Ty.rel0 R.ctr v.records b.state.records b'.state.records := hcr ▸ hb.1.1
      rw [broken_rel (hens (ctx a.state a.state.records c i, b.state.records, ())
        (ctx a'.state a'.state.records c' i', b'.state.records, ()) ⟨hcx, hbr, trivial⟩)]
      cases broken (x.ensures.fn (ctx a'.state a'.state.records c' i', b'.state.records, ())) with
      | cons n ns => exact lifted_error
      | nil => exact applyEvents_rel T hv R' (hcr ▸ hf (okNil, ()) (okNil, ()) ⟨okNil_rel, trivial⟩) hb
    | .inr (.inl (j, ())), .inr (.inl (j', ())), ⟨hj, _⟩ =>
      exact (applyEvents_rel T hv R (hf (.inr (.inl (j, ())), ()) (.inr (.inl (j', ())), ())
        ⟨⟨hj, trivial⟩, trivial⟩) ha1).shift 1 rfl rfl rfl rfl

theorem runQuery_rel (T : List TypeDecl) (hv : v.Equivariant) {R : Ren} {a a' : Acc v} (ha : Acc.Rel R a a')
    {x : QueryV v.records v.caller} (hx : x ∈ v.queries)
    {c c' : (Ty.origin v.caller).den0} (hc : Ty.rel0 R.ctr (Ty.origin v.caller) c c') {i i' : x.input.den0} (hi : Ty.rel0 R.ctr x.input i i')
    {f f' : Fun (Ty.fn [x.output] (.list v.event))} (hf : Fun.Rel R.ctr f f') :
    Lifted R a a' (runQuery T a x c i f) (runQuery T a' x c' i' f') := by
  obtain ⟨hcl, hacc, hres⟩ := (hv.self R.ctr).queries x hx
  unfold runQuery execQuery
  rw [admit_rel hv hcl hacc hc hi]
  cases admit x.callers x.accepts c' i' with
  | cons r rs => exact lifted_error
  | nil =>
    have hcx : Ty.rel0 R.ctr (Ty.queryCtx v.records x.input v.caller) (queryCtx a.state a.state.records c i)
        (queryCtx a'.state a'.state.records c' i') := ⟨ha.1.1, hi, hc, ha.1.2.2.2.1, trivial⟩
    obtain ⟨hst, hevs0, hout, ho, ho', hown⟩ := ha
    exact (applyEvents_rel T hv R (hf _ _ ⟨hres (queryCtx a.state a.state.records c i, ())
      (queryCtx a'.state a'.state.records c' i', ()) ⟨hcx, trivial⟩, trivial⟩)
      (a := { a with state := { a.state with fresh := a.state.fresh + 1 } })
      (a' := { a' with state := { a'.state with fresh := a'.state.fresh + 1 } })
      ⟨hst, hevs0, hout, ho, ho', hown⟩).shift 1 rfl rfl rfl rfl

theorem ownCommand_mem {name : String} {i j : Ty}
    {x : (x : CommandV v.records v.event v.caller) ×' (i = x.input ∧ j = x.rejection)}
    (h : ownCommand (v := v) name i j = some x) : x.1 ∈ v.commands := by
  obtain ⟨y, hy, hf⟩ := List.exists_of_findSome?_eq_some h
  split at hf
  · split at hf
    · cases hf; exact hy
    · cases hf
  · cases hf

theorem ownQuery_mem {name : String} {i o : Ty}
    {x : (x : QueryV v.records v.caller) ×' (i = x.input ∧ o = x.output)}
    (h : ownQuery (v := v) name i o = some x) : x.1 ∈ v.queries := by
  obtain ⟨y, hy, hf⟩ := List.exists_of_findSome?_eq_some h
  split at hf
  · split at hf
    · cases hf; exact hy
    · cases hf
  · cases hf

/-- Running related own effects from related steps, with related counters, faults on both sides or ends related. -/
theorem runOwn_rel (T : List TypeDecl) (hv : v.Equivariant) {R : Ren} {a a' : Acc v} (ha : Acc.Rel R a a')
    (hctr : R.ctr.rel a.state.fresh a'.state.fresh) {eff eff' : OwnEffectV v.event} (he : OwnEffectV.Rel R.ctr eff eff') :
    Lifted R a a' (runOwn T a eff) (runOwn T a' eff') := by
  cases he with
  | command name c i j hval hf =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    generalize hox : ownCommand (v := v) name i j = ox
    cases oc with
    | none => exact lifted_error
    | some hcp =>
      cases ox with
      | none => exact lifted_error
      | some x =>
        obtain ⟨hcp⟩ := hcp
        have hmem := ownCommand_mem hox
        obtain ⟨x, hi, hj⟩ := x
        subst hcp hi hj
        exact runCommand_rel T hv ha hctr hmem rel0_own hval hf
  | query name c i o hval hf =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    generalize hox : ownQuery (v := v) name i o = ox
    cases oc with
    | none => exact lifted_error
    | some hcp =>
      cases ox with
      | none => exact lifted_error
      | some x =>
        obtain ⟨hcp⟩ := hcp
        have hmem := ownQuery_mem hox
        obtain ⟨x, hi, ho⟩ := x
        subst hcp hi ho
        exact runQuery_rel T hv ha hmem rel0_own hval hf

end Step

section Inverse

theorem Multi.inv {α β : Type} {r : α → β → Prop} {r' : β → α → Prop} (h : ∀ a b, r a b → r' b a) {xs : List α}
    {ys : List β} (m : Multi r xs ys) : Multi r' ys xs :=
  m.flip.imp fun b a h' => h a b h'

theorem Fun.rel_inv {R : PBij} {t : Ty} {f g : Fun t} (h : Fun.Rel R f g) : Fun.Rel R.inv g f := Ty.rel0_inv.1 h

theorem WireVal.rel_inv {R : PBij} {x y : WireVal} (h : WireVal.Rel R x y) : WireVal.Rel R.inv y x := by
  cases h with | mk h => exact .mk (Ty.rel0_inv.1 h)

theorem Sender.rel_inv {R : PBij} {x y : Sender} (h : Sender.Rel R x y) : Sender.Rel R.inv y x := by
  cases h with
  | machine _ h => exact .machine _ (WireVal.rel_inv h)
  | reaction _ => exact .reaction _

theorem RequestV.rel_inv {R : PBij} {e : Ty} {x y : RequestV e} (h : RequestV.Rel R x y) : RequestV.Rel R.inv y x := by
  cases h with
  | mk _ _ _ _ hv hh ho =>
    refine .mk _ _ _ _ (Ty.rel0_inv.1 hv) ?_ (Fun.rel_inv ho)
    cases hh with
    | none => exact .none
    | some h => exact .some (Fun.rel_inv h)

theorem EffectV.rel_inv {R : PBij} {e : Ty} {x y : EffectV e} (h : EffectV.Rel R x y) : EffectV.Rel R.inv y x := by
  cases h with
  | request h => exact .request (RequestV.rel_inv h)
  | command _ _ _ _ hv hf => exact .command _ _ _ _ (Ty.rel0_inv.1 hv) (Fun.rel_inv hf)
  | query _ _ _ _ hv hf => exact .query _ _ _ _ (Ty.rel0_inv.1 hv) (Fun.rel_inv hf)

namespace Step
variable {r e : Ty}

theorem Instance.rel_inv {R : PBij} {m : MachineV r e} {i j : Instance m} (h : Instance.Rel R i j) :
    Instance.Rel R.inv j i := by
  obtain ⟨hk, hs, ht⟩ := h
  refine ⟨Ty.rel0_inv.1 hk, Ty.rel0_inv.1 hs, ?_⟩
  revert ht
  generalize i.timer = x
  generalize j.timer = y
  intro ht
  cases ht with
  | none => exact .none
  | some h => exact .some ⟨h.1.symm, Ty.rel0_inv.1 h.2⟩

theorem Machines.rel_inv {R : PBij} : {ms : List (MachineV r e)} → {l l' : Machines ms} → Machines.Rel R l l' →
    Machines.Rel R.inv l' l
  | [], .nil, .nil, _ => trivial
  | _ :: _, .cons _ _, .cons _ _, h => by
    obtain ⟨⟨hm, hd, hd'⟩, h⟩ := h
    exact ⟨⟨hm.inv fun _ _ => Instance.rel_inv, hd', hd⟩, Machines.rel_inv h⟩

variable {v : ServiceV}

theorem Acc.rel_inv {R : Ren} {a a' : Acc v} (h : Acc.Rel R a a') : Acc.Rel R.inv a' a := by
  obtain ⟨⟨hrec, hmach, hpend, hnow, hb, hb'⟩, hev, hout, ho, ho', hown⟩ := h
  exact ⟨⟨Ty.rel0_inv.1 hrec, Machines.rel_inv hmach, hpend.inv fun _ _ h => ⟨h.1, Sender.rel_inv h.2.1, h.2.2.1.symm, RequestV.rel_inv h.2.2.2⟩,
    hnow.symm, hb', hb⟩, hev.inv fun _ _ h => Ty.rel0_inv.1 h,
    hout.inv fun _ _ h => ⟨h.1, h.2.1.symm, h.2.2.1.symm, WireVal.rel_inv h.2.2.2⟩, ho', ho,
    hown.inv fun _ _ h => OwnEffectV.rel_iff.2 (EffectV.rel_inv (OwnEffectV.rel_iff.1 h))⟩

end Step

end Inverse

namespace Step

variable {v : ServiceV}

/-- Steps in progress that are the same up to a renaming of the names made from the counter `f0` and the next wire id
`n0` on, at the same counter and next wire id: the base of the equivalence the own cascade is checked up to. Names
made before stay as they are, as the oracle keeps the names earlier lines showed. -/
def RenamedFrom (f0 n0 : Nat) (a a' : Acc v) : Prop :=
  ∃ R : Ren, Acc.Rel R a a' ∧ a.state.fresh = a'.state.fresh ∧ a.state.nextId = a'.state.nextId ∧
    n0 ≤ a.state.nextId ∧ (∀ n, (n < f0 ∨ a.state.fresh ≤ n) → R.ctr.rel n n) ∧ ∀ i < n0, R.wire.rel i i

theorem RenamedFrom.symm {f0 n0 : Nat} {a a' : Acc v} : RenamedFrom f0 n0 a a' → RenamedFrom f0 n0 a' a
  | ⟨R, h, hf, hn, hn0, hfix, hw⟩ =>
    ⟨R.inv, Acc.rel_inv h, hf.symm, hn.symm, hn ▸ hn0, fun n hn' => hfix n (hf ▸ hn'), fun i hi => hw i hi⟩

/-- Fixing more names is a finer equivalence. -/
theorem RenamedFrom.mono {f0 n0 f1 n1 : Nat} (hf : f0 ≤ f1) (hn : n0 ≤ n1) {a a' : Acc v} :
    RenamedFrom f1 n1 a a' → RenamedFrom f0 n0 a a'
  | ⟨R, h, hfr, hni, hn1, hfix, hw⟩ =>
    ⟨R, h, hfr, hni, Nat.le_trans hn hn1, fun n hn' => hfix n (hn'.imp (fun h => by omega) id),
      fun i hi => hw i (by omega)⟩

/-- The two orders' equivalence: the same up to renaming the wire ids and the ids made from the counter `f0` and the
next wire id `n0` on, collections as multisets. -/
abbrev Same (f0 n0 : Nat) : Acc v → Acc v → Prop := Diamond.Closure (RenamedFrom f0 n0)

theorem Same.mono {f0 n0 f1 n1 : Nat} (hf : f0 ≤ f1) (hn : n0 ≤ n1) {a b : Acc v} (h : Same f1 n1 a b) :
    Same f0 n0 a b := by
  induction h with
  | base h => exact .base (h.mono hf hn)
  | refl a => exact .refl a
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- The own cascade respects renaming: equivalent steps in progress have as many own effects waiting, and running
any one of them has a partner on the other side that ends equivalently or also faults. -/
theorem ownSys_simulates (T : List TypeDecl) (hv : v.Equivariant) (f0 n0 : Nat) :
    Diamond.Simulates (ownSys T v) (Same (v := v) f0 n0) := by
  refine Diamond.Simulates.closure RenamedFrom.symm ?_
  intro a a' ⟨R, ha, hf, hn, hn0, hfix, hw⟩
  have hown := ha.2.2.2.2.2
  refine ⟨hown.length_eq, fun i hi => ?_⟩
  obtain ⟨j, hj, hij, hm⟩ := hown.eraseIdx i hi
  refine ⟨j, hj, ?_⟩
  have ha1 : Acc.Rel R { a with own := a.own.eraseIdx i } { a' with own := a'.own.eraseIdx j } :=
    ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.1, hm⟩
  have hctr : R.ctr.rel a.state.fresh a'.state.fresh := hf ▸ hfix _ (.inr (Nat.le_refl _))
  have hl := runOwn_rel T hv ha1 hctr hij
  simp only [ownSys, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  rcases hl with ⟨h1, h2⟩ | ⟨b, b', R', h1, h2, hc, hb, hmono, hfb, hnb, hl, hext⟩
  · exact .inr ⟨h1, h2⟩
  · rw [h1, h2]
    have : a.state.fresh = a'.state.fresh := hf
    have : a.state.nextId = a'.state.nextId := hn
    simp only at hfb hnb hl hext
    refine .inl ⟨R', hb, by omega, by omega, by omega,
      fun n hn' => hc ▸ hfix n (hn'.imp id fun h => Nat.le_trans hmono h), fun i hi => ?_⟩
    exact hext (by omega) (by omega) (hw i hi)

end Step

end Tazuna.Ir
