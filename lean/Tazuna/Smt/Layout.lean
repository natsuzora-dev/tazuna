import Tazuna.Smt.Encode
import Tazuna.Smt.EncodeExact

/-! What a layout holds for a type: `Layout.Has L t` says every datatype a value of `t` is coded with is in `L`, as
`Layout.addTys` adds them. `addTys_has` proves the builder adds what it promises, and `Has.mono` that a datatype once
found stays found as the layout grows (`Layout.Le`), so a layout built from a list of types holds each of them. -/

namespace Tazuna.Smt

open Tazuna.Ir

namespace Layout

/-- `L'` grows `L`: the same kinds of effect, and `L`'s datatypes first, at the same indices. -/
structure Le (L L' : Layout) : Prop where
  effects : L'.effects = L.effects
  owns : L'.owns = L.owns
  types : ∃ more, L'.types = L.types ++ more

theorem Le.refl (L : Layout) : Le L L := ⟨rfl, rfl, ⟨[], by simp⟩⟩

theorem Le.trans {L₁ L₂ L₃ : Layout} (a : Le L₁ L₂) (b : Le L₂ L₃) : Le L₁ L₃ := by
  obtain ⟨e1, o1, m1, h1⟩ := a
  obtain ⟨e2, o2, m2, h2⟩ := b
  exact ⟨e2.trans e1, o2.trans o1, m1 ++ m2, by rw [h2, h1, List.append_assoc]⟩

theorem find?_le {L L' : Layout} (h : Le L L') {t : Ty} {x : Nat × Nat} (hx : L.find? t = some x) :
    L'.find? t = some x := by
  obtain ⟨-, -, more, hm⟩ := h
  simp only [find?_eq, hm, List.zipIdx_append, List.find?_append] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp [hy]

theorem effectFields_le {L L' : Layout} (h : Le L L') (e : Ty) : L'.effectFields e = L.effectFields e := by
  simp [effectFields, effectsOf, ownsOf, h.effects, h.owns]

theorem push_le (L : Layout) (t : Ty) (n : Nat) : Le L (L.push t n) := by
  unfold push
  split
  · exact Le.refl L
  · exact ⟨rfl, rfl, [(t, n)], rfl⟩

theorem find?_push (L : Layout) (t : Ty) (n : Nat) : (L.push t n |>.find? t).isSome = true := by
  unfold push
  split
  · assumption
  · rename_i h
    simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
    simp only [find?_eq, List.zipIdx_append, List.find?_append] at h ⊢
    rw [Option.map_eq_none_iff.1 h]
    simp [List.zipIdx, Ty_same_self]

section
variable (L : Layout) (D : Dsl → List Ty → Prop)

mutual
/-- Every datatype a value of the type is coded with is in the layout; `D` says what a structure type needs. -/
def HasWith : Ty → Prop
  | .tuple ts => HasWiths ts ∧ (L.find? (.tuple ts)).isSome
  | .adt 0 a vs => (boolVs? vs).isSome ∨ (HasWithss vs ∧ (L.find? (.adt 0 a vs)).isSome)
  | .adt (i + 1) a vs => HasWithss vs ∧ (L.find? (.adt (i + 1) a vs)).isSome
  | .id => (L.find? .id).isSome
  | .list t => HasWith t ∧ (L.find? (.tuple [Ty.bool, t])).isSome ∧ (L.find? (.list t)).isSome
  | .bag t => HasWith t ∧ (L.find? (.tuple [Ty.bool, t])).isSome ∧ (L.find? (.bag t)).isSome
  | .table k v => HasWith k ∧ HasWith v ∧ (L.find? (.tuple [Ty.bool, k, v])).isSome ∧ (L.find? (.table k v)).isSome
  | .fn ps r => HasWiths ps ∧ HasWith r
  | .dsl k a => D k a
  | .int | .str | .point _ | .param _ => True
def HasWiths : List Ty → Prop
  | [] => True
  | t :: ts => HasWith t ∧ HasWiths ts
def HasWithss : List (List Ty) → Prop
  | [] => True
  | ts :: vs => HasWiths ts ∧ HasWithss vs
end

end

/-- What a structure type needs: the effect datatype of an event type, after its kinds' fields, which are data. -/
def HasDsl (L : Layout) : Dsl → List Ty → Prop
  | .effect, [e] => HasWithss L (fun _ _ => True) (L.effectFields e) ∧ (L.find? (.dsl .effect [e])).isSome
  | _, _ => True

/-- Every datatype a value of the type is coded with is in the layout, an effect type's included. -/
abbrev Has (L : Layout) (t : Ty) : Prop := HasWith L (HasDsl L) t

mutual
theorem HasWith.mono {L L' : Layout} (h : Le L L') {D D' : Dsl → List Ty → Prop} (hD : ∀ k a, D k a → D' k a) : (t : Ty) → HasWith L D t → HasWith L' D' t
  | .tuple ts, ⟨a, b⟩ => ⟨HasWiths.mono h hD ts a, by obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 b; simp [find?_le h hx]⟩
  | .adt 0 a vs, hv => by
    rcases hv with hb | ⟨hs, hf⟩
    · exact .inl hb
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hf
      exact .inr ⟨HasWithss.mono h hD vs hs, by simp [find?_le h hx]⟩
  | .adt (i + 1) a vs, ⟨hs, hf⟩ => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hf
    exact ⟨HasWithss.mono h hD vs hs, by simp [find?_le h hx]⟩
  | .id, hf => by obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hf; simp [HasWith, find?_le h hx]
  | .list t, ⟨a, b, c⟩ => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 b
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 c
    exact ⟨HasWith.mono h hD t a, by simp [find?_le h hx], by simp [find?_le h hy]⟩
  | .bag t, ⟨a, b, c⟩ => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 b
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 c
    exact ⟨HasWith.mono h hD t a, by simp [find?_le h hx], by simp [find?_le h hy]⟩
  | .table k v, ⟨a, a', b, c⟩ => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 b
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 c
    exact ⟨HasWith.mono h hD k a, HasWith.mono h hD v a', by simp [find?_le h hx], by simp [find?_le h hy]⟩
  | .fn ps r, ⟨a, b⟩ => ⟨HasWiths.mono h hD ps a, HasWith.mono h hD r b⟩
  | .dsl k a, hk => hD k a hk
  | .int, _ | .str, _ | .point _, _ | .param _, _ => trivial
theorem HasWiths.mono {L L' : Layout} (h : Le L L') {D D' : Dsl → List Ty → Prop} (hD : ∀ k a, D k a → D' k a) : (ts : List Ty) → HasWiths L D ts → HasWiths L' D' ts
  | [], _ => trivial
  | t :: ts, ⟨a, b⟩ => ⟨HasWith.mono h hD t a, HasWiths.mono h hD ts b⟩
theorem HasWithss.mono {L L' : Layout} (h : Le L L') {D D' : Dsl → List Ty → Prop} (hD : ∀ k a, D k a → D' k a) : (vs : List (List Ty)) → HasWithss L D vs → HasWithss L' D' vs
  | [], _ => trivial
  | ts :: vs, ⟨a, b⟩ => ⟨HasWiths.mono h hD ts a, HasWithss.mono h hD vs b⟩
end

theorem HasDsl.mono {L L' : Layout} (h : Le L L') (k : Dsl) (a : List Ty) (hk : HasDsl L k a) : HasDsl L' k a := by
  match k, a, hk with
  | .effect, [e], ⟨hs, hf⟩ =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hf
    exact ⟨by rw [effectFields_le h]; exact HasWithss.mono h (fun _ _ _ => trivial) _ hs, by simp [find?_le h hx]⟩
  | .spec, _, _ | .service, _, _ | .command, _, _ | .query, _, _ | .machine, _, _ | .reaction, _, _
  | .external, _, _ | .externalCommand, _, _ | .externalQuery, _, _ | .source, _, _ | .declared, _, _
  | .subscription, _, _ | .model, _, _ | .scope, _, _ | .values, _, _ | .create, _, _ | .response, _, _ | .scenario, _, _ | .step, _, _
  | .sender, _, _ | .closure, _, _ | .effectClosure, _, _ | .fresh, _, _ => trivial
  | .effect, [], _ | .effect, _ :: _ :: _, _ => trivial

theorem isSome_le {L L' : Layout} (h : Le L L') {t : Ty} (hf : (L.find? t).isSome = true) : (L'.find? t).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hf; simp [find?_le h hx]

section
variable {slots : Ty → Nat} {dsl : Layout → Dsl → List Ty → Layout}

mutual
theorem addTyWith_le (hd : ∀ L k a, Le L (dsl L k a)) : (L : Layout) → (t : Ty) → Le L (addTyWith slots dsl L t)
  | L, .tuple ts => (addTysWith_le hd L ts).trans (push_le _ _ _)
  | L, .adt 0 a vs => by
    simp only [addTyWith]; split
    · exact Le.refl L
    · exact (addTyssWith_le hd L vs).trans (push_le _ _ _)
  | L, .adt (i + 1) a vs => (addTyssWith_le hd L vs).trans (push_le _ _ _)
  | L, .id => push_le _ _ _
  | L, .list t => ((addTyWith_le hd L t).trans (push_le _ _ _)).trans (push_le _ _ _)
  | L, .bag t => ((addTyWith_le hd L t).trans (push_le _ _ _)).trans (push_le _ _ _)
  | L, .table k v =>
    (((addTyWith_le hd L k).trans (addTyWith_le hd _ v)).trans (push_le _ _ _)).trans (push_le _ _ _)
  | L, .fn ps r => (addTysWith_le hd L ps).trans (addTyWith_le hd _ r)
  | L, .dsl k a => hd L k a
  | L, .int | L, .str | L, .point _ | L, .param _ => Le.refl L
theorem addTysWith_le (hd : ∀ L k a, Le L (dsl L k a)) : (L : Layout) → (ts : List Ty) →
    Le L (addTysWith slots dsl L ts)
  | L, [] => Le.refl L
  | L, t :: ts => (addTyWith_le hd L t).trans (addTysWith_le hd _ ts)
theorem addTyssWith_le (hd : ∀ L k a, Le L (dsl L k a)) : (L : Layout) → (vs : List (List Ty)) →
    Le L (addTyssWith slots dsl L vs)
  | L, [] => Le.refl L
  | L, ts :: vs => (addTysWith_le hd L ts).trans (addTyssWith_le hd _ vs)
end

variable {D : Layout → Dsl → List Ty → Prop}

mutual
theorem addTyWith_has (hd : ∀ L k a, Le L (dsl L k a)) (hDm : ∀ L L', Le L L' → ∀ k a, D L k a → D L' k a)
    (hD : ∀ L k a, D (dsl L k a) k a) : (L : Layout) → (t : Ty) →
    HasWith (addTyWith slots dsl L t) (D (addTyWith slots dsl L t)) t
  | L, .tuple ts =>
    ⟨HasWiths.mono (push_le _ _ _) (hDm _ _ (push_le _ _ _)) ts (addTysWith_has hd hDm hD L ts), find?_push _ _ _⟩
  | L, .adt 0 a vs => by
    simp only [addTyWith]; split
    · exact .inl (by assumption)
    · exact .inr ⟨HasWithss.mono (push_le _ _ _) (hDm _ _ (push_le _ _ _)) vs (addTyssWith_has hd hDm hD L vs),
        find?_push _ _ _⟩
  | L, .adt (i + 1) a vs =>
    ⟨HasWithss.mono (push_le _ _ _) (hDm _ _ (push_le _ _ _)) vs (addTyssWith_has hd hDm hD L vs), find?_push _ _ _⟩
  | L, .id => find?_push _ _ _
  | L, .list t =>
    have h2 := (push_le _ _ _).trans (push_le _ _ _)
    ⟨HasWith.mono h2 (hDm _ _ h2) t (addTyWith_has hd hDm hD L t), isSome_le (push_le _ _ _) (find?_push _ _ _),
      find?_push _ _ _⟩
  | L, .bag t =>
    have h2 := (push_le _ _ _).trans (push_le _ _ _)
    ⟨HasWith.mono h2 (hDm _ _ h2) t (addTyWith_has hd hDm hD L t), isSome_le (push_le _ _ _) (find?_push _ _ _),
      find?_push _ _ _⟩
  | L, .table k v =>
    have h2 := (push_le _ _ _).trans (push_le _ _ _)
    have h3 := (addTyWith_le hd _ v).trans h2
    ⟨HasWith.mono h3 (hDm _ _ h3) k (addTyWith_has hd hDm hD L k),
      HasWith.mono h2 (hDm _ _ h2) v (addTyWith_has hd hDm hD _ v),
      isSome_le (push_le _ _ _) (find?_push _ _ _), find?_push _ _ _⟩
  | L, .fn ps r =>
    have h1 := addTyWith_le hd (addTysWith slots dsl L ps) r
    ⟨HasWiths.mono h1 (hDm _ _ h1) ps (addTysWith_has hd hDm hD L ps), addTyWith_has hd hDm hD _ r⟩
  | L, .dsl k a => hD L k a
  | _, .int | _, .str | _, .point _ | _, .param _ => trivial
theorem addTysWith_has (hd : ∀ L k a, Le L (dsl L k a)) (hDm : ∀ L L', Le L L' → ∀ k a, D L k a → D L' k a)
    (hD : ∀ L k a, D (dsl L k a) k a) : (L : Layout) → (ts : List Ty) →
    HasWiths (addTysWith slots dsl L ts) (D (addTysWith slots dsl L ts)) ts
  | _, [] => trivial
  | L, t :: ts =>
    have h1 := addTysWith_le hd (addTyWith slots dsl L t) ts
    ⟨HasWith.mono h1 (hDm _ _ h1) t (addTyWith_has hd hDm hD L t), addTysWith_has hd hDm hD _ ts⟩
theorem addTyssWith_has (hd : ∀ L k a, Le L (dsl L k a)) (hDm : ∀ L L', Le L L' → ∀ k a, D L k a → D L' k a)
    (hD : ∀ L k a, D (dsl L k a) k a) : (L : Layout) → (vs : List (List Ty)) →
    HasWithss (addTyssWith slots dsl L vs) (D (addTyssWith slots dsl L vs)) vs
  | _, [] => trivial
  | L, ts :: vs =>
    have h1 := addTyssWith_le hd (addTysWith slots dsl L ts) vs
    ⟨HasWiths.mono h1 (hDm _ _ h1) ts (addTysWith_has hd hDm hD L ts), addTyssWith_has hd hDm hD _ vs⟩
end

end

theorem fold_le (slots : Ty → Nat) : (fss : List (List Ty)) → (L : Layout) →
    Le L (fss.foldl (fun L fs => addTysWith slots (fun L _ _ => L) L fs) L)
  | [], L => Le.refl L
  | fs :: fss, L => (addTysWith_le (fun L _ _ => Le.refl L) L fs).trans (fold_le slots fss _)

theorem fold_has (slots : Ty → Nat) : (fss : List (List Ty)) → (L : Layout) →
    ∀ fs ∈ fss, HasWiths (fss.foldl (fun L fs => addTysWith slots (fun L _ _ => L) L fs) L) (fun _ _ => True) fs
  | [], _, _, h => nomatch h
  | fs :: fss, L, fs', h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact HasWiths.mono (fold_le slots fss _) (fun _ _ _ => trivial) fs'
        (addTysWith_has (D := fun _ _ _ => True) (fun L _ _ => Le.refl L) (fun _ _ _ _ _ _ => trivial)
          (fun _ _ _ => trivial) L fs')
    · exact fold_has slots fss _ fs' h

theorem hasWithss_of_mem {L : Layout} {D : Dsl → List Ty → Prop} : (vs : List (List Ty)) →
    (∀ fs ∈ vs, HasWiths L D fs) → HasWithss L D vs
  | [], _ => trivial
  | fs :: vs, h => ⟨h fs (by simp), hasWithss_of_mem vs fun fs' h' => h fs' (by simp [h'])⟩

theorem addEffect_le (slots : Ty → Nat) (L : Layout) (e : Ty) : Le L (addEffect slots L e) :=
  (fold_le slots _ L).trans (push_le _ _ _)

theorem addEffect_has (slots : Ty → Nat) (L : Layout) (e : Ty) : HasDsl (addEffect slots L e) .effect [e] := by
  refine ⟨?_, find?_push _ _ _⟩
  rw [effectFields_le (addEffect_le slots L e)]
  exact hasWithss_of_mem _ fun fs h =>
    HasWiths.mono (push_le _ _ _) (fun _ _ _ => trivial) fs (fold_has slots _ L fs h)

/-- The builder adds what it promises: every type in the list has its datatypes in the layout. -/
theorem addTys_has (slots : Ty → Nat) (L : Layout) (ts : List Ty) : HasWiths (addTys slots L ts) (HasDsl (addTys slots L ts)) ts := by
  unfold addTys
  refine addTysWith_has (D := HasDsl) ?_ (fun _ _ h => HasDsl.mono h) ?_ L ts
  · intro L k a
    match k, a with
    | .effect, [e] => exact addEffect_le _ L e
    | .effect, [] | .effect, _ :: _ :: _ | .spec, _ | .service, _ | .command, _ | .query, _ | .machine, _
    | .reaction, _ | .external, _ | .externalCommand, _ | .externalQuery, _ | .source, _ | .declared, _
    | .subscription, _ | .model, _ | .scope, _ | .values, _ | .create, _ | .response, _ | .scenario, _ | .step, _ | .sender, _
    | .closure, _ | .effectClosure, _ | .fresh, _ => exact Le.refl L
  · intro L k a
    match k, a with
    | .effect, [e] => exact addEffect_has _ L e
    | .effect, [] | .effect, _ :: _ :: _ | .spec, _ | .service, _ | .command, _ | .query, _ | .machine, _
    | .reaction, _ | .external, _ | .externalCommand, _ | .externalQuery, _ | .source, _ | .declared, _
    | .subscription, _ | .model, _ | .scope, _ | .values, _ | .create, _ | .response, _ | .scenario, _ | .step, _ | .sender, _
    | .closure, _ | .effectClosure, _ | .fresh, _ => trivial

end Layout

end Tazuna.Smt
