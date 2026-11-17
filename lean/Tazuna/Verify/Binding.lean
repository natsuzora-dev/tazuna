/-!
The binding of snapshot values to implementation values that verify builds while it compares.

- A slot holds snapshot values and as many implementation values. A slot of one value on each side binds the two. A
  larger slot says that each of its snapshot values stands for one of its implementation values, which one is not known
  yet (a group whose lines compare equal under every choice).
- No value is in two slots, on either side, so each way of choosing inside the slots binds one-to-one.
- Binding a string only refines the slots: a bound pair stays, and a larger slot only splits.
-/

namespace Tazuna.Verify

/-- Snapshot values and the implementation values that they stand for, in some order. -/
abbrev Slot := List String × List String

def domainOf (slots : List Slot) : List String := slots.flatMap (·.1)

def imageOf (slots : List Slot) : List String := slots.flatMap (·.2)

/-- No value is in two slots, on either side, and each slot holds as many values on each side. -/
def Valid (slots : List Slot) : Prop :=
  (domainOf slots).Nodup ∧ (imageOf slots).Nodup ∧ ∀ k ∈ slots, k.1.length = k.2.length

instance (slots : List Slot) : Decidable (Valid slots) := by unfold Valid; infer_instance

structure Binding where
  slots : List Slot
  valid : Valid slots

/-- Each value of each slot of `a` is in a slot of `b` that holds only values of the slot of `a`, on both sides. -/
def Refines (a b : List Slot) : Prop :=
  ∀ k ∈ a, ∀ s ∈ k.1, ∃ k' ∈ b, s ∈ k'.1 ∧ (∀ x ∈ k'.1, x ∈ k.1) ∧ (∀ y ∈ k'.2, y ∈ k.2)

instance (a b : List Slot) : Decidable (Refines a b) :=
  decidable_of_iff
    (a.all fun k => k.1.all fun s => b.any fun k' => s ∈ k'.1 && k'.1.all (· ∈ k.1) && k'.2.all (· ∈ k.2))
    (by simp [Refines, List.all_eq_true, List.any_eq_true, and_assoc])

/-- `b'` keeps what `b` binds: each pair bound in `b` stays, and each slot only splits. -/
def Binding.Extends (b b' : Binding) : Prop := Refines b.slots b'.slots

theorem Refines.refl (a : List Slot) : Refines a a :=
  fun k hk _ hs => ⟨k, hk, hs, fun _ h => h, fun _ h => h⟩

theorem Refines.trans {a b c : List Slot} (hab : Refines a b) (hbc : Refines b c) : Refines a c := by
  intro k hk s hs
  obtain ⟨k', hk', hs', h1, h2⟩ := hab k hk s hs
  obtain ⟨k'', hk'', hs'', h1', h2'⟩ := hbc k' hk' s hs'
  exact ⟨k'', hk'', hs'', fun x hx => h1 x (h1' x hx), fun y hy => h2 y (h2' y hy)⟩

theorem Binding.Extends.refl (b : Binding) : b.Extends b := Refines.refl _

theorem Binding.Extends.trans {a b c : Binding} (hab : a.Extends b) (hbc : b.Extends c) : a.Extends c :=
  Refines.trans hab hbc

def Binding.empty : Binding := ⟨[], by simp [Valid, domainOf, imageOf]⟩

/-- The pairs of the binding, choosing in each slot by position. -/
def Binding.pairs (b : Binding) : List (String × String) := b.slots.flatMap fun k => k.1.zip k.2

/--
The slots with snapshot value `s`, which a slot holds, standing for `t`: `t` must be in that slot. A larger slot splits
into the pair and the rest.
-/
def resolveIn (s t : String) : List Slot → Option (List Slot)
  | [] => none
  | k :: ks =>
    if s ∈ k.1 then
      if t ∈ k.2 then
        if k.1.length = 1 then some (k :: ks) else some (([s], [t]) :: (k.1.erase s, k.2.erase t) :: ks)
      else none
    else (resolveIn s t ks).map (k :: ·)

theorem resolveIn_spec {s t : String} : ∀ {slots slots' : List Slot}, resolveIn s t slots = some slots' →
    (domainOf slots').Perm (domainOf slots) ∧ (imageOf slots').Perm (imageOf slots) ∧
      ((∀ k ∈ slots, k.1.length = k.2.length) → ∀ k ∈ slots', k.1.length = k.2.length) ∧ Refines slots slots'
  | [], _, h => by simp [resolveIn] at h
  | k :: ks, slots', h => by
    unfold resolveIn at h
    by_cases hs : s ∈ k.1
    · by_cases ht : t ∈ k.2
      · by_cases h1 : k.1.length = 1
        · simp only [hs, ht, h1, ite_true, Option.some.injEq] at h
          subst h
          exact ⟨List.Perm.refl _, List.Perm.refl _, id, Refines.refl _⟩
        · simp only [hs, ht, h1, ite_true, ite_false, Option.some.injEq] at h
          subst h
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [domainOf, List.flatMap_cons, List.cons_append]
            exact ((List.perm_cons_erase hs).append_right _).symm
          · simp only [imageOf, List.flatMap_cons, List.cons_append]
            exact ((List.perm_cons_erase ht).append_right _).symm
          · intro hl x hx
            have hk := hl k (List.mem_cons_self ..)
            simp only [List.mem_cons] at hx
            rcases hx with rfl | rfl | hx
            · rfl
            · simp [List.length_erase_of_mem hs, List.length_erase_of_mem ht, hk]
            · exact hl x (List.mem_cons_of_mem _ hx)
          · intro x hx u hu
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · by_cases e : u = s
              · subst e
                exact ⟨([u], [t]), List.mem_cons_self .., List.mem_singleton_self _,
                  fun y hy => by simp at hy; subst hy; exact hs,
                  fun y hy => by simp at hy; subst hy; exact ht⟩
              · exact ⟨(x.1.erase s, x.2.erase t), List.mem_cons_of_mem _ (List.mem_cons_self ..),
                  (List.mem_erase_of_ne e).mpr hu, fun y hy => List.mem_of_mem_erase hy,
                  fun y hy => List.mem_of_mem_erase hy⟩
            · exact ⟨x, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx), hu, fun _ h => h, fun _ h => h⟩
      · simp [hs, ht] at h
    · simp only [hs, ite_false, Option.map_eq_some_iff] at h
      obtain ⟨rest, hr, rfl⟩ := h
      obtain ⟨hd, hi, hl, hrf⟩ := resolveIn_spec hr
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [domainOf, List.flatMap_cons] at hd ⊢; exact hd.append_left _
      · simp only [imageOf, List.flatMap_cons] at hi ⊢; exact hi.append_left _
      · intro hl' x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hl' x (List.mem_cons_self ..)
        · exact hl (fun y hy => hl' y (List.mem_cons_of_mem _ hy)) x hx
      · intro x hx u hu
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨x, List.mem_cons_self .., hu, fun _ h => h, fun _ h => h⟩
        · obtain ⟨k', hk', h1, h2, h3⟩ := hrf x hx u hu
          exact ⟨k', List.mem_cons_of_mem _ hk', h1, h2, h3⟩

theorem valid_append {slots : List Slot} {s t : String} (h : Valid slots) (hs : s ∉ domainOf slots)
    (ht : t ∉ imageOf slots) : Valid (slots ++ [([s], [t])]) := by
  obtain ⟨hd, hi, hl⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [domainOf, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hd hs ⊢
    exact List.nodup_append.mpr ⟨hd, by simp, fun a ha b hb e => by
      simp at hb; subst hb; subst e; exact hs ha⟩
  · simp only [imageOf, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hi ht ⊢
    exact List.nodup_append.mpr ⟨hi, by simp, fun a ha b hb e => by
      simp at hb; subst hb; subst e; exact ht ha⟩
  · intro k hk
    simp only [List.mem_append, List.mem_singleton] at hk
    rcases hk with hk | rfl
    · exact hl k hk
    · rfl

theorem refines_append (slots extra : List Slot) : Refines slots (slots ++ extra) :=
  fun k hk _ hs => ⟨k, List.mem_append_left _ hk, hs, fun _ h => h, fun _ h => h⟩

/--
The binding with snapshot string `s` standing for implementation string `t`. A bound `s` must stand for `t`, and an `s`
in a larger slot binds to a `t` of that slot. Any other `s` binds when it is fresh or equals `t`, unless `t` already
stands for a value.
-/
def Binding.bindString (fresh : List String) (b : Binding) (s t : String) : Option { b' : Binding // b.Extends b' } :=
  if hs : s ∈ domainOf b.slots then
    match h : resolveIn s t b.slots with
    | some slots' =>
      let r := resolveIn_spec h
      some ⟨⟨slots', r.1.nodup_iff.mpr b.valid.1, r.2.1.nodup_iff.mpr b.valid.2.1, r.2.2.1 b.valid.2.2⟩, r.2.2.2⟩
    | none => none
  else if ht : t ∉ imageOf b.slots then
    if fresh.contains s || s == t then
      some ⟨⟨b.slots ++ [([s], [t])], valid_append b.valid hs ht⟩, refines_append _ _⟩
    else none
  else none

/-- The slots with `slots'` in place of `b`'s slots, when they are valid and refine `b`'s. -/
def Binding.refine (b : Binding) (slots' : List Slot) : Option { b' : Binding // b.Extends b' } :=
  if h : Valid slots' ∧ Refines b.slots slots' then some ⟨⟨slots', h.1⟩, h.2⟩ else none

theorem map_fst_pairs (slots : List Slot) (hl : ∀ k ∈ slots, k.1.length = k.2.length) :
    (slots.flatMap fun k => k.1.zip k.2).map Prod.fst = domainOf slots := by
  induction slots with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.flatMap_cons, List.map_append, domainOf] at ih ⊢
    rw [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)),
      List.map_fst_zip (Nat.le_of_eq (hl k (List.mem_cons_self ..)))]

theorem map_snd_pairs (slots : List Slot) (hl : ∀ k ∈ slots, k.1.length = k.2.length) :
    (slots.flatMap fun k => k.1.zip k.2).map Prod.snd = imageOf slots := by
  induction slots with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.flatMap_cons, List.map_append, imageOf] at ih ⊢
    rw [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)),
      List.map_snd_zip (Nat.le_of_eq (hl k (List.mem_cons_self ..)).symm)]

theorem eq_of_map_nodup {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup → ∀ {p q : α}, p ∈ l → q ∈ l →
    f p = f q → p = q
  | [], _, _, _, hp, _, _ => by simp at hp
  | a :: l, h, p, q, hp, hq, e => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    simp only [List.mem_cons] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · exact absurd e.symm (h.1 q hq)
    · exact absurd e (h.1 p hp)
    · exact eq_of_map_nodup h.2 hp hq e

/-- No string of the pairs is bound to two strings, and no two strings to one. -/
def OneToOne (bs : List (String × String)) : Prop := ∀ p ∈ bs, ∀ q ∈ bs, (p.1 = q.1 ↔ p.2 = q.2)

theorem Binding.pairs_oneToOne (b : Binding) : OneToOne b.pairs := by
  obtain ⟨hd, hi, hl⟩ := b.valid
  have hf : (b.pairs.map Prod.fst).Nodup := by unfold Binding.pairs; rw [map_fst_pairs _ hl]; exact hd
  have hs : (b.pairs.map Prod.snd).Nodup := by unfold Binding.pairs; rw [map_snd_pairs _ hl]; exact hi
  intro p hp q hq
  constructor
  · intro e; rw [eq_of_map_nodup hf hp hq e]
  · intro e; rw [eq_of_map_nodup hs hp hq e]

end Tazuna.Verify
