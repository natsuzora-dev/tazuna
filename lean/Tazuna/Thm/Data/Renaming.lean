import Tazuna.Data.Binding
import Tazuna.Thm.Data.List
import Tazuna.Thm.Guarantee

/-!
Explore compares two runs up to a renaming of their created keys (Data/Binding): a created key of one run may stand for
a created key of the other run in the same domain, one to one, and every other string stands for itself. `Renamed`
states that relation on values, comparing the elements of a bag and the fields of an object in any order, and this
module proves it an equivalence.

- Reflexive: every value renames to itself under the empty binding (renamed_refl).
- Symmetric: a renaming read backward is the inverse binding (renamed_symm).
- Transitive: two renamings in a row are their composition, which is again one to one (renamed_trans,
  compose_fst_nodup, compose_snd_nodup).

Symmetry and transitivity need the bindings consistent with one domain function `dom`: each pair binds values of the
domain that `dom` gives their strings, as Explore's bindings do, since a created key's domain is its entity.
-/

namespace Tazuna.Thm.Data.Renaming

open Tazuna.Data
open Tazuna.Thm.Data.List (lookup_of_mem mem_of_lookup)

/-- `b` renames `s` to `t`: they are a pair of `b`, or `s` is `t` and `b` binds it to nothing and nothing to it. -/
def Renames (b : List (Bound × Bound)) (s t : Bound) : Prop :=
  (s, t) ∈ b ∨ (s = t ∧ s ∉ b.map Prod.fst ∧ s ∉ b.map Prod.snd)

/-- The binding read backward. -/
def inverse (b : List (Bound × Bound)) : List (Bound × Bound) := b.map Prod.swap

/--
The binding that renames as `b` and then `c`: each pair of `b` followed by the pair of `c` from its value, or kept when
`c` leaves its value alone, then each pair of `c` whose value `b` leaves alone.
-/
def compose (b c : List (Bound × Bound)) : List (Bound × Bound) :=
  b.filterMap (fun p => match c.lookup p.2 with
    | some u => some (p.1, u)
    | none => if p.2 ∈ c.map Prod.snd then none else some p) ++
  c.filter fun p => p.1 ∉ b.map Prod.fst && p.1 ∉ b.map Prod.snd

/-- The string relation of a binding, with each string in the domain that `dom` gives the first. -/
def StrRenames (dom : String → String) (b : List (Bound × Bound)) (s t : String) : Prop :=
  Renames b (dom s, s) (dom s, t)

/-- Each pair of `b` binds values of the domains that `dom` gives their strings. -/
def Consistent (dom : String → String) (b : List (Bound × Bound)) : Prop :=
  ∀ p ∈ b, p.1.1 = dom p.1.2 ∧ p.2.1 = dom p.2.2

mutual

/--
`s` renames to `t` under the string relation `R`: key references as `R` relates them, leaves (strings too) equal,
arrays and runs element by element, and bags and objects after reordering the elements or fields of `t`. For objects
with distinct keys, as verify reads them, reordering the fields is what sameKeys and lookup compare.
-/
inductive Renamed (R : String → String → Prop) : CValue → CValue → Prop
  | ref {e e' s t : String} : R s t → Renamed R (.ref e s) (.ref e' t)
  | leaf {x : Value} : Renamed R (.leaf x) (.leaf x)
  | arr {xs ys : List CValue} : RenamedList R xs ys → Renamed R (.arr xs) (.arr ys)
  | runs {xs ys : List CValue} : RenamedList R xs ys → Renamed R (.runs xs) (.runs ys)
  | obj {fs gs gs' : List (String × CValue)} : RenamedFields R fs gs' → gs'.Perm gs → Renamed R (.obj fs) (.obj gs)
  | bag {xs ys ys' : List CValue} : RenamedList R xs ys' → ys'.Perm ys → Renamed R (.bag xs) (.bag ys)

inductive RenamedList (R : String → String → Prop) : List CValue → List CValue → Prop
  | nil : RenamedList R [] []
  | cons {x y : CValue} {xs ys : List CValue} : Renamed R x y → RenamedList R xs ys →
      RenamedList R (x :: xs) (y :: ys)

inductive RenamedFields (R : String → String → Prop) : List (String × CValue) → List (String × CValue) → Prop
  | nil : RenamedFields R [] []
  | cons {k : String} {x y : CValue} {fs gs : List (String × CValue)} : Renamed R x y → RenamedFields R fs gs →
      RenamedFields R ((k, x) :: fs) ((k, y) :: gs)

end

/-! ## Reordering -/

theorem RenamedList.perm {R : String → String → Prop} {ys ys' zs : List CValue} (h : RenamedList R ys zs)
    (hp : ys'.Perm ys) : ∃ zs', zs'.Perm zs ∧ RenamedList R ys' zs' := by
  induction hp generalizing zs with
  | nil => exact ⟨zs, .refl _, h⟩
  | cons x _ ih =>
    cases h with
    | cons hx hl =>
      obtain ⟨zs', hp', hl'⟩ := ih hl
      exact ⟨_, hp'.cons _, .cons hx hl'⟩
  | swap x y l =>
    cases h with
    | cons hx hl =>
      cases hl with
      | cons hy hl => exact ⟨_, .swap _ _ _, .cons hy (.cons hx hl)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨zs₁, hp₁, h₁⟩ := ih₂ h
    obtain ⟨zs₂, hp₂, h₂⟩ := ih₁ h₁
    exact ⟨zs₂, hp₂.trans hp₁, h₂⟩

theorem RenamedFields.perm {R : String → String → Prop} {gs gs' hs : List (String × CValue)}
    (h : RenamedFields R gs hs) (hp : gs'.Perm gs) : ∃ hs', hs'.Perm hs ∧ RenamedFields R gs' hs' := by
  induction hp generalizing hs with
  | nil => exact ⟨hs, .refl _, h⟩
  | cons x _ ih =>
    cases h with
    | cons hx hl =>
      obtain ⟨hs', hp', hl'⟩ := ih hl
      exact ⟨_, hp'.cons _, .cons hx hl'⟩
  | swap x y l =>
    cases h with
    | cons hx hl =>
      cases hl with
      | cons hy hl => exact ⟨_, .swap _ _ _, .cons hy (.cons hx hl)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨hs₁, hp₁, h₁⟩ := ih₂ h
    obtain ⟨hs₂, hp₂, h₂⟩ := ih₁ h₁
    exact ⟨hs₂, hp₂.trans hp₁, h₂⟩

/-! ## The value relation -/

mutual

theorem Renamed.mono {R S : String → String → Prop} (hRS : ∀ s t, R s t → S s t) :
    {s t : CValue} → Renamed R s t → Renamed S s t
  | _, _, .ref h => .ref (hRS _ _ h)
  | _, _, .leaf => .leaf
  | _, _, .arr h => .arr (RenamedList.mono hRS h)
  | _, _, .runs h => .runs (RenamedList.mono hRS h)
  | _, _, .obj h hp => .obj (RenamedFields.mono hRS h) hp
  | _, _, .bag h hp => .bag (RenamedList.mono hRS h) hp

theorem RenamedList.mono {R S : String → String → Prop} (hRS : ∀ s t, R s t → S s t) :
    {xs ys : List CValue} → RenamedList R xs ys → RenamedList S xs ys
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons (Renamed.mono hRS h) (RenamedList.mono hRS hl)

theorem RenamedFields.mono {R S : String → String → Prop} (hRS : ∀ s t, R s t → S s t) :
    {fs gs : List (String × CValue)} → RenamedFields R fs gs → RenamedFields S fs gs
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons (Renamed.mono hRS h) (RenamedFields.mono hRS hl)

end

mutual

theorem Renamed.refl {R : String → String → Prop} (hR : ∀ s, R s s) : (s : CValue) → Renamed R s s
  | .leaf _ => .leaf
  | .ref _ s => .ref (hR s)
  | .arr xs => .arr (RenamedList.refl hR xs)
  | .runs xs => .runs (RenamedList.refl hR xs)
  | .obj fs => .obj (RenamedFields.refl hR fs) (.refl _)
  | .bag xs => .bag (RenamedList.refl hR xs) (.refl _)

theorem RenamedList.refl {R : String → String → Prop} (hR : ∀ s, R s s) : (xs : List CValue) → RenamedList R xs xs
  | [] => .nil
  | x :: xs => .cons (Renamed.refl hR x) (RenamedList.refl hR xs)

theorem RenamedFields.refl {R : String → String → Prop} (hR : ∀ s, R s s) :
    (fs : List (String × CValue)) → RenamedFields R fs fs
  | [] => .nil
  | (_, x) :: fs => .cons (Renamed.refl hR x) (RenamedFields.refl hR fs)

end

mutual

theorem Renamed.symm {R : String → String → Prop} : {s t : CValue} → Renamed R s t → Renamed (flip R) t s
  | _, _, .ref h => .ref h
  | _, _, .leaf => .leaf
  | _, _, .arr h => .arr (RenamedList.symm h)
  | _, _, .runs h => .runs (RenamedList.symm h)
  | _, _, .obj h hp =>
    have ⟨_, hp', h'⟩ := RenamedFields.perm (RenamedFields.symm h) hp.symm
    .obj h' hp'
  | _, _, .bag h hp =>
    have ⟨_, hp', h'⟩ := RenamedList.perm (RenamedList.symm h) hp.symm
    .bag h' hp'

theorem RenamedList.symm {R : String → String → Prop} :
    {xs ys : List CValue} → RenamedList R xs ys → RenamedList (flip R) ys xs
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons (Renamed.symm h) (RenamedList.symm hl)

theorem RenamedFields.symm {R : String → String → Prop} :
    {fs gs : List (String × CValue)} → RenamedFields R fs gs → RenamedFields (flip R) gs fs
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons (Renamed.symm h) (RenamedFields.symm hl)

end

/-- `R` and then `S`. -/
def Comp (R S : String → String → Prop) (s u : String) : Prop := ∃ t, R s t ∧ S t u

mutual

theorem Renamed.trans {R S : String → String → Prop} :
    {s t u : CValue} → Renamed R s t → Renamed S t u → Renamed (Comp R S) s u
  | _, _, _, .ref h, .ref h' => .ref ⟨_, h, h'⟩
  | _, _, _, .leaf, .leaf => .leaf
  | _, _, _, .arr h, .arr h' => .arr (RenamedList.trans h h')
  | _, _, _, .runs h, .runs h' => .runs (RenamedList.trans h h')
  | _, _, _, .obj h hp, .obj h' hp' =>
    have ⟨_, hph, hh⟩ := RenamedFields.perm h' hp
    .obj (RenamedFields.trans h hh) (hph.trans hp')
  | _, _, _, .bag h hp, .bag h' hp' =>
    have ⟨_, hpz, hz⟩ := RenamedList.perm h' hp
    .bag (RenamedList.trans h hz) (hpz.trans hp')

theorem RenamedList.trans {R S : String → String → Prop} :
    {xs ys zs : List CValue} → RenamedList R xs ys → RenamedList S ys zs → RenamedList (Comp R S) xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hl, .cons h' hl' => .cons (Renamed.trans h h') (RenamedList.trans hl hl')

theorem RenamedFields.trans {R S : String → String → Prop} :
    {fs gs hs : List (String × CValue)} → RenamedFields R fs gs → RenamedFields S gs hs →
      RenamedFields (Comp R S) fs hs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hl, .cons h' hl' => .cons (Renamed.trans h h') (RenamedFields.trans hl hl')

end

/-! ## Bindings -/

theorem renames_nil {s t : Bound} : Renames [] s t ↔ s = t := by
  simp [Renames]

theorem inverse_map_fst (b : List (Bound × Bound)) : (inverse b).map Prod.fst = b.map Prod.snd := by
  simp [inverse, List.map_map, Function.comp_def]

theorem inverse_map_snd (b : List (Bound × Bound)) : (inverse b).map Prod.snd = b.map Prod.fst := by
  simp [inverse, List.map_map, Function.comp_def]

theorem renames_inverse {b : List (Bound × Bound)} {s t : Bound} : Renames b s t → Renames (inverse b) t s := by
  intro h
  rcases h with h | ⟨rfl, h₁, h₂⟩
  · exact .inl (List.mem_map.mpr ⟨(s, t), h, rfl⟩)
  · exact .inr ⟨rfl, by rw [inverse_map_fst]; exact h₂, by rw [inverse_map_snd]; exact h₁⟩

theorem lookup_none {c : List (Bound × Bound)} {t : Bound} (h : t ∉ c.map Prod.fst) : c.lookup t = none := by
  cases hl : c.lookup t with
  | none => rfl
  | some u => exact absurd (List.mem_map.mpr ⟨(t, u), mem_of_lookup hl, rfl⟩) h

theorem mem_compose_left {b c : List (Bound × Bound)} {s t : Bound} :
    (s, t) ∈ compose b c ↔
      (∃ m, (s, m) ∈ b ∧ c.lookup m = some t) ∨ ((s, t) ∈ b ∧ c.lookup t = none ∧ t ∉ c.map Prod.snd) ∨
        ((s, t) ∈ c ∧ s ∉ b.map Prod.fst ∧ s ∉ b.map Prod.snd) := by
  simp only [compose, List.mem_append, List.mem_filterMap, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro (⟨⟨a, m⟩, ha, hm⟩ | h)
    · dsimp only at hm
      split at hm
      · rename_i u hu; cases hm; exact .inl ⟨m, ha, hu⟩
      · rename_i hu
        split at hm
        · cases hm
        · rename_i hs; cases hm; exact .inr (.inl ⟨ha, hu, hs⟩)
    · exact .inr (.inr ⟨h.1, h.2.1, h.2.2⟩)
  · rintro (⟨m, ha, hu⟩ | ⟨ha, hu, hs⟩ | h)
    · exact .inl ⟨(s, m), ha, by simp [hu]⟩
    · exact .inl ⟨(s, t), ha, by simp [hu, hs]⟩
    · exact .inr ⟨h.1, h.2.1, h.2.2⟩

theorem renames_compose {b c : List (Bound × Bound)} (hc : (c.map Prod.fst).Nodup) {s t u : Bound}
    (h₁ : Renames b s t) (h₂ : Renames c t u) : Renames (compose b c) s u := by
  rcases h₁ with h₁ | ⟨rfl, hs₁, hs₂⟩ <;> rcases h₂ with h₂ | ⟨rfl, ht₁, ht₂⟩
  · exact .inl (mem_compose_left.mpr (.inl ⟨t, h₁, lookup_of_mem hc h₂⟩))
  · exact .inl (mem_compose_left.mpr (.inr (.inl ⟨h₁, lookup_none ht₁, ht₂⟩)))
  · exact .inl (mem_compose_left.mpr (.inr (.inr ⟨h₂, hs₁, hs₂⟩)))
  · refine .inr ⟨rfl, ?_, ?_⟩
    · rintro hm
      obtain ⟨⟨a, x⟩, hp, rfl⟩ := List.mem_map.mp hm
      rcases mem_compose_left.mp hp with ⟨m, ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩
      · exact hs₁ (List.mem_map.mpr ⟨_, ha, rfl⟩)
      · exact hs₁ (List.mem_map.mpr ⟨_, ha, rfl⟩)
      · exact ht₁ (List.mem_map.mpr ⟨_, ha, rfl⟩)
    · rintro hm
      obtain ⟨⟨a, x⟩, hp, rfl⟩ := List.mem_map.mp hm
      rcases mem_compose_left.mp hp with ⟨m, _, hu⟩ | ⟨ha, _⟩ | ⟨ha, _⟩
      · exact ht₂ (List.mem_map.mpr ⟨_, mem_of_lookup hu, rfl⟩)
      · exact hs₂ (List.mem_map.mpr ⟨_, ha, rfl⟩)
      · exact ht₂ (List.mem_map.mpr ⟨_, ha, rfl⟩)

/-! ## One to one -/

/-- The first part of compose, from the pairs of `b`. -/
def composeLeft (b c : List (Bound × Bound)) : List (Bound × Bound) :=
  b.filterMap fun p => match c.lookup p.2 with
    | some u => some (p.1, u)
    | none => if p.2 ∈ c.map Prod.snd then none else some p

theorem compose_eq (b c : List (Bound × Bound)) :
    compose b c = composeLeft b c ++ c.filter fun p => p.1 ∉ b.map Prod.fst && p.1 ∉ b.map Prod.snd := rfl

theorem composeLeft_cons (p : Bound × Bound) (b c : List (Bound × Bound)) :
    composeLeft (p :: b) c = ((match c.lookup p.2 with
      | some u => some (p.1, u)
      | none => if p.2 ∈ c.map Prod.snd then none else some p).toList) ++ composeLeft b c := by
  simp only [composeLeft, List.filterMap_cons]
  split <;> simp_all

theorem composeLeft_fst_sublist (b c : List (Bound × Bound)) :
    ((composeLeft b c).map Prod.fst).Sublist (b.map Prod.fst) := by
  induction b with
  | nil => simp [composeLeft]
  | cons p b ih =>
    rw [composeLeft_cons, List.map_append, List.map_cons]
    split
    · simpa using ih.cons_cons p.1
    · split
      · simpa using ih.cons p.1
      · simpa using ih.cons_cons p.1

@[guarantee] theorem compose_fst_nodup {b c : List (Bound × Bound)} (hb : (b.map Prod.fst).Nodup)
    (hc : (c.map Prod.fst).Nodup) : ((compose b c).map Prod.fst).Nodup := by
  rw [compose_eq, List.map_append, List.nodup_append]
  refine ⟨hb.sublist (composeLeft_fst_sublist b c), hc.sublist ((List.filter_sublist).map _), ?_⟩
  intro x hx y hy hxy
  subst hxy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact hp.2.1 ((composeLeft_fst_sublist b c).subset hx)

/-- The value that compose gives a pair `p` of `b` in composeLeft. -/
theorem mem_composeLeft_snd {b c : List (Bound × Bound)} {x : Bound} (h : x ∈ (composeLeft b c).map Prod.snd) :
    ∃ p ∈ b, ((p.2, x) ∈ c) ∨ (x = p.2 ∧ x ∉ c.map Prod.snd) := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  obtain ⟨p, hp, hf⟩ := List.mem_filterMap.mp hq
  refine ⟨p, hp, ?_⟩
  split at hf
  · rename_i u hu; cases hf; exact .inl (mem_of_lookup hu)
  · split at hf
    · cases hf
    · rename_i hs; cases hf; exact .inr ⟨rfl, hs⟩

theorem composeLeft_snd_nodup {b c : List (Bound × Bound)} (hb : (b.map Prod.snd).Nodup)
    (hc : (c.map Prod.snd).Nodup) : ((composeLeft b c).map Prod.snd).Nodup := by
  induction b with
  | nil => simp [composeLeft]
  | cons p b ih =>
    simp only [List.map_cons, List.nodup_cons] at hb
    rw [composeLeft_cons, List.map_append, List.nodup_append]
    refine ⟨?_, ih hb.2, ?_⟩
    · split <;> (try split) <;> simp
    · intro x hx y hy hxy
      subst hxy
      obtain ⟨q, hq, hqx⟩ := mem_composeLeft_snd hy
      have hq2 : q.2 ≠ p.2 := fun e => hb.1 (List.mem_map.mpr ⟨q, hq, e⟩)
      split at hx
      · rename_i u hu
        simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at hx
        subst hx
        have hpu := mem_of_lookup hu
        rcases hqx with hqx | ⟨rfl, hs⟩
        · exact hq2 (congrArg Prod.fst (eq_of_map_nodup hc hqx hpu rfl))
        · exact hs (List.mem_map.mpr ⟨_, hpu, rfl⟩)
      · rename_i hu
        split at hx
        · simp at hx
        · rename_i hs
          simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at hx
          subst hx
          rcases hqx with hqx | ⟨e, _⟩
          · exact hs (List.mem_map.mpr ⟨_, hqx, rfl⟩)
          · exact hq2 e.symm

@[guarantee] theorem compose_snd_nodup {b c : List (Bound × Bound)} (hb : (b.map Prod.snd).Nodup)
    (hc : (c.map Prod.snd).Nodup) : ((compose b c).map Prod.snd).Nodup := by
  rw [compose_eq, List.map_append, List.nodup_append]
  refine ⟨composeLeft_snd_nodup hb hc, hc.sublist ((List.filter_sublist).map _), ?_⟩
  intro x hx y hy hxy
  subst hxy
  obtain ⟨r, hr, hrx⟩ := List.mem_map.mp hy
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨p, hp, hpx⟩ := mem_composeLeft_snd hx
  rcases hpx with hpx | ⟨_, hs⟩
  · have := eq_of_map_nodup hc hr.1 hpx hrx
    exact hr.2.2 (List.mem_map.mpr ⟨p, hp, (congrArg Prod.fst this).symm⟩)
  · exact hs (List.mem_map.mpr ⟨r, hr.1, hrx⟩)

/-! ## Strings in their domains -/

theorem domain_of_renames {dom : String → String} {b : List (Bound × Bound)} (hb : Consistent dom b) {s t : String}
    (h : StrRenames dom b s t) : dom t = dom s := by
  rcases h with h | ⟨h, _⟩
  · exact ((hb _ h).2).symm
  · cases h; rfl

theorem strRenames_inverse {dom : String → String} {b : List (Bound × Bound)} (hb : Consistent dom b) {s t : String}
    (h : StrRenames dom b s t) : StrRenames dom (inverse b) t s := by
  unfold StrRenames
  rw [domain_of_renames hb h]
  exact renames_inverse h

theorem strRenames_compose {dom : String → String} {b c : List (Bound × Bound)} (hb : Consistent dom b)
    (hc : (c.map Prod.fst).Nodup) {s t u : String} (h₁ : StrRenames dom b s t) (h₂ : StrRenames dom c t u) :
    StrRenames dom (compose b c) s u := by
  unfold StrRenames at h₂
  rw [domain_of_renames hb h₁] at h₂
  exact renames_compose hc h₁ h₂

/-! ## The equivalence -/

/-- Every value renames to itself under the empty binding. -/
@[guarantee] theorem renamed_refl (dom : String → String) (v : CValue) : Renamed (StrRenames dom []) v v :=
  Renamed.refl (fun _ => renames_nil.mpr rfl) v

/-- A renaming under a consistent binding reads backward under the inverse binding. -/
@[guarantee] theorem renamed_symm {dom : String → String} {b : List (Bound × Bound)} (hb : Consistent dom b) {s t : CValue}
    (h : Renamed (StrRenames dom b) s t) : Renamed (StrRenames dom (inverse b)) t s :=
  Renamed.mono (fun _ _ h => strRenames_inverse hb h) (Renamed.symm h)

/--
Two renamings in a row, the first under a consistent binding and the second under a binding that binds each value at
most once, are one renaming under their composition.
-/
@[guarantee] theorem renamed_trans {dom : String → String} {b c : List (Bound × Bound)} (hb : Consistent dom b)
    (hc : (c.map Prod.fst).Nodup) {s t u : CValue} (h₁ : Renamed (StrRenames dom b) s t)
    (h₂ : Renamed (StrRenames dom c) t u) : Renamed (StrRenames dom (compose b c)) s u :=
  Renamed.mono (fun _ _ ⟨_, h, h'⟩ => strRenames_compose hb hc h h') (Renamed.trans h₁ h₂)

end Tazuna.Thm.Data.Renaming
