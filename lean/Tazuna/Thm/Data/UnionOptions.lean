import Tazuna.Data.UnionOptions

namespace Tazuna.Thm.Data.UnionOptions

open Tazuna.Data

def sampleOf : Value → Value
  | .null => .null
  | .bool _ => .bool false
  | .num _ => .num 0
  | .str _ => .str ""
  | .arr _ => .arr []
  | .obj _ => .obj []

theorem sampleOf_mem (v : Value) : sampleOf v ∈ typeSamples := by
  cases v <;> simp [sampleOf, typeSamples]

theorem fitsType_sampleOf (s v : Value) : fitsType s (sampleOf v) = fitsType s v := by
  have : typeNames (sampleOf v) = typeNames v := by cases v <;> rfl
  simp only [fitsType, this]

theorem disjoint_admits {p q x : Value} (h : disjoint (allowed p) (allowed q) = true) (hp : admits p x = true)
    (hq : admits q x = true) : False := by
  unfold admits at hp hq
  unfold disjoint at h
  split at h
  · rename_i xs ys hx hy
    rw [hx] at hp
    rw [hy] at hq
    simp only [Option.all_some] at hp hq
    have := (List.all_eq_true.mp h) x (List.contains_iff_mem.mp hp)
    simp only [Bool.not_eq_true', hq] at this; cases this
  · simp at h

theorem obj_of_objectTyped {s v : Value} (ho : objectTyped s = true) (ht : fitsType s v = true) :
    ∃ fields, v = .obj fields := by
  simp only [objectTyped, beq_iff_eq] at ho
  simp only [fitsType, ho] at ht
  cases v <;> simp_all [typeNames]

theorem mem_of_field? {fields : List (String × Value)} {k : String} {x : Value}
    (h : (Value.obj fields).field? k = some x) : (k, x) ∈ fields := by
  simp only [Value.field?, Option.map_eq_some_iff] at h
  obtain ⟨⟨k', x'⟩, hf, rfl⟩ := h
  have hk : k' = k := by simpa using List.find?_some hf
  subst hk
  exact List.mem_of_find?_eq_some hf

theorem fits_field {s : Value} {fields : List (String × Value)} {k : String} {x : Value}
    (h : fits s (.obj fields) = true) (hm : (k, x) ∈ fields) :
    (match propertyOf s k with
      | some p => admits p x
      | none => !closed s) = true := by
  simp only [fits, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2.1 (k, x) hm

theorem fits_required {s : Value} {fields : List (String × Value)} {k : String}
    (h : fits s (.obj fields) = true) (hk : k ∈ requiredOf s) : ∃ x, (k, x) ∈ fields := by
  simp only [fits, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h.2.2 k hk)
  exact ⟨x, mem_of_field? hx⟩

theorem misses_absurd {a b : Value} {fields : List (String × Value)} (hm : missesRequired a b = true)
    (ha : fits a (.obj fields) = true) (hb : fits b (.obj fields) = true) : False := by
  simp only [missesRequired, Bool.and_eq_true, List.any_eq_true, Option.isNone_iff_eq_none] at hm
  obtain ⟨hc, k, hk, hn⟩ := hm
  obtain ⟨x, hx⟩ := fits_required hb hk
  have := fits_field ha hx
  simp [hn, hc] at this

/-- No value fits two options that are `apart`, so the option that `fits` picks in a union whose options are all apart
is the only one that the value fits. -/
theorem apart_disjoint {a b v : Value} (h : apart a b = true) (ha : fits a v = true) (hb : fits b v = true) : False := by
  have hta : fitsType a v = true := by simp only [fits, Bool.and_eq_true] at ha; exact ha.1.1
  have htb : fitsType b v = true := by simp only [fits, Bool.and_eq_true] at hb; exact hb.1.1
  simp only [apart, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (ht | hd) | ⟨ho, (hp | hm) | hm⟩
  · have := (List.all_eq_true.mp ht) (sampleOf v) (sampleOf_mem v)
    simp [fitsType_sampleOf, hta, htb] at this
  · simp only [fits, Bool.and_eq_true] at ha hb
    exact disjoint_admits hd ha.1.2 hb.1.2
  · obtain ⟨fields, rfl⟩ : ∃ fields, v = .obj fields := by
      rcases ho with ho | ho
      · exact obj_of_objectTyped ho hta
      · exact obj_of_objectTyped ho htb
    simp only [List.any_eq_true, List.mem_append] at hp
    obtain ⟨k, hk, hd⟩ := hp
    obtain ⟨x, hx⟩ : ∃ x, (k, x) ∈ fields := by
      rcases hk with hk | hk
      · exact fits_required ha hk
      · exact fits_required hb hk
    have hfa := fits_field ha hx
    have hfb := fits_field hb hx
    split at hd
    · rename_i p q hpa hqb
      simp only [hpa] at hfa
      simp only [hqb] at hfb
      exact disjoint_admits hd hfa hfb
    · simp at hd
  · obtain ⟨fields, rfl⟩ : ∃ fields, v = .obj fields := by
      rcases ho with ho | ho
      · exact obj_of_objectTyped ho hta
      · exact obj_of_objectTyped ho htb
    exact misses_absurd hm ha hb
  · obtain ⟨fields, rfl⟩ : ∃ fields, v = .obj fields := by
      rcases ho with ho | ho
      · exact obj_of_objectTyped ho hta
      · exact obj_of_objectTyped ho htb
    exact misses_absurd hm hb ha

end Tazuna.Thm.Data.UnionOptions
