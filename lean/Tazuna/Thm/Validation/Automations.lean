import Tazuna.Validation.Automations

namespace Tazuna.Thm.Validation.Automations

open Tazuna.Data Tazuna.Spec Tazuna.Validation Tazuna.Validation.Automations

/-- Whether `b` receives an event that the command of `a` emits. -/
def Follows (s : Structure) (a b : Automation) : Prop :=
  b ∈ automations s ∧ ∃ e ∈ s.emitsOf a.command, sameRef b.receives e = true

inductive Chain (s : Structure) : Automation → Automation → Prop
  | single {a b : Automation} : Follows s a b → Chain s a b
  | head {a b c : Automation} : Follows s a b → Chain s b c → Chain s a c

theorem Chain.trans {s : Structure} {a b c : Automation} (hab : Chain s a b) (hbc : Chain s b c) : Chain s a c := by
  induction hab with
  | single h => exact .head h hbc
  | head h _ ih => exact .head h (ih hbc)

theorem Chain.mem {s : Structure} {a b : Automation} (h : Chain s a b) : b ∈ automations s := by
  induction h with
  | single h => exact h.1
  | head _ _ ih => exact ih

theorem index_injective (s : Structure) {a b : Automation} (ha : a ∈ automations s) (hb : b ∈ automations s)
    (h : a.index = b.index) : a = b := by
  simp only [automations, List.mem_map] at ha hb
  obtain ⟨⟨⟨r, rc, c⟩, i⟩, hi, rfl⟩ := ha
  obtain ⟨⟨⟨r', rc', c'⟩, i'⟩, hi', rfl⟩ := hb
  simp only at h
  subst h
  have h1 := List.mem_zipIdx_iff_getElem?.mp hi
  have h2 := List.mem_zipIdx_iff_getElem?.mp hi'
  simp only at h1 h2
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  rfl

/--
Whether, from `x`, a chain through automations whose indices are above `start` and in `rest` leads to index
`start`.
-/
inductive Leads (s : Structure) (start : Nat) : List Nat → Automation → Prop
  | last {rest : List Nat} {x b : Automation} : Follows s x b → b.index = start → Leads s start rest x
  | step {rest : List Nat} {x n : Automation} :
    Follows s x n → start < n.index → n.index ∈ rest → Leads s start rest n → Leads s start rest x

theorem Leads.erase {s : Structure} {start : Nat} {rest : List Nat} {x : Automation} (h : Leads s start rest x)
    (k : Nat) : Leads s start (rest.erase k) x ∨ ∃ z ∈ automations s, z.index = k ∧ Leads s start (rest.erase k) z := by
  induction h with
  | last hf hb => exact .inl (.last hf hb)
  | @step _ n hf hlt hmem _ ih =>
    rcases ih with ih | ih
    · by_cases hk : n.index = k
      · exact .inr ⟨n, hf.1, hk, ih⟩
      · exact .inl (.step hf hlt ((List.mem_erase_of_ne hk).mpr hmem) ih)
    · exact .inr ih

theorem walk_finds (s : Structure) (start : Nat) (rest : List Nat) (last : Automation) (chain : List Ref)
    (h : Leads s start rest last) : walk s (automations s) start rest last chain ≠ [] := by
  rw [walk]
  intro hnil
  rw [List.flatMap_eq_nil_iff] at hnil
  cases h with
  | @last _ b hf hb =>
    obtain ⟨hbm, e, he, hr⟩ := hf
    have := List.flatMap_eq_nil_iff.mp (hnil e he) b (List.mem_filter.mpr ⟨hbm, hr⟩)
    simp [hb] at this
  | @step _ n hf hlt hmem hn =>
    obtain ⟨hnm, e, he, hr⟩ := hf
    have := List.flatMap_eq_nil_iff.mp (hnil e he) n (List.mem_filter.mpr ⟨hnm, hr⟩)
    have hne : (n.index == start) = false := by simp only [beq_eq_false_iff_ne]; omega
    have hcond : start < n.index ∧ n.index ∈ rest := ⟨hlt, hmem⟩
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hcond, and_self, ↓reduceDIte] at this
    have hn' : Leads s start (rest.erase n.index) n := by
      rcases hn.erase n.index with h' | ⟨z, hz, hzk, h'⟩
      · exact h'
      · rwa [index_injective s hz hnm hzk] at h'
    exact walk_finds s start (rest.erase n.index) n (chain ++ [n.ref]) hn' this
termination_by rest.length
decreasing_by exact List.length_erase_of_mem hmem ▸ Nat.sub_lt (List.length_pos_of_mem hmem) Nat.one_pos

theorem walk_chain (s : Structure) (start : Nat) (rest : List Nat) (last : Automation) (chain found : List Ref)
    (h : found ∈ walk s (automations s) start rest last chain) :
    ∃ b ∈ automations s, b.index = start ∧ Chain s last b := by
  rw [walk] at h
  obtain ⟨e, he, h⟩ := List.mem_flatMap.mp h
  obtain ⟨n, hn, h⟩ := List.mem_flatMap.mp h
  obtain ⟨hnm, hr⟩ := List.mem_filter.mp hn
  have hf : Follows s last n := ⟨hnm, e, he, hr⟩
  by_cases hs : n.index = start
  · exact ⟨n, hnm, hs, .single hf⟩
  have hne : (n.index == start) = false := by simpa using hs
  by_cases hcond : start < n.index ∧ n.index ∈ rest
  · simp only [hne, Bool.false_eq_true, ↓reduceIte, hcond, and_self, ↓reduceDIte] at h
    obtain ⟨b, hb, hbs, hnb⟩ := walk_chain s start (rest.erase n.index) n (chain ++ [n.ref]) found h
    exact ⟨b, hb, hbs, .head hf hnb⟩
  · simp [hne, hcond] at h
termination_by rest.length
decreasing_by exact List.length_erase_of_mem hcond.2 ▸ Nat.sub_lt (List.length_pos_of_mem hcond.2) Nat.one_pos

/-- The theorem covers only automations that send a command to their own service (`automations`). -/
theorem no_automation_returns (s : Structure) : Automations.check s = [] ↔ ∀ a ∈ automations s, ¬ Chain s a a := by
  constructor
  · intro h a ha
    suffices ∀ k, ∀ m ∈ automations s, m.index = k → ¬ Chain s m m from this a.index a ha rfl
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
    intro m hm hk hcycle
    by_cases hlower : ∃ y ∈ automations s, y.index < k ∧ Chain s y y
    · obtain ⟨y, hy, hlt, hy'⟩ := hlower
      exact ih y.index hlt y hy rfl hy'
    have above : ∀ y, Chain s m y → Chain s y m → y = m ∨ m.index < y.index := by
      intro y hmy hym
      by_cases hy : y = m
      · exact .inl hy
      · have hne : y.index ≠ m.index := fun he => hy (index_injective s hmy.mem hm he)
        have : ¬ y.index < k := fun hlt => hlower ⟨y, hmy.mem, hlt, hym.trans hmy⟩
        exact .inr (by omega)
    let rest := ((automations s).map (·.index)).erase m.index
    have leads : ∀ x y, Chain s x y → y = m → (x = m ∨ Chain s m x) → Leads s m.index rest x := by
      intro x y hxy
      induction hxy with
      | single hf => intro hy _; exact .last hf (by rw [hy])
      | @head x z y hf hzy ih =>
        intro hy hon
        have hmz : Chain s m z := by
          rcases hon with rfl | hmx
          · exact .single hf
          · exact hmx.trans (.single hf)
        rcases above z hmz (hy ▸ hzy) with rfl | hlt
        · exact .last hf rfl
        · have hin : z.index ∈ rest := (List.mem_erase_of_ne (by omega)).mpr (List.mem_map.mpr ⟨z, hf.1, rfl⟩)
          exact .step hf hlt hin (ih hy (.inr hmz))
    apply walk_finds s m.index rest m [] (leads m m hcycle rfl (.inl rfl))
    have := List.flatMap_eq_nil_iff.mp h m hm
    simpa using this
  · intro h
    refine List.flatMap_eq_nil_iff.mpr fun a ha =>
      List.map_eq_nil_iff.mpr (List.eq_nil_iff_forall_not_mem.mpr fun found hw => ?_)
    obtain ⟨b, hb, hbi, hab⟩ := walk_chain s a.index _ a [] found hw
    exact h a ha (index_injective s hb ha hbi ▸ hab)

end Tazuna.Thm.Validation.Automations
