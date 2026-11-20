import Tazuna.Service.Basic

namespace Tazuna.Thm.Service.Basic

open Tazuna.Service

theorem requirements_ofStructure (j : Spec.Structure) (service : String) :
    (ofStructure (m := Id) j service).run.requirements = requirementsOf j service := rfl

theorem lookup_of_mem {β : Type} {l : List (String × β)} {a : String} {b : β} (h : (a, b) ∈ l) :
    ∃ b', l.lookup a = some b' := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : a = k
    · subst hk
      exact ⟨v, by simp [List.lookup]⟩
    · rcases List.mem_cons.mp h with h | h
      · cases h
        exact absurd rfl hk
      · obtain ⟨b', hb⟩ := ih h
        have hf : (a == k) = false := by simp [hk]
        exact ⟨b', by simp [List.lookup, hf, hb]⟩

/--
Every own command, query, and screen of a service has requirements, so the requirements lookups that the run makes
through expectFound find them.
-/
theorem requirements_lookup (j : Spec.Structure) (service : String) (d : Spec.Definition) (hd : d ∈ j.definitions)
    (hs : d.service = service) (hk : d.body matches .command _ | .query _ | .screen _) :
    ∃ rq, (ofStructure (m := Id) j service).run.requirements.lookup d.name = some rq := by
  rw [requirements_ofStructure]
  unfold requirementsOf
  generalize j.definitions = ds at hd
  induction ds with
  | nil => cases hd
  | cons x xs ih =>
    rcases List.mem_cons.mp hd with rfl | h
    · clear ih
      obtain ⟨_, _, body⟩ := d
      subst hs
      cases body <;> simp_all
    · obtain ⟨rq, hrq⟩ := ih h
      simp only [List.filterMap_cons]
      split
      · exact ⟨rq, hrq⟩
      · next p _ =>
        obtain ⟨k, v⟩ := p
        by_cases hn : d.name = k
        · exact ⟨v, by simp [List.lookup, hn]⟩
        · have hf : (d.name == k) = false := by simp [hn]
          exact ⟨rq, by simp only [List.lookup, hf]; exact hrq⟩

end Tazuna.Thm.Service.Basic
