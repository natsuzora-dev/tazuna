import Tazuna.Sim.Run
import Tazuna.Thm.Verify.Pairing
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Sim.Given

open Tazuna.Data Tazuna.Service Tazuna.Sim
open Tazuna.Scenario (GivenRecord PeerEntry)

variable {fsOf : String → Functions Id}

/-- No two of the records share an entity and a key. -/
def RecordsDistinct (rs : List GivenRecord) : Prop := (rs.map fun g => (g.entity, g.key)).Nodup

theorem keyBefore_trans {a b c : Option String} (h₁ : keyBefore a b = true) (h₂ : keyBefore b c = true) :
    keyBefore a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [keyBefore]
  exact String.le_trans h₁ h₂

theorem keyBefore_total (a b : Option String) : (keyBefore a b || keyBefore b a) = true := by
  cases a <;> cases b <;> simp [keyBefore, String.le_total]

theorem keyBefore_antisymm {a b : Option String} (h₁ : keyBefore a b = true) (h₂ : keyBefore b a = true) : a = b := by
  cases a <;> cases b <;> simp_all [keyBefore]
  exact String.le_antisymm h₁ h₂

theorem before_trans (a b c : GivenRecord) (h₁ : recordBefore a b = true) (h₂ : recordBefore b c = true) :
    recordBefore a c = true := by
  unfold recordBefore at *
  by_cases hab : a.entity = b.entity
  · by_cases hbc : b.entity = c.entity
    · simp only [hab, hbc, ite_true] at h₁ h₂ ⊢; exact keyBefore_trans h₁ h₂
    · simp only [hab, hbc, ite_false, decide_eq_true_eq] at h₁ h₂ ⊢; exact h₂
  · simp only [hab, ite_false, decide_eq_true_eq] at h₁
    by_cases hbc : b.entity = c.entity
    · rw [← hbc]; simp only [hab, ite_false, decide_eq_true_eq]; exact h₁
    · simp only [hbc, ite_false, decide_eq_true_eq] at h₂
      by_cases hac : a.entity = c.entity
      · exact absurd (String.le_antisymm h₁ (hac ▸ h₂)) hab
      · simp only [hac, ite_false, decide_eq_true_eq]; exact String.le_trans h₁ h₂

theorem before_total (a b : GivenRecord) : (recordBefore a b || recordBefore b a) = true := by
  unfold recordBefore
  by_cases h : a.entity = b.entity
  · simp only [h, ite_true]; exact keyBefore_total _ _
  · simp only [h, Ne.symm h, ite_false]; simpa using String.le_total a.entity b.entity

theorem before_antisymm {a b : GivenRecord} (h₁ : recordBefore a b = true) (h₂ : recordBefore b a = true) :
    (a.entity, a.key) = (b.entity, b.key) := by
  unfold recordBefore at *
  by_cases h : a.entity = b.entity
  · simp only [h, ite_true] at h₁ h₂
    rw [h, keyBefore_antisymm h₁ h₂]
  · simp only [h, Ne.symm h, ite_false, decide_eq_true_eq] at h₁ h₂
    exact absurd (String.le_antisymm h₁ h₂) h

/-- Records with distinct entities and keys are ordered the same way whatever order they are written in. -/
theorem sorted_perm {rs rs' : List GivenRecord} (hp : rs.Perm rs') (hn : RecordsDistinct rs) :
    rs.mergeSort recordBefore = rs'.mergeSort recordBefore := by
  apply List.Perm.eq_of_pairwise _ (List.pairwise_mergeSort before_trans before_total _)
    (List.pairwise_mergeSort before_trans before_total _)
    ((List.mergeSort_perm _ _).trans (hp.trans (List.mergeSort_perm _ _).symm))
  intro a b ha hb hab hba
  exact eq_of_map_nodup (f := fun g : GivenRecord => (g.entity, g.key)) hn ((List.mergeSort_perm _ _).mem_iff.mp ha)
    (hp.mem_iff.mpr ((List.mergeSort_perm _ _).mem_iff.mp hb)) (before_antisymm hab hba)

/--
The order in which Given writes the records of a running service reaches nothing: a scenario that writes, for each
running service, the records of another scenario in another order, with no two of them of one entity and key, simulates
alike, with the same traces, messages, halt, and violations.
-/
@[guarantee] theorem simulate_records_perm (j : Spec.Structure) (start : World) (sc : Scenario) (records : List GivenRecord)
    (peers : List PeerEntry) (hs : peers.map (·.service) = sc.given.peers.map (·.service))
    (hp : ∀ s, (writtenRecords { sc with given := { sc.given with records, peers } } s).Perm (writtenRecords sc s))
    (hn : ∀ s, RecordsDistinct (writtenRecords sc s)) :
    simulate j fsOf start { sc with given := { sc.given with records, peers } } = simulate j fsOf start sc := by
  have hg (s : String) : givenRecords { sc with given := { sc.given with records, peers } } s = givenRecords sc s :=
    (sorted_perm (hp s).symm (hn s)).symm
  have hw : start.given j fsOf { sc with given := { sc.given with records, peers } } = start.given j fsOf sc := by
    unfold World.given
    simp only [hg, hs]
  unfold simulate
  rw [hw]
  rfl

end Tazuna.Thm.Sim.Given
