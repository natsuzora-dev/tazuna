import Tazuna.Service.Records

namespace Tazuna.Thm.Service.Records

open Tazuna.Data Tazuna.Service

def KeysDistinct (records : Records) : Prop := (records.map fun r => (r.entity, r.key)).Nodup

/-- Functions read the keys of an entity in one order, whatever order the records were written in. -/
theorem keys_perm {r₁ r₂ : Records} (h : r₁.Perm r₂) (entity : String) : r₁.keys entity = r₂.keys entity := by
  have trans (a b c : String) (hab : decide (a ≤ b) = true) (hbc : decide (b ≤ c) = true) : decide (a ≤ c) = true := by
    simp only [decide_eq_true_eq] at *; exact String.le_trans hab hbc
  have total (a b : String) : (decide (a ≤ b) || decide (b ≤ a)) = true := by simpa using String.le_total a b
  unfold Records.keys
  apply List.Perm.eq_of_pairwise _ (List.pairwise_mergeSort trans total _) (List.pairwise_mergeSort trans total _)
    ((List.mergeSort_perm _ _).trans (((h.filter _).filterMap _).trans (List.mergeSort_perm _ _).symm))
  intro a b _ _ hab hba
  simp only [decide_eq_true_eq] at hab hba
  exact String.le_antisymm hab hba

end Tazuna.Thm.Service.Records
