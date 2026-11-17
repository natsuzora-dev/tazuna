import Tazuna.Explore.ChoiceDependent

namespace Tazuna.Thm.Explore.ChoiceDependent

open Tazuna.Data Tazuna.Service Tazuna.Explore Tazuna.Sim

variable {m : Type → Type} [Monad m] [LawfulMonad m] (compare : Compare m)

theorem difference_same (o : Explore.Outcome) (set : List Binding) (h : compare (o.renaming o) o.lines o.lines = pure (.ok set))
    (hr : sameRecords set o o = .same) :
    difference compare o o = pure .same := by
  unfold difference
  split
  · simp
  · simp [h, hr]

theorem stepOrder_swap (a b : StepName) (aOrder bOrder : List StepName) (aFirst bFirst : Explore.Outcome)
    (h : (ToValue.toValue a).canonical ≠ (ToValue.toValue b).canonical) :
    stepOrder compare a b aOrder bOrder aFirst bFirst = stepOrder compare b a bOrder aOrder bFirst aFirst := by
  unfold stepOrder
  by_cases hab : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical
  · have hba : ¬ (ToValue.toValue b).canonical ≤ (ToValue.toValue a).canonical :=
      fun hba => h (String.le_antisymm hab hba)
    simp [hab, hba]
  · have hba : (ToValue.toValue b).canonical ≤ (ToValue.toValue a).canonical :=
      (String.le_total _ _).resolve_left hab
    simp [hab, hba]

theorem stepOrder_of_no_difference (a b : StepName) (aOrder bOrder : List StepName) (aFirst bFirst : Explore.Outcome)
    (ha : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical → difference compare aFirst bFirst = pure .same)
    (hb : ¬ (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical →
      difference compare bFirst aFirst = pure .same) :
    stepOrder compare a b aOrder bOrder aFirst bFirst = pure none := by
  unfold stepOrder
  by_cases h : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical
  · simp [h, ha h, Comparison.violation]
  · simp [h, hb h, Comparison.violation]

end Tazuna.Thm.Explore.ChoiceDependent
