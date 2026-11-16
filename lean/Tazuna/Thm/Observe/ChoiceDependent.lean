import Tazuna.Observe.ChoiceDependent

namespace Tazuna.Thm.Observe.ChoiceDependent

open Tazuna.Data Tazuna.Semantics Tazuna.Observe

variable {m : Type → Type} [Monad m] [LawfulMonad m] (compare : Compare m)

theorem difference_same (o : Observe.Outcome) (bindings : Bindings) (h : compare o.lines o.lines = pure (.ok bindings))
    (hr : recordsText bindings o.records = recordsText [] o.records) :
    difference compare o o = pure none := by
  unfold difference
  split
  · simp
  · simp [h, hr]

theorem stepOrder_swap (a b : StepName) (aOrder bOrder : List StepName) (aFirst bFirst : Observe.Outcome)
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

theorem stepOrder_of_no_difference (a b : StepName) (aOrder bOrder : List StepName) (aFirst bFirst : Observe.Outcome)
    (ha : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical → difference compare aFirst bFirst = pure none)
    (hb : ¬ (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical →
      difference compare bFirst aFirst = pure none) :
    stepOrder compare a b aOrder bOrder aFirst bFirst = pure none := by
  unfold stepOrder
  by_cases h : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical
  · simp [h, ha h]
  · simp [h, hb h]

end Tazuna.Thm.Observe.ChoiceDependent
