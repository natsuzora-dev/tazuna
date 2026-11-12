import Tazuna.Observe.ChoiceDependent

namespace Tazuna.Thm.Observe.ChoiceDependent

open Tazuna.Data Tazuna.Semantics Tazuna.Observe

variable {m : Type → Type} [Monad m] [LawfulMonad m] (compare : Compare m)

theorem difference_same (o : Outcome) (bindings : Bindings) (h : compare o.lines o.lines = pure (.ok bindings))
    (hr : recordsText bindings o.records = recordsText [] o.records) :
    difference compare o o = pure none := by
  unfold difference
  split
  · simp
  · simp [h, hr]

/-- Two orders of one pair give one violation, whichever order the caller names first. -/
theorem deadlineOrder_swap (chart : DeadlineId → Option Syntax.Ref) (a b : DeadlineId) (aFirst bFirst : Outcome)
    (h : (ToValue.toValue a).canonical ≠ (ToValue.toValue b).canonical) :
    deadlineOrder compare chart a b aFirst bFirst = deadlineOrder compare chart b a bFirst aFirst := by
  unfold deadlineOrder
  by_cases hab : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical
  · have hba : ¬ (ToValue.toValue b).canonical ≤ (ToValue.toValue a).canonical :=
      fun hba => h (String.le_antisymm hab hba)
    simp [hab, hba]
  · have hba : (ToValue.toValue b).canonical ≤ (ToValue.toValue a).canonical :=
      (String.le_total _ _).resolve_left hab
    simp [hab, hba]

theorem answerOrder_swap (x y : String) (xSender ySender : Syntax.Ref) (xFirst yFirst : Outcome) (h : x ≠ y) :
    answerOrder compare x y xSender ySender xFirst yFirst = answerOrder compare y x ySender xSender yFirst xFirst := by
  unfold answerOrder
  by_cases hxy : x ≤ y
  · have hyx : ¬ y ≤ x := fun hyx => h (String.le_antisymm hxy hyx)
    simp [hxy, hyx]
  · have hyx : y ≤ x := (String.le_total x y).resolve_left hxy
    simp [hxy, hyx]

theorem stepOrder_swap (a b : StepName) (aFirst bFirst : Outcome)
    (h : (ToValue.toValue a).canonical ≠ (ToValue.toValue b).canonical) :
    stepOrder compare a b aFirst bFirst = stepOrder compare b a bFirst aFirst := by
  unfold stepOrder
  by_cases hab : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical
  · have hba : ¬ (ToValue.toValue b).canonical ≤ (ToValue.toValue a).canonical :=
      fun hba => h (String.le_antisymm hab hba)
    simp [hab, hba]
  · have hba : (ToValue.toValue b).canonical ≤ (ToValue.toValue a).canonical :=
      (String.le_total _ _).resolve_left hab
    simp [hab, hba]

theorem deadlineOrder_of_no_difference (chart : DeadlineId → Option Syntax.Ref) (a b : DeadlineId)
    (aFirst bFirst : Outcome)
    (ha : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical → difference compare aFirst bFirst = pure none)
    (hb : ¬ (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical →
      difference compare bFirst aFirst = pure none) :
    deadlineOrder compare chart a b aFirst bFirst = pure none := by
  unfold deadlineOrder
  by_cases h : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical
  · simp [h, ha h]
  · simp [h, hb h]

theorem answerChoice_of_no_difference (sender : Syntax.Ref) (request other : String) (answered alternative : Outcome)
    (h : difference compare answered alternative = pure none) :
    answerChoice compare sender request other answered alternative = pure none := by
  simp [answerChoice, h]

theorem answerOrder_of_no_difference (x y : String) (xSender ySender : Syntax.Ref) (xFirst yFirst : Outcome)
    (hx : x ≤ y → difference compare xFirst yFirst = pure none)
    (hy : ¬ x ≤ y → difference compare yFirst xFirst = pure none) :
    answerOrder compare x y xSender ySender xFirst yFirst = pure none := by
  unfold answerOrder
  by_cases h : x ≤ y
  · simp [h, hx h]
  · simp [h, hy h]

theorem requestOrder_of_no_difference (first second : Syntax.Ref) (forward backward : Outcome)
    (h : difference compare forward backward = pure none) :
    requestOrder compare first second forward backward = pure none := by
  simp [requestOrder, h]

theorem stepOrder_of_no_difference (a b : StepName) (aFirst bFirst : Outcome)
    (ha : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical → difference compare aFirst bFirst = pure none)
    (hb : ¬ (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical →
      difference compare bFirst aFirst = pure none) :
    stepOrder compare a b aFirst bFirst = pure none := by
  unfold stepOrder
  by_cases h : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical
  · simp [h, ha h]
  · simp [h, hb h]

end Tazuna.Thm.Observe.ChoiceDependent
