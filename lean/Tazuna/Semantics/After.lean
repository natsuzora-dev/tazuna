import Tazuna.Semantics.Step

/-! The state a step reaches before it checks the invariants. A step that breaks an invariant leaves the state it began
with, so a counterexample shows this state as `after`; `step_settled` ties it to `step`. -/

namespace Tazuna.Ir.Step

variable (T : List TypeDecl) {v : ServiceV}

/-- What a step's events and internal steps leave before the invariant check, or none when the step ends before
it: Invalid, rejected, a fault, a query, time moving back. -/
def settled (s : State v) : Input v → Option (Acc v)
  | .command i caller input =>
    match execCommand T { state := s } (v.commands.get i) caller input with
    | .ok (.accepted a) => (settle T v.bounds.cascadeNat a).toOption
    | _ => none
  | .query .. => none
  | .answer to ⟨t, value⟩ =>
    match s.pending.find? (·.id == to) with
    | none => none
    | some p => match Ty.same t (answerTy p.request.output p.request.rejection) with
      | none => none
      | some ⟨h⟩ => match broken (p.request.holds (h ▸ value)) with
        | _ :: _ => none
        | [] => (applyEvents T { state := { s with pending := s.pending.filter (·.id != to) } }
            (p.request.onAnswer.fn (h ▸ value, ())) >>= settle T v.bounds.cascadeNat).toOption
  | .event i value =>
    (applyEvents T { state := s } [(v.subscribes.get i).wrap.fn (value, ())] >>= settle T v.bounds.cascadeNat).toOption
  | .clock time =>
    if time < s.now then none else
    match fire { s with now := time } (v.bounds.cascadeNat + 1) with
    | none => none
    | some (s', effs) => (start { state := s' } effs >>= settle T v.bounds.cascadeNat).toOption

end Step

/-- Where a step gets to its invariant check, its outcome is the first invariant the state it reached breaks, else
accepted with that state. -/
theorem step_settled (T : List TypeDecl) {v : ServiceV} (s : State v) (x : Input v) {a : Step.Acc v}
    (h : Step.settled T s x = some a) :
    step T v s x = match Step.invariants a.state with
      | n :: _ => ⟨(step T v s x).state, .fault (.invariant n), [], []⟩
      | [] => ⟨a.state, .accepted, a.events, a.out⟩ := by
  have fin : ∀ (s0 : State v) (r : Except Fault (Step.Acc v)) (o : Outcome),
      (r >>= Step.settle T v.bounds.cascadeNat).toOption = some a →
      Step.finish T s0 r o = match Step.invariants a.state with
        | n :: _ => ⟨s0, .fault (.invariant n), [], []⟩
        | [] => ⟨a.state, o, a.events, a.out⟩ := by
    intro s0 r o hr
    unfold Step.finish
    cases hs : r >>= Step.settle T v.bounds.cascadeNat with
    | error => simp [hs, Except.toOption] at hr
    | ok b =>
      simp only [hs, Except.toOption, Option.some.injEq] at hr
      subst hr
      rfl
  cases x with
  | command i caller input =>
    simp only [Step.settled] at h
    split at h <;> try cases h
    rename_i a0 he
    have := fin { s with fresh := s.fresh + 1 } (.ok a0) .accepted h
    simp only [step, he, this]
    split <;> rfl
  | query => cases h
  | answer to w =>
    obtain ⟨t, value⟩ := w
    simp only [Step.settled] at h
    split at h
    · cases h
    · rename_i p hp
      split at h
      · cases h
      · rename_i hh
        split at h
        · cases h
        · rename_i hb
          simp only [step, hp, hh, hb]
          rw [fin _ _ _ h]
          split <;> rfl
  | event i value =>
    simp only [Step.settled] at h
    simp only [step]
    rw [fin _ _ _ h]
    split <;> rfl
  | clock time =>
    simp only [Step.settled] at h
    split at h
    · cases h
    · rename_i hlt
      split at h
      · cases h
      · rename_i s' effs hf
        simp only [step, hlt, ite_false, hf]
        rw [fin _ _ _ h]
        split <;> rfl

end Tazuna.Ir
