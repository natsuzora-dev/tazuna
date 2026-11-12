import Tazuna.Thm.Data.Trace
import Tazuna.Verify.External

namespace Tazuna.Thm.Verify.External

open Tazuna.Data Tazuna.Syntax Tazuna.Thm.Data.Trace Tazuna.Verify

theorem checkExternal_after_malformed (s : Structure) (service : String) (pre post₁ post₂ : List (FileLine TraceLine)) :
    checkExternal s service (pre ++ .malformed :: post₁) = checkExternal s service (pre ++ .malformed :: post₂) := by
  simp only [checkExternal, untilMalformed_append_malformed]

/-- The value that TS `byLine` sorts violations by. -/
def lineOf : Finding → Option Value
  | .mismatch m => m.data.field? "line"
  | .uncomparable u => u.data.field? "line"

theorem resultOfFinding_line (line : Nat) (event : Ref) (requestId : String) (target : Ref) (m : ResultOfMismatch) :
    lineOf (resultOfFinding line event requestId target m) = some (ToValue.toValue line) := by
  cases m <;> simp [resultOfFinding, lineOf, Mismatch.data, Uncomparable.data, Value.field?]

theorem checkLine_line (s : Structure) (service : String) (requests : List (String × Option Request)) (line : Nat)
    (l : TraceLine) (f : Finding) (h : (checkLine s service requests line l).1 = some f) :
    lineOf f = some (ToValue.toValue line) := by
  unfold checkLine at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; simp [lineOf, Mismatch.data, Uncomparable.data, Value.field?]; done)
    | (obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact resultOfFinding_line _ _ _ _ m)

theorem checkLines_lines (s : Structure) (service : String) :
    ∀ (lines : List (Option TraceLine)) (line : Nat) (requests : List (String × Option Request)),
      ∃ found : List (Option Finding), found.length = lines.length ∧
        (∀ i f, found[i]? = some (some f) → lineOf f = some (ToValue.toValue (line + i))) ∧
        checkLines s service lines line requests = found.filterMap id
  | [], _, _ => ⟨[], rfl, by simp, by simp [checkLines]⟩
  | none :: ls, line, requests => by
    obtain ⟨found, hl, hf, he⟩ := checkLines_lines s service ls (line + 1) requests
    refine ⟨none :: found, by simp [hl], fun i f hi => ?_, by simp [checkLines, he]⟩
    cases i with
    | zero => simp at hi
    | succ i => simpa [Nat.add_assoc, Nat.add_comm 1 i] using hf i f (by simpa using hi)
  | some l :: ls, line, requests => by
    obtain ⟨found, hl, hf, he⟩ := checkLines_lines s service ls (line + 1) (checkLine s service requests line l).2
    refine ⟨(checkLine s service requests line l).1 :: found, by simp [hl], fun i f hi => ?_, ?_⟩
    · cases i with
      | zero => simpa using checkLine_line s service requests line l f (by simpa using hi)
      | succ i => simpa [Nat.add_assoc, Nat.add_comm 1 i] using hf i f (by simpa using hi)
    · simp only [checkLines, he]
      cases (checkLine s service requests line l).1 <;> rfl

theorem checkExternal_lines (s : Structure) (service : String) (trace : List (FileLine TraceLine)) :
    ∃ found : List (Option Finding), found.length = (untilMalformed trace).1.length ∧
      (∀ i f, found[i]? = some (some f) → lineOf f = some (ToValue.toValue (i + 1))) ∧
      (∀ n, (untilMalformed trace).2 = some n → n = found.length + 1) ∧
      checkExternal s service trace =
        found.filterMap id ++ ((untilMalformed trace).2.map fun n => .uncomparable (.lineSchema n)).toList := by
  obtain ⟨found, hl, hf, he⟩ := checkLines_lines s service (untilMalformed trace).1 1 []
  refine ⟨found, hl, fun i f hi => by simpa [Nat.add_comm] using hf i f hi, fun n hn => ?_, ?_⟩
  · rw [hl]; exact untilMalformed_line trace hn
  · simp only [checkExternal, he]

end Tazuna.Thm.Verify.External
