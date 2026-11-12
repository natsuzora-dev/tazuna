import Tazuna.Semantics.Service.Command
import Tazuna.Thm.Semantics.Functions
import Tazuna.Thm.Semantics.Service.Contract
import Tazuna.Thm.Semantics.Service.Integrity
import Tazuna.Thm.Semantics.State

namespace Tazuna.Thm.Semantics.Service.Command

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Semantics.Functions Tazuna.Thm.Semantics.Service.Integrity Tazuna.Thm.Semantics.Service.Records Tazuna.Thm.Semantics.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Semantics.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem processCommand_clock (name : String) (raw : Value) (id : Option String) (n : Nat) :
    (processCommand st fs s name raw id n).1.clock = s.clock := by
  simp only [processCommand, id_bind]
  split
  · cases id <;> rfl
  · exact (emitAll_clock _ _).trans (by simp [State.clock])
  · simp [State.clock]

theorem processCommand_commandAnswers (name : String) (raw : Value) (id : Option String) (n : Nat) :
    (processCommand st fs s name raw id n).1.commandAnswers = s.commandAnswers :=
  congrArg Prod.fst (processCommand_clock name raw id n)

theorem processCommand_grows (name : String) (raw : Value) (id : Option String) (n : Nat) :
    Grows s (processCommand st fs s name raw id n).1 := by
  simp only [processCommand, id_bind]
  split
  · exact answer_grows s _ _
  · rename_i records emits vs _
    exact ((Grows.of_lines (reportAll_lines (s := { s with records }) vs)).trans (reportAll_now (s := { s with records }) vs)
      (answer_grows _ id (.accepted none))).trans (by simp) (emitAll_grows _ _)
  · exact Grows.of_lines (reportAll_lines ..)

theorem evaluate_accepted_applies (records : Records) (now : Time) (name : String) (raw : Value) (written : Records)
    (emits : List Emit) (vs : List Fault) (h : evaluate st fs records now name raw = .accepted written emits vs) :
    applyAll st records emits = written ∧ duplicated st written = false ∧
      ∃ input, fs.parse (.input name) raw = .ok (some input) ∧
        vs = (commandEnsures st fs name input records written now).run ++ (integrityViolations st fs written name).run := by
  simp only [evaluate, id_bind] at h
  split at h
  · cases h
  · cases h
  · rename_i input hp
    split at h
    · cases h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i hd
              split at h
              · cases h
              · injection h with h₁ h₂ h₃
                subst h₁ h₂ h₃
                exact ⟨rfl, by simpa using hd, input, hp, rfl⟩

theorem processCommand_keysDistinct (name : String) (raw : Value) (id : Option String) (n : Nat)
    (h : KeysDistinct s.records) : KeysDistinct (processCommand st fs s name raw id n).1.records := by
  simp only [processCommand, id_bind]
  split
  · cases id <;> exact h
  · rename_i written emits vs he
    have hr := congrArg Fixed.records (emitAll_fixed (s := ({ s with records := written }.reportAll vs).answer id (.accepted none)) emits)
    show KeysDistinct (State.emitAll _ emits).records
    rw [show (State.emitAll _ emits).records = _ from hr]
    show KeysDistinct ((State.answer _ id _).records)
    rw [answer_records, reportAll_records]
    exact keysDistinct_of_not_duplicated (evaluate_accepted_applies _ _ _ _ _ _ _ he).2.1
  · show KeysDistinct (State.reportAll _ _).records
    rw [reportAll_records]
    exact h

theorem processCommand_answer (name : String) (raw : Value) (id : Option String) (n : Nat) :
    (processCommand st fs s name raw id n).2.1 = (evaluate st fs s.records s.now name raw).answer := by
  simp only [processCommand, id_bind]
  split <;> simp_all [Outcome.answer]

/-- A rejected command writes no record and emits no event: the state only gains the answer line. -/
theorem rejected_command_changes_nothing (name : String) (raw : Value) (id : Option String) (n : Nat) (r : Rejection)
    (h : evaluate st fs s.records s.now name raw = .rejected r) :
    processCommand st fs s name raw id n = (s.answer id (.rejected r), .rejected r, []) ∧
      (processCommand st fs s name raw id n).1.records = s.records := by
  have hp : processCommand st fs s name raw id n = (s.answer id (.rejected r), .rejected r, []) := by
    simp only [processCommand, id_bind, h]; rfl
  exact ⟨hp, by rw [hp]; exact answer_records s id _⟩

theorem accepted_command_writes_then_queues_reactions (name : String) (raw : Value) (id : Option String) (n : Nat)
    (written : Records) (emits : List Emit) (vs : List Fault)
    (h : evaluate st fs s.records s.now name raw = .accepted written emits vs) :
    applyAll st s.records emits = written ∧
      (processCommand st fs s name raw id n).1.records = written ∧
      (processCommand st fs s name raw id n).2.2 = emits := by
  refine ⟨(evaluate_accepted_applies _ _ _ _ _ _ _ h).1, ?_, ?_⟩
  · simp only [processCommand, id_bind, h]
    exact (congrArg Fixed.records (emitAll_fixed
      (s := ({ s with records := written }.reportAll vs).answer id (.accepted none)) _)).trans
      (by show (State.answer _ id _).records = _; rw [answer_records, reportAll_records])
  · simp [processCommand, h]

theorem own_command_answer_has_no_output (name : String) (raw : Value) (id : Option String) (n : Nat) (o : Value) :
    (processCommand st fs s name raw id n).2.1 ≠ .accepted (some o) := by
  rw [processCommand_answer]
  cases evaluate st fs s.records s.now name raw <;> simp [Outcome.answer]

theorem command_invalid_input_rejected (records : Records) (now : Time) (name : String) (raw : Value)
    (hp : fs.parse (.input name) raw = .ok none) :
    evaluate st fs records now name raw = .rejected { kind := .invalidInput } := by
  simp [evaluate, hp]

theorem already_exists_iff_duplicated (records : Records) (now : Time) (name : String) (raw input : Value)
    (emits normalized : List Emit) (hp : fs.parse (.input name) raw = .ok (some input))
    (hr : requirementsRejection st fs records now name input = .ok none)
    (hd : fs.decide name input records now = .ok emits) (hl : ∀ e ∈ emits, st.lists name e = true)
    (hn : normalizeEmits st fs name emits = .ok normalized) :
    evaluate st fs records now name raw = .rejected { kind := .alreadyExists } ↔
      duplicated st (applyAll st records normalized) = true := by
  have hf : emits.find? (!st.lists name ·) = none := List.find?_eq_none.mpr fun e he => by simp [hl e he]
  simp only [evaluate, id_bind, hp, hr, hd, hf, hn]
  split
  · simp_all
  · simp only [Bool.not_eq_true] at *
    simp_all only [Bool.false_eq_true, iff_false]
    split <;> simp

theorem unlisted_emitted_event_halts (records : Records) (now : Time) (name : String) (raw input : Value)
    (decided : List Emit) (hp : fs.parse (.input name) raw = .ok (some input))
    (hr : requirementsRejection st fs records now name input = .ok none)
    (hd : fs.decide name input records now = .ok decided) (hu : ∃ e ∈ decided, st.lists name e = false) :
    ∃ v, evaluate st fs records now name raw = .halted [v] ∧ v.halts = true ∧
      ∃ event, v = .unlistedEmittedEvent (st.ref name) event := by
  cases hf : decided.find? (!st.lists name ·) with
  | none =>
    obtain ⟨e, he, hl⟩ := hu
    simpa [hl] using List.find?_eq_none.mp hf e he
  | some e =>
    simp only [evaluate, id_bind, hp, hr, hd, hf]
    exact ⟨_, rfl, rfl, _, rfl⟩

theorem decide_payloads_sorted_before_normalize (name : String) (emits out : List Emit)
    (h : normalizeEmits st fs name emits = .ok out) :
    out.length = emits.length ∧ ∀ p ∈ emits.zip out, NormalizedEmit st fs p.1 p.2 := by
  obtain ⟨os, ho, hl, hp⟩ := normalizeEmits_fold name emits [] out h
  simp only [List.nil_append] at ho
  subst ho
  exact ⟨hl, hp⟩

theorem accepted_emits_decided (records : Records) (now : Time) (name : String) (raw : Value) (written : Records)
    (emits : List Emit) (vs : List Fault) (h : evaluate st fs records now name raw = .accepted written emits vs) :
    ∃ input decided, fs.parse (.input name) raw = .ok (some input) ∧ fs.decide name input records now = .ok decided ∧
      (∀ e ∈ decided, st.lists name e = true) ∧ ∀ e ∈ emits, ∃ e' ∈ decided, e.event = e'.event := by
  simp only [evaluate, id_bind] at h
  split at h
  · cases h
  · cases h
  · rename_i input hp
    split at h
    · cases h
    · cases h
    · split at h
      · cases h
      · rename_i decided hd
        split at h
        · cases h
        · rename_i hf
          split at h
          · cases h
          · rename_i out hn
            split at h
            · cases h
            · split at h
              · cases h
              · injection h with _ h₂ _
                subst h₂
                refine ⟨input, decided, hp, hd, fun e he => ?_, fun e he => ?_⟩
                · simpa using List.find?_eq_none.mp hf e he
                · obtain ⟨hl, hz⟩ := decide_payloads_sorted_before_normalize name _ out hn
                  obtain ⟨x, hx⟩ := exists_zip_of_mem_right hl he
                  exact ⟨x, (List.of_mem_zip hx).1, (hz _ hx).1⟩

theorem processCommand_mocks (name : String) (raw : Value) (id : Option String) (n : Nat) :
    (processCommand st fs s name raw id n).1.mocks = s.mocks := by
  simp only [processCommand, id_bind]
  split
  · cases id <;> rfl
  · exact (congrArg Fixed.mocks (emitAll_fixed _)).trans (by cases id <;> exact congrArg Fixed.mocks (reportAll_fixed _))
  · exact congrArg Fixed.mocks (reportAll_fixed ..)

theorem emitAll_violations (t : State) (emits : List Emit) : (t.emitAll emits).violations = t.violations := by
  unfold State.emitAll
  induction emits generalizing t with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons]; exact ih _

theorem emitAll_halted (t : State) (emits : List Emit) : (t.emitAll emits).halted = t.halted := by
  unfold State.emitAll
  induction emits generalizing t with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons]; exact ih _

theorem accepted_command_reports_violations (name : String) (raw : Value) (id : Option String) (n : Nat)
    (written : Records) (emits : List Emit) (vs : List Fault)
    (h : evaluate st fs s.records s.now name raw = .accepted written emits vs) :
    (processCommand st fs s name raw id n).1.violations = ({ s with records := written }.reportAll vs).violations ∧
      (processCommand st fs s name raw id n).1.halted = ({ s with records := written }.reportAll vs).halted ∧
      (processCommand st fs s name raw id n).2.1 = .accepted none := by
  simp only [processCommand, id_bind, h]
  refine ⟨?_, ?_, rfl⟩
  · show (State.emitAll _ emits).violations = _
    rw [emitAll_violations]
    cases id <;> rfl
  · show (State.emitAll _ emits).halted = _
    rw [emitAll_halted]
    cases id <;> rfl

end Tazuna.Thm.Semantics.Service.Command
