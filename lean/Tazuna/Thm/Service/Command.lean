import Tazuna.Service.Command
import Tazuna.Thm.Service.Functions
import Tazuna.Thm.Service.Contract
import Tazuna.Thm.Service.Integrity
import Tazuna.Thm.Service.State

namespace Tazuna.Thm.Service.Command

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.Records Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem processCommand_clock (name : String) (raw : Value) (id : Option LineId) (n : Nat) :
    (processCommand st fs s name raw id n).1.clock = s.clock := by
  simp only [processCommand, id_bind]
  split
  · cases id <;> rfl
  · exact (emitAll_clock _ _ _).trans (by simp [State.clock])
  · simp [State.clock]

theorem processCommand_grows (name : String) (raw : Value) (id : Option LineId) (n : Nat) :
    Grows s (processCommand st fs s name raw id n).1 := by
  simp only [processCommand, id_bind]
  split
  · exact answer_grows s _ _ _
  · rename_i records emits vs _
    exact ((Grows.of_lines (reportAll_lines (s := { s with records }) vs)).trans (reportAll_now (s := { s with records }) vs)
      (answer_grows _ id _ (.accepted none))).trans (by simp) (emitAll_grows _ _ _)
  · exact Grows.of_lines (reportAll_lines ..)

theorem evaluate_accepted_applies (records : Records) (now : Time) (name : String) (raw : Value) (written : Records)
    (groups : List (List Emit)) (vs : List Fault)
    (h : evaluate st fs records now name raw = .accepted written groups vs) :
    applyAll st records groups.flatten = written ∧ duplicated st written = false ∧
      ∃ input, fs.parseOutside st (.input (st.ref name)) raw = .ok (some input) ∧
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

theorem processCommand_keysDistinct (name : String) (raw : Value) (id : Option LineId) (n : Nat)
    (h : KeysDistinct s.records) : KeysDistinct (processCommand st fs s name raw id n).1.records := by
  simp only [processCommand, id_bind]
  split
  · cases id <;> exact h
  · rename_i written groups vs he
    have hr := congrArg Fixed.records
      (emitAll_fixed (s := ({ s with records := written }.reportAll vs).answer id (st.ref name) (.accepted none)) id (emittedBy n groups))
    show KeysDistinct (State.emitAll _ id (emittedBy n groups)).records
    rw [show (State.emitAll _ id (emittedBy n groups)).records = _ from hr]
    show KeysDistinct ((State.answer _ id _ _).records)
    rw [answer_records, reportAll_records]
    exact keysDistinct_of_not_duplicated (evaluate_accepted_applies _ _ _ _ _ _ _ he).2.1
  · show KeysDistinct (State.reportAll _ _).records
    rw [reportAll_records]
    exact h

/-- A rejected command writes no record and emits no event: the state only gains the answer line. -/
theorem rejected_command_changes_nothing (name : String) (raw : Value) (id : Option LineId) (n : Nat) (r : Rejection)
    (h : evaluate st fs s.records s.now name raw = .rejected r) :
    processCommand st fs s name raw id n = (s.answer id (st.ref name) (.rejected r), .rejected r, []) ∧
      (processCommand st fs s name raw id n).1.records = s.records := by
  have hp : processCommand st fs s name raw id n = (s.answer id (st.ref name) (.rejected r), .rejected r, []) := by
    simp only [processCommand, id_bind, h]; rfl
  exact ⟨hp, by rw [hp]; exact answer_records s id _ _⟩

theorem accepted_command_writes_then_queues_reactions (name : String) (raw : Value) (id : Option LineId) (n : Nat)
    (written : Records) (groups : List (List Emit)) (vs : List Fault)
    (h : evaluate st fs s.records s.now name raw = .accepted written groups vs) :
    applyAll st s.records groups.flatten = written ∧
      (processCommand st fs s name raw id n).1.records = written ∧
      (processCommand st fs s name raw id n).2.2 = groups := by
  refine ⟨(evaluate_accepted_applies _ _ _ _ _ _ _ h).1, ?_, ?_⟩
  · simp only [processCommand, id_bind, h]
    exact (congrArg Fixed.records (emitAll_fixed
      (s := ({ s with records := written }.reportAll vs).answer id (st.ref name) (.accepted none)) _ _)).trans
      (by show (State.answer _ id _ _).records = _; rw [answer_records, reportAll_records])
  · simp [processCommand, h]

theorem command_invalid_input_rejected (records : Records) (now : Time) (name : String) (raw : Value)
    (hp : fs.parseOutside st (.input (st.ref name)) raw = .ok none) :
    evaluate st fs records now name raw = .rejected { kind := .invalidInput } := by
  simp [evaluate, hp]

theorem unlisted_emitted_event_halts (records : Records) (now : Time) (name : String) (raw input : Value)
    (decided : List (List Emit)) (hp : fs.parseOutside st (.input (st.ref name)) raw = .ok (some input))
    (hr : requirementsRejection st fs records now name input = .ok none)
    (hd : fs.decide name input records now = .ok decided) (hu : ∃ e ∈ decided.flatten, st.lists name e = false) :
    ∃ v, evaluate st fs records now name raw = .halted [v] ∧ v.halts = true ∧
      ∃ event, v = .unlistedEmittedEvent (st.ref name) event := by
  cases hf : decided.flatten.find? (!st.lists name ·) with
  | none =>
    obtain ⟨e, he, hl⟩ := hu
    simpa [hl] using List.find?_eq_none.mp hf e he
  | some e =>
    simp only [evaluate, id_bind, hp, hr, hd, hf]
    exact ⟨_, rfl, rfl, _, rfl⟩

theorem mem_chunks {α : Type} : ∀ (ns : List Nat) (xs : List α) (x : α), x ∈ (chunks ns xs).flatten → x ∈ xs
  | [], _, _, h => by simp [chunks] at h
  | n :: ns, xs, x, h => by
    simp only [chunks, List.flatten_cons, List.mem_append] at h
    rcases h with h | h
    · exact List.mem_of_mem_take h
    · exact List.mem_of_mem_drop (mem_chunks ns _ x h)

theorem mem_orderedGroups (decided : List (List Emit)) (sorted : List Emit) (e : Emit)
    (h : e ∈ (orderedGroups decided sorted).flatten) : e ∈ sorted := by
  simp only [orderedGroups, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨g, hg, rfl⟩, he⟩ := h
  exact mem_chunks _ _ e (List.mem_flatten.mpr ⟨g, hg, (List.mergeSort_perm _ _).mem_iff.mp he⟩)

theorem accepted_emits_decided (records : Records) (now : Time) (name : String) (raw : Value) (written : Records)
    (groups : List (List Emit)) (vs : List Fault)
    (h : evaluate st fs records now name raw = .accepted written groups vs) :
    ∃ input decided, fs.parseOutside st (.input (st.ref name)) raw = .ok (some input) ∧ fs.decide name input records now = .ok decided ∧
      (∀ e ∈ decided.flatten, st.lists name e = true) ∧
      groups = orderedGroups decided decided.flatten := by
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
          · split at h
            · cases h
            · split at h
              · cases h
              · injection h with _ h₂ _
                subst h₂
                refine ⟨input, decided, hp, hd, fun e he => ?_, rfl⟩
                simpa using List.find?_eq_none.mp hf e he

end Tazuna.Thm.Service.Command
