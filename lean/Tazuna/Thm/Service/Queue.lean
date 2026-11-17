import Tazuna.Service.Queue
import Tazuna.Thm.Service.Screen.Subscription
import Tazuna.Thm.Service.Query
import Tazuna.Thm.Service.Clock

namespace Tazuna.Thm.Service.Queue

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Screen.Subscription Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.Query Tazuna.Thm.Service.Records Tazuna.Thm.Service.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Service.Chart.Basic Tazuna.Thm.Service.Clock

variable {st : Service} {fs : Functions Id} {s : State}

theorem checkHolds_fixed : (checkHolds st fs s).fixed = s.fixed := by
  unfold checkHolds
  rw [foldlM_id]
  generalize s.running = is
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split
    · rfl
    · rw [foldlM_id]
      exact holdsFold_fixed i _

theorem invariantViolations_eq : invariantViolations st fs s = (s.machines.filter (!·.closed)).filterMap fun i =>
    match fs.chartInvariant (s.scopeOf i none) s.records with
    | .error e => some (issueViolation st (st.ref i.chart.name) e)
    | .ok failed => failed.map (.failedChartInvariant (st.ref i.chart.name)) := by
  simp only [invariantViolations, id_bind, mapM_id, List.filterMap_map]
  congr 1

/-- Whether every open machine's invariants answer without an Issue. -/
def InvariantsAnswer (fs : Functions Id) (s : State) : Prop :=
  ∀ i ∈ s.machines, i.closed = false → ∃ failed, fs.chartInvariant (s.scopeOf i none) s.records = .ok failed

theorem invariantViolations_not_halts (h : InvariantsAnswer fs s) :
    ∀ f ∈ (invariantViolations st fs s).run, f.halts = false := by
  intro f hp
  rw [invariantViolations_eq] at hp
  obtain ⟨i, hm, hi⟩ := List.mem_filterMap.mp hp
  obtain ⟨hm, hc⟩ := List.mem_filter.mp hm
  obtain ⟨failed, hf⟩ := h i hm (by simpa using hc)
  rw [hf] at hi
  obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hi
  rfl

theorem checkInvariants_fixed : (checkInvariants st fs s).fixed = s.fixed := reportAll_fixed _

theorem checkInvariants_lines : (checkInvariants st fs s).lines = s.lines := reportAll_lines _

theorem failed_chart_invariant_reported (i : Instance) (c : String) (hh : s.halted = none) (hi : i ∈ s.machines)
    (hc : i.closed = false) (ha : InvariantsAnswer fs s)
    (hf : fs.chartInvariant (s.scopeOf i none) s.records = .ok (some c)) :
    (Finding.fault (.failedChartInvariant (st.ref i.chart.name) c)).toViolation ∈
      (checkInvariants st fs s).violations := by
  show _ ∈ (s.reportAll (invariantViolations st fs s).run).violations
  rw [(reportAll_not_halts _ (invariantViolations_not_halts ha) s).2 hh]
  refine List.mem_append_right _ (List.mem_map.mpr ⟨.failedChartInvariant (st.ref i.chart.name) c, ?_, rfl⟩)
  rw [invariantViolations_eq]
  refine List.mem_filterMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hc]⟩, ?_⟩
  simp [hf]

theorem invariants_hold_report_nothing
    (h : ∀ i ∈ s.machines, i.closed = false → fs.chartInvariant (s.scopeOf i none) s.records = .ok none) :
    checkInvariants st fs s = s := by
  show s.reportAll (invariantViolations st fs s).run = s
  rw [invariantViolations_eq, List.filterMap_eq_nil_iff.mpr (fun i hi => ?_)]
  · rfl
  · obtain ⟨hi, hc⟩ := List.mem_filter.mp hi
    simp [h i hi (by simpa using hc)]

theorem afterMessage_fixed : (afterMessage st fs s).fixed = s.fixed := by
  simp only [afterMessage, id_bind]
  split
  · exact checkHolds_fixed
  · split
    · exact rearm_fixed.trans (checkInvariants_fixed.trans checkHolds_fixed)
    · exact publish_fixed.trans (rearm_fixed.trans (checkInvariants_fixed.trans checkHolds_fixed))

theorem afterMessage_commandAnswers : (afterMessage st fs s).commandAnswers = s.commandAnswers :=
  congrArg Fixed.commandAnswers afterMessage_fixed

theorem fireDue_commandAnswers (to : Time) (fuel : Nat) (tie : Option Time) :
    (fireDue st fs to fuel tie s).commandAnswers = s.commandAnswers := by
  induction fuel generalizing s tie with
  | zero => simp only [fireDue]; split <;> rfl
  | succ fuel ih =>
    rw [fireDue]
    split
    · rfl
    · split
      · rfl
      · dsimp only
        split
        · simp
        · rename_i hc
          obtain ⟨_, rfl⟩ := chooseDeadline_orders hc
          try simp only [id_bind]
          rw [ih, afterMessage_commandAnswers, drain_commandAnswers, (keeps_settled _ _ (keeps_fire _ _)).commandAnswers]
          rfl

theorem finish_commandAnswers : (finish st fs s).commandAnswers = s.commandAnswers := by
  simp only [finish, id_bind, fireDue_commandAnswers, afterMessage_commandAnswers]

theorem message_commandAnswers (q : Queue) : (message st fs s q).commandAnswers = s.commandAnswers := by
  simp only [message, id_bind, finish_commandAnswers, drain_commandAnswers]

theorem checkHolds_lines : (checkHolds st fs s).lines = s.lines := by
  unfold checkHolds
  rw [foldlM_id]
  generalize s.running = is
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split
    · rfl
    · rw [foldlM_id]
      exact holdsFold_lines i _

theorem afterMessage_grows : Grows s (afterMessage st fs s) := by
  simp only [afterMessage, id_bind]
  split
  · exact Grows.of_lines checkHolds_lines
  · split
    · exact Grows.of_lines (rearm_lines.trans (checkInvariants_lines.trans checkHolds_lines))
    · exact (Grows.of_lines (rearm_lines.trans (checkInvariants_lines.trans checkHolds_lines))).trans
        (congrArg Fixed.now (rearm_fixed.trans (checkInvariants_fixed.trans checkHolds_fixed))) publish_grows

theorem fireDue_extends (to : Time) (fuel : Nat) (tie : Option Time) : Extends s (fireDue st fs to fuel tie s) := by
  induction fuel generalizing s tie with
  | zero => simp only [fireDue]; split <;> exact ⟨#[], by simp [State.report, Fault.halts, State.halt]⟩
  | succ fuel ih =>
    rw [fireDue]
    split
    · exact Extends.refl _
    · split
      · exact Extends.refl _
      · dsimp only
        split
        · exact ⟨#[], by simp⟩
        · rename_i hc
          obtain ⟨_, rfl⟩ := chooseDeadline_orders hc
          try simp only [id_bind]
          refine Extends.trans ?_ (ih _)
          refine Extends.trans ?_ afterMessage_grows.toExtends
          refine Extends.trans ?_ (drain_grows _ _).toExtends
          exact (growsBy_settled _ _ (growsBy_fire _ _) (keeps_fire _ _) _).toExtends

theorem message_extends (q : Queue) : Extends s (message st fs s q) := by
  simp only [message, finish, id_bind]
  exact (drain_grows _ _).toExtends.trans (afterMessage_grows.toExtends.trans (fireDue_extends _ _ _))

theorem afterMessage_records : (afterMessage st fs s).records = s.records := congrArg Fixed.records afterMessage_fixed

theorem afterMessage_keysDistinct (h : KeysDistinct s.records) : KeysDistinct (afterMessage st fs s).records := by
  rw [afterMessage_records]
  exact h

theorem fireDue_keysDistinct (to : Time) (fuel : Nat) (tie : Option Time) (h : KeysDistinct s.records) :
    KeysDistinct (fireDue st fs to fuel tie s).records := by
  induction fuel generalizing s tie with
  | zero => simp only [fireDue]; split <;> exact h
  | succ fuel ih =>
    rw [fireDue]
    split
    · exact h
    · split
      · exact h
      · dsimp only
        split
        · simpa using h
        · rename_i hc
          obtain ⟨_, rfl⟩ := chooseDeadline_orders hc
          try simp only [id_bind]
          exact ih _ (afterMessage_keysDistinct (drain_keysDistinct _ _ (by rw [(keeps_settled _ _ (keeps_fire _ _)).records]; exact h)))

theorem message_keysDistinct (q : Queue) (h : KeysDistinct s.records) : KeysDistinct (message st fs s q).records := by
  simp only [message, finish, id_bind]
  exact fireDue_keysDistinct _ _ _ (afterMessage_keysDistinct (drain_keysDistinct _ _ h))

theorem deadline_is_own_message (to : Time) (fuel : Nat) (tie : Option Time) (e t : Deadline) (s' : State)
    (hh : s.halted = none) (he : earliestDeadline s.deadlines to = some e)
    (hc : chooseDeadline st s e (s.deadlines.filter (·.time == e.time))
      (1 < (s.deadlines.filter (·.time == e.time)).length || tie == e.time) = .ok (t, s')) :
    fireDue st fs to (fuel + 1) tie s =
      let time := t.time.getD s'.now
      let s₁ := { s' with now := max s'.now time }.newMessage
      let tied := 1 < (s.deadlines.filter (·.time == e.time)).length || tie == e.time
      let (s₂, step) := s₁.newStep none (tie := if tied then e.time else none)
      let r := settled fs st step (some t.machine) (fire fs st step t) ⟨s₂, {}⟩
      fireDue st fs to fuel
        (if 1 < (s.deadlines.filter (·.time == e.time)).length || tie == e.time then e.time else none)
        (afterMessage st fs (drain st fs Limit.messageWork.max r.state r.queue)) := by
  simp [fireDue, hh, he, hc]

theorem message_keeps_earlier_lines (q : Queue) : ∃ new, (message st fs s q).lines = s.lines ++ new :=
  message_extends q

theorem deadline_message_at_its_time (to : Time) (fuel : Nat) (tie : Option Time) (e t : Deadline) (s' : State)
    (hh : s.halted = none) (he : earliestDeadline s.deadlines to = some e)
    (hc : chooseDeadline st s e (s.deadlines.filter (·.time == e.time))
      (1 < (s.deadlines.filter (·.time == e.time)).length || tie == e.time) = .ok (t, s')) :
    ∃ s₁ q tie', fireDue st fs to (fuel + 1) tie s =
        fireDue st fs to fuel tie' (afterMessage st fs (drain st fs Limit.messageWork.max s₁ q)) ∧
      s₁.now = max s'.now (t.time.getD s'.now) := by
  refine ⟨_, _, _, by simp only [fireDue, hh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, he, hc, Tazuna.Thm.Service.Note.note_id,
      id_pure, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, id_bind]; rfl, ?_⟩
  exact (keeps_settled _ _ (keeps_fire _ t)).now _

theorem afterMessage_takenAnswers : (afterMessage st fs s).takenAnswers = s.takenAnswers :=
  congrArg Fixed.takenAnswers afterMessage_fixed

theorem fireDue_takenAnswers (to : Time) (fuel : Nat) (tie : Option Time) :
    (fireDue st fs to fuel tie s).takenAnswers = s.takenAnswers := by
  induction fuel generalizing s tie with
  | zero => simp only [fireDue]; split <;> rfl
  | succ fuel ih =>
    rw [fireDue]
    split
    · rfl
    · split
      · rfl
      · dsimp only
        split
        · exact congrArg Fixed.takenAnswers (report_fixed ..)
        · rename_i hc
          obtain ⟨_, rfl⟩ := chooseDeadline_orders hc
          try simp only [id_bind]
          rw [ih, afterMessage_takenAnswers, drain_takenAnswers, (keeps_settled _ _ (keeps_fire _ _)).takenAnswers]
          rfl

theorem message_takenAnswers (q : Queue) : (message st fs s q).takenAnswers = s.takenAnswers := by
  simp only [message, finish, id_bind]
  rw [fireDue_takenAnswers, afterMessage_takenAnswers, drain_takenAnswers]

theorem message_outputs_at_its_time (n : Nat) (q : Queue) :
    ∃ new, (afterMessage st fs (drain st fs n s q)).lines = s.lines ++ new ∧ ∀ l ∈ new, l.time = s.now :=
  (drain_grows n q).trans (drain_keeps_now n q) afterMessage_grows

theorem fireDue_at_deadline_limit (to : Time) (tie : Option Time) :
    fireDue st fs to 0 tie s =
      if s.halted.isNone && (earliestDeadline s.deadlines to).isSome then s.halt (Finding.fault (.exceededDueDeadlines Limit.dueDeadlines.max)).toViolation else s := by
  simp only [fireDue, id_pure, State.report]
  rfl

end Tazuna.Thm.Service.Queue
