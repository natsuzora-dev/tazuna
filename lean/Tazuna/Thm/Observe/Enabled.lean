import Tazuna.Observe.Enabled
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Observe.Enabled

open Tazuna.Data Tazuna.Semantics Tazuna.Observe
open Tazuna.Thm.Data.Basic

variable {st : Service} {stepper : Stepper Id} {fs : Functions Id}

macro "unfold_state" : tactic => `(tactic| simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
  StateT.get, pure, StateT.pure, liftM, monadLift, MonadLift.monadLift, StateT.lift, modify, modifyGet,
  MonadStateOf.modifyGet, StateT.modifyGet, id_bind, id_pure] at *)

theorem enabledStep_stopped (s : State) (input : Step) (log : EnabledLog)
    (h : log.stopped.isSome) : enabledStep st stepper fs s input log = (s, log) := by
  simp only [enabledStep]
  unfold_state
  simp [h, StateT.pure]

theorem enabledStep_running (s : State) (input : Step) (log : EnabledLog)
    (h : log.stopped = none) :
    enabledStep st stepper fs s input log =
      let s₁ := stepper s input
      if s₁.halted.isSome then (s₁, log) else
      match enabled st fs s₁ with
      | .error fault => (s₁, { log with stopped := some (Finding.fault fault).toViolation })
      | .ok e => (s₁, { log with enabled := log.enabled ++ [e] }) := by
  simp only [enabledStep]
  unfold_state
  simp only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  by_cases hh : (stepper s input).halted.isSome
  · simp [hh, StateT.bind, StateT.lift, StateT.pure]
  · cases he : enabled st fs (stepper s input) <;>
      simp [hh, he, h, StateT.bind, StateT.lift, StateT.pure, StateT.modifyGet]

theorem runFrom_stopped (s : State) (inputs : List Step) (log : EnabledLog) (h : log.stopped.isSome) :
    runFrom (enabledStep st stepper fs) s inputs log = (s, log) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have hs := enabledStep_stopped (st := st) (stepper := stepper) (fs := fs) s i log h
    simp only [runFrom]
    unfold_state
    rw [hs]
    dsimp only
    split
    · rfl
    · exact ih s

def runPrefix (stepper : Stepper Id) : Nat → State → List Step → State
  | 0, s, _ | _, s, [] => s
  | k + 1, s, input :: rest =>
    let s := stepper s input
    if s.halted.isSome then s else runPrefix stepper k s rest

theorem runFrom_prefix (s : State) (inputs : List Step) (log : EnabledLog) (h₀ : log.stopped = none) :
    ∃ added, ((runFrom (enabledStep st stepper fs) s inputs).run log).2.enabled = log.enabled ++ added ∧
      ((runFrom (enabledStep st stepper fs) s inputs).run log).1 = runPrefix stepper (added.length + 1) s inputs := by
  induction inputs generalizing s log with
  | nil => exact ⟨[], by simp [runFrom, StateT.run, pure, StateT.pure], by simp [runFrom, runPrefix, StateT.run, pure, StateT.pure]⟩
  | cons i rest ih =>
    have hs := enabledStep_running (st := st) (stepper := stepper) (fs := fs) s i log h₀
    simp only [runFrom]
    unfold_state
    by_cases hh : (stepper s i).halted.isSome
    · simp only [hh, ↓reduceIte] at hs
      rw [hs]
      refine ⟨[], ?_, ?_⟩ <;> simp [hh, runPrefix, StateT.pure]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte] at hs
      cases he : enabled st fs (stepper s i) with
      | error v =>
        simp only [he] at hs
        rw [hs]
        simp only [hh, Bool.false_eq_true, ↓reduceIte]
        rw [runFrom_stopped _ _ _ rfl]
        refine ⟨[], by simp, ?_⟩
        cases rest <;> simp [runPrefix]
      | ok e =>
        simp only [he] at hs
        rw [hs]
        simp only [hh, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨added, ha, hr⟩ := ih (stepper s i) { log with enabled := log.enabled ++ [e] } h₀
        refine ⟨e :: added, by simp [ha], ?_⟩
        rw [hr]
        simp [runPrefix, hh]

theorem enabled_agrees (inputs : List Step) :
    let r := (runFrom (enabledStep st stepper fs) {} inputs).run {}
    r.1 = runPrefix stepper (r.2.enabled.length + 1) {} inputs := by
  obtain ⟨added, ha, hr⟩ := runFrom_prefix (st := st) (stepper := stepper) (fs := fs) {} inputs {} rfl
  simp only [List.nil_append] at ha
  dsimp only
  rw [ha, hr]

theorem runFrom_unstopped (s : State) (inputs : List Step) (log : EnabledLog) (h₀ : log.stopped = none)
    (h : ((runFrom (enabledStep st stepper fs) s inputs).run log).2.stopped = none) :
    ((runFrom (enabledStep st stepper fs) s inputs).run log).1 = runFrom stepper s inputs := by
  induction inputs generalizing s log with
  | nil => rfl
  | cons i rest ih =>
    have hs := enabledStep_running (st := st) (stepper := stepper) (fs := fs) s i log h₀
    simp only [runFrom] at h ⊢
    unfold_state
    by_cases hh : (stepper s i).halted.isSome
    · simp only [hh, ↓reduceIte] at hs
      rw [hs]
      simp [hh, StateT.pure]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte] at hs
      cases he : enabled st fs (stepper s i) with
      | error v =>
        simp only [he] at hs
        rw [hs] at h
        simp only [hh, Bool.false_eq_true, ↓reduceIte] at h
        rw [runFrom_stopped _ _ _ rfl] at h
        simp at h
      | ok e =>
        simp only [he] at hs
        rw [hs] at h ⊢
        simp only [hh, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ih _ _ h₀ h

theorem enabled_agrees_unstopped (inputs : List Step)
    (h : ((runFrom (enabledStep st stepper fs) {} inputs).run {}).2.stopped = none) :
    ((runFrom (enabledStep st stepper fs) {} inputs).run {}).1 = runFrom stepper {} inputs := by
  exact runFrom_unstopped {} _ {} rfl h

end Tazuna.Thm.Observe.Enabled
