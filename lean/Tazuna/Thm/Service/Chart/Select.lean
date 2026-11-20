import Tazuna.Service.Chart.Select
import Tazuna.Thm.Service.State
import Tazuna.Thm.Service.Functions

namespace Tazuna.Thm.Service.Chart.Select

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Functions Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape
  Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem leaf_selects_innermost (s : State) (extra : Extra) (i : Instance) (ts : List Transition)
    (rest : List (Instance × List Transition)) (t : Transition) (h : choose fs st s i extra ts = .ok (some t)) :
    firstLevel fs st s extra ((i, ts) :: rest) = .ok (some (i.id, t)) := by
  simp [firstLevel, h]

theorem keyed_payload_reaches_matching (chart : Chart) (map : String) (payload : Value) (k : Value)
    (hk : copyKey fs st chart map payload = .ok (.copy k)) (cs : List Instance) (hcs : CopiesOf chart map cs) :
    cs.filter (fun c => reaches fs st c payload matches .ok true) =
      cs.filter (fun c => c.id.key? == some k) := by
  refine List.filter_congr (fun c hc => ?_)
  obtain ⟨hn, hm⟩ := hcs c hc
  simp only [reaches, hm, id_bind, hn, hk, id_pure]
  cases c.id.key? == some k <;> rfl

theorem keyless_payload_reaches_all (chart : Chart) (map : String) (payload : Value)
    (hk : copyKey fs st chart map payload = .ok .everyCopy) (cs : List Instance) (hcs : CopiesOf chart map cs) :
    cs.filter (fun c => reaches fs st c payload matches .ok true) = cs := by
  refine List.filter_eq_self.mpr (fun c hc => ?_)
  obtain ⟨hn, hm⟩ := hcs c hc
  simp [reaches, hn, hm, hk]

theorem keyed_payload_reaches_at_most_one (chart : Chart) (map : String) (payload : Value) (k : Value)
    (hk : copyKey fs st chart map payload = .ok (.copy k)) (cs : List Instance) (hcs : CopiesOf chart map cs)
    (hd : (cs.map (·.id.key?)).Nodup) :
    (cs.filter fun c => reaches fs st c payload matches .ok true).length ≤ 1 := by
  rw [keyed_payload_reaches_matching chart map payload k hk cs hcs]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.nodup_cons] at hd
    have ih' := ih (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hd.2
    simp only [List.filter_cons]
    split
    · rename_i hc
      have : cs.filter (fun c => c.id.key? == some k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro d hdm hd'
        apply hd.1
        simp only [beq_iff_eq] at hc hd'
        exact List.mem_map.mpr ⟨d, hdm, by rw [hc, hd']⟩
      simp [this]
    · exact ih'

theorem removeConflicts_sublist (s : State) (c : Chart) (enabled : List (InstanceId × Transition)) :
    (s.removeConflicts c enabled).Sublist enabled := by
  unfold State.removeConflicts
  have key : ∀ (xs kept pre : List (InstanceId × Transition)), kept.Sublist pre →
      (xs.foldl (fun kept t₁ =>
        let exits := s.exitKeys t₁
        let overlapping := kept.filter fun t₂ => (s.exitKeys t₂).any (· ∈ exits)
        if overlapping.any fun t₂ => !c.tree.isInside t₁.2.source t₂.2.source then kept
        else kept.filter (· ∉ overlapping) ++ [t₁]) kept).Sublist (pre ++ xs) := by
    intro xs
    induction xs with
    | nil => intro kept pre h; simpa using h
    | cons t xs ih =>
      intro kept pre h
      simp only [List.foldl_cons]
      rw [show pre ++ t :: xs = (pre ++ [t]) ++ xs by simp]
      apply ih
      split
      · exact h.trans (List.sublist_append_left _ _)
      · exact (List.filter_sublist.trans h).append (List.Sublist.refl _)
  simpa using key enabled [] [] List.Sublist.slnil

theorem select_follows_leaves (s : State) (top : Instance) (trigger : Spec.Trigger) (extra : Extra)
    (leaves : List (InstanceId × Option String)) (chosen : List (InstanceId × Transition))
    (h : select fs st s top trigger extra leaves = .ok chosen) :
    chosen.Sublist (leaves.filterMap fun l =>
      match pick fs st s top trigger extra l with
      | .ok (some c) => some c
      | _ => none) := by
  let g : InstanceId × Option String → Option (InstanceId × Transition) := fun l =>
    match pick fs st s top trigger extra l with
    | .ok (some c) => some c
    | _ => none
  have key : ∀ (xs pre : List (InstanceId × Option String))
      (acc : Except Fault (List (InstanceId × Transition))),
      (∀ e, acc = .ok e → e.Sublist (pre.filterMap g)) →
      ∀ e, xs.foldlM (m := Id) (fun acc l => do
        match acc with
        | .error v => pure (.error v)
        | .ok enabled =>
          match ← pick fs st s top trigger extra l with
          | .error v => pure (.error v)
          | .ok none => pure (.ok enabled)
          | .ok (some c) => pure (.ok (if enabled.contains c then enabled else enabled ++ [c]))) acc = .ok e →
        e.Sublist ((pre ++ xs).filterMap g) := by
    intro xs
    induction xs with
    | nil => intro pre acc hacc e he; simpa using hacc e he
    | cons l xs ih =>
      intro pre acc hacc e he
      simp only [List.foldlM_cons, id_bind] at he
      rw [show pre ++ l :: xs = (pre ++ [l]) ++ xs by simp]
      refine ih (pre ++ [l]) _ ?_ e he
      intro e' he'
      cases acc with
      | error v => simp at he'
      | ok enabled =>
        simp only at he'
        have hg : g l = match pick fs st s top trigger extra l with | .ok (some c) => some c | _ => none := rfl
        cases hp : pick fs st s top trigger extra l with
        | error v => rw [hp] at he'; cases he'
        | ok o =>
          cases o with
          | none =>
            rw [hp] at he'; cases he'
            rw [hp] at hg
            simpa [List.filterMap_append, hg] using hacc _ rfl
          | some c' =>
            rw [hp] at he'; cases he'
            rw [hp] at hg
            rw [List.filterMap_append, show [l].filterMap g = [c'] by simp [hg]]
            split
            · exact (hacc _ rfl).trans (List.sublist_append_left _ _)
            · exact (hacc _ rfl).append (List.Sublist.refl _)
  unfold select at h
  simp only [id_bind] at h
  revert h
  generalize hfound : List.foldlM (m := Id) _ _ leaves = found
  intro h
  cases found with
  | error v => simp [Except.map] at h
  | ok e =>
    simp only [Except.map, id_pure] at h
    cases h
    exact (removeConflicts_sublist s _ e).trans (by simpa using key leaves [] _ (by intro e he; cases he; simp) e hfound)

theorem select_picked_by_leaf (s : State) (top : Instance) (trigger : Spec.Trigger) (extra : Extra)
    (leaves : List (InstanceId × Option String)) (chosen : List (InstanceId × Transition))
    (h : select fs st s top trigger extra leaves = .ok chosen) :
    ∀ c ∈ chosen, ∃ l ∈ leaves, pick fs st s top trigger extra l = .ok (some c) := by
  intro c hc
  obtain ⟨l, hl, hg⟩ := List.mem_filterMap.mp ((select_follows_leaves s top trigger extra leaves chosen h).subset hc)
  refine ⟨l, hl, ?_⟩
  revert hg
  cases pick fs st s top trigger extra l with
  | error v => simp
  | ok o =>
    cases o with
    | none => simp
    | some c' => intro hg; cases hg; rfl

theorem choose_error_halts (s : State) (i : Instance) (extra : Extra) (ts : List Transition)
    (v : Fault) (h : choose fs st s i extra ts = .error v) : v.halts = true := by
  induction ts with
  | nil => simp [choose] at h
  | cons t rest ih =>
    simp only [choose, id_bind] at h
    split at h
    · rename_i e _
      injection h with h
      rw [← h]
      exact issueViolation_halts_default _ e
    · cases h
    · exact ih h

theorem firstLevel_error_halts (s : State) (extra : Extra) (levels : List (Instance × List Transition))
    (v : Fault) (h : firstLevel fs st s extra levels = .error v) : v.halts = true := by
  induction levels with
  | nil => simp [firstLevel] at h
  | cons l rest ih =>
    simp only [firstLevel, id_bind] at h
    split at h
    · rename_i hc
      injection h with h
      exact choose_error_halts s l.1 extra l.2 v (h ▸ hc)
    · cases h
    · exact ih h

theorem select_error_halts (s : State) (top : Instance) (trigger : Spec.Trigger) (extra : Extra)
    (leaves : List (InstanceId × Option String)) (v : Fault)
    (h : select fs st s top trigger extra leaves = .error v) : v.halts = true := by
  have key : ∀ (xs : List (InstanceId × Option String)) (acc : Except Fault (List (InstanceId × Transition))),
      (∀ w, acc = .error w → w.halts = true) →
      ∀ w, xs.foldlM (m := Id) (fun acc l => do
        match acc with
        | .error v => pure (.error v)
        | .ok enabled =>
          match ← pick fs st s top trigger extra l with
          | .error v => pure (.error v)
          | .ok none => pure (.ok enabled)
          | .ok (some c) => pure (.ok (if enabled.contains c then enabled else enabled ++ [c]))) acc = .error w →
        w.halts = true := by
    intro xs
    induction xs with
    | nil => intro acc hacc w hw; exact hacc w hw
    | cons l xs ih =>
      intro acc hacc w hw
      simp only [List.foldlM_cons, id_bind] at hw
      refine ih _ ?_ w hw
      intro w' hw'
      cases acc with
      | error u => injection hw' with hw'; exact hw' ▸ hacc u rfl
      | ok enabled =>
        simp only at hw'
        cases hp : pick fs st s top trigger extra l with
        | error u =>
          rw [hp] at hw'
          injection hw' with hw'
          subst hw'
          unfold pick at hp
          split at hp
          · cases hp
          · exact firstLevel_error_halts s extra _ u hp
        | ok o => rw [hp] at hw'; cases o <;> cases hw'
  unfold select at h
  simp only [id_bind] at h
  revert h
  generalize hfound : List.foldlM (m := Id) _ _ leaves = found
  intro h
  cases found with
  | error u =>
    simp only [Except.map, id_pure] at h
    injection h with h
    exact h ▸ key leaves _ (fun w hw => by cases hw) u hfound
  | ok e => simp [Except.map] at h

end Tazuna.Thm.Service.Chart.Select
