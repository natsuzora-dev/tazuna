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

theorem descendant_replaces_ancestor (s : State) (c : Chart) (a d : InstanceId × Transition) (x : InstanceId × String)
    (hxa : x ∈ s.exitKeys a) (hxd : x ∈ s.exitKeys d) (hin : c.tree.isInside d.2.source a.2.source = true) :
    s.removeConflicts c [a, d] = [d] := by
  simp only [State.removeConflicts, List.any_filter, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Prod.exists,
      Bool.not_eq_eq_eq_not, Bool.not_true, List.mem_filter, not_and, not_exists, decide_not, List.foldl_cons,
      List.filter_nil, List.any_nil, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, decide_false, Bool.not_false,
      List.nil_append, List.any_cons, hin, Bool.and_false, Bool.or_self, List.mem_cons, or_false, List.foldl_nil,
      List.append_left_eq_self, List.filter_eq_nil_iff, decide_eq_false_iff_not, not_imp, Classical.not_forall,
      Decidable.not_not, forall_eq, true_and]
  exact ⟨x.1, x.2, hxa, hxd⟩

theorem ancestor_after_descendant_dropped (s : State) (c : Chart) (a d : InstanceId × Transition) (x : InstanceId × String)
    (hxa : x ∈ s.exitKeys a) (hxd : x ∈ s.exitKeys d) (hout : c.tree.isInside a.2.source d.2.source = false) :
    s.removeConflicts c [d, a] = [d] := by
  simp only [State.removeConflicts, List.any_filter, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Prod.exists,
      Bool.not_eq_eq_eq_not, Bool.not_true, List.mem_filter, not_and, not_exists, decide_not, List.foldl_cons,
      List.filter_nil, List.any_nil, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, decide_false, Bool.not_false,
      List.nil_append, List.any_cons, hout, Bool.and_true, Bool.or_false, List.mem_cons, or_false, List.foldl_nil,
      ite_eq_left_iff]
  intro h
  exact absurd hxa (h x.1 x.2 hxd)

theorem ancestor_only_without_descendant (s : State) (extra : Extra) (levels : List (Instance × List Transition))
    (h' : InstanceId) (t : Transition) (h : firstLevel fs st s extra levels = .ok (some (h', t))) :
    ∃ k : Nat, (∃ i ts, levels[k]? = some (i, ts) ∧ i.id = h' ∧ choose fs st s i extra ts = .ok (some t)) ∧
      ∀ j < k, ∀ i ts, levels[j]? = some (i, ts) → choose fs st s i extra ts = .ok none := by
  induction levels with
  | nil =>
    simp only [firstLevel, id_pure] at h
    injection h with h
    cases h
  | cons l rest ih =>
    obtain ⟨i, ts⟩ := l
    simp only [firstLevel, id_bind] at h
    split at h
    · cases h
    · rename_i t' ht'
      injection h with h
      injection h with h
      injection h with h₁ h₂
      subst h₂
      exact ⟨0, ⟨i, ts, rfl, h₁, ht'⟩, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · rename_i hn
      obtain ⟨k, ⟨i', ts', hk, hr, hc⟩, hb⟩ := ih h
      refine ⟨k + 1, ⟨i', ts', by simpa using hk, hr, hc⟩, fun j hj i'' ts'' hj' => ?_⟩
      cases j with
      | zero =>
        simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hj'
        obtain ⟨rfl, rfl⟩ := hj'
        exact hn
      | succ j => exact hb j (by omega) i'' ts'' (by simpa using hj')

theorem keyed_payload_reaches_matching (chart map : String) (payload : Value) (k : String)
    (hk : fs.copyKey chart map payload = .ok (some (some k))) (cs : List Instance) (hcs : CopiesOf chart map cs) :
    cs.filter (fun c => reaches fs st c payload matches .ok true) =
      cs.filter (fun c => c.id.key? == some k) := by
  refine List.filter_congr (fun c hc => ?_)
  obtain ⟨hn, co, hco, hm⟩ := hcs c hc
  simp only [reaches, hco, id_bind, hn, hm, hk, id_pure]
  cases c.id.key? == some k <;> rfl

theorem keyless_payload_reaches_all (chart map : String) (payload : Value)
    (hk : fs.copyKey chart map payload = .ok none) (cs : List Instance) (hcs : CopiesOf chart map cs) :
    cs.filter (fun c => reaches fs st c payload matches .ok true) = cs := by
  refine List.filter_eq_self.mpr (fun c hc => ?_)
  obtain ⟨hn, co, hco, hm⟩ := hcs c hc
  simp [reaches, hco, hn, hm, hk]

theorem keyed_payload_reaches_at_most_one (chart map : String) (payload : Value) (k : String)
    (hk : fs.copyKey chart map payload = .ok (some (some k))) (cs : List Instance) (hcs : CopiesOf chart map cs)
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
    simp only [choose] at h
    split at h
    · simp only [id_bind] at h
      split at h
      · rename_i e _
        injection h with h
        rw [← h]
        exact issueViolation_halts_default _ e
      · cases h
      · exact ih h
    · cases h

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

theorem copyLeaves_any (s : State) (reached : List InstanceId) (h : InstanceId) (n : String)
    (ha : ((reached.filterMap fun h => (s.machine? h).map fun ci => (h, ci.chart.tree.leaves ci.active)).lookup h).any
      (n ∈ ·) = true) :
    ∃ ci, s.machine? h = some ci ∧ n ∈ ci.chart.tree.leaves ci.active := by
  induction reached with
  | nil => simp at ha
  | cons r rs ih =>
    cases hm : s.machine? r with
    | none => simp only [List.filterMap_cons, hm, Option.map_none] at ha; exact ih ha
    | some ci =>
      simp only [List.filterMap_cons, hm, Option.map_some, List.lookup] at ha
      split at ha
      · rename_i heq
        have hr : h = r := by simpa using heq
        subst hr
        simp only [Option.any_some, decide_eq_true_eq] at ha
        exact ⟨ci, hm, ha⟩
      · exact ih ha

theorem leavesOf_atomic (s : State) (top : Instance) (reached : List InstanceId) :
    ∀ l ∈ leavesOf s top reached, l.2 = none ∨ ∃ n, l.2 = some n ∧
      (l.1 = top.id ∧ n ∈ top.chart.tree.leaves top.active ∨ ∃ ci, s.machine? l.1 = some ci ∧ n ∈ ci.chart.tree.leaves ci.active) := by
  intro l hl
  unfold leavesOf at hl
  simp only at hl
  split at hl
  · simp only [List.mem_singleton] at hl; subst hl; exact Or.inl rfl
  · obtain ⟨⟨h, n⟩, hm, rfl⟩ := List.mem_map.mp hl
    have ha := (List.mem_filter.mp hm).2
    refine Or.inr ⟨n, rfl, ?_⟩
    by_cases e : h = top.id
    · simp only [e, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at ha
      exact Or.inl ⟨e, ha.1⟩
    · have : (h == top.id) = false := by simpa using e
      simp only [this, Bool.false_eq_true, ↓reduceIte] at ha
      exact Or.inr (copyLeaves_any s reached h n ha)

theorem select_one_per_leaf (s : State) (top : Instance) (trigger : Spec.Trigger) (extra : Extra)
    (leaves : List (InstanceId × Option String)) (chosen : List (InstanceId × Transition))
    (h : select fs st s top trigger extra leaves = .ok chosen) :
    ∃ f : InstanceId × Transition → InstanceId × Option String,
      (∀ c ∈ chosen, f c ∈ leaves) ∧ ∀ c₁ ∈ chosen, ∀ c₂ ∈ chosen, f c₁ = f c₂ → c₁ = c₂ := by
  classical
  have hp := select_picked_by_leaf s top trigger extra leaves chosen h
  let f : InstanceId × Transition → InstanceId × Option String := fun c =>
    if hc : c ∈ chosen then (hp c hc).choose else default
  refine ⟨f, fun c hc => ?_, fun c₁ h₁ c₂ h₂ he => ?_⟩
  · simp only [f, hc, ↓reduceDIte]; exact (hp c hc).choose_spec.1
  · simp only [f, h₁, h₂, ↓reduceDIte] at he
    have hf₁ := (hp c₁ h₁).choose_spec.2
    have hf₂ := (hp c₂ h₂).choose_spec.2
    rw [he, hf₂] at hf₁
    cases hf₁
    rfl

end Tazuna.Thm.Service.Chart.Select
