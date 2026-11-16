import Tazuna.Service.Screen.Subscription
import Tazuna.Thm.Service.Chart.Exit

namespace Tazuna.Thm.Service.Screen.Subscription

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

def kept (wanted : List Wanted) (p : Pending) : Bool := (inputOf wanted (p.requester.slot?.getD "")).any (· == p.input)

def matched (opened : List Pending) (w : Wanted) : Bool :=
  opened.any fun p => p.requester.slot? == some w.slot && p.input == w.input

theorem inputOf_some_mem (wanted : List Wanted) (slot : String) (v : Value) (h : inputOf wanted slot = some v) :
    ∃ w ∈ wanted, w.slot = slot ∧ w.input = v := by
  unfold inputOf at h
  cases hf : wanted.find? (·.slot == slot) with
  | none => simp [hf] at h
  | some w =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    exact ⟨w, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

theorem inputOf_of_mem (wanted : List Wanted) (hw : (wanted.map (·.slot)).Nodup) (w : Wanted) (h : w ∈ wanted) :
    inputOf wanted w.slot = some w.input := by
  induction wanted with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hw
    rcases List.mem_cons.mp h with rfl | h
    · simp [inputOf]
    · have hne : x.slot ≠ w.slot := fun e => hw.1 (e ▸ List.mem_map_of_mem (f := (·.slot)) h)
      have ih := ih hw.2 h
      unfold inputOf at ih ⊢
      simp [hne, ih]

theorem endShowStep_fixed (wanted : List Wanted) (owner : String) (t : State)
    (p : Pending) : (t.endShowStep wanted owner p).fixed = t.fixed := by
  dsimp only [State.endShowStep]
  split
  · rfl
  · split <;> rfl

theorem subscribeStep_fixed (opened : List Pending) (owner : String) (t : State)
    (w : Wanted) : (t.subscribeStep opened owner w).fixed = t.fixed := by
  obtain ⟨slot, a, input⟩ := w
  dsimp only [State.subscribeStep]
  split <;> rfl

theorem syncShows_fixed (owner : String) (wanted : List Wanted) :
    (s.syncShows owner wanted).fixed = s.fixed :=
  (foldl_fixed _ (subscribeStep_fixed _ _) _ _).trans (foldl_fixed _ (endShowStep_fixed _ _) _ _)

theorem refresh_fixed (owner : String) : (refresh st fs s owner).fixed = s.fixed := by
  unfold refresh
  split
  · rfl
  · split
    · rfl
    · simp only [id_bind]
      split
      · exact report_fixed ..
      · exact syncShows_fixed _ _

theorem refreshScreens_fixed : (refreshScreens st fs s).fixed = s.fixed := by
  unfold refreshScreens
  rw [foldlM_id]
  exact foldl_fixed _ (fun t i => by
    split
    · rfl
    · exact refresh_fixed _) _ _

theorem endShowStep_grows (wanted : List Wanted) (owner : String) (t : State)
    (p : Pending) : Grows t (t.endShowStep wanted owner p) := by
  dsimp only [State.endShowStep]
  split
  · exact Grows.refl _
  · split
    · exact (endSubscription_grows (s := t) p).trans rfl (Grows.of_lines (s := t.endSubscription p) rfl)
    · exact endSubscription_grows _

theorem subscribeStep_grows (opened : List Pending) (owner : String) (t : State)
    (w : Wanted) : Grows t (t.subscribeStep opened owner w) := by
  obtain ⟨slot, a, input⟩ := w
  dsimp only [State.subscribeStep]
  split
  · exact Grows.refl _
  · exact (grows_write (s := t) Dir.out none _).trans rfl (Grows.of_lines rfl)

theorem syncShows_grows (owner : String) (wanted : List Wanted) :
    Grows s (s.syncShows owner wanted) :=
  (foldl_grows _ (endShowStep_grows _ _) (fun t p => congrArg Fixed.now (endShowStep_fixed _ _ t p)) _ _).trans
    (congrArg Fixed.now (foldl_fixed _ (endShowStep_fixed _ _) _ _))
    (foldl_grows _ (subscribeStep_grows _ _) (fun t w => congrArg Fixed.now (subscribeStep_fixed _ _ t w)) _ _)

theorem refresh_grows (owner : String) : Grows s (refresh st fs s owner) := by
  unfold refresh
  split
  · exact Grows.refl _
  · split
    · exact Grows.refl _
    · simp only [id_bind]
      split
      · exact Grows.of_lines (report_lines ..)
      · exact syncShows_grows _ _

theorem refreshScreens_grows : Grows s (refreshScreens st fs s) := by
  unfold refreshScreens
  rw [foldlM_id]
  refine foldl_grows _ (fun t i => ?_) (fun t i => ?_) _ _
  · split
    · exact Grows.refl _
    · exact refresh_grows _
  · split
    · rfl
    · exact congrArg Fixed.now (refresh_fixed _)

theorem endShowStep_pending (wanted : List Wanted) (owner : String) (t : State) (p : Pending) :
    (t.endShowStep wanted owner p).pending =
      if kept wanted p then t.pending
      else t.pending.map fun q => if q.id == p.id then { q with stale := true } else q := by
  dsimp only [State.endShowStep, kept]
  by_cases hc : ((inputOf wanted (p.requester.slot?.getD "")).any (· == p.input)) = true
  · simp only [hc, ↓reduceIte]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    split <;> rfl

theorem endShows_pending (wanted : List Wanted) (owner : String) :
    ∀ (L : List Pending) (t : State), (L.foldl (State.endShowStep wanted owner) t).pending =
      t.pending.map fun q => if (L.filter fun p => !kept wanted p).any (·.id == q.id) then { q with stale := true } else q := by
  intro L
  induction L with
  | nil => intro t; simp
  | cons p L ih =>
    intro t
    rw [List.foldl_cons, ih, endShowStep_pending]
    by_cases hk : kept wanted p = true
    · simp [hk]
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, List.map_map]
      congr 1
      funext q
      simp only [Function.comp, List.filter_cons, hk, Bool.not_false, ↓reduceIte, List.any_cons]
      by_cases h : q.id = p.id
      · simp [h]
      · by_cases h' : (L.filter fun p => !kept wanted p).any (·.id == q.id) = true
        · simp [h, h']
        · simp [h, h', Ne.symm h]

theorem subscribes_pending (opened : List Pending) (owner : String) :
    ∀ (W : List Wanted) (t : State), ∃ new, (W.foldl (State.subscribeStep opened owner) t).pending = t.pending ++ new ∧
      (∀ q ∈ new, q.requester.machine? = some owner ∧ q.stale = false ∧ ∃ w ∈ W, matched opened w = false ∧
        q.requester.slot? = some w.slot ∧ q.input = w.input) ∧
      (∀ w ∈ W, matched opened w = false → ∃ q ∈ new, q.requester.slot? = some w.slot ∧ q.input = w.input) := by
  intro W
  induction W with
  | nil => intro t; exact ⟨[], by simp, by simp, by simp⟩
  | cons w W ih =>
    intro t
    rw [List.foldl_cons]
    obtain ⟨slot, a, input⟩ := w
    by_cases hm : matched opened ⟨slot, a, input⟩ = true
    · have he : t.subscribeStep opened owner ⟨slot, a, input⟩ = t := by
        dsimp only [State.subscribeStep]
        simp only [matched] at hm
        simp [hm]
      rw [he]
      obtain ⟨new, h₁, h₂, h₃⟩ := ih t
      refine ⟨new, h₁, fun q hq => ?_, fun w hw hu => ?_⟩
      · obtain ⟨h₁, h₂, w, hw, h₄⟩ := h₂ q hq
        exact ⟨h₁, h₂, w, List.mem_cons_of_mem _ hw, h₄⟩
      · rcases List.mem_cons.mp hw with rfl | hw
        · simp [hm] at hu
        · exact h₃ w hw hu
    · have hm' : matched opened ⟨slot, a, input⟩ = false := by simpa using hm
      let q : Pending := { id := (t.write .out none (.subscribe a.target input)).2, activity := a,
                           requester := .slot owner slot, input, turn := t.turn }
      have he : (t.subscribeStep opened owner ⟨slot, a, input⟩).pending = t.pending ++ [q] := by
        dsimp only [State.subscribeStep]
        simp only [matched] at hm'
        simp only [hm', Bool.false_eq_true, ↓reduceIte]
        rfl
      obtain ⟨new, h₁, h₂, h₃⟩ := ih (t.subscribeStep opened owner ⟨slot, a, input⟩)
      refine ⟨q :: new, by rw [h₁, he, List.append_assoc]; rfl, fun r hr => ?_, fun w hw hu => ?_⟩
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨rfl, rfl, ⟨slot, a, input⟩, List.mem_cons_self, hm', rfl, rfl⟩
        · obtain ⟨h₁, h₂, w, hw, h₄⟩ := h₂ r hr
          exact ⟨h₁, h₂, w, List.mem_cons_of_mem _ hw, h₄⟩
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact ⟨q, List.mem_cons_self, rfl, rfl⟩
        · obtain ⟨r, hr, h⟩ := h₃ w hw hu
          exact ⟨r, List.mem_cons_of_mem _ hr, h⟩

theorem kept_stays_open (wanted : List Wanted) (owner : String) (hid : (s.pending.map (·.id)).Nodup) (p : Pending)
    (hp : p ∈ s.openShows owner) (hk : kept wanted p = true) :
    p ∈ ((s.openShows owner).foldl (State.endShowStep wanted owner) s).openShows owner := by
  unfold State.openShows at hp ⊢
  rw [endShows_pending]
  have hmem := (List.mem_filter.mp hp).1
  have hopen := (List.mem_filter.mp hp).2
  have hnot : ((s.pending.filter fun p => p.requester.machine? == some owner && p.requester.slot?.isSome && !p.stale).filter
      fun p => !kept wanted p).any (·.id == p.id) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨q, hq, he⟩ := List.any_eq_true.mp h
    have hq1 := (List.mem_filter.mp hq)
    have hqs := (List.mem_filter.mp hq1.1).1
    have hqp : q = p := nodup_map_inj s.pending hid hqs hmem (by simpa using he)
    subst hqp
    simp [hk] at hq1
  refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨p, hmem, by simp only [hnot, Bool.false_eq_true, ↓reduceIte]⟩, hopen⟩

theorem open_after_end_kept (wanted : List Wanted) (owner : String) (q : Pending)
    (hq : q ∈ ((s.openShows owner).foldl (State.endShowStep wanted owner) s).openShows owner) :
    q ∈ s.openShows owner ∧ kept wanted q = true := by
  unfold State.openShows at hq ⊢
  rw [endShows_pending] at hq
  obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq1
  by_cases hm : ((s.pending.filter fun p => p.requester.machine? == some owner && p.requester.slot?.isSome && !p.stale).filter
      fun p => !kept wanted p).any (·.id == p.id) = true
  · simp only [hm, ↓reduceIte, Bool.not_true, Bool.and_false, Bool.false_eq_true] at hq2
  · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hq2 ⊢
    refine ⟨List.mem_filter.mpr ⟨hp, hq2⟩, ?_⟩
    by_cases hk : kept wanted p = true
    · exact hk
    · exfalso
      apply hm
      exact List.any_eq_true.mpr ⟨p, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hp, hq2⟩, by simpa using hk⟩,
        by simp⟩

theorem syncShows_matches (owner : String) (wanted : List Wanted) (hw : (wanted.map (·.slot)).Nodup)
    (hid : (s.pending.map (·.id)).Nodup) :
    (∀ w ∈ wanted, ∃ p ∈ (s.syncShows owner wanted).openShows owner,
      p.requester.slot? = some w.slot ∧ p.input = w.input) ∧
    (∀ p ∈ (s.syncShows owner wanted).openShows owner, ∃ w ∈ wanted,
      p.requester.slot? = some w.slot ∧ p.input = w.input) := by
  let t := (s.openShows owner).foldl (State.endShowStep wanted owner) s
  obtain ⟨new, hN, hnew, hcover⟩ := subscribes_pending (s.openShows owner) owner wanted t
  have hS : (s.syncShows owner wanted).openShows owner = t.openShows owner ++ new.filter (isOpenShow owner) := by
    show List.filter _ (wanted.foldl _ t).pending = _
    rw [hN, List.filter_append]
    rfl
  rw [hS]
  refine ⟨fun w hwm => ?_, fun p hp => ?_⟩
  · by_cases hm : matched (s.openShows owner) w = true
    · obtain ⟨p, hp, he⟩ := List.any_eq_true.mp hm
      simp only [Bool.and_eq_true, beq_iff_eq] at he
      have hk : kept wanted p = true := by
        unfold kept
        rw [he.1, Option.getD_some, inputOf_of_mem wanted hw w hwm]
        simp [he.2]
      exact ⟨p, List.mem_append_left _ (kept_stays_open wanted owner hid p hp hk), he⟩
    · obtain ⟨q, hq, h⟩ := hcover w hwm (by simpa using hm)
      obtain ⟨hqm, hqs, _⟩ := hnew q hq
      refine ⟨q, List.mem_append_right _ (List.mem_filter.mpr ⟨hq, ?_⟩), h⟩
      simp [isOpenShow, hqm, hqs, h.1]
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨hpo, hk⟩ := open_after_end_kept wanted owner p hp
      unfold kept at hk
      have hsome := (List.mem_filter.mp hpo).2
      simp only [Bool.and_eq_true, beq_iff_eq] at hsome
      obtain ⟨slot, hslot⟩ := Option.isSome_iff_exists.mp hsome.1.2
      rw [hslot, Option.getD_some] at hk
      cases hv : inputOf wanted slot with
      | none => simp [hv] at hk
      | some v =>
        simp only [hv, Option.any_some, beq_iff_eq] at hk
        obtain ⟨w, hw', hs, hi⟩ := inputOf_some_mem wanted slot v hv
        exact ⟨w, hw', by rw [hslot, hs], by rw [hi, hk]⟩
    · obtain ⟨_, _, w, hw', _, h⟩ := hnew p (List.mem_filter.mp hp).1
      exact ⟨w, hw', h⟩

theorem setWanted_nodup (wanted : List Wanted) (w : Wanted)
    (h : (wanted.map (·.slot)).Nodup) : ((setWanted wanted w).map (·.slot)).Nodup := by
  unfold setWanted
  split
  · rw [List.map_map]
    have : ((·.slot) ∘ fun (x : Wanted) => if x.slot == w.slot then w else x) = fun x => x.slot := by
      funext x
      simp only [Function.comp]
      split
      · rename_i he; exact (beq_iff_eq.mp he).symm
      · rfl
    rw [this]
    exact h
  · rename_i hk
    rw [List.map_append, List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb he
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    apply hk
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact List.any_eq_true.mpr ⟨x, hx, by simp [he]⟩

theorem wantedShows_nodup (i : Instance) (wanted : List Wanted) (h : wantedShows st fs s i = .ok wanted) :
    (wanted.map (·.slot)).Nodup := by
  let P : Except Fault (List Wanted) → Prop := fun acc =>
    ∀ w, acc = .ok w → (w.map (·.slot)).Nodup
  have hP : P (wantedShows st fs s i) := by
    unfold wantedShows
    rw [foldlM_id]
    refine foldl_keeps P _ (fun acc cs hacc => ?_) _ _ (fun w hw => by cases hw; exact List.nodup_nil)
    simp only [id_bind]
    split
    · intro w hw; cases hw
    · rename_i wanted
      split
      · intro w hw; cases hw
      · intro w hw
        cases hw
        exact setWanted_nodup _ _ (hacc _ rfl)
  exact hP wanted h

theorem same_input_subscription_kept (owner : String) (wanted : List Wanted) (hw : (wanted.map (·.slot)).Nodup)
    (hid : (s.pending.map (·.id)).Nodup) (p : Pending) (hp : p ∈ s.openShows owner) (slot : String)
    (a : Activity) (hs : p.requester.slot? = some slot) (hin : ⟨slot, a, p.input⟩ ∈ wanted) :
    p ∈ (s.syncShows owner wanted).openShows owner := by
  have hk : kept wanted p = true := by
    unfold kept
    rw [hs, Option.getD_some, inputOf_of_mem wanted hw _ hin]
    simp
  let t := (s.openShows owner).foldl (State.endShowStep wanted owner) s
  obtain ⟨new, hN, _, _⟩ := subscribes_pending (s.openShows owner) owner wanted t
  have hS : (s.syncShows owner wanted).openShows owner = t.openShows owner ++ new.filter (isOpenShow owner) := by
    show List.filter _ (wanted.foldl _ t).pending = _
    rw [hN, List.filter_append]
    rfl
  rw [hS]
  exact List.mem_append_left _ (kept_stays_open wanted owner hid p hp hk)

theorem refresh_open_shows_match (owner : String) (i : Instance) (wanted : List Wanted) (hi : s.machine? owner = some i)
    (hc : i.closed = false) (hw : wantedShows st fs s i = .ok wanted) (hid : (s.pending.map (·.id)).Nodup) :
    (∀ w ∈ wanted, ∃ p ∈ (refresh st fs s owner).openShows owner, p.requester.slot? = some w.slot ∧ p.input = w.input) ∧
    (∀ p ∈ (refresh st fs s owner).openShows owner, ∃ w ∈ wanted, p.requester.slot? = some w.slot ∧ p.input = w.input) := by
  have e : refresh st fs s owner = s.syncShows owner wanted := by
    simp [refresh, hi, hc, hw]
  rw [e]
  exact syncShows_matches owner wanted (wantedShows_nodup i wanted hw) hid

end Tazuna.Thm.Service.Screen.Subscription
