import Tazuna.Service.Chart.Exit
import Tazuna.Thm.Service.Chart.Queue
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Service.Chart.Exit

open Tazuna.Data Tazuna.Service
open Tazuna.Spec (Tree)
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem keeps_runAssign (name : InstanceId) (a : Assignment) (scope : Option String) (extra : Extra)
    (held : Option Value) : Keeps (runAssign fs st name a scope extra held) := by
  unfold runAssign
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  split
  · simp [Processing.report, report_eq, State.fixed]
  · split <;> rfl

theorem keeps_endWith {exit : InstanceId → String → Processing → Id Processing} (h : ∀ c n, Keeps (exit c n))
    (c : InstanceId) : Keeps (endWith exit c) := by
  unfold endWith
  apply keeps_withMachine
  intro ci r
  simp only [id_bind]
  have hf := foldlM_keeps (fun n => keeps_unlessHalted (h c n)) (ci.chart.tree.exitOrder ci.active) r
  split
  · exact hf
  · exact (foldl_fixed (fun t p => State.endSubscription t p) (fun t p => rfl) _ _).trans hf

theorem keeps_leaveWith {exit : InstanceId → String → Processing → Id Processing} (h : ∀ c n, Keeps (exit c n))
    (name : InstanceId) (n : String) : Keeps (leaveWith fs st exit name n) := by
  intro r
  unfold leaveWith
  simp only [id_bind]
  have hc := foldlM_keeps (fun c => keeps_unlessHalted (keeps_endWith h c))
  split
  · exact keeps_runAssign name _ _ _ _ r
  · exact (hc _ _).trans (keeps_runAssign name _ _ _ _ r)

theorem keeps_exitOne (fuel : Nat) (name : InstanceId) (n : String) : Keeps (exitOne fs st fuel name n) := by
  induction fuel generalizing name n with
  | zero => intro r; rfl
  | succ fuel ih =>
    intro r
    rw [exitOne]
    refine keeps_withMachine (fun i r => ?_) r
    simp only [id_bind]
    have h1 := foldlM_keeps (fun c => keeps_unlessHalted (keeps_endWith (fun c n => ih c n) (InstanceId.copy i.id n c)))
      (i.copyKeysOf n).reverse r
    split
    · exact h1
    · exact (keeps_leaveWith (fun c n => ih c n) name n _).trans h1

theorem sameLines_runAssign (name : InstanceId) (a : Assignment) (scope : Option String) (extra : Extra)
    (held : Option Value) : SameLines (runAssign fs st name a scope extra held) := by
  unfold runAssign
  apply sameLines_withMachine
  intro i r
  try simp only [id_bind]
  split
  · simp [Processing.report]
  · split <;> rfl

theorem endSubscription_grows (p : Pending) : Grows s (s.endSubscription p) :=
  ⟨#[_], Array.push_eq_append, by simp⟩

theorem growsBy_endWith {exit : InstanceId → String → Processing → Id Processing} (h : ∀ c n, GrowsBy (exit c n))
    (hk : ∀ c n, Keeps (exit c n)) (c : InstanceId) : GrowsBy (endWith exit c) := by
  unfold endWith
  apply growsBy_withMachine
  intro ci r
  simp only [id_bind]
  have hg := foldlM_grows (fun n => growsBy_unlessHalted (h c n)) (fun n => keeps_unlessHalted (hk c n))
    (ci.chart.tree.exitOrder ci.active) r
  have hn := foldlM_now (fun n => keeps_unlessHalted (hk c n)) (ci.chart.tree.exitOrder ci.active) r
  split
  · exact hg
  · exact hg.trans hn (foldl_grows (fun t p => State.endSubscription t p)
      (fun t p => endSubscription_grows _) (fun t p => rfl) _ _)

theorem growsBy_leaveWith {exit : InstanceId → String → Processing → Id Processing} (h : ∀ c n, GrowsBy (exit c n))
    (hk : ∀ c n, Keeps (exit c n)) (name : InstanceId) (n : String) : GrowsBy (leaveWith fs st exit name n) := by
  intro r
  unfold leaveWith
  simp only [id_bind]
  have gc := foldlM_grows (fun c => growsBy_unlessHalted (growsBy_endWith h hk c))
    (fun c => keeps_unlessHalted (keeps_endWith hk c))
  have ga := sameLines_runAssign (st := st) (fs := fs) name (.exit n) (some n) .none none r
  have na := (keeps_runAssign (st := st) (fs := fs) name (.exit n) (some n) .none none).now r
  split
  · exact Grows.of_lines ga
  · exact (Grows.of_lines ga).trans na ((gc _ _).bridge (by rfl) (by rfl))

theorem growsBy_exitOne (fuel : Nat) (name : InstanceId) (n : String) : GrowsBy (exitOne fs st fuel name n) := by
  induction fuel generalizing name n with
  | zero => intro r; exact Grows.refl _
  | succ fuel ih =>
    intro r
    rw [exitOne]
    refine growsBy_withMachine (fun i r => ?_) r
    simp only [id_bind]
    have hk : ∀ c n, Keeps (exitOne fs st fuel c n) := fun c n => keeps_exitOne fuel c n
    have g1 := foldlM_grows (fun c => growsBy_unlessHalted (growsBy_endWith (fun c n => ih c n) hk (InstanceId.copy i.id n c)))
      (fun c => keeps_unlessHalted (keeps_endWith hk (InstanceId.copy i.id n c))) (i.copyKeysOf n).reverse r
    have n1 := foldlM_now (fun c => keeps_unlessHalted (keeps_endWith hk (InstanceId.copy i.id n c))) (i.copyKeysOf n).reverse r
    split
    · exact g1
    · exact g1.trans n1 ((growsBy_leaveWith (fun c n => ih c n) hk name n _).bridge (by rfl) (by rfl))

theorem foldl_endSubscription_pending (ps : List Pending) (s : State) :
    (ps.foldl (fun s p => s.endSubscription p) s).pending =
      s.pending.map fun q => if ps.any (·.id == q.id) then { q with stale := true } else q := by
  induction ps generalizing s with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih]
    show List.map _ (List.map _ s.pending) = _
    rw [List.map_map]
    congr 1
    funext q
    simp only [Function.comp, List.any_cons]
    by_cases h : q.id = p.id
    · simp [h]
    · by_cases h' : ps.any (·.id == q.id) = true
      · simp [h, h']
      · simp [h, h', Ne.symm h]

@[simp] theorem foldl_endSubscription_machines (ps : List Pending) (s : State) :
    (ps.foldl (fun s p => s.endSubscription p) s).machines = s.machines := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => exact ih _

@[simp] theorem foldl_endSubscription_copies (ps : List Pending) (s : State) :
    (ps.foldl (fun s p => s.endSubscription p) s).copies = s.copies := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => exact ih _

theorem endWith_exits_then_closes (exit : InstanceId → String → Processing → Id Processing) (c : InstanceId) (r : Processing)
    (ci : Instance) (hh : r.state.halted = none) (hi : r.state.machine? c = some ci) :
    endWith exit c r =
      let exited := (ci.chart.tree.exitOrder ci.active).foldlM (m := Id) (fun r n => unlessHalted (exit c n) r) r
      if exited.halted then exited else
      let s := exited.state.setMachine c fun i => { i with closed := true }
      ⟨((s.openShows c).foldl (fun s p => s.endSubscription p) s).removeFromStack c, exited.queue⟩ := by
  simp only [endWith, withMachine, Processing.halted, hh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hi, id_bind]
  rfl

theorem runAssign_deadlines (name : InstanceId) (a : Assignment) (scope : Option String) (extra : Extra)
    (held : Option Value) (r : Processing) : (runAssign fs st name a scope extra held r).1.deadlines = r.state.deadlines := by
  unfold runAssign withMachine
  split
  · rfl
  · split
    · simp only [id_bind]
      split
      · simp [Processing.report, report_eq]
      · split <;> rfl
    · rfl

theorem deadlinesShrink_endWith {exit : InstanceId → String → Processing → Id Processing}
    (h : ∀ c n, DeadlinesShrink (exit c n)) (c : InstanceId) : DeadlinesShrink (endWith exit c) := by
  apply deadlinesShrink_withMachine
  intro ci r t ht
  simp only [id_bind] at ht
  have hf :=
    foldlM_deadlinesShrink (fun n => deadlinesShrink_unlessHalted (h c n)) (ci.chart.tree.exitOrder ci.active) r
  split at ht
  · exact hf t ht
  · have : ∀ (qs : List Pending) (s : State), (qs.foldl (fun s q => s.endSubscription q) s).deadlines
        = s.deadlines := by
      intro qs
      induction qs with
      | nil => intro s; rfl
      | cons q qs ih => intro s; exact ih _
    simp only [id_pure, State.removeFromStack, this] at ht
    exact hf t ht

theorem leave_removes_deadlines {exit : InstanceId → String → Processing → Id Processing} (h : ∀ c n, DeadlinesShrink (exit c n))
    (name : InstanceId) (n : String) (r : Processing) (hh : (leaveWith fs st exit name n r).1.halted = none) :
    ∀ t ∈ (leaveWith fs st exit name n r).1.deadlines, ¬(t.machine = name ∧ t.state = n) := by
  have hc := foldlM_deadlinesShrink (fun c => deadlinesShrink_unlessHalted (deadlinesShrink_endWith h c))
  have key : ∀ (ts : List Deadline), ∀ t ∈ List.filter (fun (t : Deadline) => !(t.machine == name && t.state == n)) ts,
      ¬(t.machine = name ∧ t.state = n) := by
    intro ts t ht he
    have := (List.mem_filter.mp ht).2
    simp [he.1, he.2] at this
  unfold leaveWith at hh ⊢
  simp only [id_bind] at hh ⊢
  split at hh
  · rename_i hr
    simp only [id_pure] at hh
    simp [Processing.halted, hh] at hr
  · rename_i hr
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
    intro t ht
    exact key _ t (hc _ _ t ht)

theorem deadlinesShrink_leaveWith {exit : InstanceId → String → Processing → Id Processing} (h : ∀ c n, DeadlinesShrink (exit c n))
    (name : InstanceId) (n : String) : DeadlinesShrink (leaveWith fs st exit name n) := by
  intro r t ht
  have hc := foldlM_deadlinesShrink (fun c => deadlinesShrink_unlessHalted (deadlinesShrink_endWith h c))
  unfold leaveWith at ht
  simp only [id_bind] at ht
  split at ht
  · simp only [id_pure, runAssign_deadlines] at ht; exact ht
  · have := (List.mem_filter.mp (hc _ _ t ht)).1
    simp only [State.setMachine, runAssign_deadlines] at this
    exact this

theorem deadlinesShrink_exitOne (fuel : Nat) (name : InstanceId) (n : String) : DeadlinesShrink (exitOne fs st fuel name n) := by
  induction fuel generalizing name n with
  | zero => intro r t ht; exact ht
  | succ fuel ih =>
    intro r
    rw [exitOne]
    refine deadlinesShrink_withMachine (fun i r t ht => ?_) r
    simp only [id_bind] at ht
    have h1 := foldlM_deadlinesShrink (fun c => deadlinesShrink_unlessHalted
      (deadlinesShrink_endWith (fun c n => ih c n) (InstanceId.copy i.id n c))) (i.copyKeysOf n).reverse r
    generalize (i.copyKeysOf n).reverse.foldlM (fun r k => unlessHalted (endWith (exitOne fs st fuel) (InstanceId.copy i.id n k)) r) r = X at ht h1
    split at ht
    · exact h1 t ht
    · have h2 := deadlinesShrink_leaveWith (fun c n => ih c n) name n _ t ht
      exact h1 t h2

theorem exit_cancels_deadlines (fuel : Nat) (name : InstanceId) (n : String) (r : Processing) (i : Instance)
    (hi : r.state.machine? name = some i) (hh : (exitOne fs st (fuel + 1) name n r).1.halted = none) :
    ∀ t ∈ (exitOne fs st (fuel + 1) name n r).1.deadlines, ¬(t.machine = name ∧ t.state = n) := by
  rw [exitOne] at hh ⊢
  unfold withMachine at hh ⊢
  split at hh
  · rename_i hr
    simp only [id_pure] at hh
    simp [Processing.halted, hh] at hr
  · rename_i hr
    simp only [hr, Bool.false_eq_true, ↓reduceIte, hi] at hh ⊢
    simp only [id_bind] at hh ⊢
    split at hh
    · rename_i hx
      simp only [id_pure] at hh
      simp [Processing.halted, hh, -List.foldlM_reverse] at hx
    · rename_i hx
      simp only [hx, Bool.false_eq_true, ↓reduceIte] at hh ⊢
      exact leave_removes_deadlines (fun c n => deadlinesShrink_exitOne fuel c n) name n _ hh

theorem runAssign_pending (name : InstanceId) (a : Assignment) (scope : Option String) (extra : Extra)
    (held : Option Value) (r : Processing) : (runAssign fs st name a scope extra held r).1.pending = r.state.pending := by
  unfold runAssign withMachine
  split
  · rfl
  · split
    · simp only [id_bind]
      split
      · simp [Processing.report, report_eq]
      · split <;> rfl
    · rfl

theorem leaveMark_marked (name : InstanceId) (n : String) (q : Pending) : Marked q (leaveMark name n q) := by
  unfold leaveMark
  split
  · exact ⟨rfl, rfl, fun _ => rfl⟩
  · exact Marked.refl q

theorem foldl_endSubscription_mapped (ps : List Pending) (s : State) :
    ∃ g : Pending → Pending, (∀ p, Marked p (g p)) ∧
      (ps.foldl (fun s p => s.endSubscription p) s).pending = s.pending.map g := by
  refine ⟨_, fun q => ?_, foldl_endSubscription_pending ps s⟩
  split
  · exact ⟨rfl, rfl, fun _ => rfl⟩
  · exact Marked.refl q

theorem pendingMapped_runAssign (name : InstanceId) (a : Assignment) (scope : Option String) (extra : Extra)
    (held : Option Value) : PendingMapped (runAssign fs st name a scope extra held) :=
  PendingMapped.of_eq (runAssign_pending name a scope extra held)

theorem pendingMapped_endWith {exit : InstanceId → String → Processing → Id Processing}
    (h : ∀ c n, PendingMapped (exit c n)) (c : InstanceId) : PendingMapped (endWith exit c) := by
  apply pendingMapped_withMachine
  intro ci r
  simp only [id_bind]
  obtain ⟨a, ha, ea⟩ := foldlM_pendingMapped (fun n => pendingMapped_unlessHalted (h c n)) (ci.chart.tree.exitOrder ci.active) r
  split
  · exact ⟨a, ha, ea⟩
  · simp only [id_pure, State.removeFromStack]
    obtain ⟨b, hb, eb⟩ := foldl_endSubscription_mapped (State.openShows _ c) (State.setMachine _ c fun i => { i with closed := true })
    refine ⟨b ∘ a, fun p => (ha p).trans (hb (a p)), ?_⟩
    rw [eb]
    simp only [State.setMachine, ea, List.map_map]

theorem pendingMapped_leaveWith {exit : InstanceId → String → Processing → Id Processing}
    (h : ∀ c n, PendingMapped (exit c n)) (name : InstanceId) (n : String) : PendingMapped (leaveWith fs st exit name n) := by
  intro r
  unfold leaveWith
  simp only [id_bind]
  obtain ⟨a, ha, ea⟩ := pendingMapped_runAssign (st := st) (fs := fs) name (.exit n) (some n) .none none r
  split
  · exact ⟨a, ha, ea⟩
  · obtain ⟨b, hb, eb⟩ := foldlM_pendingMapped (fun c => pendingMapped_unlessHalted (pendingMapped_endWith h c)) _
      ⟨(runAssign fs st name (.exit n) (some n) .none none r).state.leaveState name n, (runAssign fs st name (.exit n) (some n) .none none r).queue⟩
    refine ⟨b ∘ leaveMark name n ∘ a, fun p => (ha p).trans ((leaveMark_marked name n (a p)).trans (hb _)), ?_⟩
    rw [eb]
    simp only [State.leaveState, State.setMachine, ea, List.map_map]

theorem pendingMapped_exitOne (fuel : Nat) (name : InstanceId) (n : String) : PendingMapped (exitOne fs st fuel name n) := by
  induction fuel generalizing name n with
  | zero => exact PendingMapped.of_eq (fun _ => rfl)
  | succ fuel ih =>
    intro r
    rw [exitOne]
    refine pendingMapped_withMachine (fun i r => ?_) r
    simp only [id_bind]
    obtain ⟨a, ha, ea⟩ := foldlM_pendingMapped (fun c => pendingMapped_unlessHalted
      (pendingMapped_endWith (fun c n => ih c n) (InstanceId.copy i.id n c))) (i.copyKeysOf n).reverse r
    dsimp only at ea
    generalize (i.copyKeysOf n).reverse.foldlM (fun r k => unlessHalted (endWith (exitOne fs st fuel) (InstanceId.copy i.id n k)) r) r = X at ea ⊢
    split
    · exact ⟨a, ha, ea⟩
    · obtain ⟨b, hb, eb⟩ := pendingMapped_leaveWith (st := st) (fs := fs) (fun c n => ih c n) name n
        ⟨X.state.setMachine name fun i => { i with copyKeys := i.copyKeys.filter (·.1 != n) }, X.queue⟩
      refine ⟨b ∘ a, fun p => (ha p).trans (hb (a p)), ?_⟩
      rw [eb]
      simp only [State.setMachine, ea, List.map_map]

@[guarantee] theorem leave_makes_requests_stale (fuel : Nat) (name : InstanceId) (n : String) (r : Processing) (p : Pending)
    (hp : p ∈ r.state.pending) (hr : p.requester = .state name n)
    (ha : (runAssign fs st name (.exit n) (some n) .none none r).1.halted = none) :
    ∃ p' ∈ (leaveWith fs st (exitOne fs st fuel) name n r).1.pending, p'.id = p.id ∧ p'.stale = true := by
  have hc := foldlM_pendingMapped (fun c => pendingMapped_unlessHalted
    (pendingMapped_endWith (fun c n => pendingMapped_exitOne (st := st) (fs := fs) fuel c n) c))
  have hmark : (leaveMark name n p).stale = true := by simp [leaveMark, hr]
  unfold leaveWith
  simp only [id_bind]
  simp only [Processing.halted, ha, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  have ha' : p ∈ (runAssign fs st name (.exit n) (some n) .none none r).state.pending := by rw [runAssign_pending]; exact hp
  obtain ⟨p₂, h₂, m₂⟩ := (hc _).kept ⟨(runAssign fs st name (.exit n) (some n) .none none r).state.leaveState name n,
    (runAssign fs st name (.exit n) (some n) .none none r).queue⟩ (leaveMark name n p) (List.mem_map_of_mem ha')
  exact ⟨p₂, h₂, m₂.1.trans (leaveMark_marked name n p).1, m₂.2.2 hmark⟩

@[simp] theorem endSubscription_fixed (p : Pending) : (s.endSubscription p).fixed = s.fixed := rfl

@[simp] theorem foldl_endSubscription_deadlines (ps : List Pending) (s : State) :
    (ps.foldl (fun s p => s.endSubscription p) s).deadlines = s.deadlines := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => exact ih _

theorem machinesKept_runAssign (name : InstanceId) (a : Assignment) (scope : Option String) (extra : Extra)
    (held : Option Value) : MachinesKept (runAssign fs st name a scope extra held) := by
  unfold runAssign
  apply machinesKept_withMachine
  intro i r
  try simp only [id_bind]
  split
  · simp [Processing.report, report_eq]
  · split
    · simp only [id_pure]
      rw [setMachine_resources _ _ _ (by intro _; rfl), setMachine_resources _ _ _ (by intro _; rfl)]
      rfl
    · simp only [id_pure]
      rw [setMachine_resources _ _ _ (by intro _; rfl)]
      rfl

theorem machinesKept_endWith {exit : InstanceId → String → Processing → Id Processing}
    (h : ∀ c n, MachinesKept (exit c n)) (c : InstanceId) : MachinesKept (endWith exit c) := by
  apply machinesKept_withMachine
  intro ci r
  simp only [id_bind]
  have hf := foldlM_machinesKept (fun n => machinesKept_unlessHalted (h c n)) (ci.chart.tree.exitOrder ci.active) r
  split
  · exact hf
  · simp only [id_pure, State.removeFromStack, foldl_endSubscription_machines]
    rw [setMachine_resources _ _ _ (by intro _; rfl)]
    exact hf

theorem machinesKept_leaveWith {exit : InstanceId → String → Processing → Id Processing}
    (h : ∀ c n, MachinesKept (exit c n)) (name : InstanceId) (n : String) : MachinesKept (leaveWith fs st exit name n) := by
  intro r
  unfold leaveWith
  simp only [id_bind]
  have hc := foldlM_machinesKept (fun c => machinesKept_unlessHalted (machinesKept_endWith h c))
  have ha := machinesKept_runAssign (st := st) (fs := fs) name (.exit n) (some n) .none none r
  split
  · exact ha
  · refine (hc _ _).trans ?_
    simp only [State.leaveState]
    rw [setMachine_resources _ _ _ (by intro _; rfl)]
    exact ha

theorem machinesKept_exitOne (fuel : Nat) (name : InstanceId) (n : String) : MachinesKept (exitOne fs st fuel name n) := by
  induction fuel generalizing name n with
  | zero => intro r; rfl
  | succ fuel ih =>
    intro r
    rw [exitOne]
    refine machinesKept_withMachine (fun i r => ?_) r
    simp only [id_bind]
    have h1 := foldlM_machinesKept (fun c => machinesKept_unlessHalted
      (machinesKept_endWith (fun c n => ih c n) (InstanceId.copy i.id n c))) (i.copyKeysOf n).reverse r
    generalize (i.copyKeysOf n).reverse.foldlM (fun r k => unlessHalted (endWith (exitOne fs st fuel) (InstanceId.copy i.id n k)) r) r = X at h1 ⊢
    split
    · exact h1
    · refine (machinesKept_leaveWith (st := st) (fs := fs) (fun c n => ih c n) name n _).trans ?_
      simp only
      rw [setMachine_resources _ _ _ (by intro _; rfl)]
      exact h1

theorem exit_stales_requests (fuel : Nat) (name : InstanceId) (n : String) (r : Processing) (i : Instance)
    (hi : r.state.machine? name = some i) (hh : (exitOne fs st (fuel + 1) name n r).1.halted = none) :
    ∀ p ∈ (exitOne fs st (fuel + 1) name n r).1.pending, p.requester = .state name n → p.stale = true := by
  rw [exitOne] at hh ⊢
  unfold withMachine at hh ⊢
  split at hh
  · rename_i hr
    simp only [id_pure] at hh
    simp [Processing.halted, hh] at hr
  · rename_i hr
    simp only [hr, Bool.false_eq_true, ↓reduceIte, hi] at hh ⊢
    simp only [id_bind] at hh ⊢
    split at hh
    · rename_i hx
      simp only [id_pure] at hh
      simp [Processing.halted, hh, -List.foldlM_reverse] at hx
    · rename_i hx
      simp only [hx, Bool.false_eq_true, ↓reduceIte] at hh ⊢
      generalize (i.copyKeysOf n).reverse.foldlM (fun r k => unlessHalted (endWith (exitOne fs st fuel) (InstanceId.copy i.id n k)) r) r = X at hh ⊢
      unfold leaveWith at hh ⊢
      simp only [id_bind] at hh ⊢
      split at hh
      · rename_i ha
        simp only [id_pure] at hh
        simp [Processing.halted, hh] at ha
      · rename_i ha
        simp only [ha, Bool.false_eq_true, ↓reduceIte]
        intro p hp hr
        obtain ⟨q, hq, mq⟩ := (foldlM_pendingMapped (fun c => pendingMapped_unlessHalted
          (pendingMapped_endWith (fun c n => pendingMapped_exitOne (st := st) (fs := fs) fuel c n) c)) _).marked _ p hp
        obtain ⟨o, -, rfl⟩ := List.mem_map.mp hq
        have mo := (leaveMark_marked name n o).trans mq
        refine mq.2.2 ?_
        have hr' : o.requester = .state name n := by rw [← mo.2.1]; exact hr
        simp [leaveMark, hr']

theorem unlessHalted_foldlM_halted {α : Type} (g : α → Processing → Id Processing) (xs : List α) (r : Processing)
    (hr : r.halted = true) : xs.foldlM (m := Id) (fun r x => unlessHalted (g x) r) r = r := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons, id_bind, unlessHalted, hr, ↓reduceIte]
    exact ih

theorem machine?_isSome_of_mem (s : State) (c : InstanceId) (hm : c ∈ s.machines.map (·.id)) :
    ∃ i, s.machine? c = some i := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
  cases h : s.machine? j.id with
  | none =>
    simp only [State.machine?, List.find?_eq_none] at h
    exact absurd (by simp) (h j (List.mem_append_left _ hj))
  | some i => exact ⟨i, rfl⟩

theorem exits_cancel (c : InstanceId) (ns : List String) (r : Processing) (hm : c ∈ r.state.machines.map (·.id))
    (hn : (ns.foldlM (m := Id) (fun r n => unlessHalted (exitOne fs st st.exitFuel c n) r) r).halted = false) :
    (∀ t ∈ (ns.foldlM (m := Id) (fun r n => unlessHalted (exitOne fs st st.exitFuel c n) r) r).state.deadlines,
      t.machine = c → t.state ∉ ns) ∧
      ∀ p ∈ (ns.foldlM (m := Id) (fun r n => unlessHalted (exitOne fs st st.exitFuel c n) r) r).state.pending,
        ∀ n, p.requester = .state c n → n ∈ ns → p.stale = true := by
  induction ns generalizing r with
  | nil => exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ _ h => (nomatch h)⟩
  | cons x xs ih =>
    simp only [List.foldlM_cons, id_bind] at hn ⊢
    have hr1 : (unlessHalted (exitOne fs st st.exitFuel c x) r).halted = false := by
      cases h1 : (unlessHalted (exitOne fs st st.exitFuel c x) r).halted
      · rfl
      · rw [unlessHalted_foldlM_halted _ _ _ h1] at hn; rw [h1] at hn; cases hn
    have hr0 : r.halted = false := by
      cases h0 : r.halted
      · rfl
      · simp [unlessHalted, h0] at hr1
    have hstep : unlessHalted (exitOne fs st st.exitFuel c x) r = exitOne fs st st.exitFuel c x r := by
      simp [unlessHalted, hr0]
    rw [hstep] at hr1 hn ⊢
    have hm1 : c ∈ (exitOne fs st st.exitFuel c x r).1.machines.map (·.id) := by
      rw [machinesKept_exitOne]; exact hm
    obtain ⟨i, hi⟩ := machine?_isSome_of_mem r.state c hm
    have hh1 : (exitOne fs st st.exitFuel c x r).1.halted = none := by
      simpa [Processing.halted] using hr1
    obtain ⟨iht, ihp⟩ := ih _ hm1 hn
    refine ⟨fun t ht htm hts => ?_, fun p hp hps hpm hpn => ?_⟩
    · rcases List.mem_cons.mp hts with hx | hx
      · exact exit_cancels_deadlines _ c x r i hi hh1 t
          (foldlM_deadlinesShrink (fun n => deadlinesShrink_unlessHalted (deadlinesShrink_exitOne _ c n)) xs _ t ht)
          ⟨htm, hx⟩
      · exact iht t ht htm hx
    · rcases List.mem_cons.mp hpn with hx | hx
      · obtain ⟨q, hq, mq⟩ := (foldlM_pendingMapped (fun n => pendingMapped_unlessHalted (pendingMapped_exitOne _ c n))
          xs).marked _ p hp
        subst hx
        exact mq.2.2 (exit_stales_requests _ c _ r i hi hh1 q hq (mq.2.1 ▸ hpm))
      · exact ihp p hp hps hpm hx

@[guarantee] theorem endWith_cancels_deadlines_and_requests (c : InstanceId) (r : Processing) (ci : Instance) (hh : r.state.halted = none)
    (hi : r.state.machine? c = some ci) (hm : c ∈ r.state.machines.map (·.id))
    (hn : (endWith (exitOne fs st st.exitFuel) c r).1.halted = none)
    (ht : ∀ t ∈ r.state.deadlines, t.machine = c → t.state ∈ ci.chart.tree.exitOrder ci.active)
    (hp : ∀ p ∈ r.state.pending, ∀ n, p.requester = .state c n → p.stale = false → n ∈ ci.chart.tree.exitOrder ci.active) :
    (∀ t ∈ (endWith (exitOne fs st st.exitFuel) c r).1.deadlines, t.machine ≠ c) ∧
      ∀ p ∈ (endWith (exitOne fs st st.exitFuel) c r).1.pending, p.requester.machine? = some c → p.stale = true := by
  rw [endWith_exits_then_closes _ c r ci hh hi] at hn ⊢
  have hT := foldlM_deadlinesShrink (fun n => deadlinesShrink_unlessHalted (deadlinesShrink_exitOne (st := st) (fs := fs) st.exitFuel c n))
    (ci.chart.tree.exitOrder ci.active) r
  have hP := (foldlM_pendingMapped (fun n => pendingMapped_unlessHalted (pendingMapped_exitOne (st := st) (fs := fs) st.exitFuel c n))
    (ci.chart.tree.exitOrder ci.active)).marked r
  generalize hX : List.foldlM (m := Id) (fun r n => unlessHalted (exitOne fs st st.exitFuel c n) r) r
    (ci.chart.tree.exitOrder ci.active) = X at hn hT hP ⊢
  by_cases hx : X.halted = true
  · simp only [hx, ↓reduceIte] at hn
    simp [Processing.halted, hn] at hx
  · have hx' : X.halted = false := by simpa using hx
    obtain ⟨cT, cP⟩ := exits_cancel (st := st) (fs := fs) c (ci.chart.tree.exitOrder ci.active) r hm (hX ▸ hx')
    rw [hX] at cT cP
    simp only [hx, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun t htm he => ?_, fun p hpm he => ?_⟩
    · have htm' : t ∈ X.state.deadlines := by
        simpa [State.removeFromStack, State.setMachine, foldl_endSubscription_deadlines] using htm
      exact cT t htm' he (ht t (hT t htm') he)
    · simp only [State.removeFromStack] at hpm
      rw [foldl_endSubscription_pending] at hpm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpm
      have hqm : q.requester.machine? = some c := by split at he <;> simpa using he
      have hq' : q ∈ X.state.pending := hq
      split
      · rfl
      · rename_i hany
        cases hreq : q.requester with
        | slot m slot =>
          cases hst : q.stale with
          | true => rfl
          | false =>
            exfalso
            apply hany
            rw [List.any_eq_true]
            refine ⟨q, ?_, by simp⟩
            simp only [State.openShows, List.mem_filter]
            have hm' := hqm
            rw [hreq] at hm'
            exact ⟨hq, by simp [hm', hreq, hst, Requester.slot?]⟩
        | state m n =>
          have hmc : m = c := by simpa [hreq, Requester.machine?] using hqm
          subst hmc
          obtain ⟨o, ho, mo⟩ := hP q hq'
          cases hos : o.stale with
          | true => exact mo.2.2 hos
          | false =>
            have hor : o.requester = .state m n := by rw [← mo.2.1]; exact hreq
            exact cP q hq' n hreq (hp o ho n hor hos)
        | automation a => simp [hreq, Requester.machine?] at hqm

@[guarantee] theorem leave_makes_queued_stale (s : State) (name : InstanceId) (n : String) :
    ∀ q ∈ (s.leaveState name n).queued, q.machine = name → q.state = n → q.stale = true := by
  intro q hq hm hs
  simp only [State.leaveState, List.mem_map] at hq
  obtain ⟨o, -, rfl⟩ := hq
  by_cases h : (o.machine == name && o.state == n) = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hm hs ⊢
    simp [hm, hs] at h

end Tazuna.Thm.Service.Chart.Exit
