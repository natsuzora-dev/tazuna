import Tazuna.Service.Chart.Queue
import Tazuna.Thm.Service.State

namespace Tazuna.Thm.Service.Chart.Queue

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

def Keeps (f : Processing → Id Processing) : Prop := ∀ r, (f r).1.fixed = r.state.fixed

theorem Keeps.commandAnswers {f : Processing → Id Processing} (h : Keeps f) (r : Processing) :
    (f r).1.commandAnswers = r.state.commandAnswers := congrArg Fixed.commandAnswers (h r)

theorem Keeps.records {f : Processing → Id Processing} (h : Keeps f) (r : Processing) : (f r).1.records = r.state.records :=
  congrArg Fixed.records (h r)

theorem Keeps.now {f : Processing → Id Processing} (h : Keeps f) (r : Processing) : (f r).1.now = r.state.now :=
  congrArg Fixed.now (h r)

theorem Keeps.started {f : Processing → Id Processing} (h : Keeps f) (r : Processing) : (f r).1.started = r.state.started :=
  congrArg Fixed.started (h r)

theorem Keeps.answers {f : Processing → Id Processing} (h : Keeps f) (r : Processing) : (f r).1.answers = r.state.answers :=
  congrArg Fixed.answers (h r)

theorem keeps_unlessHalted {f : Processing → Id Processing} (h : Keeps f) : Keeps (unlessHalted f) := by
  intro r
  unfold unlessHalted
  split
  · rfl
  · exact h r

theorem keeps_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing} (h : ∀ i, Keeps (f i)) :
    Keeps (withMachine name f) := by
  intro r
  unfold withMachine
  split
  · rfl
  · split
    · exact h _ r
    · rfl

theorem foldlM_keeps {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, Keeps (g x)) (xs : List α) (r : Processing) :
    (xs.foldlM (fun r x => g x r) r).1.fixed = r.state.fixed := by
  rw [foldlM_id]
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih, h x r]

theorem foldl_fixed' {α : Type} (f : Processing → α → Processing) (h : ∀ r x, (f r x).1.fixed = r.state.fixed) (xs : List α)
    (r : Processing) : (xs.foldl f r).1.fixed = r.state.fixed := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih, h]

theorem foldl_pair_keeps {α : Type} (f : Processing × Bool → α → Processing × Bool)
    (h : ∀ acc x, (f acc x).1.1.fixed = acc.1.state.fixed) (xs : List α) (acc : Processing × Bool) :
    (xs.foldl f acc).1.1.fixed = acc.1.state.fixed := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih, h]

def GrowsBy (f : Processing → Id Processing) : Prop := ∀ r, Grows r.state (f r).1

theorem Grows.comp {f g : Processing → Id Processing} (hf : GrowsBy f) (hk : Keeps f) (hg : GrowsBy g) (r : Processing) :
    Grows r.state (g (f r)).1 :=
  (hf r).trans (hk.now r) (hg (f r))

def SameLines (f : Processing → Id Processing) : Prop := ∀ r, (f r).1.lines = r.state.lines

theorem SameLines.grows {f : Processing → Id Processing} (h : SameLines f) : GrowsBy f := fun r => Grows.of_lines (h r)

theorem Grows.after {f : Processing → Id Processing} (hf : GrowsBy f) {r r' : Processing} (hl : r'.state.lines = r.state.lines)
    (hn : r'.state.now = r.state.now) : Grows r.state (f r').1 :=
  (Grows.of_lines hl).trans hn (hf r')

theorem sameLines_unlessHalted {f : Processing → Id Processing} (h : SameLines f) : SameLines (unlessHalted f) := by
  intro r
  unfold unlessHalted
  split
  · rfl
  · exact h r

theorem foldlM_now {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, Keeps (g x)) (xs : List α) (r : Processing) :
    (xs.foldlM (fun r x => g x r) r).1.now = r.state.now := congrArg Fixed.now (foldlM_keeps h xs r)

theorem growsBy_unlessHalted {f : Processing → Id Processing} (h : GrowsBy f) : GrowsBy (unlessHalted f) := by
  intro r
  unfold unlessHalted
  split
  · exact Grows.refl _
  · exact h r

theorem growsBy_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing} (h : ∀ i, GrowsBy (f i)) :
    GrowsBy (withMachine name f) := by
  intro r
  unfold withMachine
  split
  · exact Grows.refl _
  · split
    · exact h _ r
    · exact Grows.refl _

theorem sameLines_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing} (h : ∀ i, SameLines (f i)) :
    SameLines (withMachine name f) := by
  intro r
  unfold withMachine
  split
  · rfl
  · split
    · exact h _ r
    · rfl

theorem foldlM_grows {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, GrowsBy (g x)) (hk : ∀ x, Keeps (g x))
    (xs : List α) (r : Processing) : Grows r.state (xs.foldlM (fun r x => g x r) r).1 := by
  rw [foldlM_id]
  induction xs generalizing r with
  | nil => exact Grows.refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact (h x r).trans ((hk x).now r) (ih _)

theorem foldlM_sameLines {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, SameLines (g x)) (xs : List α) (r : Processing) :
    (xs.foldlM (fun r x => g x r) r).1.lines = r.state.lines := by
  rw [foldlM_id]
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih, h x r]

theorem foldl_run_grows {α : Type} (f : Processing → α → Processing) (h : ∀ r x, Grows r.state (f r x).1)
    (hn : ∀ r x, (f r x).1.now = r.state.now) (xs : List α) (r : Processing) : Grows r.state (xs.foldl f r).1 := by
  induction xs generalizing r with
  | nil => exact Grows.refl _
  | cons x xs ih => simp only [List.foldl_cons]; exact (h r x).trans (hn r x) (ih _)

def DeadlinesShrink (f : Processing → Id Processing) : Prop := ∀ r, ∀ t ∈ (f r).1.deadlines, t ∈ r.state.deadlines

theorem deadlinesShrink_unlessHalted {f : Processing → Id Processing} (h : DeadlinesShrink f) : DeadlinesShrink (unlessHalted f) := by
  intro r t ht
  unfold unlessHalted at ht
  split at ht
  · exact ht
  · exact h r t ht

theorem deadlinesShrink_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing} (h : ∀ i, DeadlinesShrink (f i)) :
    DeadlinesShrink (withMachine name f) := by
  intro r t ht
  unfold withMachine at ht
  split at ht
  · exact ht
  · split at ht
    · exact h _ r t ht
    · exact ht

theorem foldlM_deadlinesShrink {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, DeadlinesShrink (g x))
    (xs : List α) (r : Processing) : ∀ t ∈ (xs.foldlM (fun r x => g x r) r).1.deadlines, t ∈ r.state.deadlines := by
  rw [foldlM_id]
  induction xs generalizing r with
  | nil => intro t ht; exact ht
  | cons x xs ih =>
    intro t ht
    simp only [List.foldl_cons] at ht
    exact h x r t (ih _ t ht)

def Marked (p p' : Pending) : Prop :=
  p'.id = p.id ∧ p'.requester = p.requester ∧ (p.stale = true → p'.stale = true)

theorem Marked.refl (p : Pending) : Marked p p := ⟨rfl, rfl, id⟩

theorem Marked.trans {p q r : Pending} (h₁ : Marked p q) (h₂ : Marked q r) : Marked p r :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun h => h₂.2.2 (h₁.2.2 h)⟩

def PendingMapped (f : Processing → Id Processing) : Prop :=
  ∀ r, ∃ g : Pending → Pending, (∀ p, Marked p (g p)) ∧ (f r).1.pending = r.state.pending.map g

theorem PendingMapped.of_eq {f : Processing → Id Processing} (h : ∀ r, (f r).1.pending = r.state.pending) :
    PendingMapped f := fun r => ⟨id, Marked.refl, by rw [h, List.map_id]⟩

theorem PendingMapped.kept {f : Processing → Id Processing} (h : PendingMapped f) (r : Processing) (p : Pending)
    (hp : p ∈ r.state.pending) : ∃ p' ∈ (f r).1.pending, Marked p p' := by
  obtain ⟨g, hg, he⟩ := h r
  exact ⟨g p, he ▸ List.mem_map_of_mem hp, hg p⟩

theorem PendingMapped.marked {f : Processing → Id Processing} (h : PendingMapped f) (r : Processing) :
    ∀ p' ∈ (f r).1.pending, ∃ p ∈ r.state.pending, Marked p p' := by
  obtain ⟨g, hg, he⟩ := h r
  intro p' hp'
  rw [he] at hp'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
  exact ⟨p, hp, hg p⟩

theorem PendingMapped.comp {f g : Processing → Id Processing} (hf : PendingMapped f) (hg : PendingMapped g) :
    PendingMapped (fun r => g (f r)) := by
  intro r
  obtain ⟨a, ha, ea⟩ := hf r
  obtain ⟨b, hb, eb⟩ := hg (f r)
  exact ⟨b ∘ a, fun p => (ha p).trans (hb (a p)), by simp only [eb, ea, List.map_map]⟩

theorem pendingMapped_unlessHalted {f : Processing → Id Processing} (h : PendingMapped f) :
    PendingMapped (unlessHalted f) := by
  intro r
  unfold unlessHalted
  split
  · exact PendingMapped.of_eq (fun _ => rfl) r
  · exact h r

theorem pendingMapped_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing}
    (h : ∀ i, PendingMapped (f i)) : PendingMapped (withMachine name f) := by
  intro r
  unfold withMachine
  split
  · exact PendingMapped.of_eq (fun _ => rfl) r
  · split
    · exact h _ r
    · exact PendingMapped.of_eq (fun _ => rfl) r

theorem foldlM_pendingMapped {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, PendingMapped (g x))
    (xs : List α) : PendingMapped (fun r => xs.foldlM (fun r x => g x r) r) := by
  induction xs with
  | nil => exact PendingMapped.of_eq (fun _ => rfl)
  | cons x xs ih =>
    intro r
    simp only [List.foldlM_cons, id_bind]
    exact (h x).comp ih r

def MachinesKept (f : Processing → Id Processing) : Prop :=
  ∀ r, (f r).1.machines.map (·.id) = r.state.machines.map (·.id)

theorem machinesKept_unlessHalted {f : Processing → Id Processing} (h : MachinesKept f) :
    MachinesKept (unlessHalted f) := by
  intro r
  unfold unlessHalted
  split
  · rfl
  · exact h r

theorem machinesKept_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing}
    (h : ∀ i, MachinesKept (f i)) : MachinesKept (withMachine name f) := by
  intro r
  unfold withMachine
  split
  · rfl
  · split
    · exact h _ r
    · rfl

theorem foldlM_machinesKept {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, MachinesKept (g x)) (xs : List α)
    (r : Processing) : (xs.foldlM (fun r x => g x r) r).1.machines.map (·.id) = r.state.machines.map (·.id) := by
  rw [foldlM_id]
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact (ih _).trans (h x r)

theorem setMachine_resources (s : State) (name : InstanceId) (f : Instance → Instance) (hf : ∀ i, (f i).id = i.id) :
    (s.setMachine name f).machines.map (·.id) = s.machines.map (·.id) := by
  simp only [State.setMachine, List.map_map]
  congr 1
  funext i
  simp only [Function.comp]
  split <;> simp [hf]

end Tazuna.Thm.Service.Chart.Queue
