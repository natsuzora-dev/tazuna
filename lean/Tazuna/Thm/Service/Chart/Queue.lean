import Tazuna.Service.Chart.Queue
import Tazuna.Thm.Service.State

namespace Tazuna.Thm.Service.Chart.Queue

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

/-- Processing `f` relates the state before it to the state after it by `R`. Each tower below is one `R`. -/
def By (R : State → State → Prop) (f : Processing → Id Processing) : Prop := ∀ r, R r.state (f r).1

theorem By.unlessHalted {R : State → State → Prop} (refl : ∀ s, R s s) {f : Processing → Id Processing} (h : By R f) :
    By R (unlessHalted f) := by
  intro r; unfold Service.unlessHalted; split
  · exact refl _
  · exact h r

theorem By.withMachine {R : State → State → Prop} (refl : ∀ s, R s s) {name : InstanceId}
    {f : Instance → Processing → Id Processing} (h : ∀ i, By R (f i)) : By R (withMachine name f) := by
  intro r; unfold Service.withMachine; split
  · exact refl _
  · split
    · exact h _ r
    · exact refl _

theorem By.foldlM {R : State → State → Prop} (refl : ∀ s, R s s) (trans : ∀ a b c, R a b → R b c → R a c) {α : Type}
    {g : α → Processing → Id Processing} (h : ∀ x, By R (g x)) (xs : List α) (r : Processing) :
    R r.state (xs.foldlM (fun r x => g x r) r).1 := by
  rw [foldlM_id]
  induction xs generalizing r with
  | nil => exact refl _
  | cons x xs ih => exact trans _ _ _ (h x r) (ih _)

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

theorem keeps_unlessHalted {f : Processing → Id Processing} (h : Keeps f) : Keeps (unlessHalted f) :=
  By.unlessHalted (R := fun s t => t.fixed = s.fixed) (fun _ => rfl) h

theorem keeps_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing} (h : ∀ i, Keeps (f i)) :
    Keeps (withMachine name f) :=
  By.withMachine (R := fun s t => t.fixed = s.fixed) (fun _ => rfl) h

theorem foldlM_keeps {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, Keeps (g x)) (xs : List α) (r : Processing) :
    (xs.foldlM (fun r x => g x r) r).1.fixed = r.state.fixed :=
  By.foldlM (R := fun s t => t.fixed = s.fixed) (fun _ => rfl) (fun _ _ _ h₁ h₂ => h₂.trans h₁) h xs r

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

theorem sameLines_unlessHalted {f : Processing → Id Processing} (h : SameLines f) : SameLines (unlessHalted f) :=
  By.unlessHalted (R := fun s t => t.lines = s.lines) (fun _ => rfl) h

theorem foldlM_now {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, Keeps (g x)) (xs : List α) (r : Processing) :
    (xs.foldlM (fun r x => g x r) r).1.now = r.state.now := congrArg Fixed.now (foldlM_keeps h xs r)

theorem growsBy_unlessHalted {f : Processing → Id Processing} (h : GrowsBy f) : GrowsBy (unlessHalted f) :=
  By.unlessHalted (R := Grows) Grows.refl h

theorem growsBy_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing} (h : ∀ i, GrowsBy (f i)) :
    GrowsBy (withMachine name f) :=
  By.withMachine (R := Grows) Grows.refl h

theorem sameLines_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing} (h : ∀ i, SameLines (f i)) :
    SameLines (withMachine name f) :=
  By.withMachine (R := fun s t => t.lines = s.lines) (fun _ => rfl) h

theorem foldlM_grows {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, GrowsBy (g x)) (hk : ∀ x, Keeps (g x))
    (xs : List α) (r : Processing) : Grows r.state (xs.foldlM (fun r x => g x r) r).1 := by
  rw [foldlM_id]
  induction xs generalizing r with
  | nil => exact Grows.refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact (h x r).trans ((hk x).now r) (ih _)

theorem foldlM_sameLines {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, SameLines (g x)) (xs : List α) (r : Processing) :
    (xs.foldlM (fun r x => g x r) r).1.lines = r.state.lines :=
  By.foldlM (R := fun s t => t.lines = s.lines) (fun _ => rfl) (fun _ _ _ h₁ h₂ => h₂.trans h₁) h xs r

theorem foldl_run_grows {α : Type} (f : Processing → α → Processing) (h : ∀ r x, Grows r.state (f r x).1)
    (hn : ∀ r x, (f r x).1.now = r.state.now) (xs : List α) (r : Processing) : Grows r.state (xs.foldl f r).1 := by
  induction xs generalizing r with
  | nil => exact Grows.refl _
  | cons x xs ih => simp only [List.foldl_cons]; exact (h r x).trans (hn r x) (ih _)

def DeadlinesShrink (f : Processing → Id Processing) : Prop := ∀ r, ∀ t ∈ (f r).1.deadlines, t ∈ r.state.deadlines

theorem deadlinesShrink_unlessHalted {f : Processing → Id Processing} (h : DeadlinesShrink f) : DeadlinesShrink (unlessHalted f) :=
  By.unlessHalted (R := fun s t => ∀ x ∈ t.deadlines, x ∈ s.deadlines) (fun _ _ h => h) h

theorem deadlinesShrink_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing} (h : ∀ i, DeadlinesShrink (f i)) :
    DeadlinesShrink (withMachine name f) :=
  By.withMachine (R := fun s t => ∀ x ∈ t.deadlines, x ∈ s.deadlines) (fun _ _ h => h) h

theorem foldlM_deadlinesShrink {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, DeadlinesShrink (g x))
    (xs : List α) (r : Processing) : ∀ t ∈ (xs.foldlM (fun r x => g x r) r).1.deadlines, t ∈ r.state.deadlines :=
  By.foldlM (R := fun s t => ∀ x ∈ t.deadlines, x ∈ s.deadlines) (fun _ _ h => h) (fun _ _ _ h₁ h₂ x hx => h₁ x (h₂ x hx)) h xs r

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
    PendingMapped (unlessHalted f) :=
  By.unlessHalted (R := fun s t => ∃ g : Pending → Pending, (∀ p, Marked p (g p)) ∧ t.pending = s.pending.map g)
    (fun _ => ⟨id, Marked.refl, by rw [List.map_id]⟩) h

theorem pendingMapped_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing}
    (h : ∀ i, PendingMapped (f i)) : PendingMapped (withMachine name f) :=
  By.withMachine (R := fun s t => ∃ g : Pending → Pending, (∀ p, Marked p (g p)) ∧ t.pending = s.pending.map g)
    (fun _ => ⟨id, Marked.refl, by rw [List.map_id]⟩) h

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
    MachinesKept (unlessHalted f) :=
  By.unlessHalted (R := fun s t => t.machines.map (·.id) = s.machines.map (·.id)) (fun _ => rfl) h

theorem machinesKept_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing}
    (h : ∀ i, MachinesKept (f i)) : MachinesKept (withMachine name f) :=
  By.withMachine (R := fun s t => t.machines.map (·.id) = s.machines.map (·.id)) (fun _ => rfl) h

theorem foldlM_machinesKept {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, MachinesKept (g x)) (xs : List α)
    (r : Processing) : (xs.foldlM (fun r x => g x r) r).1.machines.map (·.id) = r.state.machines.map (·.id) :=
  By.foldlM (R := fun s t => t.machines.map (·.id) = s.machines.map (·.id)) (fun _ => rfl) (fun _ _ _ h₁ h₂ => h₂.trans h₁) h xs r

theorem setMachine_resources (s : State) (name : InstanceId) (f : Instance → Instance) (hf : ∀ i, (f i).id = i.id) :
    (s.setMachine name f).machines.map (·.id) = s.machines.map (·.id) := by
  simp only [State.setMachine, List.map_map]
  congr 1
  funext i
  simp only [Function.comp]
  split <;> simp [hf]

end Tazuna.Thm.Service.Chart.Queue
