import Tazuna.Service.Chart.Microstep
import Tazuna.Thm.Service.Chart.Deadline
import Tazuna.Thm.Service.Chart.Done
import Tazuna.Thm.Service.Chart.Request
import Tazuna.Thm.Data.List
import Tazuna.Thm.Spec.Tree
import Tazuna.Thm.Service.Note

namespace Tazuna.Thm.Service.Chart.Microstep

open Tazuna.Data Tazuna.Service
open Tazuna.Spec (Tree)
open Tazuna.Thm.Data.Basic Tazuna.Thm.Data.List Tazuna.Thm.Service.Note Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem keeps_enterOne (step : Nat) (name : InstanceId) (n : String) : Keeps (enterOne fs st step name n) := by
  unfold enterOne
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  have ha := keeps_runAssign (st := st) (fs := fs) name (.entry n) (some n) .none
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩
  split
  · exact ha
  · split
    · exact ha
    · split
      · split
        · split
          · exact (keeps_closeFinal st step name _).trans ha
          · exact (keeps_endWith (fun c n => keeps_exitOne Limit.exitDepth.max c n) name _).trans ha
        · simp only [id_pure, enterFinal_fixed]; exact ha
      · exact (addDeadlines_fixed _ _ _).trans ha

theorem keeps_enter (step : Nat) (name : InstanceId) (targets : List String) : Keeps (enter fs st step name targets) := by
  unfold enter
  apply keeps_withMachine
  intro i r
  exact foldlM_keeps (fun n => keeps_unlessHalted (keeps_enterOne step name n)) _ r

theorem keeps_microstep (step : Nat) (name : InstanceId) (chosen : List (InstanceId × Transition)) (extra : Extra) :
    Keeps (microstep fs st step name chosen extra) := by
  unfold microstep
  apply keeps_withMachine
  intro i r
  split
  · rfl
  · simp only [id_bind, note_id, id_pure]
    refine (foldlM_keeps (fun (e : (InstanceId × String) × Nat) => keeps_unlessHalted (keeps_enterOne step e.1.1 e.1.2)) _ _).trans ?_
    refine (foldlM_keeps (fun (c : (InstanceId × Transition) × Nat) => keeps_unlessHalted (keeps_runAssign c.1.1 _ _ _)) _ _).trans ?_
    refine (foldlM_keeps (fun (e : (InstanceId × String) × Nat) =>
      keeps_unlessHalted (keeps_exitOne Limit.exitDepth.max e.1.1 e.1.2)) _ _).trans ?_
    have h0 : ∀ (hs : List InstanceId) (f : InstanceId → Instance → Instance) (t : State),
        (hs.foldl (fun s h => s.setMachine h (f h)) t).fixed = t.fixed := by
      intro hs f
      induction hs with
      | nil => intro t; rfl
      | cons h hs ih => intro t; exact ih _
    exact h0 _ _ _

theorem growsBy_enterOne (step : Nat) (name : InstanceId) (n : String) : GrowsBy (enterOne fs st step name n) := by
  unfold enterOne
  apply growsBy_withMachine
  intro i r
  try simp only [id_bind]
  have ha := sameLines_runAssign (st := st) (fs := fs) name (.entry n) (some n) .none
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩
  have hn := (keeps_runAssign (st := st) (fs := fs) name (.entry n) (some n) .none).now
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩
  split
  · exact Grows.of_lines ha
  · split
    · exact Grows.of_lines ha
    · split
      · split
        · split
          · exact (Grows.of_lines ha).trans hn (growsBy_closeFinal st step name _)
          · exact (Grows.of_lines ha).trans hn (growsBy_endWith (fun c n => growsBy_exitOne Limit.exitDepth.max c n)
              (fun c n => keeps_exitOne Limit.exitDepth.max c n) name _)
        · simp only [id_pure]; exact Grows.of_lines ((enterFinal_lines _ _ _ _).trans ha)
      · exact Grows.of_lines ((addDeadlines_lines _ _ _).trans ha)

theorem growsBy_enter (step : Nat) (name : InstanceId) (targets : List String) : GrowsBy (enter fs st step name targets) := by
  unfold enter
  apply growsBy_withMachine
  intro i r
  exact foldlM_grows (fun n => growsBy_unlessHalted (growsBy_enterOne step name n))
    (fun n => keeps_unlessHalted (keeps_enterOne step name n)) _ r

theorem growsBy_microstep (step : Nat) (name : InstanceId) (chosen : List (InstanceId × Transition)) (extra : Extra) :
    GrowsBy (microstep fs st step name chosen extra) := by
  unfold microstep
  apply growsBy_withMachine
  intro i r
  split
  · exact Grows.refl _
  · simp only [id_bind, note_id, id_pure]
    have kE : ∀ xs (r : Processing), (List.foldlM (m := Id) (fun r (e : (InstanceId × String) × Nat) =>
        unlessHalted (exitOne fs st Limit.exitDepth.max e.1.1 e.1.2) r) r xs).1.fixed = r.state.fixed :=
      foldlM_keeps (fun (e : (InstanceId × String) × Nat) => keeps_unlessHalted (keeps_exitOne Limit.exitDepth.max e.1.1 e.1.2))
    have hE : ∀ xs (r : Processing), Grows r.state (List.foldlM (m := Id) (fun r (e : (InstanceId × String) × Nat) =>
        unlessHalted (exitOne fs st Limit.exitDepth.max e.1.1 e.1.2) r) r xs).1 :=
      foldlM_grows (fun (e : (InstanceId × String) × Nat) => growsBy_unlessHalted (growsBy_exitOne Limit.exitDepth.max e.1.1 e.1.2))
        (fun e => keeps_unlessHalted (keeps_exitOne Limit.exitDepth.max e.1.1 e.1.2))
    have kA : ∀ xs (r : Processing), (List.foldlM (m := Id) (fun r (c : (InstanceId × Transition) × Nat) =>
        unlessHalted (runAssign fs st c.1.1 (.transition c.1.2) c.1.2.source extra) r) r xs).1.fixed = r.state.fixed :=
      foldlM_keeps (fun (c : (InstanceId × Transition) × Nat) => keeps_unlessHalted (keeps_runAssign c.1.1 _ _ _))
    have hA : ∀ xs (r : Processing), Grows r.state (List.foldlM (m := Id) (fun r (c : (InstanceId × Transition) × Nat) =>
        unlessHalted (runAssign fs st c.1.1 (.transition c.1.2) c.1.2.source extra) r) r xs).1 := fun xs r =>
      Grows.of_lines (foldlM_sameLines (fun (c : (InstanceId × Transition) × Nat) =>
        sameLines_unlessHalted (sameLines_runAssign c.1.1 _ _ _)) xs r)
    have hN : ∀ xs (r : Processing), Grows r.state (List.foldlM (m := Id) (fun r (e : (InstanceId × String) × Nat) =>
        unlessHalted (enterOne fs st step e.1.1 e.1.2) r) r xs).1 :=
      foldlM_grows (fun (e : (InstanceId × String) × Nat) => growsBy_unlessHalted (growsBy_enterOne step e.1.1 e.1.2))
        (fun e => keeps_unlessHalted (keeps_enterOne step e.1.1 e.1.2))
    have h0 : ∀ (hs : List InstanceId) (f : InstanceId → Instance → Instance) (t : State),
        (hs.foldl (fun s h => s.setMachine h (f h)) t).lines = t.lines ∧
          (hs.foldl (fun s h => s.setMachine h (f h)) t).now = t.now := by
      intro hs f
      induction hs with
      | nil => intro t; exact ⟨rfl, rfl⟩
      | cons h hs ih => intro t; exact ih _
    obtain ⟨l0, n0⟩ := h0 (holdersOf chosen) _ r.state
    exact (Grows.of_lines l0).trans n0 ((hE _ _).trans (congrArg Fixed.now (kE _ _))
      ((hA _ _).trans (congrArg Fixed.now (kA _ _)) (hN _ _)))

theorem documentOrder_owner_pairs (i : Instance) (pairs : List (InstanceId × String)) :
    (((i.documentOrder.filter (· ∈ pairs)).filter (·.1 == i.id)).map (·.2)) =
      i.chart.tree.entryOrder ((pairs.filter (·.1 == i.id)).map (·.2)) := by
  have hc : (i.documentOrder.filter (· ∈ pairs)).filter (·.1 == i.id) =
      (i.documentOrder.filter (·.1 == i.id)).filter (· ∈ pairs) := by
    rw [List.filter_filter, List.filter_filter]; congr 1; funext a; exact Bool.and_comm _ _
  rw [hc, documentOrder_owner i]
  rw [Tree.entryOrder, tree_names]
  generalize i.chart.states = l
  induction l with
  | nil => rfl
  | cons cs rest ih =>
    simp only [List.map_cons, List.filter_cons]
    have hm : (cs.name ∈ (pairs.filter (·.1 == i.id)).map (·.2)) ↔ (i.id, cs.name) ∈ pairs := by
      simp only [List.mem_map, List.mem_filter, beq_iff_eq]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨hab, rfl⟩, rfl⟩; exact hab
      · intro hp; exact ⟨_, ⟨hp, rfl⟩, rfl⟩
    by_cases hp : (i.id, cs.name) ∈ pairs <;> simp [hp, hm, ih]

theorem microstep_exits_in_exit_order (s : State) (i : Instance) (chosen : List (InstanceId × Transition)) :
    ((((i.documentOrder.filter (· ∈ s.exitPairs chosen)).reverse).filter (·.1 == i.id)).map (·.2)) =
      i.chart.tree.exitOrder (((s.exitPairs chosen).filter (·.1 == i.id)).map (·.2)) := by
  rw [List.filter_reverse, List.map_reverse, documentOrder_owner_pairs i _]
  simp only [Tree.entryOrder, Tree.exitOrder, List.filter_reverse]

theorem microstep_enters_in_entry_order (s : State) (i : Instance) (chosen : List (InstanceId × Transition)) :
    (((i.documentOrder.filter (· ∈ s.entryPairs chosen)).filter (·.1 == i.id)).map (·.2)) =
      i.chart.tree.entryOrder (((s.entryPairs chosen).filter (·.1 == i.id)).map (·.2)) :=
  documentOrder_owner_pairs i _

end Tazuna.Thm.Service.Chart.Microstep
