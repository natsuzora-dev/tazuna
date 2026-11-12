import Tazuna.Semantics.Chart.Microstep
import Tazuna.Thm.Semantics.Chart.Deadline
import Tazuna.Thm.Semantics.Chart.Done
import Tazuna.Thm.Semantics.Chart.Request
import Tazuna.Thm.Data.List
import Tazuna.Thm.Syntax.Tree
import Tazuna.Thm.Semantics.Note

namespace Tazuna.Thm.Semantics.Chart.Microstep

open Tazuna.Data Tazuna.Semantics
open Tazuna.Syntax (Tree)
open Tazuna.Thm.Data.Basic Tazuna.Thm.Data.List Tazuna.Thm.Semantics.Note Tazuna.Thm.Semantics.Chart.Deadline Tazuna.Thm.Semantics.Chart.Done Tazuna.Thm.Semantics.Chart.Exit Tazuna.Thm.Semantics.Chart.Queue Tazuna.Thm.Semantics.Chart.Request Tazuna.Thm.Semantics.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Semantics.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem keeps_enterOne (step : Nat) (name n : String) : Keeps (enterOne fs st step name n) := by
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

theorem keeps_enter (step : Nat) (name : String) (targets : List String) : Keeps (enter fs st step name targets) := by
  unfold enter
  apply keeps_withMachine
  intro i r
  exact foldlM_keeps (fun n => keeps_unlessHalted (keeps_enterOne step name n)) _ r

theorem lookup_isSome_iff {β : Type} (e : String × String) :
    ∀ (l : List ((String × String) × β)), (l.lookup e).isSome = true ↔ e ∈ l.map (·.1)
  | [] => by simp
  | (a, b) :: l => by
    by_cases h : e = a
    · subst h; simp
    · have hb : (e == a) = false := by simpa using h
      simp only [List.lookup_cons, hb, List.map_cons, List.mem_cons, h, false_or]
      exact lookup_isSome_iff e l

theorem transitionIndexOf_keys (sets : List (List (String × String))) :
    (transitionIndexOf sets).map (·.1) = sets.flatten := by
  unfold transitionIndexOf
  rw [List.map_flatMap]
  have : ∀ (p : List (String × String) × Nat), (p.1.map (·, p.2)).map (·.1) = p.1 := by
    intro p; simp [List.map_map, Function.comp_def]
  simp only [this]
  rw [List.flatMap_def]
  exact congrArg List.flatten (List.zipIdx_map_fst 0 sets)

theorem indexedInOrder_keys (order : List (String × String)) (sets : List (List (String × String))) :
    (indexedInOrder order (transitionIndexOf sets)).map (·.1) = order.filter (· ∈ sets.flatten) := by
  unfold indexedInOrder
  induction order with
  | nil => rfl
  | cons e rest ih =>
    rw [List.filterMap_cons, List.filter_cons]
    have hk := lookup_isSome_iff e (transitionIndexOf sets)
    rw [transitionIndexOf_keys] at hk
    cases hl : (transitionIndexOf sets).lookup e with
    | none =>
      have : e ∉ sets.flatten := fun h => by have := hk.mpr h; simp [hl] at this
      simp [this, ih]
    | some k =>
      have : e ∈ sets.flatten := hk.mp (by simp [hl])
      simp [this, ih]

theorem exiting_keys (s : State) (order : List (String × String)) (chosen : List (String × Transition)) :
    (indexedInOrder order (transitionIndexOf (chosen.map s.exitPairsOf))).map (·.1) =
      order.filter (· ∈ s.exitPairs chosen) := by
  rw [indexedInOrder_keys, ← List.flatMap_def]
  rfl

theorem entering_keys (s : State) (order : List (String × String)) (chosen : List (String × Transition)) :
    (indexedInOrder order (transitionIndexOf (chosen.map s.entryPairsOf))).map (·.1) =
      order.filter (· ∈ s.entryPairs chosen) := by
  rw [indexedInOrder_keys, ← List.flatMap_def]
  rfl

theorem keeps_microstep (step : Nat) (name : String) (chosen : List (String × Transition)) (extra : Extra) :
    Keeps (microstep fs st step name chosen extra) := by
  unfold microstep
  apply keeps_withMachine
  intro i r
  split
  · rfl
  · simp only [id_bind, note_id, id_pure]
    refine (foldlM_keeps (fun (e : (String × String) × Nat) => keeps_unlessHalted (keeps_enterOne step e.1.1 e.1.2)) _ _).trans ?_
    refine (foldlM_keeps (fun (c : (String × Transition) × Nat) => keeps_unlessHalted (keeps_runAssign c.1.1 _ _ _)) _ _).trans ?_
    refine (foldlM_keeps (fun (e : (String × String) × Nat) =>
      keeps_unlessHalted (keeps_exitOne Limit.exitDepth.max e.1.1 e.1.2)) _ _).trans ?_
    have h0 : ∀ (hs : List String) (f : String → Instance → Instance) (t : State),
        (hs.foldl (fun s h => s.setMachine h (f h)) t).fixed = t.fixed := by
      intro hs f
      induction hs with
      | nil => intro t; rfl
      | cons h hs ih => intro t; exact ih _
    exact h0 _ _ _

theorem growsBy_enterOne (step : Nat) (name n : String) : GrowsBy (enterOne fs st step name n) := by
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

theorem growsBy_enter (step : Nat) (name : String) (targets : List String) : GrowsBy (enter fs st step name targets) := by
  unfold enter
  apply growsBy_withMachine
  intro i r
  exact foldlM_grows (fun n => growsBy_unlessHalted (growsBy_enterOne step name n))
    (fun n => keeps_unlessHalted (keeps_enterOne step name n)) _ r

theorem growsBy_microstep (step : Nat) (name : String) (chosen : List (String × Transition)) (extra : Extra) :
    GrowsBy (microstep fs st step name chosen extra) := by
  unfold microstep
  apply growsBy_withMachine
  intro i r
  split
  · exact Grows.refl _
  · simp only [id_bind, note_id, id_pure]
    have kE : ∀ xs (r : Processing), (List.foldlM (m := Id) (fun r (e : (String × String) × Nat) =>
        unlessHalted (exitOne fs st Limit.exitDepth.max e.1.1 e.1.2) r) r xs).1.fixed = r.state.fixed :=
      foldlM_keeps (fun (e : (String × String) × Nat) => keeps_unlessHalted (keeps_exitOne Limit.exitDepth.max e.1.1 e.1.2))
    have hE : ∀ xs (r : Processing), Grows r.state (List.foldlM (m := Id) (fun r (e : (String × String) × Nat) =>
        unlessHalted (exitOne fs st Limit.exitDepth.max e.1.1 e.1.2) r) r xs).1 :=
      foldlM_grows (fun (e : (String × String) × Nat) => growsBy_unlessHalted (growsBy_exitOne Limit.exitDepth.max e.1.1 e.1.2))
        (fun e => keeps_unlessHalted (keeps_exitOne Limit.exitDepth.max e.1.1 e.1.2))
    have kA : ∀ xs (r : Processing), (List.foldlM (m := Id) (fun r (c : (String × Transition) × Nat) =>
        unlessHalted (runAssign fs st c.1.1 (.transition c.1.2) c.1.2.source extra) r) r xs).1.fixed = r.state.fixed :=
      foldlM_keeps (fun (c : (String × Transition) × Nat) => keeps_unlessHalted (keeps_runAssign c.1.1 _ _ _))
    have hA : ∀ xs (r : Processing), Grows r.state (List.foldlM (m := Id) (fun r (c : (String × Transition) × Nat) =>
        unlessHalted (runAssign fs st c.1.1 (.transition c.1.2) c.1.2.source extra) r) r xs).1 := fun xs r =>
      Grows.of_lines (foldlM_sameLines (fun (c : (String × Transition) × Nat) =>
        sameLines_unlessHalted (sameLines_runAssign c.1.1 _ _ _)) xs r)
    have hN : ∀ xs (r : Processing), Grows r.state (List.foldlM (m := Id) (fun r (e : (String × String) × Nat) =>
        unlessHalted (enterOne fs st step e.1.1 e.1.2) r) r xs).1 :=
      foldlM_grows (fun (e : (String × String) × Nat) => growsBy_unlessHalted (growsBy_enterOne step e.1.1 e.1.2))
        (fun e => keeps_unlessHalted (keeps_enterOne step e.1.1 e.1.2))
    have h0 : ∀ (hs : List String) (f : String → Instance → Instance) (t : State),
        (hs.foldl (fun s h => s.setMachine h (f h)) t).lines = t.lines ∧
          (hs.foldl (fun s h => s.setMachine h (f h)) t).now = t.now := by
      intro hs f
      induction hs with
      | nil => intro t; exact ⟨rfl, rfl⟩
      | cons h hs ih => intro t; exact ih _
    obtain ⟨l0, n0⟩ := h0 (holdersOf chosen) _ r.state
    exact (Grows.of_lines l0).trans n0 ((hE _ _).trans (congrArg Fixed.now (kE _ _))
      ((hA _ _).trans (congrArg Fixed.now (kA _ _)) (hN _ _)))

theorem microstep_order (step : Nat) (name : String) (chosen : List (String × Transition)) (extra : Extra) (r : Processing)
    (i : Instance) (hh : r.state.halted = none) (hi : r.state.machine? name = some i) (hc : i.closed = false) :
    microstep fs st step name chosen extra r =
      let holders := holdersOf chosen
      let exiting := (i.documentOrder.filter (· ∈ r.state.exitPairs chosen)).reverse
      let exited := exiting.foldlM (m := Id) (fun r e => unlessHalted (exitOne fs st Limit.exitDepth.max e.1 e.2) r)
        ⟨holders.foldl (fun s h => s.setMachine h (recordHistory ((exiting.filter (·.1 == h)).map (·.2)))) r.state, r.queue⟩
      let assigned := chosen.foldlM (m := Id)
        (fun r c => unlessHalted (runAssign fs st c.1 (.transition c.2) c.2.source extra) r) exited
      (i.documentOrder.filter (· ∈ assigned.state.entryPairs chosen)).foldlM (m := Id)
        (fun r e => unlessHalted (enterOne fs st step e.1 e.2) r) assigned := by
  have hz : ∀ (g : Processing → String × Transition → Id Processing) (init : Processing),
      chosen.foldlM g init = chosen.zipIdx.foldlM (fun r x => g r x.1) init := by
    intro g init
    rw [← List.zipIdx_map_fst 0 chosen, List.foldlM_map, List.zipIdx_map_fst]
  simp only [microstep, withMachine, Processing.halted, hh, hi, hc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    id_bind, note_id, id_pure]
  rw [← exiting_keys, ← entering_keys, hz]
  simp only [← List.map_reverse, List.foldlM_map, List.filter_map, List.map_map, Function.comp_def]

theorem documentOrder_owner_pairs (i : Instance) (pairs : List (String × String)) :
    (((i.documentOrder.filter (· ∈ pairs)).filter (·.1 == i.resource)).map (·.2)) =
      i.chart.tree.entryOrder ((pairs.filter (·.1 == i.resource)).map (·.2)) := by
  have hc : (i.documentOrder.filter (· ∈ pairs)).filter (·.1 == i.resource) =
      (i.documentOrder.filter (·.1 == i.resource)).filter (· ∈ pairs) := by
    rw [List.filter_filter, List.filter_filter]; congr 1; funext a; exact Bool.and_comm _ _
  rw [hc, documentOrder_owner i]
  rw [Tree.entryOrder, tree_names]
  generalize i.chart.states = l
  induction l with
  | nil => rfl
  | cons cs rest ih =>
    simp only [List.map_cons, List.filter_cons]
    have hm : (cs.name ∈ (pairs.filter (·.1 == i.resource)).map (·.2)) ↔ (i.resource, cs.name) ∈ pairs := by
      simp only [List.mem_map, List.mem_filter, beq_iff_eq]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨hab, rfl⟩, rfl⟩; exact hab
      · intro hp; exact ⟨_, ⟨hp, rfl⟩, rfl⟩
    by_cases hp : (i.resource, cs.name) ∈ pairs <;> simp [hp, hm, ih]

theorem microstep_exits_in_exit_order (s : State) (i : Instance) (chosen : List (String × Transition)) :
    ((((i.documentOrder.filter (· ∈ s.exitPairs chosen)).reverse).filter (·.1 == i.resource)).map (·.2)) =
      i.chart.tree.exitOrder (((s.exitPairs chosen).filter (·.1 == i.resource)).map (·.2)) := by
  rw [List.filter_reverse, List.map_reverse, documentOrder_owner_pairs i _]
  simp only [Tree.entryOrder, Tree.exitOrder, List.filter_reverse]

theorem microstep_enters_in_entry_order (s : State) (i : Instance) (chosen : List (String × Transition)) :
    (((i.documentOrder.filter (· ∈ s.entryPairs chosen)).filter (·.1 == i.resource)).map (·.2)) =
      i.chart.tree.entryOrder (((s.entryPairs chosen).filter (·.1 == i.resource)).map (·.2)) :=
  documentOrder_owner_pairs i _

end Tazuna.Thm.Semantics.Chart.Microstep
