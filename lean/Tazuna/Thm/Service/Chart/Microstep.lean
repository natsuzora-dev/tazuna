import Tazuna.Service.Chart.Microstep
import Tazuna.Thm.Service.Chart.Deadline
import Tazuna.Thm.Service.Chart.Done
import Tazuna.Thm.Service.Chart.Request
import Tazuna.Thm.Data.List
import Tazuna.Thm.Spec.Tree
import Tazuna.Thm.Service.Note
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Service.Chart.Microstep

open Tazuna.Data Tazuna.Service
open Tazuna.Spec (Tree)
open Tazuna.Thm.Data.Basic Tazuna.Thm.Data.List Tazuna.Thm.Service.Note Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem keeps_fillHeld (name : InstanceId) (n : String) (edge : Edge) (scope : Option String) (held : Option Value)
    (extra : Extra) : Keeps (fillHeld fs st name n edge scope held extra) := by
  unfold fillHeld
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  split
  · simp [Processing.report, report_eq, State.fixed]
  · rfl

theorem sameLines_fillHeld (name : InstanceId) (n : String) (edge : Edge) (scope : Option String)
    (held : Option Value) (extra : Extra) : SameLines (fillHeld fs st name n edge scope held extra) := by
  unfold fillHeld
  apply sameLines_withMachine
  intro i r
  try simp only [id_bind]
  split
  · simp [Processing.report]
  · rfl

theorem keeps_fillByTransition (c : InstanceId × Transition) (entered : List (InstanceId × String)) (held : Value)
    (extra : Extra) : Keeps (fillByTransition fs st c entered held extra) := by
  unfold fillByTransition
  apply keeps_withMachine
  intro i r
  split
  · rfl
  · dsimp only
    split
    · exact keeps_fillHeld _ _ _ _ _ _ r
    · rfl

theorem sameLines_fillByTransition (c : InstanceId × Transition) (entered : List (InstanceId × String)) (held : Value)
    (extra : Extra) : SameLines (fillByTransition fs st c entered held extra) := by
  unfold fillByTransition
  apply sameLines_withMachine
  intro i r
  split
  · rfl
  · dsimp only
    split
    · exact sameLines_fillHeld _ _ _ _ _ _ r
    · rfl

theorem keeps_fillByInitial (filled : Bool) (name : InstanceId) (n : String) :
    Keeps (fillByInitial fs st filled name n) := by
  unfold fillByInitial
  apply keeps_withMachine
  intro i r
  split
  · split
    · split
      · exact keeps_fillHeld _ _ _ _ _ _ r
      · rfl
    · rfl
  · rfl

theorem sameLines_fillByInitial (filled : Bool) (name : InstanceId) (n : String) :
    SameLines (fillByInitial fs st filled name n) := by
  unfold fillByInitial
  apply sameLines_withMachine
  intro i r
  split
  · split
    · split
      · exact sameLines_fillHeld _ _ _ _ _ _ r
      · rfl
    · rfl
  · rfl

theorem keeps_transitionContent (extra : Extra) (sourceHeld : List Value) (entries : List (List (InstanceId × String)))
    (ck : (InstanceId × Transition) × Nat) : Keeps (fun r => transitionContent fs st extra sourceHeld entries r ck) := by
  intro r
  simp only [transitionContent, id_bind, note_id]
  exact (keeps_unlessHalted (keeps_runAssign _ _ _ _ _) _).trans (keeps_unlessHalted (keeps_fillByTransition _ _ _ _) r)

theorem sameLines_transitionContent (extra : Extra) (sourceHeld : List Value)
    (entries : List (List (InstanceId × String))) (ck : (InstanceId × Transition) × Nat) :
    SameLines (fun r => transitionContent fs st extra sourceHeld entries r ck) := by
  intro r
  simp only [transitionContent, id_bind, note_id]
  exact (sameLines_unlessHalted (sameLines_runAssign _ _ _ _ _) _).trans
    (sameLines_unlessHalted (sameLines_fillByTransition _ _ _ _) r)

theorem keeps_enterOne (step : Nat) (filled : Bool) (name : InstanceId) (n : String) :
    Keeps (enterOne fs st step filled name n) := by
  unfold enterOne
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  have hF := keeps_fillByInitial (st := st) (fs := fs) filled name n
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩
  generalize fillByInitial fs st filled name n
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩ = F at hF ⊢
  have ha := (keeps_runAssign (st := st) (fs := fs) name (.entry n) (some n) .none none F).trans hF
  split
  · exact hF
  · split
    · exact ha
    · split
      · exact ha
      · split
        · split
          · split
            · exact (keeps_closeFinal st step name _).trans ha
            · exact (keeps_endWith (fun c n => keeps_exitOne st.exitFuel c n) name _).trans ha
          · simp only [id_pure, enterFinal_fixed]; exact ha
        · exact (addDeadlines_fixed _ _ _ _).trans ha

theorem keeps_enter (step : Nat) (name : InstanceId) (targets : List String) : Keeps (enter fs st step name targets) := by
  unfold enter
  apply keeps_withMachine
  intro i r
  exact foldlM_keeps (fun n => keeps_unlessHalted (keeps_enterOne step false name n)) _ r

theorem keeps_checkChart (name : InstanceId) : Keeps (checkChart fs st name) := by
  unfold checkChart
  apply keeps_withMachine
  intro i r
  split
  · rfl
  · simp only [id_bind]; split <;> simp

theorem sameLines_checkChart (name : InstanceId) : SameLines (checkChart fs st name) := by
  unfold checkChart
  apply sameLines_withMachine
  intro i r
  split
  · rfl
  · simp only [id_bind]; split <;> simp

theorem growsBy_checkChart (name : InstanceId) : GrowsBy (checkChart fs st name) :=
  (sameLines_checkChart name).grows (keeps_checkChart name)

theorem Grows.sameLines {a b c : State} (h : Grows a b) (hl : c.lines = b.lines) (hs : c.service = b.service) :
    Grows a c := by
  obtain ⟨⟨n, e, t⟩, m⟩ := h
  exact ⟨⟨n, by rw [hl, e], t⟩, by rw [hl, hs]; exact m⟩

theorem keeps_microstep (step : Nat) (name : InstanceId) (chosen : List (InstanceId × Transition)) (extra : Extra) :
    Keeps (microstep fs st step name chosen extra) := by
  unfold microstep
  apply keeps_withMachine
  intro i r
  split
  · rfl
  · simp only [id_bind, note_id, id_pure]
    refine ((keeps_checkChart name) _).trans ?_
    refine (foldlM_keeps (fun (e : (InstanceId × String) × Nat) => keeps_unlessHalted (keeps_enterOne step _ e.1.1 e.1.2)) _ _).trans ?_
    refine (foldlM_keeps (fun c => keeps_transitionContent extra _ _ c) _ _).trans ?_
    refine (foldlM_keeps (fun (e : (InstanceId × String) × Nat) =>
      keeps_unlessHalted (keeps_exitOne st.exitFuel e.1.1 e.1.2)) _ _).trans ?_
    have h0 : ∀ (hs : List InstanceId) (f : InstanceId → Instance → Instance) (t : State),
        (hs.foldl (fun s h => s.setMachine h (f h)) t).fixed = t.fixed := by
      intro hs f
      induction hs with
      | nil => intro t; rfl
      | cons h hs ih => intro t; exact ih _
    exact h0 _ _ _

theorem growsBy_enterOne (step : Nat) (filled : Bool) (name : InstanceId) (n : String) :
    GrowsBy (enterOne fs st step filled name n) := by
  unfold enterOne
  apply growsBy_withMachine
  intro i r
  try simp only [id_bind]
  have hFl := sameLines_fillByInitial (st := st) (fs := fs) filled name n
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩
  have hFn := (keeps_fillByInitial (st := st) (fs := fs) filled name n).now
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩
  have hFs := (keeps_fillByInitial (st := st) (fs := fs) filled name n).service
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩
  generalize fillByInitial fs st filled name n
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩
    = F at hFl hFn hFs ⊢
  have ha := (sameLines_runAssign (st := st) (fs := fs) name (.entry n) (some n) .none none F).trans hFl
  have hn := ((keeps_runAssign (st := st) (fs := fs) name (.entry n) (some n) .none none).now F).trans hFn
  have hs := ((keeps_runAssign (st := st) (fs := fs) name (.entry n) (some n) .none none).service F).trans hFs
  split
  · exact Grows.of_lines hFl hFs
  · split
    · exact Grows.of_lines ha hs
    · split
      · exact Grows.of_lines ha hs
      · split
        · split
          · split
            · exact (Grows.of_lines ha hs).trans hn (growsBy_closeFinal st step name _)
            · exact (Grows.of_lines ha hs).trans hn (growsBy_endWith (fun c n => growsBy_exitOne st.exitFuel c n)
                (fun c n => keeps_exitOne st.exitFuel c n) name _)
          · simp only [id_pure]
            exact Grows.of_lines ((enterFinal_lines _ _ _ _).trans ha)
              ((congrArg Fixed.service (enterFinal_fixed _ _ _ _)).trans hs)
        · exact Grows.of_lines ((addDeadlines_lines _ _ _ _).trans ha)
            ((congrArg Fixed.service (addDeadlines_fixed _ _ _ _)).trans hs)

theorem growsBy_enter (step : Nat) (name : InstanceId) (targets : List String) : GrowsBy (enter fs st step name targets) := by
  unfold enter
  apply growsBy_withMachine
  intro i r
  exact foldlM_grows (fun n => growsBy_unlessHalted (growsBy_enterOne step false name n))
    (fun n => keeps_unlessHalted (keeps_enterOne step false name n)) _ r

theorem growsBy_microstep (step : Nat) (name : InstanceId) (chosen : List (InstanceId × Transition)) (extra : Extra) :
    GrowsBy (microstep fs st step name chosen extra) := by
  unfold microstep
  apply growsBy_withMachine
  intro i r
  split
  · exact Grows.refl _
  · simp only [id_bind, note_id, id_pure]
    have kE : ∀ xs (r : Processing), (List.foldlM (m := Id) (fun r (e : (InstanceId × String) × Nat) =>
        unlessHalted (exitOne fs st st.exitFuel e.1.1 e.1.2) r) r xs).1.fixed = r.state.fixed :=
      foldlM_keeps (fun (e : (InstanceId × String) × Nat) => keeps_unlessHalted (keeps_exitOne st.exitFuel e.1.1 e.1.2))
    have hE : ∀ xs (r : Processing), Grows r.state (List.foldlM (m := Id) (fun r (e : (InstanceId × String) × Nat) =>
        unlessHalted (exitOne fs st st.exitFuel e.1.1 e.1.2) r) r xs).1 :=
      foldlM_grows (fun (e : (InstanceId × String) × Nat) => growsBy_unlessHalted (growsBy_exitOne st.exitFuel e.1.1 e.1.2))
        (fun e => keeps_unlessHalted (keeps_exitOne st.exitFuel e.1.1 e.1.2))
    have kA : ∀ sh es xs (r : Processing),
        (List.foldlM (m := Id) (transitionContent fs st extra sh es) r xs).1.fixed = r.state.fixed :=
      fun sh es => foldlM_keeps (fun c => keeps_transitionContent extra sh es c)
    have hA : ∀ sh es xs (r : Processing),
        Grows r.state (List.foldlM (m := Id) (transitionContent fs st extra sh es) r xs).1 :=
      fun sh es xs r => Grows.of_lines (foldlM_sameLines (fun c => sameLines_transitionContent extra sh es c) xs r)
        (congrArg Fixed.service (kA sh es xs r))
    have hN : ∀ xs (r : Processing), Grows r.state (List.foldlM (m := Id) (fun r (e : (InstanceId × String) × Nat) =>
        unlessHalted (enterOne fs st step (targetedBy chosen e.1 e.2) e.1.1 e.1.2) r) r xs).1 :=
      foldlM_grows (fun (e : (InstanceId × String) × Nat) => growsBy_unlessHalted (growsBy_enterOne step _ e.1.1 e.1.2))
        (fun e => keeps_unlessHalted (keeps_enterOne step _ e.1.1 e.1.2))
    have h0 : ∀ (hs : List InstanceId) (f : InstanceId → Instance → Instance) (t : State),
        (hs.foldl (fun s h => s.setMachine h (f h)) t).lines = t.lines ∧
          (hs.foldl (fun s h => s.setMachine h (f h)) t).now = t.now ∧
          (hs.foldl (fun s h => s.setMachine h (f h)) t).service = t.service := by
      intro hs f
      induction hs with
      | nil => intro t; exact ⟨rfl, rfl, rfl⟩
      | cons h hs ih => intro t; exact ih _
    obtain ⟨l0, n0, s0⟩ := h0 (holdersOf chosen) _ r.state
    exact Grows.sameLines ((Grows.of_lines l0 s0).trans n0 ((hE _ _).trans (congrArg Fixed.now (kE _ _))
      ((hA _ _ _ _).trans (congrArg Fixed.now (kA _ _ _ _)) (hN _ _)))) (sameLines_checkChart name _)
      ((keeps_checkChart name).service _)

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
    have hm : (cs.spec.name ∈ (pairs.filter (·.1 == i.id)).map (·.2)) ↔ (i.id, cs.spec.name) ∈ pairs := by
      simp only [List.mem_map, List.mem_filter, beq_iff_eq]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨hab, rfl⟩, rfl⟩; exact hab
      · intro hp; exact ⟨_, ⟨hp, rfl⟩, rfl⟩
    by_cases hp : (i.id, cs.spec.name) ∈ pairs <;> simp [hp, hm, ih]

@[guarantee] theorem microstep_exits_in_exit_order (s : State) (i : Instance) (chosen : List (InstanceId × Transition)) :
    ((((i.documentOrder.filter (· ∈ s.exitPairs chosen)).reverse).filter (·.1 == i.id)).map (·.2)) =
      i.chart.tree.exitOrder (((s.exitPairs chosen).filter (·.1 == i.id)).map (·.2)) := by
  rw [List.filter_reverse, List.map_reverse, documentOrder_owner_pairs i _]
  simp only [Tree.entryOrder, Tree.exitOrder, List.filter_reverse]

@[guarantee] theorem microstep_enters_in_entry_order (s : State) (i : Instance) (chosen : List (InstanceId × Transition)) :
    (((i.documentOrder.filter (· ∈ s.entryPairs chosen)).filter (·.1 == i.id)).map (·.2)) =
      i.chart.tree.entryOrder (((s.entryPairs chosen).filter (·.1 == i.id)).map (·.2)) :=
  documentOrder_owner_pairs i _

end Tazuna.Thm.Service.Chart.Microstep
