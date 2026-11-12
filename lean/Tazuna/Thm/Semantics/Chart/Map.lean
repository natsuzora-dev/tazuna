import Tazuna.Semantics.Chart.Map
import Tazuna.Thm.Semantics.Chart.Microstep
import Tazuna.Thm.Semantics.Note

namespace Tazuna.Thm.Semantics.Chart.Map

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Data.List Tazuna.Thm.Semantics.Functions Tazuna.Thm.Semantics.Note Tazuna.Thm.Semantics.Chart.Deadline Tazuna.Thm.Semantics.Chart.Done Tazuna.Thm.Semantics.Chart.Exit Tazuna.Thm.Semantics.Chart.Microstep Tazuna.Thm.Semantics.Chart.Queue Tazuna.Thm.Semantics.Chart.Request Tazuna.Thm.Semantics.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Semantics.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem keeps_startCopy (step : Nat) (owner map : String) (key : Value) (k : String) :
    Keeps (startCopy fs st step owner map key k) := by
  unfold startCopy
  apply keeps_withMachine
  intro o r
  simp only [id_bind, note_id, id_pure]
  split
  · exact keeps_enter _ _ _ _
  · rfl

theorem exitLeftCopy_fixed (owner map : String) (itemKeys : List String) (r : Processing) (k : String) :
    (exitLeftCopy fs st owner map itemKeys r k).1.fixed = r.state.fixed := by
  unfold exitLeftCopy
  split
  · rfl
  · exact keeps_unlessHalted (keeps_endWith (fun c n => keeps_exitOne Limit.exitDepth.max c n) _) _

theorem syncMap_fixed (step : Nat) (owner : String) (r : Processing) (map : String) :
    (syncMap fs st step owner r map).1.1.fixed = r.state.fixed := by
  unfold syncMap
  simp only [id_bind]
  split
  · rfl
  · split
    · rfl
    · split
      · simp [Processing.report]
      · split
        · rfl
        · split
          · rfl
          · rw [foldlM_id, foldlM_id]
            exact (foldl_fixed' _ (fun (r : Processing) (k : Value × String) =>
              keeps_unlessHalted (keeps_startCopy (fs := fs) (st := st) step owner map k.1 k.2) r) _ _).trans
              (foldl_fixed' _ (exitLeftCopy_fixed _ _ _) _ _)

theorem syncCopies_fixed (step : Nat) (owner : String) (r : Processing) :
    (syncCopies fs st step owner r).1.1.fixed = r.state.fixed := by
  unfold syncCopies
  split
  · rfl
  · rw [foldlM_id]
    exact foldl_pair_keeps (fun acc map => ((syncMap fs st step owner acc.1 map).1, acc.2 || (syncMap fs st step owner acc.1 map).2))
      (fun acc map => syncMap_fixed step owner acc.1 map) _ _

theorem syncMap_unchanged (step : Nat) (owner : String) (r : Processing) (map : String)
    (h : (syncMap fs st step owner r map).2 = false) : (syncMap fs st step owner r map).1 = r := by
  by_cases hr : r.halted = true
  · simp [syncMap, hr]
  · cases ho : r.state.machine? owner with
    | none => simp [syncMap, hr, ho]
    | some o =>
      cases hi : fs.items (r.state.scopeOf o (some map)) r.state.records with
      | error v => simp [syncMap, hr, ho, hi] at h
      | ok keys =>
        cases hd : firstDuplicate (·.2) keys with
        | some k => simp [syncMap, hr, ho, hi, hd] at h
        | none =>
        by_cases he : o.copyKeysOf map = keys.map (·.2)
        · simp [syncMap, hr, ho, hi, hd, he]
        · simp [syncMap, hr, ho, hi, hd, he] at h

theorem foldl_unchanged {α : Type} (g : Processing → α → Processing × Bool) (hg : ∀ r x, (g r x).2 = false → (g r x).1 = r)
    (xs : List α) (acc : Processing × Bool)
    (h : (xs.foldl (fun acc x => ((g acc.1 x).1, acc.2 || (g acc.1 x).2)) acc).2 = false) :
    acc.2 = false ∧ (xs.foldl (fun acc x => ((g acc.1 x).1, acc.2 || (g acc.1 x).2)) acc).1 = acc.1 := by
  induction xs generalizing acc with
  | nil => exact ⟨h, rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at h ⊢
    obtain ⟨h1, h2⟩ := ih _ h
    simp only [Bool.or_eq_false_iff] at h1
    rw [h2, hg _ _ h1.2]
    exact ⟨h1.1, rfl⟩

theorem syncCopies_unchanged (step : Nat) (owner : String) (r : Processing)
    (h : (syncCopies fs st step owner r).2 = false) : (syncCopies fs st step owner r).1 = r := by
  unfold syncCopies at h ⊢
  split at h
  · rfl
  · rw [foldlM_id] at h ⊢
    exact (foldl_unchanged (fun r map => syncMap fs st step owner r map) (fun r map => syncMap_unchanged step owner r map)
      _ (r, false) h).2

theorem growsBy_startCopy (step : Nat) (owner map : String) (key : Value) (k : String) :
    GrowsBy (startCopy fs st step owner map key k) := by
  unfold startCopy
  apply growsBy_withMachine
  intro o r
  simp only [id_bind, note_id, id_pure]
  split
  · exact (growsBy_enter _ _ _ _).bridge (by rfl) (by rfl)
  · exact Grows.of_lines rfl

theorem exitLeftCopy_grows (owner map : String) (itemKeys : List String) (r : Processing) (k : String) :
    Grows r.state (exitLeftCopy fs st owner map itemKeys r k).1 := by
  unfold exitLeftCopy
  split
  · exact Grows.refl _
  · exact growsBy_unlessHalted (growsBy_endWith (fun c n => growsBy_exitOne Limit.exitDepth.max c n)
      (fun c n => keeps_exitOne Limit.exitDepth.max c n) _) r

theorem syncMap_grows (step : Nat) (owner : String) (r : Processing) (map : String) :
    Grows r.state (syncMap fs st step owner r map).1.1 := by
  unfold syncMap
  simp only [id_bind]
  split
  · exact Grows.refl _
  · split
    · exact Grows.refl _
    · split
      · exact Grows.of_lines (by simp [Processing.report])
      · split
        · exact Grows.of_lines rfl
        · split
          · exact Grows.refl _
          · rw [foldlM_id, foldlM_id]
            refine (foldl_run_grows _ (exitLeftCopy_grows _ _ _) (fun r c => congrArg Fixed.now (exitLeftCopy_fixed _ _ _ r c))
              _ _).trans ?_ ((foldl_run_grows _ (fun (r : Processing) (k : Value × String) =>
                growsBy_unlessHalted (growsBy_startCopy (fs := fs) (st := st) step owner map k.1 k.2) r)
                (fun (r : Processing) (k : Value × String) => congrArg Fixed.now
                  (keeps_unlessHalted (keeps_startCopy (fs := fs) (st := st) step owner map k.1 k.2) r)) _ _).bridge
                  (by rfl) (by rfl))
            exact congrArg Fixed.now (foldl_fixed' _ (exitLeftCopy_fixed _ _ _) _ _)

theorem syncCopies_grows (step : Nat) (owner : String) (r : Processing) :
    Grows r.state (syncCopies fs st step owner r).1.1 := by
  unfold syncCopies
  split
  · exact Grows.refl _
  · rw [foldlM_id]
    generalize (List.filter _ _) = maps
    suffices ∀ (acc : Processing × Bool), Grows acc.1.state (maps.foldl (fun acc map =>
        ((syncMap fs st step owner acc.1 map).1, acc.2 || (syncMap fs st step owner acc.1 map).2)) acc).1.1 from this _
    intro acc
    induction maps generalizing acc with
    | nil => exact Grows.refl _
    | cons x xs ih =>
      exact (syncMap_grows step owner acc.1 x).trans (congrArg Fixed.now (syncMap_fixed step owner acc.1 x)) (ih _)

theorem lookup_setCopyKeys (copyKeys : List (String × List String)) (map : String) (cs : List String) :
    (setCopyKeys copyKeys map cs).lookup map = some cs := by
  unfold setCopyKeys
  split
  · rename_i h
    induction copyKeys with
    | nil => simp at h
    | cons x xs ih =>
      obtain ⟨k, v⟩ := x
      by_cases e : k = map
      · subst e; simp
      · have hb : (k == map) = false := by simpa using e
        have hb' : (map == k) = false := by simpa using Ne.symm e
        simp only [List.any_cons, hb, Bool.false_or] at h
        simp only [List.map_cons, hb, Bool.false_eq_true, ↓reduceIte, List.lookup_cons, hb']
        exact ih h
  · rename_i h
    induction copyKeys with
    | nil => simp
    | cons x xs ih =>
      obtain ⟨k, v⟩ := x
      have e : (k == map) = false := by simp only [List.any_cons, Bool.or_eq_true, not_or] at h; simpa using h.1
      have hb' : (map == k) = false := by
        have e' : k ≠ map := by simpa using e
        simpa using Ne.symm e'
      simp only [List.any_cons, e, Bool.false_or] at h
      simp only [List.cons_append, List.lookup_cons, hb']
      exact ih h

theorem syncMap_copies_follow_items (step : Nat) (owner map : String) (r : Processing) (o : Instance)
    (keys : List (Value × String)) (hh : r.state.halted = none) (ho : r.state.machine? owner = some o)
    (hi : fs.items (r.state.scopeOf o (some map)) r.state.records = .ok keys)
    (hd : firstDuplicate (·.2) keys = none) :
    syncMap fs st step owner r map =
      let itemKeys := keys.map (·.2)
      if o.copyKeysOf map == itemKeys then (r, false) else
      let exited := (o.copyKeysOf map).reverse.foldlM (m := Id) (exitLeftCopy fs st o.resource map itemKeys) r
      let started := (newKeys (o.copyKeysOf map) keys).foldlM (m := Id)
        (fun r k => unlessHalted (startCopy fs st step owner map k.1 k.2) r) exited
      (⟨started.state.setMachine owner fun o => { o with copyKeys := setCopyKeys o.copyKeys map itemKeys }, started.queue⟩,
        true) := by
  simp only [syncMap, Processing.halted, hh, ho, hi, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, id_bind]
  split <;> rfl

theorem syncMap_halts_on_duplicate_key (step : Nat) (owner map : String) (r : Processing) (o : Instance)
    (keys : List (Value × String)) (k : Value × String) (hh : r.state.halted = none) (ho : r.state.machine? owner = some o)
    (hi : fs.items (r.state.scopeOf o (some map)) r.state.records = .ok keys)
    (hd : firstDuplicate (·.2) keys = some k) :
    syncMap fs st step owner r map =
      (⟨r.state.halt (Finding.fault (.duplicateItemKey (st.ref o.chart.name) map k.1)).toViolation, r.queue⟩, true) := by
  simp [syncMap, Processing.halted, hh, ho, hi, hd, Processing.report, State.report, Fault.halts]

theorem syncMap_copyKeys_are_item_keys (step : Nat) (owner map : String) (r : Processing) (o' : Instance)
    (hh : r.state.halted = none) (hr : (syncMap fs st step owner r map).1.state.halted = none)
    (ho' : (syncMap fs st step owner r map).1.state.machine? owner = some o') :
    ∃ o keys, r.state.machine? owner = some o ∧ fs.items (r.state.scopeOf o (some map)) r.state.records = .ok keys ∧
      o'.copyKeysOf map = keys.map (·.2) ∧ (o'.copyKeysOf map).Nodup := by
  cases ho : r.state.machine? owner with
  | none => simp [syncMap, Processing.halted, hh, ho] at ho'
  | some o =>
    cases hi : fs.items (r.state.scopeOf o (some map)) r.state.records with
    | error v =>
      have hv := issueViolation_halts (st := st) (st.ref o.chart.name) v (fun _ => .itemsSchema (st.ref o.chart.name) map)
        fun _ => rfl
      simp [syncMap, Processing.halted, Processing.report, report_halted (.fault _) hv, hh, ho, hi] at hr
    | ok keys =>
      cases hd : firstDuplicate (·.2) keys with
      | some k =>
        rw [syncMap_halts_on_duplicate_key step owner map r o keys k hh ho hi hd] at hr
        simp [State.halt] at hr
      | none =>
      have hn := (firstDuplicate_eq_none_iff _ _).mp hd
      have he : o'.copyKeysOf map = keys.map (·.2) := by
        rw [syncMap_copies_follow_items step owner map r o keys hh ho hi hd] at ho'
        simp only at ho'
        split at ho'
        · rename_i he
          rw [ho] at ho'; cases ho'
          simpa using he
        · rw [machine?_setMachine (f := fun o => { o with copyKeys := setCopyKeys o.copyKeys map (keys.map (·.2)) }) _
            (fun _ => rfl)] at ho'
          obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp ho'
          simp [Instance.copyKeysOf, lookup_setCopyKeys]
      exact ⟨o, keys, rfl, hi, he, he ▸ hn⟩

theorem syncMap_copies_in_item_order (step : Nat) (owner : String) (r : Processing) (o' : Instance) (cs : ChartState)
    (hcs : cs ∈ o'.chart.states) (hh : r.state.halted = none)
    (hr : (syncMap fs st step owner r cs.name).1.state.halted = none)
    (ho' : (syncMap fs st step owner r cs.name).1.state.machine? owner = some o') :
    ∃ o keys pre post, r.state.machine? owner = some o ∧
      fs.items (r.state.scopeOf o (some cs.name)) r.state.records = .ok keys ∧
      o'.documentOrder = pre ++ (o'.resource, cs.name) ::
        ((keys.map (·.2)).flatMap fun k => (o'.chart.tree.descendants cs.name).map (copyName o'.resource cs.name k, ·)) ++ post := by
  obtain ⟨o, keys, ho, hi, he, -⟩ := syncMap_copyKeys_are_item_keys step owner cs.name r o' hh hr ho'
  obtain ⟨pre, post, hd⟩ := documentOrder_at_map o' cs hcs
  exact ⟨o, keys, pre, post, ho, hi, he ▸ hd⟩

theorem returning_key_starts_copy (step : Nat) (owner map : String) (r : Processing) (o o' : Instance)
    (keysBefore keys : List (Value × String)) (k : Value × String) (hh : r.state.halted = none)
    (ho : r.state.machine? owner = some o) (hi : fs.items (r.state.scopeOf o (some map)) r.state.records = .ok keysBefore)
    (hr : (syncMap fs st step owner r map).1.state.halted = none)
    (ho' : (syncMap fs st step owner r map).1.state.machine? owner = some o')
    (hk : k ∈ keys) (hleft : k.2 ∉ keysBefore.map (·.2)) : k ∈ newKeys (o'.copyKeysOf map) keys := by
  obtain ⟨o₁, keys₁, ho₁, hi₁, hc, -⟩ := syncMap_copyKeys_are_item_keys step owner map r o' hh hr ho'
  rw [ho] at ho₁; cases ho₁
  rw [hi] at hi₁; cases hi₁
  simp [newKeys, hc, hk, hleft]

end Tazuna.Thm.Semantics.Chart.Map
