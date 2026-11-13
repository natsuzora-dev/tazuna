import Tazuna.Thm.Verify.Complete.Lists

namespace Tazuna.Thm.Verify.Complete.Steps

open Tazuna.Data Tazuna.Verify

/-- The lines of a window in trace order. -/
def windowLines (w : Window) : List Out := w.before ++ w.input.toList

/-- The lines of windows in trace order. -/
def flat (ws : List Window) : List Out := ws.flatMap windowLines

/-- The line `o` is the line of `ls` at its number, and `out` lines are exactly the lines before an `in` line. -/
def AtLine (ls : List (Option Line)) (o : Out) : Prop := 1 ≤ o.index ∧ ls[o.index - 1]? = some (some o.line)

theorem steps_go_spec : ∀ (ls : List (Option Line)) (i : Nat) (acc : List Out),
    (acc.map (·.index)).Pairwise (· > ·) → (∀ o ∈ acc, o.index ≤ i ∧ o.line.body.dir = .out) →
    ((flat (steps.go ls i acc)).map (·.index)).Pairwise (· < ·) ∧
      (∀ o ∈ flat (steps.go ls i acc), o ∈ acc ∨ (i < o.index ∧ ls[o.index - i - 1]? = some (some o.line))) ∧
      (∀ w ∈ steps.go ls i acc, ∀ o ∈ w.before, o.line.body.dir = .out) ∧
      (∀ w ∈ steps.go ls i acc, ∀ o, w.input = some o → o.line.body.dir ≠ .out)
  | [], i, acc, hp, ha => by
    simp only [steps.go, flat, List.flatMap_cons, List.flatMap_nil, List.append_nil, windowLines,
      Option.toList_none, List.mem_singleton, forall_eq, List.mem_reverse, List.map_reverse]
    refine ⟨?_, fun o ho => Or.inl (by simpa using ho), fun o ho => (ha o (by simpa using ho)).2, by simp⟩
    rw [List.pairwise_reverse]; exact hp
  | none :: ls, i, acc, hp, ha => by
    simp only [steps.go]
    obtain ⟨h1, h2, h3, h4⟩ := steps_go_spec ls (i + 1) acc hp (fun o ho => ⟨by have := (ha o ho).1; omega, (ha o ho).2⟩)
    refine ⟨h1, fun o ho => ?_, h3, h4⟩
    rcases h2 o ho with h | ⟨hi, hl⟩
    · exact Or.inl h
    · right
      refine ⟨by omega, ?_⟩
      have : o.index - i - 1 = (o.index - (i + 1) - 1) + 1 := by omega
      rw [this]; simpa using hl
  | some l :: ls, i, acc, hp, ha => by
    simp only [steps.go]
    split
    · rename_i hd
      have hd' : l.body.dir = .out := by simpa using hd
      obtain ⟨h1, h2, h3, h4⟩ := steps_go_spec ls (i + 1) ({ line := l, index := i + 1 } :: acc)
        (by
          simp only [List.map_cons, List.pairwise_cons, List.mem_map]
          refine ⟨?_, hp⟩
          rintro _ ⟨o, ho, rfl⟩; have := (ha o ho).1; omega)
        (by
          intro o ho
          rcases List.mem_cons.mp ho with rfl | ho
          · exact ⟨Nat.le_refl _, hd'⟩
          · exact ⟨by have := (ha o ho).1; omega, (ha o ho).2⟩)
      refine ⟨h1, fun o ho => ?_, h3, h4⟩
      rcases h2 o ho with h | ⟨hi, hl⟩
      · rcases List.mem_cons.mp h with rfl | h
        · right; simp
        · exact Or.inl h
      · right
        refine ⟨by omega, ?_⟩
        have : o.index - i - 1 = (o.index - (i + 1) - 1) + 1 := by omega
        rw [this]; simpa using hl
    · rename_i hd
      have hd' : l.body.dir ≠ .out := by simpa using hd
      obtain ⟨h1, h2, h3, h4⟩ := steps_go_spec ls (i + 1) [] (by simp) (by simp)
      have hfl : flat ({ before := acc.reverse, input := some { line := l, index := i + 1 } } ::
          steps.go ls (i + 1) []) = acc.reverse ++ [{ line := l, index := i + 1 }] ++ flat (steps.go ls (i + 1) []) := by
        simp [flat, windowLines]
      rw [hfl]
      refine ⟨?_, fun o ho => ?_, ?_, ?_⟩
      · simp only [List.map_append, List.map_reverse, List.map_cons, List.map_nil]
        refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨List.pairwise_reverse.mpr hp, by simp, ?_⟩, h1, ?_⟩
        · simp only [List.mem_reverse, List.mem_map, List.mem_singleton]
          rintro _ ⟨o, ho, rfl⟩ _ rfl; have := (ha o ho).1; omega
        · intro a ha' b hb
          obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hb
          rcases h2 o' ho' with h | ⟨hi, _⟩
          · simp at h
          · simp only [List.mem_append, List.mem_reverse, List.mem_map, List.mem_singleton] at ha'
            rcases ha' with ⟨o, ho, rfl⟩ | rfl
            · have := (ha o ho).1; omega
            · omega
      · simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at ho
        rcases ho with (ho | rfl) | ho
        · exact Or.inl ho
        · right; simp
        · rcases h2 o ho with h | ⟨hi, hl⟩
          · simp at h
          · right
            refine ⟨by omega, ?_⟩
            have : o.index - i - 1 = (o.index - (i + 1) - 1) + 1 := by omega
            rw [this]; simpa using hl
      · intro w hw o ho
        rcases List.mem_cons.mp hw with rfl | hw
        · exact (ha o (by simpa using ho)).2
        · exact h3 w hw o ho
      · intro w hw o ho
        rcases List.mem_cons.mp hw with rfl | hw
        · simp only [Option.some.injEq] at ho; subst ho; exact hd'
        · exact h4 w hw o ho

theorem steps_spec (ls : List (Option Line)) :
    ((flat (steps ls)).map (·.index)).Pairwise (· < ·) ∧ (∀ o ∈ flat (steps ls), AtLine ls o) ∧
      (∀ w ∈ steps ls, ∀ o ∈ w.before, o.line.body.dir = .out) ∧
      (∀ w ∈ steps ls, ∀ o, w.input = some o → o.line.body.dir ≠ .out) := by
  obtain ⟨h1, h2, h3, h4⟩ := steps_go_spec ls 0 [] (by simp) (by simp)
  refine ⟨h1, fun o ho => ?_, h3, h4⟩
  rcases h2 o ho with h | ⟨hi, hl⟩
  · simp at h
  · exact ⟨hi, by simpa using hl⟩

theorem mem_flat {ws : List Window} {w : Window} (hw : w ∈ ws) {o : Out} (ho : o ∈ windowLines w) : o ∈ flat ws :=
  List.mem_flatMap.mpr ⟨w, hw, ho⟩

theorem flat_split {ws : List Window} {i : Nat} {w : Window} (h : ws[i]? = some w) :
    flat ws = flat (ws.take i) ++ windowLines w ++ flat (ws.drop (i + 1)) := by
  have hi : i < ws.length := by
    by_cases hc : i < ws.length
    · exact hc
    · simp [List.getElem?_eq_none (by omega : ws.length ≤ i)] at h
  have e : ws = ws.take i ++ w :: ws.drop (i + 1) := by
    have := List.take_append_drop i ws
    rw [List.drop_eq_getElem_cons hi] at this
    simp only [List.getElem?_eq_getElem hi, Option.some.injEq] at h
    rw [h] at this
    exact this.symm
  calc flat ws = flat (ws.take i ++ w :: ws.drop (i + 1)) := congrArg flat e
    _ = _ := by simp [flat, List.flatMap_append]

/-- Lines of an earlier window come before lines of a later window. -/
theorem flat_order {ws : List Window} (h : ((flat ws).map (·.index)).Pairwise (· < ·)) {j k : Nat} (hjk : j < k)
    {wj wk : Window} (hj : ws[j]? = some wj) (hk : ws[k]? = some wk) :
    ∀ a ∈ windowLines wj, ∀ b ∈ windowLines wk, a.index < b.index := by
  rw [flat_split hk, List.map_append, List.map_append] at h
  have h1 := (List.pairwise_append.mp h).1
  have h2 := (List.pairwise_append.mp h1).2.2
  have hwj : wj ∈ ws.take k := by
    rw [List.mem_iff_getElem?]; exact ⟨j, by rw [List.getElem?_take]; simp [hjk, hj]⟩
  intro a ha b hb
  exact h2 a.index (List.mem_map_of_mem (List.mem_flatMap.mpr ⟨wj, hwj, ha⟩)) b.index (List.mem_map_of_mem hb)

theorem window_order {ws : List Window} (h : ((flat ws).map (·.index)).Pairwise (· < ·)) {i : Nat} {w : Window}
    (hw : ws[i]? = some w) : ((windowLines w).map (·.index)).Pairwise (· < ·) := by
  rw [flat_split hw, List.map_append, List.map_append] at h
  exact (List.pairwise_append.mp (List.pairwise_append.mp h).1).2.1


theorem before_order (ls : List (Option Line)) {w : Window} (hw : w ∈ steps ls) :
    (w.before.map (·.index)).Pairwise (· < ·) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
  have := window_order (steps_spec ls).1 hi
  simp only [windowLines, List.map_append] at this
  exact (List.pairwise_append.mp this).1

theorem before_atLine (ls : List (Option Line)) {w : Window} (hw : w ∈ steps ls) {o : Out} (ho : o ∈ w.before) :
    AtLine ls o :=
  (steps_spec ls).2.1 o (mem_flat hw (List.mem_append_left _ ho))

theorem AtLine.mem {ls : List (Option Line)} {o : Out} (h : AtLine ls o) : some o.line ∈ ls :=
  List.mem_of_getElem? h.2

theorem mustFollow_irrefl (S : List (Option Line)) (n : Nat) : n ∉ mustFollow S n := by
  unfold mustFollow
  cases hh : (((steps S).flatMap fun w => w.before.zipIdx.filterMap fun (o, k) =>
      if o.index - 1 == n then some ((o.line.after.getD []).filterMap (earlierWithId (w.before.take k)))
      else none).head?) with
  | none => simp
  | some xs =>
    simp only [Option.getD_some]
    intro hn
    obtain ⟨w, hw, hx⟩ := List.mem_flatMap.mp (List.mem_of_mem_head? hh)
    obtain ⟨⟨o, k⟩, hok, hf⟩ := List.mem_filterMap.mp hx
    simp only at hf
    split at hf
    · rename_i he
      simp only [Option.some.injEq] at hf
      subst hf
      obtain ⟨id, _, hy⟩ := List.mem_filterMap.mp hn
      simp only [earlierWithId, Option.map_eq_some_iff] at hy
      obtain ⟨o', hf', ho'⟩ := hy
      have hmem : o' ∈ w.before.take k := List.mem_reverse.mp (List.mem_of_find?_eq_some hf')
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
      rw [List.getElem?_take] at hj
      split at hj
      · rename_i hjk
        have hk := List.mem_zipIdx_iff_getElem?.mp hok
        simp only at hk
        have hord := before_order S hw
        have hjl : j < w.before.length := (List.getElem?_eq_some_iff.mp hj).1
        have hkl : k < w.before.length := (List.getElem?_eq_some_iff.mp hk).1
        have := List.pairwise_iff_getElem.mp hord j k (by simpa using hjl) (by simpa using hkl) hjk
        simp only [List.getElem_map] at this
        rw [List.getElem?_eq_some_iff.mp hj |>.2, List.getElem?_eq_some_iff.mp hk |>.2] at this
        have h1 := (before_atLine S hw (List.mem_of_getElem? hj)).1
        simp only [beq_iff_eq] at he
        omega
      · cases hj
    · cases hf

theorem byRank_perm : ∀ ss : List Out, (byRank ss).Perm ss
  | [] => by simp [byRank]
  | s :: ss => by
    have ih := byRank_perm ss
    simp only [byRank, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_cons] at ih ⊢
    have hr : rank s.line = 0 ∨ rank s.line = 1 ∨ rank s.line = 2 := by
      unfold rank; split
      · exact .inl rfl
      · split <;> simp
    rcases hr with h | h | h <;> simp only [h, beq_self_eq_true, ite_true, Nat.reduceBEq, Bool.false_eq_true,
      ite_false, List.cons_append]
    · exact (List.perm_cons s).mpr ih
    · exact List.perm_middle.trans ((List.perm_cons s).mpr ih)
    · rw [← List.append_assoc]
      exact List.perm_middle.trans (by rw [List.append_assoc]; exact (List.perm_cons s).mpr ih)

end Tazuna.Thm.Verify.Complete.Steps
