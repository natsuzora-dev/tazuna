import Tazuna.Thm.Verify.Complete.Inputs
import Tazuna.Thm.Verify.Complete.Steps
import Tazuna.Thm.Verify.Complete.Subscriptions

namespace Tazuna.Thm.Verify.Complete.Top

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Run Tazuna.Thm.Verify.Complete.Window Tazuna.Thm.Verify.Complete.Bindings Tazuna.Thm.Verify.Complete.Inputs Tazuna.Thm.Verify.Complete.Steps Tazuna.Thm.Verify.Complete.Subscriptions

/-- The windows that compare walks. -/
def windowsOf (E A : List Window) : List (Option Window × Option Window × Option Out) :=
  (List.range (max E.length A.length)).map fun k =>
    (E[k]?, A[k]?, if k == 0 then none else A[k - 1]?.bind (·.input))

/-- The state after comparing the `out` lines of window `k`. -/
def windowRun (c : Ctx) (E A : List Window) (k : Nat) (st : St) : St :=
  (runWindow c st ((E[k]?.map (·.before)).getD []) ((A[k]?.map (·.before)).getD [])
    (((if k == 0 then none else A[k - 1]?.bind (·.input)).map (·.index)).getD 1)).2

/-- The state after comparing the `in` line of window `k`. -/
def inputRun (E A : List Window) (k : Nat) (st : St) : St :=
  match E[k]?.bind (·.input), A[k]?.bind (·.input) with
  | some s, some t => { (sameInput st s.line t.line).2 with ids := inputIds (sameInput st s.line t.line).2.ids s.line t.line }
  | _, _ => st

/-- The state before window `k`. -/
def stateAt (c : Ctx) (E A : List Window) : Nat → St
  | 0 => {}
  | k + 1 => inputRun E A k (windowRun c E A k (stateAt c E A k))

theorem windowsOf_drop (E A : List Window) (k : Nat) (hk : k < max E.length A.length) :
    (windowsOf E A).drop k =
      (E[k]?, A[k]?, if k == 0 then none else A[k - 1]?.bind (·.input)) :: (windowsOf E A).drop (k + 1) := by
  unfold windowsOf
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  simp

/-- A quiet comparison of the windows from `k` on is quiet in window `k`, and goes on when `k` is not the last. -/
theorem quiet_step (c : Ctx) (n : Nat) (E A : List Window) (hlen : E.length = A.length)
    (hE : ∀ k, (E[k]?.bind (·.input)).isSome ↔ k + 1 < E.length)
    (hA : ∀ k, (A[k]?.bind (·.input)).isSome ↔ k + 1 < A.length) (k : Nat) (hk : k < E.length)
    (h : (compareFrom c n none ((windowsOf E A).drop k) (stateAt c E A k)).findings = []) :
    (runWindow c (stateAt c E A k) ((E[k]?.map (·.before)).getD []) ((A[k]?.map (·.before)).getD [])
        (((if k == 0 then none else A[k - 1]?.bind (·.input)).map (·.index)).getD 1)).1 = [] ∧
      (k + 1 < E.length → ∃ s t, E[k]?.bind (·.input) = some s ∧ A[k]?.bind (·.input) = some t ∧
        (sameInput (windowRun c E A k (stateAt c E A k)) s.line t.line).1 = true ∧
        (compareFrom c n none ((windowsOf E A).drop (k + 1)) (stateAt c E A (k + 1))).findings = []) := by
  rw [windowsOf_drop E A k (by omega), compareFrom] at h
  simp only at h
  generalize hw : runWindow c (stateAt c E A k) _ _ _ = w at h
  obtain ⟨found, st₁⟩ := w
  simp only [List.append_eq_nil_iff, List.map_eq_nil_iff] at h
  refine ⟨h.1, fun hk1 => ?_⟩
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp ((hE k).mpr hk1)
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((hA k).mpr (by omega))
  have h2 := h.2
  rw [hs, ht, compareInputs] at h2
  have hst₁ : st₁ = windowRun c E A k (stateAt c E A k) := by unfold windowRun; rw [hw]
  subst hst₁
  split at h2
  · simp at h2
  · rename_i st₂ heq
    refine ⟨s, t, hs, ht, by rw [heq], ?_⟩
    have : stateAt c E A (k + 1) =
        { st₂ with ids := ((st₂.ids.bind s.line.body.to? t.line.body.to?).bind s.line.body.resultOf?
          t.line.body.resultOf?).bind s.line.body.id t.line.body.id } := by
      simp only [stateAt, inputRun, hs, ht, heq, inputIds]
    rw [this]
    exact h2

/-- The position of the `in` line of window `k`, counted from 0, or `len` if the window has none. -/
def inputPos (ws : List Window) (len k : Nat) : Nat := ((ws[k]?.bind (·.input)).map (·.index - 1)).getD len

/-- The position of the first line of window `k`, counted from 0. -/
def startPos (ws : List Window) (len : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => inputPos ws len k + 1

/-- The subscriptions open before window `k`. -/
def openBefore (ws : List Window) (k : Nat) : List (String × Subscription) :=
  (ws.take k).foldl (fun o w => follow o (w.before.filter (·.line.isSubscribing))) []

theorem openBefore_succ (ws : List Window) (k : Nat) (w : Window) (hw : ws[k]? = some w) :
    openBefore ws (k + 1) = follow (openBefore ws k) (subscribing w.before) := by
  unfold openBefore
  rw [List.take_add_one, hw]
  simp

theorem openAfter_eq (ws : List Window) (k : Nat) : openAfter ws k = openBefore ws (k + 1) := rfl

theorem openBefore_nodup (ws : List Window) (k : Nat) : ((openBefore ws k).map (·.1)).Nodup := by
  unfold openBefore
  apply foldl_preserve (fun o : List (String × Subscription) => (o.map (·.1)).Nodup)
  · exact fun o _ _ h => follow_nodup o _ h
  · exact List.nodup_nil

theorem mem_follow {o : List (String × Subscription)} {lines : List Out} {x : String × Subscription}
    (h : x ∈ follow o lines) : x ∈ o ∨ (x.2.out ∈ lines ∧ ∃ d n v, x.2.out.line.body = .subscribe d (some x.1) n v) := by
  unfold follow at h
  revert h
  apply foldl_preserve (fun o' : List (String × Subscription) => x ∈ o' →
    x ∈ o ∨ (x.2.out ∈ lines ∧ ∃ d n v, x.2.out.line.body = .subscribe d (some x.1) n v))
  · intro o' l hl ho' hx
    split at hx
    · rename_i d id name v hb
      split at hx
      · exact ho' hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact ho' hx
        · simp only [List.mem_singleton] at hx
          subst hx
          exact Or.inr ⟨hl, d, name, v, hb⟩
    · exact ho' (List.mem_filter.mp hx).1
    · exact ho' hx
  · exact Or.inl

theorem mem_openBefore {ws : List Window} {k : Nat} {x : String × Subscription} (h : x ∈ openBefore ws k) :
    ∃ j < k, ∃ w, ws[j]? = some w ∧ x.2.out ∈ w.before ∧ ∃ d n v, x.2.out.line.body = .subscribe d (some x.1) n v := by
  induction k with
  | zero => simp [openBefore] at h
  | succ k ih =>
    cases hw : ws[k]? with
    | none =>
      have : ws.take (k + 1) = ws.take k := by
        rw [List.take_add_one, hw]; simp
      have h' : x ∈ openBefore ws k := by unfold openBefore at h ⊢; rwa [this] at h
      obtain ⟨j, hj, w, h1, h2⟩ := ih h'
      exact ⟨j, by omega, w, h1, h2⟩
    | some w =>
      rw [openBefore_succ ws k w hw] at h
      rcases mem_follow h with h | ⟨h1, h2⟩
      · obtain ⟨j, hj, w', h3, h4⟩ := ih h
        exact ⟨j, by omega, w', h3, h4⟩
      · exact ⟨k, by omega, w, hw, (List.mem_filter.mp h1).1, h2⟩

theorem steps_input_of_lt {ls : List (Option Line)} {k : Nat} (hk : k + 1 < (steps ls).length) :
    ∃ o, (steps ls)[k]?.bind (·.input) = some o := Option.isSome_iff_exists.mp ((input_isSome_iff ls k).mpr hk)

/-- The facts about the lines of window `k` of `ls`. -/
structure WindowAt (ls : List (Option Line)) (k : Nat) (w : Window) : Prop where
  before : ∀ o ∈ w.before, AtLine ls o ∧ o.line.body.dir = .out ∧
    startPos (steps ls) ls.length k ≤ o.index - 1 ∧ o.index - 1 < inputPos (steps ls) ls.length k
  input : ∀ o, w.input = some o → AtLine ls o ∧ o.line.body.dir ≠ .out ∧ o.index - 1 = inputPos (steps ls) ls.length k
  order : ((w.before ++ w.input.toList).map (·.index)).Pairwise (· < ·)

theorem windowAt (ls : List (Option Line)) (k : Nat) (w : Window) (hw : (steps ls)[k]? = some w) :
    WindowAt ls k w := by
  obtain ⟨h1, h2, h3, h4⟩ := steps_spec ls
  have hwm : w ∈ steps ls := List.mem_of_getElem? hw
  have hord := window_order h1 hw
  have hat : ∀ o ∈ windowLines w, AtLine ls o := fun o ho => h2 o (mem_flat hwm ho)
  have hlt : ∀ o ∈ w.before, ∀ i, w.input = some i → o.index < i.index := by
    intro o ho i hi
    have := List.pairwise_append.mp (by simpa [windowLines] using hord)
    exact this.2.2 o.index (List.mem_map_of_mem ho) i.index (by simp [hi])
  have hstart : ∀ o ∈ windowLines w, startPos (steps ls) ls.length k ≤ o.index - 1 := by
    intro o ho
    cases k with
    | zero => exact Nat.zero_le _
    | succ k =>
      simp only [startPos, inputPos]
      have hk : k + 1 < (steps ls).length := by
        by_cases hc : k + 1 < (steps ls).length
        · exact hc
        · simp [List.getElem?_eq_none (by omega : (steps ls).length ≤ k + 1)] at hw
      obtain ⟨i, hi⟩ := steps_input_of_lt (Nat.lt_of_succ_lt hk |> fun _ => by omega : k + 1 < (steps ls).length)
      cases hwk : (steps ls)[k]? with
      | none => simp [hwk] at hi
      | some wk =>
        simp only [hwk, Option.bind_some] at hi
        have := flat_order h1 (Nat.lt_succ_self k) hwk hw i (by simp [windowLines, hi]) o ho
        have hi1 := (h2 i (mem_flat (List.mem_of_getElem? hwk) (by simp [windowLines, hi]))).1
        simp only [Option.bind_some, hi, Option.map_some, Option.getD_some]
        omega
  refine ⟨fun o ho => ⟨hat o (by simp [windowLines, ho]), h3 w hwm o ho, hstart o (by simp [windowLines, ho]), ?_⟩,
    fun o ho => ⟨hat o (by simp [windowLines, ho]), h4 w hwm o ho, ?_⟩, by simpa [windowLines] using hord⟩
  · simp only [inputPos, hw, Option.bind_some]
    cases hi : w.input with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      obtain ⟨h1', h2'⟩ := hat o (by simp [windowLines, ho])
      have := (List.getElem?_eq_some_iff.mp h2').1
      omega
    | some i =>
      have := hlt o ho i hi
      have := (hat o (by simp [windowLines, ho])).1
      simp only [Option.map_some, Option.getD_some]
      omega
  · simp [inputPos, hw, ho]

theorem startPos_le_inputPos (ls : List (Option Line)) (k : Nat) (hk : k < (steps ls).length) :
    startPos (steps ls) ls.length k ≤ inputPos (steps ls) ls.length k := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    obtain ⟨w, hw⟩ : ∃ w, (steps ls)[k + 1]? = some w := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨i, hi⟩ := steps_input_of_lt hk
    cases hwk : (steps ls)[k]? with
    | none => simp [hwk] at hi
    | some wk =>
      simp only [hwk, Option.bind_some] at hi
      have hwa := windowAt ls (k + 1) w hw
      have hia := (windowAt ls k wk hwk).input i hi
      simp only [startPos]
      cases hin : w.input with
      | some j =>
        obtain ⟨hf, _, _, _⟩ := steps_spec ls
        have h1 := flat_order hf (Nat.lt_succ_self k) hwk hw i (by simp [windowLines, hi]) j (by simp [windowLines, hin])
        have h2 := (hwa.input j hin).1.1
        have h3 := hia.1.1
        simp only [inputPos, hw, hwk, Option.bind_some, hin, hi, Option.map_some, Option.getD_some]
        omega
      | none =>
        simp only [inputPos, hw, Option.bind_some, hin, Option.map_none, Option.getD_none]
        have := hia.1
        have := (List.getElem?_eq_some_iff.mp this.2).1
        simp only [hwk, Option.bind_some, hi, Option.map_some, Option.getD_some]
        omega

end Tazuna.Thm.Verify.Complete.Top
