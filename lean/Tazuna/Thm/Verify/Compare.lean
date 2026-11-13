import Tazuna.Verify.Compare

namespace Tazuna.Thm.Verify.Compare

open Tazuna.Data Tazuna.Verify

/-- No value of the renaming stands for two values, in either direction. -/
def OneToOne (r : Renaming) : Prop := ∀ u ∈ r, ∀ v ∈ r, (u.snapshot = v.snapshot ↔ u.trace = v.trace)

theorem bind_oneToOne {r r' : Renaming} {u : Use} (h : OneToOne r) (hb : r.bind u = some r') : OneToOne r' := by
  unfold Renaming.bind at hb
  cases hs : r.traceOf? u.snapshot with
  | some t =>
    rw [hs] at hb
    by_cases e : (t == u.trace) = true
    · simp only [e, ite_true, Option.some.injEq] at hb; subst hb; exact h
    · simp [e] at hb
  | none =>
    rw [hs] at hb
    by_cases ht : r.takes u.trace = true
    · simp [ht] at hb
    · simp only [ht, Bool.false_eq_true, ite_false, Option.some.injEq] at hb
      subst hb
      have ns : ∀ v ∈ r, v.snapshot ≠ u.snapshot := by
        intro v hv e
        simp only [Renaming.traceOf?, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq] at hs
        exact hs v hv e
      have nt : ∀ v ∈ r, v.trace ≠ u.trace := by
        intro v hv e
        simp only [Renaming.takes, List.any_eq_true, beq_iff_eq, not_exists, not_and] at ht
        exact ht v hv e
      intro a ha b hb
      simp only [List.mem_append, List.mem_singleton] at ha hb
      rcases ha with ha | rfl <;> rcases hb with hb | rfl
      · exact h a ha b hb
      · exact ⟨fun e => absurd e (ns a ha), fun e => absurd e (nt a ha)⟩
      · exact ⟨fun e => absurd e.symm (ns b hb), fun e => absurd e.symm (nt b hb)⟩
      · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem steps_go_inputs : ∀ (ls : List (Option Line)) (i : Nat) (acc : List Out),
    ∃ ins : List Out, (steps.go ls i acc).map (·.input) = ins.map some ++ [none]
  | [], _, _ => ⟨[], by simp [steps.go]⟩
  | none :: ls, i, acc => by simpa [steps.go] using steps_go_inputs ls (i + 1) acc
  | some l :: ls, i, acc => by
    simp only [steps.go]
    split
    · exact steps_go_inputs ls (i + 1) _
    · obtain ⟨ins, h⟩ := steps_go_inputs ls (i + 1) []
      exact ⟨{ line := l, index := i + 1 } :: ins, by simp [h]⟩

theorem steps_inputs (ls : List (Option Line)) :
    ∃ ins : List Out, (steps ls).map (·.input) = ins.map some ++ [none] :=
  steps_go_inputs ls 0 []

theorem input_isSome_iff (ls : List (Option Line)) (k : Nat) :
    (((steps ls)[k]?).bind (·.input)).isSome ↔ k + 1 < (steps ls).length := by
  obtain ⟨ins, h⟩ := steps_inputs ls
  have hl : (steps ls).length = ins.length + 1 := by
    have := congrArg List.length h; simpa using this
  have hk : ((steps ls)[k]?).bind (·.input) = (ins.map some ++ [none])[k]?.join := by
    rw [← h]; simp only [List.getElem?_map]; cases (steps ls)[k]? <;> rfl
  rw [hk, hl]
  by_cases hlt : k < ins.length
  · rw [List.getElem?_append_left (by simpa using hlt)]
    simp [hlt]
  · rw [List.getElem?_append_right (by simpa using hlt)]
    by_cases he : k = ins.length
    · subst he; simp
    · have : k - ins.length ≠ 0 := by omega
      simp only [List.length_map, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff, this,
          not_false_eq_true, getElem?_neg, Option.join_none, Option.isSome_none, Bool.false_eq_true,
          Nat.add_lt_add_iff_right, false_iff, Nat.not_lt, ge_iff_le]; omega

def IsMismatch : Finding → Prop
  | .mismatch _ => True
  | .uncomparable _ => False

def BothSome (w : Option Window × Option Window × Option Out × Option Out) : Prop :=
  ((w.1.bind (·.input)).isSome ∧ (w.2.1.bind (·.input)).isSome)

def BothNone (w : Option Window × Option Window × Option Out × Option Out) : Prop :=
  (w.1.bind (·.input)) = none ∧ (w.2.1.bind (·.input)) = none

theorem aligned_prefix (c : Ctx) (lineCount : Nat) (malformed : Option Nat) :
    ∀ (L : List (Option Window × Option Window × Option Out × Option Out)) (st : St),
      (∀ f ∈ (compareFrom c lineCount malformed L st).findings, IsMismatch f) →
      ∀ j (hj : j < L.length), (∀ i (hi : i < j), BothSome L[i]) → BothSome L[j] ∨ BothNone L[j]
  | [], _, _, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | (e, a, p) :: rest, st, h, j, hj, hprev => by
    rw [compareFrom] at h
    generalize hw : runWindow c st _ _ _ _ = w at h
    obtain ⟨found, limited, st'⟩ := w
    cases limited with
    | some u => exact False.elim (h (.uncomparable u) (by simp))
    | none =>
    have tail : ∀ f ∈ (compareInputs c lineCount malformed (e.bind (·.input)) (a.bind (·.input)) rest st').findings,
        IsMismatch f := fun f hf => h f (List.mem_append_right _ hf)
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, BothSome, BothNone]
      cases he : e.bind (·.input) <;> cases ha : a.bind (·.input) <;> rw [he, ha, compareInputs] at tail
      · right; exact ⟨rfl, rfl⟩
      · exact False.elim (tail _ List.mem_cons_self)
      · exact False.elim (tail _ List.mem_cons_self)
      · left; simp
    | succ j =>
      have h0 := hprev 0 (Nat.zero_lt_succ j)
      simp only [List.getElem_cons_zero, BothSome] at h0
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h0.1
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h0.2
      rw [hs, ht, compareInputs] at tail
      split at tail
      · exact False.elim (tail _ List.mem_cons_self)
      · exact False.elim (tail _ List.mem_cons_self)
      · simp only [List.getElem_cons_succ]
        exact aligned_prefix c lineCount malformed rest _ tail j (by simpa using hj)
          (fun i hi => by have := hprev (i + 1) (by omega); simpa using this)

theorem compareFrom_malformed (c : Ctx) (lineCount n : Nat) :
    ∀ (L : List (Option Window × Option Window × Option Out × Option Out)) (st : St), (∀ w ∈ L, (w.2.1.bind (·.input)).isSome) →
      ∃ (ms : List Mismatch) (u : Uncomparable),
        (compareFrom c lineCount (some n) L st).findings = ms.map .mismatch ++ [.uncomparable u]
  | [], _, _ => ⟨[], .lineSchema n, by rw [compareFrom]; rfl⟩
  | (e, a, p) :: rest, st, h => by
    rw [compareFrom]
    generalize runWindow c st _ _ _ _ = w
    obtain ⟨found, limited, st'⟩ := w
    cases limited with
    | some u => exact ⟨found, u, rfl⟩
    | none =>
    suffices hs : ∃ (ms : List Mismatch) (u : Uncomparable),
        (compareInputs c lineCount (some n) (e.bind (·.input)) (a.bind (·.input)) rest st').findings =
          ms.map .mismatch ++ [.uncomparable u] by
      obtain ⟨ms, u, hs⟩ := hs
      exact ⟨found ++ ms, u, by simp [hs]⟩
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h _ List.mem_cons_self)
    simp only at ht
    rw [ht]
    cases e.bind (·.input) <;> rw [compareInputs]
    · exact ⟨[], _, rfl⟩
    · split
      · exact ⟨[], _, rfl⟩
      · exact ⟨[], _, rfl⟩
      · exact compareFrom_malformed c lineCount n rest _ fun w hw => h w (List.mem_cons_of_mem _ hw)

theorem compare_malformed (snapshot lines : List (Option Line)) (n : Nat) (internal : Line → Bool) :
    ∃ (ms : List Mismatch) (u : Uncomparable),
      (Verify.compare snapshot lines (some n) internal).findings = ms.map .mismatch ++ [.uncomparable u] := by
  unfold Verify.compare
  apply compareFrom_malformed
  intro w hw
  simp only [List.mem_map, List.mem_range] at hw
  obtain ⟨k, hk, rfl⟩ := hw
  exact (input_isSome_iff lines k).mpr (by omega)

theorem inputs_align (snapshot lines : List (Option Line)) (malformed : Option Nat) (internal : Line → Bool)
    (h : ∀ f ∈ (Verify.compare snapshot lines malformed internal).findings, IsMismatch f) :
    malformed = none ∧ (steps snapshot).length = (steps lines).length := by
  have hm : malformed = none := by
    cases malformed with
    | none => rfl
    | some n =>
      obtain ⟨ms, u, hc⟩ := compare_malformed snapshot lines n internal
      exact False.elim (h (.uncomparable u) (by simp [hc]))
  subst hm
  refine ⟨rfl, ?_⟩
  unfold Verify.compare at h
  generalize hE : steps snapshot = E at h
  generalize hA : steps lines = A at h
  have hEi := input_isSome_iff snapshot
  have hAi := input_isSome_iff lines
  rw [hE] at hEi
  rw [hA] at hAi
  have hE1 : 1 ≤ E.length := by
    obtain ⟨ins, h⟩ := steps_inputs snapshot; rw [hE] at h
    have := congrArg List.length h; simp only [List.length_map, List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add] at this; omega
  have hA1 : 1 ≤ A.length := by
    obtain ⟨ins, h⟩ := steps_inputs lines; rw [hA] at h
    have := congrArg List.length h; simp only [List.length_map, List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add] at this; omega
  have P := aligned_prefix _ _ _ _ _ h
  have key : ∀ k, k < max E.length A.length → (∀ i < k, i + 1 < E.length ∧ i + 1 < A.length) →
      ((k + 1 < E.length) ↔ (k + 1 < A.length)) := by
    intro k hk hall
    have := P k (by simpa using hk) (fun i hi => by
      simp only [List.getElem_map, List.getElem_range, BothSome]
      have := hall i hi
      exact ⟨(hEi i).mpr this.1, (hAi i).mpr this.2⟩)
    simp only [List.getElem_map, List.getElem_range, BothSome, BothNone] at this
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => (hAi k).mp h2, fun _ => (hEi k).mp h1⟩
    · have n1 : ¬ k + 1 < E.length := fun hlt => by have := (hEi k).mpr hlt; simp [h1] at this
      have n2 : ¬ k + 1 < A.length := fun hlt => by have := (hAi k).mpr hlt; simp [h2] at this
      constructor <;> intro x <;> omega
  have hk : min E.length A.length - 1 < max E.length A.length := by omega
  have := key (min E.length A.length - 1) hk (fun i hi => by omega)
  omega

theorem compareFrom_shape (c : Ctx) (lineCount : Nat) (malformed : Option Nat) :
    ∀ (L : List (Option Window × Option Window × Option Out × Option Out)) (st : St),
      ∃ (ms : List Mismatch) (u : Option Uncomparable),
        (compareFrom c lineCount malformed L st).findings = ms.map .mismatch ++ u.toList.map .uncomparable
  | [], _ => ⟨[], malformed.map .lineSchema, by rw [compareFrom]; cases malformed <;> rfl⟩
  | (e, a, p) :: rest, st => by
    rw [compareFrom]
    generalize runWindow c st _ _ _ _ = w
    obtain ⟨found, limited, st'⟩ := w
    cases limited with
    | some u => exact ⟨found, some u, rfl⟩
    | none =>
    suffices h : ∃ (ms : List Mismatch) (u : Option Uncomparable),
        (compareInputs c lineCount malformed (e.bind (·.input)) (a.bind (·.input)) rest st').findings =
          ms.map .mismatch ++ u.toList.map .uncomparable by
      obtain ⟨ms, u, h⟩ := h
      exact ⟨found ++ ms, u, by simp [h]⟩
    cases e.bind (·.input) <;> cases a.bind (·.input) <;> rw [compareInputs]
    · exact ⟨[], none, rfl⟩
    · exact ⟨[], some _, rfl⟩
    · exact ⟨[], some _, rfl⟩
    · split
      · exact ⟨[], some _, rfl⟩
      · exact ⟨[], some _, rfl⟩
      · exact compareFrom_shape c lineCount malformed rest _

end Tazuna.Thm.Verify.Compare
