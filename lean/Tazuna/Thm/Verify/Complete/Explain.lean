import Tazuna.Thm.Verify.Complete.Window

/-!
`explain` always reports: a window whose search finds no pairing has a finding, unless an earlier window reported.
-/

namespace Tazuna.Thm.Verify.Complete.Explain

open Tazuna.Data Tazuna.Verify

/-- The result and state of running `m` in context `c` from state `st`. -/
abbrev runM {α : Type} (m : CompareM α) (c : Ctx) (st : St) : α × St := (m.run c).run st

theorem runM_bind {α β : Type} (m : CompareM α) (f : α → CompareM β) (c : Ctx) (st : St) :
    runM (m >>= f) c st = runM (f (runM m c st).1) c (runM m c st).2 := rfl

theorem runM_pure {α : Type} (a : α) (c : Ctx) (st : St) : runM (pure a : CompareM α) c st = (a, st) := rfl

theorem runM_get (c : Ctx) (st : St) : runM (get : CompareM St) c st = (st, st) := rfl

theorem runM_read (c : Ctx) (st : St) : runM (read : CompareM Ctx) c st = (c, st) := rfl

theorem runM_modify (f : St → St) (c : Ctx) (st : St) : runM (modify f : CompareM Unit) c st = ((), f st) := rfl

theorem runM_set (s : St) (c : Ctx) (st : St) : runM (set s : CompareM Unit) c st = ((), s) := rfl

theorem forIn_inv {α β : Type} (f : α → β → CompareM (ForInStep β)) (I : β → St → Prop) (c : Ctx)
    (hf : ∀ x b st, I b st → I (runM (f x b) c st).1.value (runM (f x b) c st).2) :
    ∀ (xs : List α) (b : β) (st : St), I b st → I (runM (forIn xs b f) c st).1 (runM (forIn xs b f) c st).2
  | [], b, st, h => h
  | x :: xs, b, st, h => by
    rw [List.forIn_cons, runM_bind]
    have h1 := hf x b st h
    generalize runM (f x b) c st = r at h1
    obtain ⟨step, st'⟩ := r
    cases step with
    | done b' => exact h1
    | yield b' => exact forIn_inv f I c hf xs b' st' h1


theorem runM_report (m : Mismatch) (c : Ctx) (st : St) :
    runM (report m) c st = ((), { st with findings := st.findings ++ [m] }) := rfl

/-- The state has a finding, or nothing was reported as missing or unexpected. -/
def Quiet (st : St) : Prop := st.findings ≠ [] ∨ (st.reportedMissing = [] ∧ st.reportedUnexpected = [])

theorem missing_found (s : Out) (line : Nat) (c : Ctx) (st : St) : (runM (missing s line) c st).2.findings ≠ [] := by
  unfold missing
  simp only [runM_bind, runM_get]
  split <;> simp [runM_report]

set_option linter.unusedSimpArgs false in
theorem explain_found (sc : Scope) (specOut : List Out) (missingAt : Nat) (c : Ctx) (st : St)
    (h0 : st.findings = []) (hm : st.reportedMissing = []) (hu : st.reportedUnexpected = []) :
    (runM (explain sc specOut missingAt) c st).2.findings ≠ [] := by
  unfold explain
  rw [runM_bind, runM_read]; dsimp only; rw [runM_bind, runM_get]; dsimp only; rw [runM_bind]
  generalize hr₁ : runM (forIn (byRank specOut) _ _) c st = r₁
  have q₁ : Quiet r₁.2 := by
    rw [← hr₁]
    refine forIn_inv _ (fun _ st => Quiet st) c (fun x b st h => ?_) _ _ st (.inr ⟨hm, hu⟩)
    repeat' (first | (simp only [runM_bind, runM_pure, runM_get, runM_modify, runM_report, runM_set]) | split)
    all_goals first
      | exact h
      | (left; exact missing_found _ _ _ _)
      | (left; simp; done)
  clear hr₁
  obtain ⟨⟨pairs, idUses, keyUses⟩, st₁⟩ := r₁
  dsimp only at q₁ ⊢
  rw [runM_bind]
  generalize hr₂ : runM (forIn sc.openSnapshot _ _) c st₁ = r₂
  have q₂ : Quiet r₂.2 ∧ (r₂.1.2.1 = true → r₂.2.findings ≠ []) := by
    rw [← hr₂]
    refine forIn_inv _ (fun (b : List Use × Bool × List (String × String)) st =>
      Quiet st ∧ (b.2.1 = true → st.findings ≠ [])) c (fun x b st h => ?_) _ _ st₁
      ⟨q₁, fun h => nomatch h⟩
    obtain ⟨id, s⟩ := x
    repeat' (first | (simp only [runM_bind, runM_pure, runM_get, runM_modify, runM_report, runM_set]) | split)
    all_goals try exact h
    all_goals by_cases hc : st.reportedMissing.contains id = true <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true, runM_bind, runM_pure, runM_set, runM_report]
    · refine ⟨h.1, fun _ => ?_⟩
      rcases h.1 with h1 | ⟨h1, _⟩
      · exact h1
      · simp [h1] at hc
    · constructor
      · left; simp
      · intro _; simp
  clear hr₂
  obtain ⟨⟨keyUses', rep, subscriptions⟩, st₂⟩ := r₂
  dsimp only at q₂ ⊢
  rw [runM_bind]
  generalize hr₃ : runM (forIn sc.openTrace _ _) c st₂ = r₃
  have q₃ : Quiet r₃.2 ∧ (r₃.1 = true → r₃.2.findings ≠ []) := by
    rw [← hr₃]
    refine forIn_inv _ (fun (b : Bool) st => Quiet st ∧ (b = true → st.findings ≠ [])) c (fun x b st h => ?_) _ _ st₂
      q₂
    obtain ⟨tid, t⟩ := x
    simp only [runM_bind, runM_get]
    by_cases ha : (!subscriptions.any fun x => x.snd == tid) = true <;>
      simp only [ha, ↓reduceIte, Bool.false_eq_true, runM_pure]
    · by_cases hc : st.reportedUnexpected.contains tid = true <;>
        simp only [hc, ↓reduceIte, Bool.false_eq_true, runM_bind, runM_pure, runM_set, runM_report]
      · refine ⟨h.1, fun _ => ?_⟩
        rcases h.1 with h1 | ⟨_, h1⟩
        · exact h1
        · simp [h1] at hc
      · constructor
        · left; simp
        · intro _; simp
    · exact h
  clear hr₃
  obtain ⟨rep', st₃⟩ := r₃
  dsimp only at q₃ ⊢
  rw [runM_bind, runM_modify]
  dsimp only
  rw [runM_bind]
  generalize hr₄ : runM (forIn pairs _ _) c _ = r₄
  have q₄ : rep' = true → r₄.2.findings ≠ [] := by
    rw [← hr₄]
    refine forIn_inv _ (fun _ st => rep' = true → st.findings ≠ []) c (fun x b st h => ?_) _ _ _ q₃.2
    obtain ⟨s, t⟩ := x
    dsimp only
    split
    · simp only [runM_bind, runM_report, runM_pure]; intro _; simp
    · exact h
  clear hr₄
  obtain ⟨_, st₄⟩ := r₄
  dsimp only at q₄ ⊢
  rw [runM_bind]
  generalize hr₅ : runM (forIn sc.traceOut _ _) c _ = r₅
  have q₅ : rep' = true → r₅.2.findings ≠ [] := by
    rw [← hr₅]
    refine forIn_inv _ (fun _ st => rep' = true → st.findings ≠ []) c (fun x b st h => ?_) _ _ _ q₄
    split
    · simp only [runM_bind, runM_report, runM_pure]; intro _; simp
    · exact h
  clear hr₅
  obtain ⟨_, st₅⟩ := r₅
  dsimp only at q₅ ⊢
  rw [runM_bind, runM_get]
  dsimp only
  have loop : ∀ (L : List (List Use)) (st' : St), st'.findings ≠ [] ∨ L ≠ [] →
      (runM (forIn L PUnit.unit fun uses _ => do
        report (Mismatch.renaming uses)
        pure (ForInStep.yield PUnit.unit)) c st').2.findings ≠ [] := by
    intro L st' hL
    cases L with
    | nil => simpa [runM_pure] using hL
    | cons u L =>
      rw [List.forIn_cons, runM_bind]
      simp only [runM_bind, runM_report, runM_pure]
      exact forIn_inv _ (fun _ st => st.findings ≠ []) c (fun x b st h => by
        simp only [runM_bind, runM_report, runM_pure]; simp) L _ _ (by simp)
  by_cases hf : st₅.findings = []
  · have hr : rep' = false := by
      cases rep'
      · rfl
      · exact absurd hf (q₅ rfl)
    simp only [hr, hf, h0, Bool.not_false, List.length_nil, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    split
    · simp [runM_report]
    · rename_i hne
      simp only [runM_bind, runM_pure]
      exact loop _ _ (.inr (by simpa using hne))
  · split
    · split
      · simp [runM_report]
      · simp only [runM_bind, runM_pure]
        exact loop _ _ (.inl hf)
    · exact hf

end Tazuna.Thm.Verify.Complete.Explain
