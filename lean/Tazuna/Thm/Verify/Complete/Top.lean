import Tazuna.Thm.Verify.Complete.Run

/-!
The states that compare walks through when it reports nothing: the state before each window, the state after its `out`
lines, and the pairing of its search.
-/

namespace Tazuna.Thm.Verify.Complete.Top

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Ids Tazuna.Thm.Verify.Complete.Search
open Tazuna.Thm.Verify.Complete.Window Tazuna.Thm.Verify.Complete.Run

/-- The windows that compare walks. -/
def windowsOf (E A : List Window) : List (Option Window × Option Window × Option Out × Option Out) :=
  (List.range (max E.length A.length)).map fun k =>
    (E[k]?, A[k]?, if k == 0 then none else (A[k - 1]?).bind (·.input),
      if k == 0 then none else (E[k - 1]?).bind (·.input))

def befores (ws : List Window) (k : Nat) : List Out := (ws[k]?.map (·.before)).getD []

/-- The line of the `in` line before window `k`, or 1. -/
def prevAt (ws : List Window) (k : Nat) : Nat :=
  ((if k == 0 then none else (ws[k - 1]?).bind (·.input)).map (·.index)).getD 1

/-- The state after comparing the `out` lines of window `k`. -/
def windowRun (c : Ctx) (E A : List Window) (k : Nat) (st : St) : St :=
  (runWindow c st (befores E k) (befores A k) (prevAt A k) (prevAt E k)).2.2

/-- The state after comparing the `in` lines of window `k`. -/
def inputRun (c : Ctx) (E A : List Window) (k : Nat) (st : St) : St :=
  match (E[k]?).bind (·.input), (A[k]?).bind (·.input) with
  | some s, some t =>
    match sameInput (inputScope c st) st s t with
    | .paired p => { st with ids := p.ids, keys := p.keys }
    | _ => st
  | _, _ => st

/-- The state before window `k`. -/
def stateAt (c : Ctx) (E A : List Window) : Nat → St
  | 0 => {}
  | k + 1 => inputRun c E A k (windowRun c E A k (stateAt c E A k))

/-- The pairing that the search of window `k` finds. -/
def pairingAt (c : Ctx) (E A : List Window) (k : Nat) : Pairing :=
  let st := stateAt c E A k
  let st₁ := enter st (befores E k) (befores A k)
  match pairAll (scopeOf c st₁ (befores A k)) (goalsOf c st₁ (befores E k)) { ids := st.ids, keys := st.keys } with
  | .paired p => p
  | _ => { ids := {}, keys := [] }

theorem windowsOf_drop (E A : List Window) (k : Nat) (hk : k < max E.length A.length) :
    (windowsOf E A).drop k =
      (E[k]?, A[k]?, (if k == 0 then none else (A[k - 1]?).bind (·.input)),
        (if k == 0 then none else (E[k - 1]?).bind (·.input))) :: (windowsOf E A).drop (k + 1) := by
  unfold windowsOf
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  simp

/-- A quiet comparison of the windows from `k` on is quiet in window `k`, and goes on when `k` is not the last. -/
theorem quiet_step (c : Ctx) (n : Nat) (E A : List Window) (hlen : E.length = A.length)
    (hE : ∀ k, (E[k]?.bind (·.input)).isSome ↔ k + 1 < E.length)
    (hA : ∀ k, (A[k]?.bind (·.input)).isSome ↔ k + 1 < A.length) (k : Nat) (hk : k < E.length)
    (h : (compareFrom c n none ((windowsOf E A).drop k) (stateAt c E A k)).findings = []) :
    (runWindow c (stateAt c E A k) (befores E k) (befores A k) (prevAt A k) (prevAt E k)).1 = [] ∧
      (runWindow c (stateAt c E A k) (befores E k) (befores A k) (prevAt A k) (prevAt E k)).2.1 = none ∧
      (k + 1 < E.length → ∃ s t p, E[k]?.bind (·.input) = some s ∧ A[k]?.bind (·.input) = some t ∧
        sameInput (inputScope c (windowRun c E A k (stateAt c E A k))) (windowRun c E A k (stateAt c E A k)) s t =
          .paired p ∧
        (compareFrom c n none ((windowsOf E A).drop (k + 1)) (stateAt c E A (k + 1))).findings = []) := by
  rw [windowsOf_drop E A k (by omega), compareFrom] at h
  have hw : runWindow c (stateAt c E A k) ((E[k]?.map (·.before)).getD []) ((A[k]?.map (·.before)).getD [])
      (((if k == 0 then none else (A[k - 1]?).bind (·.input)).map (·.index)).getD 1)
      (((if k == 0 then none else (E[k - 1]?).bind (·.input)).map (·.index)).getD 1) =
      runWindow c (stateAt c E A k) (befores E k) (befores A k) (prevAt A k) (prevAt E k) := rfl
  rw [hw] at h
  have hst : windowRun c E A k (stateAt c E A k) =
      (runWindow c (stateAt c E A k) (befores E k) (befores A k) (prevAt A k) (prevAt E k)).2.2 := rfl
  rw [hst]
  generalize hwr : runWindow c (stateAt c E A k) (befores E k) (befores A k) (prevAt A k) (prevAt E k) = w at h ⊢
  obtain ⟨found, limited, st₁⟩ := w
  dsimp only at h ⊢
  cases limited with
  | some u => simp at h
  | none =>
  simp only [List.append_eq_nil_iff, List.map_eq_nil_iff] at h
  refine ⟨h.1, rfl, fun hk1 => ?_⟩
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp ((hE k).mpr hk1)
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((hA k).mpr (by omega))
  have h2 := h.2
  rw [hs, ht, compareInputs] at h2
  split at h2
  · simp at h2
  · simp at h2
  · rename_i p heq
    refine ⟨s, t, p, hs, ht, heq, ?_⟩
    have : stateAt c E A (k + 1) = { st₁ with ids := p.ids, keys := p.keys } := by
      have hW : windowRun c E A k (stateAt c E A k) = st₁ := by
        unfold windowRun; rw [hwr]
      simp only [stateAt, inputRun, hs, ht, hW, heq]
    rw [this]
    exact h2


theorem stateAt_succ (c : Ctx) (E A : List Window) (k : Nat) {s t : Out} {p : Pairing}
    (hs : E[k]?.bind (·.input) = some s) (ht : A[k]?.bind (·.input) = some t)
    (h : sameInput (inputScope c (windowRun c E A k (stateAt c E A k))) (windowRun c E A k (stateAt c E A k)) s t =
      .paired p) :
    stateAt c E A (k + 1) = { windowRun c E A k (stateAt c E A k) with ids := p.ids, keys := p.keys } := by
  simp only [stateAt, inputRun, hs, ht, h]

end Tazuna.Thm.Verify.Complete.Top
