import Tazuna.Semantics.Diamond
import Tazuna.Semantics.Settle

/-! The own cascade with its order left open. `settle` runs the waiting own commands and queries first in, first out;
the spec writes no such order, so any waiting one may run next (`ownSys`), and `settle` is the run that always picks
the first (`settle_runs`). Where every two waiting own effects commute in one step, every order agrees with `settle`
(`settle_agrees`): the step's result does not depend on the order the semantics picked. -/

namespace Tazuna.Ir

namespace Step

variable {v : ServiceV} (T : List TypeDecl)

/-- The own cascade as a system of steps: the enabled steps are the waiting own effects, and running one takes it out
of the queue. -/
def ownSys (v : ServiceV) : Diamond.Sys (Acc v) Fault where
  len a := a.own.length
  pick a i := match a.own[i]? with
    | some eff => runOwn T { a with own := a.own.eraseIdx i } eff
    | none => .ok a
  limit := .cascadeLimit

theorem settle_first : (fuel : Nat) → (a : Acc v) → settle T fuel a = Diamond.first (ownSys T v) fuel a
  | fuel, a => by
    unfold settle Diamond.first
    cases ho : a.own with
    | nil => simp [ownSys, ho]
    | cons eff rest =>
      cases fuel with
      | zero => simp [ownSys, ho]
      | succ f =>
        simp only [ownSys, ho, List.length_cons, Nat.add_one_ne_zero, ↓reduceIte, List.getElem?_cons_zero,
          List.eraseIdx_cons_zero, bind, Except.bind]
        cases runOwn T { a with own := rest } eff with
        | error e => rfl
        | ok b => exact settle_first f b

/-- `settle` is one of the runs of the own cascade. -/
theorem settle_runs (fuel : Nat) (a : Acc v) : Diamond.Runs (ownSys T v) fuel a (settle T fuel a) := by
  rw [settle_first]
  exact Diamond.runs_first _ fuel a

/-- Where waiting own effects commute in one step, up to an equivalence the own steps respect, every order of the own
cascade ends as `settle` does, up to that equivalence, or both fault. -/
theorem settle_agrees {I : Acc v → Prop} {E : Acc v → Acc v → Prop} (hE : Diamond.Equiv E)
    (hS : Diamond.Simulates (ownSys T v) E) (hD : Diamond.Commutes (ownSys T v) I E)
    (hI : Diamond.Preserved (ownSys T v) I) (fuel : Nat) (a : Acc v) (ha : I a) {r : Except Fault (Acc v)}
    (hr : Diamond.Runs (ownSys T v) fuel a r) : Diamond.Agree E r (settle T fuel a) :=
  Diamond.runs_agree hE hS hD hI fuel a ha hr (settle_runs T fuel a)

end Step

end Tazuna.Ir
