import Tazuna.Smt.PendingWrite

/-! What every step encoding of a service reads from the layout, looked up once: the effect datatype of its event
type, the pending entry of its pending shapes and the option of an effect, each index with the lookup that found it.
The layout holds all three for every service, with an effect datatype of no variant for a service without effects
(`Layout.datatype?`). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The layout's indices of the effect datatype, the pending entry at `shs` and the effect option. -/
structure StepEnv (L : Layout) {e : Ty} (shs : List (PendingShape e)) where
  dE : Nat
  nE : Nat
  hE : L.find? (.dsl .effect [e]) = some (dE, nE)
  dP : Nat
  nP : Nat
  hPE : L.find? (pendingEntry shs) = some (dP, nP)
  dopt : Nat
  nopt : Nat
  hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt)

/-- The step environment of the layout at the pending shapes `shs`. -/
def StepEnv.of (L : Layout) {e : Ty} (shs : List (PendingShape e)) : Except Refusal (StepEnv L shs) :=
  match hE : L.find? (.dsl .effect [e]), hPE : L.find? (pendingEntry shs), hopt : L.find? (Ty.option (.dsl .effect [e])) with
  | some (dE, nE), some (dP, nP), some (dopt, nopt) => .ok ⟨dE, nE, hE, dP, nP, hPE, dopt, nopt, hopt⟩
  | none, _, _ => .error (.outside "a layout without the effect type")
  | _, none, _ => .error (.outside "a layout without the pending entry")
  | _, _, none => .error (.outside "a layout without the effect option")

end Tazuna.Smt
