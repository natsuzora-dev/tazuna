import Tazuna.Smt.PendingWrite

/-! What every step encoding of a service reads from the layout, looked up once: the effect datatype of its event
type, the pending entry of its pending shapes, the option of an effect and the pending table, each index with the
lookup that found it. The layout holds all four for every service, with an effect datatype of no variant for a service without effects
(`Layout.datatype?`). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The layout's indices of the effect datatype, the pending entry at `shs`, the effect option, and the pending table
at `shs` with its slot count and its slots' datatype. -/
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
  dT : Nat
  nT : Nat
  dtT : Nat
  hT : collD L (pendingTable shs) [.dsl .fresh [], pendingEntry shs] = .ok (dT, nT, dtT)

/-- The step environment of the layout at the pending shapes `shs`. -/
def StepEnv.of (L : Layout) {e : Ty} (shs : List (PendingShape e)) : Except Refusal (StepEnv L shs) :=
  match hE : L.find? (.dsl .effect [e]), hPE : L.find? (pendingEntry shs), hopt : L.find? (Ty.option (.dsl .effect [e])),
    hT : collD L (pendingTable shs) [.dsl .fresh [], pendingEntry shs] with
  | some (dE, nE), some (dP, nP), some (dopt, nopt), .ok (dT, nT, dtT) =>
    .ok ⟨dE, nE, hE, dP, nP, hPE, dopt, nopt, hopt, dT, nT, dtT, hT⟩
  | none, _, _, _ => .error (lacks (.dsl .effect [e]))
  | _, none, _, _ => .error (lacks (pendingEntry shs))
  | _, _, none, _ => .error (lacks (Ty.option (.dsl .effect [e])))
  | _, _, _, .error r => .error r

end Tazuna.Smt
