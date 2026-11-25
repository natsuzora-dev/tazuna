import Tazuna.Semantics.Structure

/-! One value per machine of a service, as a list indexed by the machine list (the heterogeneous-list shape of
Mathlib's `List.TProd`): the instance tables of a symbolic state, each machine's reaction or firing part, its start
slots. Recursion over the machines and their values together has no case where the two differ in number. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- One `β` per machine of `ms`, in their order. -/
inductive PerMachine (β : Type) {r e : Ty} : List (MachineV r e) → Type where
  | nil : PerMachine β []
  | cons {m : MachineV r e} {ms : List (MachineV r e)} (x : β) (xs : PerMachine β ms) : PerMachine β (m :: ms)

namespace PerMachine
variable {β γ δ : Type} {r e : Ty}

def toList : {ms : List (MachineV r e)} → PerMachine β ms → List β
  | _, .nil => []
  | _, .cons x xs => x :: xs.toList

def map (f : β → γ) : {ms : List (MachineV r e)} → PerMachine β ms → PerMachine γ ms
  | _, .nil => .nil
  | _, .cons x xs => .cons (f x) (xs.map f)

def zipWith (f : β → γ → δ) : {ms : List (MachineV r e)} → PerMachine β ms → PerMachine γ ms → PerMachine δ ms
  | _, .nil, .nil => .nil
  | _, .cons x xs, .cons y ys => .cons (f x y) (zipWith f xs ys)

@[simp] theorem toList_nil : (PerMachine.nil : PerMachine β ([] : List (MachineV r e))).toList = [] := rfl

@[simp] theorem toList_cons {m : MachineV r e} {ms : List (MachineV r e)} (x : β) (xs : PerMachine β ms) :
    (PerMachine.cons (m := m) x xs).toList = x :: xs.toList := rfl

@[simp] theorem length_toList : {ms : List (MachineV r e)} → (xs : PerMachine β ms) → xs.toList.length = ms.length
  | _, .nil => rfl
  | _, .cons _ xs => by simp [length_toList xs]

@[simp] theorem toList_map (f : β → γ) : {ms : List (MachineV r e)} → (xs : PerMachine β ms) →
    (xs.map f).toList = xs.toList.map f
  | _, .nil => rfl
  | _, .cons x xs => by simp [map, toList_map f xs]

@[simp] theorem toList_zipWith (f : β → γ → δ) : {ms : List (MachineV r e)} → (xs : PerMachine β ms) →
    (ys : PerMachine γ ms) → (zipWith f xs ys).toList = List.zipWith f xs.toList ys.toList
  | _, .nil, .nil => rfl
  | _, .cons x xs, .cons y ys => by simp [zipWith, toList_zipWith f xs ys]

end PerMachine

end Tazuna.Smt
