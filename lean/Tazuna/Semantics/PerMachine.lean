import Tazuna.Semantics.Structure

/-! One value per machine of a service, as a list indexed by the machine list (Mathlib's `List.TProd`): a state's
instances, whose type depends on the machine, and on the symbolic side each machine's table term, reaction or firing
part, start slots. Recursion over the machines and their values together has no case where the two differ in
number. -/

namespace Tazuna.Ir

/-- One `β m` per machine `m` of `ms`, in their order. -/
inductive PerMachine {r e : Ty} (β : MachineV r e → Type) : List (MachineV r e) → Type where
  | nil : PerMachine β []
  | cons {m : MachineV r e} {ms : List (MachineV r e)} (x : β m) (xs : PerMachine β ms) : PerMachine β (m :: ms)

namespace PerMachine
variable {r e : Ty}

/-- The same value `f m` for every machine `m`. -/
def ofFn {β : MachineV r e → Type} (f : (m : MachineV r e) → β m) : (ms : List (MachineV r e)) → PerMachine β ms
  | [] => .nil
  | _ :: ms => .cons (f _) (ofFn f ms)

/-- Each machine with its value, in order. -/
def toSigma {β : MachineV r e → Type} : {ms : List (MachineV r e)} → PerMachine β ms → List ((m : MachineV r e) × β m)
  | _, .nil => []
  | _, .cons x xs => ⟨_, x⟩ :: xs.toSigma

@[simp] theorem toSigma_nil {β : MachineV r e → Type} : (PerMachine.nil : PerMachine β []).toSigma = [] := rfl

@[simp] theorem toSigma_cons {β : MachineV r e → Type} {m : MachineV r e} {ms : List (MachineV r e)} (x : β m)
    (xs : PerMachine β ms) : (PerMachine.cons x xs).toSigma = ⟨m, x⟩ :: xs.toSigma := rfl

@[simp] theorem toSigma_fst {β : MachineV r e → Type} : {ms : List (MachineV r e)} → (xs : PerMachine β ms) →
    xs.toSigma.map (·.1) = ms
  | _, .nil => rfl
  | _, .cons _ xs => by simp [toSigma_fst xs]

@[simp] theorem toSigma_ofFn {β : MachineV r e → Type} (f : (m : MachineV r e) → β m) :
    (ms : List (MachineV r e)) → (ofFn f ms).toSigma = ms.map fun m => ⟨m, f m⟩
  | [] => rfl
  | _ :: ms => by simp [ofFn, toSigma_ofFn f ms]

theorem fst_mem {β : MachineV r e → Type} {ms : List (MachineV r e)} {xs : PerMachine β ms}
    {x : (m : MachineV r e) × β m} (h : x ∈ xs.toSigma) : x.1 ∈ ms :=
  toSigma_fst xs ▸ List.mem_map_of_mem h

variable {β γ δ : Type}

def toList : {ms : List (MachineV r e)} → PerMachine (fun _ => β) ms → List β
  | _, .nil => []
  | _, .cons x xs => x :: xs.toList

def map (f : β → γ) : {ms : List (MachineV r e)} → PerMachine (fun _ => β) ms → PerMachine (fun _ => γ) ms
  | _, .nil => .nil
  | _, .cons x xs => .cons (f x) (xs.map f)

def zipWith (f : β → γ → δ) : {ms : List (MachineV r e)} → PerMachine (fun _ => β) ms → PerMachine (fun _ => γ) ms →
    PerMachine (fun _ => δ) ms
  | _, .nil, .nil => .nil
  | _, .cons x xs, .cons y ys => .cons (f x y) (zipWith f xs ys)

@[simp] theorem toList_nil : (PerMachine.nil : PerMachine (fun _ => β) ([] : List (MachineV r e))).toList = [] := rfl

@[simp] theorem toList_cons {m : MachineV r e} {ms : List (MachineV r e)} (x : β) (xs : PerMachine (fun _ => β) ms) :
    (PerMachine.cons (m := m) x xs).toList = x :: xs.toList := rfl

@[simp] theorem toList_zipWith (f : β → γ → δ) : {ms : List (MachineV r e)} → (xs : PerMachine (fun _ => β) ms) →
    (ys : PerMachine (fun _ => γ) ms) → (zipWith f xs ys).toList = List.zipWith f xs.toList ys.toList
  | _, .nil, .nil => rfl
  | _, .cons x xs, .cons y ys => by simp [zipWith, toList_zipWith f xs ys]

end PerMachine

end Tazuna.Ir
