import Tazuna.Semantics.PairCommute

/-! Whether the two orders of a pair of own effects end the same once the names the pair made are renamed, run in
Lean on a counterexample of a pair question. The solver compares the two orders with each effect keeping the names it
made (the canonical order, `Step.canonPair`), which needs no search but is stricter than `Step.Same`: two effects
that each write the id they made under one key end with different ids that a renaming would match.
`sameUpToPair` searches the renamings `Same` allows from the pair's start, which are few: the two counters the pair
used kept or swapped, and the wire ids it sent permuted. Each step in progress is read as one term (`accTerm`) with
collections as sorted lists, as `Ty.canon` reads bags and tables, so equal terms mean the same values up to the order
of multisets. Kept functions compare by their site and captured values. `pairOrders` is the one reading of a pair's
two orders that prove's pair lines and smt-check both use. -/

namespace Tazuna.Smt

open Tazuna.Ir Tazuna.Ir.Step

attribute [local instance] lexOrd

variable {v : ServiceV}

section Terms
variable (σ τ : Nat → Nat)

def siteTerm (s : SiteId) : Erl := .tuple [.bin s.module, .int s.line, .int s.col, .int s.index]

/-- A kept function by its site and captured values. -/
def funTerm {t : Ty} (f : Fun t) : Erl := .tuple [siteTerm f.site, Ty.canonBy σ (.tuple f.Γ) f.env]

def wireTerm (w : WireVal) : Erl := Ty.canonBy σ w.1 w.2

def senderTerm : Sender → Erl
  | .machine n k => .tuple [.bin n, wireTerm σ k]
  | .reaction n => .tuple [.bin n]

def requestTerm {e : Ty} (r : RequestV e) : Erl :=
  .tuple [.bin r.name, Ty.canonBy σ r.input r.value, .list ((r.ensures.map (funTerm σ)).toList), funTerm σ r.onAnswer]

def effectTerm {e : Ty} : EffectV e → Erl
  | .request r => .tuple [.atom "request", requestTerm σ r]
  | .command n c i _ caller value f => .tuple [.atom "command", .bin n, Ty.canonBy σ c caller, Ty.canonBy σ i value, funTerm σ f]
  | .query n c i _ caller value f => .tuple [.atom "query", .bin n, Ty.canonBy σ c caller, Ty.canonBy σ i value, funTerm σ f]

def instTerm {r e : Ty} {m : MachineV r e} (i : Instance m) : Erl :=
  .tuple [Ty.canonBy σ m.key i.key, Ty.canonBy σ m.state i.state, match i.timer with
    | some (d, st) => .tuple [.int d, Ty.canonBy σ m.state st]
    | none => .atom "none"]

def machinesTerm {r e : Ty} : {ms : List (MachineV r e)} → Machines ms → List Erl
  | [], .nil => []
  | _ :: _, .cons l rest => .list (Erl.sort (l.map (instTerm σ))) :: machinesTerm rest

/-- A step in progress as one term, with fresh ids' counters renamed by `σ` and wire ids by `τ`, and every multiset
as a sorted list. -/
def accTerm (a : Acc v) : Erl :=
  .tuple [Ty.canonBy σ v.records a.state.records, .list (machinesTerm σ a.state.machines),
    .list (Erl.sort (a.state.pending.map fun p =>
      .tuple [.int (τ p.id), senderTerm σ p.sender, .bin p.external, requestTerm σ p.request])),
    .int a.state.now, .int a.state.fresh, .int a.state.nextId,
    .list (Erl.sort (a.events.map (Ty.canonBy σ v.event))),
    .list (Erl.sort (a.out.map fun o => .tuple [.int (τ o.id), .bin o.external, .bin o.name, wireTerm σ o.input])),
    .list (Erl.sort (a.own.map (effectTerm σ)))]

end Terms

/-- Every order of the list. -/
def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap fun p => (List.range (p.length + 1)).map fun i => p.insertIdx i x

/-- The most wire ids a pair may send for `sameUpToPair` to search their orders. -/
def wireSearchCap : Nat := 7

/-- Whether `A` and `C`, the two orders of a pair run from a step with the counter `f` and the next wire id `n0`,
are the same once the names the pair made are renamed: the counters `f` and `f + 1` kept or swapped, and the wire ids
from `n0` on permuted. None when the pair sent more wire ids than `wireSearchCap`. -/
def sameUpToPair (f n0 : Nat) (A C : Acc v) : Option Bool :=
  let k := C.state.nextId - n0
  if k > wireSearchCap then none else
  let target := accTerm id id A
  some ([id, swapFn f].any fun σ => (perms (List.range k)).any fun p =>
    accTerm σ (fun i => match p[i - n0]? with
      | some j => if n0 ≤ i then n0 + j else i
      | none => i) C == target)

/-- How the two orders of a pair of own effects compare, run in Lean from a step in progress: `e1` then `e2`, and
the canonical other order (`Step.canonPair`). `some false` where they do not commute: the second faults alone but not
after the first, or the two orders end differently under every renaming `sameUpToPair` searches. `some true` where
they end the same up to such a renaming, and none where the pair sent more wire ids than the search covers. An error
names what no counterexample of a pair's target question gives: the first faults, the second faults in both orders,
or both orders fault. -/
def pairOrders (T : List TypeDecl) (a0 : Step.Acc v) (e1 e2 : EffectV v.event) : Except String (Option Bool) :=
  match Step.runOwn T a0 e1 with
  | .error _ => .error "faults in its first step"
  | .ok b =>
    match Step.runOwn T (a0.withFresh (a0.state.fresh + 1)) e2, Step.runOwn T b e2, Step.canonPair T a0 e1 e2 with
    | .error _, .error _, _ => .error "has the second step fault in both orders"
    | .error _, .ok _, _ => .ok (some false)
    | .ok _, .error _, .error _ => .error "has both orders fault"
    | .ok _, .ok A, .ok C => .ok (sameUpToPair a0.state.fresh a0.state.nextId A C)
    | .ok _, _, _ => .ok (some false)

end Tazuna.Smt
