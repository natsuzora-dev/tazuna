import Tazuna.Explore.Inputs

/-! The key `explore` dedupes states by, exact as TLC's state set with a view and symmetry (Lamport, "Real Time is
Really Simple", sec 4.1): two states share a key when they are the same once the step counters their ids came from are
renamed, the wire ids of their pending requests likewise, and every instant is read relative to the state's time. A
number below the next one a step takes is renamed to its rank among those the state holds, and one from there on keeps
its distance from it, so a step cannot tell two such states apart: no spec can write an instant or a counter, and the
canonical order compares fresh ids only by their counters' order, which the renaming keeps. -/

namespace Tazuna.Explore

open Tazuna.Ir Tazuna.Ir.Step

mutual
/-- The ids a value holds, in no particular order. -/
def idsIn : (t : Ty) → t.den0 → List IdV
  | .list t, xs | .bag t, xs => xs.flatMap (idsIn t)
  | .tuple ts, x => idssIn ts x
  | .adt _ _ vs, x => idsAltsIn vs x
  | .table k v, x => x.1.flatMap fun e => idsIn k e.1 ++ idsIn v e.2
  | .id, n => [n]
  | .int, _ | .str, _ | .point _, _ | .fn .., _ | .param _, _ | .dsl .., _ => []
def idssIn : (ts : List Ty) → (Ty.semsWith Dsl.base ts).1 → List IdV
  | [], () => []
  | t :: ts, (x, xs) => idsIn t x ++ idssIn ts xs
def idsAltsIn : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → List IdV
  | [], x => nomatch x
  | fs :: _, .inl x => idssIn fs x
  | _ :: vs, .inr y => idsAltsIn vs y
end

mutual
/-- The step counters a value holds: of its fresh ids and its fresh-id sources, in no particular order. -/
def ctrsIn : (t : Ty) → t.den0 → List Nat
  | .list t, xs | .bag t, xs => xs.flatMap (ctrsIn t)
  | .tuple ts, x => ctrssIn ts x
  | .adt _ _ vs, x => ctrsAltsIn vs x
  | .table k v, x => x.1.flatMap fun e => ctrsIn k e.1 ++ ctrsIn v e.2
  | .id, .fresh c _ => [c]
  | .dsl .fresh _, n => [show Nat from n]
  | .id, .named _ | .int, _ | .str, _ | .point _, _ | .fn .., _ | .param _, _ | .dsl .., _ => []
def ctrssIn : (ts : List Ty) → (Ty.semsWith Dsl.base ts).1 → List Nat
  | [], () => []
  | t :: ts, (x, xs) => ctrsIn t x ++ ctrssIn ts xs
def ctrsAltsIn : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → List Nat
  | [], x => nomatch x
  | fs :: _, .inl x => ctrssIn fs x
  | _ :: vs, .inr y => ctrsAltsIn vs y
end

section Key
attribute [local instance] lexOrd

mutual
/-- A data value as a term, with each fresh id's step counter renamed by `σ` and each instant moved by `δ`
milliseconds: `Ty.canonBy` with a time shift. -/
def keyBy (σ : Nat → Nat) (δ : Int) : (t : Ty) → t.den0 → Erl
  | .int, n => .int n
  | .str, s => .bin s.1
  | .list t, xs => .list (xs.map (keyBy σ δ t))
  | .bag t, xs => .list (Erl.sort (xs.map (keyBy σ δ t)))
  | .tuple ts, x => .tuple (keysBy σ δ ts x)
  | .adt _ _ vs, x => keyAltsBy σ δ 0 vs x
  | .table k v, x =>
    let ps := Erl.sort (x.1.map fun e => (keyBy σ δ k e.1, keyBy σ δ v e.2))
    .map (ps.map (·.1)) (ps.map (·.2))
  | .point .ms, d => .int ((show Int from d) + δ)
  | .point .day, d => .int d
  | .id, .fresh s i => .tuple [.int (σ s), .int i]
  | .id, .named s => .bin s.1
  | .dsl .fresh _, n => .int (σ (show Nat from n))
  | .param _, _ | .fn .., _ | .dsl .., _ => .atom ""
def keysBy (σ : Nat → Nat) (δ : Int) : (ts : List Ty) → (Ty.semsWith Dsl.base ts).1 → List Erl
  | [], () => []
  | t :: ts, (x, xs) => keyBy σ δ t x :: keysBy σ δ ts xs
def keyAltsBy (σ : Nat → Nat) (δ : Int) (k : Nat) : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → Erl
  | [], x => nomatch x
  | fs :: _, .inl x => .tuple (.int k :: keysBy σ δ fs x)
  | _ :: vs, .inr y => keyAltsBy σ δ (k + 1) vs y
end

end Key

/-- A site as a term. -/
def siteKey (s : SiteId) : Erl := .tuple [.bin s.module, .int s.line, .int s.col, .int s.index]

/-- A kept function as a term: its site and the values it captured. Sites are told apart by name (`SitesUnique`), so
the site gives the source. -/
def funKey (σ : Nat → Nat) (δ : Int) {t : Ty} (f : Fun t) : Erl :=
  .tuple [siteKey f.site, keyBy σ δ (.tuple f.Γ) f.env]

mutual
/-- A type as a term, one per type: a pending request's types are part of it. -/
def tyKey : Ty → Erl
  | .int => .int 0
  | .str => .int 1
  | .list t => .tuple [.int 2, tyKey t]
  | .tuple ts => .tuple [.int 3, .list (tysKey ts)]
  | .fn ps r => .tuple [.int 4, .list (tysKey ps), tyKey r]
  | .adt i a vs => .tuple [.int 5, .int i, .list (tysKey a), .list (tyssKey vs)]
  | .param k => .tuple [.int 6, .int k]
  | .bag t => .tuple [.int 7, tyKey t]
  | .table k v => .tuple [.int 8, tyKey k, tyKey v]
  | .point u => .tuple [.int 9, .int u.ctorIdx]
  | .id => .int 10
  | .dsl k a => .tuple [.int 12, .int k.ctorIdx, .list (tysKey a)]
def tysKey : List Ty → List Erl
  | [] => []
  | t :: ts => tyKey t :: tysKey ts
def tyssKey : List (List Ty) → List Erl
  | [] => []
  | ts :: vs => .list (tysKey ts) :: tyssKey vs
end

def senderKey (σ : Nat → Nat) (δ : Int) : Sender → Erl
  | .machine n ⟨t, k⟩ => .tuple [.bin n, tyKey t, keyBy σ δ t k]
  | .reaction n => .bin n

-- A command's answers keep no rules: no `ensures` is a meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
/-- A pending request as a term, its wire id renamed by `ω`. -/
def pendingKey (σ : Nat → Nat) (ω : Nat → Nat) (δ : Int) {e : Ty} (p : Pending e) : Erl :=
  .tuple [.int (ω p.id), senderKey σ δ p.sender, .bin p.external, .bin p.request.name,
    .tuple [tyKey p.request.input, tyKey p.request.output, .list (p.request.rejection.toList.map tyKey)],
    keyBy σ δ p.request.input p.request.value, (p.request.ensures.map (funKey σ δ)).getD (.atom ""),
    funKey σ δ p.request.onAnswer]

def senderCtrs : Sender → List Nat
  | .machine _ ⟨t, k⟩ => ctrsIn t k
  | .reaction _ => []

def funCtrs {t : Ty} (f : Fun t) : List Nat := ctrsIn (.tuple f.Γ) f.env

def pendingCtrs {e : Ty} (p : Pending e) : List Nat :=
  senderCtrs p.sender ++ ctrsIn p.request.input p.request.value ++ (p.request.ensures.toList.flatMap funCtrs) ++
    funCtrs p.request.onAnswer

def senderIds : Sender → List IdV
  | .machine _ ⟨t, k⟩ => idsIn t k
  | .reaction _ => []

def funIds {t : Ty} (f : Fun t) : List IdV := idsIn (.tuple f.Γ) f.env

def pendingIds {e : Ty} (p : Pending e) : List IdV :=
  senderIds p.sender ++ idsIn p.request.input p.request.value ++ (p.request.ensures.toList.flatMap funIds) ++
    funIds p.request.onAnswer

variable {v : ServiceV}

/-- The ids the state holds: in its records, its machines' instances and its pending requests. -/
def stateIds (s : State v) : List IdV :=
  idsIn v.records s.records ++
    (s.machines.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => idsIn m.key i.key ++ idsIn m.state i.state) ++
    s.pending.flatMap pendingIds

/-- The step counters the state holds. -/
def stateCtrs (s : State v) : List Nat :=
  ctrsIn v.records s.records ++
    (s.machines.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => ctrsIn m.key i.key ++ ctrsIn m.state i.state) ++
    s.pending.flatMap pendingCtrs

/-- Where `x` goes among the sorted `xs` between `lo` and `hi`: binary search. -/
def rankGo (xs : Array Nat) (x : Nat) (lo hi : Nat) (h : hi ≤ xs.size) : Nat :=
  if hlt : lo < hi then
    if xs[(lo + hi) / 2]'(by omega) < x then rankGo xs x ((lo + hi) / 2 + 1) hi h
    else rankGo xs x lo ((lo + hi) / 2) (by omega)
  else lo
termination_by hi - lo

/-- The numbers of the sorted `xs` below `x`: its rank. -/
def rankIn (xs : Array Nat) (x : Nat) : Nat := rankGo xs x 0 xs.size (Nat.le_refl _)

/-- The numbers of `xs` below `base`, sorted. -/
def belowOf (xs : List Nat) (base : Nat) : Array Nat := ((xs.filter (· < base)).mergeSort (· ≤ ·)).toArray

/-- A number below `base` as its rank among the sorted `cs`, and one at or past `base` as the count of `cs` plus its
distance from `base`, so the numbers a step takes from `base` on keep their place whatever `base` is. -/
def renameBelow (cs : Array Nat) (base c : Nat) : Nat := if c < base then rankIn cs c else cs.size + (c - base)

end Tazuna.Explore
