import Tazuna.Semantics.Valid
import Tazuna.Smt.NameCode

/-! The inputs `explore` tries from a state, TLC's next-state relation over the constants a model gives: per input
kind, every value its type allows over the leaves the model and the state give (`Domain`). An Int or String field
takes the kind's value set (`tazuna.values`), an id one the service made that an out line showed and the state still
holds, an outside id the state holds, or one new outside id, an instant the state's time or that time plus a wait,
and a list, bag or table at most `others_at_most` items. A Date and a fresh-id source take none: no wire value
carries a Date the spec could not write itself, and a source never crosses the wire. Every choice is a list in a
fixed order, so the inputs and their order are a function of the state. -/

namespace Tazuna.Explore

open Tazuna.Ir Tazuna.Ir.Step

/-- What the leaves of one input kind's values range over. -/
structure Domain where
  ints : List Int
  strs : List Str
  ids : List IdV
  instants : List Int
  items : Nat

/-- Every list of at most `n` items of `xs`. -/
def seqs {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: xs.flatMap fun x => (seqs xs n).map (x :: ·)

/-- Every list of at most `n` items of `xs` whose positions in `xs` do not decrease (`strict`: increase): each
multiset (each set) of `xs` once. -/
def picks {α : Type} (strict : Bool) : List α → Nat → List (List α)
  | _, 0 => [[]]
  | [], _ + 1 => [[]]
  | x :: xs, n + 1 => (picks strict (if strict then xs else x :: xs) n).map (x :: ·) ++ picks strict xs (n + 1)
termination_by xs n => (n, xs.length)

/-- Every way to give each key one of the values `vs`, in the keys' order. -/
def pairsOf {α β : Type} (vs : List β) : List α → List (List (α × β))
  | [] => [[]]
  | k :: ks => vs.flatMap fun x => (pairsOf vs ks).map ((k, x) :: ·)

mutual
/-- The values of the type explore tries. -/
def cands (d : Domain) : (t : Ty) → List t.den0
  | .int => d.ints
  | .str => d.strs
  | .point .ms => d.instants
  | .point .day => []
  | .id => d.ids
  | .list t => seqs (cands d t) d.items
  | .bag t => picks false (cands d t) d.items
  | .table k v =>
    let vs := cands d v
    (picks true (cands d k) d.items).flatMap fun ks =>
      (pairsOf vs ks).filterMap fun xs =>
        if h : KeysUnique (Ty.semWith Dsl.base k).2 xs then some ⟨xs, h⟩ else none
  | .tuple ts => candss d ts
  | .adt _ _ vs => candAlts d vs
  | .fn .. | .param _ | .dsl .. => []
def candss (d : Domain) : (ts : List Ty) → List (Ty.semsWith Dsl.base ts).1
  | [] => [()]
  | t :: ts => (cands d t).flatMap fun x => (candss d ts).map (x, ·)
def candAlts (d : Domain) : (vs : List (List Ty)) → List (Ty.semAltsWith Dsl.base vs).1
  | [] => []
  | fs :: vs => (candss d fs).map .inl ++ (candAlts d vs).map .inr
end

end Tazuna.Explore
