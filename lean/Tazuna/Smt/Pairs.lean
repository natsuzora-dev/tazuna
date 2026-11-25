import Tazuna.Smt.EncodeThm
import Tazuna.Semantics.Step

/-! The pairs of own kinds T5 asks about. `Step.PairCommutes` is a question about two waiting own effects in an order:
the first runs first, and the other order is the canonical one. A pair whose second effect faults alone but not after
the first is a disabling the other order shows, so both orders of two kinds are asked, and a kind with itself, since
two effects of one kind are two effects. The pairs are the ordered pairs of the own kinds' places among the variants of
the effect datatype (`Layout.ownPairs`), and every two own effects a model codes fall under one
(`ownPairs_complete`, T5b): the kind coverage theorems give every own effect a step starts a variant, so no pair of
waiting effects escapes the questions. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The ordered pairs of own kinds of the event type `e`, self-pairs included, by their places among the own kinds. -/
def Layout.ownPairs (L : Layout) (e : Ty) : List (Nat × Nat) :=
  let n := (L.ownsOf e).length
  (List.range n).flatMap fun i => (List.range n).map fun j => (i, j)

theorem mem_ownPairs {L : Layout} {e : Ty} {i j : Nat} :
    (i, j) ∈ L.ownPairs e ↔ i < (L.ownsOf e).length ∧ j < (L.ownsOf e).length := by
  simp [Layout.ownPairs]

/-- An own effect's code is the variant of an own kind. -/
theorem own_variant {L : Layout} {e : Ty} {x : EffectV e} {z : Val} (hx : EffRel L x z) (hr : x.isRequest = false) :
    ∃ d n k vals, L.find? (.dsl .effect [e]) = some (d, n) ∧ k < (L.ownsOf e).length ∧
      z = .ctor d ((L.effectsOf e).length + k) vals := by
  obtain ⟨d, n, hd, ⟨_, _, _, -, -, hh⟩ | ⟨k, key, vals, hk, rfl, -⟩⟩ := hx
  · cases x with
    | request => simp [EffectV.isRequest] at hr
    | command => exact hh.elim
    | query => exact hh.elim
  · exact ⟨d, n, k, vals, hd, (List.getElem?_eq_some_iff.1 hk).1, rfl⟩

/-- T5b: any two own effects a model codes are effects of a listed pair of own kinds, in their order. -/
theorem ownPairs_complete {L : Layout} {e : Ty} {x1 x2 : EffectV e} {z1 z2 : Val} (h1 : EffRel L x1 z1)
    (h2 : EffRel L x2 z2) (hr1 : x1.isRequest = false) (hr2 : x2.isRequest = false) :
    ∃ p ∈ L.ownPairs e, ∃ d n vals1 vals2, L.find? (.dsl .effect [e]) = some (d, n) ∧
      z1 = .ctor d ((L.effectsOf e).length + p.1) vals1 ∧ z2 = .ctor d ((L.effectsOf e).length + p.2) vals2 := by
  obtain ⟨d, n, k1, vals1, hd, hk1, rfl⟩ := own_variant h1 hr1
  obtain ⟨d', n', k2, vals2, hd', hk2, rfl⟩ := own_variant h2 hr2
  rw [hd] at hd'
  cases hd'
  exact ⟨(k1, k2), mem_ownPairs.2 ⟨hk1, hk2⟩, d, n, vals1, vals2, hd, rfl, rfl⟩

end Tazuna.Smt
