/-!
Explore's search over paths after a scenario (search.ts), in the abstract: breadth-first, layer by layer, extending only
the first state of each fingerprint. The queue of search.ts takes the states in this order.
-/

namespace Tazuna.Explore

/--
A search space: `next` lists the inputs after a state and `step` takes one. `here` is what extending a state reports,
such as a fault of enumerating its moves, and `out` is what taking an input reports, such as the violations and reached
parts of the path it ends.
-/
structure Space (S I R : Type) where
  next : S → List I
  step : S → I → S
  here : S → List R
  out : S → I → List R

variable {S I R K : Type}

/-- What every path of up to `k` inputs after `s` reports, without merging. -/
def Space.tree (sp : Space S I R) : Nat → S → List R
  | 0, _ => []
  | k + 1, s => sp.here s ++ (sp.next s).flatMap fun i => sp.out s i ++ sp.tree k (sp.step s i)

/-- The states of `frontier` whose fingerprint is not in `visited` and not that of an earlier one, in order. -/
def fresh [DecidableEq K] (fp : S → K) (visited : List K) : List S → List S
  | [] => []
  | s :: ss => if fp s ∈ visited then fresh fp visited ss else s :: fresh fp (fp s :: visited) ss

/--
What the search reports in `k` more layers from `frontier`, with the fingerprints of the states extended so far in
`visited`: each state of the layer whose fingerprint is fresh is extended, and the next layer is the states its inputs
lead to.
-/
def Space.merged [DecidableEq K] (sp : Space S I R) (fp : S → K) : Nat → List S → List K → List R
  | 0, _, _ => []
  | k + 1, frontier, visited =>
    let kept := fresh fp visited frontier
    kept.flatMap (fun s => sp.here s ++ (sp.next s).flatMap (sp.out s)) ++
      sp.merged fp k (kept.flatMap fun s => (sp.next s).map (sp.step s)) (visited ++ kept.map fp)

end Tazuna.Explore
