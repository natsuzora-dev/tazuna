import Tazuna.Data.Wire

namespace Tazuna.Syntax

open Tazuna.Data

inductive StateKind where
  | atomic
  | compound
  | parallel
  | final
  | history
  /-- A state that runs its children as one copy per key from `items`. The map state itself enters no child. -/
  | map
deriving DecidableEq, Repr, Inhabited

derive_wire StateKind

/-- The shape of one state. `path` lists the names from the root's child down to the state itself. -/
structure Shape where
  name : String
  path : List String
  parent : Option String
  initial : Option String
  children : List String
  kind : StateKind
  targets : List String
deriving Repr, Inhabited

def pathNamed (shapes : List Shape) (n : String) : Option (List String) := (shapes.find? (·.name == n)).map (·.path)

/--
Whether the shapes are in preorder (document order): no name repeats, the path ends with the state's own name, and
the parent path is a prefix of the previous state's path. `stack` is the previous path, and `seen` holds the earlier
names.
-/
def preorder (stack seen : List String) : List Shape → Bool
  | [] => true
  | s :: rest =>
    s.path == s.path.dropLast ++ [s.name] && s.path.dropLast.isPrefixOf stack && !seen.contains s.name &&
      preorder s.path (seen ++ [s.name]) rest

theorem preorder_path (stack seen : List String) (l : List Shape) (h : preorder stack seen l = true) :
    ∀ x ∈ l, x.path = x.path.dropLast ++ [x.name] := by
  induction l generalizing stack seen with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
    simp only [preorder, Bool.and_eq_true, beq_iff_eq] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1.1.1
    · exact ih _ _ h.2 x hx

/-- The map state above `n`, or `none` when `n` is not inside a map. -/
def mapAbove (shapes : List Shape) (n : String) : Option String :=
  ((pathNamed shapes n).getD []).dropLast.find? fun a => shapes.any fun d => d.name == a && d.kind == .map

def targetInScope (shapes : List Shape) (source : Option String) (t : String) : Bool :=
  (pathNamed shapes t).isSome && mapAbove shapes t == source.bind (mapAbove shapes)

def shapeInTree (shapes : List Shape) (s : Shape) : Bool :=
  s.targets.all (targetInScope shapes (some s.name)) &&
  (s.kind != .final || mapAbove shapes s.name == none) &&
  ((s.kind != .final && s.kind != .history) || s.children.isEmpty) &&
  (if s.kind == .parallel || s.children.isEmpty then s.initial.isNone else s.initial.isSome) &&
  s.parent == s.path.dropLast.getLast? &&
  (s.parent.all fun p => pathNamed shapes p == some s.path.dropLast) &&
  s.children == (shapes.filter (·.parent == some s.name)).map (·.name) &&
  s.children.all (fun ch => pathNamed shapes ch == some (s.path ++ [ch])) &&
  s.initial.all (· ∈ s.children) &&
  (s.kind != .map || !shapes.any fun d => d.kind == .map && d.name != s.name && s.name ∈ d.path)

/--
Whether the shapes form a state tree. The states are in preorder. Each state's parent is the second-to-last name of
its path, children are listed in document order with extended paths, and `initial` is one of them. A compound
non-parallel state has `initial`; a parallel state has none; final and history states have no children. Inside a map
there is no map state (copies do not nest) and no final state (a copy ends only when its key leaves `items`). A
transition target is in the same copy scope as its source: copy transitions stay inside their map.
-/
def stateTree (shapes : List Shape) : Bool :=
  preorder [] [] shapes && shapes.all (shapeInTree shapes)

/--
Whether `n` has neither `@` nor `[`. A copy's resource is `{owner}@{map}[{key}]`, so a state name with `@` or `[`
could make two copies collide.
-/
def plainName (n : String) : Bool := !n.toList.contains '@' && !n.toList.contains '['

/--
Whether the shapes form the state tree of a chart whose initial is a child of the root, whose state names are all
plain (`plainName`), and whose machine-level `on` transitions target states outside copies.
-/
def chartTree (shapes : List Shape) (initial : String) (rootTargets : List String) : Bool :=
  stateTree shapes &&
    (shapes.any (fun s => s.name == initial && s.parent == none) && shapes.all (plainName ·.name) &&
      rootTargets.all (targetInScope shapes none))

theorem stateTree_of_chartTree {shapes : List Shape} {initial : String} {rootTargets : List String}
    (h : chartTree shapes initial rootTargets = true) : stateTree shapes = true := by
  simp only [chartTree, Bool.and_eq_true] at h
  exact h.1

end Tazuna.Syntax
