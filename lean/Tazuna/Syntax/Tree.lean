import Tazuna.Data.List
import Tazuna.Syntax.Shape

/-! The exit and entry sets follow computeExitSet and computeEntrySet of W3C SCXML Appendix D. -/

namespace Tazuna.Syntax

open Tazuna.Data

structure Tree where
  states : List Shape
  shaped : stateTree states = true

def Tree.state? (t : Tree) (n : String) : Option Shape := t.states.find? (·.name == n)

def Tree.kindOf (t : Tree) (n : String) : Option StateKind := (t.state? n).map (·.kind)

def Tree.pathOf (t : Tree) (n : String) : List String := ((t.state? n).map (·.path)).getD []

def Tree.parentOf (t : Tree) (n : String) : Option String := (t.state? n).bind (·.parent)

/-- Whether `n` is `anc` or a descendant of `anc`. -/
def Tree.isDescendant (t : Tree) (n anc : String) : Bool := anc ∈ t.pathOf n

def Tree.descendants (t : Tree) (n : String) : List String :=
  (t.states.filter fun d => d.name != n && t.isDescendant d.name n).map (·.name)

def Tree.enterable (t : Tree) (n : String) : List String :=
  (((t.state? n).map (·.children)).getD []).filter fun ch => t.kindOf ch != some .history

def Tree.maxDepth (t : Tree) : Nat := (t.states.map (·.path.length)).foldl max 0

theorem Tree.shape_tree (t : Tree) {st : Shape} (h : st ∈ t.states) : shapeInTree t.states st = true := by
  have := t.shaped
  simp only [stateTree, Bool.and_eq_true, List.all_eq_true] at this
  exact this.2 _ h

theorem Tree.path_last (t : Tree) {st : Shape} (h : st ∈ t.states) : st.path = st.path.dropLast ++ [st.name] := by
  have := t.shaped
  simp only [stateTree, Bool.and_eq_true] at this
  exact preorder_path [] [] _ this.1 st h

theorem Tree.pathNamed_eq (t : Tree) (n : String) : pathNamed t.states n = (t.state? n).map (·.path) := rfl

theorem Tree.state?_mem (t : Tree) {n : String} {st : Shape} (h : t.state? n = some st) : st ∈ t.states :=
  List.mem_of_find?_eq_some h

theorem Tree.pathOf_of_state? (t : Tree) {n : String} {st : Shape} (h : t.state? n = some st) :
    t.pathOf n = st.path := by
  simp [pathOf, h]

theorem Tree.pathOf_child (t : Tree) {n ch : String} {st : Shape} (h : t.state? n = some st) (hc : ch ∈ st.children) :
    t.pathOf ch = st.path ++ [ch] := by
  have ht := t.shape_tree (t.state?_mem h)
  simp only [shapeInTree, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, pathNamed_eq] at ht
  have := ht.1.1.2 ch hc
  simp only [pathOf] at this ⊢
  cases hs : t.state? ch <;> simp_all

theorem Tree.initial_mem_children (t : Tree) {n ch : String} {st : Shape} (h : t.state? n = some st)
    (hi : st.initial = some ch) : ch ∈ st.children := by
  have ht := t.shape_tree (t.state?_mem h)
  simp only [shapeInTree, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ht
  have := ht.1.2
  simp only [hi, Option.all_some, decide_eq_true_eq] at this
  exact this

theorem Tree.pathOf_parent (t : Tree) {n p : String} {st : Shape} (h : t.state? n = some st) (hp : st.parent = some p) :
    (t.pathOf p).length + 1 = (t.pathOf n).length := by
  have ht := t.shape_tree (t.state?_mem h)
  simp only [shapeInTree, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, pathNamed_eq] at ht
  have hpath := t.path_last (t.state?_mem h)
  have hpar := ht.1.1.1.1.2
  simp only [hp, Option.all_some, beq_iff_eq] at hpar
  rw [t.pathOf_of_state? h]
  simp only [pathOf]
  cases hs : t.state? p with
  | none => simp [hs] at hpar
  | some ps =>
    simp only [hs, Option.map_some, Option.some.injEq] at hpar
    simp only [Option.map_some, Option.getD_some, hpar]
    conv => rhs; rw [hpath]
    simp

theorem Tree.pathOf_le_maxDepth (t : Tree) (n : String) : (t.pathOf n).length ≤ t.maxDepth := by
  have base : ∀ (zs : List Nat) (b : Nat), b ≤ zs.foldl max b := by
    intro zs; induction zs with
    | nil => intro b; exact Nat.le_refl b
    | cons z zs ihz => intro b; exact Nat.le_trans (Nat.le_max_left b z) (ihz _)
  have mem : ∀ (ls : List Nat) (acc x : Nat), x ∈ ls → x ≤ ls.foldl max acc := by
    intro ls
    induction ls with
    | nil => intro _ _ hx; cases hx
    | cons y ys ih =>
      intro acc x hx
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_trans (Nat.le_max_right acc x) (base ys _)
      · exact ih _ _ hx
  unfold pathOf maxDepth
  cases hs : t.state? n with
  | none => simp
  | some st => exact mem _ 0 _ (List.mem_map_of_mem (t.state?_mem hs))

def commonPrefix : List String → List String → Nat
  | a :: as, b :: bs => if a = b then commonPrefix as bs + 1 else 0
  | _, _ => 0

/-- The number of the first `k` names of `path` that remain after dropping the trailing parallel states. -/
def Tree.withoutParallel (t : Tree) (path : List String) : Nat → Nat
  | 0 => 0
  | k + 1 => if (path[k]?.bind t.kindOf) == some .parallel then t.withoutParallel path k else k + 1

/--
The depth from the root of the transition domain (SCXML). 0 is the whole chart. For a target that is the source or its
descendant, the domain is the source with `reenter: false` and the source's parent with `reenter: true` (XState v5
reenter). Otherwise it is the nearest ancestor of both, or the target's parent when the target is a proper ancestor of
the source (SCXML findLCCA; even SCXML `type="internal"` exits and re-enters the source for a transition to the
source or an ancestor). A parallel state exits and enters all its regions together, so the domain widens to its
parent, except when `reenter: false` makes the source the domain.
-/
def Tree.domainDepth (t : Tree) (source : Option String) (target : String) (reenter : Bool) : Nat :=
  let tp := t.pathOf target
  let sp := match source with
    | none => []
    | some n => t.pathOf n
  let common := commonPrefix tp sp
  if common == sp.length then (if reenter then t.withoutParallel tp (common - 1) else common)
  else t.withoutParallel tp (if common == tp.length then common - 1 else common)

/-- The names in reverse document order (SCXML exitOrder). -/
def Tree.exitOrder (t : Tree) (names : List String) : List String :=
  (t.states.map (·.name)).reverse.filter (· ∈ names)

def Tree.exitSet (t : Tree) (entered : List String) (source : Option String) (target : String)
    (reenter : Bool) : List String :=
  let tp := t.pathOf target
  let common := t.domainDepth source target reenter
  let domain := if common == 0 then none else tp[common - 1]?
  (t.exitOrder entered).filter fun n =>
    some n != domain && match domain with
      | none => true
      | some d => t.isDescendant n d

def Tree.defaultChildren (t : Tree) (name : String) (st : Shape) : List String :=
  if st.kind == .parallel then t.enterable name else st.initial.toList

theorem Tree.defaultChildren_mem (t : Tree) {name ch : String} {st : Shape} (h : t.state? name = some st)
    (hc : ch ∈ t.defaultChildren name st) : ch ∈ st.children := by
  unfold defaultChildren at hc
  split at hc
  · simp only [enterable, h, Option.map_some, Option.getD_some, List.mem_filter] at hc
    exact hc.1
  · cases hi : st.initial with
    | none => simp [hi] at hc
    | some i =>
      simp only [hi, Option.toList_some, List.mem_singleton] at hc
      exact hc ▸ t.initial_mem_children h hi

theorem Tree.child_deeper (t : Tree) {name ch : String} {st : Shape} (h : t.state? name = some st)
    (hc : ch ∈ st.children) : t.maxDepth + 1 - (t.pathOf ch).length < t.maxDepth + 1 - (t.pathOf name).length := by
  have hle := t.pathOf_le_maxDepth ch
  rw [t.pathOf_child h hc] at hle ⊢
  rw [t.pathOf_of_state? h]
  simp only [List.length_append, List.length_singleton] at hle ⊢
  omega

/--
`acc` with the default descendants of `name` added. Copies enter a map state's children, so a map state has no default
descendants.
-/
def Tree.addDefaults (t : Tree) (name : String) (acc : List String) : List String :=
  match _h : t.state? name with
  | none => acc
  | some st =>
    if st.kind == .map then acc else
    (t.defaultChildren name st).attach.foldl (fun acc child => t.addDefaults child.1 (addName acc child.1)) acc
termination_by t.maxDepth + 1 - (t.pathOf name).length
decreasing_by exact t.child_deeper _h (t.defaultChildren_mem _h child.2)

/--
`acc` with the entry set of `name` added: `name` and its ancestors not yet entered, the other regions of ancestor
parallel states with their defaults, and the defaults of `name`. A copy does not enter its first `depth` ancestors from
the root (the map state and above).
-/
def Tree.addEntrySet (t : Tree) (entered : List String) (depth : Nat) (name : String) (acc : List String) : List String :=
  match t.state? name with
  | none => acc
  | some found =>
    let acc := (found.path.drop depth).foldl (fun acc n => if n ∈ entered then acc else addName acc n) acc
    let acc := found.path.zipIdx.foldl (fun acc (n, i) =>
      if depth ≤ i && t.kindOf n == some .parallel then
        (t.enterable n).foldl (fun acc region =>
          if some region != found.path[i + 1]? && region ∉ entered && region ∉ acc then
            t.addDefaults region (addName acc region)
          else acc) acc
      else acc) acc
    t.addDefaults name acc

/-- The names in document order (SCXML entryOrder). -/
def Tree.entryOrder (t : Tree) (names : List String) : List String :=
  (t.states.map (·.name)).filter (· ∈ names)

def Tree.entrySet (t : Tree) (entered : List String) (depth : Nat) (name : String) : List String :=
  t.entryOrder (t.addEntrySet entered depth name [])

/--
The states that a transition to `target` enters in its place: for an SCXML history state, the children active when
the parent was last exited, or the parent and its defaults if it never was; for any other state, `target` itself.
Copies never exit or enter their map state, so history under a map state enters the map state's initial.
-/
def Tree.historyTargets (t : Tree) (initial : String) (lastChildren : List (String × List String)) (target : String) :
    List String :=
  match t.state? target with
  | some st =>
    if st.kind == .history then
      match st.parent with
      | none => [initial]
      | some p =>
        match lastChildren.lookup p with
        | some (x :: xs) => x :: xs
        | _ =>
          match t.state? p with
          | some ps => if ps.kind == .map then ps.initial.toList else [p]
          | none => [p]
    else [target]
  | none => [target]

def Tree.recordedChildren (t : Tree) (entered : List String) (n : String) : Option (List String) :=
  match t.state? n with
  | some st => if st.children.isEmpty then none else some ((t.enterable n).filter (· ∈ entered))
  | none => none

def Tree.isDone (t : Tree) (entered : List String) (name : String) : Bool :=
  match _h : t.state? name with
  | none => false
  | some st =>
    if _hp : st.kind == .parallel then
      (t.enterable name).attach.all fun r => t.isDone entered r.1
    else st.children.any fun ch => t.kindOf ch == some .final && ch ∈ entered
termination_by t.maxDepth + 1 - (t.pathOf name).length
decreasing_by exact t.child_deeper _h (t.defaultChildren_mem _h (by simp only [Tree.defaultChildren, _hp]; exact r.2))

def Tree.doneAncestors (t : Tree) (entered : List String) (up : Option String) : List String :=
  match up with
  | none => []
  | some u =>
    match _h : t.state? u with
    | none => []
    | some st =>
      if st.kind == .parallel && t.isDone entered u then
        match _hp : st.parent with
        | none => [u]
        | some p => u :: t.doneAncestors entered (some p)
      else []
termination_by (up.map fun u => (t.pathOf u).length).getD 0
decreasing_by
  simp only [Option.map_some, Option.getD_some]
  have := t.pathOf_parent _h _hp
  omega

/--
The states that finish when `parent` enters a final child: `parent`, then each ancestor parallel state that is done, in
finishing order, like SCXML done.state events.
-/
def Tree.finished (t : Tree) (entered : List String) (parent : String) : List String :=
  parent :: t.doneAncestors entered (t.parentOf parent)

def Tree.leaves (t : Tree) (entered : List String) : List String :=
  (t.states.filter fun st => st.name ∈ entered && !(t.enterable st.name).any (· ∈ entered)).map (·.name)

def Tree.isInside (t : Tree) (inner outer : Option String) : Bool :=
  match inner, outer with
  | none, _ => false
  | some _, none => true
  | some i, some o => i != o && t.isDescendant i o

/-- The parallel state whose different regions hold `a` and `b`. -/
def Tree.parallelBetween (t : Tree) (a b : String) : Option String :=
  let pa := t.pathOf a
  let pb := t.pathOf b
  let common := commonPrefix pa pb
  if common == 0 || common == pa.length || common == pb.length then none else
  match pa[common - 1]? with
  | some p => if t.kindOf p == some .parallel then some p else none
  | none => none

end Tazuna.Syntax
