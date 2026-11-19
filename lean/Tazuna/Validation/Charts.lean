import Tazuna.Validation.Illegal

namespace Tazuna.Validation.Charts

open Tazuna.Data
open Tazuna.Spec

def parentKeys (c : Chart) : List String :=
  [("input", c.input), ("requires", c.requires), ("output", c.output), ("ensures", c.ensures)].filterMap
    fun (key, names) => if names.isEmpty then none else some key

def missingParents (s : Structure) : List Illegal :=
  s.definitions.filterMap fun d =>
    match d.body with
    | .screen c =>
      if !(parentKeys c).isEmpty && !s.isOpenedByScreen d.ref then some (.missingParent d.ref (parentKeys c))
      else none
    | _ => none

def ownQueries (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    match d.chart? with
    | some c =>
      c.queries.filterMap fun (key, q) =>
        q.bind fun q => if q.service == d.service then some (.ownQuery d.ref key) else none
    | none => []

def unlistedControls (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    match d.chart? with
    | some c => (c.controls.filter fun (k, _) => !c.offers.any (·.1 == k)).map fun (k, _) => .unlistedControl d.ref k
    | none => []

/--
The states whose always transitions are re-evaluated after `t`, in document order. For a history target, every state
that it may restore counts as entered: its targets without a record, and every child that a record may hold. A map
state's record is empty, since only copies enter its children.
-/
def lands (c : Chart) (source : String) (t : Transition) : List String :=
  match t.target with
  | none => [source]
  | some target =>
    let tree := c.tree
    let common := tree.domainDepth (some source) target t.reenters
    let found := c.state? target
    let history := (found.map (·.kind)) == some .history
    let recordable :=
      match found.bind (·.parent) with
      | some p => if history && tree.kindOf p != some .map then tree.enterable p else []
      | none => []
    let candidates := tree.historyTargets c.initial [] target ++ recordable
    let entering := candidates.foldl (fun acc cand => tree.addEntrySet [] common cand acc) []
    let entering := if !history && (tree.pathOf target).length ≤ common then addName entering target else entering
    let entering := if (tree.pathOf source).length ≤ common then addName entering source else entering
    tree.entryOrder entering

structure Edge where
  «from» : String
  lands : List String
  guarded : Bool

def edges (c : Chart) : List Edge :=
  c.states.flatMap fun st =>
    (st.transitions.filter (·.trigger == .always)).map fun t =>
      { «from» := st.name, lands := lands c st.name t, guarded := t.guarded }

/-- The BFS queue, and the predecessor of each found state. -/
abbrev Frontier := List String × List (String × String)

def visit (f : Frontier) (to «from» : String) : Frontier :=
  if f.2.any (·.1 == to) then f else (f.1 ++ [to], f.2 ++ [(to, «from»)])

def visitAll (s : String) (f : Frontier) (lands : List String) : Frontier := lands.foldl (fun f to => visit f to s) f

inductive Search where
  | cycle (predecessors : List (String × String))
  | none

def unvisited (states : List String) (f : Frontier) : Nat := (states.filter fun v => !f.2.any (·.1 == v)).length

theorem visit_le (U : List String) (f : Frontier) (to fr : String) : unvisited U (visit f to fr) ≤ unvisited U f := by
  unfold visit
  split
  · exact Nat.le_refl _
  · unfold unvisited
    apply filter_length_le
    intro v hv
    simp only [List.any_append, Bool.not_or, Bool.and_eq_true] at hv
    exact hv.1

theorem visit_progress (U : List String) (f : Frontier) (to fr : String) (hto : to ∈ U) :
    visit f to fr = f ∨ unvisited U (visit f to fr) < unvisited U f := by
  unfold visit
  split
  · exact .inl rfl
  · rename_i h
    refine .inr ?_
    unfold unvisited
    apply filter_length_lt _ _ _ to (by cases hh : f.2.any (·.1 == to) <;> simp_all) (by simp) _ hto
    intro v hv
    simp only [List.any_append, Bool.not_or, Bool.and_eq_true] at hv
    exact hv.1

theorem foldl_progress {α : Type} (U : List String) (g : Frontier → α → Frontier) (xs : List α)
    (hle : ∀ f x, unvisited U (g f x) ≤ unvisited U f)
    (hp : ∀ f, ∀ x ∈ xs, g f x = f ∨ unvisited U (g f x) < unvisited U f) :
    ∀ f, xs.foldl g f = f ∨ unvisited U (xs.foldl g f) < unvisited U f := by
  have mono : ∀ (ys : List α) (f : Frontier), unvisited U (ys.foldl g f) ≤ unvisited U f := by
    intro ys
    induction ys with
    | nil => intro f; exact Nat.le_refl _
    | cons y ys ih => intro f; exact Nat.le_trans (ih _) (hle f y)
  induction xs with
  | nil => intro f; exact .inl rfl
  | cons x xs ih =>
    intro f
    simp only [List.foldl_cons]
    rcases hp f x (List.mem_cons_self) with e | lt
    · rw [e]; exact ih (fun f y hy => hp f y (List.mem_cons_of_mem _ hy)) f
    · exact .inr (Nat.lt_of_le_of_lt (mono xs _) lt)

def expand (es : List Edge) (s : String) (f : Frontier) : Frontier :=
  (es.filter (·.«from» == s)).foldl (fun f e => visitAll s f e.lands) f

theorem expand_progress (es : List Edge) (s : String) (f : Frontier) :
    expand es s f = f ∨ unvisited (es.flatMap (·.lands)) (expand es s f) < unvisited (es.flatMap (·.lands)) f := by
  let U := es.flatMap (·.lands)
  have hvle : ∀ (lands : List String) (f : Frontier), unvisited U (visitAll s f lands) ≤ unvisited U f := by
    intro lands
    induction lands with
    | nil => intro f; exact Nat.le_refl _
    | cons x xs ih => intro f; exact Nat.le_trans (ih _) (visit_le U f x s)
  unfold expand
  refine foldl_progress U (fun f (e : Edge) => visitAll s f e.lands) _ (fun f e => hvle e.lands f) ?_ f
  intro f e he
  exact foldl_progress U (fun f to => visit f to s) e.lands (fun f to => visit_le U f to s)
    (fun f to hto => visit_progress U f to s
      (List.mem_flatMap.mpr ⟨e, (List.mem_filter.mp he).1, hto⟩)) f

def search (es : List Edge) (start : String) (f : Frontier) : Search :=
  match f with
  | ([], _) => .none
  | (s :: rest, predecessors) =>
    if s == start then .cycle predecessors else search es start (expand es s (rest, predecessors))
termination_by (unvisited (es.flatMap (·.lands)) f, f.1.length)
decreasing_by
  rcases expand_progress es s (rest, predecessors) with e | lt
  · rw [e]; exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (by simpa [unvisited] using lt)

/-- The path from `start` back to `start` through `predecessors`. -/
def pathBack (start : String) (predecessors : List (String × String)) (s : String) (path : List String) : List String :=
  match _h : predecessors.lookup s with
  | some p => if p == start then start :: path else pathBack start (dropKey predecessors s) p (p :: path)
  | none => start :: path
termination_by predecessors.length
decreasing_by exact length_dropKey_lt _h

def searchFrom (es : List Edge) (e : Edge) : Search :=
  search es e.«from» (visitAll e.«from» ([], []) e.lands)

/--
The path of the first unguarded always transition that leads back to its state. Only cycles that start with an
unguarded always transition count: a cycle of guarded ones may stop on guard values, so `test` catches it with the
always-round limit.
-/
def cyclePath (c : Chart) : Option (List String) :=
  let es := edges c
  (es.filter (!·.guarded)).findSome? fun e =>
    match searchFrom es e with
    | .cycle predecessors => some (pathBack e.«from» predecessors e.«from» [e.«from»])
    | .none => none

def alwaysCycles (s : Structure) : List Illegal :=
  s.definitions.filterMap fun d => d.chart?.bind fun c => (cyclePath c).map (.alwaysCycle d.ref)

/--
Each state with parameters that a history state may restore, with that history state: the history state's siblings,
unless their parent is a map state, whose history enters its initial state.
-/
def restoredHeldOf (c : Chart) : List (String × String) :=
  c.states.flatMap fun st =>
    if !st.hasParameters then [] else
    match st.parent.bind fun p => c.states.find? (·.name == p) with
    | some p =>
      if p.kind == .map then [] else
      (p.children.filter fun h => c.states.any fun x => x.name == h && x.kind == .history).map (st.name, ·)
    | none => []

def restoredHeld (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    match d.chart? with
    | some c => (restoredHeldOf c).map fun (st, h) => .restoredHeld d.ref st h
    | none => []

def check (s : Structure) : List Illegal :=
  missingParents s ++ ownQueries s ++ unlistedControls s ++ alwaysCycles s ++ restoredHeld s

end Tazuna.Validation.Charts
