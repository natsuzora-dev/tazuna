import Tazuna.Spec.Tree
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Data.List
import Tazuna.Thm.Spec.Shape
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Spec.Tree

open Tazuna.Data Tazuna.Spec
open Tazuna.Thm.Data.Basic Tazuna.Thm.Data.List Tazuna.Thm.Spec.Shape

theorem mem_addDefaults_of_mem (t : Tree) (n : String) {acc : List String} {x : String} (hx : x ∈ acc) :
    x ∈ t.addDefaults n acc := by
  suffices ∀ k n (acc : List String), t.maxDepth + 1 - (t.pathOf n).length = k → ∀ x, x ∈ acc → x ∈ t.addDefaults n acc
    from this _ n acc rfl x hx
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro n acc hk x hx
    rw [Tree.addDefaults.eq_def]
    split
    · exact hx
    · rename_i st h
      split
      · exact hx
      · exact mem_foldl_of_mem _ (fun _ child y hy =>
          ih _ (hk ▸ t.child_deeper h (t.defaultChildren_mem h child.2)) child.1 _ rfl y (mem_addName_of_mem child.1 hy))
          _ hx

@[guarantee] theorem enters_initial (t : Tree) (p : String) (st : Shape) (child : String) (acc : List String)
    (hs : t.state? p = some st) (hk : st.kind ≠ .parallel) (hm : st.kind ≠ .map) (hi : st.initial = some child) :
    child ∈ t.addDefaults p acc := by
  have hk' : (st.kind == .parallel) = false := by simpa using hk
  have hm' : (st.kind == .map) = false := by simpa using hm
  rw [Tree.addDefaults.eq_def]
  split
  · rename_i h; rw [hs] at h; cases h
  · rename_i st' h
    rw [hs] at h; cases h
    simp only [hm', Bool.false_eq_true, ↓reduceIte]
    have hd : t.defaultChildren p st = [child] := by simp [Tree.defaultChildren, hk', hi]
    generalize hl : (t.defaultChildren p st).attach = l
    have : l.map (·.1) = [child] := by rw [← hl, List.attach_map_subtype_val, hd]
    match l, this with
    | [⟨_, _⟩], rfl => exact mem_addDefaults_of_mem t _ (mem_addName_self acc _)

theorem withoutParallel_le (t : Tree) (path : List String) (k : Nat) : t.withoutParallel path k ≤ k := by
  induction k with
  | zero => simp [Tree.withoutParallel]
  | succ k ih =>
    simp only [Tree.withoutParallel]
    split
    · omega
    · exact Nat.le_refl _

theorem commonPrefix_append (l a b : List String) : commonPrefix (l ++ a) (l ++ b) = l.length + commonPrefix a b := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.cons_append, commonPrefix, ↓reduceIte, ih, List.length_cons]; omega

theorem pathOf_parent_eq (t : Tree) {n p : String} {st : Shape} (h : t.state? n = some st) (hp : st.parent = some p) :
    t.pathOf p = st.path.dropLast := by
  have ht := t.shape_tree (t.state?_mem h)
  simp only [shapeInTree, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Tree.pathNamed_eq] at ht
  have hpar := ht.1.1.1.1.2
  simp only [hp, Option.all_some, beq_iff_eq] at hpar
  simp only [Tree.pathOf]
  cases hs : t.state? p with
  | none => simp [hs] at hpar
  | some ps => simp only [hs, Option.map_some, Option.some.injEq] at hpar; simp [hpar]

theorem parent_of_dropLast (t : Tree) {n : String} {st : Shape} (h : t.state? n = some st) (hd : st.path.dropLast ≠ []) :
    ∃ p, st.parent = some p := by
  have ht := t.shape_tree (t.state?_mem h)
  simp only [shapeInTree, Bool.and_eq_true, beq_iff_eq] at ht
  have hpar : st.parent = st.path.dropLast.getLast? := ht.1.1.1.1.1.2
  rw [hpar]
  exact ⟨_, List.getLast?_eq_some_getLast hd⟩

theorem pathOf_getElem? (t : Tree) : ∀ (len : Nat) (n : String), (t.pathOf n).length = len →
    ∀ k q, (t.pathOf n)[k]? = some q → t.pathOf q = (t.pathOf n).take (k + 1) := by
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
    intro n hlen k q hq
    cases hs : t.state? n with
    | none => simp [Tree.pathOf, hs] at hq
    | some st =>
      have hpn : t.pathOf n = st.path := t.pathOf_of_state? hs
      have hlast := t.path_last (t.state?_mem hs)
      have hname : st.name = n := by simpa using List.find?_some hs
      have hk : k < st.path.length := by
        rw [hpn] at hq; exact (List.getElem?_eq_some_iff.mp hq).1
      rw [hpn] at hq ⊢
      rw [hlast] at hq hk ⊢
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hk' : k < st.path.dropLast.length
      · have hd : st.path.dropLast ≠ [] := by intro e; simp [e] at hk'
        obtain ⟨p, hp⟩ := parent_of_dropLast t hs hd
        have hpp := pathOf_parent_eq t hs hp
        rw [List.getElem?_append_left hk', ← hpp] at hq
        have hlp : (t.pathOf p).length < len := by
          have := t.pathOf_parent hs hp
          omega
        rw [ih _ hlp p rfl k q hq, hpp, List.take_append_of_le_length (by omega)]
      · have hk2 : k = st.path.dropLast.length := by omega
        subst hk2
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_singleton, ↓reduceIte,
          Option.some.injEq] at hq
        subst hq
        rw [List.take_of_length_le (by simp), ← hlast, ← hpn, hname]

theorem pathOf_of_mem_path (t : Tree) (x n : String) (ps rs : List String) (h : t.pathOf x = ps ++ n :: rs) :
    t.pathOf n = ps ++ [n] := by
  have hk : (t.pathOf x)[ps.length]? = some n := by simp [h]
  rw [pathOf_getElem? t _ x rfl ps.length n hk, h, List.take_append]
  simp [List.take_of_length_le (Nat.le_succ ps.length)]

theorem not_mem_path_init (t : Tree) (n : String) (ps : List String) (h : t.pathOf n = ps ++ [n]) : n ∉ ps := by
  intro hm
  obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem hm
  have hk : (t.pathOf n)[j]? = some n := by
    rw [h, List.getElem?_append_left hj, List.getElem?_eq_getElem hj, hjn]
  have := congrArg List.length (pathOf_getElem? t _ n rfl j n hk)
  rw [h] at this
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.length_take,
      Nat.add_min_add_right, Nat.add_right_cancel_iff] at this
  omega

theorem commonPrefix_within (ps rt : List String) (n : String) :
    commonPrefix (ps ++ n :: rt) (ps ++ [n]) = ps.length + 1 := by
  rw [commonPrefix_append]; cases rt <;> simp [commonPrefix]

theorem mem_exitOrder (t : Tree) (names : List String) (n : String) (st : Shape) (hs : t.state? n = some st)
    (hn : n ∈ names) : n ∈ t.exitOrder names := by
  simp only [Tree.exitOrder, List.mem_filter, List.mem_reverse, List.mem_map, decide_eq_true_eq]
  refine ⟨⟨st, List.mem_of_find?_eq_some hs, ?_⟩, hn⟩
  simpa using List.find?_some hs

theorem ancestor_before (t : Tree) (x y : String) (hy : y ∈ t.pathOf x) (hne : y ≠ x) :
    ∃ A B, t.states.map (·.name) = A ++ x :: B ∧ y ∈ A := by
  unfold Tree.pathOf at hy
  cases hs : t.state? x with
  | none => simp [hs] at hy
  | some st =>
    simp only [hs, Option.map_some, Option.getD_some] at hy
    have hname : st.name = x := by simpa using List.find?_some hs
    have hsh := t.shaped
    simp only [stateTree, Bool.and_eq_true] at hsh
    obtain ⟨A, B, hAB, hA⟩ := preorder_split [] [] _ hsh.1 (fun _ h => (nomatch h)) st (t.state?_mem hs)
    have hlast := t.path_last (t.state?_mem hs)
    have hyd : y ∈ st.path.dropLast := by
      rw [hlast] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hy
      · exact absurd (List.mem_singleton.mp hy) (hname ▸ hne)
    refine ⟨A, B, ?_, hA y hyd⟩
    rw [← hname]
    simpa using hAB

@[guarantee] theorem exitOrder_descendants_first (t : Tree) (names : List String) (x y : String) (hy : y ∈ t.pathOf x) (hne : y ≠ x)
    (hx : x ∈ names) (hyn : y ∈ names) : [x, y].Sublist (t.exitOrder names) := by
  obtain ⟨A, B, hAB, hyA⟩ := ancestor_before t x y hy hne
  unfold Tree.exitOrder
  rw [hAB]
  have h : ([x] ++ [y]).Sublist ((B.reverse ++ [x]) ++ A.reverse) :=
    (List.singleton_sublist.mpr (by simp)).append (List.singleton_sublist.mpr (List.mem_reverse.mpr hyA))
  have hf := (show [x, y].Sublist (A ++ x :: B).reverse by simpa using h).filter (· ∈ names)
  simpa [hx, hyn] using hf

@[guarantee] theorem entryOrder_ancestors_first (t : Tree) (names : List String) (x y : String) (hy : y ∈ t.pathOf x) (hne : y ≠ x)
    (hx : x ∈ names) (hyn : y ∈ names) : [y, x].Sublist (t.entryOrder names) := by
  obtain ⟨A, B, hAB, hyA⟩ := ancestor_before t x y hy hne
  unfold Tree.entryOrder
  rw [hAB]
  have h : ([y] ++ [x]).Sublist (A ++ x :: B) :=
    (List.singleton_sublist.mpr hyA).append (List.singleton_sublist.mpr (by simp))
  have hf := (show [y, x].Sublist (A ++ x :: B) by simpa using h).filter (· ∈ names)
  simpa [hx, hyn] using hf

theorem exits_of_domainDepth_le (t : Tree) (entered : List String) (source : Option String) (target n : String)
    (reenter : Bool) (ps rt : List String) (hp : t.pathOf n = ps ++ [n]) (ht : t.pathOf target = ps ++ n :: rt)
    (he : n ∈ entered) (hd : t.domainDepth source target reenter ≤ ps.length) :
    n ∈ t.exitSet entered source target reenter := by
  have hn := not_mem_path_init t n ps hp
  have hst : ∃ st, t.state? n = some st := by
    cases h : t.state? n with
    | none => simp [Tree.pathOf, h] at hp
    | some st => exact ⟨st, rfl⟩
  obtain ⟨st, hst⟩ := hst
  replace he := mem_exitOrder t entered n st hst he
  simp only [Tree.exitSet, ht]
  generalize t.domainDepth source target reenter = k at hd ⊢
  cases k with
  | zero => simpa using he
  | succ k =>
    have hk : k < ps.length := by omega
    have hd : (ps ++ n :: rt)[k]? = some ps[k] := by
      rw [getElem?_append_left' hk]; exact List.getElem?_eq_getElem hk
    simp only [Nat.add_sub_cancel, hd]
    have hne : ps[k] ≠ n := fun h => hn (h ▸ List.getElem_mem hk)
    simp [Tree.isDescendant, hp, Ne.symm hne, List.getElem_mem hk, he]

@[guarantee] theorem reenter_false_not_exited (t : Tree) (entered : List String) (source target : String) (ps rt : List String)
    (hs : t.pathOf source = ps ++ [source]) (ht : t.pathOf target = ps ++ source :: rt) :
    source ∉ t.exitSet entered (some source) target false := by
  simp [Tree.exitSet, Tree.domainDepth, hs, ht, commonPrefix_within]

@[guarantee] theorem reenter_true_exits (t : Tree) (entered : List String) (source target : String) (ps rt : List String)
    (hs : t.pathOf source = ps ++ [source]) (ht : t.pathOf target = ps ++ source :: rt)
    (he : source ∈ entered) : source ∈ t.exitSet entered (some source) target true := by
  refine exits_of_domainDepth_le t entered _ target source true ps rt hs ht he ?_
  have := withoutParallel_le t (ps ++ source :: rt) ps.length
  simpa [Tree.domainDepth, hs, ht, commonPrefix_within] using this

@[guarantee] theorem ancestor_target_exits (t : Tree) (entered : List String) (source target : String) (ps rs : List String)
    (reenter : Bool) (hs : t.pathOf source = ps ++ target :: rs) (hr : rs ≠ []) (he : target ∈ entered) :
    target ∈ t.exitSet entered (some source) target reenter := by
  have ht := pathOf_of_mem_path t source target ps rs hs
  refine exits_of_domainDepth_le t entered _ target target reenter ps [] ht ht he ?_
  have hc : commonPrefix (ps ++ [target]) (ps ++ target :: rs) = ps.length + 1 := by
    rw [commonPrefix_append]; cases rs <;> simp [commonPrefix]
  have hne : (ps.length + 1 == (ps ++ target :: rs).length) = false := by
    cases rs with
    | nil => exact absurd rfl hr
    | cons _ _ => simp
  have := withoutParallel_le t (ps ++ [target]) ps.length
  simpa [Tree.domainDepth, hs, ht, hc, hne, hr] using this

end Tazuna.Thm.Spec.Tree
