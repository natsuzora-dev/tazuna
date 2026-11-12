import Tazuna.Syntax.Tree
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Data.List
import Tazuna.Thm.Syntax.Shape

namespace Tazuna.Thm.Syntax.Tree

open Tazuna.Data Tazuna.Syntax
open Tazuna.Thm.Data.Basic Tazuna.Thm.Data.List Tazuna.Thm.Syntax.Shape

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

theorem enters_initial (t : Tree) (p : String) (st : Shape) (child : String) (acc : List String)
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

theorem commonPrefix_self (l : List String) : commonPrefix l l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [commonPrefix, ih]

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

theorem commonPrefix_le : ∀ (xs ys : List String), commonPrefix xs ys ≤ xs.length ∧ commonPrefix xs ys ≤ ys.length
  | [], _ => by simp [commonPrefix]
  | _ :: _, [] => by simp [commonPrefix]
  | x :: xs, y :: ys => by
    by_cases he : x = y
    · subst he
      have := commonPrefix_le xs ys
      simp only [commonPrefix, ↓reduceIte, List.length_cons]
      omega
    · simp [commonPrefix, he]

theorem commonPrefix_eq : ∀ (xs ys : List String) (i : Nat), i < commonPrefix xs ys → xs[i]? = ys[i]?
  | [], _, _, h => by simp [commonPrefix] at h
  | _ :: _, [], _, h => by simp [commonPrefix] at h
  | x :: xs, y :: ys, i, h => by
    by_cases he : x = y
    · subst he
      have hc : commonPrefix (x :: xs) (x :: ys) = commonPrefix xs ys + 1 := by simp [commonPrefix]
      rw [hc] at h
      cases i with
      | zero => rfl
      | succ i =>
        simp only [List.getElem?_cons_succ]
        exact commonPrefix_eq xs ys i (by omega)
    · simp [commonPrefix, he] at h

theorem commonPrefix_differs : ∀ (xs ys : List String), commonPrefix xs ys < xs.length → commonPrefix xs ys < ys.length →
    xs[commonPrefix xs ys]? ≠ ys[commonPrefix xs ys]?
  | [], _, h1, _ => by simp at h1
  | _ :: _, [], _, h2 => by simp at h2
  | x :: xs, y :: ys, h1, h2 => by
    by_cases he : x = y
    · subst he
      have hc : commonPrefix (x :: xs) (x :: ys) = commonPrefix xs ys + 1 := by simp [commonPrefix]
      rw [hc] at h1 h2 ⊢
      simp only [List.getElem?_cons_succ, List.length_cons] at h1 h2 ⊢
      exact commonPrefix_differs xs ys (by omega) (by omega)
    · have hc : commonPrefix (x :: xs) (y :: ys) = 0 := by simp [commonPrefix, he]
      rw [hc]
      simp [he]

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

theorem commonPrefix_of_take : ∀ (n : Nat) (xs ys : List String), xs.take n = ys.take n → n ≤ xs.length →
    n ≤ ys.length → xs[n]? ≠ ys[n]? → commonPrefix xs ys = n
  | 0, [], _, _, _, _, hne => by simp [commonPrefix]
  | 0, _ :: _, [], _, _, _, hne => by simp [commonPrefix]
  | 0, x :: xs, y :: ys, _, _, _, hne => by
    have : x ≠ y := by simpa using hne
    simp [commonPrefix, this]
  | n + 1, [], _, _, h1, _, _ => by simp at h1
  | n + 1, _ :: _, [], _, _, h2, _ => by simp at h2
  | n + 1, x :: xs, y :: ys, ht, h1, h2, hne => by
    simp only [List.take_succ_cons, List.cons.injEq] at ht
    obtain ⟨rfl, ht⟩ := ht
    simp only [List.length_cons] at h1 h2
    simp only [List.getElem?_cons_succ] at hne
    simp [commonPrefix, commonPrefix_of_take n xs ys ht (by omega) (by omega) hne]

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

theorem prefix_of_commonPrefix : ∀ (xs ys : List String), commonPrefix xs ys = xs.length → xs <+: ys
  | [], _, _ => List.nil_prefix
  | _ :: _, [], h => by simp [commonPrefix] at h
  | x :: xs, y :: ys, h => by
    by_cases he : x = y
    · subst he
      simp only [commonPrefix, ↓reduceIte, List.length_cons, Nat.add_right_cancel_iff] at h
      exact (List.prefix_cons_inj x).mpr (prefix_of_commonPrefix xs ys h)
    · simp [commonPrefix, he] at h

theorem commonPrefix_comm : ∀ (xs ys : List String), commonPrefix xs ys = commonPrefix ys xs
  | [], [] | [], _ :: _ | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    by_cases he : x = y
    · subst he; simp [commonPrefix, commonPrefix_comm xs ys]
    · simp [commonPrefix, he, Ne.symm he]

theorem mem_pathOf_self (t : Tree) (x : String) : x ∈ t.pathOf x ∨ t.pathOf x = [] := by
  cases hs : t.state? x with
  | none => simp [Tree.pathOf, hs]
  | some st =>
    have hname : st.name = x := by simpa using List.find?_some hs
    have hlast := t.path_last (t.state?_mem hs)
    left
    rw [Tree.pathOf_of_state? _ hs, hlast, hname]
    simp

theorem commonPrefix_nil (l : List String) : commonPrefix l [] = 0 := by
  cases l <;> rfl

theorem domainDepth_outside_source (t : Tree) (source : Option String) (target : String)
    (hs : ∀ n, source = some n → n ∉ t.pathOf target) :
    t.domainDepth source target true = t.domainDepth source target false := by
  cases hsrc : source with
  | none => simp [Tree.domainDepth, commonPrefix_nil, Tree.withoutParallel]
  | some n =>
    have hb' := hs n hsrc
    by_cases hc : commonPrefix (t.pathOf target) (t.pathOf n) = (t.pathOf n).length
    · rcases mem_pathOf_self t n with hm | hm
      · rw [commonPrefix_comm] at hc
        exact absurd ((prefix_of_commonPrefix _ _ hc).subset hm) hb'
      · simp [Tree.domainDepth, hm, commonPrefix_nil, Tree.withoutParallel]
    · simp [Tree.domainDepth, hc]

theorem addDefaults_descendants (t : Tree) (x : String) (acc : List String) (y : String) (hy : y ∈ t.addDefaults x acc) :
    y ∈ acc ∨ (x ∈ t.pathOf y ∧ (t.pathOf x).length < (t.pathOf y).length) := by
  suffices ∀ k x (acc : List String), t.maxDepth + 1 - (t.pathOf x).length = k → ∀ y, y ∈ t.addDefaults x acc →
      y ∈ acc ∨ (x ∈ t.pathOf y ∧ (t.pathOf x).length < (t.pathOf y).length) from this _ x acc rfl y hy
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro x acc hk y hy
    rw [Tree.addDefaults.eq_def] at hy
    split at hy
    · exact .inl hy
    · rename_i st h
      split at hy
      · exact .inl hy
      · have hname : st.name = x := by simpa using List.find?_some h
        have hx : x ∈ t.pathOf x := by
          rw [t.pathOf_of_state? h, t.path_last (t.state?_mem h), hname]
          simp
        have key : ∀ (l : List {ch // ch ∈ t.defaultChildren x st}) (acc' : List String),
            (∀ z ∈ acc', z ∈ acc ∨ (x ∈ t.pathOf z ∧ (t.pathOf x).length < (t.pathOf z).length)) →
            ∀ z ∈ l.foldl (fun acc child => t.addDefaults child.1 (addName acc child.1)) acc',
              z ∈ acc ∨ (x ∈ t.pathOf z ∧ (t.pathOf x).length < (t.pathOf z).length) := by
          intro l
          induction l with
          | nil => intro acc' h z hz; exact h z hz
          | cons ch l ihl =>
            intro acc' ha
            apply ihl
            intro z hz
            have hch := t.defaultChildren_mem h ch.2
            have hpc : t.pathOf ch.1 = t.pathOf x ++ [ch.1] := by rw [t.pathOf_child h hch, t.pathOf_of_state? h]
            rcases ih _ (hk ▸ t.child_deeper h hch) ch.1 _ rfl z hz with hz | ⟨hz1, hz2⟩
            · rcases mem_addName hz with hz | rfl
              · exact ha z hz
              · right; rw [hpc]; simp [hx]
            · right
              obtain ⟨j, hj, hjz⟩ := List.getElem_of_mem hz1
              have hq := pathOf_getElem? t _ z rfl j ch.1 (by rw [List.getElem?_eq_getElem hj, hjz])
              rw [hpc] at hq hz2
              simp only [List.length_append, List.length_singleton] at hz2
              exact ⟨List.mem_of_mem_take (hq ▸ List.mem_append_left _ hx), by omega⟩
        exact key _ acc (fun z hz => .inl hz) y hy

theorem region_not_in_path (t : Tree) (name p region : String) (i : Nat) (hi : (t.pathOf name)[i]? = some p)
    (hr : region ∈ t.enterable p) (hne : (t.pathOf name)[i + 1]? ≠ some region) : region ∉ t.pathOf name := by
  intro hm
  obtain ⟨l, hl, hlr⟩ := List.getElem_of_mem hm
  have hpr := pathOf_getElem? t _ name rfl l region (by rw [List.getElem?_eq_getElem hl, hlr])
  have hpp := pathOf_getElem? t _ name rfl i p hi
  have hil : i < (t.pathOf name).length := (List.getElem?_eq_some_iff.mp hi).1
  cases hs : t.state? p with
  | none => simp [Tree.enterable, hs] at hr
  | some ps =>
    have hch : region ∈ ps.children := by
      simp only [Tree.enterable, hs, Option.map_some, Option.getD_some, List.mem_filter] at hr
      exact hr.1
    have hc := t.pathOf_child hs hch
    rw [← t.pathOf_of_state? hs, hpp, hpr] at hc
    have hlen := congrArg List.length hc
    simp only [List.length_take, List.length_append, List.length_singleton] at hlen
    have hli : l = i + 1 := by omega
    subst hli
    exact hne (by rw [List.getElem?_eq_getElem hl, hlr])

theorem exitOrder_reverse_document_order (t : Tree) (names : List String) :
    (t.exitOrder names).Sublist (t.states.map (·.name)).reverse :=
  List.filter_sublist

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

theorem exitOrder_descendants_first (t : Tree) (names : List String) (x y : String) (hy : y ∈ t.pathOf x) (hne : y ≠ x)
    (hx : x ∈ names) (hyn : y ∈ names) : [x, y].Sublist (t.exitOrder names) := by
  obtain ⟨A, B, hAB, hyA⟩ := ancestor_before t x y hy hne
  unfold Tree.exitOrder
  rw [hAB]
  have h : ([x] ++ [y]).Sublist ((B.reverse ++ [x]) ++ A.reverse) :=
    (List.singleton_sublist.mpr (by simp)).append (List.singleton_sublist.mpr (List.mem_reverse.mpr hyA))
  have hf := (show [x, y].Sublist (A ++ x :: B).reverse by simpa using h).filter (· ∈ names)
  simpa [hx, hyn] using hf

theorem entryOrder_ancestors_first (t : Tree) (names : List String) (x y : String) (hy : y ∈ t.pathOf x) (hne : y ≠ x)
    (hx : x ∈ names) (hyn : y ∈ names) : [y, x].Sublist (t.entryOrder names) := by
  obtain ⟨A, B, hAB, hyA⟩ := ancestor_before t x y hy hne
  unfold Tree.entryOrder
  rw [hAB]
  have h : ([y] ++ [x]).Sublist (A ++ x :: B) :=
    (List.singleton_sublist.mpr hyA).append (List.singleton_sublist.mpr (by simp))
  have hf := (show [y, x].Sublist (A ++ x :: B) by simpa using h).filter (· ∈ names)
  simpa [hx, hyn] using hf

theorem parallelBetween_regions (t : Tree) (a b p : String) (h : t.parallelBetween a b = some p) :
    t.kindOf p = some .parallel ∧ ∃ k, (t.pathOf a)[k]? = some p ∧ (t.pathOf b)[k]? = some p ∧
      ((t.pathOf a)[k + 1]?).isSome ∧ ((t.pathOf b)[k + 1]?).isSome ∧ (t.pathOf a)[k + 1]? ≠ (t.pathOf b)[k + 1]? := by
  unfold Tree.parallelBetween at h
  simp only at h
  have hle := commonPrefix_le (t.pathOf a) (t.pathOf b)
  have hdiff := commonPrefix_differs (t.pathOf a) (t.pathOf b)
  have heq := commonPrefix_eq (t.pathOf a) (t.pathOf b)
  generalize commonPrefix (t.pathOf a) (t.pathOf b) = n at h hle hdiff heq
  split at h
  · cases h
  · rename_i hb
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hb
    obtain ⟨⟨h0, ha⟩, hbl⟩ := hb
    split at h
    · rename_i q hq
      split at h
      · rename_i hk
        cases h
        refine ⟨by simpa using hk, n - 1, hq, ?_, ?_, ?_, ?_⟩
        · rw [← heq (n - 1) (by omega)]; exact hq
        · have : n - 1 + 1 = n := by omega
          rw [this]; simp only [isSome_getElem?, gt_iff_lt]; omega
        · have : n - 1 + 1 = n := by omega
          rw [this]; simp only [isSome_getElem?, gt_iff_lt]; omega
        · have : n - 1 + 1 = n := by omega
          rw [this]; exact hdiff (by omega) (by omega)
      · cases h
    · cases h

theorem parallelBetween_of_regions (t : Tree) (a b p : String) (k : Nat) (hp : t.kindOf p = some .parallel)
    (ha : (t.pathOf a)[k]? = some p) (hb : (t.pathOf b)[k]? = some p)
    (ha1 : ((t.pathOf a)[k + 1]?).isSome) (hb1 : ((t.pathOf b)[k + 1]?).isSome)
    (hne : (t.pathOf a)[k + 1]? ≠ (t.pathOf b)[k + 1]?) : t.parallelBetween a b = some p := by
  have hka : k + 1 < (t.pathOf a).length := by
    simpa using ha1
  have hkb : k + 1 < (t.pathOf b).length := by
    simpa using hb1
  have hta := pathOf_getElem? t _ a rfl k p ha
  have htb := pathOf_getElem? t _ b rfl k p hb
  have hc : commonPrefix (t.pathOf a) (t.pathOf b) = k + 1 :=
    commonPrefix_of_take _ _ _ (hta.symm.trans htb) (by omega) (by omega) hne
  unfold Tree.parallelBetween
  simp only [hc, Nat.add_sub_cancel, ha, hp]
  have h1 : (k + 1 == (t.pathOf a).length) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have h2 : (k + 1 == (t.pathOf b).length) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  simp [h1, h2]

theorem descendants_document_order (t : Tree) (n : String) : (t.descendants n).Sublist (t.states.map (·.name)) :=
  (List.filter_sublist).map _

theorem done_by_final_child (t : Tree) (entered : List String) (n : String) (st : Shape)
    (hs : t.state? n = some st) (hk : st.kind ≠ .parallel) :
    t.isDone entered n = st.children.any fun ch => t.kindOf ch == some .final && ch ∈ entered := by
  rw [Tree.isDone.eq_def]
  split
  · rename_i h; rw [hs] at h; cases h
  · rename_i st' h
    rw [hs] at h; cases h
    simp [hk]

theorem parallel_done_by_regions (t : Tree) (entered : List String) (n : String) (st : Shape)
    (hs : t.state? n = some st) (hk : st.kind = .parallel) :
    t.isDone entered n = (t.enterable n).all (t.isDone entered) := by
  rw [Tree.isDone.eq_def]
  split
  · rename_i h; rw [hs] at h; cases h
  · rename_i st' h
    rw [hs] at h; cases h
    simp only [hk, beq_self_eq_true, ↓reduceDIte]
    simp

theorem entrySet_document_order (t : Tree) (entered : List String) (depth : Nat) (name : String) :
    (t.entrySet entered depth name).Sublist (t.states.map (·.name)) :=
  List.filter_sublist

theorem leaves_document_order (t : Tree) (entered : List String) : (t.leaves entered).Sublist (t.states.map (·.name)) :=
  List.filter_sublist.map _

theorem exitSet_in_exit_order (t : Tree) (entered : List String) (source : Option String) (target : String)
    (reenter : Bool) : (t.exitSet entered source target reenter).Sublist (t.exitOrder entered) :=
  List.filter_sublist

theorem mem_path_foldl (entered : List String) (n : String) (hn : n ∉ entered) (path : List String) (hp : n ∈ path)
    (acc : List String) : n ∈ path.foldl (fun acc m => if m ∈ entered then acc else addName acc m) acc := by
  induction path generalizing acc with
  | nil => simp at hp
  | cons m path ih =>
    simp only [List.foldl_cons]
    by_cases hm : n = m
    · subst hm
      refine mem_foldl_of_mem _ (fun acc m x hx => ?_) _ ?_
      · split
        · exact hx
        · exact mem_addName_of_mem _ hx
      · simp only [hn, ↓reduceIte]; exact mem_addName_self acc n
    · exact ih (by simpa [hm] using hp) _

theorem exited_ancestor_entered (t : Tree) (entered : List String) (depth : Nat) (name n : String) (stn : Shape)
    (hs : t.state? n = some stn) (hn : n ∈ (t.pathOf name).drop depth) (he : n ∉ entered) :
    n ∈ t.entrySet entered depth name := by
  simp only [Tree.entrySet, Tree.entryOrder, List.mem_filter, decide_eq_true_eq, List.mem_map]
  refine ⟨⟨stn, List.mem_of_find?_eq_some hs, by simpa using List.find?_some hs⟩, ?_⟩
  cases hf : t.state? name with
  | none => simp [Tree.pathOf, hf] at hn
  | some found =>
    simp only [Tree.pathOf, hf, Option.map_some, Option.getD_some] at hn
    simp only [Tree.addEntrySet, hf]
    refine mem_addDefaults_of_mem t name (mem_foldl_of_mem _ (fun acc p x hx => ?_) _
      (mem_path_foldl entered n he _ hn []))
    split
    · exact mem_foldl_of_mem _ (fun acc r y hy => by
        split
        · exact mem_addDefaults_of_mem t _ (mem_addName_of_mem _ hy)
        · exact hy) _ hx
    · exact hx

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

theorem reenter_false_not_exited (t : Tree) (entered : List String) (source target : String) (ps rt : List String)
    (hs : t.pathOf source = ps ++ [source]) (ht : t.pathOf target = ps ++ source :: rt) :
    source ∉ t.exitSet entered (some source) target false := by
  simp [Tree.exitSet, Tree.domainDepth, hs, ht, commonPrefix_within]

theorem reenter_true_exits (t : Tree) (entered : List String) (source target : String) (ps rt : List String)
    (hs : t.pathOf source = ps ++ [source]) (ht : t.pathOf target = ps ++ source :: rt)
    (he : source ∈ entered) : source ∈ t.exitSet entered (some source) target true := by
  refine exits_of_domainDepth_le t entered _ target source true ps rt hs ht he ?_
  have := withoutParallel_le t (ps ++ source :: rt) ps.length
  simpa [Tree.domainDepth, hs, ht, commonPrefix_within] using this

theorem ancestor_target_exits (t : Tree) (entered : List String) (source target : String) (ps rs : List String)
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

theorem entered_not_entered_again (t : Tree) (entered : List String) (depth : Nat) (name n : String)
    (hn : n ∈ entered) (hp : n ∈ t.pathOf name) : n ∉ t.entrySet entered depth name := by
  simp only [Tree.entrySet, Tree.entryOrder, List.mem_filter, decide_eq_true_eq, not_and]
  intro _
  obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem hp
  have hpn := pathOf_getElem? t _ name rfl j n (by rw [List.getElem?_eq_getElem hj, hjn])
  have hsub : ∀ x ∈ t.pathOf n, x ∈ t.pathOf name := fun x hx => List.mem_of_mem_take (hpn ▸ hx)
  have hlen : (t.pathOf n).length ≤ (t.pathOf name).length := by rw [hpn, List.length_take]; omega
  cases hf : t.state? name with
  | none => simp [Tree.addEntrySet, hf]
  | some found =>
    have hpf : t.pathOf name = found.path := t.pathOf_of_state? hf
    simp only [Tree.addEntrySet, hf]
    intro hm
    rcases addDefaults_descendants t name _ n hm with hm | ⟨_, hl⟩
    · revert hm
      have hregions : ∀ (p : String) (i : Nat) (rs : List String) (acc : List String),
          found.path[i]? = some p → (∀ r ∈ rs, r ∈ t.enterable p) → n ∉ acc →
          n ∉ rs.foldl (fun acc region =>
            if some region != found.path[i + 1]? && region ∉ entered && region ∉ acc then
              t.addDefaults region (addName acc region)
            else acc) acc := by
        intro p i rs
        induction rs with
        | nil => intro acc _ _ ha; exact ha
        | cons r rs ih =>
          intro acc hi hr ha
          simp only [List.foldl_cons]
          apply ih _ hi (fun r' h' => hr r' (List.mem_cons_of_mem _ h'))
          split
          · rename_i hcond
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hcond
            obtain ⟨⟨hne, hre⟩, -⟩ := hcond
            intro hm
            rcases addDefaults_descendants t r _ n hm with hm | ⟨hrn, -⟩
            · rcases mem_addName hm with hm | rfl
              · exact ha hm
              · exact hre hn
            · exact region_not_in_path t name p r i (hpf ▸ hi) (hr r List.mem_cons_self)
                (hpf ▸ fun h => hne h.symm) (hsub r hrn)
          · exact ha
      have hfold : ∀ (l : List (String × Nat)) (acc : List String), (∀ x ∈ l, found.path[x.2]? = some x.1) → n ∉ acc →
          n ∉ l.foldl (fun acc (x : String × Nat) =>
            if depth ≤ x.2 && t.kindOf x.1 == some .parallel then
              (t.enterable x.1).foldl (fun acc region =>
                if some region != found.path[x.2 + 1]? && region ∉ entered && region ∉ acc then
                  t.addDefaults region (addName acc region)
                else acc) acc
            else acc) acc := by
        intro l
        induction l with
        | nil => intro acc _ ha; exact ha
        | cons x l ih =>
          intro acc hl ha
          simp only [List.foldl_cons]
          apply ih _ (fun y hy => hl y (List.mem_cons_of_mem _ hy))
          split
          · exact hregions x.1 x.2 _ acc (hl x List.mem_cons_self) (fun _ h => h) ha
          · exact ha
      exact hfold _ _ (fun x hx => List.mem_zipIdx_iff_getElem?.mp hx)
        (not_mem_path_foldl entered n hn _ [] (by simp))
    · omega

theorem restores_last_children (t : Tree) (initial : String) (lastChildren : List (String × List String))
    (target parent : String) (st : Shape) (x : String) (xs : List String) (hs : t.state? target = some st) (hk : st.kind = .history)
    (hp : st.parent = some parent) (hl : lastChildren.lookup parent = some (x :: xs)) :
    t.historyTargets initial lastChildren target = x :: xs := by
  simp [Tree.historyTargets, hs, hk, hp, hl]

theorem never_exited_enters_parent (t : Tree) (initial : String) (lastChildren : List (String × List String))
    (target parent : String) (st : Shape) (hs : t.state? target = some st) (hk : st.kind = .history) (hp : st.parent = some parent)
    (hl : lastChildren.lookup parent = none) (hm : ∀ ps, t.state? parent = some ps → ps.kind ≠ .map) :
    t.historyTargets initial lastChildren target = [parent] := by
  simp only [Tree.historyTargets, hs, hk, hp, hl]
  simp only [beq_self_eq_true, ↓reduceIte]
  split
  · rename_i ps hps
    simp [hm ps hps]
  · rfl

theorem never_exited_map_enters_initial (t : Tree) (initial : String) (lastChildren : List (String × List String))
    (target parent : String) (st ps : Shape) (hs : t.state? target = some st) (hk : st.kind = .history)
    (hp : st.parent = some parent) (hl : lastChildren.lookup parent = none) (hps : t.state? parent = some ps)
    (hm : ps.kind = .map) :
    t.historyTargets initial lastChildren target = ps.initial.toList := by
  simp [Tree.historyTargets, hs, hk, hp, hl, hps, hm]

end Tazuna.Thm.Syntax.Tree
