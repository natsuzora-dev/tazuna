import Tazuna.Trace.Tree

/-! What a window's out lines tell of the binding, without choosing among bindings that read alike. The keys and names
not yet bound one to one lie in blocks: a block's keys are its names in some one-to-one way not yet known. A tree reads
through its blocks as its skeleton (`skK`, `skN`); two trees can be the same under a binding only if their skeletons
are. Where a bag holds several items of one skeleton, each with one key of an undecided block, any pairing of them reads
alike, so the window says only that those keys are those names in some order (`classPairs`); where it holds one, its
item pairs with the trace's one item of that skeleton. `pairs` collects these facts, and `pairs_iff` says they are
exactly what a binding that respects the blocks must meet for the trees to be the same. Items of one skeleton with two
or more undecided keys each tie their keys together, which blocks do not express: `pairs` gives up there (none), and
verify decides a key by trying each of its block's names. -/

namespace Tazuna.Trace

open Tazuna.Ir

theorem sizeOf_filter_le {α : Type} [SizeOf α] (p : α → Bool) : (l : List α) → sizeOf (l.filter p) ≤ sizeOf l
  | [] => by simp
  | x :: xs => by
    have := sizeOf_filter_le p xs
    unfold List.filter; split <;> simp <;> omega

theorem multi_singleton {α β : Type} {r : α → β → Prop} {a : α} {b : β} : Multi r [a] [b] ↔ r a b := by
  constructor
  · rintro ⟨zs, h, hp⟩
    obtain ⟨z, rfl⟩ : ∃ z, zs = [z] := by
      match zs, h with
      | [z], _ => exact ⟨z, rfl⟩
    have := List.perm_singleton.1 hp
    cases this; exact h.1
  · intro h; exact Multi.cons h Multi.nil

theorem multi_of_all {α β : Type} {r : α → β → Prop} :
    (xs : List α) → (ys : List β) → xs.length = ys.length → (∀ a ∈ xs, ∀ b ∈ ys, r a b) → Multi r xs ys
  | [], [], _, _ => Multi.nil
  | x :: xs, y :: ys, hl, h => Multi.cons (h x (by simp) y (by simp))
      (multi_of_all xs ys (by simpa using hl) fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem forall2_imp_mem {α β : Type} {r r' : α → β → Prop} :
    {xs : List α} → {ys : List β} → (∀ a ∈ xs, ∀ b ∈ ys, r a b → r' a b) → Forall2 r xs ys → Forall2 r' xs ys
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, h, ⟨hab, hs⟩ =>
    ⟨h _ (by simp) _ (by simp) hab, forall2_imp_mem (fun a ha b hb => h a (by simp [ha]) b (by simp [hb])) hs⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

theorem Multi.imp_mem {α β : Type} {r r' : α → β → Prop} {xs : List α} {ys : List β}
    (h : ∀ a ∈ xs, ∀ b ∈ ys, r a b → r' a b) : Multi r xs ys → Multi r' xs ys
  | ⟨zs, hz, hp⟩ => ⟨zs, forall2_imp_mem (fun a ha b hb => h a ha b (hp.mem_iff.1 hb)) hz, hp⟩

theorem multi_split {α β : Type} {r : α → β → Prop} {p : α → Bool} {q : β → Bool} {xs : List α} {ys : List β}
    (hpq : ∀ a ∈ xs, ∀ b ∈ ys, r a b → p a = q b) :
    Multi r xs ys ↔ Multi r (xs.filter p) (ys.filter q) ∧ Multi r (xs.filter (!p ·)) (ys.filter (!q ·)) := by
  let r' a b := r a b ∧ a ∈ xs ∧ b ∈ ys
  have hr : ∀ {xs' : List α} {ys' : List β}, (∀ a ∈ xs', a ∈ xs) → (∀ b ∈ ys', b ∈ ys) →
      (Multi r xs' ys' ↔ Multi r' xs' ys') := fun hx hy =>
    ⟨Multi.imp_mem fun a ha b hb h => ⟨h, hx a ha, hy b hb⟩, Multi.imp fun _ _ h => h.1⟩
  have hpq' : ∀ a b, r' a b → p a = q b := fun a b h => hpq a h.2.1 b h.2.2 h.1
  rw [hr (fun _ h => h) (fun _ h => h), hr (fun a ha => (List.mem_filter.1 ha).1) (fun b hb => (List.mem_filter.1 hb).1),
    hr (fun a ha => (List.mem_filter.1 ha).1) (fun b hb => (List.mem_filter.1 hb).1)]
  refine ⟨fun h => ⟨h.filter hpq', h.filter fun a b h => by rw [hpq' a b h]⟩, fun ⟨h1, h2⟩ => ?_⟩
  exact ((h1.append h2).perm_left (List.filter_append_perm p xs)).perm_right (List.filter_append_perm q ys)

theorem forall2_map_left_iff {α β γ : Type} {r : γ → β → Prop} {f : α → γ} :
    {xs : List α} → {ys : List β} → (Forall2 r (xs.map f) ys ↔ Forall2 (fun a b => r (f a) b) xs ys)
  | [], [] => Iff.rfl
  | _ :: _, _ :: _ => by simp only [List.map_cons, Forall2]; rw [forall2_map_left_iff]
  | [], _ :: _ | _ :: _, [] => Iff.rfl

theorem forall2_of_map_right_iff {α β γ δ : Type} {r : γ → δ → Prop} {f : α → γ} {g : β → δ} :
    {xs : List α} → {ys : List β} → (Forall2 r (xs.map f) (ys.map g) ↔ Forall2 (fun a b => r (f a) (g b)) xs ys)
  | [], [] => Iff.rfl
  | _ :: _, _ :: _ => by simp only [List.map_cons, Forall2]; rw [forall2_of_map_right_iff]
  | [], _ :: _ | _ :: _, [] => Iff.rfl

theorem multi_map_right_iff {α β γ δ : Type} {r : γ → δ → Prop} {f : α → γ} {g : β → δ} {xs : List α} {ys : List β} :
    Multi r (xs.map f) (ys.map g) ↔ Multi (fun a b => r (f a) (g b)) xs ys :=
  ⟨Multi.of_map fun _ _ h => h, fun h => Multi.map (r' := r) (f := f) (g := g) (fun _ _ h => h) h⟩

theorem multi_map_left_iff {α β γ : Type} {r : γ → β → Prop} {f : α → γ} {xs : List α} {ys : List β} :
    Multi r (xs.map f) ys ↔ Multi (fun a b => r (f a) b) xs ys := by
  constructor
  · exact Multi.of_map (g := id) (fun _ _ h => h) ∘ fun h => by simpa using h
  · intro h; simpa using h.map (r' := r) (f := f) (g := id) fun _ _ h => h

section
variable {σ : Type} [Leaf σ] (bk : Key → σ) (bn : Name → σ) (und : σ → Bool)

/-- A spec tree's skeleton: its keys read as their blocks. -/
def skK (x : Tree Key) : Erl := (x.map bk).erl Leaf.toErl

def skN (y : Tree Name) : Erl := (y.map bn).erl Leaf.toErl

/-- The keys of undecided blocks a tree holds. -/
def undK (x : Tree Key) : List Key := x.leaves.filter (und ∘ bk)

def undN (y : Tree Name) : List Name := y.leaves.filter (und ∘ bn)

/-- What a window says of the blocks: each pair's keys are its names in some order. -/
abbrev Cons := List (List Key × List Name)

/-- The items of one skeleton in a bag, two or more on each side: nothing, if they hold no undecided key, or that
their undecided keys are their names, if each holds one; none where they tie two or more. -/
def classPairs (xin : List (Tree Key)) (yin : List (Tree Name)) : Option Cons :=
  let ks := xin.flatMap (undK bk und)
  let ns := yin.flatMap (undN bn und)
  if xin.all fun x => (undK bk und x).isEmpty then some []
  else if xin.all (fun x => (undK bk und x).length == 1) && yin.all (fun y => (undN bn und y).length == 1) &&
      decide ks.Nodup && decide ns.Nodup && ks.length == ns.length then some [(ks, ns)]
  else none

mutual
/-- What two trees with the same skeleton say of the blocks, or none where items tie undecided keys together. -/
def pairs : Tree Key → Tree Name → Option Cons
  | .leaf k, .leaf s => some (if und (bk k) then [([k], [s])] else [])
  | .atom _, .atom _ => some []
  | .seq xs, .seq ys => pairsSeq xs ys
  | .bag xs, .bag ys => pairsBag xs ys
  | _, _ => none
termination_by x => sizeOf x
def pairsSeq : List (Tree Key) → List (Tree Name) → Option Cons
  | [], [] => some []
  | x :: xs, y :: ys => do pure ((← pairs x y) ++ (← pairsSeq xs ys))
  | _, _ => none
termination_by xs => sizeOf xs
/-- A bag's items class by class: the class of the first item's skeleton, then the rest. -/
def pairsBag : List (Tree Key) → List (Tree Name) → Option Cons
  | [], _ => some []
  | x :: xs, ys => do
    let c := skK bk x
    let rest ← pairsBag (xs.filter (skK bk · != c)) (ys.filter (skN bn · != c))
    let here ← pairsClass x (xs.filter (skK bk · == c)) (ys.filter (skN bn · == c))
    pure (here ++ rest)
termination_by xs => sizeOf xs
decreasing_by
  · have := sizeOf_filter_le (skK bk · != skK bk x) xs; simp; omega
  · simp; have : 1 ≤ sizeOf xs := by cases xs with | nil => simp | cons => simp; omega
    omega
/-- The class of `x` in a bag, with the other items of its skeleton `xin` and the trace's items `yin`: a lone item
pairs with the trace's lone item. -/
def pairsClass (x : Tree Key) : List (Tree Key) → List (Tree Name) → Option Cons
  | [], [y] => pairs x y
  | xin, yin => classPairs bk bn und (x :: xin) yin
termination_by sizeOf x + 1
end

variable (β : Key → Name) (okK : Key → Prop) (okN : Name → Prop)

/-- A binding that respects the blocks: it keeps each key in its block, and binds a decided block's key to its name. -/
structure Resp : Prop where
  blk : ∀ k, okK k → bn (β k) = bk k
  dec : ∀ k s, okK k → okN s → bk k = bn s → und (bk k) = false → β k = s

variable {bk bn und β okK okN}

theorem skel_of_same (hR : Resp bk bn und β okK okN) {x : Tree Key} {y : Tree Name} (hx : ∀ k ∈ x.leaves, okK k)
    (h : Tree.Same (x.map β) y) : Tree.Same (x.map bk) (y.map bn) := by
  have := Tree.Same.map bn h
  rwa [Tree.map_map, Tree.map_congr x (f := bn ∘ β) (g := bk) fun k hk => hR.blk k (hx k hk)] at this

omit [Leaf σ] in
theorem undN_map (hR : Resp bk bn und β okK okN) {x : Tree Key} (hx : ∀ k ∈ x.leaves, okK k) :
    undN bn und (x.map β) = (undK bk und x).map β := by
  simp only [undN, undK, Tree.leaves_map, List.filter_map]
  congr 1
  exact List.filter_congr fun k hk => by simp [hR.blk k (hx k hk)]

omit [Leaf σ] in
theorem undN_perm (hR : Resp bk bn und β okK okN) {x : Tree Key} {y : Tree Name} (hx : ∀ k ∈ x.leaves, okK k)
    (h : Tree.Same (x.map β) y) : ((undK bk und x).map β).Perm (undN bn und y) := by
  rw [← undN_map hR hx]; exact h.leaves.filter _

-- Inside the proof each list has one item, so its head is that item.
set_option linter.tazuna.silentDefault false in
theorem classPairs_iff (hR : Resp bk bn und β okK okN) {xin : List (Tree Key)} {yin : List (Tree Name)} {cs : Cons}
    (hxl : ∀ x ∈ xin, ∀ k ∈ x.leaves, okK k) (hyl : ∀ y ∈ yin, ∀ s ∈ y.leaves, okN s)
    (hsk : ∀ x ∈ xin, ∀ y ∈ yin, Tree.Same (x.map bk) (y.map bn)) (hlen : xin.length = yin.length)
    (h : classPairs bk bn und xin yin = some cs) :
    Multi (fun x y => Tree.Same (x.map β) y) xin yin ↔ ∀ c ∈ cs, (c.1.map β).Perm c.2 := by
  unfold classPairs at h
  simp only at h
  split at h
  · rename_i hnone
    cases h
    simp only [List.not_mem_nil, false_implies, implies_true, iff_true]
    refine multi_of_all xin yin hlen fun x hx y hy => Tree.same_of_skel bk bn β x y (hsk x hx y hy) ?_
    intro a ha b hb hab
    have hu : und (bk a) = false := by
      have := List.all_eq_true.1 hnone x hx
      simp only [List.isEmpty_iff, undK, List.filter_eq_nil_iff, Function.comp] at this
      simpa using this a ha
    exact hR.dec a b (hxl x hx a ha) (hyl y hy b hb) hab hu
  · split at h
    · rename_i _ hall
      cases h
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
      obtain ⟨⟨⟨⟨hx1, hy1⟩, -⟩, -⟩, -⟩ := hall
      have one : ∀ {α : Type} [Inhabited α] {l : List α}, l.length = 1 → l = [l.headD default] :=
        fun {_} _ {l} hl => by
          match l, hl with
          | [a], _ => rfl
      have fl : ∀ {α γ : Type} [Inhabited γ] {f : α → List γ} (l : List α), (∀ x ∈ l, (f x).length = 1) →
          l.flatMap f = l.map fun x => (f x).headD default := fun {_ _} _ {f} l hl => by
        induction l with
        | nil => rfl
        | cons x l ih =>
          rw [List.flatMap_cons, List.map_cons, one (hl x (by simp)), ih fun y hy => hl y (by simp [hy])]
          simp
      have hxs := fl (f := undK bk und) xin hx1
      have hys := fl (f := undN bn und) yin hy1
      simp only [List.mem_singleton, forall_eq]
      rw [hxs, hys, List.map_map]
      constructor
      · intro hm
        refine perm_map_of_multi (Multi.imp_mem (fun x hx y hy hxy => ?_) hm)
        have hp := undN_perm hR (hxl x hx) hxy
        rw [one (hx1 x hx), one (hy1 y hy), List.map_singleton] at hp
        simpa using List.perm_singleton.1 hp
      · intro hp
        refine Multi.imp_mem (fun x hx y hy hxy => ?_) (multi_of_perm_map xin yin hp)
        refine Tree.same_of_skel bk bn β x y (hsk x hx y hy) fun a ha b hb hab => ?_
        cases hu : und (bk a)
        · exact hR.dec a b (hxl x hx a ha) (hyl y hy b hb) hab hu
        · have ha' : a ∈ undK bk und x := List.mem_filter.2 ⟨ha, by simpa using hu⟩
          have hb' : b ∈ undN bn und y := List.mem_filter.2 ⟨hb, by simpa [← hab] using hu⟩
          rw [one (hx1 x hx), List.mem_singleton] at ha'
          rw [one (hy1 y hy), List.mem_singleton] at hb'
          subst ha' hb'
          simpa using hxy
    · cases h


mutual
/-- `pairs` says exactly what a binding that respects the blocks must meet for two trees of one skeleton to be the same
under it. -/
theorem pairs_iff (hR : Resp bk bn und β okK okN) : (x : Tree Key) → (y : Tree Name) → (cs : Cons) →
    (∀ k ∈ x.leaves, okK k) → (∀ s ∈ y.leaves, okN s) → Tree.Same (x.map bk) (y.map bn) →
    pairs bk bn und x y = some cs → (Tree.Same (x.map β) y ↔ ∀ c ∈ cs, (c.1.map β).Perm c.2)
  | .leaf k, .leaf s, cs, hx, hy, hsk, h => by
    simp only [pairs, Option.some.injEq] at h
    subst h
    simp only [Tree.map, Tree.same_leaf] at hsk ⊢
    split
    · simp
    · rename_i hu
      simp only [List.not_mem_nil, false_implies, implies_true, iff_true]
      exact hR.dec k s (hx k (by simp [Tree.leaves])) (hy s (by simp [Tree.leaves])) hsk (by simpa using hu)
  | .atom _, .atom _, cs, _, _, hsk, h => by
    simp only [pairs, Option.some.injEq] at h
    subst h
    simp only [Tree.map, Tree.same_atom] at hsk ⊢
    simp [hsk]
  | .seq xs, .seq ys, cs, hx, hy, hsk, h => by
    simp only [Tree.map, Tree.maps_eq, Tree.same_seq] at hsk ⊢
    rw [forall2_of_map_right_iff] at hsk
    rw [forall2_map_left_iff]
    exact pairsSeq_iff hR xs ys cs (by simpa [Tree.leaves] using hx) (by simpa [Tree.leaves] using hy) hsk
      (by simpa [pairs] using h)
  | .bag xs, .bag ys, cs, hx, hy, hsk, h => by
    simp only [Tree.map, Tree.maps_eq, Tree.same_bag] at hsk ⊢
    rw [multi_map_right_iff] at hsk
    rw [multi_map_left_iff]
    exact pairsBag_iff hR xs ys cs (by simpa [Tree.leaves] using hx) (by simpa [Tree.leaves] using hy) hsk
      (by simpa [pairs] using h)
  | .leaf _, .atom _, _, _, _, _, h => by simp [pairs] at h
  | .leaf _, .seq _, _, _, _, _, h => by simp [pairs] at h
  | .leaf _, .bag _, _, _, _, _, h => by simp [pairs] at h
  | .atom _, .leaf _, _, _, _, _, h => by simp [pairs] at h
  | .atom _, .seq _, _, _, _, _, h => by simp [pairs] at h
  | .atom _, .bag _, _, _, _, _, h => by simp [pairs] at h
  | .seq _, .leaf _, _, _, _, _, h => by simp [pairs] at h
  | .seq _, .atom _, _, _, _, _, h => by simp [pairs] at h
  | .seq _, .bag _, _, _, _, _, h => by simp [pairs] at h
  | .bag _, .leaf _, _, _, _, _, h => by simp [pairs] at h
  | .bag _, .atom _, _, _, _, _, h => by simp [pairs] at h
  | .bag _, .seq _, _, _, _, _, h => by simp [pairs] at h
termination_by x => sizeOf x
theorem pairsSeq_iff (hR : Resp bk bn und β okK okN) : (xs : List (Tree Key)) → (ys : List (Tree Name)) → (cs : Cons) →
    (∀ k ∈ Tree.leavess xs, okK k) → (∀ s ∈ Tree.leavess ys, okN s) →
    Forall2 (fun x y => Tree.Same (x.map bk) (y.map bn)) xs ys → pairsSeq bk bn und xs ys = some cs →
    (Forall2 (fun x y => Tree.Same (x.map β) y) xs ys ↔ ∀ c ∈ cs, (c.1.map β).Perm c.2)
  | [], [], cs, _, _, _, h => by simp only [pairsSeq, Option.some.injEq] at h; subst h; simp [Forall2]
  | x :: xs, y :: ys, cs, hx, hy, ⟨hsk, hsks⟩, h => by
    simp only [pairsSeq, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨c1, h1, c2, h2, rfl⟩ := h
    simp only [Forall2, List.mem_append, or_imp, forall_and]
    rw [pairs_iff hR x y c1 (fun k hk => hx k (by simp [Tree.leavess, hk])) (fun s hs => hy s (by simp [Tree.leavess, hs]))
      hsk h1, pairsSeq_iff hR xs ys c2 (fun k hk => hx k (by simp [Tree.leavess, hk]))
      (fun s hs => hy s (by simp [Tree.leavess, hs])) hsks h2]
  | [], _ :: _, _, _, _, h, _ | _ :: _, [], _, _, _, h, _ => h.elim
termination_by xs => sizeOf xs
theorem pairsBag_iff (hR : Resp bk bn und β okK okN) : (xs : List (Tree Key)) → (ys : List (Tree Name)) → (cs : Cons) →
    (∀ k ∈ Tree.leavess xs, okK k) → (∀ s ∈ Tree.leavess ys, okN s) →
    Multi (fun x y => Tree.Same (x.map bk) (y.map bn)) xs ys → pairsBag bk bn und xs ys = some cs →
    (Multi (fun x y => Tree.Same (x.map β) y) xs ys ↔ ∀ c ∈ cs, (c.1.map β).Perm c.2)
  | [], ys, cs, _, _, hsk, h => by
    simp only [pairsBag, Option.some.injEq] at h; subst h
    have := hsk.length_eq; cases ys with
    | nil => simp [Multi.nil]
    | cons => simp at this
  | x :: xs, ys, cs, hx, hy, hsk, h => by
    simp only [pairsBag, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨rest, hrest, here, hhere, rfl⟩ := h
    have hxl : ∀ a ∈ x :: xs, ∀ k ∈ a.leaves, okK k := fun a ha k hk => hx k (Tree.mem_leavess ha hk)
    have hyl : ∀ b ∈ ys, ∀ s ∈ b.leaves, okN s := fun b hb s hs => hy s (Tree.mem_leavess hb hs)
    have hpq : ∀ a ∈ x :: xs, ∀ b ∈ ys, Tree.Same (a.map bk) (b.map bn) →
        (skK bk a == skK bk x) = (skN bn b == skK bk x) := by
      intro a _ b _ h; simp only [skK, skN]; rw [show (a.map bk).erl Leaf.toErl = _ from h]
    have hpq' : ∀ a ∈ x :: xs, ∀ b ∈ ys, Tree.Same (a.map β) b →
        (skK bk a == skK bk x) = (skN bn b == skK bk x) :=
      fun a ha b hb h => hpq a ha b hb (skel_of_same hR (hxl a ha) h)
    obtain ⟨hsk1, hsk2⟩ := (multi_split hpq).1 hsk
    rw [multi_split hpq']
    have e1 : (x :: xs).filter (fun a => skK bk a == skK bk x) = x :: xs.filter (fun a => skK bk a == skK bk x) :=
      List.filter_cons_of_pos (by simp)
    have e2 : (x :: xs).filter (fun a => !(skK bk a == skK bk x)) = xs.filter (fun a => !(skK bk a == skK bk x)) :=
      List.filter_cons_of_neg (by simp)
    simp only [e1, e2] at hsk1 hsk2 ⊢
    have hrest' := pairsBag_iff hR _ _ rest (fun k hk => hx k (by
        rw [Tree.leavess_eq] at hk ⊢; obtain ⟨a, ha, hk⟩ := List.mem_flatMap.1 hk
        exact List.mem_flatMap.2 ⟨a, List.mem_cons_of_mem _ (List.mem_filter.1 ha).1, hk⟩))
      (fun s hs => hy s (by
        rw [Tree.leavess_eq] at hs ⊢; obtain ⟨b, hb, hs⟩ := List.mem_flatMap.1 hs
        exact List.mem_flatMap.2 ⟨b, (List.mem_filter.1 hb).1, hs⟩)) hsk2 (by simpa [bne] using hrest)
    rw [hrest', List.forall_mem_append, and_congr_left_iff]
    intro _
    exact pairsClass_iff hR x _ _ here (hxl x (by simp)) (fun a ha => hxl a (List.mem_cons_of_mem _ (List.mem_filter.1 ha).1))
      (fun b hb => hyl b (List.mem_filter.1 hb).1) (fun a ha => by simpa using (List.mem_filter.1 ha).2)
      (fun b hb => by simpa using (List.mem_filter.1 hb).2) hsk1 hhere
termination_by xs => sizeOf xs
decreasing_by
  · have := sizeOf_filter_le (fun a => !(skK bk a == skK bk x)) xs; simp; omega
  · simp; have : 1 ≤ sizeOf xs := by cases xs with | nil => simp | cons => simp; omega
    omega
theorem pairsClass_iff (hR : Resp bk bn und β okK okN) (x : Tree Key) : (xin : List (Tree Key)) →
    (yin : List (Tree Name)) → (cs : Cons) → (∀ k ∈ x.leaves, okK k) → (∀ a ∈ xin, ∀ k ∈ a.leaves, okK k) →
    (∀ b ∈ yin, ∀ s ∈ b.leaves, okN s) → (∀ a ∈ xin, skK bk a = skK bk x) → (∀ b ∈ yin, skN bn b = skK bk x) →
    Multi (fun x y => Tree.Same (x.map bk) (y.map bn)) (x :: xin) yin → pairsClass bk bn und x xin yin = some cs →
    (Multi (fun x y => Tree.Same (x.map β) y) (x :: xin) yin ↔ ∀ c ∈ cs, (c.1.map β).Perm c.2)
  | xin, yin, cs, hx, hxl, hyl, hxc, hyc, hsk, h => by
    unfold pairsClass at h
    split at h
    · rw [multi_singleton] at hsk ⊢
      exact pairs_iff hR x _ cs hx (hyl _ (by simp)) hsk h
    rename_i h'
    clear h'
    refine classPairs_iff hR (fun a ha k hk => ?_) hyl (fun a ha b hb => ?_) hsk.length_eq h
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hx k hk
      · exact hxl a ha k hk
    · show (a.map bk).erl Leaf.toErl = (b.map bn).erl Leaf.toErl
      have hb' := hyc b hb
      simp only [skK, skN] at hb' hxc
      rw [hb']
      rcases List.mem_cons.1 ha with rfl | ha
      · rfl
      · exact hxc a ha
termination_by sizeOf x + 1
end


mutual
/-- Each fact `pairs` gives pairs keys of the first tree with as many names of the second, none twice. -/
theorem pairs_ok : (x : Tree Key) → (y : Tree Name) → (cs : Cons) → pairs bk bn und x y = some cs →
    ∀ c ∈ cs, c.1 ⊆ x.leaves ∧ c.2 ⊆ y.leaves ∧ c.1.Nodup ∧ c.2.Nodup ∧ c.1.length = c.2.length
  | .leaf k, .leaf s, cs, h => by
    simp only [pairs, Option.some.injEq] at h; subst h
    split <;> simp [Tree.leaves]
  | .atom _, .atom _, cs, h => by simp only [pairs, Option.some.injEq] at h; subst h; simp
  | .seq xs, .seq ys, cs, h => by
    simp only [Tree.leaves]; exact pairsSeq_ok xs ys cs (by simpa [pairs] using h)
  | .bag xs, .bag ys, cs, h => by
    simp only [Tree.leaves]; exact pairsBag_ok xs ys cs (by simpa [pairs] using h)
  | .leaf _, .atom _, _, h => by simp [pairs] at h
  | .leaf _, .seq _, _, h => by simp [pairs] at h
  | .leaf _, .bag _, _, h => by simp [pairs] at h
  | .atom _, .leaf _, _, h => by simp [pairs] at h
  | .atom _, .seq _, _, h => by simp [pairs] at h
  | .atom _, .bag _, _, h => by simp [pairs] at h
  | .seq _, .leaf _, _, h => by simp [pairs] at h
  | .seq _, .atom _, _, h => by simp [pairs] at h
  | .seq _, .bag _, _, h => by simp [pairs] at h
  | .bag _, .leaf _, _, h => by simp [pairs] at h
  | .bag _, .atom _, _, h => by simp [pairs] at h
  | .bag _, .seq _, _, h => by simp [pairs] at h
termination_by x => sizeOf x
theorem pairsSeq_ok : (xs : List (Tree Key)) → (ys : List (Tree Name)) → (cs : Cons) →
    pairsSeq bk bn und xs ys = some cs →
    ∀ c ∈ cs, c.1 ⊆ Tree.leavess xs ∧ c.2 ⊆ Tree.leavess ys ∧ c.1.Nodup ∧ c.2.Nodup ∧ c.1.length = c.2.length
  | [], [], cs, h => by simp only [pairsSeq, Option.some.injEq] at h; subst h; simp
  | x :: xs, y :: ys, cs, h => by
    simp only [pairsSeq, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨c1, h1, c2, h2, rfl⟩ := h
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨a, b, d, e, f⟩ := pairs_ok x y c1 h1 c hc
      exact ⟨fun k hk => by simp [Tree.leavess, a hk], fun k hk => by simp [Tree.leavess, b hk], d, e, f⟩
    · obtain ⟨a, b, d, e, f⟩ := pairsSeq_ok xs ys c2 h2 c hc
      exact ⟨fun k hk => by simp [Tree.leavess, a hk], fun k hk => by simp [Tree.leavess, b hk], d, e, f⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [pairsSeq] at h
termination_by xs => sizeOf xs
theorem pairsBag_ok : (xs : List (Tree Key)) → (ys : List (Tree Name)) → (cs : Cons) →
    pairsBag bk bn und xs ys = some cs →
    ∀ c ∈ cs, c.1 ⊆ Tree.leavess xs ∧ c.2 ⊆ Tree.leavess ys ∧ c.1.Nodup ∧ c.2.Nodup ∧ c.1.length = c.2.length
  | [], ys, cs, h => by simp only [pairsBag, Option.some.injEq] at h; subst h; simp
  | x :: xs, ys, cs, h => by
    simp only [pairsBag, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨rest, hrest, here, hhere, rfl⟩ := h
    have sx : ∀ {p : Tree Key → Bool} {k : Key}, k ∈ Tree.leavess (xs.filter p) → k ∈ Tree.leavess (x :: xs) :=
      fun {p} {k} hk => by
        rw [Tree.leavess_eq] at hk ⊢; obtain ⟨a, ha, hk⟩ := List.mem_flatMap.1 hk
        exact List.mem_flatMap.2 ⟨a, List.mem_cons_of_mem _ (List.mem_filter.1 ha).1, hk⟩
    have sy : ∀ {p : Tree Name → Bool} {s : Name}, s ∈ Tree.leavess (ys.filter p) → s ∈ Tree.leavess ys :=
      fun {p} {s} hs => by
        rw [Tree.leavess_eq] at hs ⊢; obtain ⟨a, ha, hs⟩ := List.mem_flatMap.1 hs
        exact List.mem_flatMap.2 ⟨a, (List.mem_filter.1 ha).1, hs⟩
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨a, b, d, e, f⟩ := pairsClass_ok x _ _ here hhere c hc
      refine ⟨fun k hk => ?_, fun s hs => sy (b hs), d, e, f⟩
      have := a hk
      simp only [Tree.leavess, List.mem_append] at this
      rcases this with h | h
      · simp [Tree.leavess, h]
      · exact sx h
    · obtain ⟨a, b, d, e, f⟩ := pairsBag_ok _ _ rest hrest c hc
      exact ⟨fun k hk => sx (a hk), fun s hs => sy (b hs), d, e, f⟩
termination_by xs => sizeOf xs
decreasing_by
  · simp; have : 1 ≤ sizeOf xs := by cases xs with | nil => simp | cons => simp; omega
    omega
  · have := sizeOf_filter_le (fun a => skK bk a != skK bk x) xs; simp; omega
theorem pairsClass_ok (x : Tree Key) : (xin : List (Tree Key)) → (yin : List (Tree Name)) → (cs : Cons) →
    pairsClass bk bn und x xin yin = some cs →
    ∀ c ∈ cs, c.1 ⊆ Tree.leavess (x :: xin) ∧ c.2 ⊆ Tree.leavess yin ∧ c.1.Nodup ∧ c.2.Nodup ∧
      c.1.length = c.2.length
  | xin, yin, cs, h => by
    unfold pairsClass at h
    split at h
    · intro c hc
      obtain ⟨a, b, d, e, f⟩ := pairs_ok x _ cs h c hc
      exact ⟨fun k hk => by simp [Tree.leavess, a hk], fun s hs => by simp [Tree.leavess, b hs], d, e, f⟩
    · unfold classPairs at h
      simp only at h
      split at h
      · cases h; simp
      · split at h
        · rename_i hall
          cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hall
          simp only [List.mem_singleton, forall_eq]
          refine ⟨fun k hk => ?_, fun s hs => ?_, hall.1.1.2, hall.1.2, hall.2⟩
          · obtain ⟨a, ha, hk⟩ := List.mem_flatMap.1 hk
            rw [Tree.leavess_eq]; exact List.mem_flatMap.2 ⟨a, ha, (List.mem_filter.1 hk).1⟩
          · obtain ⟨a, ha, hs⟩ := List.mem_flatMap.1 hs
            rw [Tree.leavess_eq]; exact List.mem_flatMap.2 ⟨a, ha, (List.mem_filter.1 hs).1⟩
        · cases h
termination_by sizeOf x + 1
end


mutual
/-- Trees of one skeleton whose keys are all decided give their facts: `pairs` gives up only where undecided keys
tie. -/
theorem pairs_some : (x : Tree Key) → (y : Tree Name) → Tree.Same (x.map bk) (y.map bn) →
    (∀ k ∈ x.leaves, und (bk k) = false) → ∃ cs, pairs bk bn und x y = some cs
  | .leaf k, .leaf s, _, _ => ⟨_, by simp [pairs]; rfl⟩
  | .atom _, .atom _, _, _ => ⟨[], by simp [pairs]⟩
  | .seq xs, .seq ys, h, hd => by
    simp only [Tree.map, Tree.maps_eq, Tree.same_seq] at h
    rw [forall2_of_map_right_iff] at h
    simpa [pairs] using pairsSeq_some xs ys h (by simpa [Tree.leaves] using hd)
  | .bag xs, .bag ys, h, hd => by
    simp only [Tree.map, Tree.maps_eq, Tree.same_bag] at h
    rw [multi_map_right_iff] at h
    simpa [pairs] using pairsBag_some xs ys h (by simpa [Tree.leaves] using hd)
  | .leaf _, .atom _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .leaf _, .seq _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .leaf _, .bag _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .atom _, .leaf _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .atom _, .seq _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .atom _, .bag _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .seq _, .leaf _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .seq _, .atom _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .seq _, .bag _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .bag _, .leaf _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .bag _, .atom _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
  | .bag _, .seq _, h, _ => absurd ((Tree.tag_map _ _).symm.trans (h.tag.trans (Tree.tag_map _ _))) (by simp [Tree.tag])
termination_by x => sizeOf x
theorem pairsSeq_some : (xs : List (Tree Key)) → (ys : List (Tree Name)) →
    Forall2 (fun x y => Tree.Same (x.map bk) (y.map bn)) xs ys → (∀ k ∈ Tree.leavess xs, und (bk k) = false) →
    ∃ cs, pairsSeq bk bn und xs ys = some cs
  | [], [], _, _ => ⟨[], by simp [pairsSeq]⟩
  | x :: xs, y :: ys, ⟨h, hs⟩, hd => by
    obtain ⟨c1, h1⟩ := pairs_some x y h fun k hk => hd k (by simp [Tree.leavess, hk])
    obtain ⟨c2, h2⟩ := pairsSeq_some xs ys hs fun k hk => hd k (by simp [Tree.leavess, hk])
    exact ⟨c1 ++ c2, by simp [pairsSeq, h1, h2]⟩
  | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim
termination_by xs => sizeOf xs
theorem pairsBag_some : (xs : List (Tree Key)) → (ys : List (Tree Name)) →
    Multi (fun x y => Tree.Same (x.map bk) (y.map bn)) xs ys → (∀ k ∈ Tree.leavess xs, und (bk k) = false) →
    ∃ cs, pairsBag bk bn und xs ys = some cs
  | [], _, _, _ => ⟨[], by simp [pairsBag]⟩
  | x :: xs, ys, hsk, hd => by
    have hpq : ∀ a ∈ x :: xs, ∀ b ∈ ys, Tree.Same (a.map bk) (b.map bn) →
        (skK bk a == skK bk x) = (skN bn b == skK bk x) := by
      intro a _ b _ h; simp only [skK, skN]; rw [show (a.map bk).erl Leaf.toErl = _ from h]
    obtain ⟨hsk1, hsk2⟩ := (multi_split hpq).1 hsk
    have e1 : (x :: xs).filter (fun a => skK bk a == skK bk x) = x :: xs.filter (fun a => skK bk a == skK bk x) :=
      List.filter_cons_of_pos (by simp)
    have e2 : (x :: xs).filter (fun a => !(skK bk a == skK bk x)) = xs.filter (fun a => !(skK bk a == skK bk x)) :=
      List.filter_cons_of_neg (by simp)
    simp only [e1, e2] at hsk1 hsk2
    have sx : ∀ {p : Tree Key → Bool} {k : Key}, k ∈ Tree.leavess (xs.filter p) → k ∈ Tree.leavess (x :: xs) :=
      fun {p} {k} hk => by
        rw [Tree.leavess_eq] at hk ⊢; obtain ⟨a, ha, hk⟩ := List.mem_flatMap.1 hk
        exact List.mem_flatMap.2 ⟨a, List.mem_cons_of_mem _ (List.mem_filter.1 ha).1, hk⟩
    obtain ⟨rest, hrest⟩ := pairsBag_some _ _ hsk2 fun k hk => hd k (sx hk)
    obtain ⟨here, hhere⟩ := pairsClass_some x _ _ hsk1 (fun k hk => hd k (by simp [Tree.leavess, hk]))
      fun a ha k hk => hd k (sx (p := fun a => skK bk a == skK bk x) (Tree.mem_leavess ha hk))
    refine ⟨here ++ rest, ?_⟩
    simp only [pairsBag, Option.bind_eq_bind, Option.pure_def]
    have hrest' : pairsBag bk bn und (xs.filter (skK bk · != skK bk x)) (ys.filter (skN bn · != skK bk x)) =
        some rest := hrest
    rw [hrest']
    simp [hhere]
termination_by xs => sizeOf xs
decreasing_by
  · have := sizeOf_filter_le (fun a => !(skK bk a == skK bk x)) xs; simp; omega
  · simp; have : 1 ≤ sizeOf xs := by cases xs with | nil => simp | cons => simp; omega
    omega
theorem pairsClass_some (x : Tree Key) : (xin : List (Tree Key)) → (yin : List (Tree Name)) →
    Multi (fun x y => Tree.Same (x.map bk) (y.map bn)) (x :: xin) yin → (∀ k ∈ x.leaves, und (bk k) = false) →
    (∀ a ∈ xin, ∀ k ∈ a.leaves, und (bk k) = false) → ∃ cs, pairsClass bk bn und x xin yin = some cs
  | xin, yin, hsk, hx, hxl => by
    unfold pairsClass
    split
    · rw [multi_singleton] at hsk
      exact pairs_some x _ hsk hx
    · refine ⟨[], ?_⟩
      have hc : (x :: xin).all (fun x => (undK bk und x).isEmpty) = true := by
        simp only [List.all_eq_true, List.isEmpty_iff, undK, List.filter_eq_nil_iff, Function.comp]
        intro a ha k hk
        rcases List.mem_cons.1 ha with rfl | ha
        · simpa using hx k hk
        · simpa using hxl a ha k hk
      unfold classPairs
      simp only [hc, ↓reduceIte]
termination_by sizeOf x + 1
end

end

end Tazuna.Trace
