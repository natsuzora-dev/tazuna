import Tazuna.Semantics.Rename

/-! Values and lines as verify compares them. A tree's leaves are ids, its atoms data; a `seq` is ordered and a `bag`
is a multiset, so two trees are the same (`Tree.Same`) when they are equal once every bag's items are reordered. The
spec's side has the spec's ids (`Key`) at its leaves and the trace's side the names the trace wrote (`Name`); a
binding maps the one to the other (`Tree.map`). -/

namespace Tazuna.Trace

open Tazuna.Ir

/-- What the spec names in its out lines: an id, or the wire id of a request it sent. -/
inductive Key where
  | id (x : IdV)
  | wire (n : Nat)
deriving DecidableEq, Repr, Inhabited

/-- What a trace calls an id or a request's wire id. -/
inductive Name where
  | id (s : String)
  | wire (s : String)
deriving DecidableEq, Repr, Inhabited

/-- A key and a name of the same space: ids are named by id names, wire ids by wire names. -/
def Key.isWire : Key → Bool
  | .id _ => false
  | .wire _ => true

def Name.isWire : Name → Bool
  | .id _ => false
  | .wire _ => true

inductive Tree (α : Type) where
  | leaf (a : α)
  | atom (e : Erl)
  | seq (ts : List (Tree α))
  | bag (ts : List (Tree α))
deriving Inhabited

namespace Tree

variable {α β γ : Type}

mutual
def map (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .atom e => .atom e
  | .seq ts => .seq (maps f ts)
  | .bag ts => .bag (maps f ts)
def maps (f : α → β) : List (Tree α) → List (Tree β)
  | [] => []
  | t :: ts => map f t :: maps f ts
end

theorem maps_eq (f : α → β) : (ts : List (Tree α)) → maps f ts = ts.map (map f)
  | [] => rfl
  | t :: ts => by simp [maps, maps_eq f ts]

mutual
def leaves : Tree α → List α
  | .leaf a => [a]
  | .atom _ => []
  | .seq ts | .bag ts => leavess ts
def leavess : List (Tree α) → List α
  | [] => []
  | t :: ts => leaves t ++ leavess ts
end

theorem leavess_eq : (ts : List (Tree α)) → leavess ts = ts.flatMap leaves
  | [] => rfl
  | t :: ts => by simp [leavess, leavess_eq ts]

mutual
/-- The term a tree reads as, with each bag's items sorted, so that same trees read alike. `e` reads the leaves. -/
def erl (e : α → Erl) : Tree α → Erl
  | .leaf a => .tuple [.int 0, e a]
  | .atom x => .tuple [.int 1, x]
  | .seq ts => .tuple [.int 2, .list (erls e ts)]
  | .bag ts => .tuple [.int 3, .list (Erl.sort (erls e ts))]
def erls (e : α → Erl) : List (Tree α) → List Erl
  | [] => []
  | t :: ts => erl e t :: erls e ts
end

theorem erls_eq (e : α → Erl) : (ts : List (Tree α)) → erls e ts = ts.map (erl e)
  | [] => rfl
  | t :: ts => by simp [erls, erls_eq e ts]

mutual
theorem map_map (f : α → β) (g : β → γ) : (t : Tree α) → (t.map f).map g = t.map (g ∘ f)
  | .leaf _ => rfl
  | .atom _ => rfl
  | .seq ts => by simp only [map]; rw [maps_maps f g ts]
  | .bag ts => by simp only [map]; rw [maps_maps f g ts]
theorem maps_maps (f : α → β) (g : β → γ) : (ts : List (Tree α)) → maps g (maps f ts) = maps (g ∘ f) ts
  | [] => rfl
  | t :: ts => by simp only [maps]; rw [map_map f g t, maps_maps f g ts]
end

mutual
theorem map_congr {f g : α → β} : (t : Tree α) → (∀ a ∈ t.leaves, f a = g a) → t.map f = t.map g
  | .leaf a, h => by simp only [map]; rw [h a (by simp [leaves])]
  | .atom _, _ => rfl
  | .seq ts, h => by simp only [map]; rw [maps_congr ts (by simpa [leaves] using h)]
  | .bag ts, h => by simp only [map]; rw [maps_congr ts (by simpa [leaves] using h)]
theorem maps_congr {f g : α → β} : (ts : List (Tree α)) → (∀ a ∈ leavess ts, f a = g a) → maps f ts = maps g ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [maps]
    rw [map_congr t fun a ha => h a (by simp [leavess, ha]), maps_congr ts fun a ha => h a (by simp [leavess, ha])]
end

mutual
theorem leaves_map (f : α → β) : (t : Tree α) → (t.map f).leaves = t.leaves.map f
  | .leaf _ => rfl
  | .atom _ => rfl
  | .seq ts => by simp only [map, leaves]; exact leavess_maps f ts
  | .bag ts => by simp only [map, leaves]; exact leavess_maps f ts
theorem leavess_maps (f : α → β) : (ts : List (Tree α)) → leavess (maps f ts) = (leavess ts).map f
  | [] => rfl
  | t :: ts => by simp only [maps, leavess, List.map_append]; rw [leaves_map f t, leavess_maps f ts]
end


end Tree

/-- Lists whose images under `f` and `g` are the same multiset relate item by item once the second is reordered. -/
theorem multi_of_perm_map {α β γ : Type} {f : α → γ} {g : β → γ} :
    (xs : List α) → (ys : List β) → (xs.map f).Perm (ys.map g) → Multi (fun a b => f a = g b) xs ys
  | [], ys, h => by
    have := h.length_eq; cases ys with
    | nil => exact Multi.nil
    | cons => simp at this
  | x :: xs, ys, h => by
    have hm : f x ∈ ys.map g := h.mem_iff.1 (by simp)
    obtain ⟨y, hy, hfy⟩ := List.mem_map.1 hm
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hy
    have hp : (l1 ++ y :: l2).Perm (y :: (l1 ++ l2)) := List.perm_middle
    have h' : (xs.map f).Perm ((l1 ++ l2).map g) := by
      have := h.trans (hp.map g); rw [List.map_cons, List.map_cons, ← hfy] at this; exact this.cons_inv
    exact (Multi.cons (r := fun a b => f a = g b) hfy.symm (multi_of_perm_map xs _ h')).perm_right hp.symm

theorem map_eq_of_forall2 {α β γ : Type} {f : α → γ} {g : β → γ} :
    {xs : List α} → {zs : List β} → Forall2 (fun a b => f a = g b) xs zs → xs.map f = zs.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h, hs⟩ => by rw [List.map_cons, List.map_cons, h, map_eq_of_forall2 hs]
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- Lists related item by item once the second is reordered have images that are the same multiset. -/
theorem perm_map_of_multi {α β γ : Type} {f : α → γ} {g : β → γ} {xs : List α} {ys : List β}
    (h : Multi (fun a b => f a = g b) xs ys) : (xs.map f).Perm (ys.map g) := by
  obtain ⟨zs, h, hz⟩ := h
  rw [map_eq_of_forall2 h]; exact hz.map g

/-- Leaves that read as distinct terms, so that a tree's term tells its leaves apart. -/
class Leaf (α : Type) where
  toErl : α → Erl
  inj : ∀ a b, toErl a = toErl b → a = b

instance : Leaf Nat := ⟨fun n => .int n, fun _ _ h => by simp at h; omega⟩

instance : Leaf Key where
  toErl
    | .id (.fresh s i) => .tuple [.int 0, .int s, .int i]
    | .id (.named s) => .tuple [.int 1, .bin s.1]
    | .wire n => .tuple [.int 2, .int n]
  inj a b h := by
    rcases a with (⟨_, _⟩ | _) | _ <;> rcases b with (⟨_, _⟩ | _) | _ <;> simp_all [Subtype.ext_iff] <;> omega

instance : Leaf Name where
  toErl
    | .id s => .tuple [.int 0, .bin s]
    | .wire s => .tuple [.int 1, .bin s]
  inj a b h := by
    rcases a with _ | _ <;> rcases b with _ | _ <;> simp_all

instance {α : Type} [Leaf α] : Leaf (Option α) where
  toErl
    | none => .tuple [.int 0]
    | some a => .tuple [.int 1, Leaf.toErl a]
  inj a b h := by
    rcases a with _ | a <;> rcases b with _ | b <;> simp at h
    · rfl
    · rw [Leaf.inj a b h]

namespace Tree

variable {α β : Type} [Leaf α] [Leaf β]

/-- The same tree once every bag's items are reordered. -/
def Same (x y : Tree α) : Prop := x.erl Leaf.toErl = y.erl Leaf.toErl

instance (x y : Tree α) : Decidable (Same x y) := inferInstanceAs (Decidable (_ = _))

theorem same_leaf {a b : α} : Same (.leaf a) (.leaf b) ↔ a = b := by
  simp only [Same, erl, Erl.tuple.injEq, List.cons.injEq, true_and, and_true]
  exact ⟨Leaf.inj a b, fun h => h ▸ rfl⟩

theorem same_atom {e e' : Erl} : Same (α := α) (.atom e) (.atom e') ↔ e = e' := by
  simp [Same, erl]

theorem same_seq {xs ys : List (Tree α)} : Same (.seq xs) (.seq ys) ↔ Forall2 Same xs ys := by
  simp only [Same, erl, Erl.tuple.injEq, List.cons.injEq, Erl.list.injEq, true_and, and_true, erls_eq]
  induction xs generalizing ys with
  | nil => cases ys <;> simp [Forall2]
  | cons x xs ih => cases ys <;> simp [Forall2, ih, Same]

theorem same_bag {xs ys : List (Tree α)} : Same (.bag xs) (.bag ys) ↔ Multi Same xs ys := by
  simp only [Same, erl, Erl.tuple.injEq, List.cons.injEq, Erl.list.injEq, true_and, and_true, erls_eq,
    Erl.sort_eq_iff]
  exact ⟨multi_of_perm_map xs ys, perm_map_of_multi⟩

theorem same_refl (x : Tree α) : Same x x := rfl

def tag : Tree α → Nat
  | .leaf _ => 0
  | .atom _ => 1
  | .seq _ => 2
  | .bag _ => 3

theorem Same.tag {x y : Tree α} (h : Same x y) : x.tag = y.tag := by
  cases x <;> cases y <;> simp_all [Same, erl, Tree.tag]

mutual
/-- Same trees hold the same leaves, as often. -/
theorem Same.leaves : {x y : Tree α} → Same x y → x.leaves.Perm y.leaves
  | .leaf _, .leaf _, h => by rw [same_leaf.1 h]
  | .atom _, .atom _, _ => by simp [Tree.leaves]
  | .seq _, .seq _, h => by simp only [Tree.leaves]; exact forall2_leaves (same_seq.1 h)
  | .bag _, .bag _, h => by
    obtain ⟨zs, hz, hp⟩ := same_bag.1 h
    simp only [Tree.leaves]
    exact (forall2_leaves hz).trans (by rw [leavess_eq, leavess_eq]; exact hp.flatMap_right _)
  | .leaf _, .atom _, h => absurd h.tag (by simp [Tree.tag])
  | .leaf _, .seq _, h => absurd h.tag (by simp [Tree.tag])
  | .leaf _, .bag _, h => absurd h.tag (by simp [Tree.tag])
  | .atom _, .leaf _, h => absurd h.tag (by simp [Tree.tag])
  | .atom _, .seq _, h => absurd h.tag (by simp [Tree.tag])
  | .atom _, .bag _, h => absurd h.tag (by simp [Tree.tag])
  | .seq _, .leaf _, h => absurd h.tag (by simp [Tree.tag])
  | .seq _, .atom _, h => absurd h.tag (by simp [Tree.tag])
  | .seq _, .bag _, h => absurd h.tag (by simp [Tree.tag])
  | .bag _, .leaf _, h => absurd h.tag (by simp [Tree.tag])
  | .bag _, .atom _, h => absurd h.tag (by simp [Tree.tag])
  | .bag _, .seq _, h => absurd h.tag (by simp [Tree.tag])
theorem forall2_leaves : {xs ys : List (Tree α)} → Forall2 Same xs ys → (leavess xs).Perm (leavess ys)
  | [], [], _ => .refl _
  | _ :: _, _ :: _, ⟨h, hs⟩ => (Same.leaves h).append (forall2_leaves hs)
  | [], _ :: _, h | _ :: _, [], h => h.elim
end

omit [Leaf α] in
theorem tag_map {γ : Type} (f : γ → α) (x : Tree γ) : (x.map f).tag = x.tag := by cases x <;> rfl

mutual
/-- Renaming the leaves keeps same trees the same. -/
theorem Same.map (f : α → β) : {x y : Tree α} → Same x y → Same (x.map f) (y.map f)
  | .leaf _, .leaf _, h => by rw [same_leaf.1 h]; exact same_refl _
  | .atom _, .atom _, h => by simp only [Tree.map]; rw [same_atom.1 h]; exact same_refl _
  | .seq _, .seq _, h => by simp only [Tree.map, maps_eq]; exact same_seq.2 (forall2_map_same f (same_seq.1 h))
  | .bag _, .bag _, h => by
    obtain ⟨zs, hz, hp⟩ := same_bag.1 h
    simp only [Tree.map, maps_eq]
    exact same_bag.2 ⟨zs.map (Tree.map f), forall2_map_same f hz, hp.map _⟩
  | .leaf _, .atom _, h => absurd h.tag (by simp [Tree.tag])
  | .leaf _, .seq _, h => absurd h.tag (by simp [Tree.tag])
  | .leaf _, .bag _, h => absurd h.tag (by simp [Tree.tag])
  | .atom _, .leaf _, h => absurd h.tag (by simp [Tree.tag])
  | .atom _, .seq _, h => absurd h.tag (by simp [Tree.tag])
  | .atom _, .bag _, h => absurd h.tag (by simp [Tree.tag])
  | .seq _, .leaf _, h => absurd h.tag (by simp [Tree.tag])
  | .seq _, .atom _, h => absurd h.tag (by simp [Tree.tag])
  | .seq _, .bag _, h => absurd h.tag (by simp [Tree.tag])
  | .bag _, .leaf _, h => absurd h.tag (by simp [Tree.tag])
  | .bag _, .atom _, h => absurd h.tag (by simp [Tree.tag])
  | .bag _, .seq _, h => absurd h.tag (by simp [Tree.tag])
theorem forall2_map_same (f : α → β) : {xs ys : List (Tree α)} → Forall2 Same xs ys →
    Forall2 Same (xs.map (Tree.map f)) (ys.map (Tree.map f))
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨Same.map f h, forall2_map_same f hs⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim
end

variable {γ : Type}

omit [Leaf α] in
theorem forall2_of_map {δ ε : Type} {r : δ → ε → Prop} {f : γ → δ} {g : α → ε} :
    {xs : List γ} → {ys : List α} → Forall2 r (xs.map f) (ys.map g) → Forall2 (fun a b => r (f a) (g b)) xs ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨h, forall2_of_map hs⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

omit [Leaf α] in
theorem mem_leavess {t : Tree α} {ts : List (Tree α)} (ht : t ∈ ts) {a : α} (ha : a ∈ t.leaves) : a ∈ leavess ts := by
  rw [leavess_eq]; exact List.mem_flatMap.2 ⟨t, ht, ha⟩

mutual
/-- Two trees whose leaves read through `bk` and `bn` (their skeletons) are the same, and whose leaves agree under `g`
wherever their readings agree, are the same once the first's leaves are renamed by `g`. -/
theorem same_of_skel {σ : Type} [Leaf σ] (bk : γ → σ) (bn : α → σ) (g : γ → α) : (x : Tree γ) → (y : Tree α) →
    Same (x.map bk) (y.map bn) → (∀ a ∈ x.leaves, ∀ b ∈ y.leaves, bk a = bn b → g a = b) → Same (x.map g) y
  | .leaf a, .leaf b, h, hg => by
    simp only [Tree.map] at h ⊢
    rw [hg a (by simp [Tree.leaves]) b (by simp [Tree.leaves]) (same_leaf.1 h)]; exact same_refl _
  | .atom _, .atom _, h, _ => h
  | .seq xs, .seq ys, h, hg => by
    simp only [Tree.map, maps_eq] at h ⊢
    have h2 := forall2_skel bk bn g xs ys (forall2_of_map (same_seq.1 h)) (by simpa [Tree.leaves] using hg)
    exact same_seq.2 (forall2_map (R' := Same) (Tree.map g) (fun _ _ h => h) h2)
  | .bag xs, .bag ys, h, hg => by
    simp only [Tree.map, maps_eq] at h ⊢
    obtain ⟨zs, hz, hp⟩ := Multi.of_map (r := fun a b => Same (a.map bk) (b.map bn)) (fun _ _ h => h) (same_bag.1 h)
    have hzl : ∀ b ∈ leavess zs, b ∈ leavess ys := fun b hb => by
      rw [leavess_eq] at hb ⊢; exact (hp.flatMap_right _).mem_iff.1 hb
    have := forall2_skel bk bn g xs zs hz fun a ha b hb => hg a (by simpa [Tree.leaves] using ha) b
      (by simpa [Tree.leaves] using hzl b hb)
    exact same_bag.2 ((Multi.of_forall2 this).map (r' := Same) (g := id) (fun _ _ h => h) |>.perm_right
      (by simpa using hp))
  | .leaf _, .atom _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .leaf _, .seq _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .leaf _, .bag _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .atom _, .leaf _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .atom _, .seq _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .atom _, .bag _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .seq _, .leaf _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .seq _, .atom _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .seq _, .bag _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .bag _, .leaf _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .bag _, .atom _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
  | .bag _, .seq _, h, _ => absurd ((tag_map _ _).symm.trans (h.tag.trans (tag_map _ _))) (by simp [Tree.tag])
theorem forall2_skel {σ : Type} [Leaf σ] (bk : γ → σ) (bn : α → σ) (g : γ → α) : (xs : List (Tree γ)) → (ys : List (Tree α)) →
    Forall2 (fun a b => Same (a.map bk) (b.map bn)) xs ys →
    (∀ a ∈ leavess xs, ∀ b ∈ leavess ys, bk a = bn b → g a = b) → Forall2 (fun a b => Same (a.map g) b) xs ys
  | [], [], _, _ => trivial
  | x :: xs, y :: ys, ⟨h, hs⟩, hg =>
    ⟨same_of_skel bk bn g x y h fun a ha b hb => hg a (by simp [leavess, ha]) b (by simp [leavess, hb]),
      forall2_skel bk bn g xs ys hs fun a ha b hb => hg a (by simp [leavess, ha]) b (by simp [leavess, hb])⟩
  | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim
end

end Tree

end Tazuna.Trace
