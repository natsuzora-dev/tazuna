import Tazuna.Explore.Key
import Tazuna.Semantics.Reach
import Tazuna.Smt.PairCompare
import Tazuna.Semantics.ShiftOrder

/-! Reading a key back: data values whose keys are equal relate by any renaming that relates the counters the keys
rename alike and moves instants by the difference of the two time origins (`keyBy_read`), and a pending request's key
gives back its request up to such a renaming. -/

namespace Tazuna.Explore

open Tazuna.Ir Tazuna.Ir.Step

section Lists
variable {α β γ : Type} {r : α → β → Prop}

theorem forall2_of_map_eq2 {f : α → γ} {g : β → γ} : {xs : List α} → {ys : List β} → xs.map f = ys.map g →
    (∀ x ∈ xs, ∀ y ∈ ys, f x = g y → r x y) → Forall2 r xs ys
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, h, hr => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨hr _ List.mem_cons_self _ List.mem_cons_self h.1,
      forall2_of_map_eq2 h.2 fun x hx y hy => hr x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)⟩
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp at h

theorem multi_of_perm_map {f : α → γ} {g : β → γ} : {xs : List α} → {ys : List β} → (xs.map f).Perm (ys.map g) →
    (∀ x ∈ xs, ∀ y ∈ ys, f x = g y → r x y) → Multi r xs ys
  | [], ys, hp, _ => by
    have := hp.length_eq
    simp only [List.map_nil, List.length_nil, List.length_map] at this
    rw [List.eq_nil_of_length_eq_zero this.symm]
    exact Multi.nil
  | x :: xs, ys, hp, hr => by
    obtain ⟨y, hy, hxy⟩ := List.mem_map.1 (hp.subset (List.mem_cons_self (a := f x)))
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hy
    have hm : (l1 ++ y :: l2).Perm (y :: (l1 ++ l2)) := List.perm_middle
    have hp' : (xs.map f).Perm ((l1 ++ l2).map g) := by
      have h2 := hp.trans (hm.map g)
      rw [List.map_cons, List.map_cons, hxy] at h2
      exact h2.cons_inv
    have ih := multi_of_perm_map hp' fun a ha b hb e =>
      hr a (List.mem_cons_of_mem _ ha) b (hm.symm.subset (List.mem_cons_of_mem _ hb)) e
    exact (Multi.cons (hr x List.mem_cons_self y hy hxy.symm) ih).perm_right hm.symm

end Lists

section Read
variable {σ σ' : Nat → Nat} {δ δ' : Int}

theorem keyAltsBy_tag : (k : Nat) → (vs : List (List Ty)) → (y : (Ty.semAltsWith Dsl.base vs).1) →
    ∃ m ≥ k, ∃ rest, keyAltsBy σ δ k vs y = .tuple (.int (m : Nat) :: rest)
  | _, [], y => nomatch y
  | k, _ :: _, .inl _ => ⟨k, Nat.le_refl k, _, rfl⟩
  | k, _ :: vs, .inr y => by
    obtain ⟨m, hm, rest, h⟩ := keyAltsBy_tag (k + 1) vs y
    exact ⟨m, by omega, rest, h⟩

variable {A B : Nat → Prop} {R : PBij}

attribute [local instance] lexOrd in
mutual
/-- Values whose keys are equal relate by `R`, where `R` relates the counters `σ` and `σ'` rename alike and moves
instants from the origin `-δ` to `-δ'`: a key reads every part `Ty.rel0` compares, on a comparable type. -/
theorem keyBy_read (hR : ∀ c c', A c → B c' → σ c = σ' c' → R.rel c c') (hsh : R.shift = some (δ - δ')) :
    (t : Ty) → t.comparable = true → (x y : t.den0) → (∀ c ∈ ctrsIn t x, A c) → (∀ c ∈ ctrsIn t y, B c) →
    keyBy σ δ t x = keyBy σ' δ' t y → Ty.rel0 R t x y
  | .int, _, x, y, _, _, h => Erl.int.inj h
  | .str, _, x, y, _, _, h => Subtype.ext (Erl.bin.inj h)
  | .point .ms, _, x, y, _, _, h => by
    have e := Erl.int.inj h
    show R.point .ms x y
    simp only [PBij.point, hsh]
    dsimp only at e
    omega
  | .point .day, _, x, y, _, _, h => Erl.int.inj h
  | .id, _, .fresh c i, .fresh c' i', hx, hy, h => by
    simp only [keyBy, Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.ofNat_inj, and_true] at h
    exact .inr ⟨c, c', i, hR c c' (hx c (by simp [ctrsIn])) (hy c' (by simp [ctrsIn])) h.1, rfl, h.2 ▸ rfl⟩
  | .id, _, .named s, .named s', _, _, h => .inl ⟨s, rfl, by rw [Subtype.ext (Erl.bin.inj h)]⟩
  | .id, _, .fresh .., .named _, _, _, h | .id, _, .named _, .fresh .., _, _, h => by simp [keyBy] at h
  | .list t, hc, xs, ys, hx, hy, h =>
    forall2_of_map_eq2 (Erl.list.inj h) fun a ha b hb e =>
      keyBy_read hR hsh t hc a b (fun c hc' => hx c (List.mem_flatMap.2 ⟨a, ha, hc'⟩))
        (fun c hc' => hy c (List.mem_flatMap.2 ⟨b, hb, hc'⟩)) e
  | .bag t, hc, xs, ys, hx, hy, h =>
    multi_of_perm_map ((Erl.sort_eq_iff _ _).1 (Erl.list.inj h)) fun a ha b hb e =>
      keyBy_read hR hsh t hc a b (fun c hc' => hx c (List.mem_flatMap.2 ⟨a, ha, hc'⟩))
        (fun c hc' => hy c (List.mem_flatMap.2 ⟨b, hb, hc'⟩)) e
  | .table k v, hc, x, y, hx, hy, h => by
    simp only [Ty.comparable, Bool.and_eq_true] at hc
    simp only [keyBy, Erl.map.injEq] at h
    have hp := (Erl.sort_eq_iff _ _).1 ((map_fst_snd_iff _ _).1 h)
    refine multi_of_perm_map hp fun a ha b hb e => ?_
    simp only [Prod.mk.injEq] at e
    have hxa : ∀ c ∈ ctrsIn k a.1 ++ ctrsIn v a.2, A c := fun c hc' => hx c (List.mem_flatMap.2 ⟨a, ha, hc'⟩)
    have hyb : ∀ c ∈ ctrsIn k b.1 ++ ctrsIn v b.2, B c := fun c hc' => hy c (List.mem_flatMap.2 ⟨b, hb, hc'⟩)
    exact ⟨keyBy_read hR hsh k hc.1 a.1 b.1 (fun c h' => hxa c (List.mem_append_left _ h'))
        (fun c h' => hyb c (List.mem_append_left _ h')) e.1,
      keyBy_read hR hsh v hc.2 a.2 b.2 (fun c h' => hxa c (List.mem_append_right _ h'))
        (fun c h' => hyb c (List.mem_append_right _ h')) e.2⟩
  | .tuple ts, hc, x, y, hx, hy, h => keysBy_read hR hsh ts hc x y hx hy (Erl.tuple.inj h)
  | .adt _ _ vs, hc, x, y, hx, hy, h => keyAltsBy_read hR hsh 0 vs hc x y hx hy h
  | .param _, _, _, _, _, _, _ => trivial
  | .fn .., hc, _, _, _, _, _ => by simp [Ty.comparable] at hc
  | .dsl k _, hc, x, y, hx, hy, h => by
    cases k <;> simp [Ty.comparable] at hc
    revert x y
    show ∀ x y : Nat, (∀ c ∈ ctrsIn (.dsl .fresh _) x, A c) → (∀ c ∈ ctrsIn (.dsl .fresh _) y, B c) →
      keyBy σ δ (.dsl .fresh _) x = keyBy σ' δ' (.dsl .fresh _) y → R.rel x y
    intro x y hx hy h
    simp only [keyBy, Erl.int.injEq, Int.ofNat_inj] at h
    exact hR x y (hx x (by simp [ctrsIn])) (hy y (by simp [ctrsIn])) h
theorem keysBy_read (hR : ∀ c c', A c → B c' → σ c = σ' c' → R.rel c c') (hsh : R.shift = some (δ - δ')) :
    (ts : List Ty) → Ty.comparables ts = true → (x y : (Ty.semsWith Dsl.base ts).1) →
    (∀ c ∈ ctrssIn ts x, A c) → (∀ c ∈ ctrssIn ts y, B c) → keysBy σ δ ts x = keysBy σ' δ' ts y →
    Ty.relsWith Dsl.base (Dsl.rel0 R) R ts x y
  | [], _, (), (), _, _, _ => trivial
  | t :: ts, hc, (x, xs), (y, ys), hx, hy, h => by
    simp only [Ty.comparables, Bool.and_eq_true] at hc
    simp only [keysBy, List.cons.injEq] at h
    exact ⟨keyBy_read hR hsh t hc.1 x y (fun c h' => hx c (List.mem_append_left _ h'))
        (fun c h' => hy c (List.mem_append_left _ h')) h.1,
      keysBy_read hR hsh ts hc.2 xs ys (fun c h' => hx c (List.mem_append_right _ h'))
        (fun c h' => hy c (List.mem_append_right _ h')) h.2⟩
theorem keyAltsBy_read (hR : ∀ c c', A c → B c' → σ c = σ' c' → R.rel c c') (hsh : R.shift = some (δ - δ'))
    (k : Nat) : (vs : List (List Ty)) → Ty.comparabless vs = true → (x y : (Ty.semAltsWith Dsl.base vs).1) →
    (∀ c ∈ ctrsAltsIn vs x, A c) → (∀ c ∈ ctrsAltsIn vs y, B c) → keyAltsBy σ δ k vs x = keyAltsBy σ' δ' k vs y →
    Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs x y
  | [], _, x, _, _, _, _ => nomatch x
  | fs :: _, hc, .inl x, .inl y, hx, hy, h => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    simp only [keyAltsBy, Erl.tuple.injEq, List.cons.injEq, true_and] at h
    exact keysBy_read hR hsh fs hc.1 x y hx hy h
  | _ :: vs, hc, .inr x, .inr y, hx, hy, h => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    exact keyAltsBy_read hR hsh (k + 1) vs hc.2 x y hx hy h
  | _ :: vs, _, .inl x, .inr y, _, _, h => by
    obtain ⟨m, hm, rest, ht⟩ := keyAltsBy_tag (σ := σ') (δ := δ') (k + 1) vs y
    simp only [keyAltsBy, ht, Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.ofNat_inj] at h
    omega
  | _ :: vs, _, .inr x, .inl y, _, _, h => by
    obtain ⟨m, hm, rest, ht⟩ := keyAltsBy_tag (σ := σ) (δ := δ) (k + 1) vs x
    simp only [keyAltsBy, ht, Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.ofNat_inj] at h
    omega
end

end Read

theorem Dsl.ctorIdx_inj {a b : Dsl} (h : a.ctorIdx = b.ctorIdx) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Closes a goal whose hypothesis `h` equates the keys of types of different shapes. -/
local macro "mismatch" : tactic => `(tactic| first | (simp [tyKey] at *; done) | skip)

mutual
/-- Types with one key are one type. -/
theorem tyKey_inj : (a b : Ty) → tyKey a = tyKey b → a = b
  | .int, b, h | .str, b, h | .id, b, h => by cases b <;> mismatch
  | .point u, b, h => by
    cases b <;> mismatch
    rename_i w
    cases u <;> cases w <;> first | rfl |
      (simp only [tyKey, Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.natCast_inj] at h
       exact absurd h (by decide))
  | .list t, b, h => by
    cases b <;> mismatch
    simp only [tyKey, Erl.tuple.injEq, List.cons.injEq, true_and, and_true] at h
    rw [tyKey_inj _ _ h]
  | .bag t, b, h => by
    cases b <;> mismatch
    simp only [tyKey, Erl.tuple.injEq, List.cons.injEq, true_and, and_true] at h
    rw [tyKey_inj _ _ h]
  | .tuple ts, b, h => by
    cases b <;> mismatch
    simp only [tyKey, Erl.tuple.injEq, List.cons.injEq, Erl.list.injEq, true_and, and_true] at h
    rw [tysKey_inj _ _ h]
  | .fn ps r, b, h => by
    cases b <;> mismatch
    simp only [tyKey, Erl.tuple.injEq, List.cons.injEq, Erl.list.injEq, true_and, and_true] at h
    rw [tysKey_inj _ _ h.1, tyKey_inj _ _ h.2]
  | .adt i a vs, b, h => by
    cases b <;> mismatch
    simp only [tyKey, Erl.tuple.injEq, List.cons.injEq, Erl.list.injEq, Erl.int.injEq, Int.natCast_inj, true_and,
      and_true] at h
    rw [h.1, tysKey_inj _ _ h.2.1, tyssKey_inj _ _ h.2.2]
  | .param k, b, h => by
    cases b <;> mismatch
    simp only [tyKey, Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.natCast_inj, true_and, and_true] at h
    rw [h]
  | .table k v, b, h => by
    cases b <;> mismatch
    simp only [tyKey, Erl.tuple.injEq, List.cons.injEq, true_and, and_true] at h
    rw [tyKey_inj _ _ h.1, tyKey_inj _ _ h.2]
  | .dsl k a, b, h => by
    cases b <;> mismatch
    simp only [tyKey, Erl.tuple.injEq, List.cons.injEq, Erl.list.injEq, Erl.int.injEq, Int.natCast_inj, true_and,
      and_true] at h
    rw [Dsl.ctorIdx_inj h.1, tysKey_inj _ _ h.2]
theorem tysKey_inj : (a b : List Ty) → tysKey a = tysKey b → a = b
  | [], [], _ => rfl
  | t :: ts, u :: us, h => by
    simp only [tysKey, List.cons.injEq] at h
    rw [tyKey_inj _ _ h.1, tysKey_inj _ _ h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [tysKey] at h
theorem tyssKey_inj : (a b : List (List Ty)) → tyssKey a = tyssKey b → a = b
  | [], [], _ => rfl
  | t :: ts, u :: us, h => by
    simp only [tyssKey, List.cons.injEq, Erl.list.injEq] at h
    rw [tysKey_inj _ _ h.1, tyssKey_inj _ _ h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [tyssKey] at h
end

/-! The renaming a key reads: a binary search finds a number's rank among sorted numbers, so a renaming by rank keeps
the order of the numbers it is taken over. -/

section Rank
variable {xs : Array Nat} {x : Nat}

/-- Every index below the result holds a number below `x` and every index from it on one at least `x`. -/
theorem rankGo_spec (hs : ∀ i j (hi : i < xs.size) (hj : j < xs.size), i ≤ j → xs[i] ≤ xs[j]) :
    (lo hi : Nat) → (h : hi ≤ xs.size) → lo ≤ hi → (∀ i (hk : i < xs.size), i < lo → xs[i] < x) →
    (∀ i (hk : i < xs.size), hi ≤ i → x ≤ xs[i]) →
    rankGo xs x lo hi h ≤ hi ∧ (∀ i (hk : i < xs.size), i < rankGo xs x lo hi h → xs[i] < x) ∧
      ∀ i (hk : i < xs.size), rankGo xs x lo hi h ≤ i → x ≤ xs[i]
  | lo, hi, h, hle, hlo, hhi => by
    unfold rankGo
    split
    · rename_i hlt
      split
      · rename_i hm
        have := rankGo_spec hs ((lo + hi) / 2 + 1) hi h (by omega)
          (fun i hi' hi'' => if e : i = (lo + hi) / 2 then by subst e; exact hm
            else Nat.lt_of_le_of_lt (hs i _ hi' (by omega) (by omega)) hm) hhi
        exact ⟨this.1, this.2⟩
      · rename_i hm
        have := rankGo_spec hs lo ((lo + hi) / 2) (by omega) (by omega) hlo
          (fun i hi' hi'' => Nat.le_trans (Nat.le_of_not_lt hm) (hs _ i (by omega) hi' hi''))
        exact ⟨by omega, this.2⟩
    · exact ⟨hle, hlo, fun i hi' hi'' => hhi i hi' (by omega)⟩
termination_by lo hi => hi - lo

theorem rankIn_spec (hs : ∀ i j (hi : i < xs.size) (hj : j < xs.size), i ≤ j → xs[i] ≤ xs[j]) :
    rankIn xs x ≤ xs.size ∧ (∀ i (hi : i < xs.size), i < rankIn xs x → xs[i] < x) ∧
      ∀ i (hi : i < xs.size), rankIn xs x ≤ i → x ≤ xs[i] :=
  rankGo_spec hs 0 xs.size _ (Nat.zero_le _) (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h h' => absurd h (by omega))

/-- Ranks keep the order of the numbers the array holds. -/
theorem rankIn_lt (hs : ∀ i j (hi : i < xs.size) (hj : j < xs.size), i ≤ j → xs[i] ≤ xs[j]) {a b : Nat}
    (ha : a ∈ xs) (hab : a < b) : rankIn xs a < rankIn xs b ∧ rankIn xs a < xs.size := by
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem ha
  have h1 := (rankIn_spec (x := xs[j]) hs).2.1 j hj
  have h2 := (rankIn_spec (x := b) hs).2.2 j hj
  constructor
  · have : ¬ j < rankIn xs xs[j] := fun h => Nat.lt_irrefl _ (h1 h)
    have : ¬ rankIn xs b ≤ j := fun h => Nat.not_le_of_lt hab (h2 h)
    omega
  · have : ¬ j < rankIn xs xs[j] := fun h => Nat.lt_irrefl _ (h1 h)
    omega

end Rank

theorem belowOf_sorted (xs : List Nat) (base : Nat) :
    ∀ i j (hi : i < (belowOf xs base).size) (hj : j < (belowOf xs base).size), i ≤ j →
      (belowOf xs base)[i] ≤ (belowOf xs base)[j] := by
  intro i j hi hj hij
  have hp := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c h h' => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (xs.filter (· < base))
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · have := List.pairwise_iff_getElem.1 hp i j (by simpa [belowOf] using hi) (by simpa [belowOf] using hj) h
    simpa [belowOf] using this
  · exact Nat.le_refl _

theorem mem_belowOf {xs : List Nat} {base c : Nat} (h : c ∈ xs) (hc : c < base) : c ∈ belowOf xs base := by
  simp only [belowOf, List.mem_toArray]
  exact (List.mergeSort_perm _ _).symm.subset (List.mem_filter.2 ⟨h, by simpa using hc⟩)

/-- What `renameBelow cs base` renames in order: every number from `base` on, and those of `cs` below it. -/
def InRename (cs : Array Nat) (base c : Nat) : Prop := c < base → c ∈ cs

theorem renameBelow_lt {cs : Array Nat} {base : Nat}
    (hs : ∀ i j (hi : i < cs.size) (hj : j < cs.size), i ≤ j → cs[i] ≤ cs[j]) {a b : Nat} (ha : InRename cs base a)
    (hab : a < b) : renameBelow cs base a < renameBelow cs base b := by
  unfold renameBelow
  by_cases hb' : b < base
  · have ha' : a < base := by omega
    simp only [ha', hb', ↓reduceIte]
    exact (rankIn_lt hs (ha ha') hab).1
  · simp only [hb', ↓reduceIte]
    split
    · rename_i ha'
      have := (rankIn_lt hs (ha ha') (Nat.lt_of_lt_of_le ha' (Nat.le_of_not_lt hb'))).2
      omega
    · omega

/-- The renaming keeps the order of what it renames in order. -/
theorem renameBelow_compare {cs : Array Nat} {base : Nat}
    (hs : ∀ i j (hi : i < cs.size) (hj : j < cs.size), i ≤ j → cs[i] ≤ cs[j]) {a b : Nat} (ha : InRename cs base a)
    (hb : InRename cs base b) : compare (renameBelow cs base a) (renameBelow cs base b) = compare a b := by
  rcases Nat.lt_trichotomy a b with h | rfl | h
  · rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (renameBelow_lt hs ha h)]
  · simp
  · rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (renameBelow_lt hs hb h)]

/-- The renaming two keys read, relating what each renames in order to what the other renames alike. -/
def keyRen (σ σ' : Nat → Nat) (D D' : Nat → Prop) (hσ : ∀ a b, D a → D b → compare (σ a) (σ b) = compare a b)
    (hσ' : ∀ a b, D' a → D' b → compare (σ' a) (σ' b) = compare a b) (shift : Option Int) : PBij where
  rel c c' := D c ∧ D' c' ∧ σ c = σ' c'
  func := fun ⟨_, hb, e⟩ ⟨_, hb', e'⟩ => by
    have := hσ' _ _ hb hb'
    rw [← e, ← e', Nat.compare_eq_eq.2 rfl] at this
    exact (Nat.compare_eq_eq.1 this.symm)
  inj := fun ⟨ha, _, e⟩ ⟨ha', _, e'⟩ => by
    have := hσ _ _ ha ha'
    rw [e, e', Nat.compare_eq_eq.2 rfl] at this
    exact (Nat.compare_eq_eq.1 this.symm)
  shift := shift

theorem keyRen_mono {σ σ' : Nat → Nat} {D D' : Nat → Prop} (hσ : ∀ a b, D a → D b → compare (σ a) (σ b) = compare a b)
    (hσ' : ∀ a b, D' a → D' b → compare (σ' a) (σ' b) = compare a b) (shift : Option Int) :
    (keyRen σ σ' D D' hσ hσ' shift).Mono := by
  intro a b a' b' h h'
  rw [← hσ _ _ h.1 h'.1, ← hσ' _ _ h.2.1 h'.2.1, h.2.2, h'.2.2]

section Funs
variable {σ σ' : Nat → Nat} {δ δ' : Int} {A B : Nat → Prop} {R : PBij}

/-- Kept functions of the unique sites `P` whose keys are equal relate: the site gives the source, and the captured
values read back. -/
theorem funKey_read {P : List AnySite} (hP : SitesUnique P) (hR : ∀ c c', A c → B c' → σ c = σ' c' → R.rel c c')
    (hsh : R.shift = some (δ - δ')) {t : Ty} {f g : Fun t} (hf : f.asSite ∈ P) (hg : g.asSite ∈ P)
    (hc : (Ty.tuple f.Γ).comparable = true) (hx : ∀ c ∈ funCtrs f, A c) (hy : ∀ c ∈ funCtrs g, B c)
    (h : funKey σ δ f = funKey σ' δ' g) : Fun.Rel R f g := by
  simp only [funKey, siteKey, Erl.tuple.injEq, List.cons.injEq, Erl.bin.injEq, Erl.int.injEq, Int.ofNat_inj,
    and_true] at h
  obtain ⟨⟨hm, hi⟩, he⟩ := h
  have hs : f.site = g.site := by
    cases hf' : f.site; cases hg' : g.site; rw [hf', hg'] at hm hi; simp_all
  have e := site_eq hP hf hg hs
  obtain ⟨site, G, defs, Γ, env, hΓ, ht, body⟩ := f
  obtain ⟨site', G', defs', Γ', env', hΓ', ht', body'⟩ := g
  simp only [Fun.asSite, Sigma.mk.injEq] at e
  obtain ⟨rfl, e⟩ := e
  simp only [heq_eq_eq, Sigma.mk.injEq, true_and] at e
  cases e
  exact Site.fn_rel ⟨site, G, defs, hΓ, ht, body⟩ (keyBy_read hR hsh _ hc env env' hx hy he)

end Funs

end Tazuna.Explore
