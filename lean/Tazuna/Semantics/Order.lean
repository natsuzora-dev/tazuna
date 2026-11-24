import Tazuna.Semantics.Value

/-! The canonical order on data values: Erlang term order, the order Gleam's Erlang target compares values in. A value
is read as the Erlang term Gleam represents it by (`Ty.erl`), and terms compare as Erlang compares them: numbers before
atoms before tuples before maps before lists before binaries; tuples by size, then item by item; maps by size, then
keys in ascending order, then values in key order; lists item by item, a list before its extensions; atoms and
binaries by code points. A bag has no Erlang form of its own, so it compares as the list of its items in ascending
order. Wherever the semantics must put values in an order the spec does not write (instances that start in one step,
items of a bag on the wire), it uses this one, so the order is a function of the values and never of how a bag or table
happens to be stored. -/

namespace Tazuna.Ir

/-- An Erlang term, as far as Gleam values need. A map holds its keys in ascending order and its values in key order. -/
inductive Erl where
  | int (n : Int)
  | atom (name : String)
  | tuple (items : List Erl)
  | map (keys values : List Erl)
  | list (items : List Erl)
  | bin (text : String)
deriving Inhabited, Repr

namespace Erl

/-- One symbol of a term's serialization. -/
inductive Tok where
  | num (n : Int)
  | text (s : String)
deriving DecidableEq

def Tok.cmp : Tok → Tok → Ordering
  | .num a, .num b => compare a b
  | .text a, .text b => compare a b
  | .num _, .text _ => .lt
  | .text _, .num _ => .gt

instance : Std.TransCmp Tok.cmp where
  eq_swap {a b} := by
    cases a <;> cases b <;> simp only [Tok.cmp, Ordering.swap] <;> exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} := by
    cases a <;> cases b <;> cases c <;> simp [Tok.cmp] <;> exact Std.TransCmp.isLE_trans

instance : Std.LawfulEqCmp Tok.cmp where
  eq_of_compare {a b} h := by
    cases a <;> cases b <;> simp only [Tok.cmp, reduceCtorEq] at h <;> rw [Std.LawfulEqCmp.eq_of_compare h]

/- The serialization reads a term left to right in the order Erlang compares it: a kind tag (its rank in Erlang term
order), then sizes before items. Each list item is preceded by a marker that sorts above the end marker, so a list
sorts before its extensions. The code is uniquely decodable (`ser_inj`), so comparing serializations
lexicographically is a total order on terms. -/
mutual
def ser : Erl → List Tok
  | .int n => [.num 0, .num n]
  | .atom s => [.num 1, .text s]
  | .tuple xs => .num 2 :: .num xs.length :: sers xs
  | .map ks vs => .num 3 :: .num ks.length :: (sers ks ++ .num vs.length :: sers vs)
  | .list xs => .num 4 :: serl xs
  | .bin s => [.num 5, .text s]
def sers : List Erl → List Tok
  | [] => []
  | x :: xs => ser x ++ sers xs
def serl : List Erl → List Tok
  | [] => [.num 0]
  | x :: xs => .num 1 :: (ser x ++ serl xs)
end

mutual
theorem ser_inj : (a b : Erl) → (r r' : List Tok) → ser a ++ r = ser b ++ r' → a = b ∧ r = r'
  | .int n, b, r, r', h => by cases b <;> simp_all [ser]
  | .atom s, b, r, r', h => by cases b <;> simp_all [ser]
  | .bin s, b, r, r', h => by cases b <;> simp_all [ser]
  | .tuple xs, b, r, r', h => by
    cases b with
    | tuple ys =>
      simp only [ser, List.cons_append, List.cons.injEq, Tok.num.injEq, true_and] at h
      have hl : xs.length = ys.length := by omega
      obtain ⟨rfl, rfl⟩ := sers_inj xs ys r r' hl h.2
      exact ⟨rfl, rfl⟩
    | _ => simp [ser] at h
  | .map ks vs, b, r, r', h => by
    cases b with
    | map ks' vs' =>
      simp only [ser, List.cons_append, List.append_assoc, List.cons.injEq, Tok.num.injEq, true_and] at h
      have hl : ks.length = ks'.length := by omega
      obtain ⟨rfl, h2⟩ := sers_inj ks ks' _ _ hl h.2
      simp only [List.cons.injEq, Tok.num.injEq] at h2
      have hl' : vs.length = vs'.length := by omega
      obtain ⟨rfl, rfl⟩ := sers_inj vs vs' r r' hl' h2.2
      exact ⟨rfl, rfl⟩
    | _ => simp [ser] at h
  | .list xs, b, r, r', h => by
    cases b with
    | list ys =>
      simp only [ser, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := serl_inj xs ys r r' h
      exact ⟨rfl, rfl⟩
    | _ => simp [ser] at h
theorem sers_inj : (xs ys : List Erl) → (r r' : List Tok) → xs.length = ys.length →
    sers xs ++ r = sers ys ++ r' → xs = ys ∧ r = r'
  | [], [], r, r', _, h => by simpa [sers] using h
  | x :: xs, y :: ys, r, r', hl, h => by
    simp only [sers, List.append_assoc] at h
    obtain ⟨rfl, h2⟩ := ser_inj x y _ _ h
    obtain ⟨rfl, rfl⟩ := sers_inj xs ys r r' (by simpa using hl) h2
    exact ⟨rfl, rfl⟩
  | [], _ :: _, _, _, hl, _ | _ :: _, [], _, _, hl, _ => by simp at hl
theorem serl_inj : (xs ys : List Erl) → (r r' : List Tok) → serl xs ++ r = serl ys ++ r' → xs = ys ∧ r = r'
  | [], [], r, r', h => by simpa [serl] using h
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [serl] at h
  | x :: xs, y :: ys, r, r', h => by
    simp only [serl, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
    obtain ⟨rfl, h2⟩ := ser_inj x y _ _ h
    obtain ⟨rfl, rfl⟩ := serl_inj xs ys r r' h2
    exact ⟨rfl, rfl⟩
end

/-- Erlang term order. -/
def cmp (a b : Erl) : Ordering := List.compareLex Tok.cmp (ser a) (ser b)

instance : Ord Erl := ⟨cmp⟩

instance : Std.TransOrd Erl where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := List.compareLex Tok.cmp)
  isLE_trans := Std.TransCmp.isLE_trans (cmp := List.compareLex Tok.cmp)

instance : Std.LawfulEqOrd Erl where
  eq_of_compare {a b} h := by
    have h' : ser a = ser b := Std.LawfulEqCmp.eq_of_compare (cmp := List.compareLex Tok.cmp) h
    exact (ser_inj a b [] [] (by simpa using h')).1

instance : DecidableEq Erl := fun a b =>
  decidable_of_iff (compare a b = .eq) Std.LawfulEqCmp.compare_eq_iff_eq

/-! Erlang term order read off the terms: comparing two serializations with tails compares the terms first, since no
term's serialization extends another's (`ser_inj`). The order encoding reads it this way. -/

theorem lex_append : (u w r r' : List Tok) → (∀ t, u = w ++ t ∨ w = u ++ t → t = []) →
    List.compareLex Tok.cmp (u ++ r) (w ++ r') = (List.compareLex Tok.cmp u w).then (List.compareLex Tok.cmp r r')
  | [], [], _, _, _ => by simp [List.compareLex_nil_nil, Ordering.then]
  | [], y :: w, _, _, h => by simpa using h (y :: w) (.inr rfl)
  | x :: u, [], _, _, h => by simpa using h (x :: u) (.inl rfl)
  | x :: u, y :: w, r, r', h => by
    simp only [List.cons_append, List.compareLex_cons_cons]
    cases hxy : Tok.cmp x y with
    | lt => rfl
    | gt => rfl
    | eq =>
      have := Std.LawfulEqCmp.eq_of_compare hxy; subst this
      simp only [Ordering.then]
      exact lex_append u w r r' fun t ht => h t (by simpa using ht)

theorem ser_then (a b : Erl) (r r' : List Tok) :
    List.compareLex Tok.cmp (ser a ++ r) (ser b ++ r') = (cmp a b).then (List.compareLex Tok.cmp r r') := by
  refine lex_append _ _ r r' fun t ht => ?_
  rcases ht with ht | ht
  · exact (ser_inj b a t [] (by simp [← ht])).2
  · exact (ser_inj a b t [] (by simp [← ht])).2

/-- Lists of terms compared item by item, for lists of one length. -/
def cmps : List Erl → List Erl → Ordering
  | x :: xs, y :: ys => (cmp x y).then (cmps xs ys)
  | _, _ => .eq

theorem sers_then : (xs ys : List Erl) → xs.length = ys.length → (r r' : List Tok) →
    List.compareLex Tok.cmp (sers xs ++ r) (sers ys ++ r') = (cmps xs ys).then (List.compareLex Tok.cmp r r')
  | [], [], _, _, _ => by simp [sers, cmps, Ordering.then]
  | x :: xs, y :: ys, h, r, r' => by
    simp only [sers, List.append_assoc, ser_then, cmps]
    rw [sers_then xs ys (by simpa using h)]
    cases cmp x y <;> rfl
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => by simp at h

theorem cmp_int (a b : Int) : cmp (.int a) (.int b) = compare a b := by
  simp only [cmp, ser, List.compareLex_cons_cons, Tok.cmp, List.compareLex_nil_nil]
  cases compare a b <;> rfl

theorem cmp_bin (a b : String) : cmp (.bin a) (.bin b) = compare a b := by
  simp only [cmp, ser, List.compareLex_cons_cons, Tok.cmp, List.compareLex_nil_nil]
  cases compare a b <;> rfl

theorem cmp_int_bin (a : Int) (b : String) : cmp (.int a) (.bin b) = .lt := by
  simp [cmp, ser, List.compareLex_cons_cons, Tok.cmp]; rfl

theorem cmp_bin_int (a : String) (b : Int) : cmp (.bin a) (.int b) = .gt := by
  simp [cmp, ser, List.compareLex_cons_cons, Tok.cmp]; rfl

theorem cmp_atom (a b : String) : cmp (.atom a) (.atom b) = compare a b := by
  simp only [cmp, ser, List.compareLex_cons_cons, Tok.cmp, List.compareLex_nil_nil]
  cases compare a b <;> rfl

theorem cmp_atom_tuple (a : String) (ys : List Erl) : cmp (.atom a) (.tuple ys) = .lt := by
  simp [cmp, ser, List.compareLex_cons_cons, Tok.cmp]; rfl

theorem cmp_tuple_atom (xs : List Erl) (b : String) : cmp (.tuple xs) (.atom b) = .gt := by
  simp [cmp, ser, List.compareLex_cons_cons, Tok.cmp]; rfl

/-- Tuples compare by size, then item by item. -/
theorem cmp_tuple (xs ys : List Erl) :
    cmp (.tuple xs) (.tuple ys) = if xs.length = ys.length then cmps xs ys else compare xs.length ys.length := by
  simp only [cmp, ser, List.compareLex_cons_cons, Tok.cmp]
  split
  · rename_i h
    have := sers_then xs ys h [] []
    simp only [List.append_nil, List.compareLex_nil_nil] at this
    rw [this, h]
    simp [Ordering.then]; cases cmps xs ys <;> rfl
  · rename_i h
    have h' : compare (xs.length : Int) ys.length ≠ .eq := by
      intro e; exact h (by have := Std.LawfulEqCmp.eq_of_compare e; omega)
    have hc : compare (xs.length : Int) ys.length = compare xs.length ys.length := by
      simp only [compare, compareOfLessAndEq]
      split <;> split <;> (try split) <;> (try split) <;> first | rfl | omega
    simp only [Ordering.then]
    rw [← hc]
    cases compare (xs.length : Int) ys.length <;> simp_all

/-- Sorted ascending. -/
def sort {α : Type} [Ord α] (xs : List α) : List α := xs.mergeSort fun a b => (compare a b).isLE

/-- Two lists sort to the same list exactly when they hold the same items as often. -/
theorem sort_eq_iff {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] (xs ys : List α) :
    sort xs = sort ys ↔ xs.Perm ys := by
  constructor
  · intro h
    unfold sort at h
    exact (List.mergeSort_perm xs _).symm.trans (h ▸ List.mergeSort_perm ys _ :)
  · intro h
    have trans : ∀ a b c : α, (compare a b).isLE → (compare b c).isLE → (compare a c).isLE :=
      fun _ _ _ => Std.TransCmp.isLE_trans
    have total : ∀ a b : α, ((compare a b).isLE || (compare b a).isLE) = true := by
      intro a b
      rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := a) (b := b)]
      cases compare b a <;> rfl
    refine List.Perm.eq_of_pairwise (le := fun a b => (compare a b).isLE = true) ?_
      (List.pairwise_mergeSort trans total xs) (List.pairwise_mergeSort trans total ys)
      ((List.mergeSort_perm xs _).trans (h.trans (List.mergeSort_perm ys _).symm))
    intro a b _ _ hab hba
    exact Std.LawfulEqCmp.eq_of_compare (Std.OrientedCmp.isLE_antisymm hab hba)

end Erl

/-- The atom of variant `k` of a declaration's variants. -/
def atomAt (decl : List Variant) (k : Nat) : String := ((decl[k]?).map (atomName ·.name)).getD ""

/-- The variants of the declaration a `Ty.adt` names by its index. -/
def variantsAt (T : List TypeDecl) (i : Nat) : List Variant := (T[i]?.map (·.variants)).getD []

/-- The tag of a term Gleam makes for a variant: the atom, alone or at the head of a tuple. -/
def Erl.tag : Erl → Option String
  | .atom a => some a
  | .tuple (.atom a :: _) => some a
  | _ => none

attribute [local instance] lexOrd

section
variable (T : List TypeDecl)

mutual
/-- The Erlang term Gleam's Erlang target represents a value by. A bag, which has no Erlang form of its own, is the
list of its items in ascending order. -/
def Ty.erl : (t : Ty) → t.den0 → Erl
  | .int, n => .int n
  | .str, s => .bin s
  | .list t, xs => .list (xs.map (Ty.erl t))
  | .bag t, xs => .list (Erl.sort (xs.map (Ty.erl t)))
  | .tuple ts, x => .tuple (Ty.erls ts x)
  | .adt i _ vs, x => Ty.erlAlts (variantsAt T i) 0 vs x
  | .table k v, x =>
    let ps := Erl.sort (x.1.map fun e => (Ty.erl k e.1, Ty.erl v e.2))
    .map (ps.map (·.1)) (ps.map (·.2))
  | .date, d => .int d
  -- An id made fresh compares by when it was made, before every id from outside, which compares by its name.
  | .id, .fresh n => .int n
  | .id, .named s => .bin s
  -- A fresh-id source is a counter.
  | .dsl .fresh _, n => .int (show Nat from n)
  | .param _, _ | .fn .., _ | .dsl .., _ => .atom "nil"
def Ty.erls : (ts : List Ty) → (Ty.semsWith Dsl.base ts).1 → List Erl
  | [], () => []
  | t :: ts, (x, xs) => Ty.erl t x :: Ty.erls ts xs
/-- A value of the variants `vs`, which are the declaration's variants from index `k` on: an atom for a variant
without fields, else a tuple of the atom and the fields. -/
def Ty.erlAlts (decl : List Variant) (k : Nat) : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → Erl
  | [], x => nomatch x
  | [] :: _, .inl () => .atom (atomAt decl k)
  | (f :: fs) :: _, .inl x => .tuple (.atom (atomAt decl k) :: Ty.erls (f :: fs) x)
  | _ :: vs, .inr y => Ty.erlAlts decl (k + 1) vs y
end

mutual
/-- Whether the canonical order on the type is total with `==` as its equality: the type is `comparable`, and the
variants of each custom type have distinct atoms, which Gleam's naming rules give and loading checks. -/
def Ty.ordered : Ty → Bool
  | .int | .str | .date | .id | .param _ => true
  | .dsl k _ => k == .fresh
  | .list t | .bag t => Ty.ordered t
  | .tuple ts => Ty.ordereds ts
  | .adt i _ vs => decide (((List.range vs.length).map (atomAt (variantsAt T i))).Nodup) && Ty.orderedss vs
  | .table k v => Ty.ordered k && Ty.ordered v
  | .fn .. => false
def Ty.ordereds : List Ty → Bool
  | [] => true
  | t :: ts => Ty.ordered t && Ty.ordereds ts
def Ty.orderedss : List (List Ty) → Bool
  | [] => true
  | ts :: vs => Ty.ordereds ts && Ty.orderedss vs
end

/-- The canonical order: values compare as their Erlang terms do. -/
def Ty.cmp (t : Ty) (x y : t.den0) : Ordering := compare (Ty.erl T t x) (Ty.erl T t y)

end

section Lemmas

theorem listBeq_iff {α β : Type} {f : α → α → Bool} {g : α → β} (h : ∀ x y, f x y = true ↔ g x = g y) :
    ∀ xs ys : List α, listBeq f xs ys = true ↔ xs.map g = ys.map g
  | [], [] => by simp [listBeq]
  | [], _ :: _ | _ :: _, [] => by simp [listBeq]
  | x :: xs, y :: ys => by simp [listBeq, h, listBeq_iff h xs ys]

/-- Two lists are permutations of each other when they are as long and each item of one occurs as often in both. -/
theorem perm_iff_counts {α : Type} [DecidableEq α] :
    ∀ l₁ l₂ : List α, l₁.Perm l₂ ↔ l₁.length = l₂.length ∧ ∀ a ∈ l₁, l₁.count a = l₂.count a
  | l₁, l₂ => by
    refine ⟨fun h => ⟨h.length_eq, fun a _ => h.count_eq a⟩, ?_⟩
    induction l₁ generalizing l₂ with
    | nil =>
      rintro ⟨hl, -⟩
      cases l₂ with
      | nil => exact .nil
      | cons => simp at hl
    | cons a l₁ ih =>
      rintro ⟨hl, hc⟩
      have ha : a ∈ l₂ := by
        have := hc a List.mem_cons_self
        rw [List.count_cons] at this
        exact List.count_pos_iff.1 (by simp at this; omega)
      refine (List.Perm.cons a (ih (l₂.erase a) ⟨?_, ?_⟩)).trans (List.perm_cons_erase ha).symm
      · rw [List.length_erase_of_mem ha]; simp at hl; omega
      · intro b hb
        have := hc b (List.mem_cons_of_mem a hb)
        rw [List.count_cons] at this
        rw [List.count_erase]
        cases hab : (a == b) <;> simp only [hab, Bool.false_eq_true, ite_false, ite_true] at this ⊢ <;> omega

theorem bagBeq_iff {α β : Type} {f : α → α → Bool} {g : α → β} (h : ∀ x y, f x y = true ↔ g x = g y)
    (xs ys : List α) : bagBeq f xs ys = true ↔ (xs.map g).Perm (ys.map g) := by
  classical
  have hc : ∀ x l, countBy f x l = (l.map g).count (g x) := by
    intro x l
    rw [countBy, List.count, List.countP_map, List.countP_eq_length_filter]
    congr 1
    apply List.filter_congr
    intro y _
    show f x y = (g y == g x)
    rw [Bool.eq_iff_iff, h x y, beq_iff_eq, eq_comm]
  rw [perm_iff_counts]
  simp [bagBeq, hc, List.all_eq_true]

theorem lookupBy_some {κ ν : Type} {f : κ → κ → Bool} {k : κ} :
    ∀ {l : List (κ × ν)} {w : ν}, lookupBy f k l = some w → ∃ k', (k', w) ∈ l ∧ f k k' = true
  | [], _, h => by simp [lookupBy] at h
  | (k', v) :: l, w, h => by
    simp only [lookupBy] at h
    split at h
    · cases h; exact ⟨k', List.mem_cons_self, by assumption⟩
    · obtain ⟨k'', hm, hf⟩ := lookupBy_some h
      exact ⟨k'', List.mem_cons_of_mem _ hm, hf⟩

theorem lookupBy_of_mem {κ ν : Type} {f : κ → κ → Bool} {k : κ} :
    ∀ {l : List (κ × ν)} {e : κ × ν}, e ∈ l → f k e.1 = true → ∃ w, lookupBy f k l = some w
  | [], _, h, _ => by simp at h
  | (k', v) :: l, e, h, hf => by
    simp only [lookupBy]
    split
    · exact ⟨v, rfl⟩
    · rcases List.mem_cons.1 h with rfl | h
      · simp_all
      · exact lookupBy_of_mem h hf

theorem eq_of_nodup_fst {α β : Type} :
    ∀ {l : List (α × β)}, (l.map (·.1)).Nodup → ∀ {p q : α × β}, p ∈ l → q ∈ l → p.1 = q.1 → p = q
  | [], _, _, _, hp, _, _ => by simp at hp
  | r :: l, hn, p, q, hp, hq, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.1 hp with h1 | hp <;> rcases List.mem_cons.1 hq with h2 | hq
    · rw [h1, h2]
    · exact absurd ⟨q, hq, by rw [← he, h1]⟩ hn.1
    · exact absurd ⟨p, hp, by rw [he, h2]⟩ hn.1
    · exact eq_of_nodup_fst hn.2 hp hq he

theorem tableBeq_iff {κ ν : Type} {fk : κ → κ → Bool} {fv : ν → ν → Bool} {gk : κ → Erl} {gv : ν → Erl}
    (hk : ∀ a b, fk a b = true ↔ gk a = gk b) (hv : ∀ a b, fv a b = true ↔ gv a = gv b) {xs ys : List (κ × ν)}
    (hx : KeysUnique fk xs) (hy : KeysUnique fk ys) :
    tableBeq fk fv xs ys = true ↔
      (xs.map fun e => (gk e.1, gv e.2)).Perm (ys.map fun e => (gk e.1, gv e.2)) := by
  let P : κ × ν → Erl × Erl := fun e => (gk e.1, gv e.2)
  have nd : ∀ l, KeysUnique fk l → ((l.map P).map (·.1)).Nodup := by
    intro l hl
    simp only [List.map_map]
    unfold List.Nodup
    rw [List.pairwise_map]
    exact hl.imp fun h e => by have := (hk _ _).2 e; simp_all
  have ndP : ∀ l, KeysUnique fk l → (l.map P).Nodup := fun l hl => (nd l hl).of_map (·.1) fun _ _ h e => h (e ▸ rfl)
  show tableBeq fk fv xs ys = true ↔ (xs.map P).Perm (ys.map P)
  rw [perm_iff_counts]
  constructor
  · intro h
    simp only [tableBeq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    refine ⟨by simpa using h.1, ?_⟩
    intro a ha
    obtain ⟨⟨k, v⟩, he, rfl⟩ := List.mem_map.1 ha
    rw [(ndP xs hx).count_of_mem ha, (ndP ys hy).count_of_mem ?_]
    have := h.2 (k, v) he
    split at this
    · next w hw =>
      obtain ⟨k', hm, hkk⟩ := lookupBy_some hw
      exact List.mem_map.2 ⟨(k', w), hm, by simp [P, (hk _ _).1 hkk, (hv _ _).1 this]⟩
    · simp at this
  · rintro ⟨hlen, hc⟩
    simp only [tableBeq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨by simpa using hlen, ?_⟩
    intro ⟨k, v⟩ he
    have hpx := List.mem_map_of_mem (f := P) he
    have hm : P (k, v) ∈ ys.map P := by
      have := hc _ hpx
      rw [(ndP xs hx).count_of_mem hpx] at this
      exact List.count_pos_iff.1 (by omega)
    obtain ⟨⟨k', w⟩, hm', he'⟩ := List.mem_map.1 hm
    simp only [P, Prod.mk.injEq] at he'
    obtain ⟨w'', hw''⟩ := lookupBy_of_mem (f := fk) (k := k) hm' ((hk k k').2 he'.1.symm)
    obtain ⟨k'', hm'', hkk''⟩ := lookupBy_some hw''
    have heq : P (k'', w'') = P (k', w) :=
      eq_of_nodup_fst (nd ys hy) (List.mem_map_of_mem hm'') (List.mem_map_of_mem hm')
        (by simp [P, ← (hk _ _).1 hkk'', he'.1])
    simp only [P, Prod.mk.injEq] at heq
    rw [hw'']
    exact (hv v w'').2 (by rw [heq.2, he'.2])

theorem map_fst_snd_iff {α β : Type} :
    ∀ xs ys : List (α × β), (xs.map (·.1) = ys.map (·.1) ∧ xs.map (·.2) = ys.map (·.2)) ↔ xs = ys
  | [], [] => by simp
  | [], _ :: _ | _ :: _, [] => by simp
  | (a, b) :: xs, (c, d) :: ys => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, ← map_fst_snd_iff xs ys]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

end Lemmas

section
variable (T : List TypeDecl)

theorem Ty.erlAlts_tag (decl : List Variant) :
    ∀ (j : Nat) (vs : List (List Ty)) (y : (Ty.semAltsWith Dsl.base vs).1),
      ∃ m < vs.length, (Ty.erlAlts T decl j vs y).tag = some (atomAt decl (j + m))
  | _, [], y => nomatch y
  | j, [] :: _, .inl () => ⟨0, by simp, by simp [Ty.erlAlts, Erl.tag]⟩
  | j, (_ :: _) :: _, .inl _ => ⟨0, by simp, by simp [Ty.erlAlts, Erl.tag]⟩
  | j, _ :: vs, .inr y => by
    obtain ⟨m, hm, h⟩ := Ty.erlAlts_tag decl (j + 1) vs y
    exact ⟨m + 1, by simp; omega, by simp only [Ty.erlAlts]; rw [h]; congr 2; omega⟩

theorem Ty.erlAlts_tag_inl (decl : List Variant) (j : Nat) (fs : List Ty) (vs : List (List Ty))
    (x : (Ty.semsWith Dsl.base fs).1) :
    (Ty.erlAlts T decl j (fs :: vs) (.inl x)).tag = some (atomAt decl j) := by
  cases fs with
  | nil => cases x; rfl
  | cons => rfl

theorem atoms_head {decl : List Variant} {j n : Nat} (hd : ((List.range (n + 1)).map fun m => atomAt decl (j + m)).Nodup) :
    (∀ m < n, atomAt decl j ≠ atomAt decl (j + 1 + m)) ∧ ((List.range n).map fun m => atomAt decl (j + 1 + m)).Nodup := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.nodup_cons] at hd
  have e : ((fun m => atomAt decl (j + m)) ∘ Nat.succ) = fun m => atomAt decl (j + 1 + m) := by
    funext m; show atomAt decl (j + (m + 1)) = _; congr 1; omega
  rw [e] at hd
  refine ⟨fun m hm h => hd.1 (List.mem_map.2 ⟨m, List.mem_range.2 hm, ?_⟩), hd.2⟩
  simp only [Nat.add_zero]; exact h.symm

mutual
/-- `==` is equality of Erlang terms on every ordered type. -/
theorem Ty.erl_iff : (t : Ty) → t.ordered T = true → (x y : t.den0) →
    ((Ty.semWith Dsl.base t).2 x y = true ↔ t.erl T x = t.erl T y)
  | .int, _, x, y => (beq_iff_eq (α := Int) (a := x) (b := y)).trans ⟨congrArg Erl.int, Erl.int.inj⟩
  | .str, _, x, y => (beq_iff_eq (α := String) (a := x) (b := y)).trans ⟨congrArg Erl.bin, Erl.bin.inj⟩
  | .date, _, x, y => (beq_iff_eq (α := Int) (a := x) (b := y)).trans ⟨congrArg Erl.int, Erl.int.inj⟩
  | .param _, _, x, y => by simp [Ty.semWith, Ty.erl]
  | .id, _, x, y => by cases x <;> cases y <;> simp [Ty.semWith, Ty.erl]; omega
  | .list t, h, xs, ys => by
    show listBeq _ xs ys = true ↔ Erl.list _ = Erl.list _
    rw [Erl.list.injEq]
    exact listBeq_iff (Ty.erl_iff t h) xs ys
  | .bag t, h, xs, ys => by
    show bagBeq _ xs ys = true ↔ Erl.list _ = Erl.list _
    rw [Erl.list.injEq, Erl.sort_eq_iff]
    exact bagBeq_iff (Ty.erl_iff t h) xs ys
  | .tuple ts, h, x, y => by
    show _ ↔ Erl.tuple _ = Erl.tuple _
    rw [Erl.tuple.injEq]
    exact Ty.erls_iff ts h x y
  | .adt i _ vs, h, x, y => by
    simp only [Ty.ordered, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Ty.erlAlts_iff (variantsAt T i) 0 vs h.2 (by simpa using h.1) x y
  | .table k v, h, x, y => by
    simp only [Ty.ordered, Bool.and_eq_true] at h
    show tableBeq _ _ x.1 y.1 = true ↔ Erl.map _ _ = Erl.map _ _
    rw [Erl.map.injEq, map_fst_snd_iff, Erl.sort_eq_iff]
    exact tableBeq_iff (Ty.erl_iff k h.1) (Ty.erl_iff v h.2) x.2 y.2
  | .dsl k _, h, x, y => by
    cases k <;> simp [Ty.ordered] at h
    exact (beq_iff_eq (α := Nat) (a := x) (b := y)).trans
      ⟨fun e => congrArg (fun n : Nat => Erl.int n) e, fun e => Int.ofNat_inj.1 (Erl.int.inj e)⟩
  | .fn .., h, _, _ => by simp [Ty.ordered] at h
theorem Ty.erls_iff : (ts : List Ty) → Ty.ordereds T ts = true → (x y : (Ty.semsWith Dsl.base ts).1) →
    ((Ty.semsWith Dsl.base ts).2 x y = true ↔ Ty.erls T ts x = Ty.erls T ts y)
  | [], _, (), () => by simp [Ty.semsWith, Ty.erls]
  | t :: ts, h, (x, xs), (y, ys) => by
    simp only [Ty.ordereds, Bool.and_eq_true] at h
    show ((Ty.semWith Dsl.base t).2 x y && (Ty.semsWith Dsl.base ts).2 xs ys) = true ↔ _
    simp only [Bool.and_eq_true, Ty.erls, List.cons.injEq, Ty.erl_iff t h.1 x y, Ty.erls_iff ts h.2 xs ys]
theorem Ty.erlAlts_iff (decl : List Variant) : (j : Nat) → (vs : List (List Ty)) → Ty.orderedss T vs = true →
    ((List.range vs.length).map fun m => atomAt decl (j + m)).Nodup →
    (x y : (Ty.semAltsWith Dsl.base vs).1) →
    ((Ty.semAltsWith Dsl.base vs).2 x y = true ↔ Ty.erlAlts T decl j vs x = Ty.erlAlts T decl j vs y)
  | _, [], _, _, x, _ => nomatch x
  | j, [] :: vs, _, _, .inl (), .inl () => by simp [Ty.semAltsWith, Sem.sum, Ty.semsWith, Ty.erlAlts]
  | j, (f :: fs) :: vs, h, _, .inl x, .inl y => by
    simp only [Ty.orderedss, Bool.and_eq_true] at h
    show (Ty.semsWith Dsl.base (f :: fs)).2 x y = true ↔ _
    simp only [Ty.erlAlts, Erl.tuple.injEq, List.cons.injEq, true_and]
    exact Ty.erls_iff (f :: fs) h.1 x y
  | j, fs :: vs, h, hd, .inr x, .inr y => by
    simp only [Ty.orderedss, Bool.and_eq_true] at h
    simp only [Ty.semAltsWith, Sem.sum, Ty.erlAlts]
    exact Ty.erlAlts_iff decl (j + 1) vs h.2 (atoms_head hd).2 x y
  | j, fs :: vs, _, hd, .inl x, .inr y => by
    simp only [Ty.semAltsWith, Sem.sum, Bool.false_eq_true, false_iff]
    intro heq
    obtain ⟨m, hm, ht⟩ := Ty.erlAlts_tag T decl (j + 1) vs y
    have := Ty.erlAlts_tag_inl T decl j fs vs x
    rw [heq] at this
    simp only [Ty.erlAlts] at this
    rw [ht, Option.some.injEq] at this
    exact (atoms_head hd).1 m hm this.symm
  | j, fs :: vs, _, hd, .inr x, .inl y => by
    simp only [Ty.semAltsWith, Sem.sum, Bool.false_eq_true, false_iff]
    intro heq
    obtain ⟨m, hm, ht⟩ := Ty.erlAlts_tag T decl (j + 1) vs x
    have := Ty.erlAlts_tag_inl T decl j fs vs y
    rw [← heq] at this
    simp only [Ty.erlAlts] at this
    rw [ht, Option.some.injEq] at this
    exact (atoms_head hd).1 m hm this.symm
end

/-- The canonical order is a total order on the values of an ordered type, with `==` as its equality. -/
instance Ty.cmp_trans (t : Ty) : Std.TransCmp (Ty.cmp T t) where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := (compare : Erl → Erl → Ordering))
  isLE_trans := Std.TransCmp.isLE_trans (cmp := (compare : Erl → Erl → Ordering))

theorem Ty.cmp_eq_iff {t : Ty} (h : t.ordered T = true) (x y : t.den0) :
    Ty.cmp T t x y = .eq ↔ (Ty.semWith Dsl.base t).2 x y = true := by
  rw [Ty.erl_iff T t h, Ty.cmp]
  exact Std.LawfulEqCmp.compare_eq_iff_eq

end

section
variable (T : List TypeDecl)

/-- The values in the canonical order. -/
def Ty.sortBy (t : Ty) (xs : List t.den0) : List t.den0 := xs.mergeSort fun a b => (Ty.cmp T t a b).isLE

/-- A table's entries in the canonical order of their keys. -/
def Ty.sortKeys (k v : Ty) (xs : List (k.den0 × v.den0)) : List (k.den0 × v.den0) :=
  xs.mergeSort fun a b => (Ty.cmp T k a.1 b.1).isLE

theorem keysUnique_iff {κ ν : Type} {fk : κ → κ → Bool} {gk : κ → Erl} (hk : ∀ a b, fk a b = true ↔ gk a = gk b)
    (l : List (κ × ν)) : KeysUnique fk l ↔ (l.map fun e => gk e.1).Nodup := by
  unfold KeysUnique List.Nodup
  rw [List.pairwise_map]
  constructor
  · exact fun h => h.imp fun h e => by have := (hk _ _).2 e; simp_all
  · refine fun h => h.imp fun h => ⟨?_, ?_⟩
    · cases e : fk _ _
      · rfl
      · exact absurd ((hk _ _).1 e) h
    · cases e : fk _ _
      · rfl
      · exact absurd ((hk _ _).1 e).symm h

end

section
variable {α : Type}

/-- A list with each value's later repeats under `eq` dropped. -/
def dedupBy (eq : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun ks k => if ks.any (eq k) then ks else ks ++ [k]) []

theorem dedupBy_pairwise (eq : α → α → Bool) (xs : List α) : (dedupBy eq xs).Pairwise fun a b => eq b a = false := by
  suffices ∀ acc : List α, acc.Pairwise (fun a b => eq b a = false) →
      (xs.foldl (fun ks k => if ks.any (eq k) then ks else ks ++ [k]) acc).Pairwise fun a b => eq b a = false from
    this [] List.Pairwise.nil
  induction xs with
  | nil => exact fun _ h => h
  | cons k xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    split
    · exact ih acc h
    · rename_i hany
      refine ih _ (List.pairwise_append.2 ⟨h, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩)
      rw [List.mem_singleton] at hb; subst hb
      simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hany
      exact hany a ha

/-- In a list of distinct values sorted by a total order, the values before `x` are those below it. A step that
starts effects in the canonical order of keys gives each one's request the next wire id plus the number of effects
of the keys below its own. -/
theorem sorted_prefix (cmp : α → α → Ordering) [Std.TransCmp cmp] (xs : List α)
    (hnd : xs.Pairwise fun a b => cmp a b ≠ .eq) {pre post : List α} {x : α}
    (h : xs.mergeSort (fun a b => (cmp a b).isLE) = pre ++ x :: post) :
    pre.Perm (xs.filter fun y => cmp y x == .lt) := by
  have hp := List.mergeSort_perm xs (fun a b => (cmp a b).isLE)
  have hle := List.pairwise_mergeSort (le := fun a b => (cmp a b).isLE)
    (fun _ _ _ h1 h2 => Std.TransCmp.isLE_trans h1 h2)
    (fun a b => by
      cases h : cmp a b with
      | gt => have := Std.OrientedCmp.gt_iff_lt.1 h; simp [this]
      | _ => simp) xs
  have hne := hnd.perm hp.symm (fun h e => h (Std.OrientedCmp.eq_symm e))
  have hlt : (xs.mergeSort fun a b => (cmp a b).isLE).Pairwise fun a b => cmp a b = .lt := by
    refine (hle.and hne).imp fun ⟨h1, h2⟩ => ?_
    cases e : cmp _ _ <;> simp_all
  rw [h] at hlt
  have hsplit : (pre ++ x :: post).filter (fun y => cmp y x == .lt) = pre := by
    obtain ⟨hpre, hxpost, hcross⟩ := List.pairwise_append.1 hlt
    have hx := (List.pairwise_cons.1 hxpost).1
    rw [List.filter_append, List.filter_cons]
    have h1 : pre.filter (fun y => cmp y x == .lt) = pre :=
      List.filter_eq_self.2 fun a ha => by simp [hcross a ha x List.mem_cons_self]
    have h2 : post.filter (fun y => cmp y x == .lt) = [] :=
      List.filter_eq_nil_iff.2 fun b hb => by
        have := Std.OrientedCmp.gt_iff_lt.2 (hx b hb); simp [this]
    simp [h1, h2, Std.ReflCmp.compare_self]
  rw [← hsplit, ← h]
  exact hp.filter _

end

section
variable (T : List TypeDecl)

/-- The keys of a bag of an ordered type, each once, in the canonical order: the keys before `x` are the bag's
distinct keys below it. -/
theorem sortBy_dedup_prefix {t : Ty} (ht : t.ordered T = true) (xs : List t.den0) {pre post : List t.den0} {x : t.den0}
    (h : Ty.sortBy T t (dedupBy (Ty.semWith Dsl.base t).2 xs) = pre ++ x :: post) :
    pre.Perm ((dedupBy (Ty.semWith Dsl.base t).2 xs).filter fun y => Ty.cmp T t y x == .lt) :=
  sorted_prefix (Ty.cmp T t) _ ((dedupBy_pairwise _ xs).imp fun h e =>
    by rw [(Ty.cmp_eq_iff T ht _ _).1 (Std.OrientedCmp.eq_symm e)] at h; cases h) h

end

-- Constructor atoms as gleam 1.19 compiles them, and terms in the order Erlang's `lists:sort` gives (checked with erl).
#guard ["HTTPError", "Ab", "AB", "A1b", "A1B", "ABC", "Abc2Def", "True", "None"].map atomName ==
  ["h_t_t_p_error", "ab", "a_b", "a1b", "a1_b", "a_b_c", "abc2_def", "true", "none"]
#guard Erl.sort ([.atom "h_t_t_p_error", .atom "ab", .atom "a_b", .atom "a1b", .atom "a1_b", .atom "a_b_c",
    .atom "abc2_def", .tuple [.atom "some", .int 1], .tuple [.atom "error", .int 2], .tuple [.atom "ok", .int 1],
    .atom "none", .tuple [.atom "a", .int 1, .int 2], .list [], .list [.int 1], .bin "a", .map [.int 1] [.int 2],
    .int 3, .bin "\u00e9", .bin "z"] : List Erl) ==
  [.int 3, .atom "a1_b", .atom "a1b", .atom "a_b", .atom "a_b_c", .atom "ab", .atom "abc2_def", .atom "h_t_t_p_error",
    .atom "none", .tuple [.atom "error", .int 2], .tuple [.atom "ok", .int 1], .tuple [.atom "some", .int 1],
    .tuple [.atom "a", .int 1, .int 2], .map [.int 1] [.int 2], .list [], .list [.int 1], .bin "a", .bin "z",
    .bin "\u00e9"]
-- None is an atom and Some(1) a tuple, so None comes first; reordering a bag leaves it equal.
#guard Ty.cmp prelude (Ty.option .int) (.inr (.inl ())) (.inl ((1 : Int), ())) == .lt
#guard Ty.cmp prelude (.bag .int) ([2, 1] : List Int) ([1, 2] : List Int) == .eq

end Tazuna.Ir
