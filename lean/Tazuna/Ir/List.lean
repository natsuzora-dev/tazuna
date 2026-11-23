namespace Tazuna.Ir

/-- `acc` with `x` at the end, unless `acc` already contains an element `==` to `x`. -/
def addNew {α : Type} [BEq α] (acc : List α) (x : α) : List α := if acc.contains x then acc else acc ++ [x]

def addName {α : Type} [DecidableEq α] (acc : List α) (n : α) : List α := if n ∈ acc then acc else acc ++ [n]

def dedupe {α : Type} [DecidableEq α] (names : List α) : List α := names.foldl addName []

/-- The first element whose key is in `seen` or is the key of an earlier element. -/
def firstDuplicateFrom {α β : Type} [DecidableEq β] (key : α → β) (seen : List β) : List α → Option α
  | [] => none
  | x :: xs => if key x ∈ seen then some x else firstDuplicateFrom key (key x :: seen) xs

def firstDuplicate {α β : Type} [DecidableEq β] (key : α → β) (xs : List α) : Option α := firstDuplicateFrom key [] xs

theorem mapM_ok_map {ε α β γ : Type} (g : α → Except ε β) (p : β → γ) (q : α → γ)
    (hg : ∀ a b, g a = .ok b → p b = q a) : ∀ (l : List α) (l' : List β), l.mapM g = .ok l' → l'.map p = l.map q
  | [], l', h => by simp only [List.mapM_nil] at h; cases h; rfl
  | a :: as, l', h => by
    rw [List.mapM_cons] at h
    cases hb : g a with
    | error e => rw [hb] at h; cases h
    | ok b =>
      cases hs : as.mapM g with
      | error e => rw [hb, hs] at h; cases h
      | ok bs =>
        rw [hb, hs] at h
        cases h
        simp only [List.map_cons, hg a b hb, mapM_ok_map g p q hg as bs hs]

theorem filter_length_le {α : Type} (p q : α → Bool) (hpq : ∀ x, p x = true → q x = true) :
    ∀ l : List α, (l.filter p).length ≤ (l.filter q).length
  | [] => by simp
  | x :: l => by
    have := filter_length_le p q hpq l
    by_cases hp : p x = true
    · simp only [hp, List.filter_cons_of_pos, List.length_cons, hpq x hp, Nat.add_le_add_iff_right, ge_iff_le]; omega
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ite_false]
      split <;> simp only [List.length_cons, ge_iff_le] <;> omega

theorem filter_length_lt {α : Type} (p q : α → Bool) (hpq : ∀ x, p x = true → q x = true) (y : α)
    (hq : q y = true) (hp : p y = false) : ∀ l : List α, y ∈ l → (l.filter p).length < (l.filter q).length
  | [], h => absurd h List.not_mem_nil
  | x :: l, h => by
    rcases List.mem_cons.mp h with e | e
    · subst e
      have := filter_length_le p q hpq l
      simp only [hp, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, hq, List.filter_cons_of_pos,
          List.length_cons, gt_iff_lt]; omega
    · have := filter_length_lt p q hpq y hq hp l e
      by_cases hpx : p x = true
      · simp only [hpx, List.filter_cons_of_pos, List.length_cons, hpq x hpx, Nat.add_lt_add_iff_right, gt_iff_lt]
        omega
      · simp only [List.filter_cons, hpx, Bool.false_eq_true, ite_false]
        split <;> simp only [List.length_cons, gt_iff_lt] <;> omega

def dropKey {β : Type} (l : List (String × β)) (s : String) : List (String × β) := l.filter (·.1 != s)

theorem length_dropKey_lt {β : Type} {l : List (String × β)} {s : String} {b : β} (h : l.lookup s = some b) :
    (dropKey l s).length < l.length := by
  unfold dropKey
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    obtain ⟨a, c⟩ := x
    by_cases e : s = a
    · subst e
      have := List.length_filter_le (fun x : String × β => x.1 != s) xs
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have hb : (s == a) = false := by simpa using e
      simp only [List.lookup_cons, hb] at h
      have hne : (a != s) = true := by simpa using Ne.symm e
      simp only [List.filter_cons, hne, ↓reduceIte, List.length_cons]
      have := ih h
      omega

end Tazuna.Ir
