import Tazuna.Linter

/-! One-step diamonds give every order of the steps one result. A system runs enabled steps one at a time, any enabled
step next, until none is enabled, a step faults, or the fuel runs out. When every two distinct enabled steps close in
one step each, up to an equivalence the steps respect, every run ends in equivalent results or every run faults
(`runs_agree`). This is the diamond lemma of abstract rewriting in its strong, one-step form (Newman 1942, Huet 1980),
which partial-order reduction rests on when it checks that two transitions are independent (both enabled, neither
disables the other, both orders reach the same state).

A fault ends a run where it happens, so which fault a faulting run reports can depend on the order: with one step of
fuel left and two steps enabled, one of them faulting, one order reports that fault and the other runs out of fuel.
The theorem therefore says "equivalent, or both fault", and says nothing about which fault. -/

namespace Tazuna.Ir.Diamond

/-- A system of steps: `len a` steps are enabled at `a`, `pick a i` runs the `i`-th of them, and `limit` is the fault of
running out of fuel. -/
structure Sys (α ε : Type) where
  len : α → Nat
  pick : α → Nat → Except ε α
  limit : ε

variable {α ε : Type} (S : Sys α ε)

/-- The results a run with `fuel` steps can end in, picking any enabled step each time. -/
inductive Runs : Nat → α → Except ε α → Prop
  | done {n : Nat} {a : α} : S.len a = 0 → Runs n a (.ok a)
  | limit {a : α} : S.len a ≠ 0 → Runs 0 a (.error S.limit)
  | fault {n : Nat} {a : α} {i : Nat} {e : ε} : i < S.len a → S.pick a i = .error e → Runs (n + 1) a (.error e)
  | next {n : Nat} {a b : α} {i : Nat} {r : Except ε α} : i < S.len a → S.pick a i = .ok b → Runs n b r →
      Runs (n + 1) a r

/-- Results that are equivalent states, or the same fault. -/
def Lift (E : α → α → Prop) : Except ε α → Except ε α → Prop
  | .ok a, .ok b => E a b
  | .error e, .error e' => e = e'
  | _, _ => False

/-- Whether a result is a fault. -/
def Faults : Except ε α → Prop
  | .error _ => True
  | .ok _ => False

/-- What two runs of a system whose steps commute end in: equivalent results, or a fault each. -/
def Agree (E : α → α → Prop) (x y : Except ε α) : Prop := Lift E x y ∨ (Faults x ∧ Faults y)

/-- An equivalence relation on states. -/
structure Equiv (E : α → α → Prop) : Prop where
  refl : ∀ a, E a a
  symm : ∀ {a b}, E a b → E b a
  trans : ∀ {a b c}, E a b → E b c → E a c

/-- Steps respect `E`: equivalent states enable as many steps, and each step of one has an equivalent step of the
other. -/
def Simulates (E : α → α → Prop) : Prop :=
  ∀ a a', E a a' → S.len a = S.len a' ∧ ∀ i < S.len a, ∃ j < S.len a', Lift E (S.pick a i) (S.pick a' j)

/-- At every state where `I` holds, two distinct enabled steps commute in one step each: when both succeed, each
leaves the other enabled and running it gives equivalent results or the same fault; when the second faults, the first
leaves it enabled and faulting. One order enabled and the other not is not commuting. -/
def Commutes (I : α → Prop) (E : α → α → Prop) : Prop :=
  ∀ a, I a → ∀ i j, i < S.len a → j < S.len a → i ≠ j → ∀ b, S.pick a i = .ok b →
    (∀ c, S.pick a j = .ok c → ∃ j' < S.len b, ∃ i' < S.len c, Lift E (S.pick b j') (S.pick c i')) ∧
    (∀ e, S.pick a j = .error e → ∃ j' < S.len b, Faults (S.pick b j'))

/-- Steps that succeed keep `I`. -/
def Preserved (I : α → Prop) : Prop := ∀ a i b, I a → i < S.len a → S.pick a i = .ok b → I b

/-- The run that always picks the first enabled step. -/
def first : Nat → α → Except ε α
  | n, a => if S.len a = 0 then .ok a else match n with
    | 0 => .error S.limit
    | n + 1 => match S.pick a 0 with
      | .error e => .error e
      | .ok b => first n b

theorem runs_first : (n : Nat) → (a : α) → Runs S n a (first S n a)
  | n, a => by
    unfold first
    by_cases h : S.len a = 0
    · simp only [h, ↓reduceIte]; exact .done h
    · simp only [h, ↓reduceIte]
      have h0 : 0 < S.len a := Nat.pos_of_ne_zero h
      match n with
      | 0 => exact .limit h
      | n + 1 =>
        dsimp only
        split
        · next e he => exact .fault h0 he
        · next b hb => exact .next h0 hb (runs_first n b)

variable {S}

theorem ne0 {i n : Nat} (h : i < n) : n ≠ 0 := by omega

theorem runs_limit {a : α} {r : Except ε α} (h : S.len a ≠ 0) (hr : Runs S 0 a r) : r = .error S.limit := by
  cases hr with
  | done h' => exact absurd h' h
  | limit _ => rfl

theorem runs_sim {E : α → α → Prop} (hS : Simulates S E) {n : Nat} {a : α} {x : Except ε α} (hx : Runs S n a x) :
    ∀ a', E a a' → ∃ x', Runs S n a' x' ∧ Lift E x x' := by
  induction hx with
  | done h => intro a' ha; exact ⟨_, .done ((hS _ _ ha).1 ▸ h), ha⟩
  | limit h => intro a' ha; exact ⟨_, .limit ((hS _ _ ha).1 ▸ h), rfl⟩
  | fault hi he =>
    intro a' ha
    obtain ⟨j, hj, hl⟩ := (hS _ _ ha).2 _ hi
    rw [he] at hl
    revert hl
    cases hp : S.pick a' j with
    | error e' => intro hl; exact ⟨_, .fault hj hp, hl⟩
    | ok _ => intro hl; exact hl.elim
  | next hi hb _ ih =>
    intro a' ha
    obtain ⟨j, hj, hl⟩ := (hS _ _ ha).2 _ hi
    rw [hb] at hl
    revert hl
    cases hp : S.pick a' j with
    | error _ => intro hl; exact hl.elim
    | ok b' =>
      intro hl
      obtain ⟨x', hx', hxx⟩ := ih b' hl
      exact ⟨x', .next hj hp hx', hxx⟩

variable {E : α → α → Prop}

theorem Lift.symm (hE : Equiv E) : {x y : Except ε α} → Lift E x y → Lift E y x
  | .ok _, .ok _, h => hE.symm h
  | .error _, .error _, h => Eq.symm h
  | .ok _, .error _, h => h.elim
  | .error _, .ok _, h => h.elim

theorem Lift.trans (hE : Equiv E) : {x y z : Except ε α} → Lift E x y → Lift E y z → Lift E x z
  | .ok _, .ok _, .ok _, h, h' => hE.trans h h'
  | .error _, .error _, .error _, h, h' => Eq.trans h h'
  | .ok _, .error _, _, h, _ => h.elim
  | .error _, .ok _, _, h, _ => h.elim
  | .ok _, .ok _, .error _, _, h' => h'.elim
  | .error _, .error _, .ok _, _, h' => h'.elim

theorem Lift.faults : {x y : Except ε α} → Lift E x y → Faults x → Faults y
  | .error _, .error _, _, _ => trivial
  | .ok _, _, _, h => h.elim
  | .error _, .ok _, h, _ => h.elim

theorem Agree.symm (hE : Equiv E) {x y : Except ε α} : Agree E x y → Agree E y x
  | .inl h => .inl (h.symm hE)
  | .inr ⟨hx, hy⟩ => .inr ⟨hy, hx⟩

theorem Agree.trans (hE : Equiv E) {x y z : Except ε α} : Agree E x y → Agree E y z → Agree E x z
  | .inl h, .inl h' => .inl (h.trans hE h')
  | .inl h, .inr ⟨hy, hz⟩ => .inr ⟨(h.symm hE).faults hy, hz⟩
  | .inr ⟨hx, hy⟩, .inl h' => .inr ⟨hx, h'.faults hy⟩
  | .inr ⟨hx, _⟩, .inr ⟨_, hz⟩ => .inr ⟨hx, hz⟩

theorem Agree.faults (hE : Equiv E) {x y : Except ε α} (h : Agree E x y) (hy : Faults y) : Faults x := by
  rcases h with h | ⟨hx, _⟩
  · exact (h.symm hE).faults hy
  · exact hx

/-- Every two runs of a system whose distinct enabled steps commute in one step agree. -/
theorem runs_agree {I : α → Prop} (hE : Equiv E) (hS : Simulates S E) (hD : Commutes S I E) (hI : Preserved S I) :
    (n : Nat) → (a : α) → I a → {r r' : Except ε α} → Runs S n a r → Runs S n a r' → Agree E r r' := by
  intro n
  induction n with
  | zero =>
    intro a _ r r' hr hr'
    cases hr with
    | done h => cases hr' with
      | done _ => exact .inl (hE.refl a)
      | limit h' => exact absurd h h'
    | limit h => cases hr' with
      | done h' => exact absurd h' h
      | limit _ => exact .inl rfl
  | succ n ih =>
    intro a ha r r' hr hr'
    -- From a state where `I` holds and the step `j` faults, every run faults.
    have faulty : ∀ b, I b → ∀ j < S.len b, Faults (S.pick b j) → ∀ {r}, Runs S n b r → Faults r := by
      intro b hb j hj hf r hr
      cases n with
      | zero => rw [runs_limit (ne0 hj) hr]; trivial
      | succ m =>
        revert hf
        cases hp : S.pick b j with
        | ok _ => intro hf; exact hf.elim
        | error e => intro _; exact (ih b hb hr (.fault hj hp)).faults hE trivial
    -- One order succeeds with `b` and the other faults: both runs fault.
    have mixed : ∀ i j b e, i < S.len a → j < S.len a → i ≠ j → S.pick a i = .ok b → S.pick a j = .error e → I a →
        ∀ {r}, Runs S n b r → Faults r := by
      intro i j b e hi hj hij hb he ha r hr
      obtain ⟨j', hj', hf⟩ := (hD a ha i j hi hj hij b hb).2 e he
      exact faulty b (hI a i b ha hi hb) j' hj' hf hr
    cases hr with
    | done h => cases hr' with
      | done _ => exact .inl (hE.refl a)
      | fault hj _ => exact absurd h (ne0 hj)
      | next hj _ _ => exact absurd h (ne0 hj)
    | @fault _ _ i e hi he => cases hr' with
      | done h => exact absurd h (ne0 hi)
      | fault _ _ => exact .inr ⟨trivial, trivial⟩
      | @next _ _ b j _ hj hb hrb =>
        have hij : j ≠ i := fun h => by subst h; rw [he] at hb; cases hb
        exact .inr ⟨trivial, mixed j i b e hj hi hij hb he ha hrb⟩
    | @next _ _ b i _ hi hb hrb =>
      cases hr' with
      | done h => exact absurd h (ne0 hi)
      | @fault _ _ j e hj he =>
        have hij : i ≠ j := fun h => by subst h; rw [he] at hb; cases hb
        exact .inr ⟨mixed i j b e hi hj hij hb he ha hrb, trivial⟩
      | @next _ _ c j _ hj hc hrc =>
        by_cases hij : i = j
        · subst hij
          rw [hb] at hc
          cases hc
          exact ih b (hI a i b ha hi hb) hrb hrc
        obtain ⟨j', hj', i', hi', hl⟩ := (hD a ha i j hi hj hij b hb).1 c hc
        have hIb := hI a i b ha hi hb
        have hIc := hI a j c ha hj hc
        cases n with
        | zero =>
          rw [runs_limit (ne0 hj') hrb, runs_limit (ne0 hi') hrc]
          exact .inl rfl
        | succ m =>
          revert hl
          cases hpb : S.pick b j' with
          | error e =>
            cases hpc : S.pick c i' with
            | ok _ => intro hl; exact hl.elim
            | error e' =>
              intro hl
              have h1 := ih b hIb hrb (.fault hj' hpb)
              have h2 := ih c hIc (.fault hi' hpc) hrc
              exact h1.trans hE ((Agree.trans hE (.inl hl) h2))
          | ok d =>
            cases hpc : S.pick c i' with
            | error _ => intro hl; exact hl.elim
            | ok d' =>
              intro hl
              have hx := runs_first S m d
              obtain ⟨x', hx', hxx⟩ := runs_sim hS hx d' hl
              have h1 := ih b hIb hrb (.next hj' hpb hx)
              have h2 := ih c hIc (.next hi' hpc hx') hrc
              exact h1.trans hE ((Agree.trans hE (.inl hxx) h2))

end Tazuna.Ir.Diamond
