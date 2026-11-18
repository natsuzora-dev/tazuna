import Tazuna.Service.State
import Tazuna.Spec.Structure

/-!
The createKey values of a state: each is `<entity>-<n>` for the entity's `n`-th value, qualified by the running service that
creates it, so no two of them are equal.
-/

namespace Tazuna.Thm.Service.Keys

open Tazuna.Service

theorem cons_sep {x y p q : List Char} {c : Char} (hx : c ∉ x) (hy : c ∉ y) (h : x ++ c :: p = y ++ c :: q) :
    x = y ∧ p = q := by
  induction x generalizing y with
  | nil => cases y with
    | nil => simpa using h
    | cons b y =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hy
  | cons a x ih => cases y with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hx
    | cons b y =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih (fun m => hx (List.mem_cons_of_mem _ m)) (fun m => hy (List.mem_cons_of_mem _ m)) h
      exact ⟨by rw [this.1], this.2⟩

theorem dash_not_digit (n : Nat) : '-' ∉ Nat.toDigits 10 n := fun h => by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  revert this; decide

theorem toDigits_inj {a b : Nat} (h : Nat.toDigits 10 a = Nat.toDigits 10 b) : a = b := by
  rw [← Nat.ofDigitChars_ten_toDigits (n := a), h, Nat.ofDigitChars_ten_toDigits]

/-- The text before the entity of a createKey value of `owner`. -/
def keyPrefix : Option String → List Char
  | some owner => owner.toList ++ ['/']
  | none => []

/-- The characters of the `n`-th createKey value of `entity` that `owner` creates. -/
def keyChars (owner : Option String) (entity : String) (n : Nat) : List Char :=
  keyPrefix owner ++ entity.toList ++ '-' :: Nat.toDigits 10 n

theorem keyChars_inj {o : Option String} {e₁ e₂ : String} {n₁ n₂ : Nat} (h : keyChars o e₁ n₁ = keyChars o e₂ n₂) :
    e₁ = e₂ ∧ n₁ = n₂ := by
  have h := congrArg List.reverse h
  simp only [keyChars, List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append] at h
  obtain ⟨h₁, h₂⟩ := cons_sep (by simpa using dash_not_digit n₁) (by simpa using dash_not_digit n₂) h
  exact ⟨String.toList_inj.mp (List.reverse_inj.mp (List.append_cancel_right h₂)),
    toDigits_inj (List.reverse_inj.mp h₁)⟩

theorem length_givenKeys (keys : Keys) (es : List String) : (givenKeys keys es).length = es.length := by
  simp [givenKeys]

/-- The `i`-th value that createKey gives to calls for the entities `es`, with no value before them. -/
theorem givenKeys_getElem (o : Option String) (es : List String) (i : Nat)
    (h : i < ((givenKeys { owner := o } es).map Prod.snd).length) :
    (((givenKeys { owner := o } es).map Prod.snd)[i]).toList =
      keyChars o (es[i]'(by simpa [length_givenKeys] using h))
        (((es.take i).filter (· == es[i]'(by simpa [length_givenKeys] using h))).length + 1) := by
  cases o <;> simp [givenKeys, keyChars, keyPrefix, String.toList_append, Nat.toList_repr, toString]

theorem count_lt {es : List String} {i j : Nat} (hij : i < j) (hj : j < es.length) (he : es[i] = es[j]) :
    ((es.take i).filter (· == es[i])).length < ((es.take j).filter (· == es[j])).length := by
  have hi : i < es.length := Nat.lt_trans hij hj
  have hp : (es.take (i + 1)).filter (· == es[i]) <+: (es.take j).filter (· == es[i]) :=
    (List.take_prefix_take_left hij).filter _
  rw [List.take_add_one, List.getElem?_eq_getElem hi] at hp
  have := hp.length_le
  simp only [Option.toList_some, List.filter_append, List.filter_cons, beq_self_eq_true, ite_true, List.filter_nil,
    List.length_append, List.length_singleton] at this
  rw [← he]
  omega

/-- No two createKey values of a state are equal, whatever it went through. -/
theorem created_distinct (s : State) : (s.created.map (·.2)).Nodup := by
  unfold State.created
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  have h := congrArg String.toList heq
  rw [givenKeys_getElem _ _ _ hi, givenKeys_getElem _ _ _ hj] at h
  obtain ⟨he, hn⟩ := keyChars_inj h
  have := count_lt hij (by simpa [length_givenKeys] using hj) he
  omega

theorem toDigits_head (n : Nat) (h : 0 < n) : (Nat.toDigits 10 n).head? ≠ some '0' := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · simp only [List.head?_cons, ne_eq, Option.some.injEq, Nat.digitChar_eq_zero]; omega
    · rename_i hn
      have hd : 0 < n / 10 := Nat.div_pos (by omega) (by decide)
      obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := n / 10) (b := 10))
      have := ih (n / 10) (Nat.div_lt_self h (by decide)) hd
      rw [hc] at this ⊢
      simpa using this

/-- The `i`-th createKey value and its entity for calls for the entities `es`, with no value before them. -/
theorem givenKeys_getElem_pair (o : Option String) (es : List String) (i : Nat)
    (h : i < (givenKeys { owner := o } es).length) :
    ((givenKeys { owner := o } es)[i]).1 = es[i]'(by simpa [length_givenKeys] using h) ∧
      ((givenKeys { owner := o } es)[i]).2.toList =
        keyChars o (es[i]'(by simpa [length_givenKeys] using h))
          (((es.take i).filter (· == es[i]'(by simpa [length_givenKeys] using h))).length + 1) := by
  cases o <;> simp [givenKeys, keyChars, keyPrefix, String.toList_append, Nat.toList_repr, toString]

/-- Each createKey value of a state is `<owner>/<entity>-<n>`, `n` > 0, for its entity and the state's service. -/
theorem created_form {s : State} {e k : String} (h : (e, k) ∈ s.created) :
    ∃ n, 0 < n ∧ k.toList = keyChars (some s.service) e n := by
  unfold State.created at h
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
  obtain ⟨h₁, h₂⟩ := givenKeys_getElem_pair (some s.service) s.createdEntities i hi
  rw [he] at h₁ h₂
  simp only at h₁ h₂
  exact ⟨_, Nat.succ_pos _, h₁ ▸ h₂⟩

theorem keyChars_isKeyOf (p e : String) (n : Nat) (hn : 0 < n) (k : String)
    (hk : k.toList = keyChars (some p) e n) : Spec.isKeyOf s!"{p}/{e}" k = true := by
  have hh : (s!"{p}/{e}").toList ++ ['-'] = keyPrefix (some p) ++ e.toList ++ ['-'] := by
    simp [keyPrefix, String.toList_append, toString]
  unfold Spec.isKeyOf
  simp only [hh, hk, keyChars]
  have ht : keyPrefix (some p) ++ e.toList ++ '-' :: Nat.toDigits 10 n =
      (keyPrefix (some p) ++ e.toList ++ ['-']) ++ Nat.toDigits 10 n := by simp
  rw [ht, List.take_left', List.drop_left']
  · simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.isEmpty_eq_false_iff, bne_iff_ne, ne_eq]
    refine ⟨⟨Nat.toDigits_ne_nil, ?_⟩, toDigits_head n hn⟩
    exact List.all_eq_true.mpr fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  all_goals rfl

end Tazuna.Thm.Service.Keys
