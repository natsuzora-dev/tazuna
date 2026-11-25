/-! `Forall2` and its lemmas. Core Lean has no `List.Forall₂`. -/

namespace Tazuna.Smt

section
variable {α α' β β' γ δ ε : Type}

/-- `R` relates the lists item by item. -/
def Forall2 (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Forall2 R as bs
  | _, _ => False

theorem forall2_length {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs →
    as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => congrArg (· + 1) (forall2_length h)

theorem forall2_imp {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b) :
    {as : List α} → {bs : List β} → Forall2 R as bs → Forall2 R' as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hab, hs⟩ => ⟨h _ _ hab, forall2_imp h hs⟩

theorem forall2_flip {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs →
    Forall2 (fun b a => R a b) bs as
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨h, forall2_flip hs⟩

theorem forall2_map {R : α → β → Prop} {R' : α' → β → Prop} (f : α → α') (hf : ∀ a b, R a b → R' (f a) b) :
    {as : List α} → {bs : List β} → Forall2 R as bs → Forall2 R' (as.map f) bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨hf _ _ h, forall2_map f hf hs⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem forall2_map_right {R : α → β → Prop} {R' : α → β' → Prop} (f : β → β')
    (hf : ∀ a b, R a b → R' a (f b)) : {as : List α} → {bs : List β} → Forall2 R as bs → Forall2 R' as (bs.map f)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨hf _ _ h, forall2_map_right f hf hs⟩

theorem forall2_map_eq {R : α → β → Prop} (f : α → γ) (g : β → γ) (h : ∀ a b, R a b → f a = g b) :
    {as : List α} → {bs : List β} → Forall2 R as bs → as.map f = bs.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨hab, hs⟩ => by simp only [List.map_cons, h _ _ hab, forall2_map_eq f g h hs]

theorem forall2_map_self {R : α → β → Prop} (f : α → β) : (l : List α) → (∀ a ∈ l, R a (f a)) →
    Forall2 R l (l.map f)
  | [], _ => trivial
  | a :: l, h => ⟨h a (by simp), forall2_map_self f l fun b hb => h b (by simp [hb])⟩

theorem forall2_snd {R : α → β × γ → Prop} : {as : List α} → {bs : List (β × γ)} → Forall2 R as bs →
    Forall2 (fun a c => ∃ b, R a (b, c)) as (bs.map (·.2))
  | [], [], _ => trivial
  | _ :: _, (b, _) :: _, ⟨h, hs⟩ => ⟨⟨b, h⟩, forall2_snd hs⟩

theorem forall2_of_pairs {R : α → β → Prop} : (ps : List (α × β)) → (∀ p ∈ ps, R p.1 p.2) →
    Forall2 R (ps.map (·.1)) (ps.map (·.2))
  | [], _ => trivial
  | p :: ps, h => ⟨h p (by simp), forall2_of_pairs ps fun q hq => h q (by simp [hq])⟩

theorem forall2_zip {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs →
    ∀ p ∈ as.zip bs, R p.1 p.2
  | [], [], _, _, hp => by simp at hp
  | _ :: _, _ :: _, ⟨h, hs⟩, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h
    · exact forall2_zip hs p hp

theorem forall2_zip_left {R : α × β → γ × δ → Prop} : {as : List α} → {bs : List β} →
    {cs : List (γ × δ)} → as.length ≤ bs.length → Forall2 R (as.zip bs) cs →
    Forall2 (fun a d => ∃ b q, R (a, b) q ∧ d = q.2) as (cs.map (·.2))
  | [], _, [], _, _ => trivial
  | a :: as, b :: bs, q :: cs, hl, ⟨h, hs⟩ =>
    ⟨⟨b, q, h, rfl⟩, forall2_zip_left (by simp at hl; omega) hs⟩
  | _ :: _, [], _, hl, _ => by simp at hl
  | [], _, _ :: _, _, h => by cases ‹List _› <;> exact h.elim
  | _ :: _, _ :: _, [], _, h => h.elim

theorem forall2_zipIdx_length {R : α × Nat → β → Prop} (xs : List α) (n0 : Nat) {ps : List β}
    (h : Forall2 R (xs.zipIdx n0) ps) : ps.length = xs.length := by
  rw [← forall2_length h, List.length_zipIdx]

/-- Sorting two related lists by orders that agree on related items keeps them related. -/
theorem forall2_mergeSort {R : α → β → Prop} {le : α → α → Bool} {le' : β → β → Bool} {as : List α} {bs : List β}
    (h : Forall2 R as bs) (hle : ∀ a b a' b', R a a' → R b b' → le a b = le' a' b') :
    Forall2 R (as.mergeSort le) (bs.mergeSort le') := by
  have hl := forall2_length h
  have hz := forall2_zip h
  let P := as.zip bs
  have h1 : (P.mergeSort fun p q => le p.1 q.1).map (·.1) = as.mergeSort le := by
    rw [List.map_mergeSort (s := le) (fun _ _ _ _ => rfl)]
    simp [P, List.map_fst_zip, hl]
  have h2 : (P.mergeSort fun p q => le p.1 q.1).map (·.2) = bs.mergeSort le' := by
    rw [List.map_mergeSort (s := le') (fun p hp q hq => hle _ _ _ _ (hz p hp) (hz q hq))]
    simp [List.map_snd_zip, hl]
  rw [← h1, ← h2]
  exact forall2_of_pairs _ fun p hp => hz p ((List.mem_mergeSort).1 hp)

theorem forall2_flatMap {R : α → β → Prop} {f : α → List γ} {g : β → List γ} (hfg : ∀ a b, R a b → f a = g b) :
    {as : List α} → {bs : List β} → Forall2 R as bs → as.flatMap f = bs.flatMap g
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h, hs⟩ => by simp only [List.flatMap_cons]; rw [hfg _ _ h, forall2_flatMap hfg hs]

theorem forall2_append {R : α → β → Prop} : {a a' : List α} → {b b' : List β} → Forall2 R a b →
    Forall2 R a' b' → Forall2 R (a ++ a') (b ++ b')
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, ⟨h1, h2⟩, h => ⟨h1, forall2_append h2 h⟩

theorem forall2_append_one {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    {as : List α} → {bs : List β} → Forall2 R as bs → Forall2 R (as ++ [a]) (bs ++ [b])
  | [], [], _ => ⟨hab, trivial⟩
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨h, forall2_append_one hab hs⟩

theorem forall2_split {R : α → β → Prop} : (as as' : List α) → {bs : List β} →
    Forall2 R (as ++ as') bs →
    ∃ bs1 bs2, bs = bs1 ++ bs2 ∧ Forall2 R as bs1 ∧ Forall2 R as' bs2
  | [], _, bs, h => ⟨[], bs, rfl, trivial, h⟩
  | _ :: as, as', b :: bs, ⟨h1, h2⟩ => by
    obtain ⟨bs1, bs2, rfl, h3, h4⟩ := forall2_split as as' h2
    exact ⟨b :: bs1, bs2, rfl, ⟨h1, h3⟩, h4⟩
  | _ :: _, _, [], h => h.elim

theorem forall2_getElem? {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs →
    {i : Nat} → {a : α} → as[i]? = some a → ∃ b, bs[i]? = some b ∧ R a b
  | [], [], _, _, _, h => by cases h
  | _ :: _, _ :: _, ⟨hab, _⟩, 0, _, h => by cases h; exact ⟨_, rfl, hab⟩
  | _ :: _, _ :: _, ⟨_, hs⟩, i + 1, _, h => forall2_getElem? hs (i := i) (by simpa using h)

theorem forall2_mem_left {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs → ∀ a ∈ as,
    ∃ b ∈ bs, R a b
  | [], [], _, _, ha => by simp at ha
  | a :: as, b :: bs, ⟨h, hs⟩, a', ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, by simp, h⟩
    · obtain ⟨b', hb', h'⟩ := forall2_mem_left hs a' ha; exact ⟨b', by simp [hb'], h'⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

theorem forall2_mem_right {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs → ∀ b ∈ bs,
    ∃ a ∈ as, R a b
  | [], [], _, _, hb => by simp at hb
  | a :: as, b :: bs, ⟨h, hs⟩, b', hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, by simp, h⟩
    · obtain ⟨a', ha', h'⟩ := forall2_mem_right hs b' hb; exact ⟨a', by simp [ha'], h'⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

theorem forall2_all {E : α → β → Prop} {P : α → Prop} {R : β → Prop} (hPR : ∀ a b, E a b → (P a ↔ R b)) :
    (as : List α) → (bs : List β) → Forall2 E as bs → ((∀ a ∈ as, P a) ↔ ∀ b ∈ bs, R b)
  | [], [], _ => by simp
  | a :: as, b :: bs, ⟨hab, h⟩ => by simp only [List.mem_cons, forall_eq_or_imp, hPR a b hab, forall2_all hPR as bs h]
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- Forall2 survives reordering the right list, with the left list reordered alike. -/
theorem forall2_perm {R : α → β → Prop} {bs bs' : List β} (hp : bs.Perm bs') :
    ∀ {as : List α}, Forall2 R as bs → ∃ as', as'.Perm as ∧ Forall2 R as' bs' := by
  induction hp with
  | nil => intro as h; exact ⟨as, List.Perm.refl _, h⟩
  | cons b _ ih =>
    intro as h
    match as, h with
    | a :: as, ⟨hab, h⟩ =>
      obtain ⟨as', hp', h'⟩ := ih h
      exact ⟨a :: as', hp'.cons a, hab, h'⟩
  | swap b c l =>
    intro as h
    match as, h with
    | a1 :: a2 :: as, ⟨h1, h2, h⟩ => exact ⟨a2 :: a1 :: as, List.Perm.swap a1 a2 as, h2, h1, h⟩
  | trans _ _ ih1 ih2 =>
    intro as h
    obtain ⟨as1, hp1, h1⟩ := ih1 h
    obtain ⟨as2, hp2, h2⟩ := ih2 h1
    exact ⟨as2, hp2.trans hp1, h2⟩

theorem mapM_ok (g : α → Except ε β) : (xs : List α) → (ys : List β) → xs.mapM g = .ok ys →
    Forall2 (fun x y => g x = .ok y) xs ys
  | [], ys, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; trivial
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : g x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok y =>
      cases hxs : xs.mapM g with
      | error e => simp [hx, hxs, bind, Except.bind] at h
      | ok ys' =>
        simp [hx, hxs, bind, Except.bind, pure, Except.pure] at h
        subst h
        exact ⟨hx, mapM_ok g xs ys' hxs⟩

theorem forall2_mapM_map (g : α → Except ε γ) (p : γ → δ) {S : List α} {outs : List γ}
    (h : S.mapM g = .ok outs) : Forall2 (fun sl r => ∃ o, g sl = .ok o ∧ r = p o) S (outs.map p) :=
  go (mapM_ok g S outs h)
where
  go : {S : List α} → {outs : List γ} → Forall2 (fun x y => g x = .ok y) S outs →
      Forall2 (fun sl r => ∃ o, g sl = .ok o ∧ r = p o) S (outs.map p)
    | [], [], _ => trivial
    | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨⟨_, h, rfl⟩, go hs⟩
    | [], _ :: _, h | _ :: _, [], h => h.elim

end

end Tazuna.Smt
