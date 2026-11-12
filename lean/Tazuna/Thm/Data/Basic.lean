namespace Tazuna.Thm.Data.Basic

@[simp] theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

@[simp] theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl

@[simp] theorem id_ok_inj {ε α : Type} {a b : α} : @Eq (Id (Except ε α)) (.ok a) (.ok b) ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩

theorem foldlM_id {α β : Type} (f : β → α → Id β) (init : β) (xs : List α) :
    xs.foldlM f init = xs.foldl f init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => exact ih (f init x)

theorem mapM_id {α β : Type} (f : α → Id β) (xs : List α) : xs.mapM f = xs.map fun x => (f x).run := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.mapM_cons, ih]; rfl

theorem mem_foldl_of_mem {α : Type} (g : List String → α → List String) (hg : ∀ acc a x, x ∈ acc → x ∈ g acc a)
    (l : List α) {acc : List String} {x : String} (h : x ∈ acc) : x ∈ l.foldl g acc := by
  induction l generalizing acc with
  | nil => exact h
  | cons a l ih => exact ih (hg acc a x h)

theorem getElem?_append_left' {l₁ l₂ : List String} {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂)[i]? = l₁[i]? := List.getElem?_append_left h

theorem foldlM_error {α ε β : Type} (f : Except ε β → α → Id (Except ε β)) (hf : ∀ v x, f (.error v) x = .error v)
    (es : List α) (v : ε) : es.foldlM f (.error v) = .error v := by
  induction es with
  | nil => rfl
  | cons x xs ih => simp only [List.foldlM_cons, id_bind, hf, ih]

theorem foldl_keeps {α β : Type} (P : β → Prop) (f : β → α → β) (h : ∀ b x, P b → P (f b x)) :
    ∀ (xs : List α) (b : β), P b → P (xs.foldl f b) := by
  intro xs
  induction xs with
  | nil => intro b hb; exact hb
  | cons x xs ih => intro b hb; exact ih _ (h b x hb)

theorem mem_zipIdx_of_mem {α : Type} {x : α} {l : List α} (h : x ∈ l) : ∃ i, (x, i) ∈ l.zipIdx := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  exact ⟨i, List.mem_zipIdx_iff_getElem?.mpr hi⟩

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} (h : x >>= f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mem_mapM_ok {ε α β : Type} {f : α → Except ε β} {l : List α} {out : List β} (h : l.mapM f = .ok out)
    {x : β} (hx : x ∈ out) : ∃ a ∈ l, f a = .ok x := by
  induction l generalizing out with
  | nil => cases h; cases hx
  | cons a l ih =>
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := except_bind_ok h
    obtain ⟨bs, hbs, h⟩ := except_bind_ok h
    cases h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨a', ha', hf⟩ := ih hbs hx
      exact ⟨a', List.mem_cons_of_mem _ ha', hf⟩

theorem exists_zip_of_mem_right {α β : Type} {l₁ : List α} {l₂ : List β} (hl : l₂.length = l₁.length) {y : β}
    (hy : y ∈ l₂) : ∃ x, (x, y) ∈ l₁.zip l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with
    | nil => cases hy
    | cons => cases hl
  | cons a l₁ ih =>
    cases l₂ with
    | nil => cases hy
    | cons b l₂ =>
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨a, List.mem_cons_self⟩
      · obtain ⟨x, hx⟩ := ih (Nat.succ.inj hl) hy
        exact ⟨x, List.mem_cons_of_mem _ hx⟩

end Tazuna.Thm.Data.Basic
