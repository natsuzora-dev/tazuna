namespace Tazuna.Thm.Semantics.Value.Basic

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

theorem foldl_keeps {α β : Type} (P : β → Prop) (f : β → α → β) (h : ∀ b x, P b → P (f b x)) :
    ∀ (xs : List α) (b : β), P b → P (xs.foldl f b) := by
  intro xs
  induction xs with
  | nil => intro b hb; exact hb
  | cons x xs ih => intro b hb; exact ih _ (h b x hb)

theorem foldl_bind_error {α β ε : Type} (g : β → α → Except ε β) (e : ε) :
    ∀ (l : List α), l.foldl (fun (acc : Except ε β) x => acc.bind fun a => g a x) (.error e) = .error e
  | [] => rfl
  | _ :: l => foldl_bind_error g e l

theorem foldl_bind_inv {α β ε : Type} (g : β → α → Except ε β) (I : List α → List α → β → Prop)
    (hstep : ∀ pre x rest a a', I pre (x :: rest) a → g a x = .ok a' → I (pre ++ [x]) rest a') :
    ∀ (rest pre : List α) (a a' : β), I pre rest a →
      rest.foldl (fun (acc : Except ε β) x => acc.bind fun a => g a x) (.ok a) = .ok a' → I (pre ++ rest) [] a'
  | [], pre, a, a', hi, h => by cases h; simpa using hi
  | x :: rest, pre, a, a', hi, h => by
    simp only [List.foldl_cons] at h
    cases hg : g a x with
    | error e =>
      rw [show (Except.ok a : Except ε β).bind (fun a => g a x) = g a x from rfl, hg, foldl_bind_error] at h
      cases h
    | ok a₁ =>
      rw [show (Except.ok a : Except ε β).bind (fun a => g a x) = g a x from rfl, hg] at h
      simpa using foldl_bind_inv g I hstep rest (pre ++ [x]) a₁ a' (hstep pre x rest a a₁ hi hg) h

end Tazuna.Thm.Semantics.Value.Basic
