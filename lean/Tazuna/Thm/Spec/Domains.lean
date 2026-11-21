import Tazuna.Spec.Domains

/-!
treeOf agrees with Admitted: the tree that treeOf reads admits exactly the values that the declared domains and the
finite types admit, node by node.
-/

namespace Tazuna.Thm.Spec.Domains

open Tazuna.Data Tazuna.Spec.Domains

mutual

theorem Tree.mem_values : (t : Tree) → (v : Value) → (v ∈ t.values ↔ t.Admits v)
  | .listed vs, v => ⟨fun h => .listed h, fun h => by cases h; assumption⟩
  | .union os, v => by
    show v ∈ os.values ↔ _
    rw [Options.mem_values os v]
    exact ⟨.union, fun h => by cases h; assumption⟩
  | .object fs, v => by
    show v ∈ fs.values.map Value.obj ↔ _
    constructor
    · intro h
      obtain ⟨vs, hvs, rfl⟩ := List.mem_map.mp h
      exact .object ((Fields.mem_values fs vs).mp hvs)
    · intro h
      cases h with
      | object hf => exact List.mem_map.mpr ⟨_, (Fields.mem_values fs _).mpr hf, rfl⟩

theorem Options.mem_values : (os : Options) → (v : Value) → (v ∈ os.values ↔ os.Admit v)
  | .nil, v => ⟨fun h => by simp [Options.values] at h, fun h => by cases h⟩
  | .cons t rest, v => by
    show v ∈ t.values ++ rest.values ↔ _
    rw [List.mem_append, Tree.mem_values t v, Options.mem_values rest v]
    constructor
    · rintro (h | h)
      · exact .head h
      · exact .tail h
    · intro h
      cases h with
      | head h => exact .inl h
      | tail h => exact .inr h

theorem Fields.mem_values : (fs : Fields) → (vs : List (String × Value)) → (vs ∈ fs.values ↔ fs.Admit vs)
  | .nil, vs => by
    show vs ∈ [[]] ↔ _
    constructor
    · intro h
      rw [List.mem_singleton.mp h]
      exact .nil
    · intro h
      cases h
      simp
  | .cons name required t rest, vs => by
    show vs ∈ (t.values.flatMap fun v => rest.values.map ((name, v) :: ·)) ++
      (if required then [] else rest.values) ↔ _
    constructor
    · intro h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨v, hv, h⟩ := List.mem_flatMap.mp h
        obtain ⟨ws, hws, rfl⟩ := List.mem_map.mp h
        exact .present ((Tree.mem_values t v).mp hv) ((Fields.mem_values rest ws).mp hws)
      · cases required
        · exact .absent ((Fields.mem_values rest vs).mp h)
        · simp at h
    · intro h
      cases h with
      | present ht hr =>
        exact List.mem_append.mpr (.inl (List.mem_flatMap.mpr
          ⟨_, (Tree.mem_values t _).mpr ht, List.mem_map.mpr ⟨_, (Fields.mem_values rest _).mpr hr, rfl⟩⟩))
      | absent hr => exact List.mem_append.mpr (.inr (by simpa using (Fields.mem_values rest _).mpr hr))

end

theorem options_ok : ∀ {rs : List (Except Undeclared Tree)} {os : Options}, options rs = .ok os →
    ∀ r ∈ rs, ∃ t, r = .ok t
  | [], _, _, r, hr => by simp at hr
  | r₀ :: rest, os, h, r, hr => by
    cases hr₀ : r₀ <;> cases hrest : options rest <;>
      simp only [options, hr₀, hrest, reduceCtorEq, Except.ok.injEq] at h
    rename_i t os'
    cases List.mem_cons.mp hr with
    | inl e => exact ⟨t, by simp_all⟩
    | inr hm => exact options_ok hrest r hm

theorem options_admit : ∀ {rs : List (Except Undeclared Tree)} {os : Options}, options rs = .ok os →
    ∀ v, (os.Admit v ↔ ∃ t, .ok t ∈ rs ∧ t.Admits v)
  | [], os, h, v => by
    simp only [options, Except.ok.injEq] at h
    subst h
    simp only [List.not_mem_nil, false_and, exists_false, iff_false]
    intro ha
    cases ha
  | r₀ :: rest, os, h, v => by
    cases hr₀ : r₀ <;> cases hrest : options rest <;>
      simp only [options, hr₀, hrest, reduceCtorEq, Except.ok.injEq] at h
    rename_i t os'
    subst h
    have ih := options_admit hrest v
    constructor
    · intro ha
      cases ha with
      | head ha => exact ⟨t, List.mem_cons_self, ha⟩
      | tail ha =>
        obtain ⟨t', hm, ha⟩ := ih.mp ha
        exact ⟨t', List.mem_cons_of_mem _ hm, ha⟩
    · rintro ⟨t', hm, ha⟩
      rcases List.mem_cons.mp hm with e | hm
      · cases e; exact .head ha
      · exact .tail (ih.mpr ⟨t', hm, ha⟩)

/-- The options of a mapped list admit what the trees of its elements admit. -/
theorem options_map_admit {α : Type} {xs : List α} {f : α → Except Undeclared Tree} {os : Options}
    {P : α → Value → Prop}
    (h : options (xs.map f) = .ok os) (hf : ∀ x ∈ xs, ∀ t, f x = .ok t → ∀ v, (t.Admits v ↔ P x v)) (v : Value) :
    os.Admit v ↔ ∃ x ∈ xs, P x v := by
  rw [options_admit h v]
  constructor
  · rintro ⟨t, hm, ha⟩
    obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
    exact ⟨x, hx, (hf x hx t e v).mp ha⟩
  · rintro ⟨x, hx, hp⟩
    obtain ⟨t, e⟩ := options_ok h (f x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
    exact ⟨t, e ▸ List.mem_map.mpr ⟨x, hx, rfl⟩, (hf x hx t e v).mpr hp⟩

/-- The fields of a mapped property list admit what FieldsAdmitted states, when each property's tree agrees. -/
theorem fields_admit {β : Type} {declared : List SchemaStep → Option (List Value)} {defs : List (String × Value)}
    {required : List Value} {path : List SchemaStep} {val : β → String × Value} {g : β → Except Undeclared Tree} :
    ∀ {xs : List β} {fs : Fields},
    fields (xs.map fun x => ((val x).1, required.contains (.str (val x).1), g x)) = .ok fs →
    (∀ x ∈ xs, ∀ t, g x = .ok t → ∀ v,
      (t.Admits v ↔ Admitted declared defs (val x).2 (path ++ [.field (val x).1]) v)) →
    ∀ kvs, (fs.Admit kvs ↔ FieldsAdmitted declared defs (xs.map val) required path kvs)
  | [], fs, h, _, kvs => by
    simp only [List.map_nil, fields, Except.ok.injEq] at h
    subst h
    constructor
    · intro ha; cases ha; exact .nil
    · intro ha; cases ha; exact .nil
  | x :: xs, fs, h, hg, kvs => by
    simp only [List.map_cons] at h ⊢
    cases hk : g x <;> cases hrest : fields (xs.map fun x => ((val x).1, required.contains (.str (val x).1), g x)) <;>
      simp only [fields, hk, hrest, reduceCtorEq, Except.ok.injEq] at h
    rename_i t fs'
    subst h
    have ih := fields_admit hrest (fun y hy => hg y (List.mem_cons_of_mem _ hy))
    have hp := hg x List.mem_cons_self t hk
    rcases hx : val x with ⟨k, p⟩
    rw [hx] at hp
    generalize hb : required.contains (.str k) = b
    constructor
    · intro ha
      cases ha with
      | present ht hr => exact .present ((hp _).mp ht) ((ih _).mp hr)
      | absent hr => exact .absent hb ((ih _).mp hr)
    · intro ha
      cases ha with
      | present ht hr => exact .present ((hp _).mpr ht) ((ih _).mpr hr)
      | absent hn hr =>
        rw [hn] at hb
        subst hb
        exact .absent ((ih _).mpr hr)

theorem map_ok {α β : Type} {f : α → β} {r : Except Undeclared α} {b : β} (h : r.map f = .ok b) :
    ∃ a, r = .ok a ∧ b = f a := by
  cases r with
  | error => cases h
  | ok a => exact ⟨a, rfl, by simp [Except.map] at h; exact h.symm⟩

/-- A node of a kind other than the one nodeOf gives, or a declared path where none is declared, admits nothing. -/
macro "other_node" : tactic => `(tactic| first
  | (simp only [*, reduceCtorEq] at *; done)
  | (simp_all only [reduceCtorEq]; done))

/-- The tree that treeOf reads admits exactly what Admitted states. -/
theorem treeOf_admits (declared : List SchemaStep → Option (List Value)) (defs : List (String × Value)) (s : Value)
    (path : List SchemaStep) (t : Tree) (h : treeOf declared defs s path = .ok t) (v : Value) :
    t.Admits v ↔ Admitted declared defs s path v := by
  rw [treeOf] at h
  split at h
  · rename_i vs hd
    cases h
    constructor
    · intro ha
      cases ha
      exact .declared hd ‹_›
    · intro ha
      cases ha with
      | declared hd' hv => rw [hd] at hd'; cases hd'; exact .listed hv
      | _ => other_node
  · rename_i hd
    split at h
    · rename_i name hn
      split at h
      · rename_i d hl
        rw [treeOf_admits declared (without defs name) d path t h v]
        constructor
        · exact .ref hd hn hl
        · intro ha
          cases ha with
          | ref _ hn' hl' ha =>
            rw [hn] at hn'; cases hn'; rw [hl] at hl'; cases hl'; exact ha
          | _ => other_node
      · cases h
    · rename_i os hn
      obtain ⟨os', ho, rfl⟩ := map_ok h
      have hf := options_map_admit (P := fun (x : { x // x ∈ os.zipIdx }) v =>
          Admitted declared defs x.1.1 (path ++ [.option x.1.2]) v) ho
        (fun x _ t' ht' v' => treeOf_admits declared defs x.1.1 (path ++ [.option x.1.2]) t' ht' v') v
      constructor
      · intro ha
        cases ha with
        | union ha =>
          obtain ⟨⟨⟨o, j⟩, hm⟩, -, ha⟩ := hf.mp ha
          exact .option hd hn hm ha
      · intro ha
        cases ha with
        | option _ hn' hm ha =>
          rw [hn] at hn'; cases hn'
          exact .union (hf.mpr ⟨⟨_, hm⟩, List.mem_attach _ _, ha⟩)
        | _ => other_node
    · rename_i ts hn
      obtain ⟨os', ho, rfl⟩ := map_ok h
      have hf := options_map_admit (P := fun (x : Value × Nat) v =>
          (∃ vs, declared (path ++ [.option x.2]) = some vs ∧ v ∈ vs) ∨
          (declared (path ++ [.option x.2]) = none ∧
            ((∃ vs, typed s x.1 = .finite vs ∧ v ∈ vs) ∨
              ∃ ps required kvs, typed s x.1 = .object ps required ∧
                FieldsAdmitted declared defs ps required (path ++ [.option x.2]) kvs ∧ v = .obj kvs))) ho
        (fun ⟨ty, j⟩ _ tr htr v' => by
          simp only at htr
          split at htr
          · rename_i vs hdj
            cases htr
            constructor
            · intro ha; cases ha; exact .inl ⟨vs, hdj, ‹_›⟩
            · rintro (⟨vs', hd', hv⟩ | ⟨hn', -⟩)
              · rw [hdj] at hd'; cases hd'; exact .listed hv
              · rw [hdj] at hn'; cases hn'
          · rename_i hdj
            split at htr
            · rename_i vs hty
              cases htr
              constructor
              · intro ha; cases ha; exact .inr ⟨hdj, .inl ⟨vs, hty, ‹_›⟩⟩
              · rintro (⟨vs', hd', -⟩ | ⟨-, ⟨vs', hty', hv⟩ | ⟨ps, required, kvs, hty', -⟩⟩)
                · rw [hdj] at hd'; cases hd'
                · rw [hty] at hty'; cases hty'; exact .listed hv
                · rw [hty] at hty'; cases hty'
            · rename_i ps required hty
              obtain ⟨fs, hfs, rfl⟩ := map_ok htr
              have hf := fields_admit (val := Subtype.val)
                (g := fun x => treeOf declared defs x.1.2 (path ++ [.option j] ++ [.field x.1.1])) hfs
                (fun x _ t' ht' v'' => treeOf_admits declared defs x.1.2 (path ++ [.option j] ++ [.field x.1.1]) t' ht' v'')
              rw [List.attach_map_subtype_val] at hf
              constructor
              · intro ha
                cases ha with
                | object ha => exact .inr ⟨hdj, .inr ⟨ps, required, _, hty, (hf _).mp ha, rfl⟩⟩
              · rintro (⟨vs', hd', -⟩ | ⟨-, ⟨vs', hty', -⟩ | ⟨ps', required', kvs, hty', hfa, rfl⟩⟩)
                · rw [hdj] at hd'; cases hd'
                · rw [hty] at hty'; cases hty'
                · rw [hty] at hty'; cases hty'; exact .object ((hf _).mpr hfa)
            · cases htr) v
      constructor
      · intro ha
        cases ha with
        | union ha =>
          obtain ⟨⟨ty, j⟩, hm, ⟨vs, hdj, hv⟩ | ⟨hdj, ⟨vs, hty, hv⟩ | ⟨ps, required, kvs, hty, hfa, rfl⟩⟩⟩ := hf.mp ha
          · exact .typeDeclared hd hn hm hdj hv
          · exact .typeFinite hd hn hm hdj hty hv
          · exact .typeObject hd hn hm hdj hty hfa
      · intro ha
        cases ha with
        | typeDeclared _ hn' hm hdj hv =>
          rw [hn] at hn'; cases hn'; exact .union (hf.mpr ⟨_, hm, .inl ⟨_, hdj, hv⟩⟩)
        | typeFinite _ hn' hm hdj hty hv =>
          rw [hn] at hn'; cases hn'; exact .union (hf.mpr ⟨_, hm, .inr ⟨hdj, .inl ⟨_, hty, hv⟩⟩⟩)
        | typeObject _ hn' hm hdj hty hfa =>
          rw [hn] at hn'; cases hn'; exact .union (hf.mpr ⟨_, hm, .inr ⟨hdj, .inr ⟨_, _, _, hty, hfa, rfl⟩⟩⟩)
        | _ => other_node
    · rename_i vs hn
      cases h
      constructor
      · intro ha
        cases ha
        exact .finite hd hn ‹_›
      · intro ha
        cases ha with
        | finite _ hn' hv => rw [hn] at hn'; cases hn'; exact .listed hv
        | _ => other_node
    · rename_i ps required hn
      obtain ⟨fs, hfs, rfl⟩ := map_ok h
      have hf := fields_admit (val := Subtype.val)
        (g := fun x => treeOf declared defs x.1.2 (path ++ [.field x.1.1])) hfs
        (fun x _ t' ht' v' => treeOf_admits declared defs x.1.2 (path ++ [.field x.1.1]) t' ht' v')
      rw [List.attach_map_subtype_val] at hf
      constructor
      · intro ha
        cases ha with
        | object ha => exact .object hd hn ((hf _).mp ha)
      · intro ha
        cases ha with
        | object _ hn' hfa => rw [hn] at hn'; cases hn'; exact .object ((hf _).mpr hfa)
        | _ => other_node
    · cases h
termination_by (defs.length, sizeOf s)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (length_without_lt ‹_›)
    | exact Prod.Lex.right _ (nodeOf_union_lt ‹_› (List.fst_mem_of_mem_zipIdx (Subtype.property _)))
    | exact Prod.Lex.right _ (nodeOf_object_lt ‹_› (Subtype.property _))
    | exact Prod.Lex.right _ (typed_object_lt ‹_› (Subtype.property _))

theorem map_error {α β : Type} {f : α → β} {r : Except Undeclared α} {p : Undeclared} (h : r.map f = .error p) :
    r = .error p := by
  cases r with
  | error q => simpa [Except.map] using h
  | ok => cases h

theorem options_error : ∀ {rs : List (Except Undeclared Tree)} {p : Undeclared}, options rs = .error p →
    (∀ r ∈ rs, ∀ q, r = .error q → q ≠ []) → p ≠ []
  | [], _, h, _ => by simp [options] at h
  | r₀ :: rest, p, h, hr => by
    cases hr₀ : r₀ <;> cases hrest : options rest <;>
      simp only [options, hr₀, hrest, reduceCtorEq, Except.error.injEq] at h <;> subst h
    · intro he; exact hr r₀ List.mem_cons_self _ hr₀ (List.append_eq_nil_iff.mp he).1
    · intro he; exact hr r₀ List.mem_cons_self _ hr₀ (List.append_eq_nil_iff.mp he).1
    · exact options_error hrest fun r hm => hr r (List.mem_cons_of_mem _ hm)

theorem fields_error {β : Type} {f : β → String × Bool × Except Undeclared Tree} :
    ∀ {xs : List β} {p : Undeclared}, fields (xs.map f) = .error p →
    (∀ x ∈ xs, ∀ q, (f x).2.2 = .error q → q ≠ []) → p ≠ []
  | [], _, h, _ => by simp [fields] at h
  | x :: xs, p, h, hr => by
    simp only [List.map_cons] at h
    rcases hx : f x with ⟨k, b, r⟩
    have hx' : (f x).2.2 = r := by rw [hx]
    rw [hx] at h
    cases hr₀ : r <;> cases hrest : fields (xs.map f) <;>
      simp only [fields, hr₀, hrest, reduceCtorEq, Except.error.injEq] at h <;> subst h
    · intro he; exact hr x List.mem_cons_self _ (hx'.trans hr₀) (List.append_eq_nil_iff.mp he).1
    · intro he; exact hr x List.mem_cons_self _ (hx'.trans hr₀) (List.append_eq_nil_iff.mp he).1
    · exact fields_error hrest fun y hm => hr y (List.mem_cons_of_mem _ hm)

/-- An undeclared schema names at least one path. -/
theorem treeOf_error (declared : List SchemaStep → Option (List Value)) (defs : List (String × Value)) (s : Value)
    (path : List SchemaStep) (p : Undeclared) (h : treeOf declared defs s path = .error p) : p ≠ [] := by
  rw [treeOf] at h
  split at h
  · cases h
  · split at h
    · split at h
      · exact treeOf_error declared _ _ path p h
      · cases h; simp
    · refine options_error (map_error h) fun r hm q hq => ?_
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm
      exact treeOf_error declared defs x.1.1 _ q hq
    · refine options_error (map_error h) fun r hm q hq => ?_
      obtain ⟨⟨ty, j⟩, _, rfl⟩ := List.mem_map.mp hm
      simp only at hq
      split at hq
      · cases hq
      · split at hq
        · cases hq
        · exact fields_error (map_error hq) fun x _ q hq => treeOf_error declared defs x.1.2 _ q hq
        · cases hq; simp
    · cases h
    · exact fields_error (map_error h) fun x _ q hq => treeOf_error declared defs x.1.2 _ q hq
    · cases h; simp
termination_by (defs.length, sizeOf s)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (length_without_lt ‹_›)
    | exact Prod.Lex.right _ (nodeOf_union_lt ‹_› (List.fst_mem_of_mem_zipIdx (Subtype.property _)))
    | exact Prod.Lex.right _ (nodeOf_object_lt ‹_› (Subtype.property _))
    | exact Prod.Lex.right _ (typed_object_lt ‹_› (Subtype.property _))

end Tazuna.Thm.Spec.Domains
