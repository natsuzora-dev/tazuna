import Tazuna.Thm.Verify.Complete.Lists

/-!
Each implementation subscription that `explain.subscribed` records for a snapshot subscription was paired with an alike
snapshot subscription.
-/

namespace Tazuna.Thm.Verify.Complete.Subscriptions

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Complete.Lists

theorem lookup_setAt {β : Type} : ∀ (m : List (String × β)) (k k' : String) (v : β),
    (setAt m k v).lookup k' = if k' = k then some v else m.lookup k'
  | [], k, k', v => by by_cases h : k' = k <;> simp [setAt, h]
  | (a, b) :: rest, k, k', v => by
    by_cases e : a = k
    · subst e
      by_cases h : k' = a
      · simp [setAt, h]
      · have : (k' == a) = false := by simpa using h
        simp [setAt, h, List.lookup_cons, this]
    · have : (a == k) = false := by simpa using e
      simp only [setAt, this, Bool.false_eq_true, ite_false, List.lookup_cons]
      rw [lookup_setAt rest k k' v]
      by_cases h : k' = a
      · subst h; simp [e]
      · have : (k' == a) = false := by simpa using h
        simp [this]

theorem subscribed_foldl (sc : Scope) (pairs : List (String × String)) (G : String → String → Prop)
    (hp : ∀ s other t a b, (other, t) ∈ pairs → sc.openSnapshot.lookup s = some a →
      sc.openSnapshot.lookup other = some b → alike a.out.line b.out.line = true → G s t) :
    ∀ (rest : List (String × String)) (known : List (String × List String)),
      (∀ s ids, known.lookup s = some ids → ∀ t ∈ ids, G s t) → (∀ q ∈ rest, q ∈ pairs) →
      ∀ s ids, (rest.foldl (init := known) fun all (s, _) =>
        let lineOf (s : String) : Option Line := (sc.openSnapshot.lookup s).map (·.out.line)
        let ids := pairs.foldl (init := (all.lookup s).getD []) fun ids (other, t) =>
          match lineOf s, lineOf other with
          | some a, some b => if alike a b && !ids.contains t then ids ++ [t] else ids
          | _, _ => ids
        setAt all s ids).lookup s = some ids → ∀ t ∈ ids, G s t
  | [], known, hk, _ => hk
  | (s₀, x) :: rest, known, hk, hr => by
    simp only [List.foldl_cons]
    refine subscribed_foldl sc pairs G hp rest _ ?_ (fun q hq => hr q (List.mem_cons_of_mem _ hq))
    intro s ids hl t ht
    rw [lookup_setAt] at hl
    split at hl
    · rename_i e
      subst e
      simp only [Option.some.injEq] at hl
      subst hl
      have inner : ∀ (L : List (String × String)) (acc : List String), (∀ t ∈ acc, G s t) → (∀ q ∈ L, q ∈ pairs) →
          ∀ t ∈ L.foldl (init := acc) (fun ids (other, t) =>
            match (sc.openSnapshot.lookup s).map (·.out.line), (sc.openSnapshot.lookup other).map (·.out.line) with
            | some a, some b => if alike a b && !ids.contains t then ids ++ [t] else ids
            | _, _ => ids), G s t := by
        intro L
        induction L with
        | nil => intro acc ha _; exact ha
        | cons q L ih =>
          intro acc ha hq
          obtain ⟨other, t'⟩ := q
          simp only [List.foldl_cons]
          refine ih _ ?_ (fun q h => hq q (List.mem_cons_of_mem _ h))
          split
          · rename_i a b hsa hob
            split
            · intro t'' ht''
              rcases List.mem_append.mp ht'' with h | h
              · exact ha t'' h
              · simp only [List.mem_singleton] at h
                subst h
                rename_i hc
                obtain ⟨sa, hsa', rfl⟩ := Option.map_eq_some_iff.mp hsa
                obtain ⟨sb, hob', rfl⟩ := Option.map_eq_some_iff.mp hob
                simp only [Bool.and_eq_true] at hc
                exact hp s other t'' sa sb (hq _ List.mem_cons_self) hsa' hob' hc.1
            · exact ha
          · exact ha
      exact inner pairs _ (fun t ht => by
        cases hk' : known.lookup s with
        | none => simp [hk'] at ht
        | some l => rw [hk'] at ht; exact hk s l hk' t ht) (fun q h => h) t ht
    · exact hk s ids hl t ht


theorem subscribed_inv (sc : Scope) (pairs : List (String × String)) (G : String → String → Prop)
    (known : List (String × List String)) (hk : ∀ s ids, known.lookup s = some ids → ∀ t ∈ ids, G s t)
    (hp : ∀ s other t a b, (other, t) ∈ pairs → sc.openSnapshot.lookup s = some a →
      sc.openSnapshot.lookup other = some b → alike a.out.line b.out.line = true → G s t) :
    ∀ s ids, (explain.subscribed sc known pairs).lookup s = some ids → ∀ t ∈ ids, G s t :=
  subscribed_foldl sc pairs G hp pairs known hk (fun _ h => h)

end Tazuna.Thm.Verify.Complete.Subscriptions
