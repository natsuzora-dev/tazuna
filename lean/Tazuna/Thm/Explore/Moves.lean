import Tazuna.Explore.Moves
import Tazuna.Thm.Spec.Domains
import Tazuna.Thm.Guarantee

/-!
The enumeration of moves: a move is enumerated exactly when it fills a slot that the world enables with values that the
declared domains and the finite types admit.
-/

namespace Tazuna.Thm.Explore.Moves

open Tazuna.Data Tazuna.Spec.Domains Tazuna.Service Tazuna.Sim Tazuna.Scenario Tazuna.Explore

theorem slots_enabled (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) (e : Enabled) (s : Slot)
    (h : s ∈ slots spec st x w e) : s.Enabled spec st x w e := by
  simp only [slots, List.mem_append, List.mem_filterMap, List.mem_map, List.mem_singleton] at h
  rcases h with (((((h | h) | h) | h) | h) | h) | h
  · obtain ⟨a, ha, hs⟩ := h
    split at hs
    · cases hs
    · rename_i hend
      obtain ⟨msg, hfind, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact ⟨ha, hfind, by simpa using hend⟩
  · obtain ⟨t, ht, rfl⟩ := h
    exact ht
  · obtain ⟨o, ho, rfl⟩ := h
    exact ho
  · obtain ⟨⟨l, i⟩, hl, hs⟩ := h
    split at hs
    · cases hs
      exact ⟨l, hl, by assumption⟩
    · cases hs
  · obtain ⟨d, hd, hs⟩ := h
    split at hs
    · cases hs
    · rename_i hown
      split at hs <;> cases hs
      · exact ⟨d, hd, rfl, by simpa using hown, .inl ⟨⟨_, by assumption⟩, rfl⟩⟩
      · exact ⟨d, hd, rfl, by simpa using hown, .inr ⟨⟨_, by assumption⟩, rfl⟩⟩
  · obtain ⟨d, hd, hs⟩ := h
    split at hs
    · split at hs
      · cases hs
        rename_i hc
        simp only [Bool.and_eq_true] at hc
        exact ⟨d, hd, rfl, rfl, ⟨_, by assumption⟩, hc.1, hc.2⟩
      · cases hs
    · cases hs
  · subst h
    trivial

@[guarantee] theorem slots_complete (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) (e : Enabled) (s : Slot)
    (h : s.Enabled spec st x w e) : s ∈ slots spec st x w e := by
  simp only [slots, List.mem_append, List.mem_filterMap, List.mem_map, List.mem_singleton]
  cases s with
  | answer a msg =>
    obtain ⟨ha, hfind, hend⟩ := h
    refine .inl (.inl (.inl (.inl (.inl (.inl ⟨a, ha, ?_⟩)))))
    simp [hend, hfind]
  | «at» t => exact .inl (.inl (.inl (.inl (.inl (.inr ⟨t, h, rfl⟩)))))
  | operate o => exact .inl (.inl (.inl (.inl (.inr ⟨o, h, rfl⟩))))
  | unsubscribe i =>
    obtain ⟨l, hl, ho⟩ := h
    exact .inl (.inl (.inl (.inr ⟨(l, i), hl, by simp [ho]⟩)))
  | request r query =>
    obtain ⟨d, hd, rfl, hown, hbody⟩ := h
    refine .inl (.inl (.inr ⟨d, hd, ?_⟩))
    rcases hbody with ⟨⟨c, hc⟩, rfl⟩ | ⟨⟨q, hq⟩, rfl⟩ <;> simp [*]
  | emit peer event =>
    obtain ⟨d, hd, rfl, rfl, ⟨b, hb⟩, hext, hrec⟩ := h
    exact .inl (.inr ⟨d, hd, by simpa [hb] using And.intro hext hrec⟩)
  | restart => exact .inr rfl

/-- The values of the tree that fill enumerates for `schema` are those that Explored.Admits states. -/
theorem tree_mem (st : Service) (x : Explored) (schema : Schema) (v : Value) :
    v ∈ (Id.run (x.tree st schema)).values ↔ x.Admits st schema v := by
  unfold Explored.tree Explored.Admits
  cases hj : st.schemaOf schema with
  | none =>
    constructor
    · intro h; cases h
    · rintro ⟨_, _, hj', -⟩; cases hj'
  | some json =>
    cases ht : rootTree (domainOf x.domains schema) json with
    | error paths =>
      simp only [ht]
      constructor
      · intro h; cases h
      · rintro ⟨_, _, hj', ht', -⟩; cases hj'; rw [ht] at ht'; cases ht'
    | ok t =>
      simp only [ht]
      rw [Thm.Spec.Domains.Tree.mem_values]
      show t.Admits v ↔ _
      rw [Thm.Spec.Domains.treeOf_admits _ _ _ _ t ht v]
      constructor
      · exact fun ha => ⟨json, t, rfl, ht, ha⟩
      · rintro ⟨_, _, hj', -, ha⟩; cases hj'; exact ha

theorem mapM_id {α β : Type} (f : α → Id β) : ∀ xs : List α, Id.run (xs.mapM f) = xs.map fun a => Id.run (f a)
  | [] => rfl
  | x :: xs => by
    rw [List.mapM_cons, List.map_cons, ← mapM_id f xs]
    rfl

theorem fill_iff (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) (s : Slot) (mv : Move) :
    mv ∈ Id.run (fill spec st x w s) ↔ s.Fills spec st x w mv := by
  cases s with
  | answer a msg =>
    simp only [fill, Slot.Fills, Id.run_bind]
    generalize Id.run (targetOf st { service := a.target, name := a.name }) = shape
    generalize Id.run (requestOf msg) = request
    obtain ⟨query, output⟩ := shape
    let move := fun answer => answerMove msg.receiver request answer (msg.status == .inFlight) x.lines.length
    let kinds := spec.rejectionKinds x.own { service := a.target, name := a.name }
    let reasons := spec.rejectionReasons { service := a.target, name := a.name }
    let tree := Id.run (x.tree st (.output { service := a.target, name := a.name }))
    cases output with
    | none =>
      show mv ∈ (answers query none kinds reasons).map move ↔ _
      constructor
      · intro h
        obtain ⟨ans, hans, rfl⟩ := List.mem_map.mp h
        refine ⟨ans, rfl, ?_⟩
        simp only [answers] at hans
        rcases List.mem_append.mp hans with h1 | h1
        · exact .inl ⟨rfl, List.mem_singleton.mp h1⟩
        · obtain ⟨k, hk, hr⟩ := List.mem_flatMap.mp h1
          obtain ⟨hk, hne⟩ := List.mem_filter.mp hk
          exact .inr (.inr ⟨k, hk, by simpa using hne, hr⟩)
      · rintro ⟨ans, rfl, h⟩
        refine List.mem_map.mpr ⟨ans, ?_, rfl⟩
        simp only [answers]
        rcases h with ⟨-, rfl⟩ | ⟨hs, -⟩ | ⟨k, hk, hne, hr⟩
        · exact List.mem_append.mpr (.inl (List.mem_singleton.mpr rfl))
        · simp at hs
        · exact List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨k, List.mem_filter.mpr ⟨hk, by simpa using hne⟩, hr⟩))
    | some out =>
      show mv ∈ (answers query (some tree) kinds reasons).map move ↔ _
      constructor
      · intro h
        obtain ⟨ans, hans, rfl⟩ := List.mem_map.mp h
        refine ⟨ans, rfl, ?_⟩
        simp only [answers] at hans
        rcases List.mem_append.mp hans with h1 | h1
        · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp h1
          exact .inr (.inl ⟨rfl, o, (tree_mem st x _ o).mp ho, rfl⟩)
        · obtain ⟨k, hk, hr⟩ := List.mem_flatMap.mp h1
          obtain ⟨hk, hne⟩ := List.mem_filter.mp hk
          exact .inr (.inr ⟨k, hk, by simpa using hne, hr⟩)
      · rintro ⟨ans, rfl, h⟩
        refine List.mem_map.mpr ⟨ans, ?_, rfl⟩
        simp only [answers]
        rcases h with ⟨hs, -⟩ | ⟨-, o, ho, rfl⟩ | ⟨k, hk, hne, hr⟩
        · simp at hs
        · exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨o, (tree_mem st x _ o).mpr ho, rfl⟩))
        · exact List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨k, List.mem_filter.mpr ⟨hk, by simpa using hne⟩, hr⟩))
  | «at» t => show mv ∈ [_] ↔ _; simp [Slot.Fills]
  | operate o =>
    simp only [fill, Slot.Fills, Id.run_bind]
    let move := fun p => [Line.operate (.screen (Id.run (openedOf x w o)).origin (st.ref o.screen)) o.control (literal p)]
    cases hp : o.payloads with
    | some ps =>
      show mv ∈ ps.map move ↔ _
      constructor
      · intro h
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        exact ⟨p, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
    | none =>
      show mv ∈ (Id.run (x.tree st (.control (st.ref o.screen) o.control))).values.map move ↔ _
      constructor
      · intro h
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        exact ⟨p, (tree_mem st x _ p).mp hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact List.mem_map.mpr ⟨p, (tree_mem st x _ p).mpr hp, rfl⟩
  | unsubscribe i => show mv ∈ [_] ↔ _; simp [Slot.Fills]
  | request r query =>
    show mv ∈ (Id.run (x.tree st (.input r))).values.flatMap (requestMoves r query) ↔ _
    simp only [List.mem_flatMap, tree_mem, Slot.Fills]
  | emit peer event =>
    show mv ∈ (Id.run (x.tree st (.payload event))).values.map (emitMove x.own peer event x.lines.length) ↔ _
    simp only [List.mem_map, tree_mem, Slot.Fills]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
  | restart => show mv ∈ [_] ↔ _; simp [Slot.Fills]

/--
A move is enumerated exactly when it fills a slot that the world enables (its command, query, event, or control is
one of the spec's), with values that the declared domains and the finite types admit (Slot.Fills).
-/
@[guarantee] theorem moves_complete (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) (e : Enabled)
    (mv : Move) : mv ∈ Id.run (moves spec st x w e) ↔ ∃ s : Slot, s.Enabled spec st x w e ∧ s.Fills spec st x w mv := by
  show mv ∈ (Id.run ((slots spec st x w e).mapM (fill spec st x w))).flatten ↔ _
  rw [mapM_id, List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hmv⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    exact ⟨s, slots_enabled _ _ _ _ _ s hs, (fill_iff _ _ _ _ s mv).mp hmv⟩
  · rintro ⟨s, hs, hf⟩
    exact ⟨_, List.mem_map.mpr ⟨s, slots_complete _ _ _ _ _ s hs, rfl⟩, (fill_iff _ _ _ _ s mv).mpr hf⟩

theorem fills_realizes (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) (s : Slot) (mv : Move)
    (h : s.Fills spec st x w mv) : s.Realizes x mv := by
  cases s with
  | answer a msg =>
    simp only [Slot.Fills] at h
    obtain ⟨answer, rfl, -⟩ := h
    exact ⟨_, answer, _, rfl⟩
  | «at» t => exact h
  | operate o =>
    obtain ⟨p, -, rfl⟩ := h
    exact ⟨_, p, rfl⟩
  | unsubscribe i => exact h
  | request r query =>
    obtain ⟨v, -, h⟩ := h
    exact ⟨v, h⟩
  | emit peer event =>
    obtain ⟨v, -, rfl⟩ := h
    exact ⟨v, rfl⟩
  | restart => exact h

/-- Every move that explore appends fills a slot that the world enables (Slot.Enabled), with that slot's shape. -/
@[guarantee] theorem moves_enabled (spec : Spec.Structure) (st : Service) (x : Explored) (w : World) (e : Enabled)
    (mv : Move) (h : mv ∈ Id.run (moves spec st x w e)) :
    ∃ s ∈ slots spec st x w e, s.Enabled spec st x w e ∧ s.Realizes x mv := by
  obtain ⟨s, hs, hf⟩ := (moves_complete spec st x w e mv).mp h
  exact ⟨s, slots_complete _ _ _ _ _ s hs, hs, fills_realizes _ _ _ _ s mv hf⟩

end Tazuna.Thm.Explore.Moves
