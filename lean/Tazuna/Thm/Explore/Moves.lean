import Tazuna.Explore.Moves
import Tazuna.Thm.Guarantee

/-!
Soundness of the enumeration of moves: every move that explore appends fills a slot that the world enables, and has the
shape of that slot.
-/

namespace Tazuna.Thm.Explore.Moves

open Tazuna.Data Tazuna.Service Tazuna.Sim Tazuna.Scenario Tazuna.Explore

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

theorem bind_run_ok {ε α β : Type} {x : ExceptT ε Id α} {f : α → ExceptT ε Id β} {b : β}
    (h : (x >>= f).run = .ok b) : ∃ a, x.run = .ok a ∧ (f a).run = .ok b := by
  simp only [ExceptT.run_bind] at h
  cases hx : x.run with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

theorem pure_run_ok {ε α : Type} {a b : α} (h : (pure a : ExceptT ε Id α).run = .ok b) : a = b := by
  cases h; rfl

theorem fill_realizes (spec : Spec.Structure) (st : Service) (fs : Functions Id) (x : Explored) (w : World) (s : Slot)
    (ms : List Move) (h : (fill spec st fs x w s).run = .ok ms) : ∀ mv ∈ ms, s.Realizes x mv := by
  cases s with
  | answer a msg =>
    simp only [fill] at h
    obtain ⟨request, -, h⟩ := bind_run_ok h
    obtain ⟨body, -, h⟩ := bind_run_ok h
    have done : ∀ pool : List Value, (pure (pool.map fun answer =>
        answerMove msg.receiver request answer (msg.status == .inFlight) x.lines.length) :
          ExceptT Fault Id (List Move)).run = .ok ms → ∀ mv ∈ ms, (Slot.answer a msg).Realizes x mv := by
      intro pool hp
      cases pure_run_ok hp
      intro mv hmv
      obtain ⟨answer, -, rfl⟩ := List.mem_map.mp hmv
      exact ⟨request, answer, _, rfl⟩
    split at h
    all_goals
      repeat (obtain ⟨_, -, h⟩ := bind_run_ok h)
    all_goals
      split at h
    all_goals
      repeat (obtain ⟨_, -, h⟩ := bind_run_ok h)
    all_goals exact done _ h
  | «at» t =>
    simp [fill] at h
    cases h
    simp [Slot.Realizes]
  | operate o =>
    simp only [fill] at h
    obtain ⟨opened, -, h⟩ := bind_run_ok h
    split at h <;> obtain ⟨_, -, h⟩ := bind_run_ok h <;> cases pure_run_ok h <;> intro mv hmv <;>
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hmv <;> exact ⟨_, p, rfl⟩
  | unsubscribe i =>
    simp [fill] at h
    cases h
    simp [Slot.Realizes]
  | request r query =>
    simp only [fill] at h
    obtain ⟨values, -, h⟩ := bind_run_ok h
    cases pure_run_ok h
    intro mv hmv
    obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hmv
    exact ⟨v, hv⟩
  | emit peer event =>
    simp only [fill] at h
    obtain ⟨values, -, h⟩ := bind_run_ok h
    cases pure_run_ok h
    intro mv hmv
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hmv
    exact ⟨v, rfl⟩
  | restart =>
    simp [fill] at h
    cases h
    simp [Slot.Realizes]

theorem mapM_run_ok {ε α β : Type} (f : α → ExceptT ε Id β) :
    ∀ (xs : List α) (ys : List β), (xs.mapM f).run = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, (f x).run = .ok y
  | [], ys, h => by
    cases pure_run_ok h
    simp
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_run_ok h
    obtain ⟨rest, hrest, h⟩ := bind_run_ok h
    cases pure_run_ok h
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨x, List.mem_cons_self, hy⟩
    · obtain ⟨x', hx', h'⟩ := mapM_run_ok f xs rest hrest z hz
      exact ⟨x', List.mem_cons_of_mem _ hx', h'⟩

/-- Every move that explore appends fills a slot that the world enables (Slot.Enabled), with that slot's shape. -/
@[guarantee] theorem moves_enabled (spec : Spec.Structure) (st : Service) (fs : Functions Id) (x : Explored)
    (w : World) (e : Enabled) (ms : List Move) (h : (moves spec st fs x w e).run = .ok ms) :
    ∀ mv ∈ ms, ∃ s ∈ slots spec st x w e, s.Enabled spec st x w e ∧ s.Realizes x mv := by
  simp only [moves] at h
  obtain ⟨filled, hf, h⟩ := bind_run_ok h
  cases pure_run_ok h
  intro mv hmv
  obtain ⟨l, hl, hmv⟩ := List.mem_flatten.mp hmv
  obtain ⟨s, hs, hfill⟩ := mapM_run_ok _ _ _ hf l hl
  exact ⟨s, hs, slots_enabled _ _ _ _ _ s hs, fill_realizes _ _ _ _ _ s l hfill mv hmv⟩

end Tazuna.Thm.Explore.Moves
