import Tazuna.Thm.Verify.Complete.Explain
import Tazuna.Thm.Verify.Complete.Steps

/-!
A quiet window and a quiet pair of `in` lines give their pairings: the window's search pairs all compared lines and
open subscriptions, and the `in` lines match.
-/

namespace Tazuna.Thm.Verify.Complete.Run

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Ids Tazuna.Thm.Verify.Complete.Lists
open Tazuna.Thm.Verify.Complete.Search Tazuna.Thm.Verify.Complete.Window Tazuna.Thm.Verify.Complete.Explain
open Tazuna.Thm.Verify.Complete.Steps

theorem window_paired (c : Ctx) (st : St) (specOut traceOut : List Out) (m s : Nat)
    (hm : st.reportedMissing = []) (hu : st.reportedUnexpected = [])
    (h1 : (runWindow c st specOut traceOut m s).1 = []) (h2 : (runWindow c st specOut traceOut m s).2.1 = none) :
    ∃ p, pairAll (scopeOf c (enter st specOut traceOut) traceOut) (goalsOf c (enter st specOut traceOut) specOut)
        { ids := st.ids, keys := st.keys } = .paired p ∧
      (runWindow c st specOut traceOut m s).2.2 =
        let st₁ := enter st specOut traceOut
        { st₁ with ids := p.ids, keys := p.keys,
                   subscriptionIds := explain.subscribed (scopeOf c st₁ traceOut) st.subscriptionIds p.subscriptions }
    := by
  rw [runWindow_eq] at h1 h2 ⊢
  dsimp only at h1 h2 ⊢
  revert h1 h2
  generalize ho : pairAll _ _ _ = o
  intro h1 h2
  cases o with
  | paired p => exact ⟨p, ho, rfl⟩
  | limited => cases h2
  | unpaired => exact absurd h1 (explain_found _ _ _ c _ rfl hm hu)

theorem pairAll_spec {sc : Scope} {goals : List Goal} {start : Pairing} {p : Pairing}
    (h : pairAll sc goals start = .paired p) :
    (goals.filter fun | .out _ => true | _ => false).length = sc.traceOut.length ∧
      sc.openSnapshot.length = sc.openTrace.length ∧ search sc searchLimit [(goals, start)] = .paired p := by
  unfold pairAll at h
  split at h
  · rename_i hc
    simp only [pairable, Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1, hc.1.2, h⟩
  · cases h


theorem outGoals_map_out (L : List Out) : outGoals (L.map Goal.out) = L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem outGoals_map_subscription {α : Type} (f : α → String) (L : List α) :
    outGoals (L.map (Goal.subscription ∘ f)) = [] := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa using ih

theorem subGoals_map_out (L : List Out) : subGoals (L.map Goal.out) = [] := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa using ih

theorem subGoals_map_subscription {α : Type} (f : α → String) (L : List α) :
    subGoals (L.map (Goal.subscription ∘ f)) = L.map f := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem filter_out_length (L : List Out) {α : Type} (f : α → String) (M : List α) :
    ((L.map Goal.out ++ M.map (Goal.subscription ∘ f)).filter fun | .out _ => true | _ => false).length = L.length := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.length_nil]
    induction M with
    | nil => rfl
    | cons a M ih => simp [ih]
  | cons a L ih => simpa using ih

/-- What a window's search that finds `p` gives. -/
structure WindowOK (sc : Scope) (specOut : List Out) (ids : Ids) (keys : Renaming) (p : Pairing) : Prop where
  frame : FrameOK sc ((byRank specOut).map Goal.out ++ sc.openSnapshot.map (Goal.subscription ·.1)) { ids, keys } [] p
  pairsFst : (p.pairs.map (·.1)).Perm specOut
  pairsSnd : (p.pairs.map (·.2)).Perm sc.traceOut
  subsFst : (p.subscriptions.map (·.1)).Perm (sc.openSnapshot.map (·.1))
  subsSnd : (p.subscriptions.map (·.2)).Perm (sc.openTrace.map (·.1))

theorem window_ok {sc : Scope} {specOut : List Out} {ids : Ids} {keys : Renaming} {p : Pairing}
    (h : pairAll sc ((byRank specOut).map Goal.out ++ sc.openSnapshot.map (Goal.subscription ·.1)) { ids, keys } =
      .paired p) : WindowOK sc specOut ids keys p := by
  obtain ⟨hl, ho, hs⟩ := pairAll_spec h
  have F := search_frame (fun l sl xs ys hm => by simp at hm) hs
  have houts : (p.pairs.map (·.1)).Perm specOut := by
    have := F.outs
    rw [outGoals_nil, List.nil_append, outGoals_append, outGoals_map_out,
      show (fun x : String × Subscription => Goal.subscription x.1) = Goal.subscription ∘ (·.1) from rfl,
      outGoals_map_subscription, List.append_nil] at this
    exact this.trans (byRank_perm specOut)
  have hsubs : (p.subscriptions.map (·.1)).Perm (sc.openSnapshot.map (·.1)) := by
    have := F.subs
    rwa [subGoals_nil, List.nil_append, subGoals_append, subGoals_map_out,
      show (fun x : String × Subscription => Goal.subscription x.1) = Goal.subscription ∘ (·.1) from rfl,
      subGoals_map_subscription, List.nil_append] at this
  refine ⟨F, houts, ?_, hsubs, ?_⟩
  · refine perm_of_nodup_subset ?_ (fun x hx => ?_) ?_
    · exact nodup_of_map (·.index) (by rw [List.map_map]; exact F.pairsNodup)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact (F.pairs q hq).trace
    · rw [show (fun x : String × Subscription => Goal.subscription x.1) = Goal.subscription ∘ (·.1) from rfl,
        filter_out_length] at hl
      have := houts.length_eq
      simp only [List.length_map] at this ⊢
      have hb := (byRank_perm specOut).length_eq
      omega
  · refine perm_of_nodup_subset F.subsNodup (fun x hx => ?_) ?_
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, t, _, ht, _⟩ := F.subsOK q hq
      exact List.mem_map.mpr ⟨_, lookup_mem ht, rfl⟩
    · have := hsubs.length_eq
      simp only [List.length_map] at this ⊢
      omega


/-- What a search of an `in` line's bags that finds `p` gives. -/
theorem input_search {c : Ctx} {st : St} {ids : Ids} {l sl : Nat} {x y : Option CValue} {keys : Renaming}
    {goals : List Goal} {p : Pairing} (hw : walkContent st.declared l sl x y st.keys = some (keys, goals))
    (hs : search (inputScope c st) searchLimit [(goals, { ids, keys })] = .paired p) :
    Grows ids p.ids ∧ (IdsWf ids → IdsWf p.ids) ∧ st.keys <+: p.keys ∧ (OneToOne st.keys → OneToOne p.keys) ∧
      (∀ u ∈ p.keys, u ∈ st.keys ∨ st.declared.contains u.snapshot = true) ∧
      ∀ R, p.keys <+: R → ContentMatches (renameBy st.declared R) x y := by
  have W := walkContent_sound hw
  have F := search_frame (fun l' sl' xs ys hm => by
    obtain ⟨_, _, e, hl⟩ := W.bags _ hm
    cases e; exact hl) hs
  refine ⟨F.ids, F.idsWf, W.grows.trans F.keys, fun h => F.oneToOne (W.oneToOne h), fun u hu => ?_, fun R hR => ?_⟩
  · rcases F.declared u hu with h | h
    · rcases W.declared u h with h | h
      · exact .inl h
      · exact .inr h
    · exact .inr h
  · exact W.sound R (F.keys.trans hR) (F.content R hR (fun _ _ _ _ h => nomatch h)).1


/-- Where an answer `in` line answers: a subscription paired with an alike one, or through the bound ids. -/
def AnswerPlaced (st : St) (ids : Ids) (to : String) (t : Option String) : Prop :=
  (∃ l, st.subscriptionIds.lookup to = some l ∧ ∃ t', t = some t' ∧ t' ∈ l) ∨ IdPlaced ids (some to) t

theorem answersPlaced_spec {st : St} {s t : Out} {ids : Ids} (h : answersPlaced st s t = some ids) :
    Grows st.ids ids ∧ (IdsWf st.ids → IdsWf ids) ∧ ∀ d i to x, s.line.body = .answer d i to x →
      AnswerPlaced st ids to t.line.body.to? := by
  unfold answersPlaced at h
  split at h
  · rename_i d i to x d' i' to' x' hs ht
    split at h
    · rename_i l hl
      split at h
      · rename_i hc
        cases h
        refine ⟨List.prefix_refl _, id, fun d₁ i₁ to₁ x₁ hb => ?_⟩
        rw [hs] at hb; cases hb
        exact .inl ⟨l, hl, to', by rw [ht]; rfl, by simpa using hc⟩
      · cases h
    · obtain ⟨g, hs', _, w⟩ := useIds_spec h
      refine ⟨g, w, fun d₁ i₁ to₁ x₁ hb => ?_⟩
      rw [hs] at hb; cases hb
      exact .inr (by rw [ht]; exact useIds_placed h)
  · cases h

/-- What a quiet comparison of two `in` lines gives. -/
structure InputOK (st : St) (s t : Out) (p : Pairing) : Prop where
  type : t.line.body.type = s.line.body.type
  name : t.line.body.name? = s.line.body.name?
  time : sameTime s.line t.line = true
  ids : Grows st.ids p.ids
  idsWf : IdsWf st.ids → IdsWf p.ids
  keys : st.keys <+: p.keys
  oneToOne : OneToOne st.keys → OneToOne p.keys
  declared : ∀ u ∈ p.keys, u ∈ st.keys ∨ st.declared.contains u.snapshot = true
  own : p.ids.bound.traceOf? s.line.body.id = some t.line.body.id
  rest : match s.line.body with
    | .time .. | .restart .. => True
    | .unsubscribe _ _ to => IdPlaced p.ids (some to) t.line.body.to?
    | .answer _ _ to _ => AnswerPlaced st p.ids to t.line.body.to? ∧
        ∀ R, p.keys <+: R → ContentMatches (renameBy st.declared R) s.line.content t.line.content
    | _ => IdPlaced p.ids s.line.body.resultOf? t.line.body.resultOf? ∧
        ∀ R, p.keys <+: R → ContentMatches (renameBy st.declared R) s.line.content t.line.content

theorem input_ok {c : Ctx} {st : St} {s t : Out} {p : Pairing}
    (h : sameInput (inputScope c st) st s t = .paired p) : InputOK st s t p := by
  unfold sameInput at h
  cases hs : inputStart st s t with
  | none => rw [hs] at h; cases h
  | some r =>
  obtain ⟨goals, p₀⟩ := r
  rw [hs] at h
  dsimp only at h
  unfold inputStart at hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i hc
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or, Decidable.not_not,
    Bool.not_eq_false] at hc
  obtain ⟨⟨hty, hna⟩, hti⟩ := hc
  cases hown : st.ids.use (s.idUse t) with
  | none => rw [hown] at hs; cases hs
  | some ids₁ =>
  rw [hown] at hs
  dsimp only at hs
  obtain ⟨g₁, ho₁, w₁⟩ := use_spec hown
  have content : ∀ ids₂ : Ids, Grows ids₁ ids₂ → (IdsWf ids₁ → IdsWf ids₂) →
      (walkContent st.declared t.index s.index s.line.content t.line.content st.keys).map
        (fun (keys, goals) => (goals, ({ ids := ids₂, keys } : Pairing))) = some (goals, p₀) →
      Grows st.ids p.ids ∧ (IdsWf st.ids → IdsWf p.ids) ∧ st.keys <+: p.keys ∧ (OneToOne st.keys → OneToOne p.keys) ∧
        (∀ u ∈ p.keys, u ∈ st.keys ∨ st.declared.contains u.snapshot = true) ∧ Grows ids₂ p.ids ∧
        ∀ R, p.keys <+: R → ContentMatches (renameBy st.declared R) s.line.content t.line.content := by
    intro ids₂ g₂ w₂ hc
    cases hw : walkContent st.declared t.index s.index s.line.content t.line.content st.keys with
    | none => rw [hw] at hc; cases hc
    | some r =>
      obtain ⟨keys, goals'⟩ := r
      rw [hw] at hc
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨g₃, w₃, k₃, o₃, d₃, c₃⟩ := input_search hw h
      exact ⟨g₁.trans (g₂.trans g₃), fun w => w₃ (w₂ (w₁ w)), k₃, o₃, d₃, g₃, c₃⟩
  have own : ∀ ids : Ids, Grows ids₁ ids → ids.bound.traceOf? s.line.body.id = some t.line.body.id :=
    fun ids g => traceOf?_prefix g ho₁
  have hti' : sameTime s.line t.line = true := by simpa using hti
  have empty : ∀ q : Pairing, ([], q) = (goals, p₀) → p = q := by
    intro q e
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    simp only [search] at h
    cases h
    rfl
  cases hb : s.line.body with
  | time | restart =>
    simp only [hb, Option.some.injEq] at hs
    cases empty _ hs
    exact ⟨hty.symm, hna.symm, hti', g₁, w₁, List.prefix_refl _, id, fun u hu => .inl hu,
      own _ (List.prefix_refl _), by simp only [hb]⟩
  | unsubscribe d i to =>
    simp only [hb] at hs
    cases hu : ids₁.useIds t.index s.index (some to) t.line.body.to? with
    | none => rw [hu] at hs; cases hs
    | some ids₂ =>
      rw [hu] at hs
      simp only [Option.some.injEq] at hs
      cases empty _ hs
      obtain ⟨g₂, _, _, w₂⟩ := useIds_spec hu
      exact ⟨hty.symm, hna.symm, hti', g₁.trans g₂, fun w => w₂ (w₁ w), List.prefix_refl _, id, fun u hu => .inl hu,
        own _ g₂, by simp only [hb]; exact useIds_placed hu⟩
  | answer d i to x =>
    simp only [hb] at hs
    cases ha : answersPlaced { st with ids := ids₁ } s t with
    | none => rw [ha] at hs; cases hs
    | some ids₂ =>
      rw [ha] at hs
      dsimp only at hs
      obtain ⟨g₂, w₂, hp⟩ := answersPlaced_spec ha
      obtain ⟨g, w, k, o, dl, g₃, cm⟩ := content ids₂ g₂ w₂ hs
      refine ⟨hty.symm, hna.symm, hti', g, w, k, o, dl, own _ (g₂.trans g₃), ?_⟩
      simp only [hb]
      refine ⟨?_, cm⟩
      rcases hp d i to x hb with hl | hl
      · exact .inl hl
      · exact .inr (hl.mono g₃)
  | _ =>
    simp only [hb] at hs
    rw [← hb] at hs
    cases hu : ids₁.useIds t.index s.index s.line.body.resultOf? t.line.body.resultOf? with
    | none => rw [hu] at hs; cases hs
    | some ids₂ =>
      rw [hu] at hs
      dsimp only at hs
      obtain ⟨g₂, _, _, w₂⟩ := useIds_spec hu
      obtain ⟨g, w, k, o, dl, g₃, cm⟩ := content ids₂ g₂ w₂ hs
      refine ⟨hty.symm, hna.symm, hti', g, w, k, o, dl, own _ (g₂.trans g₃), ?_⟩
      simp only [hb]
      rw [← hb]
      exact ⟨(useIds_placed hu).mono g₃, cm⟩

end Tazuna.Thm.Verify.Complete.Run
