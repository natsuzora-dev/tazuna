import Tazuna.Thm.Verify.Complete.Ids
import Tazuna.Thm.Verify.Complete.Lists

/-!
A search that finds a pairing gives a pairing that meets every goal: each frame on the search's stack keeps `FrameOK`,
and a frame without goals is the result.
-/

namespace Tazuna.Thm.Verify.Complete.Search

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Ids Tazuna.Thm.Verify.Complete.Lists

/-- A search that finds a pairing finds it in a frame that some invariant of the frames holds for. -/
theorem search_sound (sc : Scope) (Inv : List Goal × Pairing → Prop)
    (hexp : ∀ g rest p, Inv (g :: rest, p) → ∀ f ∈ expand sc g rest p, Inv f) :
    ∀ n stack p, (∀ f ∈ stack, Inv f) → search sc n stack = .paired p → Inv ([], p)
  | _, [], _, _, h => by simp [search] at h
  | n, ([], q) :: stack, p, hs, h => by
    cases n <;> (simp only [search, Outcome.paired.injEq] at h; subst h; exact hs _ List.mem_cons_self)
  | 0, (_ :: _, _) :: _, _, _, h => by simp [search] at h
  | n + 1, (g :: rest, q) :: stack, p, hs, h => by
    simp only [search] at h
    refine search_sound sc Inv hexp n _ p (fun f hf => ?_) h
    rcases List.mem_append.mp hf with hf | hf
    · exact hexp g rest q (hs _ List.mem_cons_self) f hf
    · exact hs f (List.mem_cons_of_mem _ hf)

def outGoals (gs : List Goal) : List Out := gs.filterMap fun | .out s => some s | _ => none

def subGoals (gs : List Goal) : List String := gs.filterMap fun | .subscription id => some id | _ => none

/-- The order that `ordered` keeps between two pairs. -/
def Good (c : Ctx) (a b : Out × Out) : Prop :=
  ((c.follows (b.1.index - 1)).contains (a.1.index - 1) = true → a.2.index < b.2.index) ∧
    ((c.follows (a.1.index - 1)).contains (b.1.index - 1) = true → b.2.index < a.2.index)

theorem Good.symm {c : Ctx} {a b : Out × Out} (h : Good c a b) : Good c b a := ⟨h.2, h.1⟩

/-- What a search checks of a pair besides the values. -/
structure PairOK (sc : Scope) (ids : Ids) (q : Out × Out) : Prop where
  trace : q.2 ∈ sc.traceOut
  type : q.2.line.body.type = q.1.line.body.type
  time : sameTime q.1.line q.2.line = true
  place : match q.1.line.body with
    | .answer _ _ to _ => ∃ t, q.2.line.body.to? = some t ∧ ids.bound.traceOf? to = some t
    | _ => q.2.line.body.name? = q.1.line.body.name?

theorem PairOK.mono {sc : Scope} {ids ids' : Ids} {q : Out × Out} (h : PairOK sc ids q) (hg : Grows ids ids') :
    PairOK sc ids' q := by
  refine ⟨h.trace, h.type, h.time, ?_⟩
  have hp := h.place
  split
  · rename_i to _ hb
    rw [hb] at hp
    obtain ⟨t, ht, hl⟩ := hp
    exact ⟨t, ht, traceOf?_prefix hg hl⟩
  · rename_i hn
    split at hp
    · rename_i hb; exact absurd hb (hn _ _ _ _)
    · exact hp

/-- What a search checks of a pair of open subscriptions besides the values. -/
def SubOK (sc : Scope) (q : String × String) : Prop :=
  ∃ s t, sc.openSnapshot.lookup q.1 = some s ∧ sc.openTrace.lookup q.2 = some t ∧ s.name = t.name

/-- The paired values match under `renameBy sc.declared R`. -/
def Contents (sc : Scope) (R : Renaming) (p : Pairing) : Prop :=
  (∀ q ∈ p.pairs, ContentMatches (renameBy sc.declared R) (sc.ctx.compared q.1.line q.2.line).1
      (sc.ctx.compared q.1.line q.2.line).2) ∧
    ∀ q ∈ p.subscriptions, ∀ s t, sc.openSnapshot.lookup q.1 = some s → sc.openTrace.lookup q.2 = some t →
      ContentMatches (renameBy sc.declared R) s.out.line.content t.out.line.content

/-- The invariant of a search frame `(gs, p)` of a search that starts from goals `G₀` and pairing `p₀`. -/
structure FrameOK (sc : Scope) (G₀ : List Goal) (p₀ : Pairing) (gs : List Goal) (p : Pairing) : Prop where
  outs : (outGoals gs ++ p.pairs.map (·.1)).Perm (outGoals G₀)
  subs : (subGoals gs ++ p.subscriptions.map (·.1)).Perm (subGoals G₀)
  bagLens : ∀ l sl xs ys, Goal.bag l sl xs ys ∈ gs → xs.length = ys.length
  keys : p₀.keys <+: p.keys
  oneToOne : OneToOne p₀.keys → OneToOne p.keys
  declared : ∀ u ∈ p.keys, u ∈ p₀.keys ∨ sc.declared.contains u.snapshot = true
  ids : Grows p₀.ids p.ids
  idsWf : IdsWf p₀.ids → IdsWf p.ids
  pairs : ∀ q ∈ p.pairs, PairOK sc p.ids q
  pairsNodup : (p.pairs.map (·.2.index)).Nodup
  order : p.pairs.Pairwise (Good sc.ctx)
  subsOK : ∀ q ∈ p.subscriptions, SubOK sc q
  subsNodup : (p.subscriptions.map (·.2)).Nodup
  content : ∀ R, p.keys <+: R → BagsHold sc.declared R gs → BagsHold sc.declared R G₀ ∧ Contents sc R p

theorem FrameOK.start (sc : Scope) (G₀ : List Goal) (ids : Ids) (keys : Renaming)
    (hb : ∀ l sl xs ys, Goal.bag l sl xs ys ∈ G₀ → xs.length = ys.length) :
    FrameOK sc G₀ { ids, keys } G₀ { ids, keys } :=
  ⟨by simp, by simp, hb, List.prefix_refl _, id, fun u hu => .inl hu, List.prefix_refl _, id, by simp, by simp,
    List.Pairwise.nil, by simp, by simp, fun _ _ h => ⟨h, by simp [Contents]⟩⟩

@[simp] theorem outGoals_nil : outGoals [] = [] := rfl

@[simp] theorem subGoals_nil : subGoals [] = [] := rfl

@[simp] theorem outGoals_append (a b : List Goal) : outGoals (a ++ b) = outGoals a ++ outGoals b := by
  simp [outGoals]

@[simp] theorem subGoals_append (a b : List Goal) : subGoals (a ++ b) = subGoals a ++ subGoals b := by
  simp [subGoals]

@[simp] theorem outGoals_out (s : Out) (gs : List Goal) : outGoals (.out s :: gs) = s :: outGoals gs := by
  simp [outGoals]

@[simp] theorem outGoals_subscription (id : String) (gs : List Goal) :
    outGoals (.subscription id :: gs) = outGoals gs := by
  simp [outGoals]

@[simp] theorem outGoals_bag (l sl : Nat) (xs ys : List CValue) (gs : List Goal) :
    outGoals (.bag l sl xs ys :: gs) = outGoals gs := by
  simp [outGoals]

@[simp] theorem subGoals_out (s : Out) (gs : List Goal) : subGoals (.out s :: gs) = subGoals gs := by
  simp [subGoals]

@[simp] theorem subGoals_subscription (id : String) (gs : List Goal) :
    subGoals (.subscription id :: gs) = id :: subGoals gs := by
  simp [subGoals]

@[simp] theorem subGoals_bag (l sl : Nat) (xs ys : List CValue) (gs : List Goal) :
    subGoals (.bag l sl xs ys :: gs) = subGoals gs := by
  simp [subGoals]

theorem outGoals_bags {l sl : Nat} {gs : List Goal} (h : BagGoals l sl gs) : outGoals gs = [] := by
  simp only [outGoals, List.filterMap_eq_nil_iff]
  intro g hg
  obtain ⟨xs, ys, rfl, _⟩ := h g hg
  rfl

theorem subGoals_bags {l sl : Nat} {gs : List Goal} (h : BagGoals l sl gs) : subGoals gs = [] := by
  simp only [subGoals, List.filterMap_eq_nil_iff]
  intro g hg
  obtain ⟨xs, ys, rfl, _⟩ := h g hg
  rfl

theorem bagsHold_cons_of_not_bag {d : List String} {R : Renaming} {g : Goal} {rest : List Goal}
    (hg : ∀ l sl xs ys, g ≠ .bag l sl xs ys) (h : BagsHold d R rest) : BagsHold d R (g :: rest) := by
  intro l sl xs ys hm
  rcases List.mem_cons.mp hm with e | hm
  · exact absurd e.symm (hg l sl xs ys)
  · exact h l sl xs ys hm

theorem ordered_good {c : Ctx} {pairs : List (Out × Out)} {s t : Out} (h : ordered c pairs s t = true) :
    ∀ q ∈ pairs, Good c q (s, t) := by
  intro q hq
  simp only [ordered, List.all_eq_true] at h
  have := h q hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · rcases this.1 with h | h
    · simp only at hf; rw [hf] at h; cases h
    · exact h
  · rcases this.2 with h | h
    · simp only at hf; rw [hf] at h; cases h
    · exact h


theorem pairIds_spec {sc : Scope} {ids ids' : Ids} {s t : Out} (h : pairIds sc ids s t = some ids') :
    Grows ids ids' ∧ (IdsWf ids → IdsWf ids') ∧ ∀ d i to x, s.line.body = .answer d i to x →
      ∃ t', t.line.body.to? = some t' ∧ ids'.bound.traceOf? to = some t' := by
  have refl : ∀ ids : Ids, Grows ids ids ∧ (IdsWf ids → IdsWf ids) := fun ids => ⟨List.prefix_refl _, id⟩
  unfold pairIds at h
  cases hb : s.line.body with
  | answer d i to x =>
    rw [hb] at h
    obtain ⟨g, hs, _, w⟩ := useIds_spec h
    refine ⟨g, w, fun d' i' to' x' hb' => ?_⟩
    cases hb'
    exact hs to rfl
  | command | query =>
    rw [hb] at h
    exact ⟨(join_spec h).1, (join_spec h).2, fun _ _ _ _ h => nomatch h⟩
  | _ =>
    rw [hb] at h
    cases h
    exact ⟨(refl ids).1, (refl ids).2, fun _ _ _ _ h => nomatch h⟩


set_option linter.unusedSimpArgs false in
theorem pairOut_spec {sc : Scope} {p p' : Pairing} {s t : Out} {goals : List Goal}
    (h : pairOut sc p s t = some (p', goals)) :
    ordered sc.ctx p.pairs s t = true ∧ ∃ ids keys, pairIds sc p.ids s t = some ids ∧
      walkContent sc.declared t.index s.index (sc.ctx.compared s.line t.line).1 (sc.ctx.compared s.line t.line).2
        p.keys = some (keys, goals) ∧ p' = { p with ids, keys, pairs := p.pairs ++ [(s, t)] } := by
  unfold pairOut at h
  by_cases ho : ordered sc.ctx p.pairs s t = true
  · simp only [ho, Bool.not_true, Bool.false_eq_true, ite_false] at h
    refine ⟨ho, ?_⟩
    cases hi : pairIds sc p.ids s t with
    | none => simp [hi] at h
    | some ids =>
    cases hw : walkContent sc.declared t.index s.index (sc.ctx.compared s.line t.line).1
        (sc.ctx.compared s.line t.line).2 p.keys with
    | none => simp [hi, hw] at h
    | some x =>
    obtain ⟨keys, g⟩ := x
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some, pure_bind, hi] at h
    rw [hw] at h
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ids, keys, rfl, rfl, rfl⟩
  · simp [ho] at h


set_option linter.unusedSimpArgs false in
theorem pairSubscription_spec {sc : Scope} {p p' : Pairing} {id tid : String} {goals : List Goal}
    (h : pairSubscription sc p id tid = some (p', goals)) :
    ∃ s t keys, sc.openSnapshot.lookup id = some s ∧ sc.openTrace.lookup tid = some t ∧ s.name = t.name ∧
      walkContent sc.declared t.out.index s.out.index s.out.line.content t.out.line.content p.keys =
        some (keys, goals) ∧ p' = { p with keys, subscriptions := p.subscriptions ++ [(id, tid)] } := by
  unfold pairSubscription at h
  cases hs : sc.openSnapshot.lookup id with
  | none => simp [hs] at h
  | some s =>
  cases ht : sc.openTrace.lookup tid with
  | none => simp [hs, ht] at h
  | some t =>
  simp only [hs, ht, Option.bind_eq_bind, Option.bind_some] at h
  by_cases hn : (s.name != t.name) = true
  · simp [hn] at h
  · simp only [hn, Bool.false_eq_true, ite_false, Option.pure_def, Option.bind_some] at h
    cases hw : walkContent sc.declared t.out.index s.out.index s.out.line.content t.out.line.content p.keys with
    | none => simp [hw] at h
    | some x =>
    obtain ⟨keys, g⟩ := x
    rw [hw] at h
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s, t, keys, rfl, rfl, by simpa using hn, hw, rfl⟩

theorem mem_candidates {sc : Scope} {p : Pairing} {s t : Out} (h : t ∈ candidates sc p s) :
    t ∈ sc.traceOut ∧ (p.pairs.any (·.2.index == t.index)) = false ∧ t.line.body.type = s.line.body.type ∧
      sameTime s.line t.line = true ∧
      (match s.line.body with | .answer .. => True | _ => t.line.body.name? = s.line.body.name?) := by
  simp only [candidates, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨hm, ⟨⟨⟨hp, ht⟩, hs⟩, hn⟩⟩ := h
  refine ⟨hm, hp, ht, hs, ?_⟩
  split
  · trivial
  · split at hn
    · rename_i hno _ _ _ _ _ hb'; exact (hno _ _ _ _ hb').elim
    · simpa using hn


theorem expand_out {sc : Scope} {G₀ : List Goal} {p₀ : Pairing} {s : Out} {rest : List Goal} {p : Pairing}
    (h : FrameOK sc G₀ p₀ (.out s :: rest) p) : ∀ f ∈ expand sc (.out s) rest p, FrameOK sc G₀ p₀ f.1 f.2 := by
  intro f hf
  simp only [expand, List.mem_filterMap, Option.map_eq_some_iff] at hf
  obtain ⟨t, htd, ⟨p', goals⟩, hpo, rfl⟩ := hf
  have htc := mem_of_mem_distinct htd
  obtain ⟨htr, hnp, hty, hti, hnm⟩ := mem_candidates htc
  obtain ⟨ho, ids, keys, hpi, hwc, rfl⟩ := pairOut_spec hpo
  obtain ⟨hg, hw, hpl⟩ := pairIds_spec hpi
  have W := walkContent_sound hwc
  have hog := outGoals_bags W.bags
  have hsg := subGoals_bags W.bags
  refine ⟨?_, ?_, ?_, h.keys.trans W.grows, fun h1 => W.oneToOne (h.oneToOne h1), fun u hu => ?_, h.ids.trans hg,
    fun h1 => hw (h.idsWf h1), ?_, ?_, ?_, h.subsOK, h.subsNodup, ?_⟩
  · have := h.outs
    simp only [outGoals_out, List.cons_append] at this
    simp only [outGoals_append, hog, List.nil_append, List.map_append, List.map_singleton]
    refine List.Perm.trans ?_ this
    rw [← List.append_assoc]
    exact List.perm_append_singleton _ _
  · have := h.subs
    simp only [subGoals_out] at this
    simpa only [subGoals_append, hsg, List.nil_append] using this
  · intro l sl xs ys hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨xs', ys', e, hl⟩ := W.bags _ hm
      cases e; exact hl
    · exact h.bagLens l sl xs ys (List.mem_cons_of_mem _ hm)
  · rcases W.declared u hu with hu | hu
    · exact h.declared u hu
    · exact .inr hu
  · intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact (h.pairs q hq).mono hg
    · refine ⟨htr, hty, hti, ?_⟩
      show match s.line.body with
        | .answer _ _ to _ => ∃ t', t.line.body.to? = some t' ∧ ids.bound.traceOf? to = some t'
        | _ => t.line.body.name? = s.line.body.name?
      revert hnm hpl
      cases s.line.body with
      | answer d i to x => intro _ hpl; exact hpl d i to x rfl
      | _ => intro hnm _; exact hnm
  · simp only [List.map_append, List.map_singleton]
    refine List.nodup_append.mpr ⟨h.pairsNodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
      fun a ha b hb e => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb e
    simp only [List.any_eq_false, beq_iff_eq] at hnp
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp ha
    exact hnp q hq hqe
  · exact List.pairwise_append.mpr ⟨h.order, List.pairwise_singleton _ _,
      fun a ha b hb => by simp only [List.mem_singleton] at hb; subst hb; exact ordered_good ho a ha⟩
  · intro R hR hb
    have hold := h.content R (W.grows.trans hR) (bagsHold_cons_of_not_bag (fun _ _ _ _ e => nomatch e) hb.right)
    refine ⟨hold.1, fun q hq => ?_, hold.2.2⟩
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hold.2.1 q hq
    · exact W.sound R hR hb.left


theorem expand_subscription {sc : Scope} {G₀ : List Goal} {p₀ : Pairing} {id : String} {rest : List Goal}
    {p : Pairing} (h : FrameOK sc G₀ p₀ (.subscription id :: rest) p) :
    ∀ f ∈ expand sc (.subscription id) rest p, FrameOK sc G₀ p₀ f.1 f.2 := by
  intro f hf
  simp only [expand, List.mem_filterMap, Option.map_eq_some_iff] at hf
  obtain ⟨⟨tid, t₀⟩, htd, ⟨p', goals⟩, hps, rfl⟩ := hf
  have htc := mem_of_mem_distinct htd
  simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at htc
  obtain ⟨_, hnp, _⟩ := htc
  obtain ⟨s, t, keys, hs, ht, hn, hwc, rfl⟩ := pairSubscription_spec hps
  have W := walkContent_sound hwc
  have hog := outGoals_bags W.bags
  have hsg := subGoals_bags W.bags
  refine ⟨?_, ?_, ?_, h.keys.trans W.grows, fun h1 => W.oneToOne (h.oneToOne h1), fun u hu => ?_, h.ids,
    h.idsWf, h.pairs, h.pairsNodup, h.order, ?_, ?_, ?_⟩
  · have := h.outs
    simp only [outGoals_subscription] at this
    simpa only [outGoals_append, hog, List.nil_append] using this
  · have := h.subs
    simp only [subGoals_subscription, List.cons_append] at this
    simp only [subGoals_append, hsg, List.nil_append, List.map_append, List.map_singleton]
    refine List.Perm.trans ?_ this
    rw [← List.append_assoc]
    exact List.perm_append_singleton _ _
  · intro l sl xs ys hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨xs', ys', e, hl⟩ := W.bags _ hm
      cases e; exact hl
    · exact h.bagLens l sl xs ys (List.mem_cons_of_mem _ hm)
  · rcases W.declared u hu with hu | hu
    · exact h.declared u hu
    · exact .inr hu
  · intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact h.subsOK q hq
    · exact ⟨s, t, hs, ht, hn⟩
  · simp only [List.map_append, List.map_singleton]
    refine List.nodup_append.mpr ⟨h.subsNodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
      fun a ha b hb e => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb e
    simp only [List.any_eq_false, beq_iff_eq] at hnp
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp ha
    exact hnp q hq hqe
  · intro R hR hb
    have hold := h.content R (W.grows.trans hR) (bagsHold_cons_of_not_bag (fun _ _ _ _ e => nomatch e) hb.right)
    refine ⟨hold.1, hold.2.1, fun q hq s' t' hs' ht' => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hold.2.2 q hq s' t' hs' ht'
    · simp only at hs' ht'
      rw [hs] at hs'; rw [ht] at ht'
      cases hs'; cases ht'
      exact W.sound R hR hb.left

theorem expand_bag {sc : Scope} {G₀ : List Goal} {p₀ : Pairing} {l sl : Nat} {xs ys : List CValue}
    {rest : List Goal} {p : Pairing} (h : FrameOK sc G₀ p₀ (.bag l sl xs ys :: rest) p) :
    ∀ f ∈ expand sc (.bag l sl xs ys) rest p, FrameOK sc G₀ p₀ f.1 f.2 := by
  intro f hf
  have hlen := h.bagLens l sl xs ys List.mem_cons_self
  cases xs with
  | nil =>
    simp only [expand, List.mem_singleton] at hf
    subst hf
    have hys : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst hys
    refine ⟨by simpa using h.outs, by simpa using h.subs, fun l' sl' xs' ys' hm =>
      h.bagLens l' sl' xs' ys' (List.mem_cons_of_mem _ hm), h.keys, h.oneToOne, h.declared, h.ids, h.idsWf, h.pairs,
      h.pairsNodup, h.order, h.subsOK, h.subsNodup, fun R hR hb => h.content R hR ?_⟩
    intro l' sl' xs' ys' hm
    rcases List.mem_cons.mp hm with e | hm
    · cases e; exact ⟨[], List.Perm.refl _, trivial⟩
    · exact hb l' sl' xs' ys' hm
  | cons x more =>
    simp only [expand, List.mem_filterMap, Option.map_eq_some_iff] at hf
    obtain ⟨⟨y, i⟩, hyd, ⟨keys, goals⟩, hw, rfl⟩ := hf
    have hyi : ys[i]? = some y := List.mem_zipIdx_iff_getElem?.mp (mem_of_mem_distinct hyd)
    have hil : i < ys.length := (List.getElem?_eq_some_iff.mp hyi).1
    have W := (walk_sound sc.declared l sl).1 x y p.keys keys goals hw
    have hog := outGoals_bags W.bags
    have hsg := subGoals_bags W.bags
    refine ⟨?_, ?_, ?_, h.keys.trans W.grows, fun h1 => W.oneToOne (h.oneToOne h1), fun u hu => ?_, h.ids,
      h.idsWf, h.pairs, h.pairsNodup, h.order, h.subsOK, h.subsNodup, ?_⟩
    · have := h.outs
      simp only [outGoals_bag] at this
      simpa only [outGoals_append, hog, outGoals_bag, outGoals_nil, List.nil_append, List.singleton_append] using this
    · have := h.subs
      simp only [subGoals_bag] at this
      simpa only [subGoals_append, hsg, subGoals_bag, subGoals_nil, List.nil_append, List.singleton_append] using this
    · intro l' sl' xs' ys' hm
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with (hm | hm) | hm
      · obtain ⟨_, _, e, hl⟩ := W.bags _ hm
        cases e; exact hl
      · cases hm
        rw [List.length_eraseIdx_of_lt hil]
        simp at hlen; omega
      · exact h.bagLens l' sl' xs' ys' (List.mem_cons_of_mem _ hm)
    · rcases W.declared u hu with hu | hu
      · exact h.declared u hu
      · exact .inr hu
    · intro R hR hb
      refine h.content R (W.grows.trans hR) ?_
      intro l' sl' xs' ys' hm
      rcases List.mem_cons.mp hm with e | hm
      · cases e
        have hv := W.sound R hR hb.left.left
        obtain ⟨zs, hp, hl⟩ := hb.left.right l sl more (ys.eraseIdx i) (by simp)
        exact ⟨y :: zs, (perm_cons_eraseIdx hyi).trans ((List.perm_cons y).mpr hp), hv, hl⟩
      · exact hb.right l' sl' xs' ys' hm

theorem expand_ok {sc : Scope} {G₀ : List Goal} {p₀ : Pairing} :
    ∀ g rest p, FrameOK sc G₀ p₀ (g :: rest) p → ∀ f ∈ expand sc g rest p, FrameOK sc G₀ p₀ f.1 f.2
  | .out _, _, _, h => expand_out h
  | .subscription _, _, _, h => expand_subscription h
  | .bag .., _, _, h => expand_bag h

/-- A search from goals `G₀` and pairing `p₀` that finds `p` meets every goal. -/
theorem search_frame {sc : Scope} {G₀ : List Goal} {ids : Ids} {keys : Renaming} {n : Nat} {p : Pairing}
    (hb : ∀ l sl xs ys, Goal.bag l sl xs ys ∈ G₀ → xs.length = ys.length)
    (h : search sc n [(G₀, { ids, keys })] = .paired p) : FrameOK sc G₀ { ids, keys } [] p :=
  search_sound sc (fun f => FrameOK sc G₀ { ids, keys } f.1 f.2) (fun g rest p h => expand_ok g rest p h) n _ p
    (fun f hf => by simp only [List.mem_singleton] at hf; subst hf; exact FrameOK.start sc G₀ ids keys hb) h

end Tazuna.Thm.Verify.Complete.Search
