import Tazuna.Validation.Charts
import Tazuna.Service.Input
import Tazuna.Thm.Service.Chart.Basic

namespace Tazuna.Thm.Validation.Charts

open Tazuna.Data Tazuna.Validation Tazuna.Validation.Charts
open Tazuna.Spec

theorem queries_of_other_services (s : Structure) :
    ownQueries s = [] ↔
      ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ key q, (key, some q) ∈ c.queries → q.service ≠ d.service := by
  simp only [ownQueries, List.flatMap_eq_nil_iff]
  constructor
  · intro h d hd c hc key q hq hs
    have hd := h d hd
    simp only [hc] at hd
    have := List.filterMap_eq_nil_iff.mp hd (key, some q) hq
    simp [hs] at this
  · intro h d hd
    split
    · rename_i c hc
      refine List.filterMap_eq_nil_iff.mpr fun ⟨key, q⟩ hq => ?_
      cases q with
      | none => rfl
      | some q => simp [h d hd c hc key q hq]
    · rfl

/-- Whether taking an always transition from `y` re-evaluates always transitions in `z`. -/
def Succ (c : Chart) (y z : String) : Prop :=
  ∃ st ∈ c.states, st.name = y ∧ ∃ t ∈ st.transitions, t.trigger = .always ∧ z ∈ lands c st.name t

inductive Reaches (c : Chart) (start : List String) : String → Prop
  | base {x : String} : x ∈ start → Reaches c start x
  | step {y z : String} : Reaches c start y → Succ c y z → Reaches c start z

def seen (f : Frontier) : List String := f.2.map (·.1)

/-- Whether `f'` keeps the found states and the queue of `f`, and queues every state that it newly finds. -/
def Widens (f f' : Frontier) : Prop :=
  (∀ v ∈ seen f, v ∈ seen f') ∧ (∀ v ∈ f.1, v ∈ f'.1) ∧ (∀ v ∈ seen f', v ∈ seen f ∨ v ∈ f'.1)

theorem Widens.refl (f : Frontier) : Widens f f :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => .inl h⟩

theorem Widens.trans {a b c : Frontier} (hab : Widens a b) (hbc : Widens b c) : Widens a c := by
  refine ⟨fun v h => hbc.1 v (hab.1 v h), fun v h => hbc.2.1 v (hab.2.1 v h), fun v h => ?_⟩
  rcases hbc.2.2 v h with hb | hc
  · rcases hab.2.2 v hb with ha | hq
    · exact .inl ha
    · exact .inr (hbc.2.1 v hq)
  · exact .inr hc

theorem visit_widens (f : Frontier) (to fr : String) : Widens f (visit f to fr) := by
  unfold visit
  split
  · exact Widens.refl f
  · refine ⟨fun v h => ?_, fun v h => ?_, fun v h => ?_⟩
    · simp only [seen, List.map_append, List.mem_append] at h ⊢; exact .inl h
    · simp only [List.mem_append]; exact .inl h
    · simp only [seen, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact .inl h
      · subst h; exact .inr (by simp)

theorem visit_adds (f : Frontier) (to fr : String) : to ∈ seen (visit f to fr) := by
  unfold visit
  split
  · rename_i h
    simp only [List.any_eq_true, beq_iff_eq] at h
    obtain ⟨p, hp, rfl⟩ := h
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  · simp [seen]

theorem foldl_widens {α : Type} (g : Frontier → α → Frontier) (hg : ∀ f x, Widens f (g f x)) :
    ∀ (l : List α) (f : Frontier), Widens f (l.foldl g f)
  | [], f => Widens.refl f
  | x :: xs, f => (hg f x).trans (foldl_widens g hg xs (g f x))

theorem visitAll_widens (s : String) (f : Frontier) (lands : List String) : Widens f (visitAll s f lands) :=
  foldl_widens _ (fun f to => visit_widens f to s) lands f

theorem visitAll_adds (s : String) :
    ∀ (lands : List String) (f : Frontier), ∀ to ∈ lands, to ∈ seen (visitAll s f lands)
  | [], _, _, h => by simp at h
  | x :: xs, f, to, h => by
    simp only [visitAll, List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact (visitAll_widens s (visit f to s) xs).1 to (visit_adds f to s)
    · exact visitAll_adds s xs (visit f x s) to h

theorem edges_fold_adds (s : String) :
    ∀ (es : List Edge) (f : Frontier), ∀ e ∈ es, ∀ to ∈ e.lands,
      to ∈ seen (es.foldl (fun f e => visitAll s f e.lands) f)
  | [], _, _, h, _, _ => by simp at h
  | x :: xs, f, e, h, to, hto => by
    simp only [List.foldl_cons]
    have hg := foldl_widens (fun f (e : Edge) => visitAll s f e.lands) (fun f e => visitAll_widens s f e.lands) xs
    rcases List.mem_cons.mp h with rfl | h
    · exact (hg _).1 to (visitAll_adds s e.lands f to hto)
    · exact edges_fold_adds s xs _ e h to hto

/-- Whether the dequeued states are not `start` and all their successors are found. -/
def Inv (succ : String → String → Prop) (start : String) (f : Frontier) : Prop :=
  ∀ v ∈ seen f, v ∉ f.1 → v ≠ start ∧ ∀ z, succ v z → z ∈ seen f

theorem search_none (es : List Edge) (start : String) (succ : String → String → Prop)
    (hs : ∀ y z, succ y z → ∃ e ∈ es, e.«from» = y ∧ z ∈ e.lands) (f : Frontier) (hinv : Inv succ start f)
    (h : search es start f = .none) :
    ∃ V : List String, (∀ v ∈ seen f, v ∈ V) ∧ start ∉ V ∧ ∀ v ∈ V, ∀ z, succ v z → z ∈ V := by
  match f, hinv, h with
  | ([], prev), hinv, _ =>
    refine ⟨seen ([], prev), fun v hv => hv, fun hst => (hinv start hst (by simp)).1 rfl, fun v hv z hz => ?_⟩
    exact (hinv v hv (by simp)).2 z hz
  | (s :: rest, prev), hinv, h =>
    rw [search] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hne
      have hne : s ≠ start := fun e => hne (by simp [e])
      have hg : Widens (rest, prev) (expand es s (rest, prev)) :=
        foldl_widens (fun f (e : Edge) => visitAll s f e.lands) (fun f e => visitAll_widens s f e.lands) _ _
      have hinv' : Inv succ start (expand es s (rest, prev)) := by
        intro v hv hq
        have hvf : v ∈ seen (s :: rest, prev) := by
          rcases hg.2.2 v hv with h | h
          · exact h
          · exact absurd h hq
        have hrest : v ∉ rest := fun h => hq (hg.2.1 v h)
        by_cases hvs : v = s
        · subst hvs
          refine ⟨hne, fun z hz => ?_⟩
          obtain ⟨e, he, hfrom, hz⟩ := hs v z hz
          exact edges_fold_adds v _ (rest, prev) e (List.mem_filter.mpr ⟨he, by simp [hfrom]⟩) z hz
        · have hnq : v ∉ s :: rest := by
            intro h; rcases List.mem_cons.mp h with h | h
            · exact hvs h
            · exact hrest h
          obtain ⟨hstart, hclosed⟩ := hinv v hvf hnq
          exact ⟨hstart, fun z hz => hg.1 z (hclosed z hz)⟩
      obtain ⟨V, hV, hst, hcl⟩ := search_none es start succ hs _ hinv' h
      exact ⟨V, fun v hv => hV v (hg.1 v hv), hst, hcl⟩
termination_by (unvisited (es.flatMap (·.lands)) f, f.1.length)
decreasing_by
  rcases expand_progress es s (rest, prev) with e | lt
  · rw [e]; exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (by simpa [unvisited] using lt)

theorem edges_of_succ (c : Chart) (y z : String) (h : Succ c y z) :
    ∃ e ∈ edges c, e.«from» = y ∧ z ∈ e.lands := by
  obtain ⟨st, hst, rfl, t, ht, ha, hz⟩ := h
  refine ⟨{ «from» := st.name, lands := lands c st.name t, guarded := t.guarded }, ?_, rfl, hz⟩
  simp only [edges, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact ⟨st, hst, t, ⟨ht, by simp [ha]⟩, rfl⟩

theorem reaches_closed (c : Chart) (S V : List String) (hS : ∀ v ∈ S, v ∈ V)
    (hcl : ∀ v ∈ V, ∀ z, Succ c v z → z ∈ V) {x : String} (h : Reaches c S x) : x ∈ V := by
  induction h with
  | base hx => exact hS _ hx
  | step _ hs ih => exact hcl _ ih _ hs

theorem searchFrom_none (c : Chart) (e : Edge) (h : searchFrom (edges c) e = .none) :
    ¬ Reaches c e.lands e.«from» := by
  let f0 := visitAll e.«from» ([], []) e.lands
  have hinv : Inv (Succ c) e.«from» f0 := by
    intro v hv hq
    rcases (visitAll_widens e.«from» ([], []) e.lands).2.2 v hv with h | h
    · simp [seen] at h
    · exact absurd h hq
  obtain ⟨V, hV, hst, hcl⟩ :=
    search_none (edges c) e.«from» (Succ c) (edges_of_succ c) f0 hinv h
  intro hr
  exact hst (reaches_closed c e.lands V (fun v hv => hV v (visitAll_adds e.«from» e.lands ([], []) v hv)) hcl hr)

theorem succ_of_edge (c : Chart) (e : Edge) (he : e ∈ edges c) (to : String) (hto : to ∈ e.lands) :
    Succ c e.«from» to := by
  simp only [edges, List.mem_flatMap, List.mem_map, List.mem_filter] at he
  obtain ⟨st, hst, t, ⟨ht, hk⟩, rfl⟩ := he
  exact ⟨st, hst, rfl, t, ht, by simpa using hk, hto⟩

/-- Whether the found states are reachable from `S` and the queued states are found. -/
def ReachableFrontier (c : Chart) (S : List String) (f : Frontier) : Prop :=
  (∀ v ∈ seen f, Reaches c S v) ∧ ∀ v ∈ f.1, v ∈ seen f

theorem visit_reachable (c : Chart) (S : List String) (f : Frontier) (to fr : String) (h : ReachableFrontier c S f)
    (hto : Reaches c S to) : ReachableFrontier c S (visit f to fr) := by
  unfold visit
  split
  · exact h
  · refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · simp only [seen, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact h.1 v hv
      · exact hto
    · simp only [List.mem_append, List.mem_singleton] at hv
      simp only [seen, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]
      rcases hv with hv | rfl
      · exact .inl (h.2 v hv)
      · exact .inr rfl

theorem visitAll_reachable (c : Chart) (S : List String) (s : String) :
    ∀ (lands : List String) (f : Frontier), ReachableFrontier c S f → (∀ to ∈ lands, Reaches c S to) →
      ReachableFrontier c S (visitAll s f lands)
  | [], _, h, _ => h
  | x :: xs, f, h, hr => by
    simp only [visitAll, List.foldl_cons]
    exact visitAll_reachable c S s xs (visit f x s) (visit_reachable c S f x s h (hr x (by simp)))
      (fun to hto => hr to (List.mem_cons_of_mem _ hto))

theorem expand_reachable (c : Chart) (S : List String) (s : String) (f : Frontier) (h : ReachableFrontier c S f)
    (hs : Reaches c S s) : ReachableFrontier c S (expand (edges c) s f) := by
  have fold : ∀ (es : List Edge), (∀ e ∈ es, e ∈ edges c ∧ e.«from» = s) → ∀ f, ReachableFrontier c S f →
      ReachableFrontier c S (es.foldl (fun f e => visitAll s f e.lands) f) := by
    intro es
    induction es with
    | nil => intro _ f h; exact h
    | cons e es ih =>
      intro hes f h
      simp only [List.foldl_cons]
      obtain ⟨he, hfrom⟩ := hes e (by simp)
      refine ih (fun e' h' => hes e' (List.mem_cons_of_mem _ h')) _
        (visitAll_reachable c S s e.lands f h fun to hto => ?_)
      rw [← hfrom] at hs
      exact .step hs (succ_of_edge c e he to hto)
  exact fold _ (fun e he => by simpa using List.mem_filter.mp he) f h

theorem search_cycle (c : Chart) (S : List String) (start : String) (f : Frontier) (hf : ReachableFrontier c S f)
    (predecessors : List (String × String)) (h : search (edges c) start f = .cycle predecessors) :
    Reaches c S start := by
  match f, hf, h with
  | ([], _), _, h => simp [search] at h
  | (s :: rest, prev), hf, h =>
    rw [search] at h
    have hs : Reaches c S s := hf.1 s (hf.2 s (by simp))
    split at h
    · rename_i hst
      simp only [beq_iff_eq] at hst
      exact hst ▸ hs
    · have hrest : ReachableFrontier c S (rest, prev) := ⟨hf.1, fun v hv => hf.2 v (List.mem_cons_of_mem _ hv)⟩
      exact search_cycle c S start _ (expand_reachable c S s _ hrest hs) predecessors h
termination_by (unvisited ((edges c).flatMap (·.lands)) f, f.1.length)
decreasing_by
  rcases expand_progress (edges c) s (rest, prev) with e | lt
  · rw [e]; exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (by simpa [unvisited] using lt)

theorem searchFrom_cycle (c : Chart) (e : Edge) (predecessors : List (String × String))
    (h : searchFrom (edges c) e = .cycle predecessors) : Reaches c e.lands e.«from» :=
  search_cycle c e.lands e.«from» _
    (visitAll_reachable c e.lands e.«from» e.lands ([], [])
      ⟨fun _ hv => by simp [seen] at hv, fun _ hv => by simp at hv⟩ fun _ hto => .base hto)
    predecessors h

theorem cyclePath_returns (c : Chart) (path : List String) (h : cyclePath c = some path) :
    ∃ st ∈ c.states, ∃ t ∈ st.transitions, t.trigger = .always ∧ t.guarded = false ∧
      Reaches c (lands c st.name t) st.name := by
  simp only [cyclePath] at h
  obtain ⟨e, he, hsome⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨hedge, hg⟩ := List.mem_filter.mp he
  have hreach : Reaches c e.lands e.«from» := by
    split at hsome
    · rename_i predecessors hcycle
      exact searchFrom_cycle c e predecessors hcycle
    · exact absurd hsome (by simp)
  simp only [edges, List.mem_flatMap, List.mem_map, List.mem_filter] at hedge
  obtain ⟨st, hst, t, ⟨ht, hk⟩, rfl⟩ := hedge
  exact ⟨st, hst, t, ht, by simpa using hk, by simpa using hg, hreach⟩

theorem unguarded_always_does_not_return (s : Structure) :
    alwaysCycles s = [] ↔
      ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ st ∈ c.states, ∀ t ∈ st.transitions,
        t.trigger = .always → t.guarded = false → ¬ Reaches c (lands c st.name t) st.name := by
  constructor
  · intro halways d hd c hc st hst t ht ha hg
    have hnone := List.filterMap_eq_nil_iff.mp halways d hd
    simp only [hc, Option.bind_some, Option.map_eq_none_iff] at hnone
    have hfind := List.findSome?_eq_none_iff.mp hnone
    let e : Edge := { «from» := st.name, lands := lands c st.name t, guarded := t.guarded }
    have he : e ∈ (edges c).filter (!·.guarded) := by
      refine List.mem_filter.mpr ⟨?_, by simp [e, hg]⟩
      simp only [edges, List.mem_flatMap, List.mem_map, List.mem_filter]
      exact ⟨st, hst, t, ⟨ht, by simp [ha]⟩, rfl⟩
    have hsearch : searchFrom (edges c) e = .none := by
      have := hfind e he
      split at this
      · exact absurd this (by simp)
      · assumption
    exact searchFrom_none c e hsearch
  · intro h
    refine List.filterMap_eq_nil_iff.mpr fun d hd => ?_
    cases hc : d.chart? with
    | none => rfl
    | some c =>
      simp only [Option.bind_some, Option.map_eq_none_iff]
      cases hp : cyclePath c with
      | none => rfl
      | some path =>
        obtain ⟨st, hst, t, ht, ha, hg, hr⟩ := cyclePath_returns c path hp
        exact absurd hr (h d hd c hc st hst t ht ha hg)

end Tazuna.Thm.Validation.Charts
