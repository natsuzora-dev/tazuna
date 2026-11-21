import Tazuna.Explore.Search
import Tazuna.Thm.Guarantee

/-!
Merging the paths whose states have equal fingerprints loses no report, when equal fingerprints mean the same reports
on every continuation, up to what the path to a state already reported. Breadth-first order extends each fingerprint
first at its shallowest depth, so the state kept has at least as many inputs left as any state merged into it.
-/

namespace Tazuna.Thm.Explore.Search

open Tazuna.Explore

variable {S I R K : Type} [DecidableEq K] (sp : Space S I R) (fp : S → K)

theorem tree_mono {j k : Nat} (h : j ≤ k) (s : S) (r : R) (hr : r ∈ sp.tree j s) : r ∈ sp.tree k s := by
  induction j generalizing k s with
  | zero => simp [Space.tree] at hr
  | succ j ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Space.tree, List.mem_append, List.mem_flatMap] at hr ⊢
    rcases hr with hr | ⟨i, hi, hr | hr⟩
    · exact Or.inl hr
    · exact Or.inr ⟨i, hi, Or.inl hr⟩
    · exact Or.inr ⟨i, hi, Or.inr (ih (by omega) _ hr)⟩

theorem merged_mono {j k : Nat} (h : j ≤ k) (F : List S) (V : List K) (r : R) (hr : r ∈ sp.merged fp j F V) :
    r ∈ sp.merged fp k F V := by
  induction j generalizing k F V with
  | zero => simp [Space.merged] at hr
  | succ j ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Space.merged, List.mem_append] at hr ⊢
    rcases hr with hr | hr
    · exact Or.inl hr
    · exact Or.inr (ih (by omega) _ _ hr)

theorem mem_of_mem_fresh {V : List K} {F : List S} {s : S} (h : s ∈ fresh fp V F) : s ∈ F := by
  induction F generalizing V with
  | nil => simp [fresh] at h
  | cons x xs ih =>
    simp only [fresh] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- Each state of a layer is visited already, or has a kept state with its fingerprint. -/
theorem fresh_covers {V : List K} {F : List S} {s : S} (h : s ∈ F) : fp s ∈ V ∨ ∃ f ∈ fresh fp V F, fp f = fp s := by
  induction F generalizing V with
  | nil => simp at h
  | cons x xs ih =>
    simp only [fresh]
    rcases List.mem_cons.mp h with rfl | h
    · split
      · exact Or.inl ‹_›
      · exact Or.inr ⟨s, List.mem_cons_self, rfl⟩
    · split
      · exact ih h
      · rcases ih (V := fp x :: V) h with h | ⟨f, hf, e⟩
        · rcases List.mem_cons.mp h with e | h
          · exact Or.inr ⟨x, List.mem_cons_self, e.symm⟩
          · exact Or.inl h
        · exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, e⟩

/-- Everything the merged search reports from a frontier is in `T` when every path from the frontier reports into `T`. -/
theorem merged_sound (T : List R) : ∀ (k : Nat) (F : List S) (V : List K),
    (∀ s ∈ F, ∀ r ∈ sp.tree k s, r ∈ T) → ∀ r ∈ sp.merged fp k F V, r ∈ T := by
  intro k
  induction k with
  | zero => intro F V _ r hr; simp [Space.merged] at hr
  | succ k ih =>
    intro F V hF r hr
    simp only [Space.merged, List.mem_append, List.mem_flatMap] at hr
    rcases hr with ⟨s, hs, hr⟩ | hr
    · apply hF s (mem_of_mem_fresh fp hs)
      simp only [Space.tree, List.mem_append, List.mem_flatMap] at hr ⊢
      rcases hr with hr | ⟨i, hi, hr⟩
      · exact Or.inl hr
      · exact Or.inr ⟨i, hi, Or.inl hr⟩
    · refine ih _ _ (fun c hc r hr => ?_) r hr
      simp only [List.mem_flatMap, List.mem_map] at hc
      obtain ⟨s, hs, i, hi, rfl⟩ := hc
      apply hF s (mem_of_mem_fresh fp hs)
      simp only [Space.tree, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨i, hi, Or.inr hr⟩

/--
What `past` gives a state comes from what the path to it reported: a child's past is in its parent's past or in what
extending the parent and taking the child's input reported.
-/
def PastReported (past : S → List R) : Prop :=
  ∀ s i, i ∈ sp.next s → ∀ r ∈ past (sp.step s i), r ∈ past s ∨ r ∈ sp.here s ∨ r ∈ sp.out s i

/--
States with equal fingerprints report alike from here on: whatever `a` reports on its paths of up to `k` inputs, `b`
reports on its own or its path reported already (`past b`).
-/
def Congruent (past : S → List R) : Prop :=
  ∀ a b k, fp a = fp b → ∀ r, r ∈ sp.tree k a → r ∈ sp.tree k b ∨ r ∈ past b

/--
Every path from a frontier reports into `T` when the merged search from it does, every visited fingerprint's paths do,
and the frontier's pasts are in `T`. The paths of a kept state reach the next layer, whose own visited fingerprints
need the kept states' shallower paths, so the induction is strong.
-/
theorem merged_complete (past : S → List R) (hpast : PastReported sp past) (congruent : Congruent sp fp past)
    (T : List R) : ∀ (k : Nat) (F : List S) (V : List K), (∀ r ∈ sp.merged fp k F V, r ∈ T) →
      (∀ s, fp s ∈ V → ∀ r ∈ sp.tree k s, r ∈ T) → (∀ f ∈ F, ∀ r ∈ past f, r ∈ T) →
      ∀ s ∈ F, ∀ r ∈ sp.tree k s, r ∈ T := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro F V hM hV hF s hs r hr
  rcases k with _ | k
  · simp [Space.tree] at hr
  have hM' : ∀ r ∈ sp.merged fp k (((fresh fp V F)).flatMap fun s => (sp.next s).map (sp.step s))
      (V ++ (fresh fp V F).map fp), r ∈ T := fun r h => hM r (by
    simp only [Space.merged, List.mem_append]; exact Or.inr h)
  have hHere : ∀ f ∈ fresh fp V F, ∀ r ∈ sp.here f, r ∈ T := fun f hf r h => hM r (by
    simp only [Space.merged, List.mem_append, List.mem_flatMap]; exact Or.inl ⟨f, hf, Or.inl h⟩)
  have hOut : ∀ f ∈ fresh fp V F, ∀ i ∈ sp.next f, ∀ r ∈ sp.out f i, r ∈ T := fun f hf i hi r h => hM r (by
    simp only [Space.merged, List.mem_append, List.mem_flatMap]; exact Or.inl ⟨f, hf, Or.inr ⟨i, hi, h⟩⟩)
  have hKept : ∀ f ∈ fresh fp V F, ∀ r ∈ past f, r ∈ T := fun f hf => hF f (mem_of_mem_fresh fp hf)
  have hNext : ∀ c ∈ (fresh fp V F).flatMap (fun s => (sp.next s).map (sp.step s)), ∀ r ∈ past c, r ∈ T := by
    intro c hc r hr
    obtain ⟨g, hg, i, hi, rfl⟩ := by simpa only [List.mem_flatMap, List.mem_map] using hc
    rcases hpast g i hi r hr with h | h | h
    · exact hKept g hg r h
    · exact hHere g hg r h
    · exact hOut g hg i hi r h
  have hC : ∀ j, j ≤ k + 1 → ∀ f ∈ fresh fp V F, ∀ r ∈ sp.tree j f, r ∈ T := by
    intro j
    induction j with
    | zero => intro _ f _ r hr; simp [Space.tree] at hr
    | succ j ihj =>
      intro hj f hf r hr
      simp only [Space.tree, List.mem_append, List.mem_flatMap] at hr
      rcases hr with hr | ⟨i, hi, hr | hr⟩
      · exact hHere f hf r hr
      · exact hOut f hf i hi r hr
      · refine ih j (by omega) _ _ (fun r h => hM' r (merged_mono sp fp (by omega) _ _ r h)) ?_ hNext
          (sp.step f i) ?_ r hr
        · intro s hs r hr
          rcases List.mem_append.mp hs with hs | hs
          · exact hV s hs r (tree_mono sp (by omega) s r hr)
          · obtain ⟨g, hg, e⟩ := List.mem_map.mp hs
            rcases congruent s g j e.symm r hr with h | h
            · exact ihj (by omega) g hg r h
            · exact hKept g hg r h
        · exact List.mem_flatMap.mpr ⟨f, hf, List.mem_map.mpr ⟨i, hi, rfl⟩⟩
  rcases fresh_covers fp (V := V) hs with h | ⟨f, hf, e⟩
  · exact hV s h r hr
  · rcases congruent s f (k + 1) e.symm r hr with h | h
    · exact hC (k + 1) (Nat.le_refl _) f hf r h
    · exact hKept f hf r h

/--
Explore's search, which extends only the first state of each fingerprint, reports exactly what extending every path of
up to `bound` inputs reports, when states with equal fingerprints report alike from here on (Congruent), up to what
the path to the state kept already reported (`past`, empty at the start).
-/
@[guarantee] theorem merged_search_reports (past : S → List R) (hpast : PastReported sp past)
    (congruent : Congruent sp fp past) (bound : Nat) (start : S) (hstart : past start = []) (r : R) :
    r ∈ sp.merged fp bound [start] [] ↔ r ∈ sp.tree bound start := by
  constructor
  · exact merged_sound sp fp (sp.tree bound start) bound [start] []
      (fun s hs r hr => by simp only [List.mem_singleton] at hs; subst hs; exact hr) r
  · exact merged_complete sp fp past hpast congruent _ bound [start] [] (fun _ h => h) (fun _ hs => by simp at hs)
      (fun f hf r hr => by simp only [List.mem_singleton] at hf; subst hf; simp [hstart] at hr) start
      (List.mem_singleton_self start) r

end Tazuna.Thm.Explore.Search
