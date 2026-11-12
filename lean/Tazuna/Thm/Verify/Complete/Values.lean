import Tazuna.Thm.Verify.Compare
import Tazuna.Thm.Verify.Matching

namespace Tazuna.Thm.Verify.Complete.Values

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching

/-- `M` keeps every binding of `m`, possibly with more implementation values. -/
def Ext (m M : Bindings) : Prop := ∀ k ws, m.lookup k = some ws → ∃ ws', M.lookup k = some ws' ∧ ∀ w ∈ ws, w ∈ ws'

theorem Ext.refl (m : Bindings) : Ext m m := fun _ ws h => ⟨ws, h, fun _ hw => hw⟩

theorem Ext.trans {a b c : Bindings} (h₁ : Ext a b) (h₂ : Ext b c) : Ext a c := by
  intro k ws h
  obtain ⟨ws', h', hs⟩ := h₁ k ws h
  obtain ⟨ws'', h'', hs'⟩ := h₂ k ws' h'
  exact ⟨ws'', h'', fun w hw => hs' w (hs w hw)⟩

/-- A key's first value is its implementation value, and its other values are the key itself. -/
def Tail (m : Bindings) : Prop := ∀ k ws, (k, ws) ∈ m → ∃ w rest, ws = w :: rest ∧ ∀ x ∈ rest, x = k

/-- The invariant of the bindings, with `d` the declared createKey values. -/
structure Wf (d : List String) (m : Bindings) : Prop where
  keys : (m.map (·.1)).Nodup
  disjoint : ∀ k₁ ws₁ k₂ ws₂ w, (k₁, ws₁) ∈ m → (k₂, ws₂) ∈ m → w ∈ ws₁ → w ∈ ws₂ → k₁ = k₂
  tail : Tail m
  declared : ∀ k ws, (k, ws) ∈ m → k ∈ d

theorem Wf.empty (d : List String) : Wf d [] := ⟨by simp, by simp, by simp [Tail], by simp⟩

theorem Wf.mono {d d' : List String} {m : Bindings} (h : Wf d m) (hd : ∀ x ∈ d, x ∈ d') : Wf d' m :=
  ⟨h.keys, h.disjoint, h.tail, fun k ws hm => hd k (h.declared k ws hm)⟩

/-- The implementation value of each snapshot createKey value. -/
def rename (m : Bindings) (s : String) : Option String := (m.lookup s).bind List.head?

theorem mem_of_lookup {β : Type} : ∀ {m : List (String × β)} {k : String} {v : β}, m.lookup k = some v → (k, v) ∈ m
  | [], _, _, h => by simp at h
  | (a, b) :: rest, k, v, h => by
    by_cases e : k = a
    · subst e; simp only [List.lookup_cons, beq_self_eq_true] at h; cases h; simp
    · have : (k == a) = false := by simpa using e
      simp only [List.lookup_cons, this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem lookup_none_iff {β : Type} : ∀ {m : List (String × β)} {k : String}, m.lookup k = none ↔ k ∉ m.map (·.1)
  | [], _ => by simp
  | (a, b) :: rest, k => by
    by_cases e : k = a
    · subst e; simp
    · have : (k == a) = false := by simpa using e
      simp only [List.lookup_cons, this, List.map_cons, List.mem_cons, e, false_or]
      exact lookup_none_iff

theorem lookup_of_mem' {β : Type} : ∀ {m : List (String × β)} {k : String} {v : β},
    (m.map (·.1)).Nodup → (k, v) ∈ m → m.lookup k = some v
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (a, b) :: rest, k, v, hn, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp h with e | e
    · cases e; simp
    · have hne : k ≠ a := fun hk => hn.1 ⟨(k, v), e, hk⟩
      have : (k == a) = false := by simpa using hne
      simp only [List.lookup_cons, this]
      exact lookup_of_mem' hn.2 e

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 a ha rfl, nodup_of_map f h.2⟩

theorem eq_of_map_nodup {α β : Type} (f : α → β) :
    ∀ {l : List α} {a b : α}, (l.map f).Nodup → a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, a, b, h, ha, hb, e => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · rw [ha'] at e; exact absurd e.symm (fun e' => h.1 b hb' e')
    · rw [hb'] at e; exact absurd e (fun e' => h.1 a ha' e')
    · exact eq_of_map_nodup f h.2 ha' hb' e

theorem value_of_ext {m M : Bindings} (hM : Tail M) (he : Ext m M) {v w : String} {same : List String}
    (hl : m.lookup v = some same) (hw : w ∈ same) : w = v ∨ rename M v = some w := by
  obtain ⟨ws', h', hs⟩ := he v same hl
  obtain ⟨h, rest, e, hr⟩ := hM v ws' (mem_of_lookup h')
  subst e
  rcases List.mem_cons.mp (hs w hw) with e | e
  · right; simp [rename, h', e]
  · left; exact hr w e

theorem map_fst_setAt {β : Type} : ∀ (m : List (String × β)) (k : String) (v : β),
    (setAt m k v).map (·.1) = if k ∈ m.map (·.1) then m.map (·.1) else m.map (·.1) ++ [k]
  | [], k, v => by simp [setAt]
  | (a, b) :: rest, k, v => by
    by_cases e : a = k
    · subst e; simp [setAt]
    · have : (a == k) = false := by simpa using e
      simp only [setAt, this, Bool.false_eq_true, ite_false, List.map_cons]
      rw [map_fst_setAt rest k v]
      by_cases hk : k ∈ rest.map (·.1) <;> simp [hk, Ne.symm e]

/-- The entries of `setAt m k v`, when the keys of `m` are distinct. -/
theorem mem_setAt {β : Type} : ∀ {m : List (String × β)} {k k' : String} {v v' : β},
    (m.map (·.1)).Nodup → (k', v') ∈ setAt m k v → (k' = k ∧ v' = v) ∨ ((k', v') ∈ m ∧ k' ≠ k)
  | [], k, k', v, v', _, h => by simp [setAt] at h; left; exact h
  | (a, b) :: rest, k, k', v, v', hn, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    by_cases e : a = k
    · subst e
      simp only [setAt, beq_self_eq_true, ite_true, List.mem_cons, Prod.mk.injEq] at h
      rcases h with h | h
      · left; exact h
      · right
        exact ⟨List.mem_cons_of_mem _ h, fun hk => hn.1 ⟨(k', v'), h, hk⟩⟩
    · have : (a == k) = false := by simpa using e
      simp only [setAt, this, Bool.false_eq_true, ite_false, List.mem_cons] at h
      rcases h with h | h
      · right; cases h; exact ⟨List.mem_cons_self, e⟩
      · rcases mem_setAt hn.2 h with h | h
        · left; exact h
        · right; exact ⟨List.mem_cons_of_mem _ h.1, h.2⟩

theorem setAt_nodup {β : Type} {m : List (String × β)} (k : String) (v : β) (hn : (m.map (·.1)).Nodup) :
    ((setAt m k v).map (·.1)).Nodup := by
  rw [map_fst_setAt]
  split
  · exact hn
  · rename_i h
    exact List.nodup_append.mpr ⟨hn, by simp, by simp only [List.mem_singleton]; rintro a ha b rfl rfl; exact h ha⟩

theorem not_standsForOther {m : Bindings} {v w : String} (h : standsForOther m v w = false) :
    ∀ k ws, (k, ws) ∈ m → w ∈ ws → k = v := by
  intro k ws hm hw
  simp only [standsForOther, List.any_eq_false] at h
  have := h (k, ws) hm
  by_cases hk : k = v
  · exact hk
  · exact absurd (by simp [hk, hw]) this

theorem Ext.setAt_new {m : Bindings} {v : String} (ws : List String) (hl : m.lookup v = none) :
    Ext m (setAt m v ws) := by
  intro k vs h
  refine ⟨vs, ?_, fun _ hw => hw⟩
  rw [lookup_setAt]
  have : k ≠ v := by rintro rfl; rw [hl] at h; cases h
  simp [this, h]

theorem Ext.setAt_append {m : Bindings} {v : String} {same : List String} (x : String)
    (hl : m.lookup v = some same) : Ext m (setAt m v (same ++ [x])) := by
  intro k vs h
  rw [lookup_setAt]
  by_cases e : k = v
  · subst e; rw [hl] at h; cases h; exact ⟨same ++ [x], by simp, fun w hw => List.mem_append_left _ hw⟩
  · exact ⟨vs, by simp [e, h], fun _ hw => hw⟩

theorem Wf.setAt_new {d : List String} {m : Bindings} (h : Wf d m) {v w : String}
    (hs : standsForOther m v w = false) (hd : v ∈ d) : Wf d (setAt m v [w]) := by
  have hn := h.keys
  have hother := not_standsForOther hs
  refine ⟨setAt_nodup _ _ hn, ?_, ?_, ?_⟩
  · intro k₁ ws₁ k₂ ws₂ x h₁ h₂ hx₁ hx₂
    have back : ∀ k ws, (k, ws) ∈ setAt m v [w] → x ∈ ws → (k = v ∧ x = w) ∨ ((k, ws) ∈ m ∧ k ≠ v ∧ x ∈ ws) := by
      intro k ws hm hx
      rcases mem_setAt hn hm with ⟨hk, hw⟩ | ⟨hm, hk⟩
      · left; subst hw; simpa [hk] using hx
      · right; exact ⟨hm, hk, hx⟩
    rcases back _ _ h₁ hx₁ with ⟨hk₁, hx₁⟩ | ⟨h₁, hk₁, hx₁⟩ <;>
      rcases back _ _ h₂ hx₂ with ⟨hk₂, hx₂⟩ | ⟨h₂, hk₂, hx₂⟩
    · rw [hk₁, hk₂]
    · rw [hx₁] at hx₂; exact absurd (hother _ _ h₂ hx₂) hk₂
    · rw [hx₂] at hx₁; exact absurd (hother _ _ h₁ hx₁) hk₁
    · exact h.disjoint _ _ _ _ _ h₁ h₂ hx₁ hx₂
  · intro k ws hm
    rcases mem_setAt hn hm with ⟨_, hw⟩ | ⟨hm, _⟩
    · exact ⟨w, [], hw, by simp⟩
    · exact h.tail k ws hm
  · intro k ws hm
    rcases mem_setAt hn hm with ⟨hk, _⟩ | ⟨hm, _⟩
    · exact hk ▸ hd
    · exact h.declared k ws hm

theorem Wf.setAt_self {d : List String} {m : Bindings} (h : Wf d m) {v : String} {same : List String}
    (hl : m.lookup v = some same) (hs : standsForOther m v v = false) : Wf d (setAt m v (same ++ [v])) := by
  have hn := h.keys
  have hother := not_standsForOther hs
  have hmem := mem_of_lookup hl
  refine ⟨setAt_nodup _ _ hn, ?_, ?_, ?_⟩
  · intro k₁ ws₁ k₂ ws₂ x h₁ h₂ hx₁ hx₂
    have back : ∀ k ws, (k, ws) ∈ setAt m v (same ++ [v]) → x ∈ ws → (k = v ∧ (x ∈ same ∨ x = v)) ∨
        ((k, ws) ∈ m ∧ k ≠ v ∧ x ∈ ws) := by
      intro k ws hm hx
      rcases mem_setAt hn hm with ⟨hk, hw⟩ | ⟨hm, hk⟩
      · left; subst hw; simpa [hk] using hx
      · right; exact ⟨hm, hk, hx⟩
    rcases back _ _ h₁ hx₁ with ⟨hk₁, hx₁⟩ | ⟨h₁, hk₁, hx₁⟩ <;>
      rcases back _ _ h₂ hx₂ with ⟨hk₂, hx₂⟩ | ⟨h₂, hk₂, hx₂⟩
    · rw [hk₁, hk₂]
    · rw [hk₁]
      rcases hx₁ with hx₁ | hx₁
      · exact h.disjoint _ _ _ _ _ hmem h₂ hx₁ hx₂
      · rw [hx₁] at hx₂; exact absurd (hother _ _ h₂ hx₂) hk₂
    · rw [hk₂]
      rcases hx₂ with hx₂ | hx₂
      · exact h.disjoint _ _ _ _ _ h₁ hmem hx₁ hx₂
      · rw [hx₂] at hx₁; exact absurd (hother _ _ h₁ hx₁) hk₁
    · exact h.disjoint _ _ _ _ _ h₁ h₂ hx₁ hx₂
  · intro k ws hm
    rcases mem_setAt hn hm with ⟨hk, hw⟩ | ⟨hm, _⟩
    · obtain ⟨w, rest, e, hr⟩ := h.tail _ _ hmem
      subst e hw hk
      exact ⟨w, rest ++ [k], rfl, by intro x hx; simp only [List.mem_append, List.mem_singleton] at hx; grind⟩
    · exact h.tail k ws hm
  · intro k ws hm
    rcases mem_setAt hn hm with ⟨hk, _⟩ | ⟨hm, _⟩
    · exact hk ▸ h.declared _ _ hmem
    · exact h.declared k ws hm

/-- The bindings grow and keep their invariant. -/
def Grows (d : List String) (m m' : Bindings) : Prop := Wf d m' ∧ Ext m m'

theorem Grows.refl {d : List String} {m : Bindings} (h : Wf d m) : Grows d m m := ⟨h, Ext.refl m⟩

theorem Grows.trans {d : List String} {a b c : Bindings} (h₁ : Grows d a b) (h₂ : Grows d b c) : Grows d a c :=
  ⟨h₂.1, h₁.2.trans h₂.2⟩

theorem bindValues_grows (d : List String) (s : CValue) (t : Option CValue) (m : Bindings) (h : Wf d m) :
    Grows d m (bindValues d (some s) t m) := by
  by_cases hstr : ∃ v, s = .leaf (.str v)
  · obtain ⟨v, rfl⟩ := hstr
    by_cases ht : ∃ w, t = some (.leaf (.str w))
    · obtain ⟨w, rfl⟩ := ht
      rw [bindValues.eq_1]
      split
      · rename_i hc
        simp only [Bool.and_eq_true, List.contains_iff_mem, Option.isNone_iff_eq_none] at hc
        split
        · exact Grows.refl h
        · rename_i hs
          exact ⟨h.setAt_new (by simpa using hs) hc.1, Ext.setAt_new _ hc.2⟩
      · exact Grows.refl h
    · rw [bindValues.eq_2 _ _ _ _ (fun w e => ht ⟨w, e⟩)]
      split <;> exact Grows.refl h
  · cases t with
    | none =>
      rw [bindValues.eq_4 _ _ _ _ (fun v e => hstr ⟨v, by cases e; rfl⟩) (by simp)]
      exact Grows.refl h
    | some t =>
      rw [bindValues.eq_3 _ _ _ _ (fun v e => hstr ⟨v, e⟩)]
      split
      · apply foldl_preserve (fun b => Grows d m b) _ _ _ _ (Grows.refl h)
        rintro b ⟨k, hk⟩ _ hb
        dsimp only
        split
        · rename_i sv hs
          have := at?_sizeOf hs
          exact hb.trans (bindValues_grows d sv _ b hb.1)
        · exact hb
      · exact Grows.refl h
termination_by sizeOf s

theorem bindValues_grows' (d : List String) (s t : Option CValue) (m : Bindings) (h : Wf d m) :
    Grows d m (bindValues d s t m) := by
  cases s with
  | some s => exact bindValues_grows d s t m h
  | none => rw [bindValues.eq_4 _ _ _ _ (by simp) (by simp)]; exact Grows.refl h

mutual

theorem equal_grows (d : List String) (s t : CValue) (m : Bindings) (b : Bool) (h : Wf d m) :
    Grows d m (equal d s t m b).2 := by
  match s with
  | .leaf (.str v) =>
    rw [equal.eq_def]; dsimp only
    split
    · rename_i same hl
      split
      · rename_i w
        split
        · exact Grows.refl h
        · split
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
            exact ⟨h.setAt_self hl hc.2, Ext.setAt_append _ hl⟩
          · exact Grows.refl h
      · exact Grows.refl h
    · exact Grows.refl h
  | .leaf .null | .leaf (.bool _) | .leaf (.num _) | .leaf (.arr _) | .leaf (.obj _) =>
    rw [equal.eq_def]; dsimp only; exact Grows.refl h
  | .runs rs =>
    rw [equal.eq_def]; dsimp only
    split
    · split
      · exact equalList_grows d rs _ m b h
      · exact Grows.refl h
    · exact Grows.refl h
  | .arr xs =>
    rw [equal.eq_def]; dsimp only
    split
    · split
      · exact equalList_grows d xs _ m b h
      · exact Grows.refl h
    · exact Grows.refl h
  | .bag xs =>
    rw [equal.eq_def]; dsimp only
    split
    · rename_i ys
      split
      · rename_i matched hm
        exact matchBag_grows d xs ys m b matched h hm
      · exact Grows.refl h
    · exact Grows.refl h
  | .obj fs =>
    rw [equal.eq_def]; dsimp only
    split
    · split
      · exact equalFields_grows d fs _ m b h
      · exact Grows.refl h
    · exact Grows.refl h
termination_by (sizeOf s, 0)
decreasing_by all_goals lex_decreasing

theorem equalList_grows (d : List String) (xs ys : List CValue) (m : Bindings) (b : Bool) (h : Wf d m) :
    Grows d m (equalList d xs ys m b).2 := by
  match xs, ys with
  | [], [] => rw [equalList.eq_def]; dsimp only; exact Grows.refl h
  | x :: xs, y :: ys =>
    rw [equalList.eq_def]; dsimp only
    have hx := equal_grows d x y m b h
    split
    · rename_i m' e
      rw [e] at hx
      exact hx.trans (equalList_grows d xs ys m' b hx.1)
    · rename_i m' e
      rw [e] at hx; exact hx
  | [], _ :: _ => rw [equalList.eq_def]; dsimp only; exact Grows.refl h
  | _ :: _, [] => rw [equalList.eq_def]; dsimp only; exact Grows.refl h
termination_by (sizeOf xs, 0)
decreasing_by all_goals lex_decreasing

theorem equalFields_grows (d : List String) (fs gs : List (String × CValue)) (m : Bindings) (b : Bool)
    (h : Wf d m) : Grows d m (equalFields d fs gs m b).2 := by
  match fs with
  | [] => rw [equalFields.eq_def]; dsimp only; exact Grows.refl h
  | (k, v) :: fs =>
    rw [equalFields.eq_def]; dsimp only
    split
    · rename_i w _
      have hx := equal_grows d v w m b h
      split
      · rename_i m' e
        rw [e] at hx
        exact hx.trans (equalFields_grows d fs gs m' b hx.1)
      · rename_i m' e
        rw [e] at hx; exact hx
    · exact Grows.refl h
termination_by (sizeOf fs, 0)
decreasing_by all_goals lex_decreasing

theorem matchBag_grows (d : List String) (ss ts : List CValue) (m : Bindings) (b : Bool) (r : Bindings)
    (h : Wf d m) (hr : matchBag d ss ts m b = some r) : Grows d m r := by
  rw [matchBag.eq_def] at hr
  split at hr
  · cases hr
  · split at hr
    · cases hr; exact Grows.refl h
    · rename_i first rest
      exact matchBagFrom_grows d _ _ ts [] [] m b r h hr
termination_by (sizeOf ss, ts.length + 1)
decreasing_by all_goals lex_decreasing

theorem matchBagFrom_grows (d : List String) (first : CValue) (rest cands passed : List CValue) (tried : List Value)
    (m : Bindings) (b : Bool) (r : Bindings) (h : Wf d m)
    (hr : matchBagFrom d first rest cands passed tried m b = some r) : Grows d m r := by
  rw [matchBagFrom.eq_def] at hr; dsimp only at hr
  split at hr
  · cases hr
  · rename_i t more
    split at hr
    · exact matchBagFrom_grows d first rest more (t :: passed) tried m b r h hr
    · have ht := bindValues_grows d first (some t) m h
      have he := equal_grows d first t (bindValues d (some first) (some t) m) b ht.1
      split at hr
      · rename_i m' e
        rw [e] at he
        split at hr
        · rename_i r' e2
          simp only [Option.some.injEq] at hr; subst hr
          exact (ht.trans he).trans (matchBag_grows d rest _ m' b r' he.1 e2)
        · exact matchBagFrom_grows d first rest more (t :: passed) _ m b r h hr
      · exact matchBagFrom_grows d first rest more (t :: passed) _ m b r h hr
termination_by (sizeOf first + sizeOf rest + 1, cands.length)
decreasing_by all_goals lex_decreasing

end

/-- The values match under every growth of `m` that is the final bindings. -/
def MatchesAfter (m : Bindings) (s t : CValue) : Prop := ∀ M, Ext m M → Tail M → ValueMatches (rename M) s t

def ListMatchesAfter (m : Bindings) (xs ys : List CValue) : Prop :=
  ∀ M, Ext m M → Tail M → ListMatches (rename M) xs ys

theorem keys_iff {ks kt : List String} (h : (ks.length == kt.length && ks.all kt.contains && kt.all ks.contains) = true) :
    ∀ k, k ∈ ks ↔ k ∈ kt := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact fun k => ⟨h.1.2 k, h.2 k⟩

mutual

theorem equal_sound (d : List String) (s t : CValue) (m : Bindings) (b : Bool) (h : Wf d m)
    (he : (equal d s t m b).1 = true) : MatchesAfter (equal d s t m b).2 s t := by
  match s with
  | .leaf (.str v) =>
    revert he
    rw [equal.eq_def]; dsimp only
    split
    · rename_i same hl
      split
      · rename_i w
        split
        · rename_i hc
          intro _ M hM hT
          simp only [List.contains_iff_mem] at hc
          exact ⟨w, rfl, value_of_ext hT hM hl hc⟩
        · split
          · rename_i hc
            intro _ M _ _
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            exact ⟨w, rfl, Or.inl hc.1.2⟩
          · intro he; cases he
      · intro he; cases he
    · split
      · rename_i w
        intro he M _ _
        simp only [beq_iff_eq] at he
        subst he
        exact ⟨v, rfl, Or.inl rfl⟩
      · intro he; cases he
  | .leaf .null | .leaf (.bool _) | .leaf (.num _) | .leaf (.arr _) | .leaf (.obj _) =>
    rw [equal.eq_def] at he ⊢
    dsimp only at he ⊢
    intro M _ _
    simp only [ValueMatches]
    split at he
    · simp_all
    · simp at he
  | .runs rs =>
    rw [equal.eq_def] at he ⊢; dsimp only at he ⊢
    split at he
    · rename_i rt
      split at he
      · rename_i hl
        simp only [hl, ite_true] at he ⊢
        intro M hM hT
        exact ⟨rt, rfl, equalList_sound d rs rt m b h he M hM hT⟩
      · cases he
    · cases he
  | .arr xs =>
    rw [equal.eq_def] at he ⊢; dsimp only at he ⊢
    split at he
    · rename_i ys
      split at he
      · rename_i hl
        simp only [hl, ite_true] at he ⊢
        intro M hM hT
        exact ⟨ys, rfl, equalList_sound d xs ys m b h he M hM hT⟩
      · cases he
    · cases he
  | .bag xs =>
    rw [equal.eq_def] at he ⊢; dsimp only at he ⊢
    split at he
    · rename_i ys
      split at he
      · rename_i matched hm
        simp only
        obtain ⟨zs, hp, hz⟩ := matchBag_sound d xs ys m b matched h hm
        intro M hM hT
        exact ⟨ys, zs, rfl, hp, hz M hM hT⟩
      · cases he
    · cases he
  | .obj fs =>
    rw [equal.eq_def] at he ⊢; dsimp only at he ⊢
    split at he
    · rename_i gs
      split at he
      · rename_i hk
        simp only [hk, ite_true] at he ⊢
        intro M hM hT
        exact ⟨gs, rfl, keys_iff hk, equalFields_sound d fs gs m b h he M hM hT⟩
      · cases he
    · cases he
termination_by (sizeOf s, 0)
decreasing_by all_goals lex_decreasing

theorem equalList_sound (d : List String) (xs ys : List CValue) (m : Bindings) (b : Bool) (h : Wf d m)
    (he : (equalList d xs ys m b).1 = true) : ListMatchesAfter (equalList d xs ys m b).2 xs ys := by
  match xs, ys with
  | [], [] => intro _ _ _; simp [ListMatches]
  | x :: xs, y :: ys =>
    rw [equalList.eq_def] at he ⊢; dsimp only at he ⊢
    have hx := equal_sound d x y m b h
    have hg := equal_grows d x y m b h
    split at he
    · rename_i m' e
      rw [e] at hx hg
      have hr := equalList_sound d xs ys m' b hg.1 he
      have hr' := equalList_grows d xs ys m' b hg.1
      intro M hM hT
      exact ⟨hx rfl M (hr'.2.trans hM) hT, hr M hM hT⟩
    · cases he
  | [], _ :: _ => rw [equalList.eq_def] at he; cases he
  | _ :: _, [] => rw [equalList.eq_def] at he; cases he
termination_by (sizeOf xs, 0)
decreasing_by all_goals lex_decreasing

theorem equalFields_sound (d : List String) (fs gs : List (String × CValue)) (m : Bindings) (b : Bool)
    (h : Wf d m) (he : (equalFields d fs gs m b).1 = true) :
    ∀ M, Ext (equalFields d fs gs m b).2 M → Tail M → FieldsMatch (rename M) fs gs := by
  match fs with
  | [] => intro _ _ _; simp [FieldsMatch]
  | (k, v) :: fs =>
    revert he
    rw [equalFields.eq_def]; dsimp only
    split
    · rename_i w hw
      have hx := equal_sound d v w m b h
      have hg := equal_grows d v w m b h
      split
      · rename_i m' e
        rw [e] at hx hg
        intro he
        have hr := equalFields_sound d fs gs m' b hg.1 he
        have hr' := equalFields_grows d fs gs m' b hg.1
        intro M hM hT
        exact ⟨⟨w, hw, hx rfl M (hr'.2.trans hM) hT⟩, hr M hM hT⟩
      · intro he; cases he
    · intro he; cases he
termination_by (sizeOf fs, 0)
decreasing_by all_goals lex_decreasing

theorem matchBag_sound (d : List String) (ss ts : List CValue) (m : Bindings) (b : Bool) (r : Bindings)
    (h : Wf d m) (hr : matchBag d ss ts m b = some r) : ∃ zs, ts.Perm zs ∧ ListMatchesAfter r ss zs := by
  rw [matchBag.eq_def] at hr
  split at hr
  · cases hr
  · rename_i hl
    split at hr
    · cases hr
      have : ts = [] := List.length_eq_zero_iff.mp (by simp at hl; omega)
      subst this
      exact ⟨[], List.Perm.refl _, fun _ _ _ => by simp [ListMatches]⟩
    · obtain ⟨zs, hp, hz⟩ := matchBagFrom_sound d _ _ ts [] [] m b r h hr
      exact ⟨zs, by simpa using hp, hz⟩
termination_by (sizeOf ss, ts.length + 1)
decreasing_by all_goals lex_decreasing

theorem matchBagFrom_sound (d : List String) (first : CValue) (rest cands passed : List CValue) (tried : List Value)
    (m : Bindings) (b : Bool) (r : Bindings) (h : Wf d m)
    (hr : matchBagFrom d first rest cands passed tried m b = some r) :
    ∃ zs, (passed.reverse ++ cands).Perm zs ∧ ListMatchesAfter r (first :: rest) zs := by
  rw [matchBagFrom.eq_def] at hr; dsimp only at hr
  split at hr
  · cases hr
  · rename_i t more
    have shift : (t :: passed).reverse ++ more = passed.reverse ++ t :: more := by simp
    split at hr
    · rw [← shift]; exact matchBagFrom_sound d first rest more (t :: passed) tried m b r h hr
    · have ht := bindValues_grows d first (some t) m h
      have hx := equal_sound d first t (bindValues d (some first) (some t) m) b ht.1
      have he := equal_grows d first t (bindValues d (some first) (some t) m) b ht.1
      split at hr
      · rename_i m' e
        rw [e] at hx he
        split at hr
        · rename_i r' e2
          simp only [Option.some.injEq] at hr; subst hr
          obtain ⟨zs, hp, hz⟩ := matchBag_sound d rest _ m' b r' he.1 e2
          have hg := matchBag_grows d rest _ m' b r' he.1 e2
          refine ⟨t :: zs, ?_, fun M hM hT => ⟨hx rfl M (hg.2.trans hM) hT, hz M hM hT⟩⟩
          exact List.perm_middle.trans (hp.cons t)
        · rw [← shift]; exact matchBagFrom_sound d first rest more (t :: passed) _ m b r h hr
      · rw [← shift]; exact matchBagFrom_sound d first rest more (t :: passed) _ m b r h hr
termination_by (sizeOf first + sizeOf rest + 1, cands.length)
decreasing_by all_goals lex_decreasing

end

theorem equalContent_grows (d : List String) (s t : Option CValue) (m : Bindings) (b : Bool) (h : Wf d m) :
    Grows d m (equalContent d s t m b).2 := by
  unfold equalContent
  split
  · exact equal_grows d _ _ m b h
  · exact Grows.refl h
  · exact Grows.refl h

/-- The values match under every growth of the bindings. -/
def ContentAfter (m : Bindings) (s t : Option CValue) : Prop :=
  ∀ M, Ext m M → Tail M → ContentMatches (rename M) s t

theorem ContentAfter.mono {m m' : Bindings} {s t : Option CValue} (h : ContentAfter m s t) (he : Ext m m') :
    ContentAfter m' s t := fun M hM hT => h M (he.trans hM) hT

theorem equalContent_sound (d : List String) (s t : Option CValue) (m : Bindings) (b : Bool) (h : Wf d m)
    (he : (equalContent d s t m b).1 = true) : ContentAfter (equalContent d s t m b).2 s t := by
  unfold equalContent at he ⊢
  split
  · rename_i s t
    simp only at he
    exact fun M hM hT => equal_sound d s t m b h he M hM hT
  · exact fun _ _ _ => trivial
  · rename_i hn hs
    simp only at he
    cases s <;> cases t <;> simp_all

theorem tryEqual_grows (d : List String) (s t : Option CValue) (m : Bindings) (h : Wf d m) :
    Grows d m (tryEqual d s t m).2 := by
  have hb := bindValues_grows' d s t m h
  exact hb.trans (equalContent_grows d s t _ false hb.1)

theorem tryEqual_sound (d : List String) (s t : Option CValue) (m : Bindings) (h : Wf d m)
    (he : (tryEqual d s t m).1 = true) : ContentAfter (tryEqual d s t m).2 s t :=
  equalContent_sound d s t _ false (bindValues_grows' d s t m h).1 he

mutual

/-- The value has no bag, so comparing it outside an `in` line binds nothing. -/
def NoBag : CValue → Prop
  | .leaf _ => True
  | .arr xs => NoBagList xs
  | .obj fs => NoBagFields fs
  | .bag _ | .runs _ => False

def NoBagList : List CValue → Prop
  | [] => True
  | x :: xs => NoBag x ∧ NoBagList xs

def NoBagFields : List (String × CValue) → Prop
  | [] => True
  | (_, v) :: fs => NoBag v ∧ NoBagFields fs

end

mutual

theorem equal_noBag (d : List String) (s t : CValue) (m : Bindings) (h : NoBag s) : (equal d s t m false).2 = m := by
  match s with
  | .leaf (.str v) =>
    rw [equal.eq_def]; dsimp only
    split
    · split
      · split
        · rfl
        · split
          · rename_i hc; simp at hc
          · rfl
      · rfl
    · rfl
  | .leaf .null | .leaf (.bool _) | .leaf (.num _) | .leaf (.arr _) | .leaf (.obj _) =>
    rw [equal.eq_def]
  | .arr xs =>
    rw [equal.eq_def]; dsimp only
    split
    · split
      · exact equalList_noBag d xs _ m h
      · rfl
    · rfl
  | .obj fs =>
    rw [equal.eq_def]; dsimp only
    split
    · split
      · exact equalFields_noBag d fs _ m h
      · rfl
    · rfl
  | .bag _ | .runs _ => exact absurd h id
termination_by (sizeOf s, 0)
decreasing_by all_goals lex_decreasing

theorem equalList_noBag (d : List String) (xs ys : List CValue) (m : Bindings) (h : NoBagList xs) :
    (equalList d xs ys m false).2 = m := by
  match xs, ys with
  | [], [] => rw [equalList.eq_def]
  | x :: xs, y :: ys =>
    rw [equalList.eq_def]; dsimp only
    have hx := equal_noBag d x y m h.1
    split
    · rename_i m' e
      rw [e] at hx; subst hx
      exact equalList_noBag d xs ys _ h.2
    · rename_i m' e
      rw [e] at hx; exact hx
  | [], _ :: _ => rw [equalList.eq_def]
  | _ :: _, [] => rw [equalList.eq_def]
termination_by (sizeOf xs, 0)
decreasing_by all_goals lex_decreasing

theorem equalFields_noBag (d : List String) (fs gs : List (String × CValue)) (m : Bindings) (h : NoBagFields fs) :
    (equalFields d fs gs m false).2 = m := by
  match fs with
  | [] => rw [equalFields.eq_def]
  | (k, v) :: fs =>
    rw [equalFields.eq_def]; dsimp only
    split
    · rename_i w _
      have hx := equal_noBag d v w m h.1
      split
      · rename_i m' e
        rw [e] at hx; subst hx
        exact equalFields_noBag d fs gs _ h.2
      · rename_i m' e
        rw [e] at hx; exact hx
    · rfl
termination_by (sizeOf fs, 0)
decreasing_by all_goals lex_decreasing

end

theorem equalContent_noBag (d : List String) (s t : Option CValue) (m : Bindings) (h : ∀ v, s = some v → NoBag v) :
    (equalContent d s t m false).2 = m := by
  unfold equalContent
  split
  · exact equal_noBag d _ _ m (h _ rfl)
  · rfl
  · rfl

end Tazuna.Thm.Verify.Complete.Values
