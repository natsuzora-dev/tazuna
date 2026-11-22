import Tazuna.Verify.Compare
import Tazuna.Thm.Data.Binding
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Guarantee

/-!
What compareGroup decides: a group of `out` lines without a finding pairs every snapshot line with a trace line, one to
one, each pair comparing equal under the binding that the comparison carries on.
-/

namespace Tazuna.Thm.Verify.Compare

open Tazuna.Data Tazuna.Verify
open Tazuna.Thm.Data.Binding
open Tazuna.Thm.Data.Basic (foldl_bind_error foldl_bind_inv)
open Tazuna.Thm.Data.Renaming (Renamed Renamed.mono)

/-- Snapshot line `s` compares equal with trace line `t`, apart from their time, under a binding that `b` extends. -/
def ContentMatch (dom : String → String) (b : Binding) (s t : Line) : Prop :=
  ∃ (v : Values) (b₀ : Binding) (out : List (From b₀)) (c : From b₀),
    v.domain = dom ∧ matchContent v b₀ s t = some out ∧ c ∈ out ∧ c.val.Extends b

theorem ContentMatch.mono {dom : String → String} {b b' : Binding} {s t : Line} (h : b.Extends b') :
    ContentMatch dom b s t → ContentMatch dom b' s t
  | ⟨v, b₀, out, c, hd, hm, hc, he⟩ => ⟨v, b₀, out, c, hd, hm, hc, he.trans h⟩

/-- Two optional strings that are both absent or that `b` relates. -/
def OptBound (dom : String → String) (b : Binding) : Option String → Option String → Prop
  | none, none => True
  | some x, some y => BoundBy dom b x y
  | _, _ => False

theorem OptBound.mono {dom : String → String} {b b' : Binding} (h : b.Extends b') :
    {x y : Option String} → OptBound dom b x y → OptBound dom b' x y
  | none, none, _ => trivial
  | some _, some _, hb => BoundBy.mono h hb

theorem opt_bound {v : Values} {b : Binding} {x y : Option String} {out : List (From b)}
    (h : (match x, y with
      | none, none => some [⟨b, .refl b⟩]
      | some x, some y => v.bind b x y
      | _, _ => some [] : Matches b) = some out) {c : From b} (hc : c ∈ out) : OptBound v.domain c.val x y := by
  match x, y with
  | none, none => trivial
  | some x, some y => exact bind_bound h c hc
  | none, some _ | some _, none => cases h; cases hc

/--
What two lines that compare equal under `b` share: their type, direction and name; their ids, when the snapshot line is
an `in` line or an `out` request; the request they answer and their `resultOf`; and their content, renamed under `b`.
-/
@[guarantee] theorem contentMatch_renamed {dom : String → String} {b : Binding} {s t : Line} (h : ContentMatch dom b s t)
    (hd : ∀ x ∈ s.content, Distinct x) (he : ∀ y ∈ t.content, Distinct y) :
    s.fields = t.fields ∧ ((s.body.dir = .in ∨ s.isOutRequest = true) → BoundBy dom b s.body.id t.body.id) ∧
      OptBound dom b s.body.to? t.body.to? ∧ OptBound dom b s.body.resultOf? t.body.resultOf? ∧
      (s.content.isSome = t.content.isSome) ∧
      ∀ x ∈ s.content, ∀ y ∈ t.content, Renamed (BoundBy dom b) x y := by
  obtain ⟨v, b₀, out, c, rfl, hm, hc, hext⟩ := h
  unfold matchContent at hm
  split at hm
  · cases hm; cases hc
  · rename_i hf
    obtain ⟨l₁, hl₁, c₁, hc₁, l₂, hl₂, c₂, hc₂, e₂⟩ := mem_andThen hm hc
    obtain ⟨l₃, hl₃, c₃, hc₃, l₄, hl₄, c₄, hc₄, e₄⟩ := mem_andThen hl₂ hc₂
    obtain ⟨l₅, hl₅, c₅, hc₅, l₆, hl₆, c₆, hc₆, e₆⟩ := mem_andThen hl₄ hc₄
    have h₆ : c₆.val.Extends b := by rw [← e₆, ← e₄, ← e₂]; exact hext
    have h₅ : c₅.val.Extends b := c₆.property.trans h₆
    have h₃ : c₃.val.Extends b := c₅.property.trans h₅
    have h₁ : c₁.val.Extends b := c₃.property.trans h₃
    refine ⟨by simpa using hf, fun hdir => ?_, (opt_bound hl₃ hc₃).mono h₃, (opt_bound hl₅ hc₅).mono h₅, ?_, ?_⟩
    · split at hl₁
      · exact BoundBy.mono h₁ (bind_bound hl₁ c₁ hc₁)
      · rename_i hn
        exfalso; apply hn
        rcases hdir with hdir | hdir <;> simp [hdir]
    · unfold matchOption at hl₆
      split at hl₆
      · simp_all
      · simp_all
      · cases hl₆; cases hc₆
    · intro x hx y hy
      unfold matchOption at hl₆
      split at hl₆
      · simp_all
      · rename_i x' y' hx' hy'
        rw [hx'] at hx; rw [hy'] at hy
        cases hx; cases hy
        exact Renamed.mono (fun _ _ => BoundBy.mono h₆)
          (matchValue_renamed v c₅.val x y (hd x (by simp [hx'])) (he y (by simp [hy'])) hl₆ c₆ hc₆)
      · cases hl₆; cases hc₆

/-- The pair of line numbers `p` pairs a snapshot line with a trace line that compare equal under `b`. -/
def PairMatch (dom : String → String) (snapshot trace : List Numbered) (b : Binding) (p : Nat × Nat) : Prop :=
  ∃ s ∈ snapshot, s.index = p.1 ∧ ∃ t ∈ trace, t.index = p.2 ∧ ContentMatch dom b s.line t.line

/-- What every way holds: its pairs compare equal under its binding, except those of the snapshot lines `bad`, no trace line is paired twice, and its binding
extends a binding of the set that the group started from. -/
def WayInv {root : Binding} (dom : String → String) (set : List (From root)) (snapshot trace : List Numbered)
    (bad : List Nat) (st : State root) : Prop :=
  (st.pairs.map (·.2)).Nodup ∧ (∀ p ∈ st.pairs, PairMatch dom snapshot trace st.binding.val p ∨ p.1 ∈ bad) ∧
    ∃ c ∈ set, c.val.Extends st.binding.val

/-- What the exact pass holds after the snapshot lines `pre`: every way pairs each of them that did not fail. -/
def ExactInv {root : Binding} (dom : String → String) (set : List (From root)) (snapshot trace : List Numbered)
    (pre rest : List Numbered) (a : List (State root) × List Numbered) : Prop :=
  pre ++ rest = snapshot ∧ a.1 ≠ [] ∧ (∀ s ∈ a.2, s ∈ snapshot) ∧
    ∀ st ∈ a.1, ((st.pairs.map (·.1)) ++ a.2.map (·.index)).Perm (pre.map (·.index)) ∧
      WayInv dom set snapshot trace [] st

theorem paired_mem {root : Binding} {st : State root} {s t : Numbered} {cs : List (From st.binding.val)}
    {w : State root} (hw : w ∈ st.paired s t cs) :
    ∃ c ∈ cs, w.binding.val = c.val ∧ w.pairs = st.pairs ++ [(s.index, t.index)] := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact ⟨d, hd, rfl, rfl⟩

theorem wayInv_paired {root : Binding} {dom : String → String} {set : List (From root)} {snapshot trace : List Numbered}
    {bad : List Nat} {st : State root} (hi : WayInv dom set snapshot trace bad st) {s t : Numbered} (hs : s ∈ snapshot) (ht : t ∈ trace)
    (hu : t.index ∉ st.used) {v : Values} (hd : v.domain = dom) {cs : List (From st.binding.val)}
    (hm : matchContent v st.binding.val s.line t.line = some cs) {w : State root} (hw : w ∈ st.paired s t cs) :
    WayInv dom set snapshot trace bad w := by
  obtain ⟨c, hc, hb, hp⟩ := paired_mem hw
  obtain ⟨hn, hpm, c₀, hc₀, he⟩ := hi
  refine ⟨?_, ?_, c₀, hc₀, ?_⟩
  · rw [hp, List.map_append, List.nodup_append]
    exact ⟨hn, by simp, fun a ha b hb e => by simp at hb; subst hb; subst e; exact hu ha⟩
  · intro p hpw
    rw [hp] at hpw
    rcases List.mem_append.mp hpw with hpw | hpw
    · rcases hpm p hpw with ⟨s', hs', e₁, t', ht', e₂, hcm⟩ | hbad
      · exact .inl ⟨s', hs', e₁, t', ht', e₂, hb ▸ hcm.mono c.property⟩
      · exact .inr hbad
    · simp at hpw; subst hpw
      exact .inl ⟨s, hs, rfl, t, ht, rfl, v, st.binding.val, cs, c, hd, hm, hc, hb ▸ .refl _⟩
  · rw [hb]; exact he.trans c.property

theorem matchLine_content {v : Values} {b : Binding} {s t : Line} {out : List (From b)}
    (h : matchLine v b s t = some out) {c : From b} (hc : c ∈ out) :
    s.time = t.time ∧ matchContent v b s t = some out := by
  unfold matchLine at h
  split at h
  · rename_i he; exact ⟨beq_iff_eq.mp he, h⟩
  · cases h; cases hc

theorem exact_step {root : Binding} {dom : String → String} {set : List (From root)} {v : Values} (hd : v.domain = dom)
    {relation : Bool} {snapshot trace : List Numbered} {place : Nat} {same : State root → State root → Bool}
    (pre : List Numbered) (s : Numbered) (rest : List Numbered) (a a' : List (State root) × List Numbered)
    (hi : ExactInv dom set snapshot trace pre (s :: rest) a) (h : pairExact v relation snapshot trace place same a s = .ok a') :
    ExactInv dom set snapshot trace (pre ++ [s]) rest a' := by
  obtain ⟨states, failed⟩ := a
  obtain ⟨hsplit, hne, hf, hst⟩ := hi
  have hs : s ∈ snapshot := hsplit ▸ List.mem_append_right _ List.mem_cons_self
  dsimp only [pairExact] at h
  split at h
  · cases h
  · cases h
    refine ⟨by simpa using hsplit, hne, fun x hx => ?_, fun st hst' => ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact hf x hx
      · simp at hx; subst hx; exact hs
    · obtain ⟨hp, hw⟩ := hst st hst'
      refine ⟨?_, hw⟩
      simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
      exact hp.append_right _
  · rename_i ways hnil hways
    cases h
    refine ⟨by simpa using hsplit, ?_, hf, fun w hw => ?_⟩
    · intro e; subst e; exact hnil rfl
    · obtain ⟨st, hst', ys, hnext, hwys⟩ := mem_expand hways hw
      simp only [bind, Option.bind] at hnext
      split at hnext
      · cases hnext
      · rename_i all hall
        cases hnext
        obtain ⟨l, hl, hwl⟩ := List.mem_flatten.mp hwys
        obtain ⟨t, ht, hm⟩ := mem_of_mapM hall l hl
        simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at ht
        cases hml : matchLine v st.binding.val s.line t.line with
        | none => simp [hml] at hm
        | some cs =>
          simp only [hml, Option.map_some, Option.some.injEq] at hm
          subst hm
          obtain ⟨c, hc, -, hpairs⟩ := paired_mem hwl
          have hcm := (matchLine_content hml hc).2
          obtain ⟨hp, hwi⟩ := hst st hst'
          refine ⟨?_, wayInv_paired hwi hs ht.1 (by simpa [State.used] using ht.2.1.1) hd hcm hwl⟩
          rw [hpairs]
          simp only [List.map_append, List.map_cons, List.map_nil]
          refine List.Perm.trans ?_ (hp.append_right [s.index])
          simp only [List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm

/-- The snapshot lines, by number, that the place pass left without a pair. -/
def unplaced (placed : List (Numbered × Option (Numbered × Bool))) : List Nat :=
  placed.filterMap fun x => if x.2.isNone then some x.1.index else none

/-- The snapshot lines, by number, that the place pass paired by place with a line whose content differs. -/
def misplaced (placed : List (Numbered × Option (Numbered × Bool))) : List Nat :=
  placed.filterMap fun x => if x.2.any (!·.2) then some x.1.index else none

/-- What the place pass holds after the failed lines `pre`: every way pairs each snapshot line but the unplaced ones. -/
def PlaceInv {root : Binding} (dom : String → String) (set : List (From root)) (snapshot trace : List Numbered)
    (failed : List Numbered) (pre rest : List Numbered)
    (a : List (State root) × List (Numbered × Option (Numbered × Bool))) : Prop :=
  pre ++ rest = failed ∧ a.1 ≠ [] ∧
    ∀ st ∈ a.1, (st.pairs.map (·.1) ++ unplaced a.2 ++ rest.map (·.index)).Perm (snapshot.map (·.index)) ∧
      WayInv dom set snapshot trace (misplaced a.2) st

theorem place_step {root : Binding} {dom : String → String} {set : List (From root)} {v : Values}
    (hd : v.domain = dom) {snapshot trace failed : List Numbered} (hfailed : ∀ s ∈ failed, s ∈ snapshot) {place : Nat}
    {same : State root → State root → Bool} (pre : List Numbered) (s : Numbered) (rest : List Numbered)
    (a a' : List (State root) × List (Numbered × Option (Numbered × Bool)))
    (hi : PlaceInv dom set snapshot trace failed pre (s :: rest) a) (h : pairPlace v trace place same a s = .ok a') :
    PlaceInv dom set snapshot trace failed (pre ++ [s]) rest a' := by
  obtain ⟨states, placed⟩ := a
  obtain ⟨hsplit, hne, hst⟩ := hi
  have hs : s ∈ snapshot := hfailed s (hsplit ▸ List.mem_append_right _ List.mem_cons_self)
  have hsplit' : (pre ++ [s]) ++ rest = failed := by simpa using hsplit
  dsimp only [pairPlace] at h
  split at h
  · cases h
    refine ⟨hsplit', hne, fun st hst' => ?_⟩
    obtain ⟨hp, hw⟩ := hst st hst'
    refine ⟨?_, by simpa [misplaced] using hw⟩
    simpa [unplaced, List.append_assoc] using hp
  · rename_i t hat
    obtain ⟨first, hfirst, ht⟩ := Option.bind_eq_some_iff.mp hat
    have htt : t ∈ trace := List.mem_of_find?_eq_some ht
    have htf : t.index ∉ first.used := by
      have := List.find?_some ht
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      simpa [State.used] using this.1
    have hfirst' : first ∈ states := by
      cases states with
      | nil => exact absurd rfl hne
      | cons f fs => simp at hfirst; subst hfirst; exact List.mem_cons_self
    have hfree : first ∈ states.filter fun st => !st.used.contains t.index := by
      simpa [hfirst'] using htf
    split at h
    · cases h
    · rename_i w ws hways
      cases h
      refine ⟨hsplit', by simp, fun w' hw' => ?_⟩
      obtain ⟨st, hst', ys, hnext, hwys⟩ := mem_expand hways hw'
      simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hst'
      cases hmc : matchContent v st.binding.val s.line t.line with
      | none => simp [hmc] at hnext
      | some cs =>
        simp only [hmc, Option.map_some, Option.some.injEq] at hnext
        subst hnext
        obtain ⟨hp, hwi⟩ := hst st hst'.1
        obtain ⟨c, hc, -, hpairs⟩ := paired_mem hwys
        refine ⟨?_, by simpa [misplaced] using
          wayInv_paired hwi hs htt (by simpa [State.used] using hst'.2) hd hmc hwys⟩
        rw [hpairs]
        simp only [unplaced, List.filterMap_append, List.map_append, List.map_cons, List.map_nil,
          Option.isNone_some, Bool.false_eq_true, ↓reduceIte, List.filterMap_cons, List.filterMap_nil,
          List.append_nil] at hp ⊢
        refine List.Perm.trans ?_ hp
        simp only [List.append_assoc]
        refine List.Perm.append_left _ ?_
        rw [List.singleton_append]; exact List.perm_middle.symm
    · cases h
      refine ⟨hsplit', ?_, fun w hw => ?_⟩
      · simp only [ne_eq, List.map_eq_nil_iff]
        intro e; rw [e] at hfree; cases hfree
      · obtain ⟨st, hst', rfl⟩ := List.mem_map.mp hw
        simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hst'
        obtain ⟨hp, hn, hpm, c₀, hc₀, he⟩ := hst st hst'.1
        have hu : t.index ∉ st.pairs.map (·.2) := by simpa [State.used] using hst'.2
        have hext : ∀ (c : From root), st.binding.val.Extends c.val →
            WayInv dom set snapshot trace (misplaced (placed ++ [(s, some (t, false))]))
              { binding := c, pairs := st.pairs ++ [(s.index, t.index)] } := by
          intro c hc
          refine ⟨?_, fun p hpw => ?_, c₀, hc₀, he.trans hc⟩
          · simp only [List.map_append, List.nodup_append]
            exact ⟨hn, by simp, fun a ha b hb e => by
              simp at hb; subst hb; subst e; exact hu ha⟩
          · rcases List.mem_append.mp hpw with hpw | hpw
            · rcases hpm p hpw with ⟨s', hs', e₁, t', ht', e₂, hcm⟩ | hbad
              · exact .inl ⟨s', hs', e₁, t', ht', e₂, hcm.mono hc⟩
              · exact .inr (by simp [misplaced] at hbad ⊢; exact .inl hbad)
            · simp at hpw; subst hpw; exact .inr (by simp [misplaced])
        refine ⟨?_, ?_⟩
        · simp only [unplaced, List.filterMap_append, List.map_append, List.map_cons, List.map_nil,
            Option.isNone_some, Bool.false_eq_true, ↓reduceIte, List.filterMap_cons, List.filterMap_nil,
            List.append_nil] at hp ⊢
          refine List.Perm.trans ?_ hp
          simp only [List.append_assoc]
          refine List.Perm.append_left _ ?_
          rw [List.singleton_append]; exact List.perm_middle.symm
        · dsimp only
          split
          · split
            · rename_i c hc; exact hext ⟨c.val, st.binding.property.trans c.property⟩ c.property
            · exact hext st.binding (.refl _)
          · exact hext st.binding (.refl _)

theorem mem_of_sameSet {a b : List Nat} (h : sameSet a b = true) (hn : a.Nodup) {x : Nat} (hx : x ∈ b) : x ∈ a := by
  simp only [sameSet, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at h
  refine Classical.byContradiction fun hxa => ?_
  have := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hxa, hn⟩) (fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact h.2 y hy)
  simp at this; omega

theorem sameSet_self (a : List Nat) : sameSet a a = true := by
  simp [sameSet, List.all_eq_true]

theorem mem_distinctBy {α : Type} {same : α → α → Bool} {xs : List α} {x : α} (h : x ∈ distinctBy same xs) :
    x ∈ xs := by
  unfold distinctBy at h
  have : ∀ (acc rest : List α), (∀ y ∈ acc, y ∈ xs) → (∀ y ∈ rest, y ∈ xs) →
      ∀ y ∈ rest.foldl (fun acc x => if acc.any (same x) then acc else acc ++ [x]) acc, y ∈ xs := by
    intro acc rest hacc hrest
    induction rest generalizing acc with
    | nil => exact hacc
    | cons r rest ih =>
      simp only [List.foldl_cons]
      apply ih _ _ (fun y hy => hrest y (List.mem_cons_of_mem _ hy))
      split
      · exact hacc
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hacc y hy
        · simp at hy; subst hy; exact hrest _ List.mem_cons_self
  exact this [] xs (by simp) (fun _ h => h) x h

theorem distinctBy_ne_nil {α : Type} {same : α → α → Bool} {xs : List α} (h : xs ≠ []) :
    distinctBy same xs ≠ [] := by
  unfold distinctBy
  have : ∀ (acc rest : List α), acc ≠ [] →
      rest.foldl (fun acc x => if acc.any (same x) then acc else acc ++ [x]) acc ≠ [] := by
    intro acc rest hacc
    induction rest generalizing acc with
    | nil => exact hacc
    | cons r rest ih =>
      simp only [List.foldl_cons]
      apply ih
      split
      · exact hacc
      · simp
  cases xs with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [List.foldl_cons, List.any_nil, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact this [x] xs (by simp)

/-- `pairs` pairs the snapshot lines with the trace lines one to one, by line number. -/
def Covers (snapshot trace : List Numbered) (pairs : List (Nat × Nat)) : Prop :=
  (pairs.map (·.1)).Perm (snapshot.map (·.index)) ∧ (pairs.map (·.2)).Perm (trace.map (·.index))

theorem find?_index {l : List Numbered} (hn : (l.map (·.index)).Nodup) {x : Numbered} (hx : x ∈ l) :
    l.find? (·.index == x.index) = some x := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have : (y.index == x.index) = false := by
        simp only [beq_eq_false_iff_ne]; intro e; exact hn.1 ⟨x, hx, e.symm⟩
      rw [List.find?_cons, this]; exact ih hn.2 hx

/-- The pairs of lines that compareGroup checks the time and order of, from the pairs of numbers of the first way. -/
def linePairs (snapshot trace : List Numbered) (pairs : List (Nat × Nat)) : List (Numbered × Numbered) :=
  pairs.filterMap fun (i, j) => do pure (← snapshot.find? (·.index == i), ← trace.find? (·.index == j))

theorem find?_linePairs {snapshot trace : List Numbered} (hsn : (snapshot.map (·.index)).Nodup)
    (htn : (trace.map (·.index)).Nodup) :
    ∀ {pairs : List (Nat × Nat)}, (pairs.map (·.1)).Nodup →
      (∀ p ∈ pairs, ∃ s ∈ snapshot, s.index = p.1 ∧ ∃ t ∈ trace, t.index = p.2) →
      ∀ {i j : Nat}, (i, j) ∈ pairs → ∃ s ∈ snapshot, s.index = i ∧ ∃ t ∈ trace, t.index = j ∧
        (linePairs snapshot trace pairs).find? (·.1.index == i) = some (s, t)
  | (i', j') :: pairs, hn, hl, i, j, hp => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    obtain ⟨s', hs', e₁, t', ht', e₂⟩ := hl (i', j') List.mem_cons_self
    simp only at e₁ e₂
    have hhead : linePairs snapshot trace ((i', j') :: pairs) = (s', t') :: linePairs snapshot trace pairs := by
      simp only [linePairs, List.filterMap_cons]
      subst e₁ e₂
      rw [find?_index hsn hs', find?_index htn ht']
      rfl
    rw [hhead]
    rcases List.mem_cons.mp hp with e | hp
    · cases e
      exact ⟨s', hs', e₁, t', ht', e₂, by simp [e₁]⟩
    · obtain ⟨s, hs, e₃, t, ht, e₄, hf⟩ := find?_linePairs hsn htn hn.2 (fun p hp => hl p (List.mem_cons_of_mem _ hp)) hp
      refine ⟨s, hs, e₃, t, ht, e₄, ?_⟩
      have : (s'.index == i) = false := by
        simp only [beq_eq_false_iff_ne, e₁]; intro e; subst e; exact hn.1 ⟨(i', j), hp, rfl⟩
      rw [List.find?_cons]; simp only [this]; exact hf

/--
The `out` lines of one group pair one to one through one pairing: each pair compares equal under `b` at equal times, the
pairing keeps the order that each snapshot line's `after` names, and, when `relation`, each trace line's `after` equals
the snapshot line's through the pairing (sameAfter).
-/
def OutsMatch (dom : String → String) (relation : Bool) (b : Binding) (snapshot trace : List Numbered) : Prop :=
  ∃ pairs, Covers snapshot trace pairs ∧
    (∀ p ∈ pairs, ∃ s ∈ snapshot, s.index = p.1 ∧ ∃ t ∈ trace, t.index = p.2 ∧
      s.line.time = t.line.time ∧ ContentMatch dom b s.line t.line ∧
      (relation = true → sameAfter snapshot trace pairs s t = true)) ∧
    ∀ sk ∈ snapshot.zipIdx, ∀ n ∈ mustFollow snapshot sk.1 sk.2, ∀ j j', (sk.1.index, j) ∈ pairs → (n, j') ∈ pairs →
      j' < j

theorem OutsMatch.mono {dom : String → String} {relation : Bool} {b b' : Binding} (h : b.Extends b')
    {snapshot trace : List Numbered} : OutsMatch dom relation b snapshot trace → OutsMatch dom relation b' snapshot trace
  | ⟨pairs, hc, hm, ho⟩ => ⟨pairs, hc, fun p hp => by
      obtain ⟨s, hs, e₁, t, ht, e₂, htime, hcm, ha⟩ := hm p hp
      exact ⟨s, hs, e₁, t, ht, e₂, htime, hcm.mono h, ha⟩, ho⟩

/-- What a way that pairChecks finds nothing in holds: equal times, the order that `after` names, and, when `relation`, the same `after`. -/
theorem pairChecks_nil {relation : Bool} {snapshot trace : List Numbered} {pairs : List (Nat × Nat)}
    (h : pairChecks relation snapshot trace pairs = []) :
    (∀ p ∈ linePairs snapshot trace pairs, p.1.line.time = p.2.line.time) ∧
    (∀ sk ∈ snapshot.zipIdx, ∀ s₀ t, (linePairs snapshot trace pairs).find? (·.1.index == sk.1.index) = some (s₀, t) →
      ∀ n ∈ mustFollow snapshot sk.1 sk.2, ∀ s₁ before,
        (linePairs snapshot trace pairs).find? (·.1.index == n) = some (s₁, before) → before.index < t.index) ∧
    (relation = true → ∀ p ∈ linePairs snapshot trace pairs, sameAfter snapshot trace pairs p.1 p.2 = true) := by
  unfold pairChecks at h
  simp only [List.append_eq_nil_iff] at h
  obtain ⟨⟨htimes, horders⟩, hafters⟩ := h
  refine ⟨fun p hp => ?_, fun sk hsk s₀ t hft n hn s₁ before hfb => ?_, fun hr p hp => ?_⟩
  · have := List.filterMap_eq_nil_iff.mp htimes p hp
    obtain ⟨s, t⟩ := p
    simp only at this
    split at this
    · rename_i he; exact beq_iff_eq.mp he
    · cases this
  · have := List.flatMap_eq_nil_iff.mp horders sk hsk
    obtain ⟨s, k⟩ := sk
    simp only at this hft hn ⊢
    rw [linePairs] at hft hfb
    rw [hft] at this
    have := List.filterMap_eq_nil_iff.mp this n hn
    rw [hfb] at this
    refine Classical.byContradiction fun hlt => ?_
    simp [hlt] at this
  · simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hafters
    have := List.filterMap_eq_nil_iff.mp hafters p hp
    obtain ⟨s, t⟩ := p
    simp only at this
    split at this
    · assumption
    · cases this

/-- The ways that a group without a difference ends with, and what its empty findings say of the first. -/
theorem compareGroup_final {root : Binding} {set : List (From root)} {v : Values} {snapshot trace : List Numbered}
    {place : Nat} {set' : List (From root)} {stop : Bool} {relation : Bool} (hset : set ≠ [])
    (h : compareGroup set v relation snapshot trace place = ([], set', stop)) :
    ∃ first firsts, stop = false ∧
      set' = distinctBy From.same (((first :: firsts).filter fun st => sameSet st.used first.used &&
        (pairChecks relation snapshot trace st.pairs).isEmpty).map (·.binding)) ∧
      (∀ st ∈ first :: firsts, (st.pairs.map (·.1)).Perm (snapshot.map (·.index)) ∧
        WayInv v.domain set snapshot trace [] st) ∧
      (∀ t ∈ trace, t.index ∈ first.used) ∧ pairChecks relation snapshot trace first.pairs = [] := by
  dsimp only [compareGroup] at h
  split at h
  · cases h
  · rename_i states failed hexact
    have hE := foldl_bind_inv _ (ExactInv v.domain set snapshot trace) (fun pre x rest a a' hi hg =>
      exact_step rfl pre x rest a a' hi hg) snapshot [] _ _ ⟨rfl, by simpa using hset, by simp, fun st hst => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hst
        exact ⟨by simp, by simp, fun _ hp => by simp at hp, c, hc, .refl _⟩⟩ hexact
    obtain ⟨-, hne, hf, hst⟩ := hE
    split at h
    · cases h
    · rename_i states' placed hplace
      have hP := foldl_bind_inv _ (PlaceInv v.domain set snapshot trace failed) (fun pre x rest a a' hi hg =>
        place_step rfl hf pre x rest a a' hi hg) failed [] _ _ ⟨rfl, hne, fun st hst' => by
          obtain ⟨hp, hw⟩ := hst st hst'
          exact ⟨by simpa [unplaced] using hp, by simpa [misplaced] using hw⟩⟩ hplace
      obtain ⟨-, hne', hst'⟩ := hP
      simp only [Prod.mk.injEq, List.append_eq_nil_iff] at h
      obtain ⟨⟨⟨hdiff, hunexp⟩, hchecks⟩, hset', hstop⟩ := h
      have hall : ∀ x ∈ placed, ∃ t, x.2 = some (t, true) := by
        intro x hx
        have := List.filterMap_eq_nil_iff.mp hdiff x hx
        obtain ⟨s, o⟩ := x
        match o, this with
        | some (t, true), _ => exact ⟨t, rfl⟩
        | some (_, false), h => simp at h
        | none, h => simp at h
      have hun : unplaced placed = [] := List.filterMap_eq_nil_iff.mpr fun x hx => by
        obtain ⟨t, ht⟩ := hall x hx; simp [ht]
      have hmis : misplaced placed = [] := List.filterMap_eq_nil_iff.mpr fun x hx => by
        obtain ⟨t, ht⟩ := hall x hx; simp [ht]
      obtain ⟨first, firsts, hstates⟩ : ∃ f fs, states' = f :: fs := by
        cases states' with
        | nil => exact absurd rfl hne'
        | cons f fs => exact ⟨f, fs, rfl⟩
      subst hstates
      simp only [List.head?_cons, Option.map_some, Option.getD_some] at hset' hunexp hchecks
      refine ⟨first, firsts, hstop.symm, ?_, fun st hst => ?_, fun t ht => ?_, hchecks⟩
      · rw [← hset']
        simp [hchecks]
      · obtain ⟨hp, hw⟩ := hst' st hst
        rw [hun] at hp; rw [hmis] at hw
        exact ⟨by simpa using hp, hw⟩
      · have hu := List.filter_eq_nil_iff.mp (List.map_eq_nil_iff.mp hunexp) t ht
        simpa [State.used] using hu

/--
A group that compareGroup finds no difference in pairs its snapshot lines with its trace lines one to one under every
binding that it carries on, through one pairing per binding: each pair compares equal under that binding at equal times,
the pairing keeps the order that each snapshot line's `after` names, and, when `relation`, each trace line's `after`
equals the snapshot line's through the pairing. Each binding extends a binding that the group started from.
-/
theorem compareGroup_paired {root : Binding} {set : List (From root)} {v : Values} {snapshot trace : List Numbered}
    {place : Nat} {set' : List (From root)} {stop : Bool} {relation : Bool} (hsn : (snapshot.map (·.index)).Nodup)
    (htn : (trace.map (·.index)).Nodup) (hset : set ≠ [])
    (h : compareGroup set v relation snapshot trace place = ([], set', stop)) :
    stop = false ∧ set' ≠ [] ∧ ∀ c' ∈ set', (∃ c ∈ set, c.val.Extends c'.val) ∧
      OutsMatch v.domain relation c'.val snapshot trace := by
  obtain ⟨first, firsts, hstop, rfl, hst, hused, hfirst⟩ := compareGroup_final hset h
  refine ⟨hstop, distinctBy_ne_nil ?_, fun c' hc' => ?_⟩
  · simp only [ne_eq, List.map_eq_nil_iff]
    intro e
    have : first ∈ (first :: firsts).filter fun st => sameSet st.used first.used &&
        (pairChecks relation snapshot trace st.pairs).isEmpty := by simp [sameSet_self, hfirst]
    rw [e] at this; cases this
  · obtain ⟨st, hst₁, rfl⟩ := List.mem_map.mp (mem_distinctBy hc')
    simp only [List.mem_filter, Bool.and_eq_true, List.isEmpty_iff] at hst₁
    obtain ⟨hst₁, hsame, hchecks⟩ := hst₁
    obtain ⟨hp, hn, hpm, c, hc, he⟩ := hst st hst₁
    obtain ⟨htimes, horders, hafters⟩ := pairChecks_nil hchecks
    have hl : ∀ p ∈ st.pairs, ∃ s ∈ snapshot, s.index = p.1 ∧ ∃ t ∈ trace, t.index = p.2 := fun p hp' => by
      rcases hpm p hp' with ⟨s, hs, e₁, t, ht, e₂, _⟩ | hbad
      · exact ⟨s, hs, e₁, t, ht, e₂⟩
      · cases hbad
    have hfn : (st.pairs.map (·.1)).Nodup := hp.nodup_iff.mpr hsn
    refine ⟨⟨c, hc, he⟩, st.pairs, ⟨hp, ?_⟩, fun p hp' => ?_, fun sk hsk n hn' j j' hj hj' => ?_⟩
    · refine (List.perm_ext_iff_of_nodup hn htn).mpr fun j => ⟨fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hj
        obtain ⟨_, _, _, t, ht, e⟩ := hl p hp'
        exact List.mem_map.mpr ⟨t, ht, e⟩
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hj
        exact mem_of_sameSet hsame hn (hused t ht)
    · obtain ⟨i, j⟩ := p
      obtain ⟨s, hs, e₁, t, ht, e₂, hf⟩ := find?_linePairs hsn htn hfn hl hp'
      have hmem := List.mem_of_find?_eq_some hf
      rcases hpm (i, j) hp' with ⟨s', hs', e₁', t', ht', e₂', hcm⟩ | hbad
      · have hss : s' = s := by
          have := find?_index hsn hs'
          rw [e₁', ← e₁, find?_index hsn hs] at this
          exact (Option.some.inj this).symm
        have htt : t' = t := by
          have := find?_index htn ht'
          rw [e₂', ← e₂, find?_index htn ht] at this
          exact (Option.some.inj this).symm
        subst hss htt
        exact ⟨s', hs', e₁, t', ht', e₂, htimes (s', t') hmem, hcm, fun hr => hafters hr (s', t') hmem⟩
      · cases hbad
    · obtain ⟨s, hs, e₁, t, ht, e₂, hf⟩ := find?_linePairs hsn htn hfn hl hj
      obtain ⟨s', hs', e₁', t', ht', e₂', hf'⟩ := find?_linePairs hsn htn hfn hl hj'
      have := horders sk hsk s t hf n hn' s' t' hf'
      rw [← e₂, ← e₂']; exact this

/-! ## Groups -/

theorem groups_go_nodup : ∀ (ls : List (Option Line)) (i : Nat) (input : Option Numbered) (acc : List Numbered),
    (acc.map (·.index)).Nodup → (∀ x ∈ acc, x.index < i) →
      ∀ g ∈ groups.go ls i input acc, (g.outs.map (·.index)).Nodup
  | [], i, input, acc, hn, _ => by
    simp only [groups.go, List.mem_singleton]
    rintro g rfl
    simpa [List.map_reverse] using (List.reverse_perm _).nodup_iff.mpr hn
  | none :: ls, i, input, acc, hn, hl => by
    simp only [groups.go]
    exact groups_go_nodup ls (i + 1) input acc hn fun x hx => by have := hl x hx; omega
  | some l :: ls, i, input, acc, hn, hl => by
    simp only [groups.go]
    split
    · refine groups_go_nodup ls (i + 1) input _ ?_ ?_
      · simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
        exact ⟨fun x hx e => by have := hl x hx; omega, hn⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · have := hl x hx; omega
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simpa [List.map_reverse] using (List.reverse_perm _).nodup_iff.mpr hn
      · exact groups_go_nodup ls (i + 1) _ [] (by simp) (by simp) g hg

/-- No two `out` lines of a group of `groups` have one number. -/
theorem groups_nodup (lines : List (Option Line)) : ∀ g ∈ groups lines, (g.outs.map (·.index)).Nodup :=
  groups_go_nodup lines 1 none [] (by simp) (by simp)

/-- Two `in` lines, or none, that compare equal under a binding that `b` extends, at the same time. -/
def InputMatch (dom : String → String) (b : Binding) : Option Numbered → Option Numbered → Prop
  | none, none => True
  | some s, some t => s.line.time = t.line.time ∧ ContentMatch dom b s.line t.line
  | _, _ => False

theorem InputMatch.mono {dom : String → String} {b b' : Binding} (h : b.Extends b') :
    {x y : Option Numbered} → InputMatch dom b x y → InputMatch dom b' x y
  | none, none, _ => trivial
  | some _, some _, ⟨ht, hc⟩ => ⟨ht, hc.mono h⟩

/-- Each snapshot group matches the trace group at its place under `b`: their inputs, and their compared `out` lines. -/
def GroupsMatch (dom : String → String) (internal : Line → Bool) (relation : Bool) (b : Binding) :
    List Group → List Group → Prop
  | [], [] => True
  | e :: es, a :: as => (InputMatch dom b e.input a.input ∧
      OutsMatch dom relation b (e.outs.filter fun o => !internal o.line) (a.outs.filter fun o => !internal o.line)) ∧
      GroupsMatch dom internal relation b es as
  | _, _ => False

theorem filter_nodup {l : List Numbered} (h : (l.map (·.index)).Nodup) (p : Numbered → Bool) :
    ((l.filter p).map (·.index)).Nodup :=
  (List.filter_sublist.map _).nodup h

/--
Comparing groups without a finding matches each snapshot group with the trace group at its place, under every binding
that the comparison ends with; each of those extends a binding that it started from. Only a first group lacks an `in`
line, as `groups` makes them.
-/
theorem compareGroups_match (lineCount : Nat) (internal : Line → Bool) (relation : Bool) (inputs : List Line)
    (outs : List Numbered)
    {root : Binding} : ∀ (expected actual : List Group) (v : Values) (set : List (From root)),
      set ≠ [] → (∀ e ∈ expected, (e.outs.map (·.index)).Nodup) →
      (∀ a ∈ actual, (a.outs.map (·.index)).Nodup) →
      (expected = [] → ∀ a ∈ actual, a.input.isSome) → (actual = [] → ∀ e ∈ expected, e.input.isSome) →
      (∀ e ∈ expected.drop 1, e.input.isSome) → (∀ a ∈ actual.drop 1, a.input.isSome) →
      (compareGroups lineCount internal relation inputs outs false expected actual v set).1 = [] →
      (compareGroups lineCount internal relation inputs outs false expected actual v set).2 ≠ [] ∧
      ∀ c ∈ (compareGroups lineCount internal relation inputs outs false expected actual v set).2,
        (∃ c₀ ∈ set, c₀.val.Extends c.val) ∧ GroupsMatch v.domain internal relation c.val expected actual
  | [], [], v, set, hset, _, _, _, _, _, _, _ => by
    exact ⟨by simpa [compareGroups] using hset, fun c hc => ⟨⟨c, by simpa [compareGroups] using hc, .refl _⟩, trivial⟩⟩
  | [], a :: as, v, set, _, _, _, hE, _, _, _, h => by
    have ha := hE rfl a List.mem_cons_self
    simp only [compareGroups] at h
    split at h
    · cases h
    · rename_i hn; rw [hn] at ha; cases ha
  | e :: es, [], v, set, _, _, _, _, hA, _, _, h => by
    have he := hA rfl e List.mem_cons_self
    simp only [compareGroups] at h
    split at h
    · cases h
    · rename_i hn; rw [hn] at he; cases he
  | e :: es, a :: as, v, set, hset, hen, han, _, _, hes, has, h => by
    generalize hr : compareGroups lineCount internal relation inputs outs false (e :: es) (a :: as) v set = r at h ⊢
    rw [compareGroups] at hr
    have hin : ∀ set₁ : List (From root),
        (match e.input, a.input with
          | none, none => Except.ok set
          | some s, some t =>
            match expand From.same set fun b => (matchLine { v with fresh := [] } b.val s.line t.line).map
                (lift b.property) with
            | none => .error (Finding.uncomparable (.bindingLimit t.index (Subject.of s.line.toTraceLine) s.index bindingLimit))
            | some [] => .error (differentInput ((set.head?.map (·.val)).getD .empty) s t)
            | some set' =>
              match unrouted (set.map (·.val)) v inputs s.line with
              | some images =>
                .error (.uncomparable (.ambiguous t.index (Subject.of s.line.toTraceLine) s.index
                  ((outs.filter fun o => images.contains o.line.body.id).map (·.index))))
              | none => .ok set'
          | some s, none => .error (.uncomparable (.missingInput lineCount (lineValue s.line) s.index))
          | none, some t => .error (.uncomparable (.unexpectedInput t.index (lineValue t.line))) :
            Except Finding (List (From root))) = .ok set₁ →
        set₁ ≠ [] ∧ ∀ c ∈ set₁, ∃ c₀ ∈ set, c₀.val.Extends c.val ∧ InputMatch v.domain c.val e.input a.input := by
      intro set₁ hs
      split at hs
      · rename_i hx hy
        cases hs
        exact ⟨hset, fun c hc => ⟨c, hc, .refl _, by rw [hx, hy]; trivial⟩⟩
      · rename_i s t hx hy
        split at hs
        · cases hs
        · cases hs
        · rename_i set' hnil hexp
          split at hs
          · cases hs
          · cases hs
            refine ⟨fun e' => hnil e', fun c hc => ?_⟩
            obtain ⟨b, hb, ys, hys, hcys⟩ := mem_expand hexp hc
            cases hml : matchLine { v with fresh := [] } b.val s.line t.line with
            | none => simp [hml] at hys
            | some cs =>
              simp only [hml, Option.map_some, Option.some.injEq] at hys
              subst hys
              obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hcys
              obtain ⟨htime, hcm⟩ := matchLine_content hml hd
              refine ⟨b, hb, d.property, ?_⟩
              rw [hx, hy]
              exact ⟨htime, { v with fresh := [] }, b.val, cs, d, rfl, hcm, hd, .refl _⟩
      · cases hs
      · cases hs
    dsimp only at hr
    split at hr
    · subst hr; simp at h
    · rename_i set₁ hinputs
      obtain ⟨hne₁, hset₁⟩ := hin set₁ hinputs
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hr
      generalize hcg : compareGroup set₁ { v with fresh := v.fresh ++ e.outs.flatMap (·.line.fresh) } relation
        (e.outs.filter fun o => !internal o.line) (a.outs.filter fun o => !internal o.line)
        ((a.input.map (·.index)).getD 1) = cg at hr
      obtain ⟨found, set₂, stop⟩ := cg
      generalize hrest : compareGroups lineCount internal relation inputs outs false es as
        { v with fresh := v.fresh ++ e.outs.flatMap (·.line.fresh) } set₂ = rest at hr
      subst hr
      by_cases hstop : stop = true
      · simp only [hstop, ↓reduceIte] at h
        subst h
        have := (compareGroup_paired (filter_nodup (hen e List.mem_cons_self) _)
          (filter_nodup (han a List.mem_cons_self) _) hne₁ hcg).1
        rw [this] at hstop; cases hstop
      · simp only [hstop, Bool.false_eq_true, ↓reduceIte] at h ⊢
        obtain ⟨found', set₃⟩ := rest
        simp only [List.append_eq_nil_iff] at h
        obtain ⟨hfound, hfound'⟩ := h
        subst hfound
        have hen' := hen e List.mem_cons_self
        have han' := han a List.mem_cons_self
        obtain ⟨-, hne₂, hset₂⟩ := compareGroup_paired (filter_nodup hen' _) (filter_nodup han' _) hne₁ hcg
        have ih := compareGroups_match lineCount internal relation inputs outs es as
          { v with fresh := v.fresh ++ e.outs.flatMap (·.line.fresh) } set₂ hne₂ (fun g hg => hen g (List.mem_cons_of_mem _ hg))
          (fun g hg => han g (List.mem_cons_of_mem _ hg))
          (fun hnil g hg => has g (by simpa using hg)) (fun hnil g hg => hes g (by simpa using hg))
          (fun g hg => hes g (by simpa using List.mem_of_mem_drop hg))
          (fun g hg => has g (by simpa using List.mem_of_mem_drop hg))
        rw [hrest] at ih
        obtain ⟨hne₃, hset₃⟩ := ih hfound'
        refine ⟨hne₃, fun c hc => ?_⟩
        obtain ⟨⟨c₂, hc₂, he₂⟩, hgm⟩ := hset₃ c hc
        obtain ⟨⟨c₁, hc₁, he₁⟩, hom⟩ := hset₂ c₂ hc₂
        obtain ⟨c₀, hc₀, he₀, him⟩ := hset₁ c₁ hc₁
        exact ⟨⟨c₀, hc₀, he₀.trans (he₁.trans he₂)⟩, ⟨him.mono (he₁.trans he₂), hom.mono he₂⟩, hgm⟩

theorem groups_go_shape : ∀ (ls : List (Option Line)) (i : Nat) (input : Option Numbered) (acc : List Numbered),
    groups.go ls i input acc ≠ [] ∧ (∀ g ∈ (groups.go ls i input acc).drop 1, g.input.isSome) ∧
      (input.isSome → ∀ g ∈ groups.go ls i input acc, g.input.isSome)
  | [], i, input, acc => by
    simp only [groups.go]
    exact ⟨by simp, by simp, fun h g hg => by simp at hg; subst hg; exact h⟩
  | none :: ls, i, input, acc => by
    simp only [groups.go]; exact groups_go_shape ls (i + 1) input acc
  | some l :: ls, i, input, acc => by
    simp only [groups.go]
    split
    · exact groups_go_shape ls (i + 1) input _
    · obtain ⟨-, -, hsome⟩ := groups_go_shape ls (i + 1) (some { line := l, index := i }) []
      refine ⟨by simp, fun g hg => hsome rfl g (by simpa using hg), fun h g hg => ?_⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · exact h
      · exact hsome rfl g hg

theorem groups_shape (lines : List (Option Line)) :
    groups lines ≠ [] ∧ ∀ g ∈ (groups lines).drop 1, g.input.isSome :=
  ⟨(groups_go_shape lines 1 none []).1, (groups_go_shape lines 1 none []).2.1⟩

/--
A trace that compare finds no violation in matches the snapshot: no line cut the trace, and under every binding that the
comparison ends with, each snapshot group matches the trace group at its place (GroupsMatch). Each binding is one to one
within each domain.
-/
@[guarantee] theorem compare_matches (snapshot lines : List (Option Line)) (cut : Option Uncomparable) (internal : Line → Bool)
    (renamed : Values → Values) (relation : Bool)
    (h : (Verify.compare snapshot lines cut internal renamed relation).findings = []) :
    cut = none ∧ (Verify.compare snapshot lines cut internal renamed relation).bindings ≠ [] ∧
      ∀ b ∈ (Verify.compare snapshot lines cut internal renamed relation).bindings, OneToOne b.pairs ∧
        GroupsMatch (renamed { domain := valueDomains snapshot, fresh := [], image := fun _ _ => true }).domain
          internal relation b (groups snapshot) (groups lines) := by
  unfold Verify.compare at h ⊢
  simp only [List.append_eq_nil_iff, Option.toList_eq_nil_iff, Option.map_eq_none_iff] at h
  obtain ⟨hfound, rfl⟩ := h
  simp only [Option.isSome_none] at hfound ⊢
  obtain ⟨hes, hes'⟩ := groups_shape snapshot
  obtain ⟨has, has'⟩ := groups_shape lines
  have := compareGroups_match lines.length internal relation _ _ (groups snapshot) (groups lines) _
    [⟨Binding.empty, .refl _⟩] (by simp) (groups_nodup snapshot) (groups_nodup lines)
    (fun e => absurd e hes) (fun e => absurd e has) hes' has' hfound
  obtain ⟨hne, hall⟩ := this
  refine ⟨trivial, fun e => hne (List.map_eq_nil_iff.mp e), fun b hb => ?_⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact ⟨c.val.pairs_oneToOne, (hall c hc).2⟩


/--
A restart ends every subscription for verify: the lines after it are compared as if no subscription were open, whatever
answers came before. The first answer to a subscription that is open with no answer yet is kept.
-/
@[guarantee] theorem first_answer_after_restart_kept (r a : Line) (ls : List (Option Line))
    (open_ : List (String × Option String)) (restartId id to : String) (answer : Answer)
    (hr : r.body = .restart .in restartId) (ha : a.body = .answer .out id to answer) :
    withoutRepeatedAnswers.go (some r :: ls) open_ = some r :: withoutRepeatedAnswers.go ls [] ∧
      (open_.lookup to = some none → withoutRepeatedAnswers.go (some a :: ls) open_ =
        some a :: withoutRepeatedAnswers.go ls (setAt open_ to (some (answerContent answer a.value).key))) := by
  refine ⟨by simp [withoutRepeatedAnswers.go, hr], fun hl => ?_⟩
  simp [withoutRepeatedAnswers.go, ha, hl]

end Tazuna.Thm.Verify.Compare
