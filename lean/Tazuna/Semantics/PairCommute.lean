import Tazuna.Semantics.Support

/-! The question T5 asks of two waiting own effects, and why its answer covers every order of a cascade. Two own
effects `e1` and `e2` commute from a step in progress `a0` (where neither waits any more) when running `e1` then `e2`
ends as running them the other way round with the counters swapped: `e2` takes the counter it gets after `e1`, and
`e1` the one it gets first (`canonPair`), so each effect makes the same names in both orders, and the results are
compared up to renaming wire ids and reading collections as multisets (`PairCommutes`). This is the solver's question:
it has no renaming to search for. Swapping the counters back is a renaming the cascade respects, and the effects that
still wait are a frame no internal step reads, so pairs that commute at the front of the queue make every two waiting
effects commute wherever they wait (`commutes_of_pairs`), and every order of the cascade agrees with `settle`
(`cascade_agrees`). -/

namespace Tazuna.Ir

/-- `f` and `f + 1` swapped. -/
def swapFn (f a : Nat) : Nat := if a = f then f + 1 else if a = f + 1 then f else a

theorem swapFn_swapFn (f a : Nat) : swapFn f (swapFn f a) = a := by
  unfold swapFn
  by_cases h1 : a = f <;> by_cases h2 : a = f + 1 <;> simp [h1, h2]

theorem swapFn_of_lt {f a : Nat} (h : a < f) : swapFn f a = a := by
  unfold swapFn; simp only [Nat.ne_of_lt h, Nat.ne_of_lt (Nat.lt_succ_of_lt h), ite_false]

theorem swapFn_of_ge {f a : Nat} (h : f + 2 ≤ a) : swapFn f a = a := by
  unfold swapFn
  simp only [show a ≠ f by omega, show a ≠ f + 1 by omega, ite_false]

/-- The counters `f` and `f + 1` swapped, every other counter kept. -/
def PBij.swap (f : Nat) : PBij where
  rel a b := b = swapFn f a
  func := by rintro _ _ _ rfl rfl; rfl
  inj := by
    intro a a' b h h'
    rw [← swapFn_swapFn f a, ← swapFn_swapFn f a', ← h, ← h']

theorem PBij.swap_fixes (f : Nat) : (PBij.swap f).Fixes f := fun _ hc => (swapFn_of_lt hc).symm

theorem PBij.swap_above {f n : Nat} (h : f + 2 ≤ n) : (PBij.swap f).rel n n := (swapFn_of_ge h).symm

namespace Step

variable {v : ServiceV} (T : List TypeDecl)

/-- The step in progress with the counter `k`. -/
def Acc.withFresh (a : Acc v) (k : Nat) : Acc v := { a with state := { a.state with fresh := k } }

/-- The two orders' equivalence: the same up to renaming wire ids and the ids made so far, collections as multisets. -/
abbrev Same : Acc v → Acc v → Prop := Diamond.Closure OwnRel

/-- `e2` then `e1` with each effect's counter as it is when `e1` runs first. -/
def canonPair (a0 : Acc v) (e1 e2 : EffectV v.event) : Except Fault (Acc v) := do
  let c ← runOwn T (a0.withFresh (a0.state.fresh + 1)) e2
  let d ← runOwn T (c.withFresh a0.state.fresh) e1
  pure (d.withFresh (a0.state.fresh + 2))

/-- Two own effects commute from `a0`: where `e1` runs, `e2` after it ends as the canonical other order does, up to
renaming, or both fault; and if `e2` faults first, it still faults after `e1`. -/
def PairCommutes (a0 : Acc v) (e1 e2 : EffectV v.event) : Prop :=
  ∀ b, runOwn T a0 e1 = .ok b →
    (∀ c, runOwn T (a0.withFresh (a0.state.fresh + 1)) e2 = .ok c → Diamond.Agree Same (runOwn T b e2) (canonPair T a0 e1 e2)) ∧
    (∀ f, runOwn T (a0.withFresh (a0.state.fresh + 1)) e2 = .error f → Diamond.Faults (runOwn T b e2))

theorem Acc.Rel.withFresh {R : Ren} {a a' : Acc v} (h : Acc.Rel R a a') (k k' : Nat) :
    Acc.Rel R (a.withFresh k) (a'.withFresh k') := h

/-- Running `e2` first with its own counter or with the counter it has after `e1` differs by swapping the two
counters, so the actual other order and the canonical one agree up to renaming. -/
theorem actual_canon (hv : v.Equivariant) {a0 : Acc v} (ha : SelfAt a0.state.fresh a0) {e1 e2 : EffectV v.event}
    (he1 : OwnAt a0.state.fresh e1) (he2 : OwnAt a0.state.fresh e2) :
    (∃ W, Lifted ⟨PBij.swap a0.state.fresh, W⟩ a0
        (a0.withFresh (a0.state.fresh + 1)) (runOwn T a0 e2) (runOwn T (a0.withFresh (a0.state.fresh + 1)) e2)) ∧
      ∀ c1, runOwn T a0 e2 = .ok c1 → Diamond.Agree Same (runOwn T c1 e1) (canonPair T a0 e1 e2) := by
  generalize hf : a0.state.fresh = f at ha he1 he2 ⊢
  obtain ⟨W, hA⟩ := ha _ (PBij.swap_fixes f)
  have hctr : (PBij.swap f).rel f (f + 1) := by show _ = _; simp [swapFn]
  have hl := runOwn_rel T hv (R := ⟨PBij.swap f, W⟩) (a := a0) (a' := a0.withFresh (f + 1))
    (hA.withFresh f (f + 1)) (by rw [hf]; exact hctr) (he2.2 _ (PBij.swap_fixes f))
  refine ⟨⟨W, hl⟩, fun c1 hc1 => ?_⟩
  have hfr1 : c1.state.fresh = f + 1 := by rw [runOwn_fresh T he2.1 hc1, hf]
  rcases hl with ⟨h1, -⟩ | ⟨b, c', R', h1, h2, hc, hb, -, -, hn⟩
  · rw [hc1] at h1; exact h1.elim
  · rw [hc1] at h1; cases h1
    have hfr' : c'.state.fresh = f + 2 := runOwn_fresh T he2.1 h2
    have hctr2 : R'.ctr.rel (f + 1) f := by rw [hc]; show _ = _; simp [swapFn]
    have hl2 := runOwn_rel T hv (hb.withFresh (f + 1) f) hctr2 (by rw [hc]; exact he1.2 _ (PBij.swap_fixes f))
    simp only [canonPair, hf, h2, bind, Except.bind]
    have hb1 : c1 = c1.withFresh (f + 1) := by rw [← hfr1]; rfl
    rw [← hb1] at hl2
    rcases hl2 with ⟨h3, h4⟩ | ⟨d, d', R'', h3, h4, hc', hd, -, -, hn'⟩
    · refine .inr ⟨h3, ?_⟩
      revert h4
      cases runOwn T (c'.withFresh f) e1 <;> intro h4
      · trivial
      · exact h4.elim
    · rw [h3, h4]
      have hfd : d.state.fresh = f + 2 := by rw [runOwn_fresh T he1.1 h3, hfr1]
      refine .inl (.base ⟨R'', hd.withFresh d.state.fresh (f + 2), ?_, ?_, fun n hn2 => ?_⟩)
      · show d.state.fresh = f + 2; exact hfd
      · show d.state.nextId = d'.state.nextId
        simp only [Acc.withFresh] at hn hn'
        omega
      · rw [hc', hc]; exact PBij.swap_above (by omega)

/-- Where the place `j` of a list is once the place `i` is taken out. -/
def afterErase (i j : Nat) : Nat := if j < i then j else j - 1

/-- `l` with the places `i` and `j` taken out. -/
def dropTwo {α : Type} (l : List α) (i j : Nat) : List α := (l.eraseIdx i).eraseIdx (afterErase i j)

theorem eraseIdx_eraseIdx_lt {α : Type} : (l : List α) → {i j : Nat} → i < j →
    (l.eraseIdx i).eraseIdx (j - 1) = (l.eraseIdx j).eraseIdx i
  | [], _, _, _ => rfl
  | x :: xs, 0, j + 1, _ => by simp
  | x :: xs, i + 1, j + 1, h => by
    have hj : j = (j - 1) + 1 := by omega
    rw [List.eraseIdx_cons_succ, List.eraseIdx_cons_succ, Nat.add_sub_cancel, hj, List.eraseIdx_cons_succ,
      List.eraseIdx_cons_succ, ← hj, eraseIdx_eraseIdx_lt xs (by omega : i < j)]

theorem dropTwo_comm {α : Type} (l : List α) {i j : Nat} (hij : i ≠ j) : dropTwo l i j = dropTwo l j i := by
  unfold dropTwo afterErase
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · simp only [show ¬ j < i by omega, h, ite_false, ite_true, eraseIdx_eraseIdx_lt l h]
  · simp only [show ¬ i < j by omega, h, ite_false, ite_true, eraseIdx_eraseIdx_lt l h]

theorem afterErase_lt {α : Type} {l : List α} {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i ≠ j) :
    afterErase i j < (l.eraseIdx i).length := by
  rw [List.length_eraseIdx_of_lt hi]; unfold afterErase; split <;> omega

theorem getElem_afterErase {α : Type} {l : List α} {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (hij : i ≠ j) : (l.eraseIdx i)[afterErase i j]'(afterErase_lt hi hj hij) = l[j] := by
  rw [List.getElem_eraseIdx]
  unfold afterErase
  split
  · simp
  · simp only [show ¬ (j - 1 < i) by omega, ↓reduceDIte]; congr 1; omega

theorem mem_dropTwo {α : Type} {l : List α} {i j : Nat} {x : α} (h : x ∈ dropTwo l i j) : x ∈ l :=
  mem_eraseIdx (mem_eraseIdx h)

theorem runOwn_frame (a : Acc v) (xs : List (EffectV v.event)) (e : EffectV v.event) :
    runOwn T { a with own := xs } e = (runOwn T { a with own := [] } e).map (Acc.ownFront xs) := by
  have h := runOwn_own T xs { a with own := [] } e
  simp only [Acc.ownFront, List.append_nil] at h
  exact h

theorem runOwn_frame_error {a : Acc v} {xs ys : List (EffectV v.event)} {e : EffectV v.event} {f : Fault}
    (h : runOwn T { a with own := xs } e = .error f) : runOwn T { a with own := ys } e = .error f := by
  rw [runOwn_frame] at h ⊢
  cases h0 : runOwn T { a with own := [] } e with
  | error f' => rw [h0] at h; cases h; rfl
  | ok _ => rw [h0] at h; cases h

/-- The `i`-th waiting own effect runs, and then the one that waited `j`-th: as running the two from the step with both
taken out, the rest of the queue being a frame neither reads. -/
theorem pick_two (a : Acc v) {i j : Nat} (hi : i < a.own.length) (hj : j < a.own.length) (hij : i ≠ j) {b : Acc v}
    (hb : (ownSys T v).pick a i = .ok b) : ∃ A1, runOwn T { a with own := dropTwo a.own i j } a.own[i] = .ok A1 ∧
      (ownSys T v).pick b (afterErase i j) = runOwn T A1 a.own[j] ∧ afterErase i j < (ownSys T v).len b := by
  simp only [ownSys, List.getElem?_eq_getElem hi] at hb
  rw [runOwn_frame] at hb
  cases h0 : runOwn T { a with own := [] } a.own[i] with
  | error f => rw [h0] at hb; cases hb
  | ok b0 =>
    rw [h0] at hb
    cases hb
    have hlt := afterErase_lt hi hj hij
    refine ⟨b0.ownFront (dropTwo a.own i j), ?_, ?_, ?_⟩
    · rw [runOwn_frame]
      show (runOwn T { a with own := [] } a.own[i]).map _ = _
      rw [h0]; rfl
    · have hget : (a.own.eraseIdx i ++ b0.own)[afterErase i j]? = some a.own[j] := by
        rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt, getElem_afterErase hi hj hij]
      simp only [ownSys, Acc.ownFront, hget, List.eraseIdx_append_of_lt_length hlt]
      rfl
    · show afterErase i j < (a.own.eraseIdx i ++ b0.own).length
      rw [List.length_append]; omega

/-- Pairs that commute at the front of the queue, in the canonical form, make any two waiting own effects commute in
the cascade, wherever they wait. -/
theorem commutes_of_pairs (hv : v.Equivariant)
    (hP : ∀ a : Acc v, Supp a → ∀ i j (hi : i < a.own.length) (hj : j < a.own.length), i ≠ j →
      PairCommutes T { a with own := dropTwo a.own i j } a.own[i] a.own[j]) :
    Diamond.Commutes (ownSys T v) Supp Same := by
  intro a ha i j hi hj hij b hb
  obtain ⟨A1, hA1, hpb, hk⟩ := pick_two T a hi hj hij hb
  have hp := hP a ha i j hi hj hij A1 hA1
  have hsa : SelfAt a.state.fresh { a with own := dropTwo a.own i j } :=
    SelfAt.own ha.1 fun x hx => ha.2 x (mem_dropTwo hx)
  obtain ⟨⟨W, hl⟩, hac⟩ := actual_canon T hv (a0 := { a with own := dropTwo a.own i j }) hsa
    (ha.2 _ (List.getElem_mem hi)) (ha.2 _ (List.getElem_mem hj))
  refine ⟨fun c hc => ?_, fun e he => ?_⟩
  · obtain ⟨C1, hC1, hpc, hk'⟩ := pick_two T a hj hi (Ne.symm hij) hc
    rw [dropTwo_comm _ (Ne.symm hij)] at hC1
    refine ⟨_, hk, _, hk', ?_⟩
    rw [hpb, hpc]
    rcases hl with ⟨h1, -⟩ | ⟨_, c', _, h1, h2, -⟩
    · rw [hC1] at h1; exact h1.elim
    · exact (hp.1 c' h2).trans Diamond.Closure.equiv ((hac C1 hC1).symm Diamond.Closure.equiv)
  · refine ⟨_, hk, ?_⟩
    rw [hpb]
    simp only [ownSys, List.getElem?_eq_getElem hj] at he
    have h0 : runOwn T { a with own := dropTwo a.own i j } a.own[j] = .error e := runOwn_frame_error T he
    rcases hl with ⟨-, h2⟩ | ⟨_, _, _, h1, -⟩
    · revert h2
      cases hf : runOwn T (Acc.withFresh { a with own := dropTwo a.own i j } (a.state.fresh + 1)) a.own[j] with
      | error f => intro _; exact hp.2 f hf
      | ok _ => intro h2; exact h2.elim
    · rw [h0] at h1; cases h1

/-- Where every two waiting own effects of a step in progress whose names are below its counter commute in the
canonical sense, every order of the own cascade ends as `settle` does, up to renaming and reading collections as
multisets, or both fault. -/
theorem cascade_agrees (hv : v.Equivariant) (hkw : ∀ m ∈ v.machines, m.key.wire = true)
    (hP : ∀ a : Acc v, Supp a → ∀ i j (hi : i < a.own.length) (hj : j < a.own.length), i ≠ j →
      PairCommutes T { a with own := dropTwo a.own i j } a.own[i] a.own[j])
    (fuel : Nat) (a : Acc v) (ha : Supp a) {r : Except Fault (Acc v)} (hr : Diamond.Runs (ownSys T v) fuel a r) :
    Diamond.Agree Same r (settle T fuel a) :=
  settle_agrees T Diamond.Closure.equiv (ownSys_simulates T hv) (commutes_of_pairs T hv hP) (ownSys_preserved T hv hkw)
    fuel a ha hr

end Step

end Tazuna.Ir
