import Tazuna.Semantics.Support

/-! The question T5 asks of two waiting own effects, and why its answer covers every order of a cascade. Two own
effects `e1` and `e2` commute from a step in progress `a0` (where neither waits any more) when running `e1` then `e2`
ends as running them the other way round with the names swapped: `e2` takes the counter it gets after `e1`, and `e1`
the one it gets first, and the wire ids `e1` sends come before `e2`'s (`canonPair`), so each effect makes the same
names in both orders, and the results are compared up to renaming the names the two made, every name from before
kept, and reading collections as multisets (`PairCommutes`). This is the solver's question: in the canonical order the names already agree, so it has no renaming
to search for. Swapping the names back is a renaming the cascade respects, and the effects that
still wait are a frame no internal step reads, so pairs that commute at the front of the queue make every two waiting
effects commute wherever they wait (`commutes_of_pairs`), and every order of the cascade agrees with `settle` up to
renaming the names the cascade made (`cascade_agrees`). -/

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

/-- The wire ids from `n` to `m` and from `m` to `k` swapped as blocks, every other id kept: what two internal steps
sent from `n` on, renumbered as if the second had sent first. -/
def wireSwap (n m k i : Nat) : Nat :=
  if n ≤ i ∧ i < m then i + (k - m) else if m ≤ i ∧ i < k then i - (m - n) else i

theorem wireSwap_inj {n m k i j : Nat} (h : wireSwap n m k i = wireSwap n m k j) : i = j := by
  unfold wireSwap at h
  repeat' split at h
  all_goals omega

theorem wireSwap_lt {n m k i : Nat} (h : i < k) : wireSwap n m k i < k := by
  unfold wireSwap
  repeat' split
  all_goals omega

/-- `P` followed by the injective `σ`. -/
def PBij.post (P : PBij) (σ : Nat → Nat) (hσ : ∀ {i j}, σ i = σ j → i = j) : PBij where
  rel a b := ∃ c, P.rel a c ∧ b = σ c
  func := by rintro _ _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩; rw [P.func hc hc']
  inj := by rintro _ _ _ ⟨c, hc, rfl⟩ ⟨c', hc', h⟩; exact P.inj hc (hσ h ▸ hc')

namespace Step

variable {v : ServiceV} (T : List TypeDecl)

/-- The step in progress with the counter `k`. -/
def Acc.withFresh (a : Acc v) (k : Nat) : Acc v := { a with state := { a.state with fresh := k } }

/-- The step in progress with its wire ids renamed by `σ`. -/
def Acc.mapWire (σ : Nat → Nat) (a : Acc v) : Acc v :=
  { a with state := { a.state with pending := a.state.pending.map fun p => { p with id := σ p.id } },
           out := a.out.map fun o => { o with id := σ o.id } }

/-- Renaming the wire ids of one side by an injective `σ` that keeps them below the next one keeps the two related. -/
theorem Acc.Rel.mapWire {R : Ren} {a a' : Acc v} (h : Acc.Rel R a a') {σ : Nat → Nat}
    (hσ : ∀ {i j}, σ i = σ j → i = j) (hlt : ∀ i < a'.state.nextId, σ i < a'.state.nextId) :
    Acc.Rel ⟨R.ctr, R.wire.post σ hσ⟩ a (a'.mapWire σ) := by
  obtain ⟨⟨hrec, hmach, hpend, hnow, hb, hb'⟩, hev, hout, ho, ho', hown⟩ := h
  have hp := hpend.map (f := id) (r' := Pending.Rel ⟨R.ctr, R.wire.post σ hσ⟩)
    (g := fun p => { p with id := σ p.id }) fun _ _ hpq => ⟨⟨_, hpq.1, rfl⟩, hpq.2⟩
  have hq := hout.map (f := id) (r' := OutLine.Rel ⟨R.ctr, R.wire.post σ hσ⟩)
    (g := fun o => { o with id := σ o.id }) fun _ _ hpq => ⟨⟨_, hpq.1, rfl⟩, hpq.2⟩
  rw [List.map_id] at hp hq
  refine ⟨⟨hrec, hmach, hp, hnow, hb, ?_⟩, hev, hq, ho, ?_, hown⟩
  · simp only [Acc.mapWire, List.mem_map]
    rintro _ ⟨p, hp, rfl⟩
    exact hlt _ (hb' p hp)
  · simp only [Acc.mapWire, List.mem_map]
    rintro _ ⟨o, ho, rfl⟩
    exact hlt _ (ho' o ho)

/-- `e2` then `e1` with each effect's names as they are when `e1` runs first: `e2` takes the counter after `e1`'s, and
the wire ids `e1` sends come first, then `e2`'s. -/
def canonPair (a0 : Acc v) (e1 e2 : OwnEffectV v.event) : Except Fault (Acc v) := do
  let c ← runOwn T (a0.withFresh (a0.state.fresh + 1)) e2
  let d ← runOwn T (c.withFresh a0.state.fresh) e1
  pure ((d.withFresh (a0.state.fresh + 2)).mapWire (wireSwap a0.state.nextId c.state.nextId d.state.nextId))

/-- Two own effects commute from `a0`: where `e1` runs, `e2` after it ends as the canonical other order does, up to
renaming the names the two made, or both fault; and if `e2` faults first, it still faults after `e1`. -/
def PairCommutes (a0 : Acc v) (e1 e2 : OwnEffectV v.event) : Prop :=
  ∀ b, runOwn T a0 e1 = .ok b →
    (∀ c, runOwn T (a0.withFresh (a0.state.fresh + 1)) e2 = .ok c →
      Diamond.Agree (Same a0.state.fresh a0.state.nextId) (runOwn T b e2) (canonPair T a0 e1 e2)) ∧
    (∀ f, runOwn T (a0.withFresh (a0.state.fresh + 1)) e2 = .error f → Diamond.Faults (runOwn T b e2))

theorem Acc.Rel.withFresh {R : Ren} {a a' : Acc v} (h : Acc.Rel R a a') (k k' : Nat) :
    Acc.Rel R (a.withFresh k) (a'.withFresh k') := h

/-- Running `e2` first with its own counter or with the counter it has after `e1` differs by swapping the two
counters, and the canonical order's wire ids differ from the actual other order's by swapping two blocks, so the two
orders agree up to renaming the names the two made. -/
theorem actual_canon (hv : v.Equivariant) {a0 : Acc v} (ha : Below Acc.Self a0.state.fresh a0)
    {e1 e2 : OwnEffectV v.event} (he1 : Below (fun P x => OwnEffectV.Rel P x x) a0.state.fresh e1)
    (he2 : Below (fun P x => OwnEffectV.Rel P x x) a0.state.fresh e2) :
    Lifted ⟨PBij.swap a0.state.fresh, PBij.refl⟩ a0
        (a0.withFresh (a0.state.fresh + 1)) (runOwn T a0 e2) (runOwn T (a0.withFresh (a0.state.fresh + 1)) e2) ∧
      ∀ c1, runOwn T a0 e2 = .ok c1 →
        Diamond.Agree (Same a0.state.fresh a0.state.nextId) (runOwn T c1 e1) (canonPair T a0 e1 e2) := by
  generalize hf : a0.state.fresh = f at ha he1 he2 ⊢
  have hA := (ha _ (PBij.swap_fixes f)).1
  have hctr : (PBij.swap f).rel f (f + 1) := by show _ = _; simp [swapFn]
  have hl := runOwn_rel T hv (R := ⟨PBij.swap f, PBij.refl⟩) (a := a0) (a' := a0.withFresh (f + 1))
    (hA.withFresh f (f + 1)) (by rw [hf]; exact hctr) (he2 _ (PBij.swap_fixes f))
  refine ⟨hl, fun c1 hc1 => ?_⟩
  have hfr1 : c1.state.fresh = f + 1 := by rw [runOwn_fresh T hc1, hf]
  rcases hl with ⟨h1, -⟩ | ⟨b, c', R', h1, h2, hc, hb, -, -, hn, hl1, hw1⟩
  · rw [hc1] at h1; exact h1.elim
  · rw [hc1] at h1; cases h1
    have hfr' : c'.state.fresh = f + 2 := runOwn_fresh T h2
    have hctr2 : R'.ctr.rel (f + 1) f := by rw [hc]; show _ = _; simp [swapFn]
    have hl2 := runOwn_rel T hv (hb.withFresh (f + 1) f) hctr2 (by rw [hc]; exact he1 _ (PBij.swap_fixes f))
    simp only [canonPair, hf, h2, bind, Except.bind]
    have hb1 : c1 = c1.withFresh (f + 1) := by rw [← hfr1]; rfl
    rw [← hb1] at hl2
    rcases hl2 with ⟨h3, h4⟩ | ⟨d, d', R'', h3, h4, hc', hd, -, -, hn', hl2, hw2⟩
    · refine .inr ⟨h3, ?_⟩
      revert h4
      cases runOwn T (c'.withFresh f) e1 <;> intro h4
      · trivial
      · exact h4.elim
    · rw [h3, h4]
      have hfd : d.state.fresh = f + 2 := by rw [runOwn_fresh T h3, hfr1]
      simp only [Acc.withFresh] at hn hn' hl1 hl2 hw1 hw2
      refine .inl (.base ⟨_, (hd.withFresh d.state.fresh (f + 2)).mapWire wireSwap_inj fun _ => wireSwap_lt,
        ?_, ?_, ?_, fun n hn2 => ?_, fun i hi => ?_⟩)
      · show d.state.fresh = f + 2; exact hfd
      · show d.state.nextId = d'.state.nextId
        omega
      · show a0.state.nextId ≤ d.state.nextId
        omega
      · show R''.ctr.rel n n
        rw [hc', hc]
        rcases hn2 with hn2 | hn2
        · exact PBij.swap_fixes f n hn2
        · exact PBij.swap_above (show f + 2 ≤ n by rw [← hfd]; exact hn2)
      · refine ⟨i, hw2 (by omega) (by omega) (hw1 hi (by omega) rfl), ?_⟩
        show i = wireSwap a0.state.nextId c'.state.nextId d'.state.nextId i
        unfold wireSwap; split <;> (try split) <;> omega

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
  List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx h)

theorem runOwn_frame (a : Acc v) (xs : List (OwnEffectV v.event)) (e : OwnEffectV v.event) :
    runOwn T { a with own := xs } e = (runOwn T { a with own := [] } e).map (Acc.ownFront xs) := by
  have h := runOwn_own T xs { a with own := [] } e
  simp only [Acc.ownFront, List.append_nil] at h
  exact h

theorem runOwn_frame_error {a : Acc v} {xs ys : List (OwnEffectV v.event)} {e : OwnEffectV v.event} {f : Fault}
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

/-- An own step from a step whose names are below its counter sends from the next wire id on. -/
theorem runOwn_nextId (hv : v.Equivariant) {a : Acc v} (ha : Supp a) {i : Nat}
    (hi : i < a.own.length) {b : Acc v} (hb : runOwn T { a with own := a.own.eraseIdx i } a.own[i] = .ok b) :
    a.state.nextId ≤ b.state.nextId := by
  have hA := ha PBij.refl fun _ _ => rfl
  have hl := runOwn_rel T hv (hA.sub_own (xs := a.own.eraseIdx i) fun x hx => List.mem_of_mem_eraseIdx hx).1 rfl
    (hA.2.2 _ (List.getElem_mem hi))
  rw [hb] at hl
  rcases hl with ⟨h, -⟩ | ⟨_, _, _, h1, -, -, -, -, -, -, hl, -⟩
  · exact h.elim
  · cases h1; exact hl

/-- The own cascade from a step with the counter `f0` and the next wire id `n0` keeps every name below the counter
and the two numbers no lower. -/
theorem suppFrom_preserved (hv : v.Equivariant) (f0 n0 : Nat) : Diamond.Preserved (ownSys T v)
    fun a => Supp a ∧ f0 ≤ a.state.fresh ∧ n0 ≤ a.state.nextId := by
  intro a i b ⟨ha, hf, hn⟩ hi hb
  refine ⟨ownSys_preserved T hv a i b ha hi hb, ?_, ?_⟩
  · simp only [ownSys, List.getElem?_eq_getElem hi] at hb
    have := runOwn_fresh T hb
    simp only at this; omega
  · simp only [ownSys, List.getElem?_eq_getElem hi] at hb
    have := runOwn_nextId T hv ha hi hb
    omega

/-- Pairs that commute at the front of the queue, in the canonical form, wherever `J` holds, make any two waiting own
effects commute in the cascade there, wherever they wait, up to renaming the names made from the cascade's start on. -/
theorem commutes_of_pairs (hv : v.Equivariant) {J : Acc v → Prop}
    (hP : ∀ a : Acc v, Supp a → J a → ∀ i j (hi : i < a.own.length) (hj : j < a.own.length),
      i ≠ j → PairCommutes T { a with own := dropTwo a.own i j } a.own[i] a.own[j]) (f0 n0 : Nat) :
    Diamond.Commutes (ownSys T v)
      (fun a => (Supp a ∧ f0 ≤ a.state.fresh ∧ n0 ≤ a.state.nextId) ∧ J a) (Same f0 n0) := by
  intro a ⟨⟨ha, hf0, hn0⟩, hJ⟩ i j hi hj hij b hb
  obtain ⟨A1, hA1, hpb, hk⟩ := pick_two T a hi hj hij hb
  have hp := hP a ha hJ i j hi hj hij A1 hA1
  obtain ⟨hl, hac⟩ := actual_canon T hv (a0 := { a with own := dropTwo a.own i j })
    (fun P hP => (ha P hP).sub_own fun x hx => mem_dropTwo hx)
    (fun P hP => (ha P hP).2.2 _ (List.getElem_mem hi)) (fun P hP => (ha P hP).2.2 _ (List.getElem_mem hj))
  refine ⟨fun c hc => ?_, fun e he => ?_⟩
  · obtain ⟨C1, hC1, hpc, hk'⟩ := pick_two T a hj hi (Ne.symm hij) hc
    rw [dropTwo_comm _ (Ne.symm hij)] at hC1
    refine ⟨_, hk, _, hk', ?_⟩
    rw [hpb, hpc]
    rcases hl with ⟨h1, -⟩ | ⟨_, c', _, h1, h2, -⟩
    · rw [hC1] at h1; exact h1.elim
    · exact Diamond.Agree.mono (fun h => Same.mono hf0 hn0 h)
        ((hp.1 c' h2).trans Diamond.Closure.equiv ((hac C1 hC1).symm Diamond.Closure.equiv))
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
canonical sense, at every step in progress where `J` holds, which internal steps keep, every order of the own cascade
from one where it holds ends as `settle` does, up to renaming the names the cascade made and reading collections as
multisets, or both fault. -/
theorem cascade_agrees (hv : v.Equivariant) {J : Acc v → Prop} (hJ : Diamond.Preserved (ownSys T v) J)
    (hP : ∀ a : Acc v, Supp a → J a → ∀ i j (hi : i < a.own.length) (hj : j < a.own.length),
      i ≠ j → PairCommutes T { a with own := dropTwo a.own i j } a.own[i] a.own[j])
    (fuel : Nat) (a : Acc v) (ha : Supp a) (haJ : J a) {r : Except Fault (Acc v)}
    (hr : Diamond.Runs (ownSys T v) fuel a r) :
    Diamond.Agree (Same a.state.fresh a.state.nextId) r (settle T fuel a) :=
  settle_agrees T Diamond.Closure.equiv (ownSys_simulates T hv _ _) (commutes_of_pairs T hv hP _ _)
    (fun b i c hb hi hc => ⟨suppFrom_preserved T hv _ _ b i c hb.1 hi hc, hJ b i c hb.2 hi hc⟩) fuel a
    ⟨⟨ha, Nat.le_refl _, Nat.le_refl _⟩, haJ⟩ hr

end Step

end Tazuna.Ir
