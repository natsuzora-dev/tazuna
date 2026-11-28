import Tazuna.Explore.Move
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas

/-! What `explore` covers: every transition of every run of the scope's inputs within the coverage it reports shows
only classes, faults and broken responses it lists (`explore_sound`). A breadth-first search keeps one node per key;
nodes with equal keys are related (`key_link`), and related nodes move alike (`link_move`), so a run through a node
it did not keep moves as one through the node it kept. -/

namespace Tazuna.Explore

open Tazuna.Ir Tazuna.Ir.Step

variable {T : List TypeDecl} {v : ServiceV} {sc : ScopeV}

/-- The nodes explore reaches from the initial one in `k` transitions on the scope's inputs, faulting nowhere. -/
inductive Reach (T : List TypeDecl) (sc : ScopeV) : Nat → Node v → Prop
  | init : Reach T sc 0 (Node.init v)
  | step {k : Nat} {n n' : Node v} {x : Input v} : Reach T sc k n → x ∈ inputsOf sc n → (move T n x).next = some n' →
    Reach T sc (k + 1) n'

theorem move_next_state {n n' : Node v} {x : Input v} (h : (move T n x).next = some n') :
    n'.state = (step T v n.state x).state := by
  unfold move at h
  simp only at h
  split at h
  · cases h
  · cases h; rfl

theorem Reach.inv {P : List AnySite} {E : List AnyEffectSite} (hv : v.Reach P E) {k : Nat} {n : Node v}
    (h : Reach T sc k n) : Inv P n.state := by
  induction h with
  | init => exact init_inv
  | step _ _ hn ih => rw [move_next_state hn]; exact step_inv T hv _ ih _

/-- The search keeps the transition from `n` on `x`: each class it shows, the fault it ends in and each response it
breaks. -/
structure Recorded (T : List TypeDecl) (st : SearchSt v) (n : Node v) (x : Input v) : Prop where
  classes : ∀ c ∈ classes T v x (move T n x).result, st.byClass.contains c = true
  faults : ∀ f, (move T n x).result.outcome = .fault f → st.byFault.contains f = true
  responses : ∀ j ∈ (move T n x).broken, st.byResp.contains j = true

/-- `st'` keeps everything `st` keeps. -/
structure Ext (st st' : SearchSt v) : Prop where
  byClass : ∀ c, st.byClass.contains c = true → st'.byClass.contains c = true
  byFault : ∀ f, st.byFault.contains f = true → st'.byFault.contains f = true
  byResp : ∀ j, st.byResp.contains j = true → st'.byResp.contains j = true
  seen : ∀ key, st.seen.contains key = true → st'.seen.contains key = true
  size : st.nodes.size ≤ st'.nodes.size
  nodes : ∀ i (h : i < st.nodes.size), st'.nodes[i]'(Nat.lt_of_lt_of_le h size) = st.nodes[i]

theorem Ext.refl (st : SearchSt v) : Ext st st :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, Nat.le_refl _, fun _ _ => rfl⟩

theorem Ext.trans {st st' st'' : SearchSt v} (h : Ext st st') (h' : Ext st' st'') : Ext st st'' :=
  ⟨fun c hc => h'.byClass c (h.byClass c hc), fun f hf => h'.byFault f (h.byFault f hf),
    fun j hj => h'.byResp j (h.byResp j hj), fun k hk => h'.seen k (h.seen k hk), Nat.le_trans h.size h'.size,
    fun i hi => (h'.nodes i (Nat.lt_of_lt_of_le hi h.size)).trans (h.nodes i hi)⟩

theorem Recorded.mono {st st' : SearchSt v} (h : Ext st st') {n : Node v} {x : Input v} (hr : Recorded T st n x) :
    Recorded T st' n x :=
  ⟨fun c hc => h.byClass c (hr.classes c hc), fun f hf => h.byFault f (hr.faults f hf),
    fun j hj => h.byResp j (hr.responses j hj)⟩

/-- What the search keeps true: every key it holds is a kept node's, every node it keeps is reached, and every class
and fault it keeps is in its order. -/
structure Good (T : List TypeDecl) (sc : ScopeV) (st : SearchSt v) : Prop where
  seen : ∀ key, st.seen.contains key = true → ∃ i, ∃ h : i < st.nodes.size, (st.nodes[i]).1.key = key
  reach : ∀ i (h : i < st.nodes.size), ∃ k, Reach T sc k (st.nodes[i]).1
  classOrder : ∀ c, st.byClass.contains c = true → c ∈ st.classOrder
  faultOrder : ∀ f, st.byFault.contains f = true → f ∈ st.faultOrder

section AddHit
variable {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] (hit : Hit v)

theorem addHit_mono (acc : Std.HashMap κ (Hit v) × Array κ × Bool) (c d : κ) (h : acc.1.contains d = true) :
    (addHit hit acc c).1.contains d = true := by
  unfold addHit
  split
  · exact h
  · simp [Std.HashMap.contains_insert, h]

theorem addHit_self (acc : Std.HashMap κ (Hit v) × Array κ × Bool) (c : κ) : (addHit hit acc c).1.contains c = true := by
  unfold addHit
  split
  · assumption
  · simp [Std.HashMap.contains_insert]

theorem addHit_order (acc : Std.HashMap κ (Hit v) × Array κ × Bool) (hacc : ∀ d, acc.1.contains d = true → d ∈ acc.2.1)
    (c : κ) : ∀ d, (addHit hit acc c).1.contains d = true → d ∈ (addHit hit acc c).2.1 := by
  intro d hd
  unfold addHit at hd ⊢
  by_cases hc : acc.1.contains c = true
  · simp only [hc, ↓reduceIte] at hd ⊢
    exact hacc d hd
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hd ⊢
    simp only [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hd
    simp only [Array.mem_push]
    rcases hd with rfl | hd
    · exact .inr rfl
    · exact .inl (hacc d hd)

theorem foldl_addHit (l : List κ) : (acc : Std.HashMap κ (Hit v) × Array κ × Bool) →
    (∀ d, acc.1.contains d = true → (l.foldl (addHit hit) acc).1.contains d = true) ∧
    (∀ c ∈ l, (l.foldl (addHit hit) acc).1.contains c = true) ∧
    ((∀ d, acc.1.contains d = true → d ∈ acc.2.1) →
      ∀ d, (l.foldl (addHit hit) acc).1.contains d = true → d ∈ (l.foldl (addHit hit) acc).2.1) := by
  induction l with
  | nil => intro acc; exact ⟨fun _ h => h, by simp, fun h => h⟩
  | cons c l ih =>
    intro acc
    obtain ⟨h1, h2, h3⟩ := ih (addHit hit acc c)
    refine ⟨fun d hd => h1 d (addHit_mono hit acc c d hd), fun d hd => ?_, fun h => h3 (addHit_order hit acc h c)⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h1 d (addHit_self hit acc d)
    · exact h2 d hd

end AddHit

section Visit
variable {cap k i : Nat} {n : Node v} {st : SearchSt v} {x : Input v}

/-- What `keep` does: keeps the keys, keeps the nodes or adds the node reached, and holds its key unless the level hit
the cap. -/
theorem keep_spec (next : Option (Node v)) :
    (∀ key, st.seen.contains key = true → (keep cap i x st next).2.1.contains key = true) ∧
    ((keep cap i x st next).1 = st.nodes ∧
        (∀ key, (keep cap i x st next).2.1.contains key = true → st.seen.contains key = true) ∨
      ∃ n', next = some n' ∧ (keep cap i x st next).1 = st.nodes.push (n', i, some x) ∧
        ∀ key, (keep cap i x st next).2.1.contains key = true → st.seen.contains key = true ∨ n'.key = key) ∧
    (∀ n', next = some n' → (keep cap i x st next).2.2 = true ∨ (keep cap i x st next).2.1.contains n'.key = true) ∧
    (st.full = true → (keep cap i x st next).2.2 = true) := by
  cases next with
  | none => exact ⟨fun _ h => h, .inl ⟨rfl, fun _ h => h⟩, (fun _ h => nomatch h), fun h => h⟩
  | some n' =>
    simp only [keep]
    by_cases h1 : (st.full || st.seen.contains n'.key) = true
    · rw [ite_eq_left_iff.2 (fun h => absurd h1 h)]
      refine ⟨fun _ h => h, .inl ⟨rfl, fun _ h => h⟩, fun m hm => ?_, fun h => h⟩
      cases hm
      simpa [Bool.or_eq_true] using h1
    · rw [ite_eq_right_iff.2 (fun h => absurd h h1)]
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1
      by_cases h2 : st.nodes.size ≥ cap
      · rw [ite_eq_left_iff.2 (fun h => absurd h2 h)]
        exact ⟨fun _ h => h, .inl ⟨rfl, fun _ h => h⟩, fun _ _ => .inl rfl, fun h => absurd h (by simp [h1.1])⟩
      · rw [ite_eq_right_iff.2 (fun h => absurd h h2)]
        refine ⟨fun key h => ?_, .inr ⟨n', rfl, rfl, fun key h => ?_⟩, fun m hm => ?_, fun h => ?_⟩
        · simp [Std.HashSet.contains_insert, h]
        · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
          exact h.symm
        · cases hm
          exact .inr (by simp [Std.HashSet.contains_insert])
        · simp [h1.1] at h

theorem visit_spec (hg : Good T sc st) (hn : ∃ k, Reach T sc k n) (hx : x ∈ inputsOf sc n) :
    Good T sc (visit T cap k i n st x) ∧ Ext st (visit T cap k i n st x) ∧ Recorded T (visit T cap k i n st x) n x ∧
      (∀ n', (move T n x).next = some n' →
        (visit T cap k i n st x).full = true ∨ (visit T cap k i n st x).seen.contains n'.key = true) ∧
      (st.full = true → (visit T cap k i n st x).full = true) := by
  obtain ⟨kk, hkk⟩ := hn
  have hc := foldl_addHit ⟨k + 1, st.order, i, x⟩ (classes T v x (move T n x).result) (st.byClass, st.classOrder, false)
  have hr := foldl_addHit ⟨k + 1, st.order, i, x⟩ (move T n x).broken (st.byResp, #[], false)
  have hf : (∀ f, st.byFault.contains f = true → (match (move T n x).result.outcome with
        | .fault f => addHit ⟨k + 1, st.order, i, x⟩ (st.byFault, st.faultOrder, false) f
        | _ => (st.byFault, st.faultOrder, false)).1.contains f = true) ∧
      (∀ f, (move T n x).result.outcome = .fault f → (match (move T n x).result.outcome with
        | .fault f => addHit ⟨k + 1, st.order, i, x⟩ (st.byFault, st.faultOrder, false) f
        | _ => (st.byFault, st.faultOrder, false)).1.contains f = true) ∧
      (∀ f, (match (move T n x).result.outcome with
        | .fault f => addHit ⟨k + 1, st.order, i, x⟩ (st.byFault, st.faultOrder, false) f
        | _ => (st.byFault, st.faultOrder, false)).1.contains f = true → f ∈ (match (move T n x).result.outcome with
        | .fault f => addHit ⟨k + 1, st.order, i, x⟩ (st.byFault, st.faultOrder, false) f
        | _ => (st.byFault, st.faultOrder, false)).2.1) := by
    generalize (move T n x).result.outcome = o
    cases o with
    | fault f =>
      refine ⟨fun d hd => addHit_mono _ _ f d hd, fun d hd => ?_, addHit_order _ _ hg.faultOrder f⟩
      simp only [Outcome.fault.injEq] at hd
      subst hd
      exact addHit_self _ _ _
    | _ => exact ⟨fun _ h => h, (fun _ h => nomatch h), hg.faultOrder⟩
  have hk := keep_spec (cap := cap) (i := i) (x := x) (st := st) (move T n x).next
  unfold visit
  dsimp only
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk
  refine ⟨⟨fun key hkey => ?_, fun j hj => ?_, hc.2.2 hg.classOrder, hf.2.2⟩, ⟨hc.1, hf.1, hr.1, hk1, ?_, ?_⟩,
    ⟨hc.2.1, hf.2.1, hr.2.1⟩, hk3, hk4⟩
  · rcases hk2 with ⟨he, hs⟩ | ⟨n', hnext, he, hs⟩
    · obtain ⟨j, hj, e⟩ := hg.seen key (hs key hkey)
      exact ⟨j, by rw [he]; exact hj, by simp only [he]; exact e⟩
    · rcases hs key hkey with hs | hs
      · obtain ⟨j, hj, e⟩ := hg.seen key hs
        exact ⟨j, by rw [he]; simp; omega, by simp only [he, Array.getElem_push_lt hj]; exact e⟩
      · exact ⟨st.nodes.size, by rw [he]; simp, by simp only [he, Array.getElem_push_eq]; exact hs⟩
  · rcases hk2 with ⟨he, -⟩ | ⟨n', hnext, he, -⟩
    · simp only [he] at hj ⊢; exact hg.reach j hj
    · simp only [he] at hj ⊢
      by_cases hlt : j < st.nodes.size
      · rw [Array.getElem_push_lt hlt]; exact hg.reach j hlt
      · have : j = st.nodes.size := by simp at hj; omega
        subst this
        rw [Array.getElem_push_eq]
        exact ⟨kk + 1, .step hkk hx hnext⟩
  · rcases hk2 with ⟨he, -⟩ | ⟨n', -, he, -⟩ <;> simp [he]
  · intro j hj
    rcases hk2 with ⟨he, -⟩ | ⟨n', -, he, -⟩
    · simp only [he]
    · simp only [he, Array.getElem_push_lt hj]

theorem foldl_spec {α σ : Type} (f : σ → α → σ) (I : σ → Prop) (E : σ → σ → Prop) (Q : σ → α → Prop)
    (hrefl : ∀ s, E s s) (htrans : ∀ s s' s'', E s s' → E s' s'' → E s s'') (hQ : ∀ s s' a, E s s' → Q s a → Q s' a) :
    (l : List α) → (∀ s a, a ∈ l → I s → I (f s a) ∧ E s (f s a) ∧ Q (f s a) a) → ∀ s, I s →
    I (l.foldl f s) ∧ E s (l.foldl f s) ∧ ∀ a ∈ l, Q (l.foldl f s) a
  | [], _, s, hs => ⟨hs, hrefl s, fun _ h => nomatch h⟩
  | a :: l, hstep, s, hs => by
    obtain ⟨h1, h2, h3⟩ := hstep s a List.mem_cons_self hs
    obtain ⟨h4, h5, h6⟩ := foldl_spec f I E Q hrefl htrans hQ l (fun s b hb => hstep s b (List.mem_cons_of_mem _ hb))
      (f s a) h1
    refine ⟨h4, htrans _ _ _ h2 h5, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hQ _ _ _ h5 h3
    · exact h6 b hb

/-- The transition from `n` on `x` is kept, and the node it reaches is kept unless the level hit the cap. -/
def Done (T : List TypeDecl) (st : SearchSt v) (n : Node v) (x : Input v) : Prop :=
  Recorded T st n x ∧ ∀ n', (move T n x).next = some n' → st.full = true ∨ st.seen.contains n'.key = true

/-- `st'` keeps everything `st` keeps, and holds the cap once `st` does. -/
def Ext' (st st' : SearchSt v) : Prop := Ext st st' ∧ (st.full = true → st'.full = true)

theorem Done.mono {st st' : SearchSt v} (h : Ext' st st') {n : Node v} {x : Input v} (hd : Done T st n x) :
    Done T st' n x :=
  ⟨hd.1.mono h.1, fun n' hn => (hd.2 n' hn).imp (h.2 ·) (h.1.seen _ ·)⟩

theorem level_spec {cap k : Nat} {st : SearchSt v} (hg : Good T sc st) (lo hi : Nat) (hhi : hi ≤ st.nodes.size) :
    Good T sc (level T sc cap k st lo hi) ∧ Ext' st (level T sc cap k st lo hi) ∧
      ∀ i (h : i < st.nodes.size), lo ≤ i → i < hi → ∀ x ∈ inputsOf sc (st.nodes[i]).1,
        Done T (level T sc cap k st lo hi) (st.nodes[i]).1 x := by
  have hext' : ∀ s : SearchSt v, Ext' s s := fun s => ⟨Ext.refl s, id⟩
  have htr : ∀ s s' s'' : SearchSt v, Ext' s s' → Ext' s' s'' → Ext' s s'' :=
    fun _ _ _ h h' => ⟨h.1.trans h'.1, h'.2 ∘ h.2⟩
  obtain ⟨h1, h2, h3⟩ := foldl_spec (l := List.range' lo (hi - lo))
    (I := fun s => Good T sc s ∧ Ext' st s)
    (E := Ext')
    (Q := fun s i => ∀ (h : i < st.nodes.size), ∀ x ∈ inputsOf sc (st.nodes[i]).1, Done T s (st.nodes[i]).1 x)
    (f := fun st i => match st.nodes[i]? with
      | some (n, _, _) => (inputsOf sc n).foldl (visit T cap k i n) st
      | none => st)
    hext' htr (fun s s' i h hq hi x hx => (hq hi x hx).mono h) (fun s i hi ⟨hgs, hes⟩ => by
      have hilt : i < st.nodes.size := by simp [List.mem_range'] at hi; omega
      have hsi : s.nodes[i]? = some st.nodes[i] := by
        rw [Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le hilt hes.1.size), hes.1.nodes i hilt]
      simp only [hsi]
      have hreach := hg.reach i hilt
      obtain ⟨g1, g2, g3⟩ := foldl_spec (l := inputsOf sc (st.nodes[i]).1)
        (I := Good T sc) (E := Ext') (Q := fun s x => Done T s (st.nodes[i]).1 x)
        (f := visit T cap k i (st.nodes[i]).1) hext' htr (fun _ _ _ h hq => hq.mono h)
        (fun s x hx hgs => by
          obtain ⟨v1, v2, v3, v4, v5⟩ := visit_spec (cap := cap) (k := k) (i := i) (st := s) hgs hreach hx
          exact ⟨v1, ⟨v2, v5⟩, v3, v4⟩) s hgs
      exact ⟨⟨g1, htr _ _ _ hes g2⟩, g2, fun _ x hx => g3 x hx⟩) st ⟨hg, hext' st⟩
  exact ⟨h1.1, h2, fun i hs hlo hhi' x hx => h3 i (List.mem_range'_1.2 ⟨hlo, by omega⟩) hs x hx⟩

end Visit

section Sim
variable {P : List AnySite} {E : List AnyEffectSite}

/-- Linked nodes of states with the step invariant. -/
def Lk (P : List AnySite) (a b : Node v) : Prop := Link a b ∧ Inv P a.state ∧ Inv P b.state

/-- Nodes a chain of links relates: no run tells them apart. -/
inductive Sim (P : List AnySite) : Node v → Node v → Prop
  | refl (a : Node v) : Sim P a a
  | tail {a b c : Node v} : Sim P a b → Lk P b c → Sim P a c

theorem option_rel_refl {α : Type} {r : α → α → Prop} (hr : ∀ a, r a a) : (x : Option α) → Option.Rel r x x
  | none => .none
  | some a => .some (hr a)

/-- Related nodes move alike, through any chain of links. -/
theorem sim_move (chk : Smt.Checked P E T v) (ho : Ordered T v) {a b : Node v} (h : Sim P a b) {x : Input v} (hx : x ∈ inputsOf sc a) :
    ∃ x' ∈ inputsOf sc b, classes T v x (move T a x).result = classes T v x' (move T b x').result ∧
      (∀ f, (move T a x).result.outcome = .fault f ↔ (move T b x').result.outcome = .fault f) ∧
      (move T a x).broken = (move T b x').broken ∧ Option.Rel (Sim P) (move T a x).next (move T b x').next := by
  induction h with
  | refl => exact ⟨x, hx, rfl, fun _ => Iff.rfl, rfl, option_rel_refl Sim.refl _⟩
  | @tail b c h1 hl ih =>
    obtain ⟨xb, hxb, e1, e2, e3, e4⟩ := ih
    obtain ⟨xc, hxc, f1, f2, f3, f4⟩ := link_move chk ho sc hl.1 hl.2.1 hxb
    refine ⟨xc, hxc, e1.trans f1, fun f => (e2 f).trans (f2 f), e3.trans f3, ?_⟩
    have hb' : ∀ n', (move T b xb).next = some n' → Inv P n'.state := fun n' hn => by
      rw [move_next_state hn]; exact step_inv T chk.reach _ hl.2.1 _
    have hc' : ∀ n', (move T c xc).next = some n' → Inv P n'.state := fun n' hn => by
      rw [move_next_state hn]; exact step_inv T chk.reach _ hl.2.2 _
    revert e4 f4 hb' hc'
    generalize (move T a x).next = na
    generalize (move T b xb).next = nb
    generalize (move T c xc).next = nc
    intro e4 f4 hb' hc'
    cases e4 with
    | none => cases f4; exact .none
    | some hs =>
      cases f4 with
      | some hl' => exact .some (.tail hs ⟨hl', hb' _ rfl, hc' _ rfl⟩)

/-- A transition from a node related to a kept node whose transitions reach kept keys reaches a node related to a
kept node. -/
theorem sim_step (chk : Smt.Checked P E T v) (hv : v.Equivariant) {st : SearchSt v} (hg : Good T sc st) {i : Nat}
    (hi : i < st.nodes.size)
    (hcl : ∀ x ∈ inputsOf sc (st.nodes[i]).1, ∀ n', (move T (st.nodes[i]).1 x).next = some n' →
      st.seen.contains n'.key = true)
    {m0 m : Node v} (hs : Sim P m0 (st.nodes[i]).1) {x : Input v}
    (hx : x ∈ inputsOf sc m0) (hn : (move T m0 x).next = some m) :
    ∃ i' : Nat, ∃ h : i' < st.nodes.size, Sim P m (st.nodes[i']).1 := by
  have ho : Ordered T v := ⟨hv, fun m hm => (chk.keys m hm).2⟩
  obtain ⟨x', hx', -, -, -, hrel⟩ := sim_move chk ho hs hx
  rw [hn] at hrel
  revert hrel
  generalize hnext : (move T (st.nodes[i]).1 x').next = o
  intro hrel
  cases hrel with
  | some hsim =>
    rename_i n''
    obtain ⟨i', hi', hkey⟩ := hg.seen _ (hcl x' hx' n'' hnext)
    obtain ⟨k, hk⟩ := hg.reach i hi
    obtain ⟨k', hk'⟩ := hg.reach i' hi'
    have hn'' : Reach T sc (k + 1) n'' := .step hk hx' hnext
    exact ⟨i', hi', .tail hsim ⟨key_link chk hv (hn''.inv chk.reach) (hk'.inv chk.reach) hkey.symm,
      hn''.inv chk.reach, hk'.inv chk.reach⟩⟩

/-- Where every kept node's transitions are kept and reach kept keys, every node reached relates to a kept node. -/
theorem closed_all (chk : Smt.Checked P E T v) (hv : v.Equivariant) {st : SearchSt v} (hg : Good T sc st)
    (hcl : ∀ i (h : i < st.nodes.size), ∀ x ∈ inputsOf sc (st.nodes[i]).1, ∀ n',
      (move T (st.nodes[i]).1 x).next = some n' → st.seen.contains n'.key = true)
    (h0 : ∃ i, ∃ h : i < st.nodes.size, Sim P (Node.init v) (st.nodes[i]).1) :
    ∀ {j : Nat} {m : Node v}, Reach T sc j m → ∃ i, ∃ h : i < st.nodes.size, Sim P m (st.nodes[i]).1 := by
  intro j m hm
  induction hm with
  | init => exact h0
  | step hm0 hx hn ih =>
    obtain ⟨i, hi, hs⟩ := ih
    exact sim_step chk hv hg hi (hcl i hi) hs hx hn

theorem good_full {st : SearchSt v} (hg : Good T sc st) (b : Bool) : Good T sc { st with full := b } :=
  ⟨hg.seen, hg.reach, hg.classOrder, hg.faultOrder⟩

theorem ext_full (st : SearchSt v) (b : Bool) : Ext st { st with full := b } :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, Nat.le_refl _, fun _ _ => rfl⟩

/-- Where the search stops with the nodes below `lo` closed and `k` levels covered: what it covers relates to a kept
node whose transitions are all kept. -/
theorem stop_case (chk : Smt.Checked P E T v) (hv : v.Equivariant) {st : SearchSt v} {k lo hi : Nat}
    (hg : Good T sc st) (hhi : hi = st.nodes.size)
    (hC : ∀ i (h : i < st.nodes.size), i < lo → ∀ x ∈ inputsOf sc (st.nodes[i]).1,
      Recorded T st (st.nodes[i]).1 x ∧
        ∀ n', (move T (st.nodes[i]).1 x).next = some n' → st.seen.contains n'.key = true)
    (hD1 : ∀ j < k, ∀ m, Reach T sc j m → ∃ i, ∃ h : i < st.nodes.size, i < lo ∧ Sim P m (st.nodes[i]).1)
    (hD2 : ∀ j ≤ k, ∀ m, Reach T sc j m → ∃ i, ∃ h : i < st.nodes.size, Sim P m (st.nodes[i]).1)
    {j : Nat} {m : Node v} (hm : Reach T sc j m) (hcov : j < k ∨ decide (lo = hi) = true) :
    Good T sc st ∧ ∃ e ∈ st.nodes, Sim P m e.1 ∧ ∀ x ∈ inputsOf sc e.1, Recorded T st e.1 x := by
  refine ⟨hg, ?_⟩
  rcases hcov with hj | he
  · obtain ⟨i, hi, hil, hs⟩ := hD1 j hj m hm
    exact ⟨_, Array.getElem_mem hi, hs, fun x hx => (hC i hi hil x hx).1⟩
  · simp only [decide_eq_true_eq] at he
    subst he
    have hall : ∀ i (h : i < st.nodes.size), i < lo := fun i h => by omega
    obtain ⟨i, hi, hs⟩ := closed_all chk hv hg (fun i h x hx n' hn => (hC i h (hall i h) x hx).2 n' hn)
      (hD2 0 (Nat.zero_le _) _ .init) hm
    exact ⟨_, Array.getElem_mem hi, hs, fun x hx => (hC i hi (hall i hi) x hx).1⟩

/-- What the levels from `k` on cover: every node a run reaches within the covered levels, or at any depth where no
state was left, relates to a kept node whose transitions are all kept. -/
theorem levels_spec (chk : Smt.Checked P E T v) (hv : v.Equivariant) {depth cap : Nat} :
    (fuel k : Nat) → (st : SearchSt v) → (lo hi : Nat) → (sizes : Array Nat) → depth - k ≤ fuel →
    Good T sc st → hi = st.nodes.size → lo ≤ hi →
    (∀ i (h : i < st.nodes.size), i < lo → ∀ x ∈ inputsOf sc (st.nodes[i]).1,
      Recorded T st (st.nodes[i]).1 x ∧
        ∀ n', (move T (st.nodes[i]).1 x).next = some n' → st.seen.contains n'.key = true) →
    (∀ j < k, ∀ m, Reach T sc j m → ∃ i, ∃ h : i < st.nodes.size, i < lo ∧ Sim P m (st.nodes[i]).1) →
    (∀ j ≤ k, ∀ m, Reach T sc j m → ∃ i, ∃ h : i < st.nodes.size, Sim P m (st.nodes[i]).1) →
    ∀ j m, Reach T sc j m →
      (j < (levels T sc depth cap k st lo hi sizes).2.2.1 ∨ (levels T sc depth cap k st lo hi sizes).2.2.2.1 = true) →
      Good T sc (levels T sc depth cap k st lo hi sizes).1 ∧
      ∃ e ∈ (levels T sc depth cap k st lo hi sizes).1.nodes, Sim P m e.1 ∧
        ∀ x ∈ inputsOf sc e.1, Recorded T (levels T sc depth cap k st lo hi sizes).1 e.1 x := by
  intro fuel
  induction fuel with
  | zero =>
    intro k st lo hi sizes hf hg hhi hlo hC hD1 hD2 j m hm hcov
    have hk : ¬ k < depth := by omega
    unfold levels at hcov ⊢
    simp only [hk, ↓reduceIte] at hcov ⊢
    exact stop_case chk hv hg hhi hC hD1 hD2 hm hcov
  | succ fuel ih =>
    intro k st lo hi sizes hf hg hhi hlo hC hD1 hD2 j m hm hcov
    unfold levels at hcov ⊢
    by_cases hk : k < depth
    · simp only [hk, ↓reduceIte] at hcov ⊢
      by_cases he : lo = hi
      · simp only [he, ↓reduceIte] at hcov ⊢
        subst he
        exact stop_case chk hv hg hhi hC hD1 hD2 (lo := lo) hm (.inr (by simp))
      · simp only [he, ↓reduceIte] at hcov ⊢
        have hg0 := good_full hg false
        have hhi0 : hi ≤ ({ st with full := false } : SearchSt v).nodes.size := by simp [hhi]
        obtain ⟨g1, ⟨ge, gf⟩, gd⟩ := level_spec (cap := cap) (k := k) hg0 lo hi hhi0
        obtain ⟨st1, hst1⟩ : ∃ st1, level T sc cap k { st with full := false } lo hi = st1 := ⟨_, rfl⟩
        rw [hst1] at g1 ge gf gd hcov
        rw [hst1]
        have hext : Ext st st1 := (ext_full st false).trans ge
        have hnode : ∀ i (h : i < st.nodes.size), st1.nodes[i]'(Nat.lt_of_lt_of_le h hext.size) = st.nodes[i] :=
          hext.nodes
        have hdone : ∀ i (h : i < st.nodes.size), i < hi → ∀ x ∈ inputsOf sc (st.nodes[i]).1,
            Recorded T st1 (st.nodes[i]).1 x ∧ (∀ n', (move T (st.nodes[i]).1 x).next = some n' →
              st1.full = true ∨ st1.seen.contains n'.key = true) := by
          intro i hi' hih x hx
          by_cases hil : i < lo
          · obtain ⟨r1, r2⟩ := hC i hi' hil x hx
            exact ⟨r1.mono hext, fun n' hn => .inr (hext.seen _ (r2 n' hn))⟩
          · exact gd i hi' (by omega) hih x hx
        by_cases hfull : st1.full = true
        · simp only [hfull, ↓reduceIte] at hcov ⊢
          have hj : j ≤ k := by simp at hcov; omega
          obtain ⟨i, hi', hs⟩ := hD2 j hj m hm
          refine ⟨g1, st.nodes[i], ?_, hs, fun x hx => (hdone i hi' (by omega) x hx).1⟩
          rw [← hnode i hi']
          exact Array.getElem_mem _
        · simp only [hfull, Bool.false_eq_true, ↓reduceIte] at hcov ⊢
          have hC' : ∀ i (h : i < st1.nodes.size), i < hi → ∀ x ∈ inputsOf sc (st1.nodes[i]).1,
              Recorded T st1 (st1.nodes[i]).1 x ∧
                ∀ n', (move T (st1.nodes[i]).1 x).next = some n' → st1.seen.contains n'.key = true := by
            intro i hi1 hih x hx
            have hi' : i < st.nodes.size := by omega
            rw [hnode i hi'] at hx ⊢
            obtain ⟨d1, d2⟩ := hdone i hi' hih x hx
            exact ⟨d1, fun n' hn => (d2 n' hn).resolve_left hfull⟩
          refine ih (k + 1) st1 hi st1.nodes.size _ (by omega) g1 rfl (by have := hext.size; omega) hC' (fun j' hj' m' hm' => ?_)
            (fun j' hj' m' hm' => ?_) j m hm hcov
          · obtain ⟨i, hi', hs⟩ := hD2 j' (by omega) m' hm'
            exact ⟨i, Nat.lt_of_lt_of_le hi' hext.size, by omega, by rw [hnode i hi']; exact hs⟩
          · by_cases hj'' : j' ≤ k
            · obtain ⟨i, hi', hs⟩ := hD2 j' hj'' m' hm'
              exact ⟨i, Nat.lt_of_lt_of_le hi' hext.size, by rw [hnode i hi']; exact hs⟩
            · obtain rfl : j' = k + 1 := by omega
              cases hm' with
              | step hm0 hx hn =>
                obtain ⟨i, hi', hs⟩ := hD2 k (Nat.le_refl _) _ hm0
                have hi1 : i < st1.nodes.size := Nat.lt_of_lt_of_le hi' hext.size
                rw [← hnode i hi'] at hs
                exact sim_step chk hv g1 hi1 (fun x hx n' hn => (hC' i hi1 (by omega) x hx).2 n' hn) hs hx hn
    · simp only [hk, ↓reduceIte] at hcov ⊢
      exact stop_case chk hv hg hhi hC hD1 hD2 hm hcov
theorem good_init : Good T sc (SearchSt.init v) := by
  refine ⟨fun key h => ⟨0, by simp [SearchSt.init], ?_⟩, fun i h => ⟨0, ?_⟩, fun c h => ?_, fun f h => ?_⟩
  · simp only [SearchSt.init, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · simpa [SearchSt.init] using h
    · simp at h
  · have : i = 0 := by simp [SearchSt.init] at h; omega
    subst this
    exact .init
  · simp [SearchSt.init] at h
  · simp [SearchSt.init] at h

/-- explore covers what it reports: every transition of a run of the scope's inputs that faults nowhere before it, from
a node reached within `coverage.depth` transitions, or at any depth where `coverage.exhausted` (no state was left),
shows only classes of out line among `classes`, faults only by a fault among `faults`, and breaks only responses
among `responses`. -/
theorem explore_sound {P : List AnySite} {E : List AnyEffectSite} (chk : Smt.Checked P E T v) (hv : v.Equivariant)
    (sc : ScopeV) (depth cap : Nat) {j : Nat} {m : Node v} (hm : Reach T sc j m)
    (hcov : j < (search T v sc depth cap).coverage.depth ∨ (search T v sc depth cap).coverage.exhausted = true)
    {x : Input v} (hx : x ∈ inputsOf sc m) :
    (∀ c ∈ classes T v x (move T m x).result, ∃ h, (c, h) ∈ (search T v sc depth cap).classes) ∧
      (∀ f, (move T m x).result.outcome = .fault f → ∃ h, (f, h) ∈ (search T v sc depth cap).faults) ∧
      (∀ r ∈ (move T m x).broken, ∃ h, (r, h) ∈ (search T v sc depth cap).responses) := by
  have ho : Ordered T v := ⟨hv, fun m hm => (chk.keys m hm).2⟩
  have hl := levels_spec (P := P) chk hv (depth := depth) (cap := cap) depth 0 (SearchSt.init v) 0 1 #[1]
    (by omega) good_init rfl (by omega) (fun i _ h => absurd h (Nat.not_lt_zero _))
    (fun j h => absurd h (Nat.not_lt_zero _)) (fun j hj m hm => by
      obtain rfl : j = 0 := by omega
      cases hm
      exact ⟨0, by simp [SearchSt.init], .refl _⟩) j m hm
  unfold search at hcov ⊢
  revert hl hcov
  generalize levels T sc depth cap 0 (SearchSt.init v) 0 1 #[1] = r
  obtain ⟨st, sizes, covered, exhausted, capped⟩ := r
  intro hcov hl
  dsimp only at hcov hl ⊢
  obtain ⟨hg, e, -, hs, hrec⟩ := hl hcov
  obtain ⟨x', hx', e1, e2, e3, -⟩ := sim_move chk ho hs hx
  have hr := hrec x' hx'
  refine ⟨fun c hc => ?_, fun f hf => ?_, fun r hr' => ?_⟩
  · have hcon := hr.classes c (e1 ▸ hc)
    rw [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at hcon
    obtain ⟨h, hh⟩ := hcon
    refine ⟨h, List.mem_filterMap.2 ⟨c, Array.mem_toList_iff.2 (hg.classOrder c ?_), ?_⟩⟩
    · rw [Std.HashMap.contains_eq_isSome_getElem?, hh]; rfl
    · simp [Std.HashMap.get?_eq_getElem?, hh]
  · have hcon := hr.faults f ((e2 f).1 hf)
    rw [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at hcon
    obtain ⟨h, hh⟩ := hcon
    refine ⟨h, List.mem_filterMap.2 ⟨f, Array.mem_toList_iff.2 (hg.faultOrder f ?_), ?_⟩⟩
    · rw [Std.HashMap.contains_eq_isSome_getElem?, hh]; rfl
    · simp [Std.HashMap.get?_eq_getElem?, hh]
  · have hcon := hr.responses r (e3 ▸ hr')
    rw [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at hcon
    obtain ⟨h, hh⟩ := hcon
    exact ⟨h, (List.mergeSort_perm _ _).symm.subset (Std.HashMap.mem_toList_iff_getElem?_eq_some.2 hh)⟩

end Sim

end Tazuna.Explore
