import Tazuna.Thm.Verify.Complete.Bindings

namespace Tazuna.Thm.Verify.Complete.Inputs

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Run Tazuna.Thm.Verify.Complete.Window Tazuna.Thm.Verify.Complete.Bindings

/-- What a placed `in` line tells: the ids that the line names, with the request or subscription it answers. -/
def InPlaced (st : St) (s t : Line) : Prop :=
  match s.body with
  | .time .. | .restart .. => True
  | .unsubscribe _ _ to => st.ids.matches (some to) t.body.to? = true
  | .answer _ _ to _ => ∃ to', t.body.to? = some to' ∧
    ((∃ qs, st.subscriptionIds.lookup to = some qs ∧ to' ∈ qs) ∨ st.ids.matches (some to) (some to') = true)
  | _ => st.ids.matches s.body.resultOf? t.body.resultOf? = true

/-- Whether the `in` line compares values. -/
def ComparesValue (s : Line) : Prop :=
  match s.body with
  | .time .. | .restart .. | .unsubscribe .. => False
  | _ => True

theorem sameInput_true (st : St) (s t : Line) (h : (sameInput st s t).1 = true) :
    t.body.type = s.body.type ∧ t.body.name? = s.body.name? ∧ sameTime s t = true ∧
      (sameInput st s t).2 = { st with values := (sameInput st s t).2.values } ∧ InPlaced st s t ∧
      (ComparesValue s →
        equalContent st.declared s.content t.content st.values true = (true, (sameInput st s t).2.values)) ∧
      (¬ComparesValue s → (sameInput st s t).2.values = st.values) := by
  unfold sameInput at h ⊢
  by_cases hc : (s.body.type != t.body.type || s.body.name? != t.body.name? || !sameTime s t) = true
  · simp only [hc, ite_true] at h; cases h
  · simp only [hc, Bool.false_eq_true, ite_false] at h ⊢
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or, Decidable.not_not,
      Bool.not_eq_false] at hc
    obtain ⟨⟨htype, hname⟩, htime⟩ := hc
    refine ⟨htype.symm, hname.symm, htime, ?_⟩
    have ec : ∀ (b : Bool) (p : Bool × Bindings), (if b = true then (false, st) else (p.1, { st with values := p.2 })).1
        = true → b = false ∧ p.1 = true := by
      intro b p hb; cases b <;> simp_all
    cases hsb : s.body with
    | time d i => simp [hsb, InPlaced, ComparesValue]
    | restart d i => simp [hsb, InPlaced, ComparesValue]
    | unsubscribe d i to =>
      simp only [hsb] at h ⊢
      exact ⟨trivial, by simpa [InPlaced, hsb] using h, by simp [ComparesValue, hsb], fun _ => trivial⟩
    | answer d i to a =>
      cases htb : t.body with
      | answer d' i' to' a' =>
        simp only [hsb, htb] at h ⊢
        obtain ⟨hp, he⟩ := ec _ _ h
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at hp
        simp only [hp, Bool.not_true, Bool.false_eq_true, ite_false]
        refine ⟨trivial, ?_, fun _ => Prod.ext he rfl, fun hn => absurd (by simp [ComparesValue, hsb]) hn⟩
        simp only [InPlaced, hsb, htb, TraceLine.Body.to?, Option.some.injEq, exists_eq_left']
        split at hp
        · rename_i qs hl; exact Or.inl ⟨qs, hl, by simpa using hp⟩
        · exact Or.inr hp
      | _ => rw [hsb, htb] at htype; simp [TraceLine.Body.type] at htype
    | command d i n v | query d i n v | subscribe d i n v | event d i n v r | operation d i n v
    | unacceptedOperation d i n v =>
      simp only [hsb] at h ⊢
      obtain ⟨hp, he⟩ := ec _ _ h
      simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at hp
      simp only [hp, Bool.not_true, Bool.false_eq_true, ite_false]
      refine ⟨trivial, by simpa [InPlaced, hsb] using hp, fun _ => Prod.ext he rfl,
        fun hn => absurd (by simp [ComparesValue, hsb]) hn⟩

theorem matches_some (ids : Ids) (r q : String) (h : ids.matches (some r) (some q) = true) :
    ids.bound.lookup r = some q ∨
      (ids.bound.lookup r = none ∧ ∃ qs, ids.groups.lookup r = some qs ∧ q ∈ qs ∧ q ∉ ids.taken) := by
  simp only [Ids.matches] at h
  split at h
  · rename_i b hb; left; simp only [beq_iff_eq] at h; rw [hb, h]
  · rename_i hb
    right
    refine ⟨hb, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨hg, ht⟩ := h
    cases hgl : ids.groups.lookup r with
    | none => simp [hgl] at hg
    | some qs =>
      simp only [hgl, Option.map_some, Option.getD_some, List.contains_iff_mem] at hg
      exact ⟨qs, rfl, hg, by simpa using ht⟩

theorem lookup_append_none {β : Type} {m : List (String × β)} {r : String} (n : List (String × β))
    (h : m.lookup r = none) : (m ++ n).lookup r = n.lookup r := by
  induction m with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases e : r = a
    · subst e; simp at h
    · have : (r == a) = false := by simpa using e
      simp only [List.lookup_cons, this] at h
      simp only [List.cons_append, List.lookup_cons, this]
      exact ih h

theorem matches_shape (ids : Ids) (a b : Option String) (h : ids.matches a b = true) :
    (a = none ∧ b = none) ∨ ∃ r q, a = some r ∧ b = some q := by
  cases a <;> cases b <;> simp_all [Ids.matches]

/-- What the ids tell about a name: the bound implementation id of an id that names no subscription, or a
subscription paired with an alike one. -/
def PlacedAt (S : List (Option Line)) (ids : Ids) (sids : List (String × List String)) :
    Option String → Option String → Prop
  | some r, some q => (¬SubId S r ∧ ids.bound.lookup r = some q) ∨ ∃ qs, sids.lookup r = some qs ∧ q ∈ qs
  | none, none => True
  | _, _ => False

theorem PlacedAt.ext {S : List (Option Line)} {ids ids' : Ids} {sids : List (String × List String)}
    {a b : Option String} (h : PlacedAt S ids sids a b) (he : BoundExt ids ids') : PlacedAt S ids' sids a b := by
  cases a <;> cases b <;> simp only [PlacedAt] at h ⊢
  rcases h with ⟨h1, h2⟩ | h
  · exact Or.inl ⟨h1, he _ _ h2⟩
  · exact Or.inr h

theorem placedAt_of_lookup {S L : List (Option Line)} {bS bI : Nat} {ids : Ids} {sids : List (String × List String)}
    (h : IdsInv S L bS bI ids sids) {r q : String} (hl : ids.bound.lookup r = some q) :
    PlacedAt S ids sids (some r) (some q) := by
  by_cases hs : SubId S r
  · exact Or.inr (h.sub r q (mem_of_lookup hl) hs)
  · exact Or.inl ⟨hs, hl⟩

theorem _root_.Tazuna.Thm.Verify.Complete.Bindings.IdsInv.bind_matched {S L : List (Option Line)} {bS bI : Nat} {ids : Ids} {sids : List (String × List String)}
    (hS : IdsDistinct S) (h : IdsInv S L bS bI ids sids) (r q : String) (hm : ids.matches (some r) (some q) = true) :
    IdsInv S L bS bI (ids.bind (some r) (some q)) sids ∧ (ids.bind (some r) (some q)).bound.lookup r = some q := by
  rcases matches_some ids r q hm with hb | ⟨hn, qs, hg, hq, ht⟩
  · rw [Ids.bind_bound ids (by simp [hb])]; exact ⟨h, hb⟩
  · have hgm := mem_of_lookup hg
    obtain ⟨j, hj, l, hl, hreq, hid⟩ := h.groupKeys r qs hgm
    obtain ⟨i, hi, l', hl', _, hid'⟩ := h.groupValues r qs hgm q hq
    refine ⟨h.bind r q (fun _ => ⟨j, hj, l, hl, hid⟩) (fun _ _ => ⟨i, hi, l', hl', hid'⟩)
      (fun _ hs => absurd hs (request_not_sub hS hl hreq hid)) (fun _ _ r' hm' => ?_), ?_⟩
    · exact absurd (by rw [h.taken]; exact List.mem_map_of_mem (f := (·.2)) hm') ht
    · rw [Ids.bind_new ids hn]; simp [lookup_append_none _ hn]

theorem _root_.Tazuna.Thm.Verify.Complete.Bindings.IdsInv.bind_sub {S L : List (Option Line)} {bS bI : Nat} {ids : Ids} {sids : List (String × List String)}
    (h : IdsInv S L bS bI ids sids) (r q : String) {qs : List String} (hl : sids.lookup r = some qs) (hq : q ∈ qs) :
    IdsInv S L bS bI (ids.bind (some r) (some q)) sids := by
  obtain ⟨j, hj, l, hl', hsub, hid⟩ := h.subKeys r qs (mem_of_lookup hl)
  exact h.bind r q (fun _ => ⟨j, hj, l, hl', hid⟩) (fun _ hs => absurd ⟨j, l, hl', hsub, hid⟩ hs)
    (fun _ _ => ⟨qs, hl, hq⟩) (fun _ hs => absurd ⟨j, l, hl', hsub, hid⟩ hs)

theorem _root_.Tazuna.Thm.Verify.Complete.Bindings.IdsInv.bind_input {S L : List (Option Line)} {pS pI : Nat} {ids : Ids} {sids : List (String × List String)}
    (hS : IdsDistinct S) (hL : IdsDistinct L) (h : IdsInv S L pS pI ids sids) {s t : Line} (i j : String)
    (hs : S[pS]? = some (some s)) (hsd : s.body.dir ≠ .out) (hi : s.body.id = some i)
    (ht : L[pI]? = some (some t)) (hj : t.body.id = some j) :
    ids.bound.lookup i = none ∧ IdsInv S L (pS + 1) (pI + 1) (ids.bind (some i) (some j)) sids := by
  have hnone : ids.bound.lookup i = none := by
    cases hl : ids.bound.lookup i with
    | none => rfl
    | some q =>
      obtain ⟨j', hj', hA⟩ := h.snap i q (mem_of_lookup hl)
      have := IdAt.unique hS hA ⟨s, hs, hi⟩
      omega
  refine ⟨hnone, (h.mono (Nat.le_succ _) (Nat.le_succ _)).bind i j (fun _ => ⟨pS, by omega, s, hs, hi⟩)
    (fun _ _ => ⟨pI, by omega, t, ht, hj⟩) (fun _ hsub => ?_) (fun _ _ r' hm => ?_)⟩
  · obtain ⟨j', l, hl, ⟨hd, _⟩, hid⟩ := hsub
    have := IdAt.unique hS ⟨l, hl, hid⟩ ⟨s, hs, hi⟩
    subst this
    rw [hs] at hl
    simp only [Option.some.injEq] at hl
    subst hl
    exact absurd hd hsd
  · refine Classical.byContradiction fun hr' => ?_
    obtain ⟨i', hi', hA⟩ := h.impl r' j hm hr'
    have := IdAt.unique hL hA ⟨t, ht, hj⟩
    omega

/-- What a placed `in` line gives after its ids are bound. -/
def InFacts (S : List (Option Line)) (ids : Ids) (sids : List (String × List String)) (s t : Line) : Prop :=
  (∀ i j, s.body.id = some i → t.body.id = some j → ids.bound.lookup i = some j) ∧
    match s.body with
    | .time .. | .restart .. => True
    | .unsubscribe _ _ to | .answer _ _ to _ => PlacedAt S ids sids (some to) t.body.to?
    | _ => PlacedAt S ids sids s.body.resultOf? t.body.resultOf?

/-- The ids after an `in` line, as compareInputs binds them. -/
def inputIds (ids : Ids) (s t : Line) : Ids :=
  ((ids.bind s.body.to? t.body.to?).bind s.body.resultOf? t.body.resultOf?).bind s.body.id t.body.id

theorem inputIds_spec {S L : List (Option Line)} {pS pI : Nat} (st : St) (hS : IdsDistinct S) (hL : IdsDistinct L)
    (h : IdsInv S L pS pI st.ids st.subscriptionIds) {s t : Line} (hs : S[pS]? = some (some s))
    (hsd : s.body.dir ≠ .out) (ht : L[pI]? = some (some t)) (hp : InPlaced st s t) :
    IdsInv S L (pS + 1) (pI + 1) (inputIds st.ids s t) st.subscriptionIds ∧ BoundExt st.ids (inputIds st.ids s t) ∧
      InFacts S (inputIds st.ids s t) st.subscriptionIds s t := by
  have first : ∃ ids₂ : Ids, (st.ids.bind s.body.to? t.body.to?).bind s.body.resultOf? t.body.resultOf? = ids₂ ∧
      IdsInv S L pS pI ids₂ st.subscriptionIds ∧ BoundExt st.ids ids₂ ∧
      (match s.body with
        | .time .. | .restart .. => True
        | .unsubscribe _ _ to | .answer _ _ to _ => PlacedAt S ids₂ st.subscriptionIds (some to) t.body.to?
        | _ => PlacedAt S ids₂ st.subscriptionIds s.body.resultOf? t.body.resultOf?) := by
    unfold InPlaced at hp
    cases hsb : s.body with
    | time d i | restart d i =>
      refine ⟨_, rfl, ?_, ?_, trivial⟩ <;> simp only [TraceLine.Body.to?, TraceLine.Body.resultOf?,
        Ids.bind_none_left] <;> first | exact h | exact BoundExt.refl _
    | unsubscribe d i to =>
      rw [hsb] at hp
      simp only at hp
      obtain ⟨to', hto⟩ : ∃ to', t.body.to? = some to' := by
        cases h' : t.body.to? with
        | none => rw [h'] at hp; simp [Ids.matches] at hp
        | some x => exact ⟨x, rfl⟩
      rw [hto] at hp
      obtain ⟨hi, hl⟩ := h.bind_matched hS to to' hp
      rw [hto]
      refine ⟨_, rfl, ?_, ?_, ?_⟩ <;>
        simp only [TraceLine.Body.to?, TraceLine.Body.resultOf?, Ids.bind_none_left]
      · exact hi
      · exact BoundExt.bind _ _ _
      · exact placedAt_of_lookup hi hl
    | answer d i to a =>
      rw [hsb] at hp
      simp only at hp
      obtain ⟨to', hto, hpl⟩ := hp
      rw [hto]
      rcases hpl with ⟨qs, hl, hq⟩ | hm
      · refine ⟨_, rfl, ?_, ?_, ?_⟩ <;>
          simp only [TraceLine.Body.to?, TraceLine.Body.resultOf?, Ids.bind_none_left]
        · exact h.bind_sub to to' hl hq
        · exact BoundExt.bind _ _ _
        · exact Or.inr ⟨qs, hl, hq⟩
      · obtain ⟨hi, hl⟩ := h.bind_matched hS to to' hm
        refine ⟨_, rfl, ?_, ?_, ?_⟩ <;>
          simp only [TraceLine.Body.to?, TraceLine.Body.resultOf?, Ids.bind_none_left]
        · exact hi
        · exact BoundExt.bind _ _ _
        · exact placedAt_of_lookup hi hl
    | command d i n v | query d i n v | subscribe d i n v | event d i n v r | operation d i n v
    | unacceptedOperation d i n v =>
      rw [hsb] at hp
      simp only at hp
      simp only [TraceLine.Body.to?, Ids.bind_none_left]
      rcases matches_shape _ _ _ hp with ⟨ha, hb⟩ | ⟨r', q', ha, hb⟩
      · rw [ha, hb, Ids.bind_none_left]
        exact ⟨_, rfl, h, BoundExt.refl _, trivial⟩
      · rw [ha, hb] at hp
        rw [ha, hb]
        obtain ⟨hi, hl⟩ := h.bind_matched hS r' q' hp
        exact ⟨_, rfl, hi, BoundExt.bind _ _ _, placedAt_of_lookup hi hl⟩
  obtain ⟨ids₂, e, hi₂, hx₂, hp₂⟩ := first
  unfold inputIds
  rw [e]
  have hfinal : IdsInv S L (pS + 1) (pI + 1) (ids₂.bind s.body.id t.body.id) st.subscriptionIds ∧
      BoundExt ids₂ (ids₂.bind s.body.id t.body.id) ∧
      (∀ i j, s.body.id = some i → t.body.id = some j → (ids₂.bind s.body.id t.body.id).bound.lookup i = some j) := by
    cases hi : s.body.id with
    | none =>
      rw [Ids.bind_none_left]
      exact ⟨hi₂.mono (Nat.le_succ _) (Nat.le_succ _), BoundExt.refl _, by simp⟩
    | some i =>
      cases hj : t.body.id with
      | none =>
        rw [Ids.bind_none_right]
        exact ⟨hi₂.mono (Nat.le_succ _) (Nat.le_succ _), BoundExt.refl _, by simp⟩
      | some j =>
        obtain ⟨hn, hinv⟩ := hi₂.bind_input hS hL i j hs hsd hi ht hj
        refine ⟨hinv, BoundExt.bind _ _ _, fun i' j' e1 e2 => ?_⟩
        simp only [Option.some.injEq] at e1 e2
        subst e1 e2
        rw [Ids.bind_new _ hn]
        simp [lookup_append_none _ hn]
  obtain ⟨f1, f2, f3⟩ := hfinal
  refine ⟨f1, hx₂.trans f2, f3, ?_⟩
  revert hp₂
  split <;> intro hp₂
  · trivial
  · trivial
  · exact hp₂.ext f2
  · exact hp₂.ext f2
  · exact hp₂.ext f2

end Tazuna.Thm.Verify.Complete.Inputs
