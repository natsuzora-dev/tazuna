import Tazuna.Thm.Verify.Complete.Window

namespace Tazuna.Thm.Verify.Complete.Bindings

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Run Tazuna.Thm.Verify.Complete.Window

/-- Line `i` of `ls`, counted from 0, has id `x`. -/
def IdAt (ls : List (Option Line)) (i : Nat) (x : String) : Prop :=
  ∃ l, ls[i]? = some (some l) ∧ l.body.id = some x

/-- The ids of the lines of `ls` are distinct. -/
def IdsDistinct (ls : List (Option Line)) : Prop := (ls.filterMap fun l => l.bind (·.body.id)).Nodup

theorem IdAt.unique {ls : List (Option Line)} (h : IdsDistinct ls) :
    ∀ {i j : Nat} {x : String}, IdAt ls i x → IdAt ls j x → i = j := by
  induction ls with
  | nil => intro i j x ⟨l, hl, _⟩; simp at hl
  | cons a as ih =>
    intro i j x ⟨l, hl, hx⟩ ⟨l', hl', hx'⟩
    have hrest : IdsDistinct as := by
      unfold IdsDistinct at h ⊢
      cases a with
      | none => simpa using h
      | some a =>
        cases ha : a.body.id with
        | none => simpa [ha] using h
        | some y => simp only [List.filterMap_cons, Option.bind_some, ha] at h; exact (List.nodup_cons.mp h).2
    have mem : ∀ (k : Nat) (l : Line), as[k]? = some (some l) → l.body.id = some x →
        x ∈ as.filterMap fun l => l.bind (·.body.id) := by
      intro k l hk hxl
      exact List.mem_filterMap.mpr ⟨some l, List.mem_of_getElem? hk, by simpa using hxl⟩
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hl hl'
        subst hl
        unfold IdsDistinct at h
        simp only [List.filterMap_cons, Option.bind_some, hx] at h
        exact absurd (mem _ _ hl' hx') (List.nodup_cons.mp h).1
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hl hl'
        subst hl'
        unfold IdsDistinct at h
        simp only [List.filterMap_cons, Option.bind_some, hx'] at h
        exact absurd (mem _ _ hl hx) (List.nodup_cons.mp h).1
      | succ j =>
        simp only [List.getElem?_cons_succ] at hl hl'
        exact congrArg (· + 1) (ih hrest ⟨l, hl, hx⟩ ⟨l', hl', hx'⟩)

/-- An `out` command or query line. -/
def OutRequest (l : Line) : Prop := l.body.dir = .out ∧ l.isRequest = true

/-- An `out` subscribe line. -/
def OutSubscribe (l : Line) : Prop := l.body.dir = .out ∧ ∃ d i n v, l.body = .subscribe d i n v

/-- The id of an `out` subscribe line of `ls`. -/
def SubId (ls : List (Option Line)) (r : String) : Prop :=
  ∃ (i : Nat) (l : Line), ls[i]? = some (some l) ∧ OutSubscribe l ∧ l.body.id = some r

/-- The ids of the `out` command and query lines of `ls`. -/
def requestIds (ls : List (Option Line)) : List String :=
  ls.filterMap fun l => l.bind fun l => if l.body.dir == .out && l.isRequest then l.body.id else none

/--
The invariant of the ids, with the snapshot `S`, the implementation trace `L`, and bounds on the lines that bound ids
come from. Ids of subscriptions are left out of `inj`, as alike subscriptions answer for each other.
-/
structure IdsInv (S L : List (Option Line)) (bS bI : Nat) (ids : Ids) (sids : List (String × List String)) :
    Prop where
  keys : (ids.bound.map (·.1)).Nodup
  taken : ids.taken = ids.bound.map (·.2)
  snap : ∀ r q, (r, q) ∈ ids.bound → ∃ j < bS, IdAt S j r
  impl : ∀ r q, (r, q) ∈ ids.bound → ¬SubId S r → ∃ i < bI, IdAt L i q
  sub : ∀ r q, (r, q) ∈ ids.bound → SubId S r → ∃ qs, sids.lookup r = some qs ∧ q ∈ qs
  inj : ∀ r₁ r₂ q, (r₁, q) ∈ ids.bound → (r₂, q) ∈ ids.bound → ¬SubId S r₁ → ¬SubId S r₂ → r₁ = r₂
  groupKeys : ∀ r qs, (r, qs) ∈ ids.groups → ∃ j < bS, ∃ l, S[j]? = some (some l) ∧ OutRequest l ∧ l.body.id = some r
  groupValues : ∀ r qs, (r, qs) ∈ ids.groups → ∀ q ∈ qs,
    ∃ i < bI, ∃ l, L[i]? = some (some l) ∧ OutRequest l ∧ l.body.id = some q
  subKeys : ∀ r qs, (r, qs) ∈ sids → ∃ j < bS, ∃ l, S[j]? = some (some l) ∧ OutSubscribe l ∧ l.body.id = some r

theorem IdsInv.mono {S L : List (Option Line)} {bS bI bS' bI' : Nat} {ids : Ids} {sids : List (String × List String)}
    (h : IdsInv S L bS bI ids sids) (hS : bS ≤ bS') (hI : bI ≤ bI') : IdsInv S L bS' bI' ids sids :=
  ⟨h.keys, h.taken, fun r q hm => by obtain ⟨j, hj, hj'⟩ := h.snap r q hm; exact ⟨j, by omega, hj'⟩,
    fun r q hm hs => by obtain ⟨i, hi, hi'⟩ := h.impl r q hm hs; exact ⟨i, by omega, hi'⟩, h.sub, h.inj,
    fun r qs hm => by obtain ⟨j, hj, hj'⟩ := h.groupKeys r qs hm; exact ⟨j, by omega, hj'⟩,
    fun r qs hm q hq => by obtain ⟨i, hi, hi'⟩ := h.groupValues r qs hm q hq; exact ⟨i, by omega, hi'⟩,
    fun r qs hm => by obtain ⟨j, hj, hj'⟩ := h.subKeys r qs hm; exact ⟨j, by omega, hj'⟩⟩

theorem Ids.bind_none_left (ids : Ids) (t : Option String) : ids.bind none t = ids := rfl

theorem Ids.bind_none_right (ids : Ids) (s : Option String) : ids.bind s none = ids := by
  cases s <;> rfl

theorem Ids.bind_bound (ids : Ids) {s t : String} (h : (ids.bound.lookup s).isSome = true) :
    ids.bind (some s) (some t) = ids := by
  simp [Ids.bind, h]

theorem Ids.bind_new (ids : Ids) {s t : String} (h : ids.bound.lookup s = none) :
    ids.bind (some s) (some t) =
      { bound := ids.bound ++ [(s, t)], taken := ids.taken ++ [t], groups := ids.groups.filter (·.1 != s) } := by
  simp [Ids.bind, h]

/-- A bound id keeps its implementation id. -/
def BoundExt (ids ids' : Ids) : Prop := ∀ r q, ids.bound.lookup r = some q → ids'.bound.lookup r = some q

theorem BoundExt.refl (ids : Ids) : BoundExt ids ids := fun _ _ h => h

theorem BoundExt.trans {a b c : Ids} (h₁ : BoundExt a b) (h₂ : BoundExt b c) : BoundExt a c :=
  fun r q h => h₂ r q (h₁ r q h)

theorem lookup_append_of_some {β : Type} {m : List (String × β)} {r : String} {q : β} (n : List (String × β))
    (h : m.lookup r = some q) : (m ++ n).lookup r = some q := by
  induction m with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases e : r = a
    · subst e; simpa using h
    · have : (r == a) = false := by simpa using e
      simp only [List.lookup_cons, this] at h ⊢
      simp only [List.cons_append, List.lookup_cons, this]
      exact ih h

theorem BoundExt.bind (ids : Ids) (s t : Option String) : BoundExt ids (ids.bind s t) := by
  intro r q h
  unfold Ids.bind
  split
  · split
    · exact h
    · exact lookup_append_of_some _ h
  · exact h

theorem BoundExt.group (ids : Ids) (snapshot trace : List String) : BoundExt ids (ids.group snapshot trace) := by
  unfold Ids.group
  split
  · exact BoundExt.bind _ _ _
  · exact BoundExt.refl _

theorem BoundExt.groupedIds (pairs : List Pair) (ids : Ids) : BoundExt ids (groupedIds pairs ids) := by
  unfold Window.groupedIds
  exact foldl_preserve (fun ids' => BoundExt ids ids') _ _ _ (fun b _ _ h => h.trans (BoundExt.group _ _ _))
    (BoundExt.refl _)

/-- The invariant after binding snapshot id `r` to the fresh implementation id `q`. -/
theorem IdsInv.bind {S L : List (Option Line)} {bS bI : Nat} {ids : Ids} {sids : List (String × List String)}
    (h : IdsInv S L bS bI ids sids) (r q : String)
    (hsnap : ids.bound.lookup r = none → ∃ j < bS, IdAt S j r)
    (himpl : ids.bound.lookup r = none → ¬SubId S r → ∃ i < bI, IdAt L i q)
    (hsub : ids.bound.lookup r = none → SubId S r → ∃ qs, sids.lookup r = some qs ∧ q ∈ qs)
    (hfresh : ids.bound.lookup r = none → ¬SubId S r → ∀ r', (r', q) ∈ ids.bound → SubId S r') :
    IdsInv S L bS bI (ids.bind (some r) (some q)) sids := by
  cases hl : ids.bound.lookup r with
  | some _ => rw [Ids.bind_bound ids (by simp [hl])]; exact h
  | none =>
    rw [Ids.bind_new ids hl]
    have hr : r ∉ ids.bound.map (·.1) := lookup_none_iff.mp hl
    refine ⟨?_, by simp [h.taken], ?_, ?_, ?_, ?_, ?_, ?_, h.subKeys⟩
    · simp only [List.map_append, List.map_cons, List.map_nil]
      exact List.nodup_append.mpr ⟨h.keys, by simp, by simp only [List.mem_singleton]; rintro a ha b rfl rfl; exact hr ha⟩
    · intro r' q' hm
      rcases List.mem_append.mp hm with hm | hm
      · exact h.snap r' q' hm
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm; rw [hm.1]; exact hsnap hl
    · intro r' q' hm hs
      rcases List.mem_append.mp hm with hm | hm
      · exact h.impl r' q' hm hs
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm; obtain ⟨e1, e2⟩ := hm; subst e1 e2; exact himpl hl hs
    · intro r' q' hm hs
      rcases List.mem_append.mp hm with hm | hm
      · exact h.sub r' q' hm hs
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm; obtain ⟨e1, e2⟩ := hm; subst e1 e2; exact hsub hl hs
    · intro r₁ r₂ q' h₁ h₂ hs₁ hs₂
      rcases List.mem_append.mp h₁ with h₁ | h₁ <;> rcases List.mem_append.mp h₂ with h₂ | h₂
      · exact h.inj r₁ r₂ q' h₁ h₂ hs₁ hs₂
      · simp only [List.mem_singleton, Prod.mk.injEq] at h₂
        rw [h₂.1] at hs₂; rw [h₂.2] at h₁
        exact absurd (hfresh hl hs₂ r₁ h₁) hs₁
      · simp only [List.mem_singleton, Prod.mk.injEq] at h₁
        rw [h₁.1] at hs₁; rw [h₁.2] at h₂
        exact absurd (hfresh hl hs₁ r₂ h₂) hs₂
      · simp only [List.mem_singleton, Prod.mk.injEq] at h₁ h₂; rw [h₁.1, h₂.1]
    · intro r' qs hm
      simp only [List.mem_filter] at hm
      exact h.groupKeys r' qs hm.1
    · intro r' qs hm
      simp only [List.mem_filter] at hm
      exact h.groupValues r' qs hm.1

theorem flatMap_modify {α β : Type} (f : α → α) (g : α → List β) (l : List α) (i : Nat) (hi : i < l.length)
    (e : List β) (he : g (f l[i]) = g l[i] ++ e) : ((l.modify i f).flatMap g).Perm (l.flatMap g ++ e) := by
  have hl : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    have := List.take_append_drop i l
    rw [List.drop_eq_getElem_cons hi] at this
    exact this.symm
  rw [List.modify_eq_take_drop, List.drop_eq_getElem_cons hi, List.modifyHead_cons]
  calc ((l.take i ++ f l[i] :: l.drop (i + 1)).flatMap g)
      = (l.take i).flatMap g ++ (g l[i] ++ e) ++ (l.drop (i + 1)).flatMap g := by simp [he]
    List.Perm _ ((l.take i).flatMap g ++ g l[i] ++ (l.drop (i + 1)).flatMap g ++ e) := by
        simp only [List.append_assoc]
        exact List.Perm.append_left _ (List.Perm.append_left _ List.perm_append_comm)
    _ = l.flatMap g ++ e := by
        have hf := congrArg (List.flatMap g) hl
        simp only [List.flatMap_append, List.flatMap_cons] at hf
        rw [hf, List.append_assoc (List.flatMap g (List.take i l))]

/-- The snapshot and implementation ids of the pairs, where both lines have one. -/
def idPairs (pairs : List Pair) : List (String × String) :=
  pairs.filterMap fun p => match p.1.line.body.id, p.2.line.body.id with
    | some si, some ti => some (si, ti)
    | _, _ => none

theorem requestGroups_perm (pairs : List Pair) :
    ((requestGroups pairs).flatMap fun g => g.2.1.zip g.2.2).Perm (idPairs pairs) ∧
      ∀ g ∈ requestGroups pairs, g.2.1.length = g.2.2.length := by
  unfold requestGroups idPairs
  suffices ∀ (ps : List Pair) (gs : List (Line × List String × List String)),
      (∀ g ∈ gs, g.2.1.length = g.2.2.length) →
      ((ps.foldl (fun groups (x : Pair) =>
          match x.1.line.body.id, x.2.line.body.id with
          | some si, some ti =>
            match groups.findIdx? (fun (l, _, _) => alike l x.1.line) with
            | some i => groups.modify i fun (l, ss, ts) => (l, ss ++ [si], ts ++ [ti])
            | none => groups ++ [(x.1.line, [si], [ti])]
          | _, _ => groups) gs).flatMap fun g => g.2.1.zip g.2.2).Perm
        ((gs.flatMap fun g => g.2.1.zip g.2.2) ++ ps.filterMap fun p => match p.1.line.body.id, p.2.line.body.id with
          | some si, some ti => some (si, ti)
          | _, _ => none) ∧
      ∀ g ∈ ps.foldl (fun groups (x : Pair) =>
          match x.1.line.body.id, x.2.line.body.id with
          | some si, some ti =>
            match groups.findIdx? (fun (l, _, _) => alike l x.1.line) with
            | some i => groups.modify i fun (l, ss, ts) => (l, ss ++ [si], ts ++ [ti])
            | none => groups ++ [(x.1.line, [si], [ti])]
          | _, _ => groups) gs, g.2.1.length = g.2.2.length by
    have := this pairs [] (by simp)
    simp only [List.flatMap_nil, List.nil_append] at this
    exact this
  intro ps
  induction ps with
  | nil => intro gs h; simpa using h
  | cons p ps ih =>
    intro gs h
    simp only [List.foldl_cons]
    split
    · rename_i si ti hs ht
      split
      · rename_i i hi
        have hil : i < gs.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).1
        have h' : ∀ g ∈ gs.modify i (fun (l, ss, ts) => (l, ss ++ [si], ts ++ [ti])), g.2.1.length = g.2.2.length := by
          intro g hg
          rcases mem_modify _ gs i g hg with hg | ⟨y, hy, e⟩
          · exact h g hg
          · subst e; simp [h y hy]
        obtain ⟨h1, h2⟩ := ih _ h'
        refine ⟨h1.trans ?_, h2⟩
        simp only [List.filterMap_cons, hs, ht]
        refine List.Perm.append_right _ (flatMap_modify _ _ gs i hil [(si, ti)] ?_) |>.trans ?_
        · simp [List.zip_append (h _ (List.getElem_mem hil))]
        · simp
      · obtain ⟨h1, h2⟩ := ih (gs ++ [(p.1.line, [si], [ti])]) (by
          intro g hg
          rcases List.mem_append.mp hg with hg | hg
          · exact h g hg
          · simp at hg; subst hg; rfl)
        refine ⟨h1.trans ?_, h2⟩
        simp [hs, ht]
    · rename_i hn
      obtain ⟨h1, h2⟩ := ih gs h
      refine ⟨h1.trans ?_, h2⟩
      rcases h1 : p.1.line.body.id with _ | si <;> rcases h2 : p.2.line.body.id with _ | ti
      · simp [h1]
      · simp [h1]
      · simp [h1, h2]
      · exact absurd h2 (hn si ti h1)

theorem request_not_sub {S : List (Option Line)} (hS : IdsDistinct S) {j : Nat} {l : Line} {r : String}
    (hj : S[j]? = some (some l)) (hl : OutRequest l) (hr : l.body.id = some r) : ¬SubId S r := by
  rintro ⟨j', l', hj', hs, hr'⟩
  have := IdAt.unique hS ⟨l, hj, hr⟩ ⟨l', hj', hr'⟩
  subst this
  rw [hj] at hj'
  simp only [Option.some.injEq] at hj'
  subst hj'
  obtain ⟨_, d, i, n, v, hb⟩ := hs
  simp [OutRequest, Line.isRequest, hb] at hl

theorem mem_zip_fst {α β : Type} : ∀ {xs : List α} {ys : List β}, xs.length = ys.length → ∀ x ∈ xs, ∃ y, (x, y) ∈ xs.zip ys
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | _ :: _, [], h, _, _ => by simp at h
  | a :: xs, b :: ys, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, by simp⟩
    · obtain ⟨y, hy⟩ := mem_zip_fst (by simpa using h) x hx
      exact ⟨y, by simp [hy]⟩

theorem mem_zip_snd {α β : Type} : ∀ {xs : List α} {ys : List β}, xs.length = ys.length → ∀ y ∈ ys, ∃ x, (x, y) ∈ xs.zip ys
  | _, [], _, _, hy => absurd hy List.not_mem_nil
  | [], _ :: _, h, _, _ => by simp at h
  | a :: xs, b :: ys, h, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨a, by simp⟩
    · obtain ⟨x, hx⟩ := mem_zip_snd (by simpa using h) y hy
      exact ⟨x, by simp [hx]⟩

theorem map_snd_zip {α β : Type} : ∀ {xs : List α} {ys : List β}, xs.length = ys.length → (xs.zip ys).map (·.2) = ys
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | _ :: xs, _ :: ys, h => by simp [map_snd_zip (xs := xs) (ys := ys) (by simpa using h)]

theorem mem_idPairs {pairs : List Pair} {si ti : String} (h : (si, ti) ∈ idPairs pairs) :
    ∃ p ∈ pairs, p.1.line.body.id = some si ∧ p.2.line.body.id = some ti := by
  unfold idPairs at h
  obtain ⟨p, hp, e⟩ := List.mem_filterMap.mp h
  refine ⟨p, hp, ?_⟩
  split at e
  · rename_i a b ha hb; simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact ⟨ha, hb⟩
  · cases e

/-- The invariant after grouping the requests of a window, whose implementation lines are at `bI` or later. -/
theorem IdsInv.groupedIds {S L : List (Option Line)} {bS bI bI' : Nat} {ids : Ids}
    {sids : List (String × List String)} (hS : IdsDistinct S) (hL : IdsDistinct L) (h : IdsInv S L bS bI ids sids)
    (requests : List Pair) (hI : bI ≤ bI')
    (hreqS : ∀ p ∈ requests, ∃ j < bS, S[j]? = some (some p.1.line) ∧ OutRequest p.1.line)
    (hreqI : ∀ p ∈ requests, ∃ i, bI ≤ i ∧ i < bI' ∧ L[i]? = some (some p.2.line) ∧ OutRequest p.2.line)
    (hn : ((idPairs requests).map (·.2)).Nodup) : IdsInv S L bS bI' (groupedIds requests ids) sids := by
  obtain ⟨hperm, hlen⟩ := requestGroups_perm requests
  let gs := requestGroups requests
  have hts : (gs.flatMap (·.2.2)).Nodup := by
    have e : gs.flatMap (·.2.2) = (gs.flatMap fun g => g.2.1.zip g.2.2).map (·.2) := by
      rw [List.map_flatMap]
      have : ∀ (xs : List (Line × List String × List String)), (∀ g ∈ xs, g.2.1.length = g.2.2.length) →
          xs.flatMap (·.2.2) = xs.flatMap fun g => (g.2.1.zip g.2.2).map (·.2) := by
        intro xs hx
        induction xs with
        | nil => rfl
        | cons g xs ih =>
          simp only [List.flatMap_cons]
          rw [map_snd_zip (hx g List.mem_cons_self), ih (fun g' hg' => hx g' (List.mem_cons_of_mem _ hg'))]
      exact this gs hlen
    rw [e]
    exact (hperm.map _).nodup_iff.mpr hn
  have hpair : ∀ g ∈ gs, ∀ s ∈ g.2.1, ∃ p ∈ requests, p.1.line.body.id = some s := by
    intro g hg s hs
    obtain ⟨t, ht⟩ := mem_zip_fst (hlen g hg) s hs
    obtain ⟨p, hp, h1, _⟩ := mem_idPairs (hperm.subset (List.mem_flatMap.mpr ⟨g, hg, ht⟩))
    exact ⟨p, hp, h1⟩
  have hpair' : ∀ g ∈ gs, ∀ t ∈ g.2.2, ∃ p ∈ requests, p.2.line.body.id = some t := by
    intro g hg t ht
    obtain ⟨s, hs⟩ := mem_zip_snd (hlen g hg) t ht
    obtain ⟨p, hp, _, h2⟩ := mem_idPairs (hperm.subset (List.mem_flatMap.mpr ⟨g, hg, hs⟩))
    exact ⟨p, hp, h2⟩
  let F : List (Line × List String × List String) → Ids → Prop := fun done ids' =>
    IdsInv S L bS bI' ids' sids ∧ ∀ r q, (r, q) ∈ ids'.bound → ¬SubId S r →
      (∃ i < bI, IdAt L i q) ∨ q ∈ done.flatMap (·.2.2)
  suffices ∀ (rest done : List (Line × List String × List String)) (ids' : Ids), done ++ rest = gs → F done ids' →
      F gs (rest.foldl (fun ids (_, ss, ts) => ids.group ss ts) ids') from
    (this gs [] ids rfl ⟨h.mono (Nat.le_refl _) hI, fun r q hm hs => Or.inl (h.impl r q hm hs)⟩).1
  intro rest
  induction rest with
  | nil => intro done ids' e hF; simp only [List.append_nil] at e; subst e; exact hF
  | cons g rest ih =>
    intro done ids' e ⟨hF, hold⟩
    have hg : g ∈ gs := by rw [← e]; simp
    obtain ⟨l, ss, ts⟩ := g
    simp only [List.foldl_cons]
    apply ih (done ++ [(l, ss, ts)]) _ (by rw [← e]; simp)
    have hts' : ∀ t ∈ ts, t ∉ done.flatMap (·.2.2) := by
      intro t ht hd
      rw [← e, List.flatMap_append, List.flatMap_cons] at hts
      exact (List.nodup_append.mp hts).2.2 t hd t (List.mem_append_left _ ht) rfl
    have hpos : ∀ t ∈ ts, ∃ i, bI ≤ i ∧ i < bI' ∧ IdAt L i t ∧ ∃ l', L[i]? = some (some l') ∧ OutRequest l' ∧
        l'.body.id = some t := by
      intro t ht
      obtain ⟨p, hp, hid⟩ := hpair' _ hg t ht
      obtain ⟨i, hi1, hi2, hi3, hi4⟩ := hreqI p hp
      exact ⟨i, hi1, hi2, ⟨p.2.line, hi3, hid⟩, p.2.line, hi3, hi4, hid⟩
    have hkey : ∀ s ∈ ss, ∃ j < bS, ∃ l', S[j]? = some (some l') ∧ OutRequest l' ∧ l'.body.id = some s := by
      intro s hs
      obtain ⟨p, hp, hid⟩ := hpair _ hg s hs
      obtain ⟨j, hj1, hj2, hj3⟩ := hreqS p hp
      exact ⟨j, hj1, p.1.line, hj2, hj3, hid⟩
    unfold Ids.group
    split
    · rename_i s
      have hs := hkey s (by simp)
      obtain ⟨j, hj, l', hl', hreq, hid⟩ := hs
      have hns : ¬SubId S s := request_not_sub hS hl' hreq hid
      cases hth : ts.head? with
      | none =>
        rw [Ids.bind_none_right]
        exact ⟨hF, fun r q hm hsr => by
          rcases hold r q hm hsr with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by rw [List.flatMap_append]; exact List.mem_append_left _ h')⟩
      | some t =>
        have ht : t ∈ ts := List.mem_of_mem_head? hth
        obtain ⟨i, hi1, hi2, hiA, _⟩ := hpos t ht
        refine ⟨hF.bind s t (fun _ => ⟨j, hj, l', hl', hid⟩) (fun _ _ => ⟨i, hi2, hiA⟩)
          (fun _ h' => absurd h' hns) (fun _ _ r' hm => ?_), ?_⟩
        · refine Classical.byContradiction fun hr' => ?_
          rcases hold r' t hm hr' with ⟨i', hi', hA'⟩ | h'
          · have := IdAt.unique hL hA' hiA; omega
          · exact hts' t ht h'
        · intro r q hm hsr
          have old : (r, q) ∈ ids'.bound → (∃ i < bI, IdAt L i q) ∨ q ∈ (done ++ [(l, [s], ts)]).flatMap (·.2.2) :=
            fun hm => by
              rcases hold r q hm hsr with h' | h'
              · exact Or.inl h'
              · exact Or.inr (by rw [List.flatMap_append]; exact List.mem_append_left _ h')
          cases hl : ids'.bound.lookup s with
          | some _ => rw [Ids.bind_bound _ (by simp [hl])] at hm; exact old hm
          | none =>
            rw [Ids.bind_new _ hl] at hm
            rcases List.mem_append.mp hm with hm | hm
            · exact old hm
            · simp only [List.mem_singleton, Prod.mk.injEq] at hm
              right; rw [hm.2]; simp [ht]
    · refine ⟨⟨hF.keys, hF.taken, hF.snap, hF.impl, hF.sub, hF.inj, ?_, ?_, hF.subKeys⟩, ?_⟩
      · intro r qs hm
        simp only at hm
        revert hm
        apply foldl_preserve (fun g => (r, qs) ∈ g →
          ∃ j < bS, ∃ l, S[j]? = some (some l) ∧ OutRequest l ∧ l.body.id = some r)
        · intro g id hid hg hm
          rcases mem_setAt_any hm with ⟨e1, _⟩ | hm
          · subst e1; exact hkey r hid
          · exact hg hm
        · exact hF.groupKeys r qs
      · intro r qs hm
        simp only at hm
        revert hm
        apply foldl_preserve (fun g => (r, qs) ∈ g → ∀ q ∈ qs,
          ∃ i < bI', ∃ l, L[i]? = some (some l) ∧ OutRequest l ∧ l.body.id = some q)
        · intro g id _ hg hm q hq
          rcases mem_setAt_any hm with ⟨_, e2⟩ | hm
          · subst e2
            obtain ⟨i, _, hi2, _, l', hl', hr, hid⟩ := hpos q hq
            exact ⟨i, hi2, l', hl', hr, hid⟩
          · exact hg hm q hq
        · exact hF.groupValues r qs
      · intro r q hm hsr
        rcases hold r q hm hsr with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [List.flatMap_append]; exact List.mem_append_left _ h')

end Tazuna.Thm.Verify.Complete.Bindings
