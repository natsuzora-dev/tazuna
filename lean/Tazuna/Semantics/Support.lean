import Tazuna.Semantics.StepRename

/-! What a step in progress holds names only below its counter. A renaming that leaves the counters below `n` as they
are (`PBij.Fixes`) relates such a value to itself; for stored data it is enough that the value relates to anything
under the renaming that keeps exactly those counters (`PBij.below`), since that renaming moves no name (the support of
nominal techniques, Pitts 2013). -/

namespace Tazuna.Ir

/-- `P` keeps every counter below `n`. -/
def PBij.Fixes (P : PBij) (n : Nat) : Prop := ∀ c < n, P.rel c c

/-- Each counter below `n` to itself, and nothing else. -/
def PBij.below (n : Nat) : PBij where
  rel a b := a = b ∧ a < n
  func := by rintro _ _ _ ⟨rfl, _⟩ ⟨rfl, _⟩; rfl
  inj := by rintro _ _ _ ⟨rfl, _⟩ ⟨rfl, _⟩; rfl

theorem PBij.below_fixes (n : Nat) : (PBij.below n).Fixes n := fun _ h => ⟨rfl, h⟩

theorem PBij.Fixes.mono {P : PBij} {n m : Nat} (h : P.Fixes m) (hnm : n ≤ m) : P.Fixes n :=
  fun c hc => h c (Nat.lt_of_lt_of_le hc hnm)

/-- `x` holds names only below `n`: every renaming that keeps the counters below `n` relates it to itself, as `self`
reads that for its kind of value. -/
def Below {α : Type} (self : PBij → α → Prop) (n : Nat) (x : α) : Prop := ∀ P : PBij, P.Fixes n → self P x

theorem Below.mono {α : Type} {self : PBij → α → Prop} {n m : Nat} {x : α} (h : Below self n x) (hnm : n ≤ m) :
    Below self m x :=
  fun P hP => h P (hP.mono hnm)

section Self
variable {n : Nat} {P : PBij}

theorem IdV.self_of_below {a b : IdV} (h : IdV.Rel (PBij.below n) a b) (hP : P.Fixes n) : IdV.Rel P a a := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨c, c', i, ⟨rfl, hc⟩, rfl, rfl⟩
  · exact .inl ⟨s, rfl, rfl⟩
  · exact .inr ⟨c, c, i, hP c hc, rfl, rfl⟩

theorem Multi.self_of {α β : Type} {r : α → β → Prop} {s : α → α → Prop} (h : ∀ a b, r a b → s a a)
    {xs : List α} {ys : List β} : Multi r xs ys → Multi s xs xs
  | ⟨_, hz, _⟩ => Multi.of_forall2 (forall2_self_of h hz)

mutual
/-- Stored data that relates to anything under the renaming keeping the counters below `n` relates to itself under
every renaming that keeps them. -/
theorem Ty.self_of_below (hP : P.Fixes n) : (t : Ty) → t.comparable = true → {x y : t.den0} →
    Ty.rel0 (PBij.below n) t x y → Ty.rel0 P t x x
  | .int, _, _, _, _ | .str, _, _, _, _ | .date, _, _, _, _ => rfl
  | .param _, _, _, _, _ => trivial
  | .list t, hw, _, _, h => forall2_self_of (fun _ _ => Ty.self_of_below hP t hw) h
  | .bag t, hw, _, _, h => Multi.self_of (fun _ _ => Ty.self_of_below hP t hw) h
  | .table k v, hw, _, _, h => by
    simp only [Ty.comparable, Bool.and_eq_true] at hw
    exact Multi.self_of (fun _ _ hab => ⟨Ty.self_of_below hP k hw.1 hab.1, Ty.self_of_below hP v hw.2 hab.2⟩) h
  | .tuple ts, hw, _, _, h => Ty.selfs_of_below hP ts hw h
  | .adt _ _ vs, hw, _, _, h => Ty.selfAlts_of_below hP vs hw h
  | .id, _, _, _, h => IdV.self_of_below h hP
  | .dsl k _, hw, _, _, h => by
    simp only [Ty.comparable, beq_iff_eq] at hw
    subst hw
    obtain ⟨rfl, hc⟩ := h
    exact hP _ hc
  | .fn .., hw, _, _, _ => by simp [Ty.comparable] at hw
theorem Ty.selfs_of_below (hP : P.Fixes n) : (ts : List Ty) → Ty.comparables ts = true →
    {x y : (Ty.semsWith Dsl.base ts).1} →
    Ty.relsWith Dsl.base (Dsl.rel0 (PBij.below n)) (PBij.below n) ts x y → Ty.relsWith Dsl.base (Dsl.rel0 P) P ts x x
  | [], _, _, _, _ => trivial
  | t :: ts, hw, _, _, ⟨h, hs⟩ => by
    simp only [Ty.comparables, Bool.and_eq_true] at hw
    exact ⟨Ty.self_of_below hP t hw.1 h, Ty.selfs_of_below hP ts hw.2 hs⟩
theorem Ty.selfAlts_of_below (hP : P.Fixes n) : (vs : List (List Ty)) → Ty.comparabless vs = true →
    {x y : (Ty.semAltsWith Dsl.base vs).1} →
    Ty.relAltsWith Dsl.base (Dsl.rel0 (PBij.below n)) (PBij.below n) vs x y →
    Ty.relAltsWith Dsl.base (Dsl.rel0 P) P vs x x
  | [], _, x, _, _ => nomatch x
  | fs :: _, hw, .inl _, .inl _, h => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hw
    exact Ty.selfs_of_below hP fs hw.1 h
  | _ :: vs, hw, .inr _, .inr _, h => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hw
    exact Ty.selfAlts_of_below hP vs hw.2 h
  | _ :: _, _, .inl _, .inr _, h | _ :: _, _, .inr _, .inl _, h => h.elim
end

end Self

namespace Step

variable {v : ServiceV} (T : List TypeDecl)

/-- The step in progress related to itself by `P` with every wire id kept, and each pending request and each waiting
own effect related to itself on its own: the multiset relation does not give an item's relation back, since two items
may relate to each other and not to themselves. -/
def Acc.Self (P : PBij) (a : Acc v) : Prop :=
  Acc.Rel ⟨P, PBij.refl⟩ a a ∧ (∀ p ∈ a.state.pending, Pending.Rel ⟨P, PBij.refl⟩ p p) ∧
    ∀ x ∈ a.own, OwnEffectV.Rel P x x

/-- Starting effects that each relate to themselves keeps a step in progress related to itself with every wire id
kept: each request it writes relates to itself at its own id. -/
theorem start_self {P : PBij} {a : Acc v} (ha : Acc.Self P a) {effs : List (Sender × EffectV v.event)}
    (he : ∀ x ∈ effs, Started.Rel P x x) {b : Acc v} (h : start a effs = .ok b) : Acc.Self P b := by
  have hd : ¬ ∃ x ∈ reqsOf effs, Undeclared v.declared x := fun ⟨x, hx, hu⟩ => by
    have := start_undeclared effs ⟨x, (List.mem_filter.1 hx).1, hu⟩ a
    rw [h] at this; exact this
  obtain ⟨ps, hps⟩ := writes_of_declared v.declared (reqsOf effs) a.state.nextId
    fun x hx => ⟨by simpa using (List.mem_filter.1 hx).2, fun hu => hd ⟨x, hx, hu⟩⟩
  rw [start_requests a effs ps hps] at h
  cases h
  have hnew : ∀ p ∈ ps, Pending.Rel ⟨P, PBij.refl⟩ p p ∧ p.id < a.state.nextId + (reqsOf effs).length := by
    intro p hp
    obtain ⟨x, hx, r, o, hr, -, rfl⟩ := forall2_mem_right hps p hp
    obtain ⟨hs, hrr⟩ := he x.1 (List.mem_filter.1 (List.fst_mem_of_mem_zipIdx hx)).1
    rw [hr] at hrr
    cases hrr with
    | request hrr => exact ⟨⟨rfl, hs, rfl, hrr⟩, (List.mem_zipIdx hx).2.1⟩
  obtain ⟨⟨⟨hrec, hmach, hpend, hnow, hb, -⟩, hev, hout, ho, -, hown⟩, hpi, hoi⟩ := ha
  have hqi : ∀ x ∈ queuedOf effs, OwnEffectV.Rel P x x := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := List.mem_filterMap.1 hx
    exact OwnEffectV.rel_iff.2 (EffectV.own?_eq_some hyx ▸ (he y hy).2)
  have hpb : ∀ p ∈ a.state.pending ++ ps, p.id < a.state.nextId + (reqsOf effs).length := fun p hp =>
    (List.mem_append.1 hp).elim (fun h => Nat.lt_of_lt_of_le (hb p h) (Nat.le_add_right _ _)) fun h => (hnew p h).2
  have hob : ∀ o ∈ a.out ++ ps.map Pending.line, o.id < a.state.nextId + (reqsOf effs).length := fun o hp =>
    (List.mem_append.1 hp).elim (fun h => Nat.lt_of_lt_of_le (ho o h) (Nat.le_add_right _ _)) fun h => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.1 h; exact (hnew p hp').2
  refine ⟨⟨⟨hrec, hmach, hpend.append (Multi.of_forall2 (forall2_refl_of fun p hp => (hnew p hp).1)), hnow, hpb, hpb⟩,
    hev, hout.append (Multi.of_forall2 (forall2_refl_of fun o ho => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho; exact Pending.rel_line (hnew p hp).1)), hob, hob,
    hown.append (Multi.of_forall2 (forall2_refl_of hqi))⟩, fun p hp => ?_, fun x hx => ?_⟩
  · exact (List.mem_append.1 hp).elim (hpi p) fun h => (hnew p h).1
  · exact (List.mem_append.1 hx).elim (hoi x) (hqi x)

theorem mem_foldl_dedup {α : Type} (eq : α → α → Bool) (x : α) : (xs acc : List α) →
    x ∈ xs.foldl (fun ks k => if ks.any (eq k) then ks else ks ++ [k]) acc → x ∈ acc ∨ x ∈ xs
  | [], _, h => .inl h
  | k :: xs, acc, h => by
    simp only [List.foldl_cons] at h
    rcases mem_foldl_dedup eq x xs _ h with h | h
    · split at h
      · exact .inl h
      · rcases List.mem_append.1 h with h | h
        · exact .inl h
        · rw [List.mem_singleton] at h; exact .inr (h ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h)

theorem mem_of_mem_dedupBy {α : Type} (eq : α → α → Bool) (xs : List α) {x : α} (h : x ∈ dedupBy eq xs) : x ∈ xs := by
  simpa using mem_foldl_dedup eq x xs [] h

section Machine
variable {r e : Ty} {n : Nat}

/-- Every effect a machine starts on an event relates to itself under each renaming that keeps the counters below `n`,
when the records, the event and the instances do. -/
theorem machineStep_self {m : MachineV r e} (hm : m.Equi) {records : r.den0}
    (hrec : ∀ P : PBij, P.Fixes n → Ty.rel0 P r records records) (now : Int) {ev : e.den0}
    (hev : ∀ P : PBij, P.Fixes n → Ty.rel0 P e ev ev) {insts : List (Instance m)}
    (hl : ∀ P : PBij, P.Fixes n → Insts.Rel P insts insts) :
    ∀ x ∈ (machineStep T records now ev m insts).2, ∀ P : PBij, P.Fixes n → Started.Rel P x x := by
  intro x hx P hP
  simp only [machineStep, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, ⟨k, hk, rfl⟩, hx⟩ := hx
  have hk0 : k ∈ (show List m.key.den0 from m.instances.fn (records, ())) :=
    mem_of_mem_dedupBy _ _ ((List.mergeSort_perm _ _).mem_iff.1 hk)
  have hb : Multi (Ty.rel0 (PBij.below n) m.key) (show List m.key.den0 from m.instances.fn (records, ()))
      (m.instances.fn (records, ())) :=
    (hm.self _).instances _ _ ⟨hrec _ (PBij.below_fixes n), trivial⟩
  obtain ⟨k', -, hkk⟩ := hb.mem_left hk0
  have hks : Ty.rel0 P m.key k k := Ty.self_of_below hP m.key hm.key hkk
  exact forall2_self (reactKey_rel hm (hl P hP) (hrec P hP) now (hev P hP) hks).2 x hx

theorem reactMachines_self {records : r.den0} (hrec : ∀ P : PBij, P.Fixes n → Ty.rel0 P r records records) (now : Int)
    {ev : e.den0} (hev : ∀ P : PBij, P.Fixes n → Ty.rel0 P e ev ev) : {ms : List (MachineV r e)} →
    (∀ m ∈ ms, m.Equi) → (l : Machines ms) → (∀ P : PBij, P.Fixes n → Machines.Rel P l l) →
    ∀ x ∈ (reactMachines T records now ev l).2, ∀ P : PBij, P.Fixes n → Started.Rel P x x
  | [], _, .nil, _, x, hx => by simp [reactMachines] at hx
  | _ :: _, hms, .cons insts rest, hl, x, hx => by
    simp only [reactMachines, List.mem_append] at hx
    rcases hx with hx | hx
    · exact machineStep_self T (hms _ List.mem_cons_self) hrec now hev
        (fun P hP => (hl P hP).1) x hx
    · exact reactMachines_self hrec now hev (fun m h => hms m (List.mem_cons_of_mem _ h)) rest
        (fun P hP => (hl P hP).2) x hx

end Machine

variable {v : ServiceV} {n : Nat}

/-- Every effect an event starts relates to itself under each renaming that keeps the counters below `n`, when the
records, the instances and the event do. -/
theorem react_self (hv : v.Equivariant) {s : State v}
    (hs : ∀ P : PBij, P.Fixes n → Ty.rel0 P v.records s.records s.records ∧ Machines.Rel P s.machines s.machines)
    {ev : v.event.den0} (hev : ∀ P : PBij, P.Fixes n → Ty.rel0 P v.event ev ev) :
    ∀ x ∈ (react T s ev).2, ∀ P : PBij, P.Fixes n → Started.Rel P x x := by
  have hrec : ∀ P : PBij, P.Fixes n → Ty.rel0 P v.records (v.apply.fn (.inl (s.records, s.now, ()), ev, ())) (v.apply.fn (.inl (s.records, s.now, ()), ev, ())) :=
    fun P hP => (hv.self P).apply _ _ ⟨⟨(hs P hP).1, rfl, trivial⟩, hev P hP, trivial⟩
  intro x hx P hP
  simp only [react, List.mem_append] at hx
  rcases hx with hx | hx
  · exact reactMachines_self T hrec s.now hev hv.machines s.machines
      (fun P hP => (hs P hP).2) x hx P hP
  · simp only [List.mem_flatMap, List.mem_map] at hx
    obtain ⟨y, hy, eff, he, rfl⟩ := hx
    have hl := EffectFun.apply_rel y.react ((hv.self P).reactions y hy)
      (xs := (.inl (v.apply.fn (.inl (s.records, s.now, ()), ev, ()), s.now, ()), ev, ()))
      (ys := (.inl (v.apply.fn (.inl (s.records, s.now, ()), ev, ()), s.now, ()), ev, ())) ⟨⟨hrec P hP, rfl, trivial⟩, hev P hP, trivial⟩
    exact ⟨.reaction _, forall2_self hl eff he⟩

theorem applyEvents_self (hv : v.Equivariant) (n : Nat) :
    (evs : List v.event.den0) → (a : Acc v) → Below Acc.Self n a →
    (∀ ev ∈ evs, ∀ P : PBij, P.Fixes n → Ty.rel0 P v.event ev ev) → ∀ b, applyEvents T a evs = .ok b → Below Acc.Self n b
  | [], a, ha, _, b, h => by
    simp only [applyEvents, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ha
  | ev :: evs, a, ha, hev, b, h => by
    unfold applyEvents at h
    rw [List.foldlM_cons] at h
    let a2 : Acc v := { a with state := (react T a.state ev).1, events := a.events ++ [ev] }
    cases hs : start a2 (react T a.state ev).2 with
    | error e => simp only [a2] at hs; simp [hs, bind, Except.bind] at h
    | ok a1 =>
      simp only [a2] at hs
      simp only [hs, bind, Except.bind] at h
      have hev1 : ∀ P : PBij, P.Fixes n → Ty.rel0 P v.event ev ev := hev ev List.mem_cons_self
      have h1 : Below Acc.Self n a1 := fun P hP => by
        obtain ⟨hA, hp, ho⟩ := ha P hP
        have hr := react_rel T hv (R := ⟨P, PBij.refl⟩) hA.1 (hev1 P hP)
        obtain ⟨_, hevs, hout, hob, hob', hown⟩ := hA
        exact start_self (a := a2) ⟨⟨hr.1, hevs.append (Multi.cons (hev1 P hP) Multi.nil), hout, hob, hob', hown⟩,
          fun p hp' => hp p (by simpa [a2, react] using hp'), ho⟩
          (react_self T hv (s := a.state) (fun P hP => ⟨(ha P hP).1.1.1, (ha P hP).1.1.2.1⟩) hev1 · · P hP) hs
      exact applyEvents_self hv n evs a1 h1 (fun e he => hev e (List.mem_cons_of_mem _ he)) b h

theorem below_fresh {n k : Nat} {a : Acc v} (h : Below Acc.Self n a) :
    Below Acc.Self n { a with state := { a.state with fresh := k } } := fun P hP => by
  obtain ⟨⟨hst, hevs, hout, ho, ho', hown⟩, hp, hoi⟩ := h P hP
  exact ⟨⟨hst, hevs, hout, ho, ho', hown⟩, hp, hoi⟩

/-- The step in progress with some of its waiting own effects. -/
theorem Acc.Self.sub_own {P : PBij} {a : Acc v} (h : Acc.Self P a) {xs : List (OwnEffectV v.event)}
    (hxs : ∀ x ∈ xs, x ∈ a.own) : Acc.Self P { a with own := xs } := by
  obtain ⟨⟨hst, hevs, hout, ho, ho', -⟩, hp, hoi⟩ := h
  exact ⟨⟨hst, hevs, hout, ho, ho', Multi.of_forall2 (forall2_refl_of fun x hx => hoi x (hxs x hx))⟩, hp,
    fun x hx => hoi x (hxs x hx)⟩

theorem runCommand_self (hv : v.Equivariant) {a : Acc v}
    (ha : Below Acc.Self (a.state.fresh + 1) a) {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands)
    {c : (Ty.origin v.caller).den0} (hc : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P (Ty.origin v.caller) c c) {i : x.input.den0}
    (hi : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P x.input i i)
    {f : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))}
    (hf : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Fun.Rel P f f) :
    ∀ b, runCommand T a x c i f = .ok b → Below Acc.Self (a.state.fresh + 1) b := by
  intro b h
  have hdec : ∀ P : PBij, P.Fixes (a.state.fresh + 1) →
      Ty.rel0 P (Ty.result (.list v.event) x.rejection) (x.decide.fn (ctx a.state a.state.records c i, ()))
        (x.decide.fn (ctx a.state a.state.records c i, ())) := fun P hP => by
    have hA := ha P hP
    exact ((hv.self P).commands x hx).decide _ _
      ⟨⟨hA.1.1.1, hi P hP, hc P hP, rfl, hP _ (Nat.lt_succ_self _), trivial⟩, trivial⟩
  have ha1 : Below Acc.Self (a.state.fresh + 1) { a with state := { a.state with fresh := a.state.fresh + 1 } } :=
    below_fresh ha
  unfold runCommand execCommand at h
  cases had : admit x.callers x.accepts c i with
  | cons r rs => simp [had, bind, Except.bind] at h
  | nil =>
    simp only [had] at h
    revert hdec h
    generalize x.decide.fn (ctx a.state a.state.records c i, ()) = d
    intro hdec h
    match d, hdec with
    | .inl (evs, ()), hdec =>
      simp only [bind, Except.bind] at h
      cases h3 : applyEvents T { a with state := { a.state with fresh := a.state.fresh + 1 } } evs with
      | error e => simp [h3] at h
      | ok a3 =>
        simp only [h3] at h
        have hevs : ∀ ev ∈ (show List v.event.den0 from evs), ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.event ev ev :=
          fun ev hev P hP => forall2_self (hdec P hP).1 ev hev
        have hs3 := applyEvents_self T hv _ evs _ ha1 hevs a3 h3
        split at h
        · cases h
        · next r heq =>
          split at heq
          · cases heq
          cases heq
          simp only at h
          have hans : ∀ ev ∈ (show List v.event.den0 from f.fn (okNil, ())), ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.event ev ev :=
            fun ev hev P hP => forall2_self (hf P hP (okNil, ()) (okNil, ()) ⟨okNil_rel, trivial⟩) ev hev
          exact applyEvents_self T hv _ _ _ hs3 hans b h
    | .inr (.inl (j, ())), hdec =>
      simp only [bind, Except.bind] at h
      have hans : ∀ ev ∈ (show List v.event.den0 from f.fn (.inr (.inl (j, ())), ())), ∀ P : PBij, P.Fixes (a.state.fresh + 1) →
          Ty.rel0 P v.event ev ev :=
        fun ev hev P hP => by
          obtain ⟨hj, -⟩ := hdec P hP
          exact forall2_self (hf P hP (.inr (.inl (j, ())), ()) (.inr (.inl (j, ())), ()) ⟨⟨hj, trivial⟩, trivial⟩) ev hev
      exact applyEvents_self T hv _ _ _ ha1 hans b h

theorem runQuery_self (hv : v.Equivariant) {a : Acc v}
    (ha : Below Acc.Self (a.state.fresh + 1) a) {x : QueryV v.records v.caller} (hx : x ∈ v.queries)
    {c : (Ty.origin v.caller).den0} (hc : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P (Ty.origin v.caller) c c) {i : x.input.den0}
    (hi : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P x.input i i)
    {f : Fun (Ty.fn [x.output] (.list v.event))} (hf : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Fun.Rel P f f) :
    ∀ b, runQuery T a x c i f = .ok b → Below Acc.Self (a.state.fresh + 1) b := by
  intro b h
  unfold runQuery execQuery at h
  cases had : admit x.callers x.accepts c i with
  | cons r rs => simp [had] at h
  | nil =>
    simp only [had] at h
    have hans : ∀ ev ∈ (show List v.event.den0 from f.fn (x.resolve.fn (queryCtx a.state a.state.records c i, ()), ())),
        ∀ P : PBij,
        P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.event ev ev := fun ev hev P hP => by
      have hA := ha P hP
      exact forall2_self (hf P hP (x.resolve.fn (queryCtx a.state a.state.records c i, ()), ())
        (x.resolve.fn (queryCtx a.state a.state.records c i, ()), ()) ⟨((hv.self P).queries x hx).resolve _ _
        ⟨⟨hA.1.1.1, hi P hP, hc P hP, rfl, trivial⟩, trivial⟩, trivial⟩) ev hev
    exact applyEvents_self T hv _ _ { a with state := { a.state with fresh := a.state.fresh + 1 } } (below_fresh ha) hans
      b h

theorem start_fresh : (effs : List (Sender × EffectV v.event)) → (a : Acc v) → {b : Acc v} → start a effs = .ok b →
    b.state.fresh = a.state.fresh
  | [], a, b, h => by
    simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | (snd, eff) :: effs, a, b, h => by
    simp only [start, List.foldlM_cons] at h
    have tail : ∀ a', start a' effs = .ok b → a'.state.fresh = a.state.fresh → b.state.fresh = a.state.fresh :=
      fun a' h' e => (start_fresh effs a' h').trans e
    cases eff with
    | request r =>
      cases ho : r.ownerIn v.declared with
      | none => simp only [ho] at h; cases h
      | some o =>
        simp only [ho, bind, Except.bind] at h
        exact tail _ h rfl
    | command => simp only [bind, Except.bind] at h; exact tail _ h rfl
    | query => simp only [bind, Except.bind] at h; exact tail _ h rfl

theorem applyEvents_fresh : (evs : List v.event.den0) → (a : Acc v) → {b : Acc v} → applyEvents T a evs = .ok b →
    b.state.fresh = a.state.fresh
  | [], a, b, h => by
    simp only [applyEvents, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | ev :: evs, a, b, h => by
    unfold applyEvents at h
    rw [List.foldlM_cons] at h
    cases hs : start { a with state := (react T a.state ev).1, events := a.events ++ [ev] } (react T a.state ev).2 with
    | error e => simp [hs, bind, Except.bind] at h
    | ok a1 =>
      simp only [hs, bind, Except.bind] at h
      rw [applyEvents_fresh evs a1 h, start_fresh _ _ hs]
      rfl

theorem runCommand_fresh {a b : Acc v} {x : CommandV v.records v.event v.caller} {c : (Ty.origin v.caller).den0}
    {i : x.input.den0} {f : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))}
    (h : runCommand T a x c i f = .ok b) : b.state.fresh = a.state.fresh + 1 := by
  unfold runCommand execCommand at h
  cases had : admit x.callers x.accepts c i with
  | cons r rs => simp [had, bind, Except.bind] at h
  | nil =>
    simp only [had] at h
    generalize x.decide.fn (ctx a.state a.state.records c i, ()) = d at h
    match d with
    | .inl (evs, ()) =>
      simp only [bind, Except.bind] at h
      cases h3 : applyEvents T { a with state := { a.state with fresh := a.state.fresh + 1 } } evs with
      | error e => simp [h3] at h
      | ok a3 =>
        simp only [h3] at h
        split at h
        · cases h
        · next r heq =>
          split at heq
          · cases heq
          cases heq
          simp only at h
          rw [applyEvents_fresh T _ _ h]
          exact applyEvents_fresh T _ _ h3
    | .inr (.inl (j, ())) =>
      simp only [bind, Except.bind] at h
      exact applyEvents_fresh T _ _ h

/-- An own command or query that runs takes one counter. -/
theorem runOwn_fresh {a b : Acc v} {e : OwnEffectV v.event} (h : runOwn T a e = .ok b) :
    b.state.fresh = a.state.fresh + 1 := by
  cases e with
  | command name c i j value onAnswer =>
    dsimp only [runOwn] at h
    revert h
    generalize Ty.same c v.caller = oc
    generalize ownCommand (v := v) name i j = ox
    cases oc with
    | none => intro h; change Except.error _ = _ at h; cases h
    | some hcp =>
      cases ox with
      | none => intro h; change Except.error _ = _ at h; cases h
      | some x =>
        obtain ⟨hcp⟩ := hcp
        obtain ⟨x, hi, hj⟩ := x
        subst hcp hi hj
        intro h
        change runCommand T a x _ _ _ = _ at h
        exact runCommand_fresh T h
  | query name c i o value onAnswer =>
    dsimp only [runOwn] at h
    revert h
    generalize Ty.same c v.caller = oc
    generalize ownQuery (v := v) name i o = ox
    cases oc with
    | none => intro h; change Except.error _ = _ at h; cases h
    | some hcp =>
      cases ox with
      | none => intro h; change Except.error _ = _ at h; cases h
      | some x =>
        obtain ⟨hcp⟩ := hcp
        obtain ⟨x, hi, ho⟩ := x
        subst hcp hi ho
        intro h
        change runQuery T a x _ _ _ = _ at h
        unfold runQuery at h
        split at h
        · cases h
        · exact applyEvents_fresh T _ _ h

theorem OwnEffectV.rel_command_inv {P : PBij} {e : Ty} {n : String} {c i j : Ty} {x x' : i.den0}
    {f f' : Fun (Ty.fn [Ty.result Ty.nil j] (.list e))}
    (h : OwnEffectV.Rel P (.command n c i j x f) (.command n c i j x' f')) :
    Ty.rel0 P i x x' ∧ Fun.Rel P f f' := by
  cases h; exact ⟨‹_›, ‹_›⟩

theorem OwnEffectV.rel_query_inv {P : PBij} {e : Ty} {n : String} {c i o : Ty} {x x' : i.den0}
    {f f' : Fun (Ty.fn [o] (.list e))}
    (h : OwnEffectV.Rel P (.query n c i o x f) (.query n c i o x' f')) :
    Ty.rel0 P i x x' ∧ Fun.Rel P f f' := by
  cases h; exact ⟨‹_›, ‹_›⟩

theorem runOwn_self (hv : v.Equivariant) {a : Acc v}
    (ha : Below Acc.Self (a.state.fresh + 1) a) {e : OwnEffectV v.event}
    (he : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → OwnEffectV.Rel P e e) :
    ∀ b, runOwn T a e = .ok b → Below Acc.Self (a.state.fresh + 1) b := by
  intro b h
  cases e with
  | command name c i j value onAnswer =>
    dsimp only [runOwn] at h
    revert h
    generalize Ty.same c v.caller = oc
    generalize hox : ownCommand (v := v) name i j = ox
    cases oc with
    | none => intro h; change Except.error _ = _ at h; cases h
    | some hcp =>
      cases ox with
      | none => intro h; change Except.error _ = _ at h; cases h
      | some x =>
        obtain ⟨hcp⟩ := hcp
        have hmem := ownCommand_mem hox
        obtain ⟨x, hi, hj⟩ := x
        subst hcp hi hj
        intro h
        change runCommand T a x _ _ _ = _ at h
        exact runCommand_self T hv ha hmem (fun _ _ => rel0_own)
          (fun P hP => (OwnEffectV.rel_command_inv (he P hP)).1) (fun P hP => (OwnEffectV.rel_command_inv (he P hP)).2) b h
  | query name c i o value onAnswer =>
    dsimp only [runOwn] at h
    revert h
    generalize Ty.same c v.caller = oc
    generalize hox : ownQuery (v := v) name i o = ox
    cases oc with
    | none => intro h; change Except.error _ = _ at h; cases h
    | some hcp =>
      cases ox with
      | none => intro h; change Except.error _ = _ at h; cases h
      | some x =>
        obtain ⟨hcp⟩ := hcp
        have hmem := ownQuery_mem hox
        obtain ⟨x, hi, ho⟩ := x
        subst hcp hi ho
        intro h
        change runQuery T a x _ _ _ = _ at h
        exact runQuery_self T hv ha hmem (fun _ _ => rel0_own)
          (fun P hP => (OwnEffectV.rel_query_inv (he P hP)).1) (fun P hP => (OwnEffectV.rel_query_inv (he P hP)).2) b h

/-- A step in progress whose names are all below its counter. The own cascade keeps it (`ownSys_preserved`). -/
abbrev Supp (a : Acc v) : Prop := Below Acc.Self a.state.fresh a

/-- The own cascade keeps every name below the counter. -/
theorem ownSys_preserved (hv : v.Equivariant) : Diamond.Preserved (ownSys T v) Supp := by
  intro a i b ha hi hb
  simp only [ownSys, List.getElem?_eq_getElem hi] at hb
  have hmem : a.own[i] ∈ a.own := List.getElem_mem hi
  have ha' : Below Acc.Self (a.state.fresh + 1) { a with own := a.own.eraseIdx i } :=
    Below.mono (fun P hP => (ha P hP).sub_own fun x hx => List.mem_of_mem_eraseIdx hx) (Nat.le_succ _)
  have hs := runOwn_self T hv (a := { a with own := a.own.eraseIdx i }) ha'
    (fun P hP => (ha P (hP.mono (Nat.le_succ _))).2.2 _ hmem) b hb
  have hfr : b.state.fresh = a.state.fresh + 1 := runOwn_fresh T (a := { a with own := a.own.eraseIdx i }) hb
  show Supp b
  rw [Supp, hfr]; exact hs

end Step

end Tazuna.Ir
