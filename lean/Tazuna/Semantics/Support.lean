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

section Self
variable {n : Nat} {P : PBij}

theorem IdV.self_of_below {a b : IdV} (h : IdV.Rel (PBij.below n) a b) (hP : P.Fixes n) : IdV.Rel P a a := by
  rcases h with ⟨s, rfl, rfl⟩ | ⟨c, c', i, ⟨rfl, hc⟩, rfl, rfl⟩
  · exact .inl ⟨s, rfl, rfl⟩
  · exact .inr ⟨c, c, i, hP c hc, rfl, rfl⟩

theorem forall2_self_of {α β : Type} {r : α → β → Prop} {s : α → α → Prop} (h : ∀ a b, r a b → s a a) :
    {xs : List α} → {ys : List β} → Forall2 r xs ys → Forall2 s xs xs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hx, hxs⟩ => ⟨h _ _ hx, forall2_self_of h hxs⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Multi.self_of {α β : Type} {r : α → β → Prop} {s : α → α → Prop} (h : ∀ a b, r a b → s a a)
    {xs : List α} {ys : List β} : Multi r xs ys → Multi s xs xs
  | ⟨_, hz, _⟩ => Multi.of_forall2 (forall2_self_of h hz)

mutual
/-- Stored data that relates to anything under the renaming keeping the counters below `n` relates to itself under
every renaming that keeps them. -/
theorem Ty.self_of_below (hP : P.Fixes n) : (t : Ty) → t.wire = true → {x y : t.den0} → Ty.rel0 (PBij.below n) t x y →
    Ty.rel0 P t x x
  | .int, _, _, _, _ | .str, _, _, _, _ | .date, _, _, _, _ => rfl
  | .param _, _, _, _, _ => trivial
  | .list t, hw, _, _, h => forall2_self_of (fun _ _ => Ty.self_of_below hP t hw) h
  | .bag t, hw, _, _, h => Multi.self_of (fun _ _ => Ty.self_of_below hP t hw) h
  | .table k v, hw, _, _, h => by
    simp only [Ty.wire, Bool.and_eq_true] at hw
    exact Multi.self_of (fun _ _ hab => ⟨Ty.self_of_below hP k hw.1 hab.1, Ty.self_of_below hP v hw.2 hab.2⟩) h
  | .tuple ts, hw, _, _, h => Ty.selfs_of_below hP ts hw h
  | .adt _ _ vs, hw, _, _, h => Ty.selfAlts_of_below hP vs hw h
  | .id, _, _, _, h => IdV.self_of_below h hP
  | .fn .., hw, _, _, _ | .dsl .., hw, _, _, _ => by simp [Ty.wire] at hw
theorem Ty.selfs_of_below (hP : P.Fixes n) : (ts : List Ty) → Ty.wires ts = true → {x y : (Ty.semsWith Dsl.base ts).1} →
    Ty.relsWith Dsl.base (Dsl.rel0 (PBij.below n)) (PBij.below n) ts x y → Ty.relsWith Dsl.base (Dsl.rel0 P) P ts x x
  | [], _, _, _, _ => trivial
  | t :: ts, hw, _, _, ⟨h, hs⟩ => by
    simp only [Ty.wires, Bool.and_eq_true] at hw
    exact ⟨Ty.self_of_below hP t hw.1 h, Ty.selfs_of_below hP ts hw.2 hs⟩
theorem Ty.selfAlts_of_below (hP : P.Fixes n) : (vs : List (List Ty)) → Ty.wiress vs = true → {x y : (Ty.semAltsWith Dsl.base vs).1} →
    Ty.relAltsWith Dsl.base (Dsl.rel0 (PBij.below n)) (PBij.below n) vs x y →
    Ty.relAltsWith Dsl.base (Dsl.rel0 P) P vs x x
  | [], _, x, _, _ => nomatch x
  | fs :: _, hw, .inl _, .inl _, h => by
    simp only [Ty.wiress, Bool.and_eq_true] at hw
    exact Ty.selfs_of_below hP fs hw.1 h
  | _ :: vs, hw, .inr _, .inr _, h => by
    simp only [Ty.wiress, Bool.and_eq_true] at hw
    exact Ty.selfAlts_of_below hP vs hw.2 h
  | _ :: _, _, .inl _, .inr _, h | _ :: _, _, .inr _, .inl _, h => h.elim
end

end Self

namespace Step

variable {v : ServiceV} (T : List TypeDecl)

theorem start_own_mem : (effs : List (Sender × EffectV v.event)) → (a : Acc v) → {b : Acc v} → start a effs = .ok b →
    ∀ x ∈ b.own, x ∈ a.own ∨ x.isRequest = false ∧ ∃ s, (s, x) ∈ effs
  | [], a, b, h, x, hx => by
    simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .inl hx
  | (snd, eff) :: effs, a, b, h, x, hx => by
    simp only [start, List.foldlM_cons] at h
    have tail : ∀ a', start a' effs = .ok b →
        (x ∈ a'.own → x ∈ a.own ∨ x.isRequest = false ∧ ∃ s, (s, x) ∈ (snd, eff) :: effs) →
        x ∈ a.own ∨ x.isRequest = false ∧ ∃ s, (s, x) ∈ (snd, eff) :: effs := fun a' h' k => by
      rcases start_own_mem effs a' h' x hx with h1 | ⟨hr, s, hs⟩
      · exact k h1
      · exact .inr ⟨hr, s, List.mem_cons_of_mem _ hs⟩
    cases eff with
    | request r =>
      cases ho : r.ownerIn v.declared with
      | none => simp only [ho] at h; cases h
      | some o =>
        simp only [ho, bind, Except.bind] at h
        exact tail _ h .inl
    | command name c i j caller value onAnswer =>
      simp only [bind, Except.bind] at h
      refine tail _ h fun h1 => ?_
      rcases List.mem_append.1 h1 with h1 | h1
      · exact .inl h1
      · rw [List.mem_singleton] at h1; subst h1; exact .inr ⟨rfl, snd, List.mem_cons_self⟩
    | query name c i o caller value onAnswer =>
      simp only [bind, Except.bind] at h
      refine tail _ h fun h1 => ?_
      rcases List.mem_append.1 h1 with h1 | h1
      · exact .inl h1
      · rw [List.mem_singleton] at h1; subst h1; exact .inr ⟨rfl, snd, List.mem_cons_self⟩

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
theorem machineStep_self {m : MachineV r e} (hm : m.Equi) (hkw : m.key.wire = true) {records : r.den0}
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
  have hks : Ty.rel0 P m.key k k := Ty.self_of_below hP m.key hkw hkk
  exact forall2_self (reactKey_rel hm (hl P hP) (hrec P hP) now (hev P hP) hks).2 x hx

theorem reactMachines_self {records : r.den0} (hrec : ∀ P : PBij, P.Fixes n → Ty.rel0 P r records records) (now : Int)
    {ev : e.den0} (hev : ∀ P : PBij, P.Fixes n → Ty.rel0 P e ev ev) : {ms : List (MachineV r e)} →
    (∀ m ∈ ms, m.Equi ∧ m.key.wire = true) → (l : Machines ms) → (∀ P : PBij, P.Fixes n → Machines.Rel P l l) →
    ∀ x ∈ (reactMachines T records now ev l).2, ∀ P : PBij, P.Fixes n → Started.Rel P x x
  | [], _, .nil, _, x, hx => by simp [reactMachines] at hx
  | _ :: _, hms, .cons insts rest, hl, x, hx => by
    simp only [reactMachines, List.mem_append] at hx
    rcases hx with hx | hx
    · exact machineStep_self T (hms _ List.mem_cons_self).1 (hms _ List.mem_cons_self).2 hrec now hev
        (fun P hP => (hl P hP).1) x hx
    · exact reactMachines_self hrec now hev (fun m h => hms m (List.mem_cons_of_mem _ h)) rest
        (fun P hP => (hl P hP).2) x hx

end Machine

variable {v : ServiceV} {n : Nat}

/-- Every effect an event starts relates to itself under each renaming that keeps the counters below `n`, when the
records, the instances and the event do. -/
theorem react_self (hv : v.Equivariant) (hkw : ∀ m ∈ v.machines, m.key.wire = true) {s : State v}
    (hs : ∀ P : PBij, P.Fixes n → Ty.rel0 P v.records s.records s.records ∧ Machines.Rel P s.machines s.machines)
    {ev : v.event.den0} (hev : ∀ P : PBij, P.Fixes n → Ty.rel0 P v.event ev ev) :
    ∀ x ∈ (react T s ev).2, ∀ P : PBij, P.Fixes n → Started.Rel P x x := by
  have hrec : ∀ P : PBij, P.Fixes n → Ty.rel0 P v.records (v.apply.fn (s.records, ev, ())) (v.apply.fn (s.records, ev, ())) :=
    fun P hP => (hv.self P).apply _ _ ⟨(hs P hP).1, hev P hP, trivial⟩
  intro x hx P hP
  simp only [react, List.mem_append] at hx
  rcases hx with hx | hx
  · exact reactMachines_self T hrec s.now hev (fun m hm => ⟨hv.machines m hm, hkw m hm⟩) s.machines
      (fun P hP => (hs P hP).2) x hx P hP
  · simp only [List.mem_flatMap, List.mem_map] at hx
    obtain ⟨y, hy, eff, he, rfl⟩ := hx
    have hl := EffectFun.apply_rel y.react ((hv.self P).reactions y hy)
      (xs := (.inl (v.apply.fn (s.records, ev, ()), s.now, ()), ev, ()))
      (ys := (.inl (v.apply.fn (s.records, ev, ()), s.now, ()), ev, ())) ⟨⟨hrec P hP, rfl, trivial⟩, hev P hP, trivial⟩
    exact ⟨.reaction _, forall2_self hl eff he⟩

/-- Names below `n`: every renaming that keeps the counters below `n` relates the step to itself. -/
def SelfAt (n : Nat) (a : Acc v) : Prop := ∀ P : PBij, P.Fixes n → ∃ W, Acc.Rel ⟨P, W⟩ a a

/-- A waiting own effect with names below `n`. -/
def OwnAt (n : Nat) (x : EffectV v.event) : Prop := x.isRequest = false ∧ ∀ P : PBij, P.Fixes n → EffectV.Rel P x x

theorem lifted_self {a b : Acc v} {P : PBij} {W : PBij} (h : Lifted ⟨P, W⟩ a a (.ok b) (.ok b)) :
    ∃ W', Acc.Rel ⟨P, W'⟩ b b := by
  rcases h with ⟨h, _⟩ | ⟨b1, b2, ⟨ctr, wire⟩, h1, h2, hc, hb, -⟩
  · exact h.elim
  · cases h1; cases h2
    simp only at hc
    subst hc
    exact ⟨wire, hb⟩

theorem applyEvents_self (hv : v.Equivariant) (hkw : ∀ m ∈ v.machines, m.key.wire = true) (n : Nat) :
    (evs : List v.event.den0) → (a : Acc v) → SelfAt n a → (∀ ev ∈ evs, ∀ P : PBij, P.Fixes n → Ty.rel0 P v.event ev ev) →
    ∀ b, applyEvents T a evs = .ok b → SelfAt n b ∧ ∀ x ∈ b.own, x ∈ a.own ∨ OwnAt n x
  | [], a, ha, _, b, h => by
    simp only [applyEvents, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨ha, fun x hx => .inl hx⟩
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
      have h1 : SelfAt n a1 := fun P hP => by
        obtain ⟨W, hA⟩ := ha P hP
        have hr := react_rel T hv (R := ⟨P, W⟩) hA.1 (hev1 P hP)
        obtain ⟨_, hevs, hout, ho, ho', hown⟩ := hA
        have hl := start_rel (a := a2) (a' := a2) ⟨hr.1, hevs.append (Multi.cons (hev1 P hP) Multi.nil), hout, ho, ho',
          hown⟩ hr.2
        rw [hs] at hl
        exact lifted_self hl
      have hown1 : ∀ x ∈ a1.own, x ∈ a.own ∨ OwnAt n x := by
        intro x hx
        rcases start_own_mem _ _ hs x hx with hx | ⟨hr, snd, hx⟩
        · exact .inl hx
        · refine .inr ⟨hr, fun P hP => ?_⟩
          have hS := react_self T hv hkw (s := a.state) (fun P hP => by
            obtain ⟨W, hA⟩ := ha P hP; exact ⟨hA.1.1, hA.1.2.1⟩) hev1 _ hx P hP
          exact hS.2
      obtain ⟨hb, hbo⟩ := applyEvents_self hv hkw n evs a1 h1 (fun e he => hev e (List.mem_cons_of_mem _ he)) b h
      refine ⟨hb, fun x hx => ?_⟩
      rcases hbo x hx with hx | hx
      · exact hown1 x hx
      · exact .inr hx

theorem SelfAt.mono {n m : Nat} {a : Acc v} (h : SelfAt n a) (hnm : n ≤ m) : SelfAt m a :=
  fun P hP => h P (hP.mono hnm)

theorem SelfAt.fresh {n k : Nat} {a : Acc v} (h : SelfAt n a) :
    SelfAt n { a with state := { a.state with fresh := k } } := fun P hP => by
  obtain ⟨W, hst, hevs, hout, ho, ho', hown⟩ := h P hP
  exact ⟨W, hst, hevs, hout, ho, ho', hown⟩

theorem runCommand_self (hv : v.Equivariant) (hkw : ∀ m ∈ v.machines, m.key.wire = true) {a : Acc v}
    (ha : SelfAt (a.state.fresh + 1) a) {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands)
    {c : v.caller.den0} (hc : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.caller c c) {i : x.input.den0}
    (hi : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P x.input i i)
    {f : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))}
    (hf : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Fun.Rel P f f) :
    ∀ b, runCommand T a x c i f = .ok b → SelfAt (a.state.fresh + 1) b ∧
      ∀ y ∈ b.own, y ∈ a.own ∨ OwnAt (a.state.fresh + 1) y := by
  intro b h
  have hdec : ∀ P : PBij, P.Fixes (a.state.fresh + 1) →
      Ty.rel0 P (Ty.result (.list v.event) x.rejection) (x.decide.fn (ctx a.state a.state.records c i, ()))
        (x.decide.fn (ctx a.state a.state.records c i, ())) := fun P hP => by
    obtain ⟨W, hA⟩ := ha P hP
    exact ((hv.self P).commands x hx).decide _ _
      ⟨⟨hA.1.1, hi P hP, hc P hP, rfl, hP _ (Nat.lt_succ_self _), trivial⟩, trivial⟩
  have ha1 : SelfAt (a.state.fresh + 1) { a with state := { a.state with fresh := a.state.fresh + 1 } } := ha.fresh
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
        obtain ⟨hs3, ho3⟩ := applyEvents_self T hv hkw _ evs _ ha1 hevs a3 h3
        split at h
        · cases h
        · next r heq =>
          split at heq
          · cases heq
          cases heq
          simp only at h
          have hans : ∀ ev ∈ (show List v.event.den0 from f.fn (okNil, ())), ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.event ev ev :=
            fun ev hev P hP => forall2_self (hf P hP (okNil, ()) (okNil, ()) ⟨okNil_rel, trivial⟩) ev hev
          obtain ⟨hs4, ho4⟩ := applyEvents_self T hv hkw _ _ _ hs3 hans b h
          refine ⟨hs4, fun y hy => ?_⟩
          rcases ho4 y hy with hy | hy
          · exact ho3 y hy
          · exact .inr hy
    | .inr (.inl (j, ())), hdec =>
      simp only [bind, Except.bind] at h
      have hans : ∀ ev ∈ (show List v.event.den0 from f.fn (.inr (.inl (j, ())), ())), ∀ P : PBij, P.Fixes (a.state.fresh + 1) →
          Ty.rel0 P v.event ev ev :=
        fun ev hev P hP => by
          obtain ⟨hj, -⟩ := hdec P hP
          exact forall2_self (hf P hP (.inr (.inl (j, ())), ()) (.inr (.inl (j, ())), ()) ⟨⟨hj, trivial⟩, trivial⟩) ev hev
      exact applyEvents_self T hv hkw _ _ _ ha1 hans b h

theorem runQuery_self (hv : v.Equivariant) (hkw : ∀ m ∈ v.machines, m.key.wire = true) {a : Acc v}
    (ha : SelfAt (a.state.fresh + 1) a) {x : QueryV v.records v.caller} (hx : x ∈ v.queries)
    {c : v.caller.den0} (hc : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.caller c c) {i : x.input.den0}
    (hi : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P x.input i i)
    {f : Fun (Ty.fn [x.output] (.list v.event))} (hf : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Fun.Rel P f f) :
    ∀ b, runQuery T a x c i f = .ok b → SelfAt (a.state.fresh + 1) b ∧
      ∀ y ∈ b.own, y ∈ a.own ∨ OwnAt (a.state.fresh + 1) y := by
  intro b h
  unfold runQuery execQuery at h
  cases had : admit x.callers x.accepts c i with
  | cons r rs => simp [had] at h
  | nil =>
    simp only [had] at h
    have hans : ∀ ev ∈ (show List v.event.den0 from f.fn (x.resolve.fn (queryCtx a.state a.state.records c i, ()), ())),
        ∀ P : PBij,
        P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.event ev ev := fun ev hev P hP => by
      obtain ⟨W, hA⟩ := ha P hP
      exact forall2_self (hf P hP (x.resolve.fn (queryCtx a.state a.state.records c i, ()), ())
        (x.resolve.fn (queryCtx a.state a.state.records c i, ()), ()) ⟨((hv.self P).queries x hx).resolve _ _
        ⟨⟨hA.1.1, hi P hP, hc P hP, rfl, trivial⟩, trivial⟩, trivial⟩) ev hev
    exact applyEvents_self T hv hkw _ _ { a with state := { a.state with fresh := a.state.fresh + 1 } } ha.fresh hans b h

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

theorem runCommand_fresh {a b : Acc v} {x : CommandV v.records v.event v.caller} {c : v.caller.den0}
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
theorem runOwn_fresh {a b : Acc v} {e : EffectV v.event} (hr : e.isRequest = false) (h : runOwn T a e = .ok b) :
    b.state.fresh = a.state.fresh + 1 := by
  cases e with
  | request => cases hr
  | command name c i j caller value onAnswer =>
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
  | query name c i o caller value onAnswer =>
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

theorem EffectV.rel_command_inv {P : PBij} {e : Ty} {n : String} {c i j : Ty} {a a' : c.den0} {x x' : i.den0}
    {f f' : Fun (Ty.fn [Ty.result Ty.nil j] (.list e))}
    (h : EffectV.Rel P (.command n c i j a x f) (.command n c i j a' x' f')) :
    Ty.rel0 P c a a' ∧ Ty.rel0 P i x x' ∧ Fun.Rel P f f' := by
  cases h; exact ⟨‹_›, ‹_›, ‹_›⟩

theorem EffectV.rel_query_inv {P : PBij} {e : Ty} {n : String} {c i o : Ty} {a a' : c.den0} {x x' : i.den0}
    {f f' : Fun (Ty.fn [o] (.list e))}
    (h : EffectV.Rel P (.query n c i o a x f) (.query n c i o a' x' f')) :
    Ty.rel0 P c a a' ∧ Ty.rel0 P i x x' ∧ Fun.Rel P f f' := by
  cases h; exact ⟨‹_›, ‹_›, ‹_›⟩

theorem runOwn_self (hv : v.Equivariant) (hkw : ∀ m ∈ v.machines, m.key.wire = true) {a : Acc v}
    (ha : SelfAt (a.state.fresh + 1) a) {e : EffectV v.event}
    (he : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → EffectV.Rel P e e) :
    ∀ b, runOwn T a e = .ok b → SelfAt (a.state.fresh + 1) b ∧ ∀ y ∈ b.own, y ∈ a.own ∨ OwnAt (a.state.fresh + 1) y := by
  intro b h
  cases e with
  | request => cases h; exact ⟨ha, fun y hy => .inl hy⟩
  | command name c i j caller value onAnswer =>
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
        exact runCommand_self T hv hkw ha hmem (fun P hP => (EffectV.rel_command_inv (he P hP)).1)
          (fun P hP => (EffectV.rel_command_inv (he P hP)).2.1) (fun P hP => (EffectV.rel_command_inv (he P hP)).2.2) b h
  | query name c i o caller value onAnswer =>
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
        exact runQuery_self T hv hkw ha hmem (fun P hP => (EffectV.rel_query_inv (he P hP)).1)
          (fun P hP => (EffectV.rel_query_inv (he P hP)).2.1) (fun P hP => (EffectV.rel_query_inv (he P hP)).2.2) b h

/-- A step in progress whose names are all below its counter: every renaming that keeps those counters relates its
state to itself, and each waiting own effect to itself. The own cascade keeps it (`ownSys_preserved`). -/
def Supp (a : Acc v) : Prop := SelfAt a.state.fresh { a with own := [] } ∧ ∀ x ∈ a.own, OwnAt a.state.fresh x

theorem OwnAt.mono {n m : Nat} {x : EffectV v.event} (h : OwnAt n x) (hnm : n ≤ m) : OwnAt m x :=
  ⟨h.1, fun P hP => h.2 P (hP.mono hnm)⟩

theorem forall2_refl_of {α : Type} {r : α → α → Prop} : {xs : List α} → (∀ x ∈ xs, r x x) → Forall2 r xs xs
  | [], _ => trivial
  | _ :: _, h => ⟨h _ List.mem_cons_self, forall2_refl_of fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

theorem SelfAt.own {n : Nat} {a : Acc v} (h : SelfAt n { a with own := [] }) {xs : List (EffectV v.event)}
    (hxs : ∀ x ∈ xs, OwnAt n x) : SelfAt n { a with own := xs } := fun P hP => by
  obtain ⟨W, hst, hevs, hout, ho, ho', -⟩ := h P hP
  exact ⟨W, hst, hevs, hout, ho, ho', Multi.of_forall2 (forall2_refl_of fun x hx => (hxs x hx).2 P hP)⟩

theorem SelfAt.drop {n : Nat} {a : Acc v} (h : SelfAt n a) : SelfAt n { a with own := [] } := fun P hP => by
  obtain ⟨W, hst, hevs, hout, ho, ho', -⟩ := h P hP
  exact ⟨W, hst, hevs, hout, ho, ho', Multi.nil⟩

theorem mem_eraseIdx {α : Type} {x : α} : {l : List α} → {i : Nat} → x ∈ l.eraseIdx i → x ∈ l
  | [], _, h => by simp at h
  | _ :: _, 0, h => List.mem_cons_of_mem _ (by simpa using h)
  | y :: l, i + 1, h => by
    simp only [List.eraseIdx_cons_succ, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_eraseIdx h)

/-- The own cascade keeps every name below the counter. -/
theorem ownSys_preserved (hv : v.Equivariant) (hkw : ∀ m ∈ v.machines, m.key.wire = true) :
    Diamond.Preserved (ownSys T v) Supp := by
  intro a i b ha hi hb
  simp only [ownSys, List.getElem?_eq_getElem hi] at hb
  have hmem : a.own[i] ∈ a.own := List.getElem_mem hi
  have ha' : SelfAt (a.state.fresh + 1) { a with own := a.own.eraseIdx i } :=
    (SelfAt.own (a := a) ha.1 fun x hx => ha.2 x (mem_eraseIdx hx)).mono (Nat.le_succ _)
  have he : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → EffectV.Rel P a.own[i] a.own[i] :=
    fun P hP => (ha.2 _ hmem).2 P (hP.mono (Nat.le_succ _))
  obtain ⟨hs, ho⟩ := runOwn_self T hv hkw (a := { a with own := a.own.eraseIdx i }) ha' he b hb
  have hfr : b.state.fresh = a.state.fresh + 1 := runOwn_fresh T (a := { a with own := a.own.eraseIdx i }) (ha.2 _ hmem).1 hb
  rw [Supp, hfr]
  refine ⟨hs.drop, fun y hy => ?_⟩
  rcases ho y hy with hy | hy
  · exact (ha.2 y (mem_eraseIdx hy)).mono (Nat.le_succ _)
  · exact hy

end Step

end Tazuna.Ir
