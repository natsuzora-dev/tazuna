import Tazuna.Semantics.PairCommute
import Tazuna.Semantics.PendingInv

/-! Valid inputs keep every name of a state below its counter, so every cascade a run starts is one T5 speaks about
(`Supp`). An input is valid when the ids it carries are ones the service made before (counters below its own) or
names from outside (`Input.Valid`): a trace and a scenario can write no others, since a trace names a fresh id only
after the service made it and an unknown name is an outside id. A state keeps its names below its counter
(`StateSupp`): its records and instances relate to themselves under each renaming that keeps those counters, and so
does each pending request on its own. A multiset relation does not give that last part back (two requests may relate
to each other and not to themselves), so it is carried request by request: a step adds requests only from effects
that relate to themselves (`start_pend`). -/

namespace Tazuna.Ir

namespace Step

variable (T : List TypeDecl) {v : ServiceV}

/-- A pending request whose names are below `n`. -/
def PendingAt (n : Nat) (p : Pending v.event) : Prop :=
  ∀ P : PBij, P.Fixes n → Sender.Rel P p.sender p.sender ∧ RequestV.Rel P p.request p.request

theorem PendingAt.mono {n m : Nat} {p : Pending v.event} (h : PendingAt n p) (hnm : n ≤ m) : PendingAt m p :=
  fun P hP => h P (hP.mono hnm)

/-- Every pending request of the step in progress has its names below `n`. -/
def PendAt (n : Nat) (a : Acc v) : Prop := ∀ p ∈ a.state.pending, PendingAt n p

theorem PendAt.mono {n m : Nat} {a : Acc v} (h : PendAt n a) (hnm : n ≤ m) : PendAt m a :=
  fun p hp => (h p hp).mono hnm

theorem start_pend {n : Nat} : (effs : List (Sender × EffectV v.event)) →
    (∀ x ∈ effs, ∀ P : PBij, P.Fixes n → Started.Rel P x x) → (a : Acc v) → PendAt n a → {b : Acc v} →
    start a effs = .ok b → PendAt n b
  | [], _, a, ha, b, h => by
    simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ha
  | (snd, eff) :: effs, he, a, ha, b, h => by
    simp only [start, List.foldlM_cons] at h
    have he' : ∀ x ∈ effs, ∀ P : PBij, P.Fixes n → Started.Rel P x x := fun x hx => he x (List.mem_cons_of_mem _ hx)
    cases eff with
    | request r =>
      cases ho : r.ownerIn v.declared with
      | none => simp only [ho] at h; cases h
      | some o =>
        simp only [ho, bind, Except.bind] at h
        refine start_pend effs he' _ ?_ h
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ha p hp
        · rw [List.mem_singleton] at hp; subst hp
          intro P hP
          obtain ⟨hs, hr⟩ := he _ List.mem_cons_self P hP
          cases hr with
          | request hr => exact ⟨hs, hr⟩
    | command name c i j caller value onAnswer =>
      simp only [bind, Except.bind] at h
      exact start_pend effs he' { a with own := a.own ++ [.command name c i j caller value onAnswer] } ha h
    | query name c i o caller value onAnswer =>
      simp only [bind, Except.bind] at h
      exact start_pend effs he' { a with own := a.own ++ [.query name c i o caller value onAnswer] } ha h

theorem applyEvents_pend (hv : v.Equivariant) (n : Nat) :
    (evs : List v.event.den0) → (a : Acc v) → SelfAt n a → PendAt n a →
    (∀ ev ∈ evs, ∀ P : PBij, P.Fixes n → Ty.rel0 P v.event ev ev) → ∀ b, applyEvents T a evs = .ok b → PendAt n b
  | [], a, _, hp, _, b, h => by
    simp only [applyEvents, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hp
  | ev :: evs, a, ha, hp, hev, b, h => by
    unfold applyEvents at h
    rw [List.foldlM_cons] at h
    let a2 : Acc v := { a with state := (react T a.state ev).1, events := a.events ++ [ev] }
    cases hs : start a2 (react T a.state ev).2 with
    | error e => simp only [a2] at hs; simp [hs, bind, Except.bind] at h
    | ok a1 =>
      simp only [a2] at hs
      simp only [hs, bind, Except.bind] at h
      have hev1 : ∀ P : PBij, P.Fixes n → Ty.rel0 P v.event ev ev := hev ev List.mem_cons_self
      have h1 : applyEvents T a [ev] = .ok a1 := by
        unfold applyEvents
        simp only [List.foldlM_cons, List.foldlM_nil, hs, bind, Except.bind]
        rfl
      have hsa := (applyEvents_self T hv n [ev] a ha (by simpa using hev1) a1 h1).1
      have hst := react_self T hv (s := a.state) (fun P hP => by
        exact ⟨(ha P hP).1.1, (ha P hP).1.2.1⟩) hev1
      have hp1 : PendAt n a1 := start_pend _ hst a2 (fun p hp' => hp p (by simpa [a2, react] using hp')) hs
      exact applyEvents_pend hv n evs a1 hsa hp1 (fun e he => hev e (List.mem_cons_of_mem _ he)) b h

theorem runCommand_pend (hv : v.Equivariant) {a : Acc v}
    (ha : SelfAt (a.state.fresh + 1) a) (hp : PendAt (a.state.fresh + 1) a) {x : CommandV v.records v.event v.caller}
    (hx : x ∈ v.commands) {c : v.caller.den0} (hc : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.caller c c)
    {i : x.input.den0} (hi : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P x.input i i)
    {f : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))}
    (hf : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Fun.Rel P f f) :
    ∀ b, runCommand T a x c i f = .ok b → PendAt (a.state.fresh + 1) b := by
  intro b h
  have hdec : ∀ P : PBij, P.Fixes (a.state.fresh + 1) →
      Ty.rel0 P (Ty.result (.list v.event) x.rejection) (x.decide.fn (ctx a.state a.state.records c i, ()))
        (x.decide.fn (ctx a.state a.state.records c i, ())) := fun P hP => by
    have hA := ha P hP
    exact ((hv.self P).commands x hx).decide _ _
      ⟨⟨hA.1.1, hi P hP, hc P hP, rfl, hP _ (Nat.lt_succ_self _), trivial⟩, trivial⟩
  have ha1 : SelfAt (a.state.fresh + 1) { a with state := { a.state with fresh := a.state.fresh + 1 } } := ha.fresh
  have hp1 : PendAt (a.state.fresh + 1) { a with state := { a.state with fresh := a.state.fresh + 1 } } := hp
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
        have hevs : ∀ ev ∈ (show List v.event.den0 from evs), ∀ P : PBij, P.Fixes (a.state.fresh + 1) →
            Ty.rel0 P v.event ev ev :=
          fun ev hev P hP => forall2_self (hdec P hP).1 ev hev
        have hs3 := (applyEvents_self T hv _ evs _ ha1 hevs a3 h3).1
        have hp3 := applyEvents_pend T hv _ evs _ ha1 hp1 hevs a3 h3
        split at h
        · cases h
        · next r heq =>
          split at heq
          · cases heq
          cases heq
          simp only at h
          have hans : ∀ ev ∈ (show List v.event.den0 from f.fn (okNil, ())), ∀ P : PBij,
              P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.event ev ev :=
            fun ev hev P hP => forall2_self (hf P hP (okNil, ()) (okNil, ()) ⟨okNil_rel, trivial⟩) ev hev
          exact applyEvents_pend T hv _ _ _ hs3 hp3 hans b h
    | .inr (.inl (j, ())), hdec =>
      simp only [bind, Except.bind] at h
      have hans : ∀ ev ∈ (show List v.event.den0 from f.fn (.inr (.inl (j, ())), ())), ∀ P : PBij,
          P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.event ev ev :=
        fun ev hev P hP => by
          obtain ⟨hj, -⟩ := hdec P hP
          exact forall2_self (hf P hP (.inr (.inl (j, ())), ()) (.inr (.inl (j, ())), ()) ⟨⟨hj, trivial⟩, trivial⟩) ev hev
      exact applyEvents_pend T hv _ _ _ ha1 hp1 hans b h

theorem runQuery_pend (hv : v.Equivariant) {a : Acc v}
    (ha : SelfAt (a.state.fresh + 1) a) (hp : PendAt (a.state.fresh + 1) a) {x : QueryV v.records v.caller}
    (hx : x ∈ v.queries) {c : v.caller.den0} (hc : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.caller c c)
    {i : x.input.den0} (hi : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P x.input i i)
    {f : Fun (Ty.fn [x.output] (.list v.event))} (hf : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Fun.Rel P f f) :
    ∀ b, runQuery T a x c i f = .ok b → PendAt (a.state.fresh + 1) b := by
  intro b h
  unfold runQuery execQuery at h
  cases had : admit x.callers x.accepts c i with
  | cons r rs => simp [had] at h
  | nil =>
    simp only [had] at h
    have hans : ∀ ev ∈ (show List v.event.den0 from f.fn (x.resolve.fn (queryCtx a.state a.state.records c i, ()), ())),
        ∀ P : PBij, P.Fixes (a.state.fresh + 1) → Ty.rel0 P v.event ev ev := fun ev hev P hP => by
      have hA := ha P hP
      exact forall2_self (hf P hP (x.resolve.fn (queryCtx a.state a.state.records c i, ()), ())
        (x.resolve.fn (queryCtx a.state a.state.records c i, ()), ()) ⟨((hv.self P).queries x hx).resolve _ _
        ⟨⟨hA.1.1, hi P hP, hc P hP, rfl, trivial⟩, trivial⟩, trivial⟩) ev hev
    exact applyEvents_pend T hv _ _ { a with state := { a.state with fresh := a.state.fresh + 1 } } ha.fresh hp hans
      b h

theorem runOwn_pend (hv : v.Equivariant) {a : Acc v}
    (ha : SelfAt (a.state.fresh + 1) a) (hp : PendAt (a.state.fresh + 1) a) {e : EffectV v.event}
    (he : ∀ P : PBij, P.Fixes (a.state.fresh + 1) → EffectV.Rel P e e) :
    ∀ b, runOwn T a e = .ok b → PendAt (a.state.fresh + 1) b := by
  intro b h
  cases e with
  | request => cases h; exact hp
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
        exact runCommand_pend T hv ha hp hmem (fun P hP => (EffectV.rel_command_inv (he P hP)).1)
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
        exact runQuery_pend T hv ha hp hmem (fun P hP => (EffectV.rel_query_inv (he P hP)).1)
          (fun P hP => (EffectV.rel_query_inv (he P hP)).2.1) (fun P hP => (EffectV.rel_query_inv (he P hP)).2.2) b h

/-- The own cascade keeps every name below the counter, pending requests one by one included. -/
theorem settle_supp (hv : v.Equivariant) :
    (fuel : Nat) → (a : Acc v) → Supp a → PendAt a.state.fresh a → ∀ b, settle T fuel a = .ok b →
      Supp b ∧ PendAt b.state.fresh b
  | fuel, a, ha, hp, b, h => by
    unfold settle at h
    match hown : a.own, fuel, h with
    | [], _, h => cases h; exact ⟨ha, hp⟩
    | _ :: _, 0, h => cases h
    | e :: rest, f + 1, h =>
      simp only [bind, Except.bind] at h
      cases h1 : runOwn T { a with own := rest } e with
      | error _ => rw [h1] at h; cases h
      | ok a1 =>
        rw [h1] at h
        have hi : 0 < a.own.length := by rw [hown]; simp
        have hpick : (ownSys T v).pick a 0 = .ok a1 := by
          simp only [ownSys, hown, List.getElem?_cons_zero, List.eraseIdx_cons_zero]; exact h1
        have hs1 := ownSys_preserved T hv a 0 a1 ha hi hpick
        have hmem : e ∈ a.own := by rw [hown]; exact List.mem_cons_self
        have ha' : SelfAt (a.state.fresh + 1) { a with own := rest } :=
          (SelfAt.own (a := a) ha.1 fun x hx => ha.2 x (by rw [hown]; exact List.mem_cons_of_mem _ hx)).mono
            (Nat.le_succ _)
        have hp1 := runOwn_pend T hv (a := { a with own := rest }) ha' (hp.mono (Nat.le_succ _))
          (fun P hP => (ha.2 _ hmem).2 P (hP.mono (Nat.le_succ _))) a1 h1
        have hfr : a1.state.fresh = a.state.fresh + 1 :=
          runOwn_fresh T (a := { a with own := rest }) (ha.2 _ hmem).1 h1
        rw [← hfr] at hp1
        exact settle_supp hv f a1 hs1 hp1 b h

/-- A state whose names are below its counter: its records and instances relate to themselves under each renaming
that keeps the counters below it, and so does each pending request on its own. -/
structure StateSupp (s : State v) : Prop where
  data : ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P v.records s.records s.records ∧ Machines.Rel P s.machines s.machines
  pending : ∀ p ∈ s.pending, PendingAt s.fresh p

theorem StateSupp.selfAt {s : State v} (h : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId) :
    SelfAt s.fresh ({ state := s } : Acc v) := fun P hP =>
  ⟨⟨(h.data P hP).1, (h.data P hP).2,
    Multi.of_forall2 (forall2_refl_of fun p hp => ⟨rfl, (h.pending p hp P hP).1, rfl, (h.pending p hp P hP).2⟩),
    rfl, hb, hb⟩, Multi.nil, Multi.nil, nofun, nofun, Multi.nil⟩

theorem StateSupp.of_supp {a : Acc v} (h : Supp a) (hp : PendAt a.state.fresh a) : StateSupp a.state :=
  ⟨fun P hP => ⟨(h.1 P hP).1.1, (h.1 P hP).1.2.1⟩, hp⟩

/-- The same records and instances, a subset of the pending requests, and a counter no lower. -/
theorem StateSupp.sub {s s' : State v} (h : StateSupp s) (hr : s'.records = s.records)
    (hm : s'.machines = s.machines) (hp : ∀ p ∈ s'.pending, p ∈ s.pending) (hf : s.fresh ≤ s'.fresh) :
    StateSupp s' :=
  ⟨fun P hP => by rw [hr, hm]; exact h.data P (hP.mono hf), fun p hp' => (h.pending p (hp p hp')).mono hf⟩

/-- Every id an input carries is one the service made before (a counter below its own) or a name from outside. A
query writes nothing, so it asks nothing. -/
def _root_.Tazuna.Ir.Input.Valid (s : State v) : Input v → Prop
  | .command i caller input => ∀ P : PBij, P.Fixes s.fresh →
      Ty.rel0 P v.caller caller caller ∧ Ty.rel0 P (v.commands.get i).input input input
  | .query .. => True
  | .answer _ ⟨t, value⟩ => ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P t value value
  | .event i value => ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P (v.subscribes.get i).event value value
  | .clock _ => True

/-- What a run of internal steps from `a` starts at, read as `Supp`: the step in progress whose names are below its
counter, with every waiting own effect's. -/
theorem supp_of {n : Nat} {a : Acc v} (hs : SelfAt n a) (ho : ∀ y ∈ a.own, OwnAt n y) (hf : a.state.fresh = n) :
    Supp a := by
  subst hf; exact ⟨hs.drop, ho⟩

theorem RequestV.Rel.onAnswer_self {R : PBij} {e : Ty} {x : RequestV e} (h : RequestV.Rel R x x) :
    Fun.Rel R x.onAnswer x.onAnswer := by
  obtain ⟨name, input, output, rejection, value, holds, onAnswer⟩ := x
  cases h; assumption

/-- An accepted command's step in progress, before its cascade, has its names below its counter. -/
theorem command_begin (hv : v.Equivariant) {s : State v} (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId)
    {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands) {c : v.caller.den0} {i : x.input.den0}
    (hc : ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P v.caller c c) (hi : ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P x.input i i)
    {a : Acc v} (h : execCommand T { state := s } x c i = .ok (.accepted a)) : Supp a ∧ PendAt a.state.fresh a := by
  have ha0 := hs.selfAt hb
  have hdec : ∀ P : PBij, P.Fixes (s.fresh + 1) →
      Ty.rel0 P (Ty.result (.list v.event) x.rejection) (x.decide.fn (ctx s s.records c i, ()))
        (x.decide.fn (ctx s s.records c i, ())) := fun P hP => by
    have hA := ha0 P (hP.mono (Nat.le_succ _))
    exact ((hv.self P).commands x hx).decide _ _
      ⟨⟨hA.1.1, hi P (hP.mono (Nat.le_succ _)), hc P (hP.mono (Nat.le_succ _)), rfl, hP _ (Nat.lt_succ_self _),
        trivial⟩, trivial⟩
  have ha1 : SelfAt (s.fresh + 1) ({ state := { s with fresh := s.fresh + 1 } } : Acc v) :=
    (ha0.mono (Nat.le_succ _)).fresh
  have hp1 : PendAt (s.fresh + 1) ({ state := { s with fresh := s.fresh + 1 } } : Acc v) :=
    fun p hp => (hs.pending p hp).mono (Nat.le_succ _)
  unfold execCommand at h
  cases had : admit x.callers x.accepts c i with
  | cons r rs => simp [had] at h
  | nil =>
    simp only [had] at h
    revert hdec h
    generalize x.decide.fn (ctx s s.records c i, ()) = d
    intro hdec h
    match d, hdec with
    | .inl (evs, ()), hdec =>
      simp only [bind, Except.bind] at h
      cases h3 : applyEvents T ({ state := { s with fresh := s.fresh + 1 } } : Acc v) evs with
      | error e => simp [h3] at h
      | ok a3 =>
        simp only [h3] at h
        split at h
        · cases h
        · cases h
          have hevs : ∀ ev ∈ (show List v.event.den0 from evs), ∀ P : PBij, P.Fixes (s.fresh + 1) →
              Ty.rel0 P v.event ev ev :=
            fun ev hev P hP => forall2_self (hdec P hP).1 ev hev
          obtain ⟨hs3, ho3⟩ := applyEvents_self T hv _ evs _ ha1 hevs a h3
          have hfr : a.state.fresh = s.fresh + 1 := applyEvents_fresh T _ _ h3
          refine ⟨supp_of hs3 (fun y hy => (ho3 y hy).resolve_left nofun) hfr, ?_⟩
          rw [hfr]; exact applyEvents_pend T hv _ evs _ ha1 hp1 hevs a h3
    | .inr (.inl (j, ())), _ => cases h

/-- An answer's step in progress, before its cascade, has its names below its counter. -/
theorem answer_begin (hv : v.Equivariant) {s : State v} (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId)
    {p : Pending v.event} (hp : p ∈ s.pending) (to : Nat) {t : Ty} {value : t.den0}
    (hval : ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P t value value)
    (h : t = answerTy p.request.output p.request.rejection) {a : Acc v}
    (happ : applyEvents T { state := { s with pending := s.pending.filter (·.id != to) } }
      (p.request.onAnswer.fn (h ▸ value, ())) = .ok a) : Supp a ∧ PendAt a.state.fresh a := by
  subst h
  let s' : State v := { s with pending := s.pending.filter (·.id != to) }
  have hs' : StateSupp s' := hs.sub rfl rfl (fun q hq => (List.mem_filter.1 hq).1) (Nat.le_refl _)
  have ha0 : SelfAt s.fresh ({ state := s' } : Acc v) :=
    hs'.selfAt fun q hq => hb q (List.mem_filter.1 hq).1
  have hevs : ∀ ev ∈ (show List v.event.den0 from p.request.onAnswer.fn (value, ())), ∀ P : PBij, P.Fixes s.fresh →
      Ty.rel0 P v.event ev ev := fun ev hev P hP =>
    forall2_self (RequestV.Rel.onAnswer_self (hs.pending p hp P hP).2 (value, ()) (value, ()) ⟨hval P hP, trivial⟩) ev hev
  obtain ⟨hs3, ho3⟩ := applyEvents_self T hv _ _ _ ha0 hevs a happ
  have hfr : a.state.fresh = s.fresh := applyEvents_fresh T _ _ happ
  refine ⟨supp_of hs3 (fun y hy => (ho3 y hy).resolve_left nofun) hfr, ?_⟩
  rw [hfr]; exact applyEvents_pend T hv _ _ _ ha0 hs'.pending hevs a happ

/-- An event's step in progress, before its cascade, has its names below its counter. -/
theorem event_begin (hv : v.Equivariant) {s : State v} (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId)
    (i : Fin v.subscribes.length) {value : (v.subscribes.get i).event.den0}
    (hval : ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P (v.subscribes.get i).event value value) {a : Acc v}
    (happ : applyEvents T { state := s } [(v.subscribes.get i).wrap.fn (value, ())] = .ok a) :
    Supp a ∧ PendAt a.state.fresh a := by
  have ha0 := hs.selfAt hb
  have hevs : ∀ ev ∈ [(v.subscribes.get i).wrap.fn (value, ())], ∀ P : PBij, P.Fixes s.fresh →
      Ty.rel0 P v.event ev ev := fun ev hev P hP => by
    rw [List.mem_singleton] at hev; subst hev
    exact (hv.self P).subscribes _ (List.get_mem _ _) (value, ()) (value, ()) ⟨hval P hP, trivial⟩
  obtain ⟨hs3, ho3⟩ := applyEvents_self T hv _ _ _ ha0 hevs a happ
  have hfr : a.state.fresh = s.fresh := applyEvents_fresh T _ _ happ
  refine ⟨supp_of hs3 (fun y hy => (ho3 y hy).resolve_left nofun) hfr, ?_⟩
  rw [hfr]; exact applyEvents_pend T hv _ _ _ ha0 hs.pending hevs a happ

section Fire
variable {r e : Ty} {n : Nat}

/-- Instances that relate to themselves one by one, from a multiset relation under every renaming keeping the
counters below `n`: under the renaming that keeps exactly those counters each instance's data relates to something,
so its names are below `n`. -/
theorem insts_self {m : MachineV r e} (hk : m.key.comparable = true) (hst : m.state.comparable = true)
    {l : List (Instance m)} (hl : ∀ P : PBij, P.Fixes n → Insts.Rel P l l) :
    ∀ i ∈ l, ∀ P : PBij, P.Fixes n → Instance.Rel P i i := by
  intro i hi P hP
  obtain ⟨j, -, hk', hs', ht'⟩ := (hl _ (PBij.below_fixes n)).1.mem_left hi
  refine ⟨Ty.self_of_below hP _ hk hk', Ty.self_of_below hP _ hst hs', ?_⟩
  revert ht'
  cases i.timer <;> cases j.timer <;> intro ht'
  · exact .none
  · cases ht'
  · cases ht'
  · obtain ⟨-, h⟩ := Option.rel_some_some.1 ht'  
    exact .some ⟨rfl, Ty.self_of_below hP _ hst h⟩

theorem insts_rel {m : MachineV r e} {l : List (Instance m)} (h : ∀ i ∈ l, ∀ P : PBij, P.Fixes n → Instance.Rel P i i)
    (hd : KeysDistinct l) : ∀ P : PBij, P.Fixes n → Insts.Rel P l l :=
  fun P hP => ⟨Multi.of_forall2 (forall2_refl_of fun i hi => h i hi P hP), hd, hd⟩

theorem fired_self {m : MachineV r e} (hm : m.Equi) {records : r.den0}
    (hrec : ∀ P : PBij, P.Fixes n → Ty.rel0 P r records records) (now : Int) {i : Instance m}
    (hi : ∀ P : PBij, P.Fixes n → Instance.Rel P i i) :
    (∀ P : PBij, P.Fixes n → Instance.Rel P (fired m records now i).1 (fired m records now i).1) ∧
      ∀ x ∈ (fired m records now i).2, ∀ P : PBij, P.Fixes n → Started.Rel P x x := by
  unfold fired
  split
  · next d target ht =>
    have htg : ∀ P : PBij, P.Fixes n → Ty.rel0 P m.state target target := fun P hP => by
      have h := (hi P hP).2.2
      rw [ht] at h
      exact (Option.rel_some_some.1 h).2
    exact ⟨fun P hP => (enter_rel hm (hrec P hP) now (hi P hP).1 (htg P hP)).1,
      fun x hx P hP => forall2_self (enter_rel hm (hrec P hP) now (hi P hP).1 (htg P hP)).2 x hx⟩
  · exact ⟨hi, fun _ hx => nomatch hx⟩

theorem fireFirst_self {m : MachineV r e} (hm : m.Equi) {records : r.den0}
    (hrec : ∀ P : PBij, P.Fixes n → Ty.rel0 P r records records) (now d : Int) : (l : List (Instance m)) →
    (∀ i ∈ l, ∀ P : PBij, P.Fixes n → Instance.Rel P i i) →
    (∀ i ∈ (fireFirst m records now d l).1, ∀ P : PBij, P.Fixes n → Instance.Rel P i i) ∧
      (∀ x ∈ (fireFirst m records now d l).2.1, ∀ P : PBij, P.Fixes n → Started.Rel P x x) ∧
      (fireFirst m records now d l).1.map (·.key) = l.map (·.key)
  | [], _ => ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), rfl⟩
  | i :: is, hl => by
    have hi := hl i List.mem_cons_self
    have his : ∀ j ∈ is, ∀ P : PBij, P.Fixes n → Instance.Rel P j j := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    unfold fireFirst
    split
    · have hf := fired_self hm hrec now hi
      refine ⟨fun j hj => ?_, hf.2, by simp [fired_key]⟩
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hf.1
      · exact his j hj
    · have ih := fireFirst_self hm hrec now d is his
      refine ⟨fun j hj => ?_, ih.2.1, by simp [ih.2.2]⟩
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hi
      · exact ih.1 j hj

theorem keysDistinct_of_keys {m : MachineV r e} {l l' : List (Instance m)} (h : l'.map (·.key) = l.map (·.key))
    (hd : KeysDistinct l) : KeysDistinct l' := by
  unfold KeysDistinct at hd ⊢
  have e : l'.Pairwise (fun a b => m.key.deq0 a.key b.key = false) ↔
      (l'.map (·.key)).Pairwise (fun a b => m.key.deq0 a b = false) :=
    (List.pairwise_map (f := fun i : Instance m => i.key) (R := fun a b => m.key.deq0 a b = false)).symm
  rw [e, h, List.pairwise_map]; exact hd

theorem fireMachines_self {records : r.den0} (hrec : ∀ P : PBij, P.Fixes n → Ty.rel0 P r records records)
    (now d : Int) : (done : Bool) → {ms : List (MachineV r e)} → (∀ m ∈ ms, m.Equi ∧ m.state.comparable = true) →
    (l : Machines ms) → (∀ P : PBij, P.Fixes n → Machines.Rel P l l) →
    (∀ P : PBij, P.Fixes n → Machines.Rel P (fireMachines records now d done l).1 (fireMachines records now d done l).1) ∧
      ∀ x ∈ (fireMachines records now d done l).2.1, ∀ P : PBij, P.Fixes n → Started.Rel P x x
  | done, [], _, .nil, _ => ⟨fun _ _ => trivial, fun _ h => by cases done <;> exact nomatch h⟩
  | true, _ :: _, hms, .cons insts rest, hl => by
    have ih := fireMachines_self hrec now d true (fun m h => hms m (List.mem_cons_of_mem _ h)) rest
      (fun P hP => (hl P hP).2)
    exact ⟨fun P hP => ⟨(hl P hP).1, ih.1 P hP⟩, ih.2⟩
  | false, m :: _, hms, .cons insts rest, hl => by
    obtain ⟨hm, hst⟩ := hms m List.mem_cons_self
    have hi := insts_self hm.key hst (fun P hP => (hl P hP).1)
    have hf := fireFirst_self hm hrec now d insts hi
    have hd : KeysDistinct (fireFirst m records now d insts).1 :=
      keysDistinct_of_keys hf.2.2 ((hl _ (PBij.below_fixes n)).1.2.1)
    have ih := fireMachines_self hrec now d (fireFirst m records now d insts).2.2
      (fun m h => hms m (List.mem_cons_of_mem _ h)) rest (fun P hP => (hl P hP).2)
    refine ⟨fun P hP => ⟨insts_rel hf.1 hd P hP, ih.1 P hP⟩, fun x hx P hP => ?_⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact hf.2.1 x hx P hP
    · exact ih.2 x hx P hP

theorem fire_self {v : ServiceV} (hms : ∀ m ∈ v.machines, m.Equi ∧ m.state.comparable = true) :
    (fuel : Nat) → (s : State v) → (∀ P : PBij, P.Fixes n → Ty.rel0 P v.records s.records s.records) →
    (∀ P : PBij, P.Fixes n → Machines.Rel P s.machines s.machines) → ∀ {s' effs}, fire s fuel = some (s', effs) →
    (∀ P : PBij, P.Fixes n → Machines.Rel P s'.machines s'.machines) ∧
      (∀ x ∈ effs, ∀ P : PBij, P.Fixes n → Started.Rel P x x) ∧ s'.records = s.records ∧ s'.pending = s.pending ∧
      s'.fresh = s.fresh ∧ s'.nextId = s.nextId
  | 0, _, _, _, _, _, h => by cases h
  | fuel + 1, s, hrec, hl, s', effs, h => by
    unfold fire at h
    split at h
    · cases h; exact ⟨hl, fun _ h => (nomatch h), rfl, rfl, rfl, rfl⟩
    · next d _ =>
      have hx := fireMachines_self hrec s.now d false hms s.machines hl
      dsimp only at h
      cases h1 : fire { s with machines := (fireMachines s.records s.now d false s.machines).1 } fuel with
      | none => rw [h1] at h; cases h
      | some p =>
        rw [h1] at h
        obtain ⟨s1, es⟩ := p
        cases h
        have ih := fire_self hms fuel { s with machines := (fireMachines s.records s.now d false s.machines).1 } hrec
          hx.1 h1
        refine ⟨ih.1, fun x hx' => ?_, ih.2.2.1, ih.2.2.2.1, ih.2.2.2.2.1, ih.2.2.2.2.2⟩
        rcases List.mem_append.1 hx' with hx' | hx'
        · exact hx.2 x hx'
        · exact ih.2.1 x hx'

end Fire

/-- A clock line's step in progress, before its cascade, has its names below its counter. -/
theorem clock_begin (hv : v.Equivariant) (hst : ∀ m ∈ v.machines, m.state.comparable = true) {s : State v}
    (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId) (time : Int) {fuel : Nat} {s' : State v}
    {effs : List (Sender × EffectV v.event)} (hf : fire { s with now := time } fuel = some (s', effs)) {a : Acc v}
    (h : start { state := s' } effs = .ok a) : Supp a ∧ PendAt a.state.fresh a := by
  obtain ⟨hm', he, hr, hp, hfr, hn⟩ := fire_self (n := s.fresh) (fun m hm => ⟨hv.machines m hm, hst m hm⟩) fuel
    { s with now := time } (fun P hP => (hs.data P hP).1) (fun P hP => (hs.data P hP).2) hf
  have hs' : StateSupp s' := ⟨fun P hP => by
      rw [hfr] at hP
      exact ⟨by rw [hr]; exact (hs.data P hP).1, hm' P hP⟩,
    fun p hp' => by rw [hfr]; exact hs.pending p (by rw [hp] at hp'; exact hp')⟩
  have ha0 := hs'.selfAt (fun p hp' => by rw [hn]; exact hb p (by rw [hp] at hp'; exact hp'))
  have hfa : a.state.fresh = s'.fresh := start_fresh _ _ h
  have hsa : SelfAt s'.fresh a := fun P hP => by
    exact start_self (ha0 P hP) (fun x hx => he x hx P (by rw [hfr] at hP; exact hP)) h
  refine ⟨supp_of hsa (fun y hy => ?_) hfa, ?_⟩
  · rcases start_own_mem _ _ h y hy with hy | ⟨hr', snd, hy⟩
    · exact nomatch hy
    · exact ⟨hr', fun P hP => (he _ hy P (by rw [hfr] at hP; exact hP)).2⟩
  · rw [hfa]
    exact start_pend effs (fun x hx P hP => he x hx P (by rw [hfr] at hP; exact hP)) ({ state := s' } : Acc v)
      hs'.pending h

theorem finish_supp (hv : v.Equivariant) {s0 : State v} (hs0 : StateSupp s0) (x : Except Fault (Acc v))
    (hx : ∀ a, x = .ok a → Supp a ∧ PendAt a.state.fresh a) (o : Outcome) : StateSupp (finish T s0 x o).state := by
  unfold finish
  split
  · exact hs0
  · rename_i b hb
    split
    · exact hs0
    · cases x with
      | error e => cases hb
      | ok a =>
        obtain ⟨ha, hp⟩ := hx a rfl
        obtain ⟨hb1, hb2⟩ := settle_supp T hv _ a ha hp b hb
        exact StateSupp.of_supp hb1 hb2

/-- A step on a valid input keeps the state's names below its counter. -/
theorem step_supp (hv : v.Equivariant) (hst : ∀ m ∈ v.machines, m.state.comparable = true) {s : State v}
    (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId) (x : Input v) (hx : x.Valid s) :
    StateSupp (step T v s x).state := by
  have hfresh : StateSupp ({ s with fresh := s.fresh + 1 } : State v) :=
    hs.sub rfl rfl (fun _ h => h) (Nat.le_succ _)
  cases x with
  | command i caller input =>
    simp only [step]
    split
    · exact hfresh
    · exact hfresh
    · exact hfresh
    · rename_i a ha
      exact finish_supp T hv hfresh _ (fun a' h => by
        cases h
        exact command_begin T hv hs hb (List.get_mem _ _) (fun P hP => (hx P hP).1) (fun P hP => (hx P hP).2) ha) _
  | query i caller input =>
    simp only [step]
    split <;> exact hs
  | answer to w =>
    obtain ⟨t, value⟩ := w
    simp only [step]
    split
    · exact hs
    · rename_i p hp
      split
      · exact hs
      · rename_i h _
        split
        · exact hs
        · exact finish_supp T hv hs _ (fun a ha =>
            answer_begin T hv hs hb (List.mem_of_find?_eq_some hp) to hx h ha) _
  | event i value =>
    exact finish_supp T hv hs _ (fun a ha => event_begin T hv hs hb i hx ha) _
  | clock time =>
    simp only [step]
    split
    · exact hs
    · split
      · exact hs
      · rename_i s' effs hr
        exact finish_supp T hv hs _ (fun a ha => clock_begin hv hst hs hb time hr ha) _

/-- Inputs each valid at the state the run has reached when it comes. -/
def ValidRun : State v → List (Input v) → Prop
  | _, [] => True
  | s, x :: xs => x.Valid s ∧ ValidRun (step T v s x).state xs

theorem machines_empty (P : PBij) : (ms : List (MachineV v.records v.event)) →
    Machines.Rel P (PerMachine.ofFn (fun _ => ([] : List (Instance _))) ms : Machines ms)
      (PerMachine.ofFn (fun _ => []) ms)
  | [] => trivial
  | _ :: ms => ⟨⟨Multi.nil, .nil, .nil⟩, machines_empty P ms⟩

theorem init_supp (hv : v.Equivariant) : StateSupp (State.init v) :=
  ⟨fun P _ => ⟨(hv.self P).init, machines_empty P v.machines⟩, fun _ h => nomatch h⟩

/-- Every state a run on valid inputs reaches from a state whose names are below its counter keeps them so. -/
theorem run_supp (hv : v.Equivariant) (hst : ∀ m ∈ v.machines, m.state.comparable = true) {P : List AnySite}
    {E : List AnyEffectSite} (hr : v.Reach P E) : (s : State v) → Inv P s → StateSupp s → (xs : List (Input v)) →
    ValidRun T s xs → StateSupp (run T v s xs).1
  | _, _, hs, [], _ => hs
  | s, hi, hs, x :: xs, ⟨hx, hxs⟩ =>
    run_supp hv hst hr _ (step_inv T hr s hi x) (step_supp T hv hst hs hi.below x hx) xs hxs

/-- Every cascade a step on a valid input starts, from a state whose names are below its counter, is one T5 speaks
about, and its pending requests' names are below its counter. -/
theorem begins_supp (hv : v.Equivariant) (hst : ∀ m ∈ v.machines, m.state.comparable = true) {s : State v}
    (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId) {x : Input v} (hx : x.Valid s) {a : Acc v}
    (h : Begins T s x a) : Supp a ∧ PendAt a.state.fresh a := by
  cases h with
  | command i caller input a h =>
    exact command_begin T hv hs hb (List.get_mem _ _) (fun P hP => (hx P hP).1) (fun P hP => (hx P hP).2) h
  | answer to value p h a hp _ happ => exact answer_begin T hv hs hb (List.mem_of_find?_eq_some hp) to hx h happ
  | event i value a h => exact event_begin T hv hs hb i hx h
  | clock time s' effs a _ hf h => exact clock_begin hv hst hs hb time hf h

end Step

end Tazuna.Ir
