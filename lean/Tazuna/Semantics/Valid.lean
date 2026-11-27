import Tazuna.Semantics.PairCommute
import Tazuna.Semantics.PendingInv
import Tazuna.Trace.Wire

/-! Valid inputs keep every name of a state below its counter, so every cascade a run starts is one T5 speaks about
(`Supp`). What a line's `assumes` states (`Assumption.text`) is that ids the service made are used only after they
appeared on an out line, and outside ids are unrestricted: guarding against guessed ids is the implementation's job.
`ShownRun` is that sentence: it follows the ids each step's out lines show (`Result.shownIds`), and an input may carry
an id the service made only once one of them showed it (`Input.Shown`). It implies `ValidRun` (an id counts once its
counter is below the state's, shown or not), which the inductive proofs read, so every verdict over all runs on
valid inputs holds of the runs the sentence allows. A state keeps its names below its counter (`StateSupp`): its
records and instances relate to themselves under each renaming that keeps those counters, and so does each pending
request on its own, as `Supp` reads a step in progress (`Acc.Self`). -/

namespace Tazuna.Ir

namespace Step

variable (T : List TypeDecl) {v : ServiceV}

/-- The own cascade keeps every name below the counter. -/
theorem settle_supp (hv : v.Equivariant) :
    (fuel : Nat) → (a : Acc v) → Supp a → ∀ b, settle T fuel a = .ok b → Supp b
  | fuel, a, ha, b, h => by
    unfold settle at h
    match hown : a.own, fuel, h with
    | [], _, h => cases h; exact ha
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
        exact settle_supp hv f a1 (ownSys_preserved T hv a 0 a1 ha hi hpick) b h

/-- The state's records and instances related to themselves by `P`, and each pending request on its own. -/
def State.Self (P : PBij) (s : State v) : Prop :=
  Ty.rel0 P v.records s.records s.records ∧ Machines.Rel P s.machines s.machines ∧
    ∀ p ∈ s.pending, Pending.Rel ⟨P, PBij.refl⟩ p p

/-- A state whose names are below its counter. -/
abbrev StateSupp (s : State v) : Prop := Below State.Self s.fresh s

theorem State.Self.acc {P : PBij} {s : State v} (h : State.Self P s) (hb : ∀ p ∈ s.pending, p.id < s.nextId) :
    Acc.Self P ({ state := s } : Acc v) :=
  ⟨⟨⟨h.1, h.2.1, Multi.of_forall2 (forall2_refl_of h.2.2), rfl, hb, hb⟩, Multi.nil, Multi.nil, nofun, nofun, Multi.nil⟩,
    h.2.2, nofun⟩

theorem Acc.Self.state {P : PBij} {a : Acc v} (h : Acc.Self P a) : State.Self P a.state :=
  ⟨h.1.1.1, h.1.1.2.1, h.2.1⟩

/-- The same records and instances, a subset of the pending requests, and a counter no lower. -/
theorem StateSupp.sub {s s' : State v} (h : StateSupp s) (hr : s'.records = s.records)
    (hm : s'.machines = s.machines) (hp : ∀ p ∈ s'.pending, p ∈ s.pending) (hf : s.fresh ≤ s'.fresh) :
    StateSupp s' := fun P hP => by
  obtain ⟨h1, h2, h3⟩ := h P (hP.mono hf)
  exact ⟨hr ▸ h1, hm ▸ h2, fun p hp' => h3 p (hp p hp')⟩

/-- Every id an input carries is one the service made before (a counter below its own), shown on an out line or not, or
a name from outside. A query writes nothing, so it asks nothing. -/
def _root_.Tazuna.Ir.Input.Valid (s : State v) : Input v → Prop
  | .command i caller input => ∀ P : PBij, P.Fixes s.fresh →
      Ty.rel0 P v.caller caller caller ∧ Ty.rel0 P (v.commands.get i).input input input
  | .query .. => True
  | .answer _ ⟨t, value⟩ => ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P t value value
  | .event i value => ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P (v.subscribes.get i).event value value
  | .clock _ => True

theorem RequestV.Rel.onAnswer_self {R : PBij} {e : Ty} {x : RequestV e} (h : RequestV.Rel R x x) :
    Fun.Rel R x.onAnswer x.onAnswer := by
  obtain ⟨name, input, output, rejection, value, holds, onAnswer⟩ := x
  cases h; assumption

/-- An accepted command's step in progress, before its cascade, has its names below its counter. -/
theorem command_begin (hv : v.Equivariant) {s : State v} (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId)
    {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands) {c : (Ty.origin v.caller).den0} {i : x.input.den0}
    (hc : ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P (Ty.origin v.caller) c c) (hi : ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P x.input i i)
    {a : Acc v} (h : execCommand T { state := s } x c i = .ok (.accepted a)) : Supp a := by
  have ha0 : Below Acc.Self s.fresh ({ state := s } : Acc v) := fun P hP => (hs P hP).acc hb
  have hdec : ∀ P : PBij, P.Fixes (s.fresh + 1) →
      Ty.rel0 P (Ty.result (.list v.event) x.rejection) (x.decide.fn (ctx s s.records c i, ()))
        (x.decide.fn (ctx s s.records c i, ())) := fun P hP => by
    have hA := ha0 P (hP.mono (Nat.le_succ _))
    exact ((hv.self P).commands x hx).decide _ _
      ⟨⟨hA.1.1.1, hi P (hP.mono (Nat.le_succ _)), hc P (hP.mono (Nat.le_succ _)), rfl, hP _ (Nat.lt_succ_self _),
        trivial⟩, trivial⟩
  have ha1 : Below Acc.Self (s.fresh + 1) ({ state := { s with fresh := s.fresh + 1 } } : Acc v) :=
    below_fresh (ha0.mono (Nat.le_succ _))
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
          have hfr : a.state.fresh = s.fresh + 1 := applyEvents_fresh T _ _ h3
          rw [Supp, hfr]; exact applyEvents_self T hv _ evs _ ha1 hevs a h3
    | .inr (.inl (j, ())), _ => cases h

/-- An answer's step in progress, before its cascade, has its names below its counter. -/
theorem answer_begin (hv : v.Equivariant) {s : State v} (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId)
    {p : Pending v.event} (hp : p ∈ s.pending) (to : Nat) {t : Ty} {value : t.den0}
    (hval : ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P t value value)
    (h : t = answerTy p.request.output p.request.rejection) {a : Acc v}
    (happ : applyEvents T { state := { s with pending := s.pending.filter (·.id != to) } }
      (p.request.onAnswer.fn (h ▸ value, ())) = .ok a) : Supp a := by
  subst h
  let s' : State v := { s with pending := s.pending.filter (·.id != to) }
  have hs' : StateSupp s' := hs.sub rfl rfl (fun q hq => (List.mem_filter.1 hq).1) (Nat.le_refl _)
  have ha0 : Below Acc.Self s.fresh ({ state := s' } : Acc v) := fun P hP =>
    (hs' P hP).acc fun q hq => hb q (List.mem_filter.1 hq).1
  have hevs : ∀ ev ∈ (show List v.event.den0 from p.request.onAnswer.fn (value, ())), ∀ P : PBij, P.Fixes s.fresh →
      Ty.rel0 P v.event ev ev := fun ev hev P hP =>
    forall2_self (RequestV.Rel.onAnswer_self ((hs P hP).2.2 p hp).2.2.2 (value, ()) (value, ()) ⟨hval P hP, trivial⟩)
      ev hev
  have hfr : a.state.fresh = s.fresh := applyEvents_fresh T _ _ happ
  rw [Supp, hfr]; exact applyEvents_self T hv _ _ _ ha0 hevs a happ

/-- An event's step in progress, before its cascade, has its names below its counter. -/
theorem event_begin (hv : v.Equivariant) {s : State v} (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId)
    (i : Fin v.subscribes.length) {value : (v.subscribes.get i).event.den0}
    (hval : ∀ P : PBij, P.Fixes s.fresh → Ty.rel0 P (v.subscribes.get i).event value value) {a : Acc v}
    (happ : applyEvents T { state := s } [(v.subscribes.get i).wrap.fn (value, ())] = .ok a) :
    Supp a := by
  have ha0 : Below Acc.Self s.fresh ({ state := s } : Acc v) := fun P hP => (hs P hP).acc hb
  have hevs : ∀ ev ∈ [(v.subscribes.get i).wrap.fn (value, ())], ∀ P : PBij, P.Fixes s.fresh →
      Ty.rel0 P v.event ev ev := fun ev hev P hP => by
    rw [List.mem_singleton] at hev; subst hev
    exact (hv.self P).subscribes _ (List.get_mem _ _) (value, ()) (value, ()) ⟨hval P hP, trivial⟩
  have hfr : a.state.fresh = s.fresh := applyEvents_fresh T _ _ happ
  rw [Supp, hfr]; exact applyEvents_self T hv _ _ _ ha0 hevs a happ

section Fire
variable {r e : Ty} {n : Nat}

/-- Instances that relate to themselves one by one, from a multiset relation under every renaming keeping the
counters below `n`: under the renaming that keeps exactly those counters each instance's data relates to something,
so its names are below `n`. -/
theorem insts_self {m : MachineV r e} (hk : m.key.comparable = true) (hst : m.state.comparable = true)
    {l : List (Instance m)} (hl : ∀ P : PBij, P.Fixes n → Insts.Rel P l l) :
    ∀ i ∈ l, ∀ P : PBij, P.Fixes n → Instance.Rel P i i := by
  intro i hi P hP
  obtain ⟨j, -, hk', hs'⟩ := (hl _ (PBij.below_fixes n)).1.mem_left hi
  exact ⟨Ty.self_of_below hP _ hk hk', Ty.self_of_below hP _ hst hs'⟩

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
      have h := timerAt_rel hm (hrec P hP) (hi P hP).1 (hi P hP).2
      simp only [timerOf] at ht
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
theorem clock_begin (hv : v.Equivariant) {s : State v}
    (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId) (time : Int) {fuel : Nat} {s' : State v}
    {effs : List (Sender × EffectV v.event)} (hf : fire { s with now := time } fuel = some (s', effs)) {a : Acc v}
    (h : start { state := s' } effs = .ok a) : Supp a := by
  obtain ⟨hm', he, hr, hp, hfr, hn⟩ := fire_self (n := s.fresh) (fun m hm => ⟨hv.machines m hm, hv.states m hm⟩) fuel
    { s with now := time } (fun P hP => (hs P hP).1) (fun P hP => (hs P hP).2.1) hf
  have hfa : a.state.fresh = s'.fresh := start_fresh _ _ h
  rw [Supp, hfa]
  intro P hP
  rw [hfr] at hP
  refine start_self (State.Self.acc ⟨by rw [hr]; exact (hs P hP).1, hm' P (hfr ▸ hP), fun p hp' => (hs P hP).2.2 p
    (by rw [hp] at hp'; exact hp')⟩ fun p hp' => by rw [hn]; exact hb p (by rw [hp] at hp'; exact hp'))
    (fun x hx => he x hx P hP) h

theorem finish_supp (hv : v.Equivariant) {s0 : State v} (hs0 : StateSupp s0) (x : Except Fault (Acc v))
    (hx : ∀ a, x = .ok a → Supp a) (o : Outcome) : StateSupp (finish T s0 x o).state := by
  unfold finish
  split
  · exact hs0
  · rename_i b hb
    split
    · exact hs0
    · cases x with
      | error e => cases hb
      | ok a =>
        exact fun P hP => (settle_supp T hv _ a (hx a rfl) b hb P hP).state

/-- A step on a valid input keeps the state's names below its counter. -/
theorem step_supp (hv : v.Equivariant) {s : State v}
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
        exact command_begin T hv hs hb (List.get_mem _ _) (fun P hP => rel0_outside (hx P hP).1) (fun P hP => (hx P hP).2) ha) _
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
        exact finish_supp T hv hs _ (fun a ha => clock_begin hv hs hb time hr ha) _

/-- `p` at every step of the run from `s`: at the state the run has reached when each input comes. -/
def EachStep (p : State v → Input v → Prop) : State v → List (Input v) → Prop
  | _, [] => True
  | s, x :: xs => p s x ∧ EachStep p (step T v s x).state xs

instance EachStep.decidable {p : State v → Input v → Prop} [hp : ∀ s x, Decidable (p s x)] :
    (s : State v) → (xs : List (Input v)) → Decidable (EachStep T p s xs)
  | _, [] => .isTrue trivial
  | s, x :: xs => @instDecidableAnd _ _ (hp s x) (EachStep.decidable _ xs)

/-- Inputs each valid at the state the run has reached when it comes. -/
abbrev ValidRun : State v → List (Input v) → Prop := EachStep T fun s x => x.Valid s

/-- Whether a clock line at `time` passes no timer that waits: every instance's timer is due at `time` or later. -/
def timely (s : State v) (time : Int) : Bool :=
  s.machines.toSigma.all fun ⟨_, insts⟩ => insts.all fun i => match timerOf s.records i with
    | some (d, _) => decide (time ≤ d)
    | none => true

/-- Whether the input is timely at `s`: a clock line passes no timer that waits; other inputs ask nothing. -/
def timelyAt (s : State v) : Input v → Bool
  | .clock time => timely s time
  | _ => true

/-- Clock lines each timely at the state the run has reached when they come. Without it the environment breaks every
timed response by moving the clock past the timer that would answer in time, since a timer fired late carries the late
time (timed automata block time from passing a deadline in the same way). -/
abbrev TimelyRun : State v → List (Input v) → Prop := EachStep T fun s x => timelyAt s x = true

/-- No step of the run faults. A fault is a spec bug that prove reports on its own; a search over runs leaves runs
through one out. -/
abbrev NoFaultRun : State v → List (Input v) → Prop := EachStep T fun s x => ∀ f, (step T v s x).outcome ≠ .fault f

/-- The ids an input carries, in the order its in line writes them: a request's caller and input, an answer's value,
an event's value. -/
def _root_.Tazuna.Ir.Input.ids : Input v → List IdV
  | .command i caller input => Trace.idsOf T v.caller caller ++ Trace.idsOf T (v.commands.get i).input input
  | .query i caller input => Trace.idsOf T v.caller caller ++ Trace.idsOf T (v.queries.get i).input input
  | .answer _ ⟨t, value⟩ => Trace.idsOf T t value
  | .event i value => Trace.idsOf T (v.subscribes.get i).event value
  | .clock _ => []

/-- The ids a step's out lines show: its answer's output or rejection, its events, the inputs of the requests it
sends. -/
def _root_.Tazuna.Ir.Result.shownIds (r : Result v) : List IdV :=
  (match r.outcome with
    | .answered ⟨t, x⟩ | .rejected ⟨t, x⟩ => Trace.idsOf T t x
    | _ => []) ++ r.events.flatMap (Trace.idsOf T v.event) ++ r.out.flatMap fun o => Trace.idsOf T o.input.1 o.input.2

/-- Whether an id is from outside the service, or one of `seen`. -/
def _root_.Tazuna.Ir.IdV.Known (seen : List IdV) : IdV → Prop
  | .named _ => True
  | i => i ∈ seen

/-- The input carries only ids from outside and ids among `seen`, and its names are below the counter (`Input.Valid`,
which a wire value's ids already give when every id in `seen` is). -/
def _root_.Tazuna.Ir.Input.Shown (seen : List IdV) (s : State v) (x : Input v) : Prop :=
  x.Valid s ∧ ∀ i ∈ x.ids T, i.Known seen

/-- Inputs each carrying only ids from outside and ids an earlier step's out lines showed, after `seen`. -/
def ShownRun : List IdV → State v → List (Input v) → Prop
  | _, _, [] => True
  | seen, s, x :: xs => x.Shown T seen s ∧ ShownRun (seen ++ (step T v s x).shownIds T) (step T v s x).state xs

theorem ShownRun.valid : {seen : List IdV} → {s : State v} → {xs : List (Input v)} → ShownRun T seen s xs →
    ValidRun T s xs
  | _, _, [], _ => trivial
  | _, _, _ :: _, ⟨hx, hxs⟩ => ⟨hx.1, ShownRun.valid hxs⟩

/-- An assumption a proof rests on beyond the spec's invariants: what it says of a run, and the words a line's
`assumes` names it by, kept together so the two cannot part. -/
inductive Assumption where
  /-- Ids the service made are used only after they appeared on an out line; outside ids are unrestricted
  (`ShownRun` from the initial state, which implies `ValidRun`, the weaker condition the inductive proofs read). -/
  | validInputs
  /-- No clock line of a run moves time past a timer that waits (`TimelyRun`). -/
  | timelyClock
  /-- No step of a run faults (`NoFaultRun`). -/
  | noFault

def Assumption.text : Assumption → String
  | .validInputs => "ids the service made are used only after they appeared on an out line"
  | .timelyClock => "no clock line moves time past a timer that waits"
  | .noFault => "no step of the run faults"

/-- What the assumption says of the run from `s` on `xs`. -/
def Assumption.Holds : Assumption → State v → List (Input v) → Prop
  | .validInputs => ShownRun T []
  | .timelyClock => TimelyRun T
  | .noFault => NoFaultRun T

/-- What a search over the runs from the initial state assumes of them: generate's unreached targets rest on it. -/
def Assumption.ofRuns : List Assumption := [.validInputs, .noFault]

/-- What a search for a response's violation assumes of the runs: a response within its bounds rests on it, and a
violating run satisfies it. -/
def Assumption.ofResponses : List Assumption := Assumption.ofRuns ++ [.timelyClock]

theorem machines_empty (P : PBij) : (ms : List (MachineV v.records v.event)) →
    Machines.Rel P (PerMachine.ofFn (fun _ => ([] : List (Instance _))) ms : Machines ms)
      (PerMachine.ofFn (fun _ => []) ms)
  | [] => trivial
  | _ :: ms => ⟨⟨Multi.nil, .nil, .nil⟩, machines_empty P ms⟩

theorem init_supp (hv : v.Equivariant) : StateSupp (State.init v) :=
  fun P _ => ⟨(hv.self P).init, machines_empty P v.machines, fun _ h => nomatch h⟩

/-- Every state a run on valid inputs reaches from a state whose names are below its counter keeps them so. -/
theorem run_supp (hv : v.Equivariant) {P : List AnySite}
    {E : List AnyEffectSite} (hr : v.Reach P E) : (s : State v) → Inv P s → StateSupp s → (xs : List (Input v)) →
    ValidRun T s xs → StateSupp (run T v s xs).1
  | _, _, hs, [], _ => hs
  | s, hi, hs, x :: xs, ⟨hx, hxs⟩ =>
    run_supp hv hr _ (step_inv T hr s hi x) (step_supp T hv hs hi.below x hx) xs hxs

/-- Every cascade a step on a valid input starts, from a state whose names are below its counter, is one T5 speaks
about. -/
theorem begins_supp (hv : v.Equivariant) {s : State v}
    (hs : StateSupp s) (hb : ∀ p ∈ s.pending, p.id < s.nextId) {x : Input v} (hx : x.Valid s) {a : Acc v}
    (h : Begins T s x a) : Supp a := by
  cases h with
  | command i caller input a h =>
    exact command_begin T hv hs hb (List.get_mem _ _) (fun P hP => rel0_outside (hx P hP).1) (fun P hP => (hx P hP).2) h
  | answer to value p h a hp _ happ => exact answer_begin T hv hs hb (List.mem_of_find?_eq_some hp) to hx h happ
  | event i value a h => exact event_begin T hv hs hb i hx h
  | clock time s' effs a _ hf h => exact clock_begin hv hs hb time hf h

end Step

end Tazuna.Ir
