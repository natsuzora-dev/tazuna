import Tazuna.Smt.Starts

/-! T2 for an event, with machines: the subscription wraps the value into an event, the records apply it, every
machine reacts (`encodeReact`), and the service's and every instance's invariants are checked on the result, in the
step's order (the service's first, then machines in declaration order, instances in key order). A machine's effects
are not encoded yet: a machine of a service whose layout has effect kinds is refused, so every machine the encoding
covers starts no effect, which the theorem derives from the relation (an effect would need a kind). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- What one machine's part of an event step encodes: its new instance table and the invariant checks of its slots. -/
structure MachineOut where
  table : Term
  checks : List InstCheck

/-- One machine's reaction to an event and its instances' invariants on the result, with their condition. -/
def encodeMachine (m : MachineV r e) (tbl records now ev : Term) : Except Refusal (MachineOut × Term) := do
  let _ ← need' "a machine whose effects would go into the pending table, which is not encoded yet"
    (L.effectsOf e).isEmpty ()
  let (rc, c0) ← ReactCode.of L m
  let (o, c1) ← encodeReact L m rc tbl records now ev
  let (inv, c2) ← m.invariants.code L
  let (checks, c3) ← encodeInstInvariants L T m inv o.table records now
  pure (⟨o.table, checks⟩, andT c0 (andT c1 (andT c2 c3)))

/-- Every machine's part of an event step, from its instance table, in the service's order. -/
def encodeMachines : List (MachineV r e) → List Term → (records now ev : Term) → Except Refusal (List MachineOut × Term)
  | [], [], _, _, _ => pure ([], tt)
  | m :: ms, x :: xs, records, now, ev => do
    let (a, c) ← encodeMachine L T m x records now ev
    let (as, cs) ← encodeMachines ms xs records now ev
    pure (a :: as, andT c cs)
  | _, _, _, _, _ => .error (.outside "machines and instance tables that differ in number")

/-- The names of the instances' broken invariants the model's tables give, machines in order. -/
def machinesBroken (M : Model) (ms : List (MachineV r e)) (outs : List MachineOut) : List String :=
  (ms.zip outs).flatMap fun (m, o) => instBroken L T M m.key o.checks

end

section
variable {T : List TypeDecl} {v : ServiceV}

/-- One event's reaction on a service without reactions: the records apply it and every machine reacts. -/
theorem react_plain (hx : v.reactions = []) (s : State v) (ev : v.event.den0) :
    Step.react T s ev =
      ({ s with records := v.apply.fn (s.records, ev, ()),
                machines := s.machines.map fun ms0 => (Step.machineStep T (v.apply.fn (s.records, ev, ())) s.now ev ms0).1 },
        s.machines.flatMap fun ms0 => (Step.machineStep T (v.apply.fn (s.records, ev, ())) s.now ev ms0).2) := by
  have h : ∀ (l : List (Step.MachineState v.records v.event)) acc effs,
      l.foldl (fun (ms, effs) ms0 =>
        let (m', es) := Step.machineStep T (v.apply.fn (s.records, ev, ())) s.now ev ms0; (ms ++ [m'], effs ++ es))
        (acc, effs) =
      (acc ++ l.map fun ms0 => (Step.machineStep T (v.apply.fn (s.records, ev, ())) s.now ev ms0).1,
        effs ++ l.flatMap fun ms0 => (Step.machineStep T (v.apply.fn (s.records, ev, ())) s.now ev ms0).2) := by
    intro l
    induction l with
    | nil => intro acc effs; simp
    | cons x l ih => intro acc effs; simp only [List.foldl_cons]; rw [ih]; simp
  simp only [Step.react, hx, List.flatMap_nil, List.append_nil]
  rw [h]
  simp

/-- An event's step on a service without reactions whose machines start no effect, computed. -/
theorem step_event_plain (hx : v.reactions = []) (s : State v) (i : Fin v.subscribes.length)
    (value : (v.subscribes.get i).event.den0)
    (hq : ∀ ms0 ∈ s.machines, (Step.machineStep T (v.apply.fn (s.records, (v.subscribes.get i).wrap.fn (value, ()), ()))
      s.now ((v.subscribes.get i).wrap.fn (value, ())) ms0).2 = []) :
    let ev := (v.subscribes.get i).wrap.fn (value, ())
    let records := v.apply.fn (s.records, ev, ())
    let s' : State v := { s with records, machines := s.machines.map fun ms0 => (Step.machineStep T records s.now ev ms0).1 }
    step T v s (.event i value) = match Step.invariants s' with
      | n :: _ => ⟨s, .fault (.invariant n), [], []⟩
      | [] => ⟨s', .accepted, [ev], []⟩ := by
  intro ev records s'
  have hnil : (s.machines.flatMap fun ms0 => (Step.machineStep T (v.apply.fn (s.records,
      (v.subscribes.get i).wrap.fn (value, ()), ())) s.now ((v.subscribes.get i).wrap.fn (value, ())) ms0).2) = [] :=
    List.flatMap_eq_nil_iff.2 hq
  simp only [step, Step.finish, Step.applyEvents, List.foldlM, react_plain hx]
  rw [hnil]
  simp only [Step.start, List.foldlM, bind, Except.bind, pure, Except.pure, Step.settle]
  rfl

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- An effect option that holds an effect relates the effect to a value. -/
theorem opt_some_rel {x : (Ty.dsl .effect [e]).den} {z : Val}
    (h : RelV L (Ty.option (.dsl .effect [e])) (.inl (x, ())) z) : ∃ zx, RelV L (.dsl .effect [e]) x zx := by
  obtain ⟨_, _, _, vals, -, v1, _, -, hx, -⟩ := h
  exact ⟨v1, hx⟩

/-- T2 for one machine's part of an event step: wherever the condition holds, the machine starts no effect, its new
table term denotes the instances after the step, and the names read from the model are the broken invariants of those
instances in key order. -/
theorem machine_event (m : MachineV r e) (hor : m.key.orderable = true) (hko : m.key.ordered T = true)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now evT : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L e (Ty.up _ m.event_data ev) (evT.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {mo : MachineOut} {c : Term} (henc : encodeMachine L T m x records now evT = .ok (mo, c)) (hc : Holds M c) :
    (Step.machineStep T recs tnow ev ⟨m, instancesOf T m tbl⟩).2 = [] ∧
      ∃ tbl', RelV L m.table (Ty.up _ m.table_data tbl') (mo.table.denote M) ∧
        instancesOf T m tbl' = (Step.machineStep T recs tnow ev ⟨m, instancesOf T m tbl⟩).1.2 ∧
        instBroken L T M m.key mo.checks =
          (instancesOf T m tbl').flatMap fun i => Step.broken (m.invariants.fn (.inl (i.key, i.state, recs, tnow, ()), ())) := by
  obtain ⟨_, h0, henc⟩ := bind_ok.1 henc
  have hk : (L.effectsOf e).isEmpty = true := by unfold need' at h0; split at h0 <;> simp_all
  obtain ⟨⟨rc, c0⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨inv, c2⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, c3⟩, h4, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hc0, hc123⟩ := (holds_andT _ _).1 hc
  obtain ⟨hc1, hc23⟩ := (holds_andT _ _).1 hc123
  obtain ⟨hc2, hc3⟩ := (holds_andT _ _).1 hc23
  obtain ⟨⟨tbl', ht', hi'⟩, svX, E, -, hhX, hEp⟩ := react_step (T := T) m hor h1 hc0 recs tnow ev hrec hnow hevT tbl
    htbl h2 hc1
  have hinv := m.invariants.code_fn m.inv_data h3 hc2
  refine ⟨?_, tbl', ht', hi', instBroken_eq m hko hinv recs tnow hrec hnow tbl' ht' h4 hc3⟩
  rw [machineStep_effects m (Ty.plain_of_orderable _ hor)]
  refine List.flatMap_eq_nil_iff.2 fun k hkk => ?_
  obtain ⟨vs, ⟨zk, z, -, -, hz⟩⟩ := forall2_mem hhX (hEp.mem_iff.2 hkk)
  unfold sentOf
  cases hst : startedOf m (instancesOf T m tbl) recs tnow ev k with
  | inl p =>
    obtain ⟨x', ⟨⟩⟩ := p
    rw [hst] at hz
    obtain ⟨zx, d, n, -, j, key, vals, hj, -⟩ := opt_some_rel hz
    rw [List.isEmpty_iff.1 hk] at hj
    simp at hj
  | inr q => match q with
    | .inl () => rfl
    | .inr y => nomatch y

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- The broken invariants of machines' instances, machines in order and instances in key order, as the step lists
them. -/
def instancesBroken (recs : v.records.den0) (tnow : Int) (sms : List (Step.MachineState v.records v.event)) :
    List String :=
  sms.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => Step.broken (m.invariants.fn (.inl (i.key, i.state, recs, tnow, ()), ()))

/-- T2 for the machines' part of an event step: wherever the condition holds, no machine starts an effect, the new
tables denote the machines after the step, and the names read from the model are their broken invariants in the
step's order. -/
theorem machines_event (recs : v.records.den0) (tnow : Int) (ev : v.event.den0) {records now evT : Term}
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L v.event (Ty.up _ hed ev) (evT.denote M)) :
    (ms : List (MachineV v.records v.event)) → (xs : List Term) → (sms : List (Step.MachineState v.records v.event)) →
    (outs : List MachineOut) → {c : Term} → MachinesRel M L T ms xs sms →
    (∀ m ∈ ms, m.key.orderable = true ∧ m.key.ordered T = true) → encodeMachines L T ms xs records now evT = .ok (outs, c) →
    Holds M c →
    (∀ ms0 ∈ sms, (Step.machineStep T recs tnow ev ms0).2 = []) ∧
      MachinesRel M L T ms (outs.map (·.table)) (sms.map fun ms0 => (Step.machineStep T recs tnow ev ms0).1) ∧
      machinesBroken L T M ms outs = instancesBroken recs tnow (sms.map fun ms0 => (Step.machineStep T recs tnow ev ms0).1)
  | [], [], [], outs, c, _, _, henc, _ => by
    simp only [encodeMachines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    exact ⟨by simp, trivial, rfl⟩
  | m :: ms, x :: xs, sm :: sms, outs, c, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hor, henc, hc => by
    obtain ⟨⟨a, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨as, c2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    obtain ⟨hor1, hko1⟩ := hor m (by simp)
    subst hsm
    obtain ⟨hq, tbl', ht', hi', hb⟩ := machine_event (T := T) m hor1 hko1 recs tnow ev hrec hnow hevT tbl htbl h1 hc1
    obtain ⟨hqs, hrel, hbs⟩ := machines_event recs tnow ev hrd hed hrec hnow hevT ms xs sms as hrest
      (fun m' hm => hor m' (by simp [hm])) h2 hc2
    refine ⟨?_, ⟨⟨tbl', ht', ?_⟩, hrel⟩, ?_⟩
    · intro ms0 hms0
      rcases List.mem_cons.1 hms0 with rfl | h
      · exact hq
      · exact hqs ms0 h
    · rw [hi']; rfl
    · simp only [machinesBroken, List.zip_cons_cons, List.flatMap_cons, List.map_cons, instancesBroken] at hbs ⊢
      rw [hb, hi']
      exact congrArg _ hbs
  | [], [], _ :: _, _, _, h, _, _, _ | [], _ :: _, _, _, _, h, _, _, _ | _ :: _, [], _, _, _, h, _, _, _
  | _ :: _, _ :: _, [], _, _, h, _, _, _ => h.elim

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model}

/-- T2 for an event on a service without reactions: wherever the conditions hold, a broken invariant's name (the
service's first, then each machine's instances in key order) is the step's fault, and otherwise the step is accepted
with the records, the instance tables and the event the terms denote, and no out line. -/
theorem event_step {v : ServiceV} (hx : v.reactions = []) (s : State v) (i : Fin v.subscribes.length)
    (value : (v.subscribes.get i).event.den0) (hd : EventData v i) {ec : EventCode v i} {ce : Term}
    (hec : EventCode.of L v i = .ok (ec, ce)) (hce : Holds M ce) {records sv now : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) (hnow : now.denote M = .int s.now)
    {xs : List Term} (hms : MachinesRel M L T v.machines xs s.machines)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    {o : EventOut} {cond : Term} (henc : encodeEvent L ec records sv = .ok (o, cond)) (hc : Holds M cond)
    {outs : List MachineOut} {cm : Term} (hm : encodeMachines L T v.machines xs o.records now o.event = .ok (outs, cm))
    (hcm : Holds M cm) :
    let r := step T v s (.event i value)
    match brokenIn M o.invariants ++ machinesBroken L T M v.machines outs with
    | n :: _ => r = ⟨s, .fault (.invariant n), [], []⟩
    | [] => r.outcome = .accepted ∧ r.out = [] ∧
        r.state = { s with records := r.state.records, machines := r.state.machines } ∧
        RelV L v.records (Ty.up _ hd.records r.state.records) (o.records.denote M) ∧
        MachinesRel M L T v.machines (outs.map (·.table)) r.state.machines ∧
        ∃ e, r.events = [e] ∧ RelV L v.event (Ty.up _ hd.event e) (o.event.denote M) := by
  intro r
  obtain ⟨hr', he', hb'⟩ := event_rel i value hd hec hce hrec hsv henc hc
  obtain ⟨hq, hrel, hbs⟩ := machines_event (T := T) _ s.now _ hd.records hd.event hr' hnow he' v.machines xs s.machines
    outs hms hor hm hcm
  simp only [r]
  rw [step_event_plain hx s i value hq]
  let ev := (v.subscribes.get i).wrap.fn (value, ())
  let recs' := v.apply.fn (s.records, ev, ())
  let ms' := s.machines.map fun ms0 => (Step.machineStep T recs' s.now ev ms0).1
  have hinv : Step.invariants ({ s with records := recs', machines := ms' } : State v) =
      brokenIn M o.invariants ++ machinesBroken L T M v.machines outs := by
    simp only [Step.invariants]
    rw [hb', hbs]
    rfl
  rw [hinv]
  cases brokenIn M o.invariants ++ machinesBroken L T M v.machines outs with
  | cons n ns => rfl
  | nil => exact ⟨rfl, rfl, rfl, hr', hrel, _, rfl, he'⟩

end

end Tazuna.Smt
