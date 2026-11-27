import Tazuna.Smt.Starts
import Tazuna.Smt.ReactExact

/-! The machines' part of an event: every machine reacts to the event on the records after it (`encodeReact`),
yielding its new instance table and its start slots, the effects its instances start, which `Tazuna.Smt.Reactions`
writes into the pending table with the reactions' requests. Instance invariants are checked once, on the tables a step
ends with (`encodeInstChecks`), machines in declaration order and instances in key order, so an event list or a
cascade of firing rounds checks them where the step does: at the end. Each condition is exact: it holds exactly when
the functions the step applies fit the layout's slot counts (each machine's reaction by `react_exact`, the instance
checks every instance's invariants on the tables after the step). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- One machine's reaction to an event, with its condition. -/
def encodeMachine (m : MachineV r e) (tbl records now ev : Term) : Except Refusal (ReactOut × Term) := do
  let (rc, c0) ← ReactCode.of L m
  let (o, c1) ← encodeReact L m rc tbl records now ev
  pure (o, andT c0 c1)

/-- Every machine's reaction to an event, from its instance table, in the service's order. -/
def encodeMachines : (ms : List (MachineV r e)) → PerMachine (fun _ => Term) ms → (records now ev : Term) →
    Except Refusal (PerMachine (fun _ => ReactOut) ms × Term)
  | [], .nil, _, _, _ => pure (.nil, tt)
  | m :: ms, .cons x xs, records, now, ev => do
    let (a, c) ← encodeMachine L m x records now ev
    let (as, cs) ← encodeMachines ms xs records now ev
    pure (.cons a as, andT c cs)

/-- Every machine's instance invariant checks on the tables `xs`, machines in order. -/
def encodeInstChecks : (ms : List (MachineV r e)) → PerMachine (fun _ => Term) ms → (records now : Term) →
    Except Refusal (PerMachine (fun _ => List InstCheck) ms × Term)
  | [], .nil, _, _ => pure (.nil, tt)
  | m :: ms, .cons x xs, records, now => do
    let (inv, c0) ← m.invariants.code L
    let (cs, c1) ← encodeInstInvariants L T m inv x records now
    let (rest, c2) ← encodeInstChecks ms xs records now
    pure (.cons cs rest, andT c0 (andT c1 c2))

/-- The names of the broken instance invariants the checks read from the model, machines in order. -/
def checksBroken (M : Model) : (ms : List (MachineV r e)) → PerMachine (fun _ => List InstCheck) ms → List String
  | [], .nil => []
  | m :: ms, .cons cs rest => instBroken L T M m.key cs ++ checksBroken M ms rest

end

section
variable {T : List TypeDecl} {v : ServiceV}

/-- The effects the reactions start on an event, reactions in order. -/
abbrev reactedBy (s : State v) (records : v.records.den0) (ev : v.event.den0) : List (Sender × EffectV v.event) :=
  v.reactions.flatMap fun x => (x.effectsAt ev records s.now).map (.reaction x.name, ·)

/-- One event's reaction: the records apply it, every machine reacts, then every reaction. -/
theorem react_eq (s : State v) (ev : v.event.den0) :
    Step.react T s ev =
      ({ s with records := v.apply.fn (.inl (s.records, s.now, ()), ev, ()),
                machines := (Step.reactMachines T (v.apply.fn (.inl (s.records, s.now, ()), ev, ())) s.now ev s.machines).1 },
        (s.machines.toSigma.flatMap fun sm => (Step.machineStep T (v.apply.fn (.inl (s.records, s.now, ()), ev, ())) s.now ev sm.1 sm.2).2) ++
          reactedBy s (v.apply.fn (.inl (s.records, s.now, ()), ev, ())) ev) := by
  simp only [Step.react, (Step.reactMachines_toSigma T _ s.now ev s.machines).2]

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- The start slots of one machine's part of an event step hold the effects its instances start. -/
theorem machine_starts (m : MachineV r e) (hor : m.key.orderable = true)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now evT : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L e (Ty.up _ m.event_data ev) (evT.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {mo : ReactOut} {c : Term} (henc : encodeMachine L m x records now evT = .ok (mo, c)) (hc : Holds M c) :
    ∃ svX E, SlotsDen M (mo.starts.map StartSlot.slot) svX ∧
      Holds2 (EStart (L := L) m (instancesOf T m tbl) recs tnow ev) E svX ∧
      E.Perm (Ty.sortBy T m.key (dedupBy (Ty.semWith Dsl.base m.key).2 (m.instances.fn (recs, ())))) := by
  obtain ⟨⟨rc, c0⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o, c1⟩, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hc0, hc1⟩ := (holds_andT _ _).1 hc
  exact (react_step (T := T) m hor h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2 hc1).2

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- The broken invariants of machines' instances, machines in order and instances in key order, as the step lists
them. -/
def instancesBroken (recs : v.records.den0) (tnow : Int) {ms : List (MachineV v.records v.event)} (sms : Step.Machines ms) :
    List String :=
  sms.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => Step.broken (m.invariants.fn (.inl (i.key, i.state, recs, tnow, ()), ()))

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem instCheckAt_cond (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)}
    {records now : Term} {sl : InstSlot} {c : InstCheck} {cj : Term}
    (hg : instCheckAt L m inv records now sl = .ok (c, cj)) : ∃ X, cj = .ite sl.flag X tt := by
  repeat obtain ⟨_, _, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  exact ⟨_, rfl⟩

/-- One occupied slot's instance invariant check: its condition holds exactly when the invariants fit at that
instance. -/
theorem instCheck_exact (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)} {ci : Term}
    (hci : m.invariants.code L = .ok (inv, ci)) (hcic : Holds M ci) (recs : r.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {f tk te : Term} {zk zv : Val} (hf : f.denote M = .bool true) (hxs : Term.denotes M [tk, te] = [zk, zv])
    (k0 : m.key.den0) (e0 : m.state.den0)
    (hk : RelV L m.key (Ty.up _ m.key_data k0) zk)
    (he : RelV L m.state (Ty.up _ m.state_data e0) zv)
    {c : InstCheck} {cj : Term} (hg : instCheckAt L m inv records now ⟨f, tk, te⟩ = .ok (c, cj)) :
    Holds M cj ↔ m.invariants.appFits L.count (.inl (k0, e0, recs, tnow, ()), ()) := by
  simp only [Term.denotes, List.cons.injEq, and_true] at hxs
  obtain ⟨htk, hte⟩ := hxs
  obtain ⟨ctx, h1, hg⟩ := bind_ok.1 hg
  obtain ⟨cx, h2, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨rs, c1⟩, h3, hg⟩ := bind_ok.1 hg
  obtain ⟨rules, h4, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  have hctx := adtCtor_rel (L := L) (M := M) (vs := [[m.key, m.state, r, .int]]) ⟨0, by simp⟩ _ _ h1
    (Ty.up _ m.key_data k0, Ty.up _ m.state_data e0, Ty.up _ m.records_data recs, tnow, ())
    ⟨_, _, rfl, htk ▸ hk, _, _, rfl, hte ▸ he, _, _, rfl, hrec, _, _, rfl, hnow, rfl⟩
  rw [← up_mctx m m.ctx_data] at hctx
  have hcx : Smt.Rel M L _ (Ty.up _ m.ctx_data (.inl (k0, e0, recs, tnow, ()))) cx :=
    (rel_ofTerm (need_ok.1 h2) _).2 hctx
  have hite : Holds M (.ite f c1 tt) ↔ Holds M c1 := by simp [holds_ite, hf, Val.toBool]
  rw [hite]
  exact m.invariants.app_exact hci hcic (by simp [Ty.machineCtx, Ty.isFn]) _ _ (ctx_rels m hcx _) h3

/-- The condition of the instances' invariant checks is exact: it holds exactly when the invariants fit at every
instance the table holds. -/
theorem instInvariants_exact (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)}
    {ci : Term} (hci : m.invariants.code L = .ok (inv, ci)) (hcic : Holds M ci) (recs : r.den0) (tnow : Int)
    {records now : Term} (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M))
    (hnow : now.denote M = .int tnow) {x : Term} (tbl : m.table.den0)
    (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {checks : List InstCheck} {cond : Term} (henc : encodeInstInvariants L T m inv x records now = .ok (checks, cond)) :
    Holds M cond ↔ ∀ i ∈ instancesOf T m tbl, m.invariants.appFits L.count (.inl (i.key, i.state, recs, tnow, ()), ()) := by
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨cs, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨p0, -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have htbl' : Smt.Rel M L (.table m.key m.state) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS, -, -, hp, hh⟩ := table_view htbl' h1
  rw [← instSlotsOf_slot] at hS
  let inst : m.key.den × m.state.den → Step.Instance m :=
    fun y => instOf m (Ty.down _ m.key_data y.1) (Ty.down _ m.state_data y.2)
  have hF : Forall2 (fun sl c => ∃ s, s.slot = sl ∧ ∃ ch, instCheckAt L m inv records now s = .ok (ch, c))
      ((instSlotsOf d dt n x).map InstSlot.slot) (cs.map (·.2)) :=
    forall2_map _ (fun s c h => ⟨s, rfl, h⟩) (forall2_snd (mapM_ok _ _ _ h3))
  rw [allT_slots_exact (P := fun y => m.invariants.appFits L.count (.inl ((inst y).key, (inst y).state, recs, tnow, ()), ()))
    _ ?_ hS hh hF]
  · have hperm : (ys.map inst).Perm (instancesOf T m tbl) := by
      have := hp.map inst
      erw [Ty.up_table m.key m.state m.table_data m.key_data m.state_data tbl, List.map_map] at this
      refine (this.trans (List.Perm.of_eq (List.map_congr_left fun q _ => ?_))).trans (List.mergeSort_perm _ _).symm
      simp [inst, Ty.down_up]
    constructor
    · intro h i hi
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hperm.mem_iff.2 hi)
      exact h y hy
    · intro h y hy
      exact h (inst y) (hperm.mem_iff.1 (List.mem_map.2 ⟨y, hy, rfl⟩))
  · rintro _ cj ⟨⟨f, tk, te⟩, rfl, ch, hg⟩
    obtain ⟨X, hX⟩ := instCheckAt_cond m hg
    refine ⟨fun hf => ?_, fun y hf hey => ?_⟩
    · simp only [InstSlot.slot] at hf
      rw [hX]; simp [holds_ite, hf, Val.toBool, holds_tt]
    · obtain ⟨zk, zv, hz, hk, he⟩ := hey
      exact instCheck_exact m hci hcic recs tnow hrec hnow hf hz (Ty.down _ m.key_data y.1)
        (Ty.down _ m.state_data y.2) (by rw [Ty.up_down]; exact hk) (by rw [Ty.up_down]; exact he) hg

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- One machine's reaction to an event: the condition holds exactly when the machine's kept sources fit and its
reaction fits (`react_exact`), and wherever it holds the new table term denotes the instances after the step. -/
theorem machine_encode (m : MachineV r e) (hor : m.key.orderable = true)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now evT : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L e (Ty.up _ m.event_data ev) (evT.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {mo : ReactOut} {c : Term} (henc : encodeMachine L m x records now evT = .ok (mo, c)) :
    (Holds M c ↔ ((m.instances.fits L.count).1 ∧ (m.on.fits L.count).1 ∧ (m.effect.fits L.count).1) ∧
      (m.instances.appFits L.count (recs, ()) ∧
        allFit (m.instances.fn (recs, ())) (keyFits L.count m (instancesOf T m tbl) recs tnow ev))) ∧
    (Holds M c → ∃ tbl', RelV L m.table (Ty.up _ m.table_data tbl') (mo.table.denote M) ∧
      instancesOf T m tbl' = (Step.machineStep T recs tnow ev m (instancesOf T m tbl)).1) := by
  have hpl := Ty.plain_of_orderable _ hor
  obtain ⟨⟨rc, c0⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o, c1⟩, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  refine ⟨?_, fun hc => ?_⟩
  · rw [holds_andT, ← reactCode_exact (M := M) m h1]
    exact ⟨fun ⟨hc0, hc1⟩ => ⟨hc0, (react_exact (T := T) m hpl h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2).1 hc1⟩,
      fun ⟨hc0, p1⟩ => ⟨hc0, (react_exact (T := T) m hpl h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2).2 p1⟩⟩
  · obtain ⟨hc0, hc1⟩ := (holds_andT _ _).1 hc
    exact (react_step (T := T) m hor h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2 hc1).1

end

section
variable {r e : Ty}

/-- Whether the functions one machine's reaction to an event applies fit: its kept sources and its reaction
(`keyFits` for each key of the bag `instances` returns). -/
def machineFits (S : Ty → Nat) (sm : Step.MachineState r e) (recs : r.den0) (tnow : Int) (ev : e.den0) : Prop :=
  ((sm.1.instances.fits S).1 ∧ (sm.1.on.fits S).1 ∧ (sm.1.effect.fits S).1) ∧
    (sm.1.instances.appFits S (recs, ()) ∧ allFit (sm.1.instances.fn (recs, ())) (keyFits S sm.1 sm.2 recs tnow ev))

/-- Whether every machine's invariants fit at its instances: the source, and applied at each instance. -/
def instChecksFit (S : Ty → Nat) (recs : r.den0) (now : Int) : {ms : List (MachineV r e)} → Step.Machines ms → Prop
  | _, .nil => True
  | m :: _, .cons insts rest => (m.invariants.fits S).1 ∧
      (∀ i ∈ insts, m.invariants.appFits S (.inl (i.key, i.state, recs, now, ()), ())) ∧ instChecksFit S recs now rest

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- The machines' part of an event step: the condition holds exactly when every machine's part fits, and wherever it
holds the new tables denote the machines after the step. -/
theorem machines_encode (recs : v.records.den0) (tnow : Int) (ev : v.event.den0) {records now evT : Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L v.event (Ty.up _ v.event_data ev) (evT.denote M)) :
    (ms : List (MachineV v.records v.event)) → (xs : PerMachine (fun _ => Term) ms) →
    (sms : Step.Machines ms) → (outs : PerMachine (fun _ => ReactOut) ms) → {c : Term} →
    MachinesRel M L T ms xs sms → (∀ m ∈ ms, m.key.orderable = true) →
    encodeMachines L ms xs records now evT = .ok (outs, c) →
    (Holds M c ↔ ∀ sm ∈ sms.toSigma, machineFits L.count sm recs tnow ev) ∧
    (Holds M c → MachinesRel M L T ms (outs.map (·.table)) (Step.reactMachines T recs tnow ev sms).1)
  | [], .nil, .nil, outs, c, _, _, henc => by
    simp only [encodeMachines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl⟩ := henc
    exact ⟨by simp [holds_tt], fun _ => trivial⟩
  | m :: ms, .cons x xs, .cons insts sms, outs, c, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hor, henc => by
    obtain ⟨⟨a, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨as, c2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    subst hsm
    have E := machine_encode (T := T) m (hor m (by simp)) recs tnow ev hrec hnow hevT tbl htbl h1
    have IH := machines_encode recs tnow ev hrec hnow hevT ms xs sms as hrest (fun m' hm => hor m' (by simp [hm])) h2
    refine ⟨?_, fun hc => ?_⟩
    · rw [holds_andT, E.1, IH.1]
      simp only [PerMachine.toSigma_cons, List.mem_cons, forall_eq_or_imp]
      rfl
    · obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
      obtain ⟨tbl', ht', hi'⟩ := E.2 hc1
      exact ⟨⟨tbl', ht', hi'.symm⟩, IH.2 hc2⟩

/-- The instance checks: the condition holds exactly when every machine's invariants fit at its instances, and
wherever it holds the checks name the broken invariants of the machines the tables denote. -/
theorem instChecks_encode (recs : v.records.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow) :
    (ms : List (MachineV v.records v.event)) → (xs : PerMachine (fun _ => Term) ms) →
    (sms : Step.Machines ms) → MachinesRel M L T ms xs sms →
    (∀ m ∈ ms, m.key.ordered T = true) → {checks : PerMachine (fun _ => List InstCheck) ms} → {c : Term} →
    encodeInstChecks L T ms xs records now = .ok (checks, c) →
    (Holds M c ↔ instChecksFit L.count recs tnow sms) ∧
    (Holds M c → checksBroken L T M ms checks = instancesBroken recs tnow sms)
  | [], .nil, .nil, _, _, checks, c, henc => by
    simp only [encodeInstChecks, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl⟩ := henc
    exact ⟨by simp [instChecksFit, holds_tt], fun _ => rfl⟩
  | m :: ms, .cons x xs, .cons insts sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hord, checks, c, henc => by
    obtain ⟨⟨inv, c0⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨cs, c1⟩, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2⟩, h3, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    subst hsm
    have hrec' : RelV L v.records (Ty.up _ m.records_data recs) (records.denote M) := hrec
    have e0 := (m.invariants.code_exact (M := M) h1).1
    have IH := instChecks_encode recs tnow hrec hnow ms xs sms hrest (fun m' hm => hord m' (by simp [hm])) h3
    refine ⟨?_, fun hc => ?_⟩
    · simp only [instChecksFit]
      rw [holds_andT, holds_andT, e0, IH.1]
      constructor
      · rintro ⟨p0, p1, p2⟩
        exact ⟨p0, (instInvariants_exact m h1 (e0.2 p0) recs tnow hrec' hnow tbl htbl h2).1 p1, p2⟩
      · rintro ⟨p0, p1, p2⟩
        exact ⟨p0, (instInvariants_exact m h1 (e0.2 p0) recs tnow hrec' hnow tbl htbl h2).2 p1, p2⟩
    · obtain ⟨hc0, hc12⟩ := (holds_andT _ _).1 hc
      obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc12
      have hinv := m.invariants.code_fn m.inv_data h1 hc0
      have hb := instBroken_eq m (hord m (by simp)) hinv recs tnow hrec' hnow tbl htbl h2 hc1
      have ih := IH.2 hc2
      simp only [checksBroken, PerMachine.toSigma_cons, List.flatMap_cons, instancesBroken] at ih ⊢
      rw [hb]
      exact congrArg _ ih

end

end Tazuna.Smt
