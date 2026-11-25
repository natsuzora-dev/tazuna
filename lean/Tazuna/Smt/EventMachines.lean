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
def encodeMachines : (ms : List (MachineV r e)) → PerMachine Term ms → (records now ev : Term) →
    Except Refusal (PerMachine ReactOut ms × Term)
  | [], .nil, _, _, _ => pure (.nil, tt)
  | m :: ms, .cons x xs, records, now, ev => do
    let (a, c) ← encodeMachine L m x records now ev
    let (as, cs) ← encodeMachines ms xs records now ev
    pure (.cons a as, andT c cs)

/-- Every machine's instance invariant checks on the tables `xs`, machines in order. -/
def encodeInstChecks : (ms : List (MachineV r e)) → PerMachine Term ms → (records now : Term) →
    Except Refusal (PerMachine (List InstCheck) ms × Term)
  | [], .nil, _, _ => pure (.nil, tt)
  | m :: ms, .cons x xs, records, now => do
    let (inv, c0) ← m.invariants.code L
    let (cs, c1) ← encodeInstInvariants L T m inv x records now
    let (rest, c2) ← encodeInstChecks ms xs records now
    pure (.cons cs rest, andT c0 (andT c1 c2))

/-- The names of the broken instance invariants the checks read from the model, machines in order. -/
def checksBroken (M : Model) : (ms : List (MachineV r e)) → PerMachine (List InstCheck) ms → List String
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
      ({ s with records := v.apply.fn (s.records, ev, ()),
                machines := s.machines.map fun ms0 => (Step.machineStep T (v.apply.fn (s.records, ev, ())) s.now ev ms0).1 },
        (s.machines.flatMap fun ms0 => (Step.machineStep T (v.apply.fn (s.records, ev, ())) s.now ev ms0).2) ++
          reactedBy s (v.apply.fn (s.records, ev, ())) ev) := by
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
  simp only [Step.react]
  rw [h]
  simp

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
    ∃ svX E, SlotsDen M (mo.starts.map fun w => (w.1, [w.key, w.effect])) svX ∧
      Holds2 (EStart (L := L) m (instancesOf T m tbl) recs tnow ev) E svX ∧
      E.Perm (Ty.sortBy T m.key (dedupBy (Ty.semWith Dsl.base m.key).2 (m.instances.fn (recs, ())))) := by
  obtain ⟨⟨rc, c0⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o, c1⟩, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hc0, hc1⟩ := (holds_andT _ _).1 hc
  exact (react_step (T := T) m hor h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2 hc1).2

/-- T2 for one machine's reaction to an event: wherever the condition holds, its new table term denotes the
instances after the step. -/
theorem machine_event (m : MachineV r e) (hor : m.key.orderable = true)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now evT : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L e (Ty.up _ m.event_data ev) (evT.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {mo : ReactOut} {c : Term} (henc : encodeMachine L m x records now evT = .ok (mo, c)) (hc : Holds M c) :
    ∃ tbl', RelV L m.table (Ty.up _ m.table_data tbl') (mo.table.denote M) ∧
      instancesOf T m tbl' = (Step.machineStep T recs tnow ev ⟨m, instancesOf T m tbl⟩).1.2 := by
  obtain ⟨⟨rc, c0⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o, c1⟩, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hc0, hc1⟩ := (holds_andT _ _).1 hc
  exact (react_step (T := T) m hor h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2 hc1).1

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- The broken invariants of machines' instances, machines in order and instances in key order, as the step lists
them. -/
def instancesBroken (recs : v.records.den0) (tnow : Int) (sms : List (Step.MachineState v.records v.event)) :
    List String :=
  sms.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => Step.broken (m.invariants.fn (.inl (i.key, i.state, recs, tnow, ()), ()))

/-- T2 for the machines' part of an event step: wherever the condition holds, the new tables denote the machines
after the step. -/
theorem machines_event (recs : v.records.den0) (tnow : Int) (ev : v.event.den0) {records now evT : Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L v.event (Ty.up _ v.event_data ev) (evT.denote M)) :
    (ms : List (MachineV v.records v.event)) → (xs : PerMachine Term ms) →
    (sms : List (Step.MachineState v.records v.event)) → (outs : PerMachine ReactOut ms) → {c : Term} →
    MachinesRel M L T ms xs sms → (∀ m ∈ ms, m.key.orderable = true) →
    encodeMachines L ms xs records now evT = .ok (outs, c) → Holds M c →
      MachinesRel M L T ms (outs.map (·.table)) (sms.map fun ms0 => (Step.machineStep T recs tnow ev ms0).1)
  | [], .nil, [], outs, c, _, _, henc, _ => by
    simp only [encodeMachines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    trivial
  | m :: ms, .cons x xs, sm :: sms, outs, c, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hor, henc, hc => by
    obtain ⟨⟨a, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨as, c2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    subst hsm
    obtain ⟨tbl', ht', hi'⟩ := machine_event (T := T) m (hor m (by simp)) recs tnow ev hrec hnow hevT tbl htbl h1 hc1
    refine ⟨⟨tbl', ht', ?_⟩, machines_event recs tnow ev hrec hnow hevT ms xs sms as hrest
      (fun m' hm => hor m' (by simp [hm])) h2 hc2⟩
    rw [hi']; rfl
  | [], .nil, _ :: _, _, _, h, _, _, _ | _ :: _, .cons _ _, [], _, _, h, _, _, _ => h.elim

/-- The instance checks name the broken invariants of the machines the tables denote. -/
theorem instChecks_rel (recs : v.records.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow) :
    (ms : List (MachineV v.records v.event)) → (xs : PerMachine Term ms) →
    (sms : List (Step.MachineState v.records v.event)) → MachinesRel M L T ms xs sms →
    (∀ m ∈ ms, m.key.ordered T = true) → {checks : PerMachine (List InstCheck) ms} → {c : Term} →
    encodeInstChecks L T ms xs records now = .ok (checks, c) →
    Holds M c → checksBroken L T M ms checks = instancesBroken recs tnow sms
  | [], .nil, [], _, _, checks, c, henc, _ => by
    simp only [encodeInstChecks, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    rfl
  | m :: ms, .cons x xs, sm :: sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hord, checks, c, henc, hc => by
    obtain ⟨⟨inv, c0⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨cs, c1⟩, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2⟩, h3, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc0, hc12⟩ := (holds_andT _ _).1 hc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc12
    subst hsm
    have hinv := m.invariants.code_fn m.inv_data h1 hc0
    have hrec' : RelV L v.records (Ty.up _ m.records_data recs) (records.denote M) := hrec
    have hb := instBroken_eq m (hord m (by simp)) hinv recs tnow hrec' hnow tbl htbl h2 hc1
    have ih := instChecks_rel recs tnow hrec hnow ms xs sms hrest (fun m' hm => hord m' (by simp [hm])) h3 hc2
    simp only [checksBroken, List.flatMap_cons, instancesBroken] at ih ⊢
    rw [hb]
    exact congrArg _ ih
  | [], .nil, _ :: _, h, _, _, _, _, _ | _ :: _, .cons _ _, [], h, _, _, _, _, _ => h.elim

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem instCheckAt_cond (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)} {de : Nat}
    {records now f : Term} {xs : List Term} {c : InstCheck} {cj : Term}
    (hg : instCheckAt L m inv de records now (f, xs) = .ok (c, cj)) : ∃ X, cj = .ite f X tt := by
  repeat obtain ⟨_, _, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  exact ⟨_, rfl⟩

/-- One occupied slot's instance invariant check: its condition holds exactly when the invariants fit at that
instance. -/
theorem instCheck_exact (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)} {ci : Term}
    (hci : m.invariants.code L = .ok (inv, ci)) (hcic : Holds M ci) (recs : r.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {de : Nat} (hde : tupleD L [m.state, Ty.option (.tuple [.int, m.state])] = .ok de)
    {f : Term} {xs : List Term} {zk zv : Val} (hf : f.denote M = .bool true) (hxs : Term.denotes M xs = [zk, zv])
    (k0 : m.key.den0) (e0 : (instEntry m.state).den0)
    (hk : RelV L m.key (Ty.up _ m.key_data k0) zk)
    (he : RelV L (instEntry m.state) (Ty.up _ m.entry_data e0) zv)
    {c : InstCheck} {cj : Term} (hg : instCheckAt L m inv de records now (f, xs) = .ok (c, cj)) :
    Holds M cj ↔ m.invariants.appFits L.count (.inl (k0, e0.1, recs, tnow, ()), ()) := by
  obtain ⟨tk, te, rfl⟩ : ∃ tk te, xs = [tk, te] := by
    match xs, hxs with
    | [tk, te], _ => exact ⟨tk, te, rfl⟩
  simp only [Term.denotes, List.cons.injEq, and_true] at hxs
  obtain ⟨htk, hte⟩ := hxs
  obtain ⟨ctx, h1, hg⟩ := bind_ok.1 hg
  obtain ⟨cx, h2, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨rs, c1⟩, h3, hg⟩ := bind_ok.1 hg
  obtain ⟨rules, h4, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero] at h1
  have hst : Ty.isData m.state = true := m.state_data
  have hopt : (Ty.tuple [Ty.option (.tuple [.int, m.state])]).isData = true := by
    simp [Ty.option, Ty.isData, Ty.isDatas, Ty.isDatass, hst]
  obtain ⟨d', n', vals, hfd, hzv, hvals⟩ := he
  obtain ⟨n'', hfd'⟩ := tupleD_ok hde
  have := find_det hfd hfd'
  subst this
  erw [Ty.up_tuple _ _ _ hst hopt] at hvals
  obtain ⟨v0, vs0, rfl, hv0, -⟩ := hvals
  have hsel : (Term.sel d' 0 0 te).denote M = v0 := by rw [sel_ctor _ (hte.trans hzv)]; rfl
  have hctx := adtCtor_rel (L := L) (M := M) (vs := [[m.key, m.state, r, .int]]) ⟨0, by simp⟩ _ _ h1
    (Ty.up _ m.key_data k0, Ty.up _ m.state_data e0.1, Ty.up _ m.records_data recs, tnow, ())
    ⟨_, _, rfl, htk ▸ hk, _, _, rfl, hsel ▸ hv0, _, _, rfl, hrec, _, _, rfl, hnow, rfl⟩
  rw [← up_mctx m m.ctx_data] at hctx
  have hcx : Smt.Rel M L _ (Ty.up _ m.ctx_data (.inl (k0, e0.1, recs, tnow, ()))) cx :=
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
  obtain ⟨de, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨cs, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨p0, -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have htbl' : Smt.Rel M L (.table m.key (instEntry m.state)) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS, -, hw, hp, hh⟩ := table_view htbl' h1
  let inst : m.key.den × (instEntry m.state).den → Step.Instance m :=
    fun y => instOf m (Ty.down _ m.key_data y.1) (Ty.down _ m.entry_data y.2)
  have hF : Forall2 (fun sl c => ∃ ch, instCheckAt L m inv de records now sl = .ok (ch, c)) (slotsOf d dt n 2 x)
      (cs.map (·.2)) := forall2_snd (mapM_ok _ _ _ h3)
  rw [allT_slots_exact (P := fun y => m.invariants.appFits L.count (.inl ((inst y).key, (inst y).state, recs, tnow, ()), ()))
    _ ?_ hS hh hF]
  · have hperm : (ys.map inst).Perm (instancesOf T m tbl) := by
      have := hp.map inst
      erw [Ty.up_table m.key (instEntry m.state) m.table_data m.key_data m.entry_data tbl, List.map_map] at this
      refine (this.trans (List.Perm.of_eq (List.map_congr_left fun q _ => ?_))).trans (List.mergeSort_perm _ _).symm
      simp [inst, Ty.down_up]
    constructor
    · intro h i hi
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hperm.mem_iff.2 hi)
      exact h y hy
    · intro h y hy
      exact h (inst y) (hperm.mem_iff.1 (List.mem_map.2 ⟨y, hy, rfl⟩))
  · rintro ⟨f, xs⟩ cj ⟨ch, hg⟩
    obtain ⟨X, hX⟩ := instCheckAt_cond m hg
    refine ⟨fun hf => ?_, fun y hf hey => ?_⟩
    · simp only at hf
      rw [hX]; simp [holds_ite, hf, Val.toBool, holds_tt]
    · obtain ⟨zk, zv, hz, hk, he⟩ := hey
      exact instCheck_exact m hci hcic recs tnow hrec hnow h2 hf hz (Ty.down _ m.key_data y.1)
        (Ty.down _ m.entry_data y.2) (by rw [Ty.up_down]; exact hk) (by rw [Ty.up_down]; exact he) hg

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- The condition of one machine's reaction to an event is exact: it holds exactly when the machine's kept sources
fit and its reaction fits (`react_exact`). -/
theorem machine_exact (m : MachineV r e) (hor : m.key.orderable = true)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now evT : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L e (Ty.up _ m.event_data ev) (evT.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {mo : ReactOut} {c : Term} (henc : encodeMachine L m x records now evT = .ok (mo, c)) :
    Holds M c ↔ ((m.instances.fits L.count).1 ∧ (m.on.fits L.count).1 ∧ (m.after.fits L.count).1 ∧
        (m.effect.fits L.count).1) ∧
      (m.instances.appFits L.count (recs, ()) ∧
        allFit (m.instances.fn (recs, ())) (keyFits L.count m (instancesOf T m tbl) recs tnow ev)) := by
  have hpl := Ty.plain_of_orderable _ hor
  obtain ⟨⟨rc, c0⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o, c1⟩, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  rw [holds_andT, ← reactCode_exact (M := M) m h1]
  exact ⟨fun ⟨hc0, hc1⟩ => ⟨hc0, (react_exact (T := T) m hpl h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2).1 hc1⟩,
    fun ⟨hc0, p1⟩ => ⟨hc0, (react_exact (T := T) m hpl h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2).2 p1⟩⟩

end

section
variable {r e : Ty}

/-- Whether the functions one machine's reaction to an event applies fit: its kept sources and its reaction
(`keyFits` for each key of the bag `instances` returns). -/
def machineFits (S : Ty → Nat) (sm : Step.MachineState r e) (recs : r.den0) (tnow : Int) (ev : e.den0) : Prop :=
  ((sm.1.instances.fits S).1 ∧ (sm.1.on.fits S).1 ∧ (sm.1.after.fits S).1 ∧ (sm.1.effect.fits S).1) ∧
    (sm.1.instances.appFits S (recs, ()) ∧ allFit (sm.1.instances.fn (recs, ())) (keyFits S sm.1 sm.2 recs tnow ev))

/-- Whether every machine's invariants fit at its instances: the source, and applied at each instance. -/
def instChecksFit (S : Ty → Nat) (recs : r.den0) (now : Int) : List (Step.MachineState r e) → Prop
  | [] => True
  | ⟨m, insts⟩ :: rest => (m.invariants.fits S).1 ∧
      (∀ i ∈ insts, m.invariants.appFits S (.inl (i.key, i.state, recs, now, ()), ())) ∧ instChecksFit S recs now rest

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- The condition of the machines' part of an event step is exact: it holds exactly when every machine's part fits. -/
theorem machines_exact (recs : v.records.den0) (tnow : Int) (ev : v.event.den0) {records now evT : Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L v.event (Ty.up _ v.event_data ev) (evT.denote M)) :
    (ms : List (MachineV v.records v.event)) → (xs : PerMachine Term ms) →
    (sms : List (Step.MachineState v.records v.event)) → (outs : PerMachine ReactOut ms) → {c : Term} →
    MachinesRel M L T ms xs sms → (∀ m ∈ ms, m.key.orderable = true) →
    encodeMachines L ms xs records now evT = .ok (outs, c) →
    (Holds M c ↔ ∀ sm ∈ sms, machineFits L.count sm recs tnow ev)
  | [], .nil, [], outs, c, _, _, henc => by
    simp only [encodeMachines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨-, rfl⟩ := henc
    simp [holds_tt]
  | m :: ms, .cons x xs, sm :: sms, outs, c, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hor, henc => by
    obtain ⟨⟨a, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨as, c2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    subst hsm
    rw [holds_andT, machine_exact (T := T) m (hor m (by simp)) recs tnow ev hrec hnow hevT tbl htbl h1,
      machines_exact recs tnow ev hrec hnow hevT ms xs sms as hrest (fun m' hm => hor m' (by simp [hm])) h2]
    simp only [List.mem_cons, forall_eq_or_imp]
    rfl
  | [], .nil, _ :: _, _, _, h, _, _ | _ :: _, .cons _ _, [], _, _, h, _, _ => h.elim

/-- The instance checks ask exactly that every machine's invariants fit at its instances. -/
theorem instChecks_exact (recs : v.records.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow) :
    (ms : List (MachineV v.records v.event)) → (xs : PerMachine Term ms) →
    (sms : List (Step.MachineState v.records v.event)) → MachinesRel M L T ms xs sms →
    {checks : PerMachine (List InstCheck) ms} → {c : Term} → encodeInstChecks L T ms xs records now = .ok (checks, c) →
    (Holds M c ↔ instChecksFit L.count recs tnow sms)
  | [], .nil, [], _, checks, c, henc => by
    simp only [encodeInstChecks, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨-, rfl⟩ := henc
    simp [instChecksFit, holds_tt]
  | m :: ms, .cons x xs, sm :: sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, checks, c, henc => by
    obtain ⟨⟨inv, c0⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨cs, c1⟩, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2⟩, h3, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    subst hsm
    have hrec' : RelV L v.records (Ty.up _ m.records_data recs) (records.denote M) := hrec
    have e0 := (m.invariants.code_exact (M := M) h1).1
    simp only [instChecksFit]
    rw [holds_andT, holds_andT, e0, instChecks_exact recs tnow hrec hnow ms xs sms hrest h3]
    constructor
    · rintro ⟨p0, p1, p2⟩
      exact ⟨p0, (instInvariants_exact m h1 (e0.2 p0) recs tnow hrec' hnow tbl htbl h2).1 p1, p2⟩
    · rintro ⟨p0, p1, p2⟩
      exact ⟨p0, (instInvariants_exact m h1 (e0.2 p0) recs tnow hrec' hnow tbl htbl h2).2 p1, p2⟩
  | [], .nil, _ :: _, h, _, _, _ | _ :: _, .cons _ _, [], h, _, _, _ => h.elim

end

end Tazuna.Smt
