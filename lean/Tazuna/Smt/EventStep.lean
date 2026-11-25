import Tazuna.Smt.Starts

/-! T2 for the machines' part of an event: every machine reacts to the event on the records after it
(`encodeReact`), yielding its new instance table and its start slots, the effects its instances start, which
`Tazuna.Smt.Reactions` writes into the pending table with the reactions' requests. Instance invariants are checked once,
on the tables a step ends with (`encodeInstChecks`), machines in declaration order and instances in key order, so an
event list or a cascade of firing rounds checks them where the step does: at the end. -/

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
def encodeMachines : List (MachineV r e) → List Term → (records now ev : Term) → Except Refusal (List ReactOut × Term)
  | [], [], _, _, _ => pure ([], tt)
  | m :: ms, x :: xs, records, now, ev => do
    let (a, c) ← encodeMachine L m x records now ev
    let (as, cs) ← encodeMachines ms xs records now ev
    pure (a :: as, andT c cs)
  | _, _, _, _, _ => .error (.outside "machines and instance tables that differ in number")

/-- Every machine's instance invariant checks on the tables `xs`, machines in order. -/
def encodeInstChecks : List (MachineV r e) → List Term → (records now : Term) → Except Refusal (List (List InstCheck) × Term)
  | [], [], _, _ => pure ([], tt)
  | m :: ms, x :: xs, records, now => do
    let (inv, c0) ← m.invariants.code L
    let (cs, c1) ← encodeInstInvariants L T m inv x records now
    let (rest, c2) ← encodeInstChecks ms xs records now
    pure (cs :: rest, andT c0 (andT c1 c2))
  | _, _, _, _ => .error (.outside "machines and instance tables that differ in number")

/-- The names of the broken instance invariants the checks read from the model, machines in order. -/
def checksBroken (M : Model) (ms : List (MachineV r e)) (checks : List (List InstCheck)) : List String :=
  (ms.zip checks).flatMap fun (m, cs) => instBroken L T M m.key cs

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
    ∃ svX E, SlotsDen M (mo.starts.map fun w => (w.1, [w.2.1, w.2.2])) svX ∧
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
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L v.event (Ty.up _ hed ev) (evT.denote M)) :
    (ms : List (MachineV v.records v.event)) → (xs : List Term) → (sms : List (Step.MachineState v.records v.event)) →
    (outs : List ReactOut) → {c : Term} → MachinesRel M L T ms xs sms →
    (∀ m ∈ ms, m.key.orderable = true) → encodeMachines L ms xs records now evT = .ok (outs, c) →
    Holds M c →
      MachinesRel M L T ms (outs.map (·.table)) (sms.map fun ms0 => (Step.machineStep T recs tnow ev ms0).1)
  | [], [], [], outs, c, _, _, henc, _ => by
    simp only [encodeMachines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    trivial
  | m :: ms, x :: xs, sm :: sms, outs, c, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hor, henc, hc => by
    obtain ⟨⟨a, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨as, c2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    subst hsm
    obtain ⟨tbl', ht', hi'⟩ := machine_event (T := T) m (hor m (by simp)) recs tnow ev hrec hnow hevT tbl htbl h1 hc1
    refine ⟨⟨tbl', ht', ?_⟩, machines_event recs tnow ev hrd hed hrec hnow hevT ms xs sms as hrest
      (fun m' hm => hor m' (by simp [hm])) h2 hc2⟩
    rw [hi']; rfl
  | [], [], _ :: _, _, _, h, _, _, _ | [], _ :: _, _, _, _, h, _, _, _ | _ :: _, [], _, _, _, h, _, _, _
  | _ :: _, _ :: _, [], _, _, h, _, _, _ => h.elim

/-- The instance checks name the broken invariants of the machines the tables denote. -/
theorem instChecks_rel (recs : v.records.den0) (tnow : Int) {records now : Term} (hrd : v.records.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow) :
    (ms : List (MachineV v.records v.event)) → (xs : List Term) → (sms : List (Step.MachineState v.records v.event)) →
    MachinesRel M L T ms xs sms → (∀ m ∈ ms, m.key.ordered T = true) →
    {checks : List (List InstCheck)} → {c : Term} → encodeInstChecks L T ms xs records now = .ok (checks, c) →
    Holds M c → checksBroken L T M ms checks = instancesBroken recs tnow sms
  | [], [], [], _, _, checks, c, henc, _ => by
    simp only [encodeInstChecks, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    rfl
  | m :: ms, x :: xs, sm :: sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hord, checks, c, henc, hc => by
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
    have ih := instChecks_rel recs tnow hrd hrec hnow ms xs sms hrest (fun m' hm => hord m' (by simp [hm])) h3 hc2
    simp only [checksBroken, List.zip_cons_cons, List.flatMap_cons, instancesBroken] at ih ⊢
    rw [hb]
    exact congrArg _ ih
  | [], [], _ :: _, h, _, _, _, _, _ | [], _ :: _, _, h, _, _, _, _, _ | _ :: _, [], _, h, _, _, _, _, _
  | _ :: _, _ :: _, [], h, _, _, _, _, _ => h.elim

end

end Tazuna.Smt
