import Tazuna.Smt.Starts

/-! T2 for an event, with machines: the subscription wraps the value into an event, the records apply it, every
machine reacts (`encodeReact`), and the service's and every instance's invariants are checked on the result, in the
step's order (the service's first, then machines in declaration order, instances in key order). Each machine's part
also yields its start slots, the effects its instances start, which `Tazuna.Smt.Reactions` writes into the pending
table with the reactions' requests for T2 of the whole event step. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- What one machine's part of an event step encodes: its new instance table, the invariant checks of its slots and
its start slots. -/
structure MachineOut where
  table : Term
  checks : List InstCheck
  starts : List (Term × Term × Term)

/-- One machine's reaction to an event and its instances' invariants on the result, with their condition. -/
def encodeMachine (m : MachineV r e) (tbl records now ev : Term) : Except Refusal (MachineOut × Term) := do
  let (rc, c0) ← ReactCode.of L m
  let (o, c1) ← encodeReact L m rc tbl records now ev
  let (inv, c2) ← m.invariants.code L
  let (checks, c3) ← encodeInstInvariants L T m inv o.table records now
  pure (⟨o.table, checks, o.starts⟩, andT c0 (andT c1 (andT c2 c3)))

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

/-- An effect option that holds an effect relates the effect to a value. -/
theorem opt_some_rel {x : (Ty.dsl .effect [e]).den} {z : Val}
    (h : RelV L (Ty.option (.dsl .effect [e])) (.inl (x, ())) z) : ∃ zx, RelV L (.dsl .effect [e]) x zx := by
  obtain ⟨_, _, _, vals, -, v1, _, -, hx, -⟩ := h
  exact ⟨v1, hx⟩

/-- The start slots of one machine's part of an event step hold the effects its instances start. -/
theorem machine_starts (m : MachineV r e) (hor : m.key.orderable = true)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now evT : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L e (Ty.up _ m.event_data ev) (evT.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {mo : MachineOut} {c : Term} (henc : encodeMachine L T m x records now evT = .ok (mo, c)) (hc : Holds M c) :
    ∃ svX E, SlotsDen M (mo.starts.map fun w => (w.1, [w.2.1, w.2.2])) svX ∧
      Holds2 (EStart (L := L) m (instancesOf T m tbl) recs tnow ev) E svX ∧
      E.Perm (Ty.sortBy T m.key (dedupBy (Ty.semWith Dsl.base m.key).2 (m.instances.fn (recs, ())))) := by
  obtain ⟨⟨rc, c0⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨inv, c2⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, c3⟩, h4, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hc0, hc123⟩ := (holds_andT _ _).1 hc
  obtain ⟨hc1, -⟩ := (holds_andT _ _).1 hc123
  exact (react_step (T := T) m hor h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2 hc1).2

/-- T2 for one machine's part of an event step: wherever the condition holds, its new table term denotes the
instances after the step, and the names read from the model are the broken invariants of those instances in key
order. -/
theorem machine_event (m : MachineV r e) (hor : m.key.orderable = true) (hko : m.key.ordered T = true)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now evT : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L e (Ty.up _ m.event_data ev) (evT.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {mo : MachineOut} {c : Term} (henc : encodeMachine L T m x records now evT = .ok (mo, c)) (hc : Holds M c) :
    ∃ tbl', RelV L m.table (Ty.up _ m.table_data tbl') (mo.table.denote M) ∧
      instancesOf T m tbl' = (Step.machineStep T recs tnow ev ⟨m, instancesOf T m tbl⟩).1.2 ∧
      instBroken L T M m.key mo.checks =
        (instancesOf T m tbl').flatMap fun i => Step.broken (m.invariants.fn (.inl (i.key, i.state, recs, tnow, ()), ())) := by
  obtain ⟨⟨rc, c0⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨inv, c2⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, c3⟩, h4, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hc0, hc123⟩ := (holds_andT _ _).1 hc
  obtain ⟨hc1, hc23⟩ := (holds_andT _ _).1 hc123
  obtain ⟨hc2, hc3⟩ := (holds_andT _ _).1 hc23
  obtain ⟨⟨tbl', ht', hi'⟩, -⟩ := react_step (T := T) m hor h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2 hc1
  have hinv := m.invariants.code_fn m.inv_data h3 hc2
  exact ⟨tbl', ht', hi', instBroken_eq m hko hinv recs tnow hrec hnow tbl' ht' h4 hc3⟩

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- The broken invariants of machines' instances, machines in order and instances in key order, as the step lists
them. -/
def instancesBroken (recs : v.records.den0) (tnow : Int) (sms : List (Step.MachineState v.records v.event)) :
    List String :=
  sms.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => Step.broken (m.invariants.fn (.inl (i.key, i.state, recs, tnow, ()), ()))

/-- T2 for the machines' part of an event step: wherever the condition holds, the new tables denote the machines
after the step, and the names read from the model are their broken invariants in the step's order. -/
theorem machines_event (recs : v.records.den0) (tnow : Int) (ev : v.event.den0) {records now evT : Term}
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L v.event (Ty.up _ hed ev) (evT.denote M)) :
    (ms : List (MachineV v.records v.event)) → (xs : List Term) → (sms : List (Step.MachineState v.records v.event)) →
    (outs : List MachineOut) → {c : Term} → MachinesRel M L T ms xs sms →
    (∀ m ∈ ms, m.key.orderable = true ∧ m.key.ordered T = true) → encodeMachines L T ms xs records now evT = .ok (outs, c) →
    Holds M c →
      MachinesRel M L T ms (outs.map (·.table)) (sms.map fun ms0 => (Step.machineStep T recs tnow ev ms0).1) ∧
      machinesBroken L T M ms outs = instancesBroken recs tnow (sms.map fun ms0 => (Step.machineStep T recs tnow ev ms0).1)
  | [], [], [], outs, c, _, _, henc, _ => by
    simp only [encodeMachines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    exact ⟨trivial, rfl⟩
  | m :: ms, x :: xs, sm :: sms, outs, c, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hor, henc, hc => by
    obtain ⟨⟨a, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨as, c2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    obtain ⟨hor1, hko1⟩ := hor m (by simp)
    subst hsm
    obtain ⟨tbl', ht', hi', hb⟩ := machine_event (T := T) m hor1 hko1 recs tnow ev hrec hnow hevT tbl htbl h1 hc1
    obtain ⟨hrel, hbs⟩ := machines_event recs tnow ev hrd hed hrec hnow hevT ms xs sms as hrest
      (fun m' hm => hor m' (by simp [hm])) h2 hc2
    refine ⟨⟨⟨tbl', ht', ?_⟩, hrel⟩, ?_⟩
    · rw [hi']; rfl
    · simp only [machinesBroken, List.zip_cons_cons, List.flatMap_cons, List.map_cons, instancesBroken] at hbs ⊢
      rw [hb, hi']
      exact congrArg _ hbs
  | [], [], _ :: _, _, _, h, _, _, _ | [], _ :: _, _, _, _, h, _, _, _ | _ :: _, [], _, _, _, h, _, _, _
  | _ :: _, _ :: _, [], _, _, h, _, _, _ => h.elim

end

end Tazuna.Smt
