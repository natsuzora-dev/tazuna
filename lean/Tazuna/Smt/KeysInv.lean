import Tazuna.Smt.Instances
import Tazuna.Semantics.PendingInv

/-! Every step keeps each machine's instances in the step's form (`InstancesOk`: in the canonical order of their keys,
no key twice) when the keys' type is ordered, which check requires (`Illegal.machineKey`). So the symbolic state's
completeness (T3) needs no assumption about instances for any state a run reaches. -/

namespace Tazuna.Ir

section
variable (T : List TypeDecl) {r e : Ty}

/-- The step's form says only something about the keys. -/
theorem instancesOk_iff_keys (m : MachineV r e) (insts : List (Step.Instance m)) :
    InstancesOk T m insts ↔ (insts.map (·.key)).Pairwise (fun a b => (Ty.cmp T m.key a b).isLE = true) ∧
      (insts.map (·.key)).Pairwise (fun a b =>
        (Ty.semWith Dsl.base m.key).2 a b = false ∧ (Ty.semWith Dsl.base m.key).2 b a = false) := by
  unfold InstancesOk KeysUnique instEntries keyLE
  simp only [List.pairwise_map]

theorem instancesOk_keys (m : MachineV r e) {l l' : List (Step.Instance m)} (h : l'.map (·.key) = l.map (·.key))
    (hl : InstancesOk T m l) : InstancesOk T m l' := by
  rw [instancesOk_iff_keys] at hl ⊢; rw [h]; exact hl

theorem instancesOk_of_lt (m : MachineV r e) (ho : m.key.ordered T = true) {insts : List (Step.Instance m)}
    (h : (insts.map (·.key)).Pairwise fun a b => Ty.cmp T m.key a b = .lt) : InstancesOk T m insts := by
  rw [instancesOk_iff_keys]
  refine ⟨h.imp fun h => by simp [h], h.imp fun {a b} hab => ⟨?_, ?_⟩⟩
  · cases hq : (Ty.semWith Dsl.base m.key).2 a b
    · rfl
    · rw [(Ty.cmp_eq_iff T ho _ _).2 hq] at hab; cases hab
  · cases hq : (Ty.semWith Dsl.base m.key).2 b a
    · rfl
    · rw [Std.OrientedCmp.eq_swap (cmp := Ty.cmp T m.key), (Ty.cmp_eq_iff T ho _ _).2 hq] at hab
      simp [Ordering.swap] at hab

theorem reactKey_erl (m : MachineV r e) (ho : m.key.ordered T = true) (insts : List (Step.Instance m))
    (records : r.den0) (now : Int) (ev : e.den0) (k : m.key.den0) :
    Ty.erl T m.key (Step.reactKey m insts records now ev k).1.key = Ty.erl T m.key k := by
  unfold Step.reactKey
  split
  · rename_i i hi
    have hk : (Ty.semWith Dsl.base m.key).2 k i.key = true := by simpa using List.find?_some hi
    have := (Ty.erl_iff T m.key ho _ _).1 hk
    split <;> exact this.symm
  · rfl

theorem machineStep_ok (records : r.den0) (now : Int) (ev : e.den0) (m : MachineV r e) (ho : m.key.ordered T = true)
    (insts : List (Step.Instance m)) : InstancesOk T m (Step.machineStep T records now ev m insts).1 := by
  apply instancesOk_of_lt T m ho
  simp only [Step.machineStep, List.map_map]
  rw [List.pairwise_map]
  refine (sortBy_dedup_lt T ho (m.instances.fn (records, ()))).imp fun {a b} hab => ?_
  simp only [Function.comp_def, Ty.cmp] at hab ⊢
  rw [reactKey_erl T m ho, reactKey_erl T m ho]; exact hab

end

namespace Step

variable (T : List TypeDecl) {v : ServiceV}

/-- Every machine's key type is ordered and its instances are in the step's form. -/
def KeysOk (s : State v) : Prop := ∀ sm ∈ s.machines.toSigma, sm.1.key.ordered T = true ∧ InstancesOk T sm.1 sm.2

theorem KeysOk.congr {s s' : State v} (h : KeysOk T s) (hm : s'.machines = s.machines) : KeysOk T s' :=
  fun sm hsm => h sm (hm ▸ hsm)

theorem init_keys (hord : ∀ m ∈ v.machines, m.key.ordered T = true) : KeysOk T (State.init v) := by
  intro sm h
  simp only [State.init, PerMachine.toSigma_ofFn, List.mem_map] at h
  obtain ⟨m, hm, rfl⟩ := h
  exact ⟨hord m hm, .nil, .nil⟩

theorem start_machines (a : Acc v) (effs : List (Sender × EffectV v.event)) {a' : Acc v} (h : start a effs = .ok a') :
    a'.state.machines = a.state.machines := by
  induction effs generalizing a with
  | nil => simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; rw [h]
  | cons x effs ih =>
    obtain ⟨snd, eff⟩ := x
    simp only [start, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      rw [ih a1 h]
      revert h1
      cases eff with
      | request r =>
        simp only
        split
        · intro h1; cases h1
        · intro h1; cases h1; rfl
      | command => intro h1; cases h1; rfl
      | query => intro h1; cases h1; rfl

theorem react_keys (s : State v) (ev : v.event.den0) (hs : KeysOk T s) : KeysOk T (react T s ev).1 := by
  intro sm' hsm'
  simp only [react, (reactMachines_toSigma T _ s.now ev s.machines).1, List.mem_map] at hsm'
  obtain ⟨sm, hsm, rfl⟩ := hsm'
  exact ⟨(hs sm hsm).1, machineStep_ok T _ s.now ev sm.1 (hs sm hsm).1 sm.2⟩

theorem applyEvents_keys (events : List v.event.den0) :
    (a : Acc v) → KeysOk T a.state → {a' : Acc v} → applyEvents T a events = .ok a' → KeysOk T a'.state := by
  induction events with
  | nil => intro a ha a' h; simp only [applyEvents, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ ha
  | cons ev events ih =>
    intro a ha a' h
    simp only [applyEvents, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      exact ih a1 ((react_keys T a.state ev ha).congr T (start_machines _ _ h1)) h

theorem execCommand_keys (a : Acc v) (ha : KeysOk T a.state) (x : CommandV v.records v.event v.caller)
    (caller : (Ty.origin v.caller).den0) (input : x.input.den0) {r : Ran v x.rejection} (h : execCommand T a x caller input = .ok r)
    (a' : Acc v) (ha' : r = .accepted a' ∨ ∃ j, r = .rejected a' j) : KeysOk T a'.state := by
  rcases execCommand_acc T a x caller input h a' ha' with rfl | ⟨_, he⟩
  · exact ha
  · exact applyEvents_keys T _ { a with state := { a.state with fresh := a.state.fresh + 1 } } ha he

theorem runOwn_keys (a : Acc v) (ha : KeysOk T a.state) (eff : OwnEffectV v.event) {a' : Acc v}
    (h : runOwn T a eff = .ok a') : KeysOk T a'.state := by
  have hcmd : ∀ (x : CommandV v.records v.event v.caller) caller input onAnswer {a' : Acc v},
      runCommand T a x caller input onAnswer = .ok a' → KeysOk T a'.state := by
    intro x caller input onAnswer a' h
    simp only [runCommand, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      have hk := execCommand_keys T a ha x caller input hr
      split at h
      · cases h
      · exact applyEvents_keys T _ _ (hk _ (.inl rfl)) h
      · exact applyEvents_keys T _ _ (hk _ (.inr ⟨_, rfl⟩)) h
  have hqry : ∀ (x : QueryV v.records v.caller) caller input onAnswer {a' : Acc v},
      runQuery T a x caller input onAnswer = .ok a' → KeysOk T a'.state := by
    intro x caller input onAnswer a' h
    simp only [runQuery] at h
    split at h
    · cases h
    · exact applyEvents_keys T _ { a with state := { a.state with fresh := a.state.fresh + 1 } } ha h
  revert h
  cases eff with
  | command name c i j value onAnswer =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    cases oc with
    | none => intro h; cases h
    | some hc =>
      generalize ownCommand (v := v) name i j = ox
      cases ox with
      | none => intro h; cases h
      | some x =>
        obtain ⟨hc⟩ := hc
        obtain ⟨x, hi, hj⟩ := x
        exact fun h => hcmd x _ _ _ h
  | query name c i o value onAnswer =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    cases oc with
    | none => intro h; cases h
    | some hc =>
      generalize ownQuery (v := v) name i o = ox
      cases ox with
      | none => intro h; cases h
      | some x =>
        obtain ⟨hc⟩ := hc
        obtain ⟨x, hi, ho⟩ := x
        exact fun h => hqry x _ _ _ h

theorem settle_keys : (fuel : Nat) → (a : Acc v) → KeysOk T a.state → {a' : Acc v} → settle T fuel a = .ok a' →
    KeysOk T a'.state
  | fuel, a, ha, a', h => by
    unfold settle at h
    split at h
    · simp only [Except.ok.injEq] at h; exact h ▸ ha
    · cases h
    · rename_i eff rest f _
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i a1 h1
        exact settle_keys f a1 (runOwn_keys T { a with own := rest } ha eff h1) h

theorem finish_keys (s0 : State v) (hs : KeysOk T s0) (x : Except Fault (Acc v))
    (hx : ∀ a, x = .ok a → KeysOk T a.state) (o : Outcome) : KeysOk T (finish T s0 x o).state := by
  unfold finish
  split
  · exact hs
  · rename_i a ha
    split
    · exact hs
    · cases x with
      | error e => cases ha
      | ok a0 => exact settle_keys T _ a0 (hx a0 rfl) ha

theorem fire_keys (s : State v) (hs : KeysOk T s) : (fuel : Nat) → {r : State v × List (Sender × EffectV v.event)} →
    fire s fuel = some r → KeysOk T r.1
  | 0, _, h => by cases h
  | fuel + 1, r, h => by
    rw [fire] at h
    split at h
    · cases h; exact hs
    · rename_i d _
      obtain ⟨⟨s', es⟩, hr, rfl⟩ := Option.map_eq_some_iff.1 h
      refine fire_keys { s with machines := (fireMachines s.records s.now d false s.machines).1 } ?_ fuel (r := (s', es)) hr
      intro sm' hsm'
      obtain ⟨sm, hsm, he | rfl⟩ := mem_fireMachines s.records s.now d false s.machines sm' hsm'
      · exact he ▸ hs sm hsm
      · exact ⟨(hs sm hsm).1, instancesOk_keys T sm.1 (fireFirst_keys sm.1 _ _ _ sm.2) (hs sm hsm).2⟩

end Step

open Step

/-- Every step keeps each machine's instances in the step's form. -/
theorem step_keys (T : List TypeDecl) {v : ServiceV} (s : State v) (hs : KeysOk T s) (i : Input v) :
    KeysOk T (step T v s i).state := by
  cases i with
  | command i caller input =>
    simp only [step]
    split
    · exact hs
    · exact hs
    · exact hs
    · rename_i a ha
      exact finish_keys T { s with fresh := s.fresh + 1 } hs (.ok a) (fun a' h => by
        cases h; exact execCommand_keys T _ hs _ _ _ ha _ (.inl rfl)) _
  | query i caller input =>
    simp only [step]
    split <;> exact hs
  | answer to w =>
    obtain ⟨t, value⟩ := w
    simp only [step]
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact hs
        · exact finish_keys T _ hs _ (fun a h => applyEvents_keys T _ _ hs h) _
  | event i value => exact finish_keys T _ hs _ (fun a h => applyEvents_keys T _ _ hs h) _
  | clock time =>
    simp only [step]
    split
    · exact hs
    · split
      · exact hs
      · rename_i s' effs hr
        exact finish_keys T _ hs _ (fun a h =>
          (fire_keys T { s with now := time } hs _ hr).congr T (start_machines { state := s' } effs h)) _

/-- Every state a run reaches from a state whose instances are in the step's form keeps them so. -/
theorem run_keys (T : List TypeDecl) {v : ServiceV} :
    (s : State v) → KeysOk T s → (is : List (Input v)) → KeysOk T (run T v s is).1
  | _, hs, [] => hs
  | s, hs, i :: is => run_keys T _ (step_keys T s hs i) is

end Tazuna.Ir
