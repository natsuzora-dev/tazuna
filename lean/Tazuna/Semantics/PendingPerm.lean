import Tazuna.Semantics.PendingInv

/-! Pending requests form a multiset: a step reads them only by wire id (an answer looks its request up by `to` and
drops it) and otherwise only appends. So two states that differ only in the order of their pending requests step to
results that differ only in that order (`step_perm`), as long as wire ids are distinct, which every reachable state
keeps (`Inv.nodup`). This is what lets step theorems that state pending only up to permutation chain (`run_perm`). -/

namespace Tazuna.Ir

variable {v : ServiceV}

def State.prepend (q : Step.Bag (Step.Pending v.event)) (s : State v) : State v := { s with pending := q ++ s.pending }

/-- The same state up to the order of pending requests. -/
def State.Equiv (s t : State v) : Prop :=
  ({ s with pending := [] } : State v) = { t with pending := [] } ∧ s.pending.Perm t.pending

/-- The same result up to the order of the next state's pending requests. -/
def Result.Equiv (r r' : Result v) : Prop :=
  r.state.Equiv r'.state ∧ r.outcome = r'.outcome ∧ r.events = r'.events ∧ r.out = r'.out

@[simp] theorem State.prepend_records (s : State v) (q) : (s.prepend q).records = s.records := rfl
@[simp] theorem State.prepend_machines (s : State v) (q) : (s.prepend q).machines = s.machines := rfl
@[simp] theorem State.prepend_now (s : State v) (q) : (s.prepend q).now = s.now := rfl
@[simp] theorem State.prepend_fresh (s : State v) (q) : (s.prepend q).fresh = s.fresh := rfl
@[simp] theorem State.prepend_nextId (s : State v) (q) : (s.prepend q).nextId = s.nextId := rfl

theorem State.Equiv.prepend {s : State v} {q q' : Step.Bag (Step.Pending v.event)} (h : q.Perm q') :
    (s.prepend q).Equiv (s.prepend q') := ⟨rfl, h.append_right _⟩

theorem State.prepend_base (s : State v) : s = ({ s with pending := [] } : State v).prepend s.pending := by
  cases s; simp [State.prepend]

theorem State.Equiv.base {s t : State v} (h : s.Equiv t) :
    s = ({ s with pending := [] } : State v).prepend s.pending ∧
      t = ({ s with pending := [] } : State v).prepend t.pending :=
  ⟨State.prepend_base s, h.1 ▸ State.prepend_base t⟩

namespace Step

def Acc.prepend (q : Bag (Pending v.event)) (a : Acc v) : Acc v := { a with state := a.state.prepend q }

@[simp] theorem Acc.prepend_state (a : Acc v) (q : Bag (Pending v.event)) : (a.prepend q).state = a.state.prepend q :=
  rfl

theorem ctx_prepend {r i c : Ty} (s : State v) (q : Bag (Pending v.event)) :
    ctx (r := r) (i := i) (c := c) (s.prepend q) = ctx s := rfl

theorem foldlM_map_comm {ε α β : Type} (g : α → β → Except ε α) (h : α → α) (hg : ∀ a x, g (h a) x = (g a x).map h) :
    (xs : List β) → (a : α) → xs.foldlM g (h a) = (xs.foldlM g a).map h
  | [], _ => rfl
  | x :: xs, a => by
    simp only [List.foldlM_cons, hg, bind, Except.bind, Except.map]
    cases g a x with
    | error e => rfl
    | ok a' => exact foldlM_map_comm g h hg xs a'

theorem map_bind_comm {ε α β : Type} (x : Except ε α) (f : α → α) (g g' : α → Except ε β) (h : β → β)
    (hg : ∀ a, g (f a) = (g' a).map h) : (x.map f >>= g) = (x >>= g').map h := by
  cases x <;> simp [Except.map, bind, Except.bind, hg]

theorem start_prepend (q : Bag (Pending v.event)) (effs : List (Sender × EffectV v.event)) (a : Acc v) :
    start (a.prepend q) effs = (start a effs).map (Acc.prepend q) := by
  refine foldlM_map_comm _ (Acc.prepend q) ?_ effs a
  rintro a ⟨snd, eff⟩
  cases eff with
  | request r =>
    dsimp only
    split
    · rfl
    · simp [Except.map, Acc.prepend, State.prepend]
  | command => rfl
  | query => rfl

theorem applyEvents_prepend (T : List TypeDecl) (q : Bag (Pending v.event)) (events : List v.event.den0)
    (a : Acc v) : applyEvents T (a.prepend q) events = (applyEvents T a events).map (Acc.prepend q) :=
  by
    unfold applyEvents
    refine foldlM_map_comm _ (Acc.prepend q) (fun a ev => ?_) events a
    exact start_prepend q (react T a.state ev).2 { a with state := (react T a.state ev).1, events := a.events ++ [ev] }

/-- A command's run with `f` applied to the step in progress it leaves. -/
def Ran.map {j : Ty} (f : Acc v → Acc v) : Ran v j → Ran v j
  | .invalid rs => .invalid rs
  | .rejected a k => .rejected (f a) k
  | .accepted a => .accepted (f a)

theorem execCommand_prepend (T : List TypeDecl) (q : Bag (Pending v.event)) (a : Acc v)
    (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0) :
    execCommand T (a.prepend q) x caller input = (execCommand T a x caller input).map (Ran.map (Acc.prepend q)) := by
  unfold execCommand
  rw [show ctx (a.prepend q).state (a.prepend q).state.records caller input = ctx a.state a.state.records caller input
    from rfl]
  split
  · rfl
  · simp only
    split
    · rw [show ({ a.prepend q with state := { (a.prepend q).state with fresh := (a.prepend q).state.fresh + 1 } } : Acc v)
          = Acc.prepend q { a with state := { a.state with fresh := a.state.fresh + 1 } } from rfl]
      erw [applyEvents_prepend T q]
      refine map_bind_comm _ _ _ _ _ fun a1 => ?_
      rw [show (Acc.prepend q a1).state.records = a1.state.records from rfl]
      split <;> rfl
    · rfl

theorem runCommand_prepend (T : List TypeDecl) (q : Bag (Pending v.event)) (a : Acc v)
    (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (onAnswer : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) :
    runCommand T (a.prepend q) x caller input onAnswer = (runCommand T a x caller input onAnswer).map (Acc.prepend q) := by
  unfold runCommand
  rw [execCommand_prepend]
  refine map_bind_comm _ _ _ _ _ fun r => ?_
  cases r with
  | invalid => rfl
  | accepted a1 => exact applyEvents_prepend T q _ a1
  | rejected a1 j => exact applyEvents_prepend T q _ a1

theorem execQuery_prepend (q : Bag (Pending v.event)) (s : State v) (x : QueryV v.records v.caller)
    (caller : v.caller.den0) (input : x.input.den0) : execQuery (s.prepend q) x caller input = execQuery s x caller input :=
  rfl

theorem runQuery_prepend (T : List TypeDecl) (q : Bag (Pending v.event)) (a : Acc v) (x : QueryV v.records v.caller)
    (caller : v.caller.den0) (input : x.input.den0) (onAnswer : Fun (Ty.fn [x.output] (.list v.event))) :
    runQuery T (a.prepend q) x caller input onAnswer = (runQuery T a x caller input onAnswer).map (Acc.prepend q) := by
  unfold runQuery
  rw [Acc.prepend_state, execQuery_prepend]
  split
  · rfl
  · exact applyEvents_prepend T q _ _

theorem runOwn_prepend (T : List TypeDecl) (q : Bag (Pending v.event)) (a : Acc v) (eff : EffectV v.event) :
    runOwn T (a.prepend q) eff = (runOwn T a eff).map (Acc.prepend q) := by
  cases eff with
  | request => rfl
  | command name c i j caller value onAnswer =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    cases oc with
    | none => rfl
    | some hc =>
      generalize ownCommand (v := v) name i j = ox
      cases ox with
      | none => rfl
      | some x =>
        obtain ⟨hc⟩ := hc
        obtain ⟨x, hi, hj⟩ := x
        exact runCommand_prepend T q a x _ _ _
  | query name c i o caller value onAnswer =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    cases oc with
    | none => rfl
    | some hc =>
      generalize ownQuery (v := v) name i o = ox
      cases ox with
      | none => rfl
      | some x =>
        obtain ⟨hc⟩ := hc
        obtain ⟨x, hi, ho⟩ := x
        exact runQuery_prepend T q a x _ _ _

theorem settle_prepend (T : List TypeDecl) (q : Bag (Pending v.event)) :
    (fuel : Nat) → (a : Acc v) → settle T fuel (a.prepend q) = (settle T fuel a).map (Acc.prepend q)
  | fuel, a => by
    unfold settle
    simp only [show (a.prepend q).own = a.own from rfl]
    cases hown : a.own with
    | nil => rfl
    | cons eff rest =>
      cases fuel with
      | zero => rfl
      | succ f =>
        simp only
        rw [show ({ a.prepend q with own := rest } : Acc v) = Acc.prepend q { a with own := rest } from rfl,
          runOwn_prepend]
        exact map_bind_comm _ _ _ _ _ fun a1 => settle_prepend T q f a1

theorem fire_prepend (q : Bag (Pending v.event)) :
    (fuel : Nat) → (s : State v) → fire (s.prepend q) fuel = (fire s fuel).map fun r => (r.1.prepend q, r.2)
  | 0, _ => rfl
  | fuel + 1, s => by
    simp only [fire, State.prepend]
    split
    · rfl
    · generalize fireMachines s.records s.now _ false s.machines = R
      have hR : ({ records := s.records, machines := R.1, pending := q ++ s.pending, now := s.now,
                   fresh := s.fresh, nextId := s.nextId } : State v) = State.prepend q { s with machines := R.1 } := rfl
      rw [hR, fire_prepend q fuel]
      simp only [Option.map_map]
      rfl

theorem finish_equiv (T : List TypeDecl) {s0 s0' : State v} (hs : s0.Equiv s0') (x : Except Fault (Acc v))
    {q q' : Bag (Pending v.event)} (hq : q.Perm q') (o : Outcome) :
    (finish T s0 (x.map (Acc.prepend q)) o).Equiv (finish T s0' (x.map (Acc.prepend q')) o) := by
  have h : ∀ q, (x.map (Acc.prepend q) >>= settle T v.bounds.cascadeNat) =
      (x >>= settle T v.bounds.cascadeNat).map (Acc.prepend q) := fun q => by
    cases x with
    | error => rfl
    | ok a => exact settle_prepend T q _ a
  unfold finish
  rw [h, h]
  cases x >>= settle T v.bounds.cascadeNat with
  | error => exact ⟨hs, rfl, rfl, rfl⟩
  | ok a =>
    have hi : ∀ q, invariants (a.prepend q).state = invariants a.state := fun _ => rfl
    simp only [Except.map, hi]
    cases invariants a.state with
    | cons => exact ⟨hs, rfl, rfl, rfl⟩
    | nil => exact ⟨State.Equiv.prepend hq, rfl, rfl, rfl⟩

end Step

open Step

/-- A step does not depend on the order of pending requests. -/
theorem step_perm (T : List TypeDecl) {v : ServiceV} {s t : State v} (h : s.Equiv t)
    (hn : (s.pending.map (·.id)).Nodup) (i : Input v) : (step T v s i).Equiv (step T v t i) := by
  obtain ⟨hs, ht⟩ := h.base
  have he0 : ({ s with pending := [] } : State v).pending = [] := rfl
  generalize ({ s with pending := [] } : State v) = e at hs ht he0
  have hp := h.2
  generalize s.pending = p at hs hp hn
  generalize t.pending = p' at ht hp
  subst hs ht
  have hres : ∀ (st : State v) (o : Outcome) (q q' : Bag (Pending v.event)), q.Perm q' →
      (⟨st.prepend q, o, [], []⟩ : Result v).Equiv ⟨st.prepend q', o, [], []⟩ :=
    fun _ _ _ _ hq => ⟨State.Equiv.prepend hq, rfl, rfl, rfl⟩
  have hacc : ∀ q, ({ state := { e with fresh := e.fresh + 1, pending := (State.prepend q e).pending } } : Acc v) =
      Acc.prepend q { state := { e with fresh := e.fresh + 1 } } := fun _ => rfl
  cases i with
  | command i caller input =>
    simp only [step]
    rw [show ({ state := e.prepend p } : Acc v) = Acc.prepend p { state := e } from rfl,
      show ({ state := e.prepend p' } : Acc v) = Acc.prepend p' { state := e } from rfl,
      execCommand_prepend, execCommand_prepend]
    cases execCommand T { state := e } (v.commands.get i) caller input with
    | error => exact hres { e with fresh := e.fresh + 1 } _ p p' hp
    | ok r =>
      cases r with
      | invalid => exact hres { e with fresh := e.fresh + 1 } _ p p' hp
      | rejected => exact hres { e with fresh := e.fresh + 1 } _ p p' hp
      | accepted a => exact finish_equiv T (State.Equiv.prepend (s := { e with fresh := e.fresh + 1 }) hp) (.ok a) hp _
  | query i caller input =>
    simp only [step, execQuery_prepend]
    split
    · exact hres e _ p p' hp
    · exact hres e _ p p' hp
  | answer to w =>
    obtain ⟨ty, value⟩ := w
    have hf : (e.prepend p).pending.find? (·.id == to) = (e.prepend p').pending.find? (·.id == to) := by
      refine find?_perm_unique (hp.append_right _) fun a ha b hb hav hbv => ?_
      have hn' : ((e.prepend p).pending.map (·.id)).Nodup := by simpa [State.prepend, he0] using hn
      simp only [beq_iff_eq] at hav hbv
      exact nodup_map_inj _ _ hn' ha hb (hav.trans hbv.symm)
    have hacc2 : ∀ q, ({ state := { e with pending := (State.prepend q e).pending.filter (·.id != to) } } : Acc v) =
        Acc.prepend (q.filter (·.id != to)) { state := e } := by
      intro q; simp [Acc.prepend, State.prepend, he0]
    simp only [step, State.prepend_records, State.prepend_now, State.prepend_fresh, State.prepend_machines,
      State.prepend_nextId]
    rw [← hf]
    split
    · exact hres e _ p p' hp
    · split
      · exact hres e _ p p' hp
      · split
        · exact hres e _ p p' hp
        · rw [hacc2, hacc2]
          erw [applyEvents_prepend, applyEvents_prepend]
          exact finish_equiv T (State.Equiv.prepend (s := e) hp) _ (hp.filter _) _
  | event i value =>
    simp only [step]
    rw [show ({ state := e.prepend p } : Acc v) = Acc.prepend p { state := e } from rfl,
      show ({ state := e.prepend p' } : Acc v) = Acc.prepend p' { state := e } from rfl,
      applyEvents_prepend, applyEvents_prepend]
    exact finish_equiv T (State.Equiv.prepend hp) _ hp _
  | clock time =>
    have hnow : ∀ q, ({ e with now := time, pending := (State.prepend q e).pending } : State v) =
        State.prepend q { e with now := time } := fun _ => rfl
    simp only [step, State.prepend_records, State.prepend_now, State.prepend_fresh, State.prepend_machines,
      State.prepend_nextId]
    by_cases ht : time < e.now
    · simp only [ht, ite_true]; exact hres e _ p p' hp
    · simp only [ht, ite_false]
      rw [hnow, hnow, fire_prepend, fire_prepend]
      cases fire { e with now := time } (v.bounds.cascadeNat + 1) with
      | none => exact hres e _ p p' hp
      | some r =>
        obtain ⟨s', effs⟩ := r
        simp only [Option.map]
        rw [show ({ state := State.prepend p s' } : Acc v) = Acc.prepend p { state := s' } from rfl,
          show ({ state := State.prepend p' s' } : Acc v) = Acc.prepend p' { state := s' } from rfl,
          start_prepend, start_prepend]
        exact finish_equiv T (State.Equiv.prepend (s := e) hp) _ hp _

/-- Runs from two states equal up to the order of pending requests agree step by step up to that order. -/
theorem run_perm (T : List TypeDecl) {P : List AnySite} {E : List AnyEffectSite} {v : ServiceV} (hv : v.Reach P E) :
    {s t : State v} → s.Equiv t → Inv P s → (is : List (Input v)) →
      (run T v s is).1.Equiv (run T v t is).1 ∧
        ∀ x ∈ (run T v s is).2.zip (run T v t is).2, x.1.Equiv x.2
  | _, _, h, _, [] => ⟨h, nofun⟩
  | s, t, h, hs, i :: is => by
    have hr := step_perm T h hs.nodup i
    obtain ⟨h1, h2⟩ := run_perm T hv hr.1 (step_inv T hv s hs i) is
    refine ⟨h1, fun x hx => ?_⟩
    simp only [run, List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hr
    · exact h2 x hx

end Tazuna.Ir
