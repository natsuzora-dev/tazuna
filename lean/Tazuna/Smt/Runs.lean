import Tazuna.Smt.Lines

/-! T5 from the lines for runs: the cascades `cascade_lines` and `cascade_within` speak about are every cascade a run
from the initial state on valid inputs starts. Each step of such a run keeps the run's invariants (wire ids below the
next, names below the counter, the program's sites, instances in the step's form), and a cascade starts (`Step.Begins`)
with what a pair question assumes of its state (`begins_keeps`). The timers of a clock line need no invariant: a timer
question is asked over a free context. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {v : ServiceV}

/-- A cascade a step on a valid input starts keeps what a pair question assumes of its state, where the state the step
starts from keeps the run's invariants. -/
theorem begins_keeps (c : CheckedSpec) (hv : v ∈ c.spec.services) {s : State v} (hinv : Step.Inv c.P s)
    (hs : Step.StateSupp s) (hk : Step.KeysOk c.T s) {x : Input v} (hx : x.Valid s) {a : Step.Acc v}
    (h : Step.Begins c.T s x a) : Lines.Keeps c.T c.P a := by
  have hr := (c.checked v hv).reach
  obtain ⟨hsupp, hpend⟩ := Step.begins_supp c.T (c.equivariant v hv) (c.states hv) hs hinv.below hx h
  have hnil : ∀ s' : State v, Step.QueueOk c.P ({ state := s' } : Step.Acc v) := fun _ x hx => nomatch hx
  refine ⟨hsupp, ?_, ?_, ?_, hpend⟩
  · cases h with
    | command i caller input a h => exact Step.execCommand_inv c.T hr _ hinv _ _ _ h a (.inl rfl)
    | answer to value p h a hp _ happ =>
      refine Step.applyEvents_inv c.T hr _ _ ?_ happ
      refine ⟨fun p hp => hinv.below p (List.mem_filter.1 hp).1, ?_, fun p hp => hinv.reach p (List.mem_filter.1 hp).1,
        fun p hp => hinv.shaped p (List.mem_filter.1 hp).1⟩
      exact (List.filter_sublist.map _).nodup hinv.nodup
    | event i value a h => exact Step.applyEvents_inv c.T hr _ _ hinv h
    | clock time s' effs a _ hf h =>
      have hf' := Step.fire_inv hr.1 { s with now := time } (Step.Inv.congr hinv rfl rfl) _ hf
      exact Step.start_inv { state := s' } effs hf'.1 hf'.2.1 hf'.2.2 h
  · cases h with
    | command i caller input a h =>
      rcases Step.execCommand_acc c.T _ _ _ _ h a (.inl rfl) with rfl | ⟨evs, he⟩
      · exact hnil _
      · exact Step.applyEvents_queue c.T hr evs _ he (Step.Inv.congr hinv rfl rfl) (hnil _)
    | answer to value p h a hp _ happ =>
      refine Step.applyEvents_queue c.T hr _ _ happ ?_ (hnil _)
      refine ⟨fun p hp => hinv.below p (List.mem_filter.1 hp).1, ?_, fun p hp => hinv.reach p (List.mem_filter.1 hp).1,
        fun p hp => hinv.shaped p (List.mem_filter.1 hp).1⟩
      exact (List.filter_sublist.map _).nodup hinv.nodup
    | event i value a h => exact Step.applyEvents_queue c.T hr _ _ h hinv (hnil _)
    | clock time s' effs a _ hf h =>
      have hf' := Step.fire_inv hr.1 { s with now := time } (Step.Inv.congr hinv rfl rfl) _ hf
      exact Step.start_queue { state := s' } effs h (hnil _) hf'.2.1
  · cases h with
    | command i caller input a h => exact Step.execCommand_keys c.T _ hk _ _ _ h a (.inl rfl)
    | answer to value p h a hp _ happ => exact Step.applyEvents_keys c.T _ _ hk happ
    | event i value a h => exact Step.applyEvents_keys c.T _ _ hk h
    | clock time s' effs a _ hf h =>
      exact (Step.fire_keys c.T { s with now := time } hk _ hf).congr c.T (Step.start_machines { state := s' } effs h)

/-- The state a run on valid inputs reaches from the initial state keeps the run's invariants. -/
theorem run_keeps (c : CheckedSpec) (hv : v ∈ c.spec.services) {xs : List (Input v)}
    (hxs : Step.ValidRun c.T (Step.State.init v) xs) :
    Step.Inv c.P (run c.T v (Step.State.init v) xs).1 ∧ Step.StateSupp (run c.T v (Step.State.init v) xs).1 ∧
      Step.KeysOk c.T (run c.T v (Step.State.init v) xs).1 := by
  have he := c.equivariant v hv
  have hr := (c.checked v hv).reach
  exact ⟨run_inv c.T hr _ Step.init_inv xs,
    Step.run_supp c.T he (c.states hv) hr _ Step.init_inv (Step.init_supp he) xs hxs,
    run_keys c.T _ (Step.init_keys c.T fun m hm => ((c.checked v hv).keys m hm).2) xs⟩

/-- T5 from the lines for runs, scoped to the slots: in a checked spec's service, a run from the initial state on valid
inputs, where every listed pair of own kinds has both questions unsat and every timer machine sets no timer or has
both its questions unsat (`Prove.proved`). Every cascade a step of the run starts with own effects a script can hold
ends, in every order, as `settle` does, up to renaming the names the cascade made, or both fault, wherever every step
in progress it reaches in any order fits the slots; and every order of the timers due at one deadline of a clock line
ends as `fire` does, wherever every timer set in a state the firing reaches in any order has a context that fits. -/
theorem run_lines (c : CheckedSpec) (hv : v ∈ c.spec.services) (senv : StepEnv L (shapes v))
    (hpairs : ∀ p ∈ L.ownPairs v.event, ∃ bq tq, pairQuestions L c.T c.P v senv p.1 p.2 = .ok (bq, tq) ∧
      Unsat L (pairTys v) bq ∧ Unsat L (pairTys v) tq)
    (htimers : ∀ m ∈ v.machines, m.noTimer = true ∨ ∃ bq tq, backQuestions L m = .ok (bq, tq) ∧
      Unsat L (backTys m) bq ∧ Unsat L (backTys m) tq)
    {xs : List (Input v)} (hxs : Step.ValidRun c.T (Step.State.init v) xs) :
    (∀ {x : Input v}, x.Valid (run c.T v (Step.State.init v) xs).1 → ∀ {a : Step.Acc v},
      Step.Begins c.T (run c.T v (Step.State.init v) xs).1 x a → Lines.Coded L a →
      (∀ b, Diamond.Reach (Step.ownSys c.T v) a b → Within L (shapes v) b.state) →
      ∀ fuel {r}, Diamond.Runs (Step.ownSys c.T v) fuel a r →
        Diamond.Agree (Step.Same a.state.fresh a.state.nextId) r (Step.settle c.T fuel a)) ∧
    (∀ (time : Int) fuel, let s := { (run c.T v (Step.State.init v) xs).1 with now := time }
      (∀ b, Diamond.Reach (Step.timerSys v) (s, []) b → TimersFit L b.1.records b.1.machines) →
      ∀ {r}, Diamond.Runs (Step.timerSys v) fuel (s, []) r → Diamond.Agree Step.TimerEq r (Step.fireResult s (fuel + 1))) := by
  obtain ⟨hinv, hs, hk⟩ := run_keeps c hv hxs
  exact ⟨fun hx _ ha hcoded hfit => cascade_lines c hv senv hpairs (begins_keeps c hv hinv hs hk hx ha) hcoded hfit,
    fun _ fuel hfit _ hr => timers_lines htimers fuel _ hfit hr⟩

/-- `run_lines` from lines that read `Prove.withinBounds`: where every listed pair of own kinds has its target question
unsat and its codes fit, the same of every cascade whose states also run each of their waiting effects, and every two
of them in either order, within the slots. -/
theorem run_within (c : CheckedSpec) (hv : v ∈ c.spec.services) (senv : StepEnv L (shapes v))
    (hpairs : ∀ p ∈ L.ownPairs v.event, ∃ bq tq, pairQuestions L c.T c.P v senv p.1 p.2 = .ok (bq, tq) ∧
      Unsat L (pairTys v) tq ∧ PairCodesFit L c.P v p.1 p.2)
    {xs : List (Input v)} (hxs : Step.ValidRun c.T (Step.State.init v) xs) {x : Input v}
    (hx : x.Valid (run c.T v (Step.State.init v) xs).1) {a : Step.Acc v}
    (ha : Step.Begins c.T (run c.T v (Step.State.init v) xs).1 x a) (hcoded : Lines.Coded L a)
    (hfit : ∀ b, Diamond.Reach (Step.ownSys c.T v) a b → Within L (shapes v) b.state ∧
      (∀ i (hi : i < b.own.length), ownFits L.count c.T b.state b.own[i]) ∧
      ∀ i j (hi : i < b.own.length) (hj : j < b.own.length), i ≠ j →
        PairFits L.count c.T { b with own := Step.dropTwo b.own i j } b.own[i] b.own[j]) :
    ∀ fuel {r}, Diamond.Runs (Step.ownSys c.T v) fuel a r →
      Diamond.Agree (Step.Same a.state.fresh a.state.nextId) r (Step.settle c.T fuel a) := by
  obtain ⟨hinv, hs, hk⟩ := run_keeps c hv hxs
  exact cascade_within c hv senv hpairs (begins_keeps c hv hinv hs hk hx ha) hcoded hfit

end

end Tazuna.Smt
