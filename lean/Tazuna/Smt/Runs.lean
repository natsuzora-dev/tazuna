import Tazuna.Smt.Lines
import Tazuna.Smt.Cover

/-! T5 for runs: the cascades `cascade_lines` speaks about are every cascade a run from the initial state on valid
inputs starts. Each step of such a run keeps the run's invariants (wire ids below the next, names below the counter,
the program's sites, instances in the step's form), and a cascade starts (`Step.Begins`) with what a pair question
assumes of its state (`begins_keeps`). Its waiting own effects are coded wherever the step that starts it is within
the slots (`begins_coded`): the step's encoding relates each own effect its events or timers queue to a value, and a
step line that reads proved, or within the bounds where the step fits, makes the encoding speak for the step. The
timers of a clock line need no invariant: a timer question is asked over a free context. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {v : ServiceV}

/-- A cascade a step on a valid input starts keeps what a pair question assumes of its state, where the state the step
starts from keeps the run's invariants. -/
theorem begins_keeps (c : CheckedSpec) (hv : v ∈ c.spec.services) {s : State v} (hinv : Step.Inv c.P s)
    (hs : Step.StateSupp s) (hk : Step.KeysOk c.T s) {x : Input v} (hx : x.Valid s) {a : Step.Acc v}
    (h : Step.Begins c.T s x a) : CascadeKeeps c.T c.P a := by
  have hr := (c.checked v hv).reach
  obtain ⟨hsupp, hpend⟩ := Step.begins_supp c.T (c.equivariant v hv) hs hinv.below hx h
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
    Step.run_supp c.T he hr _ Step.init_inv (Step.init_supp he) xs hxs,
    run_keys c.T _ (Step.init_keys c.T fun m hm => ((c.checked v hv).keys m hm).2) xs⟩

/-- What a step line's answers say, whichever verdict it reads: the input kind's questions are built, and its bound
question is unsat (`Prove.proved`) or `F` holds, the fit of the step the line's scope names (`Prove.withinBounds`). -/
def StepLine (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v)) (F : Prop)
    (inp : SymInput v (shapes v) senv.nT) : Prop :=
  ∃ gs qs, questions L T P v senv inp = .ok (gs, qs) ∧
    ((∀ q ∈ qs, q.target = none → Unsat L q.ask) ∨ F)

/-- Every own effect a cascade starts with is coded, where the step that starts it begins at a state and an input
within the slots and its input kind's step line reads proved, or within the bounds and the step stays within the slots
(`StepFits`): the bound question or the scope makes the step stay within the slots, and there its encoding relates each
own effect its events or timers queue to a value. -/
theorem begins_coded {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} (chk : Checked P E T v)
    (senv : StepEnv L (shapes v)) {s : State v} {x : Input v}
    (hq : ∀ inp ∈ stepInputs v (shapes v) senv.nT (5 + v.machines.length),
      StepLine L T P v senv (StepFits L T P v s x) inp)
    (hinv : Step.Inv P s) (hheld : Step.invariants s = []) (hkeys : Step.KeysOk T s)
    (hW : Within L (shapes v) s) (hx : (inputVals L chk.callerData x).isSome) {a : Step.Acc v}
    (hb : Step.Begins T s x a) : QueueCoded L a := by
  obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.1 hx
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  rcases covered chk senv hkeys hW x hivs with ⟨inp, hmem, _, M, hM, hS, hxd, hcase⟩ | h
  · obtain ⟨gs, qs, hqs, hor⟩ := hq inp hmem
    rcases hor with hun | hfit
    · obtain ⟨t, ht, hcodes, hsites, hcond⟩ := bound_cond senv inp hqs hS hinv hheld hord hcase
        fun q hq' hn => (hun q hq' hn).noModel_at (questions_tys L T P v senv hqs q hq') M fun n h => varSorted_of_sorted (hM n h)
      exact ((step_encode chk senv hS hinv hxd ht).2 hcodes hsites (hcase t ht)).2.2 hcond a hb
    · obtain ⟨t, ht, -⟩ := bind_ok.1 hqs
      have henc := step_encode chk senv hS hinv hxd ht
      have hcodes := henc.1.2 (codesFit_of_decode hxd hfit.1)
      have hsites := sites_of_decode senv ht hxd hfit.2.1
      have E := henc.2 hcodes hsites (hcase t ht)
      exact E.2.2 (E.1.2 hfit.2.2.2.2.2) a hb
  · exact (h.2 a hb).elim

/-- T5 for runs, scoped to the slots: in a checked spec's service whose initial state keeps its invariants, take a run
from the initial state on valid inputs. Every cascade a step of the run starts, at a state and an input within the
slots, ends in every order as `settle` does, up to renaming the names the cascade made, or both fault, wherever every
step in progress it reaches in any order fits the slots, every input kind's step line reads proved or within the
bounds where the step fits (`StepLine`), and every listed pair of own kinds reads proved or within the bounds where
the cascade fits (`PairLine`, `CascadeFits`). Where every timer line reads proved, every order of the timers due at
one deadline of a clock line ends as `fire` does, wherever every timer set in a state the firing reaches in any order
has a context that fits. -/
theorem run_lines (c : CheckedSpec) (hv : v ∈ c.spec.services) (senv : StepEnv L (shapes v))
    (hinit : Step.invariants (Step.State.init v) = []) (htimers : ∀ m ∈ v.machines, TimerLine L m)
    {xs : List (Input v)} (hxs : Step.ValidRun c.T (Step.State.init v) xs) :
    (∀ {x : Input v}, x.Valid (run c.T v (Step.State.init v) xs).1 →
      Within L (shapes v) (run c.T v (Step.State.init v) xs).1 →
      (inputVals L (c.checked v hv).callerData x).isSome →
      (∀ inp ∈ stepInputs v (shapes v) senv.nT (5 + v.machines.length),
        StepLine L c.T c.P v senv (StepFits L c.T c.P v (run c.T v (Step.State.init v) xs).1 x) inp) →
      ∀ {a : Step.Acc v}, Step.Begins c.T (run c.T v (Step.State.init v) xs).1 x a →
      (∀ p ∈ L.ownPairs v.event, PairLine L c.T c.P v senv (CascadeFits L c.T a) p) →
      (∀ b, Diamond.Reach (Step.ownSys c.T v) a b → Within L (shapes v) b.state) →
      ∀ fuel {r}, Diamond.Runs (Step.ownSys c.T v) fuel a r →
        Diamond.Agree (Step.Same a.state.fresh a.state.nextId) r (Step.settle c.T fuel a)) ∧
    (∀ (time : Int) fuel, let s := { (run c.T v (Step.State.init v) xs).1 with now := time }
      (∀ b, Diamond.Reach (Step.timerSys v) (s, []) b → TimersFit L b.1.records b.1.machines) →
      ∀ {r}, Diamond.Runs (Step.timerSys v) fuel (s, []) r → Diamond.Agree Step.TimerEq r (Step.fireResult s (fuel + 1))) := by
  obtain ⟨hinv, hs, hk⟩ := run_keeps c hv hxs
  refine ⟨fun hx hW hvals hsteps _ ha hpairs hfit => ?_, fun _ fuel hfit _ hr => timers_lines htimers fuel _ hfit hr⟩
  exact cascade_lines c hv senv (begins_keeps c hv hinv hs hk hx ha) (begins_coded (c.checked v hv) senv hsteps hinv
    (Tazuna.Ir.run_invariants c.T _ xs hinit) hk hW hvals ha) hpairs hfit

end

end Tazuna.Smt
