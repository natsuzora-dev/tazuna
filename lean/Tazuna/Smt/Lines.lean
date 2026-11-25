import Tazuna.Smt.PairLine
import Tazuna.Smt.Commute
import Tazuna.Smt.FiresForward
import Tazuna.Semantics.NoTimer

/-! T5 from the pair lines' answers, scoped to the slots, as every verdict is (run-log 121): where each listed pair of
own kinds reads `Prove.proved`, every order of a cascade ends as `settle` does, up to renaming, or both fault, for
every cascade every state of which, in any order, fits the slots and has waiting own effects a script can hold
(`cascade_lines`). The pair questions are asked over a free symbolic state, so no order of the cascade needs encoding:
what each state reached in any order must meet is the question's preconditions, which the states of a cascade keep
(`Lines.Keeps`): names below the counter, pending requests below the next id and of the program's sites, waiting
effects of its sites, instances in the step's form. Where the lines read `Prove.withinBounds`, the same holds where
every pair's codes fit and every internal step two waiting effects run in either order fits too (`cascade_within`). The timer lines say the same
of a clock line's timers (`timers_lines`): a timer machine's question is asked over a free key, state, records and
time, so each timer that fires in any order needs only its context to fit the slots. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {v : ServiceV}

/-- What a cascade's states keep and a pair question assumes of its state: the counters' invariants, the program's
sites, instances in the step's form, and every pending request's names below the counter. -/
structure Lines.Keeps (T : List TypeDecl) (P : List AnySite) (a : Step.Acc v) : Prop where
  supp : Step.Supp a
  inv : Step.Inv P a.state
  queue : Step.QueueOk P a
  keys : Step.KeysOk T a.state
  pend : Step.PendAt a.state.fresh a

/-- A step in progress whose state fits the slots and whose waiting own effects a script can hold. -/
def AccFits (L : Layout) (a : Step.Acc v) : Prop := Within L (shapes v) a.state ∧ ∀ x ∈ a.own, EffCoded L x

theorem keeps_preserved {T : List TypeDecl} {P : List AnySite} {E : List AnyEffectSite} (hv : v.Equivariant)
    (hr : v.Reach P E) : Diamond.Preserved (Step.ownSys T v) (Lines.Keeps T P) := by
  intro a i b ha hi hb
  have hs := Step.ownSys_preserved T hv a i b ha.supp hi hb
  simp only [Step.ownSys, List.getElem?_eq_getElem hi] at hb
  have hmem : a.own[i] ∈ a.own := List.getElem_mem hi
  have hq' : Step.QueueOk P { a with own := a.own.eraseIdx i } := fun x hx => ha.queue x (Step.mem_eraseIdx hx)
  have ha' : Step.SelfAt (a.state.fresh + 1) { a with own := a.own.eraseIdx i } :=
    (Step.SelfAt.own (a := a) ha.supp.1 fun x hx => ha.supp.2 x (Step.mem_eraseIdx hx)).mono (Nat.le_succ _)
  have hp1 := Step.runOwn_pend T hv (a := { a with own := a.own.eraseIdx i }) ha' (ha.pend.mono (Nat.le_succ _))
    (fun P hP => (ha.supp.2 _ hmem).2 P (hP.mono (Nat.le_succ _))) b hb
  have hfr : b.state.fresh = a.state.fresh + 1 :=
    Step.runOwn_fresh T (a := { a with own := a.own.eraseIdx i }) (ha.supp.2 _ hmem).1 hb
  rw [← hfr] at hp1
  exact ⟨hs, Step.runOwn_inv T hr { a with own := a.own.eraseIdx i } ha.inv _ hb,
    Step.runOwn_queue T hr { a with own := a.own.eraseIdx i } ha.inv hq' _ hb,
    Step.runOwn_keys T { a with own := a.own.eraseIdx i } ha.keys _ hb, hp1⟩

/-- At a step in progress a cascade keeps, which fits the slots, two of its waiting effects meet a pair question's
preconditions with the rest of the queue as the step in progress. -/
theorem pair_pre {T : List TypeDecl} {P : List AnySite} {a : Step.Acc v} (ha : Lines.Keeps T P a) {i j : Nat}
    (hi : i < a.own.length) (hj : j < a.own.length) :
    Step.KeysOk T { a with own := Step.dropTwo a.own i j }.state ∧
      Step.StateSupp { a with own := Step.dropTwo a.own i j }.state ∧
      Step.QueueOk P { a with own := Step.dropTwo a.own i j } ∧
      Step.SelfAt a.state.fresh { a with own := Step.dropTwo a.own i j } ∧
      a.own[i].isRequest = false ∧ a.own[j].isRequest = false ∧ a.own[i].Reach P ∧ a.own[j].Reach P :=
  ⟨ha.keys, Step.StateSupp.of_supp (a := { a with own := Step.dropTwo a.own i j })
      ⟨ha.supp.1, fun x hx => ha.supp.2 x (Step.mem_dropTwo hx)⟩ ha.pend, fun x hx => ha.queue x (Step.mem_dropTwo hx),
    Step.SelfAt.own ha.supp.1 fun x hx => ha.supp.2 x (Step.mem_dropTwo hx),
    (ha.queue _ (List.getElem_mem hi)).1, (ha.queue _ (List.getElem_mem hj)).1,
    (ha.queue _ (List.getElem_mem hi)).2, (ha.queue _ (List.getElem_mem hj)).2⟩

theorem CheckedSpec.recordsComparable (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services) :
    v.records.comparable = true :=
  comparable_of_embeddable _ (stateTys_iff.1 (c.checked v hv).stateTys).1.1

/-- T5 from the pair lines, scoped to the slots: where every listed pair of own kinds has both questions unsat
(`Prove.proved`), every order of a cascade from a step in progress whose names are below its counter ends as `settle`
does, up to renaming the names the cascade made, or both fault, wherever every step in progress the cascade reaches in
any order fits the slots and has waiting own effects a script can hold. -/
theorem cascade_lines (c : CheckedSpec) (hv : v ∈ c.spec.services) (senv : StepEnv L (shapes v))
    (hall : ∀ p ∈ L.ownPairs v.event, ∃ bq tq, pairQuestions L c.T c.P v senv p.1 p.2 = .ok (bq, tq) ∧
      Unsat L (pairTys v) bq ∧ Unsat L (pairTys v) tq)
    {a : Step.Acc v} (ha : Lines.Keeps c.T c.P a)
    (hfit : ∀ b, Diamond.Reach (Step.ownSys c.T v) a b → AccFits L b) :
    ∀ fuel {r}, Diamond.Runs (Step.ownSys c.T v) fuel a r →
      Diamond.Agree (Step.Same a.state.fresh a.state.nextId) r (Step.settle c.T fuel a) := by
  have he := c.equivariant v hv
  have chk := c.checked v hv
  have hmc : ∀ m ∈ v.machines, m.key.comparable = true ∧ m.state.comparable = true :=
    fun m hm => ⟨he.keys m hm, c.states hv m hm⟩
  intro fuel r hr
  refine Step.cascade_agrees c.T he (J := fun b => Diamond.Reach (Step.ownSys c.T v) a b ∧ Lines.Keeps c.T c.P b)
    (fun b i d hb hi hd => ⟨.step hb.1 hi hd, keeps_preserved he chk.reach b i d hb.2 hi hd⟩)
    (fun b _ hb i j hi hj _ => ?_) fuel a ha.supp ⟨.refl, ha⟩ hr
  obtain ⟨hk, hs, hq, hsa, ho1, ho2, hr1, hr2⟩ := pair_pre hb.2 hi hj
  obtain ⟨hW, hcoded⟩ := hfit b hb.1
  exact pairs_at chk senv (c.recordsComparable hv) hmc hall hk hW hb.2.inv hs hq hsa
    (hcoded _ (List.getElem_mem hi)) (hcoded _ (List.getElem_mem hj)) ho1 ho2 hr1 hr2

/-- T5 from pair lines that read `Prove.withinBounds`: where every listed pair of own kinds has its target question
unsat and its codes fit, `cascade_lines` holds of every cascade whose states also run every two of their waiting
effects, in either order, within the slots. -/
theorem cascade_within (c : CheckedSpec) (hv : v ∈ c.spec.services) (senv : StepEnv L (shapes v))
    (hall : ∀ p ∈ L.ownPairs v.event, ∃ bq tq, pairQuestions L c.T c.P v senv p.1 p.2 = .ok (bq, tq) ∧
      Unsat L (pairTys v) tq ∧ PairCodesFit L c.P v p.1 p.2)
    {a : Step.Acc v} (ha : Lines.Keeps c.T c.P a)
    (hfit : ∀ b, Diamond.Reach (Step.ownSys c.T v) a b → AccFits L b ∧
      ∀ i j (hi : i < b.own.length) (hj : j < b.own.length), i ≠ j →
        PairFits L.count c.T { b with own := Step.dropTwo b.own i j } b.own[i] b.own[j]) :
    ∀ fuel {r}, Diamond.Runs (Step.ownSys c.T v) fuel a r →
      Diamond.Agree (Step.Same a.state.fresh a.state.nextId) r (Step.settle c.T fuel a) := by
  have he := c.equivariant v hv
  have chk := c.checked v hv
  have hmc : ∀ m ∈ v.machines, m.key.comparable = true ∧ m.state.comparable = true :=
    fun m hm => ⟨he.keys m hm, c.states hv m hm⟩
  intro fuel r hr
  refine Step.cascade_agrees c.T he (J := fun b => Diamond.Reach (Step.ownSys c.T v) a b ∧ Lines.Keeps c.T c.P b)
    (fun b i d hb hi hd => ⟨.step hb.1 hi hd, keeps_preserved he chk.reach b i d hb.2 hi hd⟩)
    (fun b _ hb i j hi hj hij => ?_) fuel a ha.supp ⟨.refl, ha⟩ hr
  obtain ⟨hk, hs, hq, hsa, ho1, ho2, hr1, hr2⟩ := pair_pre hb.2 hi hj
  obtain ⟨⟨hW, hcoded⟩, hpf⟩ := hfit b hb.1
  exact pairsWithin_at chk senv (c.recordsComparable hv) hmc hall hk hW hb.2.inv hs hq hsa
    (hcoded _ (List.getElem_mem hi)) (hcoded _ (List.getElem_mem hj)) ho1 ho2 hr1 hr2 (hpf i j hi hj hij)

/-- A timer's context fits the slots: the instance's key, the state its timer moves it to and the records embed. -/
def CtxFits (L : Layout) {r e : Ty} (m : MachineV r e) (records : r.den0) (key : m.key.den0) (st : m.state.den0) :
    Prop :=
  (embedV L m.key (Ty.up _ m.key_data key)).isSome ∧ (embedV L m.state (Ty.up _ m.state_data st)).isSome ∧
    (embedV L r (Ty.up _ m.records_data records)).isSome

/-- Every set timer of `l` has a context that fits the slots. -/
def TimersFit (L : Layout) {r e : Ty} (records : r.den0) : {ms : List (MachineV r e)} → Step.Machines ms → Prop
  | [], .nil => True
  | m :: _, .cons insts rest =>
    (∀ i ∈ insts, ∀ p, i.timer = some p → CtxFits L m records i.key p.2) ∧ TimersFit L records rest

/-- What a timer line says: where the machine sets no timer, or both its questions are unsat, the timer `after` sets
at a context that fits the slots is no earlier than the time it is set at. -/
theorem forward_of_line {r e : Ty} {m : MachineV r e}
    (hq : m.noTimer = true ∨ ∃ bq tq, backQuestions L m = .ok (bq, tq) ∧ Unsat L (backTys m) bq ∧
      Unsat L (backTys m) tq)
    {records : r.den0} {now : Int} {key : m.key.den0} {st : m.state.den0} (hc : CtxFits L m records key st) :
    ∀ y ∈ Step.timerAt now (m.after.fn (.inl (key, st, records, now, ()), ())), now ≤ y.1 := by
  rcases hq with hn | ⟨bq, tq, hq, hb, ht⟩
  · exact Step.timerForward_of_noTimer hn records now key st
  obtain ⟨zk, hk⟩ := Option.isSome_iff_exists.1 hc.1
  obtain ⟨zs, hs⟩ := Option.isSome_iff_exists.1 hc.2.1
  obtain ⟨zr, hr⟩ := Option.isSome_iff_exists.1 hc.2.2
  let M := coverModel [zk, zs, zr, .int now]
  have hM : ∀ n (h : n < (backTys m).length), Sorted L (backTys m)[n] (M.vars n) := by
    intro n hn
    simp only [backTys, List.length_cons, List.length_nil] at hn
    match n, hn with
    | 0, _ => exact sorted_of_embed hk
    | 1, _ => exact sorted_of_embed hs
    | 2, _ => exact sorted_of_embed hr
    | 3, _ => exact ⟨now, rfl⟩
  exact (back_sound m hq ht hM ⟨key, st, records, now, decode_embed _ _ _ hk, decode_embed _ _ _ hs,
    decode_embed _ _ _ hr, rfl⟩).2 hb

theorem firesAt_of_lines {r e : Ty} {records : r.den0} {now : Int} : {ms : List (MachineV r e)} →
    (∀ m ∈ ms, m.noTimer = true ∨ ∃ bq tq, backQuestions L m = .ok (bq, tq) ∧ Unsat L (backTys m) bq ∧
      Unsat L (backTys m) tq) →
    (l : Step.Machines ms) → TimersFit L records l → Step.FiresAt records now l
  | [], _, .nil, _ => trivial
  | m :: _, hq, .cons insts rest, hf => by
    obtain ⟨hi, hrest⟩ : _ ∧ _ := hf
    refine ⟨fun i hmem d hd hdn y hy => ?_,
      firesAt_of_lines (fun m' hm' => hq m' (List.mem_cons_of_mem _ hm')) rest hrest⟩
    obtain ⟨key, st, tm⟩ := i
    cases tm with
    | none => simp [Step.hitsAt] at hd
    | some p =>
      have hc := hi _ hmem p rfl
      exact Int.le_trans hdn (forward_of_line (hq m List.mem_cons_self) hc y hy)

/-- T5 for a clock line's timers from the timer lines, scoped to the slots: where every machine sets no timer or has
both its questions unsat, every order of the timers due at one deadline ends as `fire` does, the same state and the
same effects in some order, wherever every timer set in a state the firing reaches in any order has a context that
fits the slots. -/
theorem timers_lines {v : ServiceV}
    (hq : ∀ m ∈ v.machines, m.noTimer = true ∨ ∃ bq tq, backQuestions L m = .ok (bq, tq) ∧
      Unsat L (backTys m) bq ∧ Unsat L (backTys m) tq)
    (fuel : Nat) (s : State v)
    (hfit : ∀ a, Diamond.Reach (Step.timerSys v) (s, []) a → TimersFit L a.1.records a.1.machines)
    {r : Except Fault (State v × List (Sender × EffectV v.event))} (hr : Diamond.Runs (Step.timerSys v) fuel (s, []) r) :
    Diamond.Agree Step.TimerEq r (Step.fireResult s (fuel + 1)) :=
  Step.timers_agree_at fuel s (fun a ha => firesAt_of_lines hq a.1.machines (hfit a ha)) hr

end

end Tazuna.Smt
