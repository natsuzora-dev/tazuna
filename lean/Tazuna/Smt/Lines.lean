import Tazuna.Smt.OwnCoded
import Tazuna.Smt.Timer
import Tazuna.Semantics.NoTimer

/-! T5 from the pair lines' answers, scoped to the slots, as every verdict is: where each listed pair of own kinds
reads `Prove.proved`, or `Prove.withinBounds` and the steps it names fit, every order of a cascade ends as `settle`
does, up to renaming, or both fault, for every cascade that starts with waiting own effects some value codes and every
state of which, in any order, fits the slots (`cascade_lines`). The pair questions are asked over a free symbolic
state, so no order of the cascade needs encoding: what each state reached in any order must meet is the questions'
preconditions, which the states of a cascade keep (`CascadeKeeps`): names below the counter, pending requests below
the next id and of the program's sites, waiting effects of its sites, instances in the step's form; and its waiting
effects stay coded (`coded_preserved`), since the bound question of each effect's pair with itself makes its step fit,
or the line's scope does. The timer lines say the same of a clock line's timers (`timers_lines`): a timer machine's
question is asked over a free key, state, records and time, so each timer that fires in any order needs only its
context to fit the slots. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- Every service of a checked spec respects every renaming of the ids steps make: its functions and the values they
captured relate to themselves under every renaming, and its caller, key and state types are comparable. -/
theorem CheckedSpec.equivariant (c : CheckedSpec) : ∀ v ∈ c.spec.services, v.Equivariant := by
  intro v hv
  have hk := c.checked v hv
  refine ⟨?_, fun m hm => (hk.machinesComparable m hm).1, fun m hm => (hk.machinesComparable m hm).2, fun R => ?_⟩
  · have h := hk.stateTys
    simp only [ServiceV.stateTys, Bool.and_eq_true] at h
    exact comparable_of_embeddable _ h.2.1
  · exact Var.get_rel c.program.root (Defs.eval_rel (R := R) c.program.defs) () () trivial rfl v hv

section
variable {L : Layout} {v : ServiceV}

/-- What a cascade's states keep and a pair question assumes of its state: names below the counter, the counters'
invariants, the program's sites, and instances in the step's form. -/
structure CascadeKeeps (T : List TypeDecl) (P : List AnySite) (a : Step.Acc v) : Prop where
  supp : Step.Supp a
  inv : Step.Inv P a.state
  queue : Step.QueueOk P a
  keys : Step.KeysOk T a.state

theorem keeps_preserved {T : List TypeDecl} {P : List AnySite} {E : List AnyEffectSite} (hv : v.Equivariant)
    (hr : v.Reach P E) : Diamond.Preserved (Step.ownSys T v) (CascadeKeeps T P) := by
  intro a i b ha hi hb
  have hs := Step.ownSys_preserved T hv a i b ha.supp hi hb
  simp only [Step.ownSys, List.getElem?_eq_getElem hi] at hb
  have hq' : Step.QueueOk P { a with own := a.own.eraseIdx i } := fun x hx => ha.queue x (List.mem_of_mem_eraseIdx hx)
  exact ⟨hs, Step.runOwn_inv T hr { a with own := a.own.eraseIdx i } ha.inv _ hb,
    Step.runOwn_queue T hr { a with own := a.own.eraseIdx i } ha.inv hq' _ hb,
    Step.runOwn_keys T { a with own := a.own.eraseIdx i } ha.keys _ hb⟩

/-- A cascade's step from a step in progress it keeps, whose state fits the slots and whose waiting own effects are
coded, keeps them coded where the pair lines speak for the step (`coded_step`). -/
theorem coded_preserved {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} (chk : Checked P E T v)
    (hL : SortedLayout L) (senv : StepEnv L (shapes v)) {a b : Step.Acc v} {i : Nat}
    (ha : CascadeKeeps T P a) (hW : Within L (shapes v) a.state) (hc : QueueCoded L a) (hi : i < a.own.length)
    (hcf : ∀ p ∈ L.ownPairs v.event, PairLine L T P v senv (ownFits L.count T a.state a.own[i]) p)
    (hb : (Step.ownSys T v).pick a i = .ok b) : QueueCoded L b := by
  simp only [Step.ownSys, List.getElem?_eq_getElem hi] at hb
  exact coded_step chk hL senv ha.keys hW ha.inv ha.supp ha.queue hc hi hcf hb

/-- At a step in progress a cascade keeps, which fits the slots, two of its waiting effects meet a pair question's
preconditions with the rest of the queue as the step in progress. -/
theorem pair_pre {T : List TypeDecl} {P : List AnySite} {a : Step.Acc v} (ha : CascadeKeeps T P a) {i j : Nat}
    (hi : i < a.own.length) (hj : j < a.own.length) :
    Step.KeysOk T { a with own := Step.dropTwo a.own i j }.state ∧
      Step.StateSupp { a with own := Step.dropTwo a.own i j }.state ∧
      Step.QueueOk P { a with own := Step.dropTwo a.own i j } ∧
      Step.Supp { a with own := Step.dropTwo a.own i j } ∧
      a.own[i].effect.Reach P ∧ a.own[j].effect.Reach P :=
  ⟨ha.keys, fun P hP => (ha.supp P hP).state, fun x hx => ha.queue x (Step.mem_dropTwo hx),
    fun P hP => (ha.supp P hP).sub_own fun _ hx => Step.mem_dropTwo hx,
    ha.queue _ (List.getElem_mem hi), ha.queue _ (List.getElem_mem hj)⟩

/-- What `Prove.withinBounds` names for a cascade: every step in progress it reaches in any order runs each of its
waiting effects, and every two of them in either order, within the slots. -/
def CascadeFits (L : Layout) (T : List TypeDecl) (a : Step.Acc v) : Prop :=
  ∀ b, Diamond.Reach (Step.ownSys T v) a b → (∀ i (hi : i < b.own.length), ownFits L.count T b.state b.own[i]) ∧
    ∀ i j (hi : i < b.own.length) (hj : j < b.own.length), i ≠ j →
      PairFits L.count T { b with own := Step.dropTwo b.own i j } b.own[i] b.own[j]

/-- T5 from the pair lines, scoped to the slots: where every listed pair of own kinds reads proved, or within the
bounds and the cascade fits (`CascadeFits`), every order of a cascade from a step in progress it keeps, whose waiting
own effects are coded, ends as `settle` does, up to renaming the names the cascade made, or both fault, wherever
every step in progress the cascade reaches in any order fits the slots. The effects it queues stay coded
(`coded_preserved`). -/
theorem cascade_lines (c : CheckedSpec) (hv : v ∈ c.spec.services) (hL : SortedLayout L) (senv : StepEnv L (shapes v))
    {a : Step.Acc v} (ha : CascadeKeeps c.T c.P a) (hcoded : QueueCoded L a)
    (hall : ∀ p ∈ L.ownPairs v.event, PairLine L c.T c.P v senv (CascadeFits L c.T a) p)
    (hfit : ∀ b, Diamond.Reach (Step.ownSys c.T v) a b → Within L (shapes v) b.state) :
    ∀ fuel {r}, Diamond.Runs (Step.ownSys c.T v) fuel a r →
      Diamond.Agree (Step.Same a.state.fresh a.state.nextId) r (Step.settle c.T fuel a) := by
  have he := c.equivariant v hv
  have chk := c.checked v hv
  intro fuel r hr
  refine Step.cascade_agrees c.T he
    (J := fun b => Diamond.Reach (Step.ownSys c.T v) a b ∧ CascadeKeeps c.T c.P b ∧ QueueCoded L b)
    (fun b i d hb hi hd => ⟨.step hb.1 hi hd, keeps_preserved he chk.reach b i d hb.2.1 hi hd,
      coded_preserved chk hL senv hb.2.1 (hfit b hb.1) hb.2.2 hi
        (fun p hp => (hall p hp).mono fun h => (h b hb.1).1 i hi) hd⟩)
    (fun b _ hb i j hi hj hij => ?_) fuel a ha.supp ⟨.refl, ha, hcoded⟩ hr
  obtain ⟨hk, hs, hq, hsa, hr1, hr2⟩ := pair_pre hb.2.1 hi hj
  exact pairs_at chk hL senv (fun p hp => (hall p hp).mono fun h => (h b hb.1).2 i j hi hj hij) hk (hfit b hb.1)
    hb.2.1.inv hs hq hsa (hb.2.2 _ (List.getElem_mem hi)) (hb.2.2 _ (List.getElem_mem hj)) hr1 hr2

/-- A timer's context fits the slots: the instance's key, its state and the records embed. -/
def CtxFits (L : Layout) {r e : Ty} (m : MachineV r e) (records : r.den0) (key : m.key.den0) (st : m.state.den0) :
    Prop :=
  (embedV L m.key (Ty.up _ m.key_data key)).isSome ∧ (embedV L m.state (Ty.up _ m.state_data st)).isSome ∧
    (embedV L r (Ty.up _ m.records_data records)).isSome

/-- Every instance of `l` has a timer context that fits the slots. -/
def TimersFit (L : Layout) {r e : Ty} (records : r.den0) : {ms : List (MachineV r e)} → Step.Machines ms → Prop
  | [], .nil => True
  | m :: _, .cons insts rest => (∀ i ∈ insts, CtxFits L m records i.key i.state) ∧ TimersFit L records rest

/-- What a timer line's answers say: the machine gives no timer (it gets no line), or both its questions are unsat
(`Prove.proved`). -/
def TimerLine (L : Layout) {r e : Ty} (m : MachineV r e) : Prop :=
  m.noTimer = true ∨ ∃ bq tq, timerQuestions L m = .ok (bq, tq) ∧ Unsat L bq ∧ Unsat L tq

/-- What a timer line says: at a context that fits the slots, the state the timer enters waits for no earlier timer. -/
theorem forward_of_line {r e : Ty} {m : MachineV r e}
    (hq : TimerLine L m)
    {records : r.den0} {key : m.key.den0} {st : m.state.den0} (hc : CtxFits L m records key st) :
    ∀ y ∈ m.timerAt records key st, ∀ z ∈ m.timerAt records key y.2, y.1 ≤ z.1 := by
  rcases hq with hn | ⟨bq, tq, hq, hb, ht⟩
  · exact Step.timerForward_of_noTimer hn records key st
  obtain ⟨zk, hk⟩ := Option.isSome_iff_exists.1 hc.1
  obtain ⟨zs, hs⟩ := Option.isSome_iff_exists.1 hc.2.1
  obtain ⟨zr, hr⟩ := Option.isSome_iff_exists.1 hc.2.2
  let M := coverModel L [zk, zs, zr]
  have hM : ∀ n (h : n < (timerTys m).length), Sorted L (timerTys m)[n] (M.vars n) := by
    intro n hn
    simp only [timerTys, List.length_cons, List.length_nil] at hn
    match n, hn with
    | 0, _ => exact sorted_of_embed hk
    | 1, _ => exact sorted_of_embed hs
    | 2, _ => exact sorted_of_embed hr
  have hsrt : Forall2 (SrtVal L) (timerTys m) [zk, zs, zr] :=
    ⟨embedV_srtVal hk, embedV_srtVal hs, embedV_srtVal hr, trivial⟩
  have hdata : ∀ t ∈ timerTys m, t.isData = true := by
    simp only [timerTys, List.mem_cons, List.not_mem_nil, or_false]
    rintro t (rfl | rfl | rfl)
    · exact m.key_data
    · exact m.state_data
    · exact m.records_data
  exact (timer_sound m hq ht hM (layoutSorted_coverModel hsrt hdata) ⟨key, st, records, decode_embed _ _ _ hk,
    decode_embed _ _ _ hs, decode_embed _ _ _ hr⟩).2 hb

theorem firesAt_of_lines {r e : Ty} {records : r.den0} {now : Int} : {ms : List (MachineV r e)} →
    (∀ m ∈ ms, TimerLine L m) →
    (l : Step.Machines ms) → TimersFit L records l → Step.FiresAt records now l
  | [], _, .nil, _ => trivial
  | m :: _, hq, .cons insts rest, hf => by
    obtain ⟨hi, hrest⟩ : _ ∧ _ := hf
    refine ⟨fun i hmem d hd _ y hy => ?_,
      firesAt_of_lines (fun m' hm' => hq m' (List.mem_cons_of_mem _ hm')) rest hrest⟩
    unfold Step.hitsAt at hd
    unfold Step.fired at hy
    split at hd
    · next d' tg ht =>
      have hdd : d' = d := by simpa using hd
      subst hdd
      rw [ht] at hy
      exact forward_of_line (hq m List.mem_cons_self) (hi i hmem) (d', tg) ht y (by simpa [Step.enter] using hy)
    · cases hd

/-- T5 for a clock line's timers from the timer lines, scoped to the slots: where every timer line reads proved, every
order of the timers due at one deadline ends as `fire` does, the same state and the
same effects in some order, wherever every instance of a state the firing reaches in any order has a timer context
that fits the slots. -/
theorem timers_lines {v : ServiceV}
    (hq : ∀ m ∈ v.machines, TimerLine L m)
    (fuel : Nat) (s : State v)
    (hfit : ∀ a, Diamond.Reach (Step.timerSys v) (s, []) a → TimersFit L a.1.records a.1.machines)
    {r : Except Fault (State v × List (Sender × EffectV v.event))} (hr : Diamond.Runs (Step.timerSys v) fuel (s, []) r) :
    Diamond.Agree Step.TimerEq r (Step.fireResult s (fuel + 1)) :=
  Step.timers_agree fuel s (fun a ha => firesAt_of_lines hq a.1.machines (hfit a ha)) hr

end

end Tazuna.Smt
