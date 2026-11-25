import Tazuna.Semantics.Diamond
import Tazuna.Semantics.Settle

/-! The own cascade with its order left open. `settle` runs the waiting own commands and queries first in, first out;
the spec writes no such order, so any waiting one may run next (`ownSys`), and `settle` is the run that always picks
the first (`settle_runs`). Where every two waiting own effects commute in one step, every order agrees with `settle`
(`settle_agrees`): the step's result does not depend on the order the semantics picked.

Timers on one clock line are the same: `fire` fires the earliest due deadline first, an order the trace's times write,
and among the instances due at that deadline the first machine's first key, an order the spec does not write. Any of
them may fire next (`timerSys`), `fire` is the run that picks the first (`fire_runs`), and where every two of them
commute in one step every order agrees with `fire` (`fire_agrees`). -/

namespace Tazuna.Ir

namespace Step

variable {v : ServiceV} (T : List TypeDecl)

/-- The own cascade as a system of steps: the enabled steps are the waiting own effects, and running one takes it out
of the queue. -/
def ownSys (v : ServiceV) : Diamond.Sys (Acc v) Fault where
  len a := a.own.length
  pick a i := match a.own[i]? with
    | some eff => runOwn T { a with own := a.own.eraseIdx i } eff
    | none => .ok a
  limit := .cascadeLimit

theorem settle_first : (fuel : Nat) → (a : Acc v) → settle T fuel a = Diamond.first (ownSys T v) fuel a
  | fuel, a => by
    unfold settle Diamond.first
    cases ho : a.own with
    | nil => simp [ownSys, ho]
    | cons eff rest =>
      cases fuel with
      | zero => simp [ownSys, ho]
      | succ f =>
        simp only [ownSys, ho, List.length_cons, Nat.add_one_ne_zero, ↓reduceIte, List.getElem?_cons_zero,
          List.eraseIdx_cons_zero, bind, Except.bind]
        cases runOwn T { a with own := rest } eff with
        | error e => rfl
        | ok b => exact settle_first f b

/-- `settle` is one of the runs of the own cascade. -/
theorem settle_runs (fuel : Nat) (a : Acc v) : Diamond.Runs (ownSys T v) fuel a (settle T fuel a) := by
  rw [settle_first]
  exact Diamond.runs_first _ fuel a

/-- Where waiting own effects commute in one step, up to an equivalence the own steps respect, every order of the own
cascade ends as `settle` does, up to that equivalence, or both fault. -/
theorem settle_agrees {I : Acc v → Prop} {E : Acc v → Acc v → Prop} (hE : Diamond.Equiv E)
    (hS : Diamond.Simulates (ownSys T v) E) (hD : Diamond.Commutes (ownSys T v) I E)
    (hI : Diamond.Preserved (ownSys T v) I) (fuel : Nat) (a : Acc v) (ha : I a) {r : Except Fault (Acc v)}
    (hr : Diamond.Runs (ownSys T v) fuel a r) : Diamond.Agree E r (settle T fuel a) :=
  Diamond.runs_agree hE hS hD hI fuel a ha hr (settle_runs T fuel a)

variable {r e : Ty}

/-- Fires the `k`-th instance whose timer has the deadline `d`. -/
def fireNth (m : MachineV r e) (records : r.den0) (now d : Int) :
    Nat → List (Instance m) → List (Instance m) × List (Sender × EffectV e)
  | _, [] => ([], [])
  | k, i :: is =>
    if hitsAt d i then match k with
      | 0 => ((fired m records now i).1 :: is, (fired m records now i).2)
      | k + 1 => let x := fireNth m records now d k is; (i :: x.1, x.2)
    else let x := fireNth m records now d k is; (i :: x.1, x.2)

/-- How many instances of the machines have a timer with the deadline `d`. -/
def hitCount (d : Int) : {ms : List (MachineV r e)} → Machines ms → Nat
  | _, .nil => 0
  | _, .cons insts rest => insts.countP (hitsAt d) + hitCount d rest

/-- Fires the `k`-th instance whose timer has the deadline `d`, counting machines in order and each machine's instances
in key order. -/
def fireMachinesAt (records : r.den0) (now d : Int) :
    Nat → {ms : List (MachineV r e)} → Machines ms → Machines ms × List (Sender × EffectV e)
  | _, _, .nil => (.nil, [])
  | k, _, .cons insts rest =>
    if k < insts.countP (hitsAt d) then
      let x := fireNth _ records now d k insts
      (.cons x.1 rest, x.2)
    else
      let y := fireMachinesAt records now d (k - insts.countP (hitsAt d)) rest
      (.cons insts y.1, y.2)

theorem fireFirst_none (m : MachineV r e) (records : r.den0) (now d : Int) :
    (insts : List (Instance m)) → insts.countP (hitsAt d) = 0 → fireFirst m records now d insts = (insts, [], false)
  | [], _ => rfl
  | i :: is, h => by
    have hi : hitsAt d i = false := by
      cases hh : hitsAt d i with
      | false => rfl
      | true => simp [hh] at h
    have hr : is.countP (hitsAt d) = 0 := by simpa [List.countP_cons, hi] using h
    simp [fireFirst, hi, fireFirst_none m records now d is hr]

theorem fireFirst_nth (m : MachineV r e) (records : r.den0) (now d : Int) :
    (insts : List (Instance m)) → 0 < insts.countP (hitsAt d) →
    fireFirst m records now d insts = ((fireNth m records now d 0 insts).1, (fireNth m records now d 0 insts).2, true)
  | [], h => by simp at h
  | i :: is, h => by
    cases hi : hitsAt d i with
    | true => simp [fireFirst, fireNth, hi]
    | false =>
      have hr : 0 < is.countP (hitsAt d) := by simpa [List.countP_cons, hi] using h
      simp [fireFirst, fireNth, hi, fireFirst_nth m records now d is hr]

theorem fireMachines_at (records : r.den0) (now d : Int) : {ms : List (MachineV r e)} → (l : Machines ms) →
    ((fireMachines records now d false l).1, (fireMachines records now d false l).2.1) = fireMachinesAt records now d 0 l
  | _, .nil => rfl
  | _, .cons insts rest => by
    by_cases h : 0 < insts.countP (hitsAt d)
    · simp [fireMachines, fireMachinesAt, h, fireFirst_nth _ records now d insts h, fireMachines_true]
    · have h0 : insts.countP (hitsAt d) = 0 := by omega
      have ih := fireMachines_at records now d rest
      have ih1 := congrArg Prod.fst ih
      have ih2 := congrArg Prod.snd ih
      simp only at ih1 ih2
      simp [fireMachines, fireMachinesAt, h0, fireFirst_none _ records now d insts h0, ih1, ih2]

/-- The timers of one clock line as a system of steps, with the effects they start so far: the enabled steps are the
instances whose timer has the earliest due deadline, and running one fires it. -/
def timerSys (v : ServiceV) : Diamond.Sys (State v × List (Sender × EffectV v.event)) Fault where
  len a := match (dues a.1.machines.toSigma a.1.now).min? with
    | none => 0
    | some d => hitCount d a.1.machines
  pick a k := match (dues a.1.machines.toSigma a.1.now).min? with
    | none => .ok a
    | some d =>
      let x := fireMachinesAt a.1.records a.1.now d k a.1.machines
      .ok ({ a.1 with machines := x.1 }, a.2 ++ x.2)
  limit := .cascadeLimit

/-- `fire` as a result: running out of fuel is the cascade bound's fault. -/
def fireResult (s : State v) (fuel : Nat) : Except Fault (State v × List (Sender × EffectV v.event)) :=
  match fire s fuel with
  | none => .error .cascadeLimit
  | some x => .ok x

theorem hitCount_pos {d now : Int} : {ms : List (MachineV r e)} → (l : Machines ms) →
    d ∈ dues l.toSigma now → 0 < hitCount d l
  | _, .nil, h => by simp [dues] at h
  | _, .cons insts rest, h => by
    simp only [PerMachine.toSigma_cons, dues, List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · simp only [List.mem_filterMap] at h
      obtain ⟨i, hi, hd⟩ := h
      have : hitsAt d i = true := by
        unfold hitsAt
        cases ht : i.timer with
        | none => simp [ht] at hd
        | some p =>
          obtain ⟨d', _⟩ := p
          simp only [ht, Option.bind_some] at hd
          split at hd <;> simp_all
      have : 0 < insts.countP (hitsAt d) := List.countP_pos_iff.2 ⟨i, hi, this⟩
      simp only [hitCount]; omega
    · have := hitCount_pos rest h
      simp only [hitCount]; omega

theorem fire_first : (n : Nat) → (s : State v) → (acc : List (Sender × EffectV v.event)) →
    Diamond.first (timerSys v) n (s, acc) = (fireResult s (n + 1)).map fun x => (x.1, acc ++ x.2)
  | n, s, acc => by
    unfold Diamond.first fireResult
    cases hd : (dues s.machines.toSigma s.now).min? with
    | none => simp [timerSys, fire, hd, Except.map]
    | some d =>
      have hpos : 0 < hitCount d s.machines := hitCount_pos s.machines (List.min?_mem hd)
      have hne : (timerSys v).len (s, acc) ≠ 0 := by simp only [timerSys, hd]; omega
      simp only [hne, ↓reduceIte]
      have hf := fireMachines_at s.records s.now d s.machines
      have hf1 := congrArg Prod.fst hf
      have hf2 := congrArg Prod.snd hf
      simp only at hf1 hf2
      cases n with
      | zero => simp [timerSys, fire, hd, Except.map]
      | succ m =>
        have hp : (timerSys v).pick (s, acc) 0 = .ok ({ s with machines := (fireMachinesAt s.records s.now d 0 s.machines).1 },
            acc ++ (fireMachinesAt s.records s.now d 0 s.machines).2) := by simp [timerSys, hd]
        rw [hp]
        dsimp only
        rw [fire_first m]
        have hfs : fire s (m + 1 + 1) = (fire { s with machines := (fireMachines s.records s.now d false s.machines).1 }
            (m + 1)).map fun x => (x.1, (fireMachines s.records s.now d false s.machines).2.1 ++ x.2) := by
          rw [fire.eq_2]; simp only [hd]
        unfold fireResult
        rw [hfs, hf1, hf2]
        cases fire { s with machines := (fireMachinesAt s.records s.now d 0 s.machines).1 } (m + 1) with
        | none => rfl
        | some x => simp [Except.map, Option.map]

/-- `fire` is one of the runs of a clock line's timers. -/
theorem fire_runs (fuel : Nat) (s : State v) : Diamond.Runs (timerSys v) fuel (s, []) (fireResult s (fuel + 1)) := by
  have h := fire_first fuel s []
  simp only [List.nil_append] at h
  have hm : (fireResult s (fuel + 1)).map (fun x => (x.1, x.2)) = fireResult s (fuel + 1) := by
    cases fireResult s (fuel + 1) <;> rfl
  rw [hm] at h
  rw [← h]
  exact Diamond.runs_first _ fuel (s, [])

/-- Where timers due at one deadline commute in one step, up to an equivalence firing respects, every order of a clock
line's timers ends as `fire` does, up to that equivalence, or both fault. -/
theorem fire_agrees {I : State v × List (Sender × EffectV v.event) → Prop}
    {E : State v × List (Sender × EffectV v.event) → State v × List (Sender × EffectV v.event) → Prop}
    (hE : Diamond.Equiv E) (hS : Diamond.Simulates (timerSys v) E) (hD : Diamond.Commutes (timerSys v) I E)
    (hI : Diamond.Preserved (timerSys v) I) (fuel : Nat) (s : State v) (hs : I (s, []))
    {r : Except Fault (State v × List (Sender × EffectV v.event))} (hr : Diamond.Runs (timerSys v) fuel (s, []) r) :
    Diamond.Agree E r (fireResult s (fuel + 1)) :=
  Diamond.runs_agree hE hS hD hI fuel (s, []) hs hr (fire_runs fuel s)

end Step

end Tazuna.Ir
