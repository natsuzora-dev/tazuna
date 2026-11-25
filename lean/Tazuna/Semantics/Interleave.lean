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

/-! Two timers due at one deadline commute. Firing an instance reads only that instance, the records and the time, and
writes only that instance, so firing two instances in either order leaves the same instances; the effects they start
come in the other order, which is the same multiset. What can still go wrong is the deadline: an instance whose timer
fires may set a timer before the deadline that fired, which then is the earliest and runs first. A service whose
timers never do so (`FiresForward`) has every order of a clock line's timers end as `fire` does (`timers_agree`). -/

section Timers

/-- A timer that fires sets no timer before its deadline. -/
def FiresForward (ms : List (MachineV r e)) : Prop :=
  ∀ m ∈ ms, ∀ (records : r.den0) (now d : Int) (i : Instance m), hitsAt d i = true → d ≤ now →
    ∀ x ∈ (fired m records now i).1.timer, d ≤ x.1

/-- The timer `m`'s `after` sets is never before the time it is set at: what one machine needs for `FiresForward`,
asked of every key, state, records and time, which is one question per timer machine. -/
def TimerForward (m : MachineV r e) : Prop :=
  ∀ (records : r.den0) (now : Int) (key : m.key.den0) (st : m.state.den0),
    ∀ x ∈ timerAt now (m.after.fn (.inl (key, st, records, now, ()), ())), now ≤ x.1

/-- Timers fire forward exactly when no machine's `after` sets a timer before the time it is set at: a fired timer is
set at a time no earlier than its deadline, and any state at any time is the target of some due timer. -/
theorem firesForward_iff (ms : List (MachineV r e)) : FiresForward ms ↔ ∀ m ∈ ms, TimerForward m := by
  constructor
  · intro h m hm records now key st x hx
    exact h m hm records now now ⟨key, st, some (now, st)⟩ (by simp [hitsAt]) (Int.le_refl _) x hx
  · intro h m hm records now d i hd hdn x hx
    obtain ⟨key, st, tm⟩ := i
    cases tm with
    | none => simp [hitsAt] at hd
    | some p => exact Int.le_trans hdn (h m hm records now key p.2 x hx)

/-- What firing the `k`-th and then a `j`-th due instance gives, against the other order: the same instances, and the
same effects in some order. -/
def FiredBoth {α β : Type} (fireK : Nat → α → α × List β) (count : α → Nat) (l : α) (k1 k2 : Nat) : Prop :=
  ∃ j < count (fireK k1 l).1, ∃ i < count (fireK k2 l).1,
    (fireK j (fireK k1 l).1).1 = (fireK i (fireK k2 l).1).1 ∧
      ((fireK k1 l).2 ++ (fireK j (fireK k1 l).1).2).Perm ((fireK k2 l).2 ++ (fireK i (fireK k2 l).1).2)

theorem FiredBoth.flip {α β : Type} {fireK : Nat → α → α × List β} {count : α → Nat} {l : α} {k1 k2 : Nat} :
    FiredBoth fireK count l k1 k2 → FiredBoth fireK count l k2 k1
  | ⟨j, hj, i, hi, he, hp⟩ => ⟨i, hi, j, hj, he.symm, hp.symm⟩

variable (m : MachineV r e) (records : r.den0) (now d : Int)

theorem fireNth_skip {i : Instance m} (h : hitsAt d i = false) (k : Nat) (is : List (Instance m)) :
    fireNth m records now d k (i :: is) = (i :: (fireNth m records now d k is).1, (fireNth m records now d k is).2) := by
  simp [fireNth, h]

theorem fireNth_succ {i : Instance m} (h : hitsAt d i = true) (k : Nat) (is : List (Instance m)) :
    fireNth m records now d (k + 1) (i :: is) = (i :: (fireNth m records now d k is).1, (fireNth m records now d k is).2) := by
  simp [fireNth, h]

theorem fireNth_zero {i : Instance m} (h : hitsAt d i = true) (is : List (Instance m)) :
    fireNth m records now d 0 (i :: is) = ((fired m records now i).1 :: is, (fired m records now i).2) := by
  simp [fireNth, h]

/-- The instance in front fires and one behind it fires: each order fires both. -/
theorem fireNth_head (i : Instance m) (is : List (Instance m)) (hi : hitsAt d i = true) (k : Nat)
    (hk : k < is.countP (hitsAt d)) : FiredBoth (fireNth m records now d) (List.countP (hitsAt d)) (i :: is) 0 (k + 1) := by
  unfold FiredBoth
  rw [fireNth_zero m records now d hi, fireNth_succ m records now d hi]
  cases hf : hitsAt d (fired m records now i).1
  · refine ⟨k, by simp [hf, hk], 0, by simp [hi], ?_⟩
    rw [fireNth_skip m records now d hf, fireNth_zero m records now d hi]
    exact ⟨rfl, List.perm_append_comm⟩
  · refine ⟨k + 1, by simp [hf, hk], 0, by simp [hi], ?_⟩
    rw [fireNth_succ m records now d hf, fireNth_zero m records now d hi]
    exact ⟨rfl, List.perm_append_comm⟩

theorem fireNth_comm : (l : List (Instance m)) → (k1 k2 : Nat) → k1 < l.countP (hitsAt d) →
    k2 < l.countP (hitsAt d) → k1 ≠ k2 → FiredBoth (fireNth m records now d) (List.countP (hitsAt d)) l k1 k2
  | [], _, _, h, _, _ => by simp at h
  | i :: is, k1, k2, h1, h2, hne => by
    cases hi : hitsAt d i with
    | false =>
      simp only [List.countP_cons, hi] at h1 h2
      obtain ⟨j, hj, i', hi', he, hp⟩ := fireNth_comm is k1 k2 (by simpa using h1) (by simpa using h2) hne
      simp only [FiredBoth, fireNth_skip m records now d hi, List.countP_cons, hi]
      exact ⟨j, by simpa using hj, i', by simpa using hi', by rw [he], hp⟩
    | true =>
      simp only [List.countP_cons, hi, ite_true] at h1 h2
      match k1, k2, hne with
      | 0, 0, hne => exact absurd rfl hne
      | 0, k + 1, _ => exact fireNth_head m records now d i is hi k (by omega)
      | k + 1, 0, _ => exact (fireNth_head m records now d i is hi k (by omega)).flip
      | k + 1, k' + 1, hne =>
        obtain ⟨j, hj, i', hi', he, hp⟩ :=
          fireNth_comm is k k' (by omega) (by omega) (fun h => hne (congrArg (· + 1) h))
        simp only [FiredBoth, fireNth_succ m records now d hi, List.countP_cons, hi, ite_true]
        refine ⟨j + 1, by omega, i' + 1, by omega, ?_⟩
        rw [fireNth_succ m records now d hi, fireNth_succ m records now d hi, he]
        exact ⟨rfl, hp⟩

variable {m records now d}

theorem fireMachinesAt_lt {k : Nat} {insts : List (Instance m)} {ms : List (MachineV r e)} (rest : Machines ms)
    (h : k < insts.countP (hitsAt d)) : fireMachinesAt records now d k (.cons insts rest) =
      (.cons (fireNth m records now d k insts).1 rest, (fireNth m records now d k insts).2) := by
  simp [fireMachinesAt, h]

theorem fireMachinesAt_ge {k : Nat} {insts : List (Instance m)} {ms : List (MachineV r e)} (rest : Machines ms)
    (h : insts.countP (hitsAt d) ≤ k) : fireMachinesAt records now d k (.cons insts rest) =
      (.cons insts (fireMachinesAt records now d (k - insts.countP (hitsAt d)) rest).1,
        (fireMachinesAt records now d (k - insts.countP (hitsAt d)) rest).2) := by
  simp [fireMachinesAt, Nat.not_lt.2 h]

theorem hitCount_cons (insts : List (Instance m)) {ms : List (MachineV r e)} (rest : Machines ms) :
    hitCount d (.cons insts rest) = insts.countP (hitsAt d) + hitCount d rest := rfl

/-- A timer of the first machine fires and one of a later machine fires: each order fires both. -/
theorem fireMachinesAt_apart (insts : List (Instance m)) {ms : List (MachineV r e)} (rest : Machines ms) (k1 k2 : Nat)
    (h1 : k1 < insts.countP (hitsAt d)) (h2 : insts.countP (hitsAt d) ≤ k2)
    (h2' : k2 < insts.countP (hitsAt d) + hitCount d rest) :
    FiredBoth (fun k l => fireMachinesAt records now d k l) (fun l => hitCount d l) (.cons insts rest) k1 k2 := by
  dsimp only [FiredBoth]
  rw [fireMachinesAt_lt rest h1, fireMachinesAt_ge rest h2]
  refine ⟨(fireNth m records now d k1 insts).1.countP (hitsAt d) + (k2 - insts.countP (hitsAt d)),
    by rw [hitCount_cons]; omega, k1, by rw [hitCount_cons]; omega, ?_⟩
  rw [fireMachinesAt_ge _ (by omega), fireMachinesAt_lt _ h1, Nat.add_sub_cancel_left]
  exact ⟨rfl, List.perm_append_comm⟩

theorem fireMachinesAt_comm : {ms : List (MachineV r e)} → (l : Machines ms) → (k1 k2 : Nat) → k1 < hitCount d l →
    k2 < hitCount d l → k1 ≠ k2 → FiredBoth (fun k l => fireMachinesAt records now d k l) (fun l => hitCount d l) l k1 k2
  | _, .nil, _, _, h, _, _ => by simp [hitCount] at h
  | _, .cons insts rest, k1, k2, h1, h2, hne => by
    rw [hitCount_cons] at h1 h2
    by_cases c1 : k1 < insts.countP (hitsAt d) <;> by_cases c2 : k2 < insts.countP (hitsAt d)
    · obtain ⟨j, hj, i, hi, he, hp⟩ := fireNth_comm _ records now d insts k1 k2 c1 c2 hne
      dsimp only [FiredBoth]
      rw [fireMachinesAt_lt rest c1, fireMachinesAt_lt rest c2]
      refine ⟨j, by rw [hitCount_cons]; omega, i, by rw [hitCount_cons]; omega, ?_⟩
      rw [fireMachinesAt_lt rest hj, fireMachinesAt_lt rest hi, he]
      exact ⟨rfl, hp⟩
    · exact fireMachinesAt_apart insts rest k1 k2 c1 (by omega) (by omega)
    · exact (fireMachinesAt_apart insts rest k2 k1 c2 (by omega) (by omega)).flip
    · obtain ⟨j, hj, i, hi, he, hp⟩ := fireMachinesAt_comm rest (k1 - insts.countP (hitsAt d))
        (k2 - insts.countP (hitsAt d)) (by omega) (by omega) (by omega)
      dsimp only at hj hi he hp
      dsimp only [FiredBoth]
      rw [fireMachinesAt_ge rest (by omega), fireMachinesAt_ge rest (by omega)]
      refine ⟨insts.countP (hitsAt d) + j, by rw [hitCount_cons]; omega, insts.countP (hitsAt d) + i,
        by rw [hitCount_cons]; omega, ?_⟩
      rw [fireMachinesAt_ge _ (by omega), fireMachinesAt_ge _ (by omega), Nat.add_sub_cancel_left,
        Nat.add_sub_cancel_left, he]
      exact ⟨rfl, hp⟩

/-- An instance after `fireNth` was there before, or is one that fired at `d`. -/
theorem mem_fireNth {k : Nat} : {l : List (Instance m)} → ∀ y ∈ (fireNth m records now d k l).1,
    y ∈ l ∨ ∃ i ∈ l, hitsAt d i = true ∧ y = (fired m records now i).1
  | [], _, h => by simp [fireNth] at h
  | i :: is, y, h => by
    unfold fireNth at h
    split at h
    · next hi =>
      split at h
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inr ⟨i, List.mem_cons_self, hi, rfl⟩
        · exact .inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inl List.mem_cons_self
        · rcases mem_fireNth y h with h | ⟨j, hj, hd, rfl⟩
          · exact .inl (List.mem_cons_of_mem _ h)
          · exact .inr ⟨j, List.mem_cons_of_mem _ hj, hd, rfl⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl List.mem_cons_self
      · rcases mem_fireNth y h with h | ⟨j, hj, hd, rfl⟩
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr ⟨j, List.mem_cons_of_mem _ hj, hd, rfl⟩

theorem dues_cons (insts : List (Instance m)) {ms : List (MachineV r e)} (rest : Machines ms) :
    dues (PerMachine.cons insts rest).toSigma now =
      insts.filterMap (fun i => i.timer.bind fun (d', _) => if d' ≤ now then some d' else none) ++ dues rest.toSigma now := by
  simp [dues]

theorem mem_dues_filterMap {l : List (Instance m)} {x : Int} :
    x ∈ l.filterMap (fun i => i.timer.bind fun (d', _) => if d' ≤ now then some d' else none) ↔
      ∃ i ∈ l, ∃ st, i.timer = some (x, st) ∧ x ≤ now := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, h⟩
    cases ht : i.timer with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨d', st⟩ := p
      simp only [ht, Option.bind_some] at h
      split at h
      · cases h; exact ⟨i, hi, st, ht, by assumption⟩
      · cases h
  · rintro ⟨i, hi, st, ht, hx⟩
    exact ⟨i, hi, by simp [ht, hx]⟩


/-- Every instance of `l` whose timer fires sets no timer before its deadline, at these records and this time: what
`FiresForward` says of the instances one state holds. -/
def FiresAt (records : r.den0) (now : Int) : {ms : List (MachineV r e)} → Machines ms → Prop
  | [], .nil => True
  | m :: _, .cons insts rest => (∀ i ∈ insts, ∀ d : Int, hitsAt d i = true → d ≤ now →
      ∀ x ∈ (fired m records now i).1.timer, d ≤ x.1) ∧ FiresAt records now rest

theorem firesAt_of {ms : List (MachineV r e)} (hF : FiresForward ms) (records : r.den0) (now : Int) :
    (l : Machines ms) → FiresAt records now l
  | .nil => trivial
  | .cons _ rest => ⟨fun i _ d hd hdn => hF _ List.mem_cons_self records now d i hd hdn,
      firesAt_of (fun m hm => hF m (List.mem_cons_of_mem _ hm)) records now rest⟩

theorem dues_fireAt_ge {k : Nat} {now0 : Int} (hd0 : d ≤ now) : {ms : List (MachineV r e)} → (l : Machines ms) →
    FiresAt records now l → (∀ x ∈ dues l.toSigma now0, d ≤ x) →
    ∀ x ∈ dues (fireMachinesAt records now d k l).1.toSigma now0, d ≤ x
  | _, .nil, _, _, x, hx => by simp [fireMachinesAt, dues] at hx
  | _, .cons insts rest, hF, hl, x, hx => by
    rw [dues_cons] at hl
    by_cases hk : k < insts.countP (hitsAt d)
    · rw [fireMachinesAt_lt rest hk, dues_cons, List.mem_append, mem_dues_filterMap] at hx
      rcases hx with ⟨y, hy, st, ht, hx⟩ | hx
      · rcases mem_fireNth y hy with hy | ⟨i, hi, hh, rfl⟩
        · exact hl x (List.mem_append_left _ (mem_dues_filterMap.2 ⟨y, hy, st, ht, hx⟩))
        · exact hF.1 i hi d hh hd0 (x, st) ht
      · exact hl x (List.mem_append_right _ hx)
    · rw [fireMachinesAt_ge rest (by omega), dues_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hl x (List.mem_append_left _ hx)
      · exact dues_fireAt_ge hd0 rest hF.2 (fun y hy => hl y (List.mem_append_right _ hy)) x hx

theorem mem_dues_of_hit {now0 : Int} (hd : d ≤ now0) : {ms : List (MachineV r e)} → (l : Machines ms) →
    0 < hitCount d l → d ∈ dues l.toSigma now0
  | _, .nil, h => by simp [hitCount] at h
  | _, .cons insts rest, h => by
    rw [dues_cons, List.mem_append, mem_dues_filterMap]
    rw [hitCount_cons] at h
    by_cases hc : 0 < insts.countP (hitsAt d)
    · obtain ⟨i, hi, hh⟩ := List.countP_pos_iff.1 hc
      unfold hitsAt at hh
      split at hh
      · next d' st ht => exact .inl ⟨i, hi, st, by simp at hh; rw [ht, hh], hd⟩
      · cases hh
    · exact .inr (mem_dues_of_hit hd rest (by omega))

theorem le_of_mem_dues {ms : List (MachineState r e)} {now0 x : Int} (h : x ∈ dues ms now0) : x ≤ now0 := by
  simp only [dues, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨_, _, i, _, h⟩ := h
  cases ht : i.timer with
  | none => simp [ht] at h
  | some p =>
    simp only [ht, Option.bind_some] at h
    split at h
    · cases h; assumption
    · cases h

/-- Results of a clock line's timers that are the same state, with the same effects in some order. -/
def TimerEq {v : ServiceV} (a b : State v × List (Sender × EffectV v.event)) : Prop := a.1 = b.1 ∧ a.2.Perm b.2

theorem timerEq_equiv {v : ServiceV} : Diamond.Equiv (TimerEq (v := v)) :=
  ⟨fun _ => ⟨rfl, .refl _⟩, fun ⟨h, p⟩ => ⟨h.symm, p.symm⟩, fun ⟨h, p⟩ ⟨h', p'⟩ => ⟨h.trans h', p.trans p'⟩⟩

theorem timerSys_simulates {v : ServiceV} : Diamond.Simulates (timerSys v) TimerEq := by
  rintro ⟨s, acc⟩ ⟨s', acc'⟩ ⟨rfl, hp⟩
  refine ⟨rfl, fun i hi => ⟨i, hi, .inl ?_⟩⟩
  simp only [timerSys]
  split
  · exact ⟨rfl, hp⟩
  · exact ⟨rfl, hp.append_right _⟩

theorem timerSys_commutes {v : ServiceV} {I : State v × List (Sender × EffectV v.event) → Prop}
    (hF : ∀ a, I a → FiresAt a.1.records a.1.now a.1.machines) :
    Diamond.Commutes (timerSys v) I TimerEq := by
  rintro ⟨s, acc⟩ hI i j hi hj hij b hb
  simp only [timerSys] at hi hj hb ⊢
  cases hm : (dues s.machines.toSigma s.now).min? with
  | none => rw [hm] at hi; exact absurd hi (Nat.not_lt_zero _)
  | some d =>
    rw [hm] at hi hj hb
    obtain ⟨hdm, hdl⟩ := List.min?_eq_some_iff.1 hm
    have hdn : d ≤ s.now := le_of_mem_dues hdm
    obtain ⟨j', hj', i', hi', he, hp⟩ := fireMachinesAt_comm (records := s.records) (now := s.now) s.machines i j hi hj hij
    dsimp only at hj' hi' he hp
    cases hb
    refine ⟨fun c hc => ?_, fun e he => by split at he <;> cases he⟩
    cases hc
    have keep : ∀ k, 0 < hitCount d (fireMachinesAt s.records s.now d k s.machines).1 →
        (dues (fireMachinesAt s.records s.now d k s.machines).1.toSigma s.now).min? = some d := fun k hk =>
      List.min?_eq_some_iff.2 ⟨mem_dues_of_hit hdn _ hk, dues_fireAt_ge hdn s.machines (hF _ hI) hdl⟩
    refine ⟨j', ?_, i', ?_, ?_⟩
    · simp only [keep i (by omega)]; exact hj'
    · simp only [keep j (by omega)]; exact hi'
    · simp only [keep i (by omega), keep j (by omega)]
      refine .inl ⟨by rw [he], ?_⟩
      simp only [List.append_assoc]
      exact hp.append_left acc

/-- Where timers fire forward, every order of the timers due at one deadline of a clock line ends as `fire` does: the
same state, and the same effects in some order. -/
theorem timers_agree {v : ServiceV} (hF : FiresForward v.machines) (fuel : Nat) (s : State v)
    {r : Except Fault (State v × List (Sender × EffectV v.event))} (hr : Diamond.Runs (timerSys v) fuel (s, []) r) :
    Diamond.Agree TimerEq r (fireResult s (fuel + 1)) :=
  fire_agrees timerEq_equiv timerSys_simulates (I := fun _ => True)
    (timerSys_commutes fun a _ => firesAt_of hF a.1.records a.1.now a.1.machines) (fun _ _ _ _ _ _ => trivial) fuel s
    trivial hr

/-- Where the timers of every state a clock line's firing reaches in any order fire forward there, every order of the
timers due at one deadline ends as `fire` does: the same state, and the same effects in some order. -/
theorem timers_agree_at {v : ServiceV} (fuel : Nat) (s : State v)
    (hF : ∀ a, Diamond.Reach (timerSys v) (s, []) a → FiresAt a.1.records a.1.now a.1.machines)
    {r : Except Fault (State v × List (Sender × EffectV v.event))} (hr : Diamond.Runs (timerSys v) fuel (s, []) r) :
    Diamond.Agree TimerEq r (fireResult s (fuel + 1)) :=
  fire_agrees timerEq_equiv timerSys_simulates (timerSys_commutes hF) (Diamond.reach_preserved _ _) fuel s .refl hr

end Timers

end Step

end Tazuna.Ir
