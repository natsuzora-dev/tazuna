import Tazuna.Semantics.Reach

/-! What every state a step reaches keeps: pending wire ids are distinct and below the next wire id, every pending
request's kept functions are records of the program's sites `P`, and so are the machines' effect functions. The
symbolic state codes only such states: a pending table has distinct keys and holds closures by their site, and the
step writes a new request at the next id. `step_inv` proves each step keeps the invariant, so it holds of every state a
run reaches (`run_inv`). -/

namespace Tazuna.Ir

namespace Step

variable (P : List AnySite) {v : ServiceV}

structure Inv (s : State v) : Prop where
  below : ∀ p ∈ s.pending, p.id < s.nextId
  nodup : (s.pending.map (·.id)).Nodup
  reach : ∀ p ∈ s.pending, (EffectV.request p.request).Reach P
  machines : ∀ ms ∈ s.machines, ms.1.Reach P

variable {P}

theorem Inv.congr {s s' : State v} (h : Inv P s) (hp : s'.pending = s.pending) (hn : s'.nextId = s.nextId)
    (hm : s'.machines = s.machines) : Inv P s' :=
  ⟨hp ▸ hn ▸ h.below, hp ▸ h.nodup, hp ▸ h.reach, hm ▸ h.machines⟩

theorem init_inv (hv : v.Reach P) : Inv P (State.init v) :=
  ⟨by simp [State.init], by simp [State.init], by simp [State.init], by
    intro ms h
    simp only [State.init, List.mem_map] at h
    obtain ⟨m, hm, rfl⟩ := h
    exact hv.1 m hm⟩

/-- Effects whose kept functions are records of `P`. -/
def EffsReach (P : List AnySite) {e : Ty} (effs : List (Sender × EffectV e)) : Prop := ∀ x ∈ effs, x.2.Reach P

theorem start_inv (a : Acc v) (effs : List (Sender × EffectV v.event)) (ha : Inv P a.state) (he : EffsReach P effs)
    {a' : Acc v} (h : start a effs = .ok a') : Inv P a'.state := by
  induction effs generalizing a with
  | nil => simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ ha
  | cons x effs ih =>
    obtain ⟨snd, eff⟩ := x
    simp only [start, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      refine ih a1 ?_ (fun y hy => he y (by simp [hy])) h
      have hx : eff.Reach P := he (snd, eff) (by simp)
      revert h1
      cases eff with
      | request r =>
        simp only
        split
        · intro h1; cases h1
        · rename_i x _
          intro h1
          cases h1
          refine ⟨?_, ?_, ?_, ha.machines⟩
          · intro p hp
            rcases List.mem_append.1 hp with hp | hp
            · exact Nat.lt_succ_of_lt (ha.below p hp)
            · simp only [List.mem_singleton] at hp; subst hp; exact Nat.lt_succ_self _
          · rw [List.map_append, List.nodup_append]
            refine ⟨ha.nodup, by simp, ?_⟩
            intro a hap b hb
            simp only [List.mem_singleton, List.mem_map] at hb hap
            obtain ⟨p, hp, rfl⟩ := hap
            obtain ⟨_, rfl, rfl⟩ := hb
            exact Nat.ne_of_lt (ha.below p hp)
          · intro p hp
            rcases List.mem_append.1 hp with hp | hp
            · exact ha.reach p hp
            · simp only [List.mem_singleton] at hp; subst hp; exact hx
      | command => intro h1; cases h1; exact ha
      | query => intro h1; cases h1; exact ha

theorem enter_reach {r e : Ty} (m : MachineV r e) (hm : m.Reach P) (records : r.den0) (now : Int)
    (key : m.key.den0) (st : m.state.den0) : EffsReach P (enter m records now key st).2 := by
  intro x hx
  simp only [enter, List.mem_map, Option.mem_toList] at hx
  obtain ⟨eff, heff, rfl⟩ := hx
  exact MachineV.reach_effectAt P m hm key st records now eff heff

theorem reactKey_reach {r e : Ty} (m : MachineV r e) (hm : m.Reach P) (insts : List (Instance m))
    (records : r.den0) (now : Int) (ev : e.den0) (k : m.key.den0) : EffsReach P (reactKey m insts records now ev k).2 := by
  unfold reactKey
  split
  · split
    · exact enter_reach m hm _ _ _ _
    · intro x hx; cases hx
  · exact enter_reach m hm _ _ _ _

theorem machineStep_reach {r e : Ty} (T : List TypeDecl) (records : r.den0) (now : Int) (ev : e.den0)
    (ms : MachineState r e) (hm : ms.1.Reach P) :
    (machineStep T records now ev ms).1.1 = ms.1 ∧ EffsReach P (machineStep T records now ev ms).2 := by
  obtain ⟨m, insts⟩ := ms
  refine ⟨rfl, fun x hx => ?_⟩
  simp only [machineStep, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, ⟨k, -, rfl⟩, hx⟩ := hx
  exact reactKey_reach m hm insts records now ev k x hx

theorem react_inv (T : List TypeDecl) (hv : v.Reach P) (s : State v) (ev : v.event.den0) (hs : Inv P s) :
    Inv P (react T s ev).1 ∧ EffsReach P (react T s ev).2 := by
  let records := v.apply.fn (s.records, ev, ())
  let f := fun (acc : List (MachineState v.records v.event) × List (Sender × EffectV v.event)) ms0 =>
    let (m', es) := machineStep T records s.now ev ms0; (acc.1 ++ [m'], acc.2 ++ es)
  have hfold := foldl_inv (fun (acc : List (MachineState v.records v.event) × List (Sender × EffectV v.event)) =>
      (∀ ms ∈ acc.1, ms.1.Reach P) ∧ EffsReach P acc.2) (fun ms0 => ms0.1.Reach P) f
    (fun ⟨ms, effs⟩ ms0 ⟨h1, h2⟩ h0 => by
      obtain ⟨hk, he⟩ := machineStep_reach T records s.now ev ms0 h0
      refine ⟨fun ms' hms' => ?_, fun x hx => ?_⟩
      · rcases List.mem_append.1 hms' with h | h
        · exact h1 ms' h
        · simp only [List.mem_singleton] at h; subst h; rw [hk]; exact h0
      · rcases List.mem_append.1 hx with h | h
        · exact h2 x h
        · exact he x h)
    s.machines ([], []) hs.machines ⟨by simp, by intro x hx; cases hx⟩
  have hr : EffsReach P (v.reactions.flatMap fun x => (x.effectsAt ev records s.now).map (Sender.reaction x.name, ·)) := by
    intro y hy
    simp only [List.mem_flatMap, List.mem_map] at hy
    obtain ⟨x, hx, eff, heff, rfl⟩ := hy
    exact ReactionV.reach_effectsAt P x (hv.2 x hx) ev records s.now eff heff
  have hm : (react T s ev).1.machines = (s.machines.foldl f ([], [])).1 := rfl
  have he : (react T s ev).2 = (s.machines.foldl f ([], [])).2 ++
      v.reactions.flatMap fun x => (x.effectsAt ev records s.now).map (Sender.reaction x.name, ·) := rfl
  refine ⟨⟨hs.below, hs.nodup, hs.reach, hm ▸ hfold.1⟩, fun x hx => ?_⟩
  rw [he] at hx
  rcases List.mem_append.1 hx with h | h
  · exact hfold.2 x h
  · exact hr x h

theorem applyEvents_inv (T : List TypeDecl) (hv : v.Reach P) (events : List v.event.den0) :
    (a : Acc v) → Inv P a.state → {a' : Acc v} → applyEvents T a events = .ok a' → Inv P a'.state := by
  induction events with
  | nil => intro a ha a' h; simp only [applyEvents, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ ha
  | cons ev events ih =>
    intro a ha a' h
    simp only [applyEvents, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      obtain ⟨hs, he⟩ := react_inv T hv a.state ev ha
      exact ih a1 (start_inv _ _ hs he h1) h

theorem runCommand_inv (T : List TypeDecl) (hv : v.Reach P) (a : Acc v) (ha : Inv P a.state)
    (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (onAnswer : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) {a' : Acc v}
    (h : runCommand T a x caller input onAnswer = .ok a') : Inv P a'.state := by
  have hfresh : ∀ k, Inv P ({ a with state := { a.state with fresh := k } } : Acc v).state :=
    fun _ => Inv.congr ha rfl rfl rfl
  simp only [runCommand] at h
  split at h
  · cases h
  · simp only [bind, Except.bind] at h
    split at h
    · split at h
      · cases h
      · rename_i a1 h1
        have h1' := applyEvents_inv T hv _ _ (hfresh _) h1
        split at h
        · cases h
        · exact applyEvents_inv T hv _ _ h1' h
    · exact applyEvents_inv T hv _ _ (hfresh _) h

theorem runQuery_inv (T : List TypeDecl) (hv : v.Reach P) (a : Acc v) (ha : Inv P a.state)
    (x : QueryV v.records v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (onAnswer : Fun (Ty.fn [x.output] (.list v.event))) {a' : Acc v}
    (h : runQuery T a x caller input onAnswer = .ok a') : Inv P a'.state := by
  simp only [runQuery] at h
  split at h
  · cases h
  · exact applyEvents_inv T hv _ _ ha h

theorem runOwn_inv (T : List TypeDecl) (hv : v.Reach P) (a : Acc v) (ha : Inv P a.state) (eff : EffectV v.event)
    {a' : Acc v} (h : runOwn T a eff = .ok a') : Inv P a'.state := by
  revert h
  cases eff with
  | request => intro h; simp only [runOwn, Except.ok.injEq] at h; exact h ▸ ha
  | command name c i j caller value onAnswer =>
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
        exact fun h => runCommand_inv T hv a ha x _ _ _ h
  | query name c i o caller value onAnswer =>
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
        exact fun h => runQuery_inv T hv a ha x _ _ _ h

theorem settle_inv (T : List TypeDecl) (hv : v.Reach P) : (fuel : Nat) → (a : Acc v) → Inv P a.state →
    {a' : Acc v} → settle T fuel a = .ok a' → Inv P a'.state
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
        exact settle_inv T hv f a1 (runOwn_inv T hv { a with own := rest } (Inv.congr ha rfl rfl rfl) eff h1) h

theorem finish_inv (T : List TypeDecl) (hv : v.Reach P) (s0 : State v) (hs : Inv P s0) (x : Except Fault (Acc v))
    (hx : ∀ a, x = .ok a → Inv P a.state) (o : Outcome) : Inv P (finish T s0 x o).state := by
  unfold finish
  split
  · exact hs
  · rename_i a ha
    split
    · exact hs
    · cases x with
      | error e => cases ha
      | ok a0 => exact settle_inv T hv _ a0 (hx a0 rfl) ha

abbrev FireAcc (v : ServiceV) := List (MachineState v.records v.event) × List (Sender × EffectV v.event) × Bool

def FireOk (P : List AnySite) {v : ServiceV} (acc : FireAcc v) : Prop :=
  (∀ ms ∈ acc.1, ms.1.Reach P) ∧ EffsReach P acc.2.1

theorem fire_inv (s : State v) (hs : Inv P s) : (fuel : Nat) → {r : State v × List (Sender × EffectV v.event)} →
    fire s fuel = some r → Inv P r.1 ∧ EffsReach P r.2
  | 0, _, h => by cases h
  | fuel + 1, r, h => by
    rw [fire] at h
    split at h
    · cases h; exact ⟨hs, by intro x hx; cases hx⟩
    · rename_i d _
      have key : ∀ (F : FireAcc v → MachineState v.records v.event → FireAcc v),
          (∀ b ms0, FireOk P b → ms0.1.Reach P → FireOk P (F b ms0)) →
          ∀ {mach effs done}, s.machines.foldl F ([], [], false) = (mach, effs, done) →
          ∀ {r : State v × List (Sender × EffectV v.event)},
            Option.map (fun x => (x.1, effs ++ x.2)) (fire { s with machines := mach } fuel) = some r →
            Inv P r.1 ∧ EffsReach P r.2 := by
        intro F hF mach effs done hR r h
        have hfold := foldl_inv (FireOk P) (fun ms0 => ms0.1.Reach P) F hF s.machines ([], [], false) hs.machines
          ⟨by simp, by intro x hx; cases hx⟩
        rw [hR] at hfold
        obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨h1, h2⟩ := fire_inv { s with machines := mach } ⟨hs.below, hs.nodup, hs.reach, hfold.1⟩ fuel hr
        exact ⟨h1, fun x hx => (List.mem_append.1 hx).elim (hfold.2 x) (h2 x)⟩
      have hinner : ∀ (m : MachineV v.records v.event)
          (G : List (Instance m) × List (Sender × EffectV v.event) × Bool → Instance m →
            List (Instance m) × List (Sender × EffectV v.event) × Bool),
          (∀ b i, EffsReach P b.2.1 → EffsReach P (G b i).2.1) → ∀ (insts : List (Instance m))
            (acc : List (Instance m) × List (Sender × EffectV v.event) × Bool), EffsReach P acc.2.1 →
            EffsReach P (insts.foldl G acc).2.1 := fun m G hG insts acc h0 =>
        foldl_inv (fun acc => EffsReach P acc.2.1) (fun _ => True) G (fun b i h _ => hG b i h) insts acc
          (fun _ _ => trivial) h0
      split at h
      rename_i heq
      refine key _ ?_ heq h
      rintro ⟨ms, effs, done⟩ ⟨m, insts⟩ ⟨h1, h2⟩ h0
      refine ⟨fun ms' hms' => ?_, ?_⟩
      · simp only at hms'
        rcases List.mem_append.1 hms' with h | h
        · exact h1 ms' h
        · simp only [List.mem_singleton] at h; subst h; exact h0
      · refine hinner m _ ?_ insts _ h2
        rintro ⟨acc, effs, done⟩ i h
        dsimp only
        split
        · split
          · intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact h x hx
            · exact enter_reach m h0 _ _ _ _ x hx
          · exact h
        · exact h

end Step

open Step

/-- Every step keeps the invariant. -/
theorem step_inv (T : List TypeDecl) {P : List AnySite} {v : ServiceV} (hv : v.Reach P) (s : State v)
    (hs : Inv P s) (i : Input v) : Inv P (step T v s i).state := by
  have hfresh : ∀ k, Inv P ({ s with fresh := k } : State v) := fun _ => Inv.congr hs rfl rfl rfl
  cases i with
  | command i caller input =>
    simp only [step]
    split
    · exact hfresh _
    · split
      · exact hfresh _
      · split
        · exact hfresh _
        · rename_i a ha
          split
          · exact hfresh _
          · exact finish_inv T hv _ (hfresh _) _ (fun a' h => by
              cases h; exact applyEvents_inv T hv _ _ (hfresh _) ha) _
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
        · refine finish_inv T hv _ hs _ (fun a h => applyEvents_inv T hv _ _ ?_ h) _
          refine ⟨fun p hp => hs.below p (List.mem_filter.1 hp).1, ?_, fun p hp => hs.reach p (List.mem_filter.1 hp).1,
            hs.machines⟩
          exact (List.filter_sublist.map _).nodup hs.nodup
  | event i value => exact finish_inv T hv _ hs _ (fun a h => applyEvents_inv T hv _ _ hs h) _
  | clock time =>
    simp only [step]
    split
    · exact hs
    · split
      · exact hs
      · rename_i s' effs hr
        exact finish_inv T hv _ hs _ (fun a h =>
          let hf := fire_inv { s with now := time } (Inv.congr hs rfl rfl rfl) _ hr
          start_inv { state := s' } effs hf.1 hf.2 h) _

/-- Every state a run reaches from an invariant state keeps the invariant. -/
theorem run_inv (T : List TypeDecl) {P : List AnySite} {v : ServiceV} (hv : v.Reach P) :
    (s : State v) → Inv P s → (is : List (Input v)) → Inv P (run T v s is).1
  | _, hs, [] => hs
  | s, hs, i :: is => run_inv T hv _ (step_inv T hv s hs i) is

end Tazuna.Ir
