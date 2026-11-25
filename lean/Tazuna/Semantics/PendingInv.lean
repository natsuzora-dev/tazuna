import Tazuna.Semantics.Reach
import Tazuna.Semantics.Fire

/-! What every state a step reaches keeps: pending wire ids are distinct and below the next wire id, every pending
request's kept functions are records of the program's sites `P`, and so are the machines' effect functions. The
symbolic state codes only such states: a pending table has distinct keys and holds closures by their site, and the
step writes a new request at the next id. `step_inv` proves each step keeps the invariant, so it holds of every state a
run reaches (`run_inv`). -/

namespace Tazuna.Ir

/-- An effect from a sender the service's states can name (an instance of one of its machines by its key, or one of
its reactions) whose kept functions are sites that sender can reach. -/
def FromSender (v : ServiceV) (x : Sender × EffectV v.event) : Prop :=
  ∃ ks sd S, ⟨ks, sd, S⟩ ∈ senderShapes v ∧ (Ty.tuple ks).isData = true ∧ (∃ kv, x.1 = sd.sender kv) ∧ x.2.Reach S

/-- The site of a kept function. -/
def Fun.toSite {t : Ty} (f : Fun t) : Site f.Γ t := ⟨f.site, f.G, f.defs, f.hΓ, f.ht, f.body⟩

theorem mem_sitesOf_self {P : List AnySite} {t : Ty} {f : Fun t} (h : f.asSite ∈ P) :
    (⟨f.Γ, f.toSite⟩ : (Γ : List Ty) × Site Γ t) ∈ sitesOf P t := by
  simp only [sitesOf, List.mem_filterMap]
  exact ⟨f.asSite, h, by simp only [Fun.asSite, Ty_same_rfl]; rfl⟩

theorem ownerIn_mem {e : Ty} {r : RequestV e} {ds : List (String × DeclaredV)} {x : String} (h : r.ownerIn ds = some x) :
    ∃ d, (x, d) ∈ ds ∧ r.declaredBy (x, d) = true := by
  simp only [RequestV.ownerIn, Option.map_eq_some_iff] at h
  obtain ⟨⟨x', d⟩, hf, rfl⟩ := h
  exact ⟨d, List.mem_of_find?_eq_some hf, List.find?_some hf⟩

theorem same_eq {a b : Ty} (h : (Ty.same a b).isSome = true) : a = b := by
  obtain ⟨⟨e⟩, -⟩ := Option.isSome_iff_exists.1 h; exact e

/-- A request of a shape of the service's, with its sender's key and its fields, is of the service's shapes. -/
theorem atShapes_of {v : ServiceV} {P : List AnySite} {ks : List Ty} {sd : SenderShape ks}
    (hsd : ⟨ks, sd, P⟩ ∈ senderShapes v) (hks : (Ty.tuple ks).isData = true) {rq : RequestShape v.event}
    (hrq : rq ∈ requestShapes v P) (id : Nat) (fx : Ty.dens (PendingShape.fields { rq with ks, sender := sd, hks })) :
    AtShapes (shapes v) (PendingShape.pending { rq with ks, sender := sd, hks } id fx) := by
  have hsh : ({ rq with ks, sender := sd, hks } : PendingShape v.event) ∈ shapes v := by
    simp only [shapes, List.mem_flatMap]
    exact ⟨⟨ks, sd, P⟩, hsd, by simp only [hks, dite_true]; exact List.mem_map.2 ⟨rq, hrq, rfl⟩⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hsh
  refine ⟨pendingInj _ j hj fx, ?_⟩
  rw [pendingOf_inj]
  rfl

/-- A request an effect of the service starts is of the service's shapes: its sender is one the service names, its
kept functions are sites that sender reaches, and the external that lists it declares its types. -/
theorem atShapes_start {v : ServiceV} {snd : Sender} {r : RequestV v.event} (hs : FromSender v (snd, .request r))
    {x : String} (hx : r.ownerIn v.declared = some x) (id : Nat) :
    AtShapes (shapes v) ⟨id, snd, x, r⟩ := by
  obtain ⟨ks, sd, P, hsd, hks, ⟨kv, rfl⟩, hr⟩ := hs
  obtain ⟨d, hd, hpred⟩ := ownerIn_mem hx
  obtain ⟨hA, hE, hin, hkind⟩ := hr
  obtain ⟨name, input, output, rej, value, ens, onA⟩ := r
  simp only [RequestV.declaredBy] at hpred
  dsimp only at hA hE hin hkind hpred
  cases d with
  | externalCommand n i o j =>
    cases rej with
    | none => simp at hpred
    | some j' =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hpred
      obtain ⟨⟨⟨rfl, hi⟩, ho⟩, hj⟩ := hpred
      obtain rfl := same_eq hi
      obtain rfl := same_eq ho
      obtain rfl := same_eq hj
      cases ens with
      | some _ => simp at hkind
      | none =>
        have hf : (Ty.tuple [i, .tuple [], .tuple onA.Γ]).isData = true := by
          have h1 := onA.hΓ; simp only [Ty.isData, Ty.isDatas] at h1 ⊢; simp [hin, h1]
        let rq : RequestShape v.event := ⟨x, n, i, o, some j, none, onA.Γ, onA.toSite, hf⟩
        have hrq : rq ∈ requestShapes v P := by
          simp only [requestShapes, requestShapesAt, List.mem_flatMap]
          refine ⟨(x, .externalCommand n i o j), hd, ?_⟩
          simp only [List.mem_filterMap]
          exact ⟨⟨onA.Γ, onA.toSite⟩, mem_sitesOf_self hA, by split <;> first | rfl | contradiction⟩
        have h := atShapes_of hsd hks hrq id (Ty.up _ (PendingShape.hdata _) (kv, value, (), onA.env, ()))
        have e : PendingShape.pending { rq with ks, sender := sd, hks } id
            (Ty.up _ (PendingShape.hdata _) (kv, value, (), onA.env, ())) =
            ⟨id, sd.sender kv, x, ⟨n, i, o, some j, value, none, onA⟩⟩ := by
          simp only [PendingShape.pending]; erw [Ty.down_up]; rfl
        exact e ▸ h
  | externalQuery n i o _ =>
    cases rej with
    | some _ => simp at hpred
    | none =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hpred
      obtain ⟨⟨rfl, hi⟩, ho⟩ := hpred
      obtain rfl := same_eq hi
      obtain rfl := same_eq ho
      cases ens with
      | none => simp at hkind
      | some f =>
        have hf : (Ty.tuple [i, .tuple f.Γ, .tuple onA.Γ]).isData = true := by
          have h1 := onA.hΓ; have h2 := f.hΓ
          simp only [Ty.isData, Ty.isDatas] at h1 h2 ⊢; simp [hin, h1, h2]
        let rq : RequestShape v.event := ⟨x, n, i, o, none, some ⟨f.Γ, f.toSite⟩, onA.Γ, onA.toSite, hf⟩
        have hrq : rq ∈ requestShapes v P := by
          simp only [requestShapes, requestShapesAt, List.mem_flatMap]
          refine ⟨(x, .externalQuery n i o _), hd, ?_⟩
          refine List.mem_flatMap.2 ⟨⟨f.Γ, f.toSite⟩, mem_sitesOf_self (hE f rfl), ?_⟩
          simp only [List.mem_filterMap]
          exact ⟨⟨onA.Γ, onA.toSite⟩, mem_sitesOf_self hA, by split <;> first | rfl | contradiction⟩
        have h := atShapes_of hsd hks hrq id (Ty.up _ (PendingShape.hdata _) (kv, value, f.env, onA.env, ()))
        have e : PendingShape.pending { rq with ks, sender := sd, hks } id
            (Ty.up _ (PendingShape.hdata _) (kv, value, f.env, onA.env, ())) =
            ⟨id, sd.sender kv, x, ⟨n, i, o, none, value, some f, onA⟩⟩ := by
          simp only [PendingShape.pending]; erw [Ty.down_up]; rfl
        exact e ▸ h
  | _ => cases rej <;> simp at hpred

namespace Step

variable (P : List AnySite) {v : ServiceV}

structure Inv (s : State v) : Prop where
  below : ∀ p ∈ s.pending, p.id < s.nextId
  nodup : (s.pending.map (·.id)).Nodup
  reach : ∀ p ∈ s.pending, (EffectV.request p.request).Reach P
  /-- Every pending request is of the service's shapes, so a symbolic state can hold it. -/
  shaped : ∀ p ∈ s.pending, AtShapes (shapes v) p

variable {P} {E : List AnyEffectSite}

theorem Inv.congr {s s' : State v} (h : Inv P s) (hp : s'.pending = s.pending) (hn : s'.nextId = s.nextId) :
    Inv P s' :=
  ⟨hp ▸ hn ▸ h.below, hp ▸ h.nodup, hp ▸ h.reach, hp ▸ h.shaped⟩

theorem init_inv : Inv P (State.init v) :=
  ⟨by simp [State.init], by simp [State.init], by simp [State.init], by simp [State.init]⟩

/-- Effects whose kept functions are records of `P`. -/
def EffsReach (P : List AnySite) {e : Ty} (effs : List (Sender × EffectV e)) : Prop := ∀ x ∈ effs, x.2.Reach P

/-- Effects from senders the service names, holding sites their senders reach. -/
def EffsFrom (v : ServiceV) (effs : List (Sender × EffectV v.event)) : Prop := ∀ x ∈ effs, FromSender v x

theorem machine_from {m : MachineV v.records v.event} (hm : m ∈ v.machines) (k : m.key.den0)
    {eff : EffectV v.event} (he : eff.Reach m.effect.usedSites) : FromSender v (.machine m.name ⟨m.key, k⟩, eff) := by
  have hk : m.key.isData = true := by
    have h := m.on.ht
    simp only [Ty.machineCtx, Ty.isData, Ty.isDatas, Ty.isDatass, Bool.and_eq_true] at h
    exact h.1.1.1.1
  refine ⟨[m.key], .machine m.name m.key, _, ?_, by simp [Ty.isData, Ty.isDatas, hk], ⟨(k, ()), rfl⟩, he⟩
  simp only [senderShapes, List.mem_append, List.mem_map]
  exact .inl ⟨m, hm, rfl⟩

theorem reaction_from {x : ReactionV v.records v.event} (hx : x ∈ v.reactions) {eff : EffectV v.event}
    (he : eff.Reach x.react.usedSites) : FromSender v (.reaction x.name, eff) := by
  refine ⟨[], .reaction x.name, _, ?_, rfl, ⟨(), rfl⟩, he⟩
  simp only [senderShapes, List.mem_append, List.mem_map]
  exact .inr ⟨x, hx, rfl⟩

theorem start_inv (a : Acc v) (effs : List (Sender × EffectV v.event)) (ha : Inv P a.state) (he : EffsReach P effs)
    (hf : EffsFrom v effs) {a' : Acc v} (h : start a effs = .ok a') : Inv P a'.state := by
  induction effs generalizing a with
  | nil => simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ ha
  | cons x effs ih =>
    obtain ⟨snd, eff⟩ := x
    simp only [start, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      refine ih a1 ?_ (fun y hy => he y (by simp [hy])) (fun y hy => hf y (by simp [hy])) h
      have hx : eff.Reach P := he (snd, eff) (by simp)
      have hsnd : FromSender v (snd, eff) := hf (snd, eff) (by simp)
      revert h1
      cases eff with
      | request r =>
        simp only
        split
        · intro h1; cases h1
        · rename_i x hxo
          intro h1
          cases h1
          refine ⟨?_, ?_, ?_, ?_⟩
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
          · intro p hp
            rcases List.mem_append.1 hp with hp | hp
            · exact ha.shaped p hp
            · simp only [List.mem_singleton] at hp; subst hp; exact atShapes_start hsnd hxo _
      | command => intro h1; cases h1; exact ha
      | query => intro h1; cases h1; exact ha

theorem enter_reach {r e : Ty} (m : MachineV r e) (hm : m.Reach P E) (records : r.den0) (now : Int)
    (key : m.key.den0) (st : m.state.den0) : EffsReach P (enter m records now key st).2 := by
  intro x hx
  simp only [enter, List.mem_map, Option.mem_toList] at hx
  obtain ⟨eff, heff, rfl⟩ := hx
  exact MachineV.reach_effectAt P m hm.effect key st records now eff heff

theorem reactKey_reach {r e : Ty} (m : MachineV r e) (hm : m.Reach P E) (insts : List (Instance m))
    (records : r.den0) (now : Int) (ev : e.den0) (k : m.key.den0) : EffsReach P (reactKey m insts records now ev k).2 := by
  unfold reactKey
  split
  · split
    · exact enter_reach m hm _ _ _ _
    · intro x hx; cases hx
  · exact enter_reach m hm _ _ _ _

theorem machineStep_reach {r e : Ty} (T : List TypeDecl) (records : r.den0) (now : Int) (ev : e.den0)
    (m : MachineV r e) (insts : List (Instance m)) (hm : m.Reach P E) : EffsReach P (machineStep T records now ev m insts).2 := by
  intro x hx
  simp only [machineStep, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, ⟨k, -, rfl⟩, hx⟩ := hx
  exact reactKey_reach m hm insts records now ev k x hx

/-- The machines after an event are each machine's step, and their effects are the steps' effects in turn. -/
theorem reactMachines_toSigma {r e : Ty} (T : List TypeDecl) (records : r.den0) (now : Int) (ev : e.den0) :
    {ms : List (MachineV r e)} → (xs : Machines ms) →
    (reactMachines T records now ev xs).1.toSigma =
        xs.toSigma.map (fun sm => ⟨sm.1, (machineStep T records now ev sm.1 sm.2).1⟩) ∧
      (reactMachines T records now ev xs).2 = xs.toSigma.flatMap fun sm => (machineStep T records now ev sm.1 sm.2).2
  | _, .nil => ⟨rfl, rfl⟩
  | _, .cons insts rest => by
    obtain ⟨h1, h2⟩ := reactMachines_toSigma T records now ev rest
    simp [reactMachines, h1, h2]

theorem mem_reactMachines_effs {r e : Ty} (T : List TypeDecl) (records : r.den0) (now : Int) (ev : e.den0)
    {ms : List (MachineV r e)} (xs : Machines ms) : ∀ x ∈ (reactMachines T records now ev xs).2,
    ∃ sm ∈ xs.toSigma, x ∈ (machineStep T records now ev sm.1 sm.2).2 := by
  simp [(reactMachines_toSigma T records now ev xs).2]

theorem enter_from {m : MachineV v.records v.event} (hm : m ∈ v.machines) (hr : m.Reach P E) (records : v.records.den0)
    (now : Int) (key : m.key.den0) (st : m.state.den0) : EffsFrom v (enter m records now key st).2 := by
  intro x hx
  simp only [enter, List.mem_map, Option.mem_toList] at hx
  obtain ⟨eff, heff, rfl⟩ := hx
  exact machine_from hm key (MachineV.reach_effectAt _ m (EffectFun.reach_own _ hr.effect) key st records now eff heff)

theorem machineStep_from (T : List TypeDecl) (records : v.records.den0) (now : Int) (ev : v.event.den0)
    (m : MachineV v.records v.event) (insts : List (Instance m)) (hm : m ∈ v.machines) (hr : m.Reach P E) :
    EffsFrom v (machineStep T records now ev m insts).2 := by
  intro x hx
  simp only [machineStep, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, ⟨k, -, rfl⟩, hx⟩ := hx
  revert hx
  unfold reactKey
  split
  · split
    · exact enter_from hm hr _ _ _ _ x
    · intro hx; cases hx
  · exact enter_from hm hr _ _ _ _ x

theorem react_inv (T : List TypeDecl) (hv : v.Reach P E) (s : State v) (ev : v.event.den0) (hs : Inv P s) :
    Inv P (react T s ev).1 ∧ EffsReach P (react T s ev).2 ∧ EffsFrom v (react T s ev).2 := by
  let records := v.apply.fn (s.records, ev, ())
  have hm := mem_reactMachines_effs T records s.now ev s.machines
  refine ⟨⟨hs.below, hs.nodup, hs.reach, hs.shaped⟩, fun x hx => ?_, fun x hx => ?_⟩ <;>
    rcases List.mem_append.1 hx with h | h
  · obtain ⟨sm, hsm, h⟩ := hm x h
    exact machineStep_reach T records s.now ev sm.1 sm.2 (hv.machines _ (PerMachine.fst_mem hsm)) x h
  · simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨y, hy, eff, heff, rfl⟩ := h
    exact ReactionV.reach_effectsAt P y (hv.reactions y hy) ev records s.now eff heff
  · obtain ⟨sm, hsm, h⟩ := hm x h
    exact machineStep_from T records s.now ev sm.1 sm.2 (PerMachine.fst_mem hsm)
      (hv.machines _ (PerMachine.fst_mem hsm)) x h
  · simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨y, hy, eff, heff, rfl⟩ := h
    exact reaction_from hy (ReactionV.reach_effectsAt _ y (EffectFun.reach_own _ (hv.reactions y hy)) ev records s.now
      eff heff)

theorem applyEvents_inv (T : List TypeDecl) (hv : v.Reach P E) (events : List v.event.den0) :
    (a : Acc v) → Inv P a.state → {a' : Acc v} → applyEvents T a events = .ok a' → Inv P a'.state := by
  induction events with
  | nil => intro a ha a' h; simp only [applyEvents, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ ha
  | cons ev events ih =>
    intro a ha a' h
    simp only [applyEvents, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      obtain ⟨hs, he, hf⟩ := react_inv T hv a.state ev ha
      exact ih a1 (start_inv _ _ hs he hf h1) h

/-- What a command leaves: its events applied after the fresh counter advances, or that alone on a rejection. -/
theorem execCommand_acc (T : List TypeDecl) (a : Acc v) (x : CommandV v.records v.event v.caller)
    (caller : v.caller.den0) (input : x.input.den0) {r : Ran v x.rejection} (h : execCommand T a x caller input = .ok r)
    (a' : Acc v) (ha' : r = .accepted a' ∨ ∃ j, r = .rejected a' j) :
    a' = { a with state := { a.state with fresh := a.state.fresh + 1 } } ∨
      ∃ evs, applyEvents T { a with state := { a.state with fresh := a.state.fresh + 1 } } evs = .ok a' := by
  simp only [execCommand] at h
  split at h
  · cases h; rcases ha' with h | ⟨_, h⟩ <;> cases h
  · split at h
    · simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i a1 h1
        split at h
        · cases h
        · cases h; rcases ha' with h | ⟨_, h⟩ <;> cases h; exact .inr ⟨_, h1⟩
    · cases h; rcases ha' with h | ⟨_, h⟩ <;> cases h; exact .inl rfl

theorem execCommand_inv (T : List TypeDecl) (hv : v.Reach P E) (a : Acc v) (ha : Inv P a.state)
    (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0) {r : Ran v x.rejection}
    (h : execCommand T a x caller input = .ok r) (a' : Acc v) (ha' : r = .accepted a' ∨ ∃ j, r = .rejected a' j) :
    Inv P a'.state := by
  rcases execCommand_acc T a x caller input h a' ha' with rfl | ⟨_, he⟩
  · exact Inv.congr ha rfl rfl
  · exact applyEvents_inv T hv _ { a with state := { a.state with fresh := a.state.fresh + 1 } } (Inv.congr ha rfl rfl) he

theorem runCommand_inv (T : List TypeDecl) (hv : v.Reach P E) (a : Acc v) (ha : Inv P a.state)
    (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (onAnswer : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) {a' : Acc v}
    (h : runCommand T a x caller input onAnswer = .ok a') : Inv P a'.state := by
  simp only [runCommand, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    have hi := execCommand_inv T hv a ha x caller input hr
    split at h
    · cases h
    · exact applyEvents_inv T hv _ _ (hi _ (.inl rfl)) h
    · exact applyEvents_inv T hv _ _ (hi _ (.inr ⟨_, rfl⟩)) h

theorem runQuery_inv (T : List TypeDecl) (hv : v.Reach P E) (a : Acc v) (ha : Inv P a.state)
    (x : QueryV v.records v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (onAnswer : Fun (Ty.fn [x.output] (.list v.event))) {a' : Acc v}
    (h : runQuery T a x caller input onAnswer = .ok a') : Inv P a'.state := by
  simp only [runQuery] at h
  split at h
  · cases h
  · exact applyEvents_inv T hv _ { a with state := { a.state with fresh := a.state.fresh + 1 } } ⟨ha.1, ha.2, ha.3, ha.4⟩ h

theorem runOwn_inv (T : List TypeDecl) (hv : v.Reach P E) (a : Acc v) (ha : Inv P a.state) (eff : OwnEffectV v.event)
    {a' : Acc v} (h : runOwn T a eff = .ok a') : Inv P a'.state := by
  revert h
  cases eff with
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

theorem settle_inv (T : List TypeDecl) (hv : v.Reach P E) : (fuel : Nat) → (a : Acc v) → Inv P a.state →
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
        exact settle_inv T hv f a1 (runOwn_inv T hv { a with own := rest } (Inv.congr ha rfl rfl) eff h1) h

theorem finish_inv (T : List TypeDecl) (hv : v.Reach P E) (s0 : State v) (hs : Inv P s0) (x : Except Fault (Acc v))
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

/-- The own queue holds own commands and queries whose kept functions are records of `P`: an internal step runs
each at the site its `on_answer` names. -/
def QueueOk (P : List AnySite) (a : Acc v) : Prop := ∀ x ∈ a.own, x.effect.Reach P

theorem start_queue (a : Acc v) (effs : List (Sender × EffectV v.event)) {a' : Acc v} (h : start a effs = .ok a')
    (ha : QueueOk P a) (he : EffsReach P effs) : QueueOk P a' := by
  induction effs generalizing a with
  | nil => simp only [start, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ ha
  | cons x effs ih =>
    obtain ⟨snd, eff⟩ := x
    simp only [start, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      refine ih a1 h ?_ (fun y hy => he y (by simp [hy]))
      have hx : eff.Reach P := he (snd, eff) (by simp)
      revert h1
      cases eff with
      | request r =>
        simp only
        split
        · intro h1; cases h1
        · intro h1; cases h1; exact ha
      | command =>
        intro h1; cases h1
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact ha y hy
        · simp only [List.mem_singleton] at hy; subst hy; exact hx
      | query =>
        intro h1; cases h1
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact ha y hy
        · simp only [List.mem_singleton] at hy; subst hy; exact hx

theorem applyEvents_queue (T : List TypeDecl) (hv : v.Reach P E) (events : List v.event.den0) :
    (a : Acc v) → {a' : Acc v} → applyEvents T a events = .ok a' → Inv P a.state → QueueOk P a → QueueOk P a' := by
  induction events with
  | nil => intro a a' h _ hq; simp only [applyEvents, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h ▸ hq
  | cons ev events ih =>
    intro a a' h ha hq
    simp only [applyEvents, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i a1 h1
      obtain ⟨hs, he, hf⟩ := react_inv T hv a.state ev ha
      exact ih a1 h (start_inv _ _ hs he hf h1) (start_queue _ _ h1 hq he)

theorem runOwn_queue (T : List TypeDecl) (hv : v.Reach P E) (a : Acc v) (ha : Inv P a.state) (hq : QueueOk P a)
    (eff : OwnEffectV v.event) {a' : Acc v} (h : runOwn T a eff = .ok a') : QueueOk P a' := by
  have hcmd : ∀ (x : CommandV v.records v.event v.caller) caller input onAnswer,
      runCommand T a x caller input onAnswer = .ok a' → QueueOk P a' := by
    intro x caller input onAnswer h
    simp only [runCommand, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      have hq1 : ∀ a1, (r = .accepted a1 ∨ ∃ j, r = .rejected a1 j) → Inv P a1.state ∧ QueueOk P a1 := by
        intro a1 ha1
        refine ⟨execCommand_inv T hv a ha x caller input hr a1 ha1, ?_⟩
        rcases execCommand_acc T a x caller input hr a1 ha1 with rfl | ⟨_, he⟩
        · exact hq
        · exact applyEvents_queue T hv _ { a with state := { a.state with fresh := a.state.fresh + 1 } } he
            (Inv.congr ha rfl rfl) hq
      split at h
      · cases h
      · obtain ⟨h1, h2⟩ := hq1 _ (.inl rfl); exact applyEvents_queue T hv _ _ h h1 h2
      · obtain ⟨h1, h2⟩ := hq1 _ (.inr ⟨_, rfl⟩); exact applyEvents_queue T hv _ _ h h1 h2
  have hqry : ∀ (x : QueryV v.records v.caller) caller input onAnswer,
      runQuery T a x caller input onAnswer = .ok a' → QueueOk P a' := by
    intro x caller input onAnswer h
    simp only [runQuery] at h
    split at h
    · cases h
    · exact applyEvents_queue T hv _ { a with state := { a.state with fresh := a.state.fresh + 1 } } h ⟨ha.1, ha.2, ha.3, ha.4⟩ hq
  revert h
  cases eff with
  | command name c i j caller value onAnswer =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    generalize ownCommand (v := v) name i j = ox
    cases oc with
    | none => intro h; cases h
    | some hc =>
      cases ox with
      | none => intro h; cases h
      | some x =>
        obtain ⟨hc⟩ := hc
        obtain ⟨x, hi, hj⟩ := x
        exact hcmd _ _ _ _
  | query name c i o caller value onAnswer =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    generalize ownQuery (v := v) name i o = ox
    cases oc with
    | none => intro h; cases h
    | some hc =>
      cases ox with
      | none => intro h; cases h
      | some x =>
        obtain ⟨hc⟩ := hc
        obtain ⟨x, hi, ho⟩ := x
        exact hqry _ _ _ _

theorem fire_inv (hm : ∀ m ∈ v.machines, m.Reach P E) (s : State v) (hs : Inv P s) : (fuel : Nat) → {r : State v × List (Sender × EffectV v.event)} →
    fire s fuel = some r → Inv P r.1 ∧ EffsReach P r.2 ∧ EffsFrom v r.2
  | 0, _, h => by cases h
  | fuel + 1, r, h => by
    rw [fire] at h
    split at h
    · cases h; exact ⟨hs, (by intro x hx; cases hx), (by intro x hx; cases hx)⟩
    · rename_i d _
      obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨h1, h2, h3⟩ := fire_inv hm { s with machines := (fireMachines s.records s.now d false s.machines).1 }
        ⟨hs.below, hs.nodup, hs.reach, hs.shaped⟩ fuel hr
      have hfx := mem_fireMachines_effs s.records s.now d false s.machines
      refine ⟨h1, fun x hx => (List.mem_append.1 hx).elim (fun hx => ?_) (h2 x),
        fun x hx => (List.mem_append.1 hx).elim (fun hx => ?_) (h3 x)⟩
      · obtain ⟨ms, hms, k, st, hx⟩ := hfx x hx
        exact enter_reach ms.1 (hm _ (PerMachine.fst_mem hms)) _ _ _ _ x hx
      · obtain ⟨ms, hms, k, st, hx⟩ := hfx x hx
        exact enter_from (PerMachine.fst_mem hms) (hm _ (PerMachine.fst_mem hms)) _ _ _ _ x hx

end Step

open Step

/-- Every step keeps the invariant. -/
theorem step_inv (T : List TypeDecl) {P : List AnySite} {E : List AnyEffectSite} {v : ServiceV} (hv : v.Reach P E) (s : State v)
    (hs : Inv P s) (i : Input v) : Inv P (step T v s i).state := by
  have hfresh : ∀ k, Inv P ({ s with fresh := k } : State v) := fun _ => Inv.congr hs rfl rfl
  cases i with
  | command i caller input =>
    simp only [step]
    split
    · exact hfresh _
    · exact hfresh _
    · exact hfresh _
    · rename_i a ha
      exact finish_inv T hv _ (hfresh _) _ (fun a' h => by
        cases h; exact execCommand_inv T hv _ hs _ _ _ ha _ (.inl rfl)) _
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
            fun p hp => hs.shaped p (List.mem_filter.1 hp).1⟩
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
          let hf := fire_inv hv.1 { s with now := time } (Inv.congr hs rfl rfl) _ hr
          start_inv { state := s' } effs hf.1 hf.2.1 hf.2.2 h) _

/-- Every state a run reaches from an invariant state keeps the invariant. -/
theorem run_inv (T : List TypeDecl) {P : List AnySite} {E : List AnyEffectSite} {v : ServiceV} (hv : v.Reach P E) :
    (s : State v) → Inv P s → (is : List (Input v)) → Inv P (run T v s is).1
  | _, hs, [] => hs
  | s, hs, i :: is => run_inv T hv _ (step_inv T hv s hs i) is

end Tazuna.Ir
