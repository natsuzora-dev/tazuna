import Tazuna.Smt.StepEnv
import Tazuna.Smt.Own
import Tazuna.Smt.EncodeExact

/-! Writing the requests a step starts into the pending table. The step writes each effect at the next wire id, in
its order (machines in declaration order, instances in key order), and sends it as an out line. The
encoding ranks each machine's start slots (`rankStarts`) after the ids of the machines before it, writes each flagged
slot's entry (`entryT`) and moves the new entries into the pending table's free slots (`moveAll`). Pending ids are
distinct and below the next id in every state a step reaches (`Step.Inv`), so the new ids collide with none. -/

namespace Tazuna.Ir

namespace Step

variable {v : ServiceV}

/-- The out line of a pending request: its wire id, external, command or query name and input. -/
def Pending.line {e : Ty} (p : Pending e) : OutLine := ⟨p.id, p.external, p.request.name, ⟨p.request.input, p.request.value⟩⟩

/-- An effect with its wire id is the request `p` the step writes for it: a request, to the external that lists it. -/
def Writes (ds : List (String × DeclaredV)) {e : Ty} (x : (Sender × EffectV e) × Nat) (p : Pending e) : Prop :=
  ∃ r o, x.1.2 = .request r ∧ r.ownerIn ds = some o ∧ p = ⟨x.2, x.1.1, o, r⟩

/-- The step in progress `a` with the requests `ps` written and sent and the next id `n`. -/
def Acc.wrote (a : Acc v) (ps : List (Pending v.event)) (n : Nat) : Acc v :=
  { a with state := { a.state with pending := a.state.pending ++ ps, nextId := n }, out := a.out ++ ps.map Pending.line }

/-- The step in progress `a` with the own commands and queries `os` queued after the waiting ones. -/
def Acc.queued (a : Acc v) (os : List (EffectV v.event)) : Acc v := { a with own := a.own ++ os }

/-- The requests among effects, in order. -/
abbrev reqsOf {e : Ty} (effs : List (Sender × EffectV e)) : List (Sender × EffectV e) := effs.filter (·.2.isRequest)

/-- The own commands and queries among effects, in order: what they queue. -/
abbrev queuedOf {e : Ty} (effs : List (Sender × EffectV e)) : List (EffectV e) :=
  (effs.filter (!·.2.isRequest)).map (·.2)

/-- Starting effects writes the requests, which externals list, into the pending table at the next ids and sends
them, and queues the own commands and queries, each in order. -/
theorem start_requests (a : Acc v) : (effs : List (Sender × EffectV v.event)) → (ps : List (Pending v.event)) →
    Tazuna.Ir.Forall2 (Writes v.declared) ((reqsOf effs).zipIdx a.state.nextId) ps →
    start a effs = .ok ((a.wrote ps (a.state.nextId + (reqsOf effs).length)).queued (queuedOf effs))
  | [], [], _ => by
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp [start, pure, Except.pure, Acc.wrote, Acc.queued]
  | (snd, .request r) :: effs, p :: ps, ⟨⟨r', o, he, ho, hp⟩, hs⟩ => by
    simp only at he hp
    cases he
    subst hp
    have h1 : start a ((snd, .request r) :: effs) =
        start (a.wrote [⟨a.state.nextId, snd, o, r⟩] (a.state.nextId + 1)) effs := by
      simp only [start, List.foldlM_cons, ho, bind, Except.bind]; rfl
    rw [h1, start_requests _ effs ps hs]
    have hl : (reqsOf ((snd, EffectV.request r) :: effs)).length = (reqsOf effs).length + 1 := by
      simp [reqsOf, EffectV.isRequest]
    have hq : queuedOf ((snd, EffectV.request r) :: effs) = queuedOf effs := by simp [queuedOf, EffectV.isRequest]
    rw [hl, hq]
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp only [Acc.wrote, Acc.queued, List.append_assoc, List.cons_append, List.nil_append, List.map_cons,
      Pending.line, Except.ok.injEq]
    congr 2
    omega
  | (snd, .command n c i j caller value f) :: effs, ps, hs => by
    have h1 : start a ((snd, .command n c i j caller value f) :: effs) =
        start (a.queued [.command n c i j caller value f]) effs := rfl
    have hr : reqsOf ((snd, EffectV.command n c i j caller value f) :: effs) = reqsOf effs := rfl
    have hq : queuedOf ((snd, EffectV.command n c i j caller value f) :: effs) =
        .command n c i j caller value f :: queuedOf effs := rfl
    rw [hr] at hs
    rw [h1, start_requests (a.queued _) effs ps hs, hr, hq]
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp [Acc.wrote, Acc.queued]
  | (snd, .query n c i j caller value f) :: effs, ps, hs => by
    have h1 : start a ((snd, .query n c i j caller value f) :: effs) =
        start (a.queued [.query n c i j caller value f]) effs := rfl
    have hr : reqsOf ((snd, EffectV.query n c i j caller value f) :: effs) = reqsOf effs := rfl
    have hq : queuedOf ((snd, EffectV.query n c i j caller value f) :: effs) =
        .query n c i j caller value f :: queuedOf effs := rfl
    rw [hr] at hs
    rw [h1, start_requests (a.queued _) effs ps hs, hr, hq]
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp [Acc.wrote, Acc.queued]
  | [], _ :: _, h => h.elim
  | (_, .request _) :: _, [], h => h.elim

end Step

end Tazuna.Ir

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {T : List TypeDecl} {v : ServiceV}

/-- The effects the machines start on an event. -/
abbrev startedBy (T : List TypeDecl) (s : State v) (records : v.records.den0) (ev : v.event.den0) :
    List (Sender × EffectV v.event) :=
  s.machines.toSigma.flatMap fun sm => (Step.machineStep T records s.now ev sm.1 sm.2).2

end

/-- A slot of the pending table: whether it holds a request, the request's wire id and its entry. -/
structure PendingSlot where
  flag : Term
  id : Term
  entry : Term

/-- A pending slot as a slot of width two. -/
def PendingSlot.slot (s : PendingSlot) : Slot 2 := (s.flag, ⟨[s.id, s.entry], rfl⟩)

/-- The pending slots with each flag and-ed with `f`. -/
def gatePending (f : Term) (S : List PendingSlot) : List PendingSlot :=
  S.map fun s => { s with flag := Term.share (.and f s.flag) }

/-- The `i`-th slot of the pending table `s`, as `slotsOf` reads it. -/
def pendingSlotAt (d dt i : Nat) (s : Term) : PendingSlot :=
  let x := Term.sel d 0 i s.share
  ⟨.sel dt 0 0 x, .sel dt 0 1 x, .sel dt 0 2 x⟩

/-- The `n` slots of the pending table `s`. -/
def pendingSlotsOf (d dt n : Nat) (s : Term) : List PendingSlot :=
  (List.range n).map fun i => pendingSlotAt d dt i s

theorem pendingSlotsOf_slot (d dt n : Nat) (s : Term) :
    (pendingSlotsOf d dt n s).map PendingSlot.slot = slotsOf d dt n 2 s := by
  simp only [pendingSlotsOf, pendingSlotAt, slotsOf, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, PendingSlot.slot, Prod.mk.injEq, true_and]
  exact Subtype.ext (by simp [List.range_succ])

theorem pendingSlot_at {d dt n i : Nat} (hi : i < n) (s : Term) :
    (slotsOf d dt n 2 s)[i]? = some (pendingSlotAt d dt i s).slot := by
  rw [← pendingSlotsOf_slot, List.getElem?_map]; simp [pendingSlotsOf, hi]

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- The pending table slot of an effect slot: its wire id and its entry. Both are shared, as are the key and the
effect the entry reads several times, because moving the slot into the table copies its items into every slot. -/
def entrySlot (dE dP dk : Nat) (dflt : Term) (js : List (Option Nat)) (s : RankedStart) : PendingSlot :=
  ⟨s.flag, Term.share s.id, Term.share (entryT dE dP dk dflt [Term.share s.key] (Term.share s.effect) 0 js)⟩

/-- A machine's effect slots as pending table slots: each flagged slot holds its wire id and its entry. -/
def entrySlots (dE dP dk : Nat) (dflt : Term) (js : List (Option Nat)) (S : List RankedStart) : List PendingSlot :=
  S.map (entrySlot dE dP dk dflt js)

/-- The own slots of a machine's own start slots, ranked from the queue place `q`, and the place after them; none when
the layout has no own kinds. -/
def ownStarts (m : MachineV r e) (dopt : Nat) (none : Bool) (os : List (StartSlot)) (q : Term) :
    Except Refusal (List OwnSlot × Term) :=
  if none then pure ([], q) else do pure (ownItems (← rankStarts L T m dopt q os), Term.add q (startCount dopt os))

/-- The pending slots of the requests the machines' start slots start, each machine's wire ids after the ones of the
machines before it, the next wire id after them all, the own slots of the own commands and queries they start, each
at its place in the queue from `q`, and the place after them. With no own kinds every effect is a request, and the
start slots are used as they are. -/
def encodeStarts (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (senv : StepEnv L shs) :
    (ms : List (MachineV r e)) → PerMachine (fun _ => List StartSlot) ms → (n q : Term) →
    Except Refusal (List PendingSlot × Term × List OwnSlot × Term)
  | [], .nil, n, q => pure ([], n, [], q)
  | m :: ms, .cons st sts, n, q => do
    let (dk, _) ← L.findE (.tuple [m.key])
    let js ← shapeIdxs shs ds ⟨[m.key], .machine m.name m.key⟩ (L.effectsOf e)
    let dflt ← defaultE L (pendingEntry shs)
    let sp := st.map (splitStart senv.dE (L.effectsOf e).length (L.ownsOf e).length senv.dopt)
    let rq := if (L.ownsOf e).isEmpty then st else sp.map (·.1)
    let S ← rankStarts L T m senv.dopt n rq
    let (oS, q') ← ownStarts L T m senv.dopt (L.ownsOf e).isEmpty (sp.map (·.2)) q
    let (rest, n', orest, q'') ← encodeStarts shs ds senv ms sts (.add n (startCount senv.dopt rq)) q'
    pure (entrySlots senv.dE senv.dP dk dflt js S ++ rest, n', oS ++ orest, q'')

/-- The pending table with the new entries moved into its free slots, and the condition that they fit. -/
def encodePending (shs : List (PendingShape e)) (pending : Term) (news : List PendingSlot) :
    Except Refusal (Term × Term) := do
  let (d, n, dt) ← collD L (pendingTable shs) [.dsl .fresh [], pendingEntry shs]
  let (S, c) := moveAll d dt (slotsOf d dt n 2 pending) (news.map PendingSlot.slot)
  pure (slotsTerm d dt S, c)

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- An entry of the pending table with its wire id is the request the step writes for an effect. -/
def WritesEntry (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (x : (Sender × EffectV e) × Nat)
    (y : (Ty.dsl .fresh []).den × (pendingEntry shs).den) : Prop :=
  y.1 = x.2 ∧ Step.Writes ds x (pendingOf shs y.1 y.2)

/-- A machine's pending slots hold, where flagged, the entries of the requests its effect slots hold. -/
theorem entrySlots_rel {P : List AnySite} (hP : SitesUnique P) (m : MachineV r e)
    {shs : List (PendingShape e)} (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)}
    {js : List (Option Nat)} (hjs : shapeIdxs shs ds ⟨[m.key], .machine m.name m.key⟩ (L.effectsOf e) = .ok js)
    {dE nE dP nP dk nk : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP)) (hdk : L.find? (.tuple [m.key]) = some (dk, nk))
    {S : List RankedStart} {sv : List (Bool × List Val)} {ys : List ((Sender × EffectV e) × Nat)} (dflt : Term)
    (hS : SlotsDen M (S.map RankedStart.slot) sv) (hy : Holds2 (EEff (L := L) m) ys sv) (hr : ∀ x ∈ ys, x.1.2.Reach P)
    (hat : ∀ x ∈ ys, ShapedFrom shs ds x.1.1 x.1.2) (hreq : ∀ x ∈ ys, x.1.2.isRequest = true) :
    ∃ sv' zs, SlotsDen M ((entrySlots dE dP dk dflt js S).map PendingSlot.slot) sv' ∧ sv'.length = sv.length ∧ (∀ p ∈ sv', p.2.length = 2) ∧
      Holds2 (ETab L (.dsl .fresh []) (pendingEntry shs)) zs sv' ∧ Forall2 (WritesEntry shs ds) ys zs := by
  have hys : Holds2 (fun x vs => EEff (L := L) m x vs ∧ x.1.2.Reach P ∧ ShapedFrom shs ds x.1.1 x.1.2 ∧
      x.1.2.isRequest = true) ys sv := by
    unfold Holds2 at hy ⊢
    generalize occupied sv = os at hy ⊢
    induction ys generalizing os with
    | nil => cases os <;> simp_all [Forall2]
    | cons x ys ih =>
      match os, hy with
      | o :: os, ⟨h1, h2⟩ => exact ⟨⟨h1, hr x (by simp), hat x (by simp), hreq x (by simp)⟩,
        ih (fun x' h => hr x' (by simp [h])) (fun x' h => hat x' (by simp [h])) (fun x' h => hreq x' (by simp [h])) os
          h2⟩
  refine mapView_den RankedStart.slot PendingSlot.slot (entrySlot dE dP dk dflt js) (fun _ => rfl) ?_ hS hys
  rintro ⟨⟨snd, eff⟩, id⟩ ⟨f, a, b, c⟩ ⟨⟨k, zk, zx, hvs, hsnd, hzk, hzx⟩, hre, hsh, hrq⟩
  simp only [RankedStart.slot, Term.denotes, List.cons.injEq, and_true] at hvs
  obtain ⟨ha, hb, hc⟩ := hvs
  simp only at hsnd hre hsh hzx
  subst hsnd
  obtain ⟨req, o, rfl, ho, y, hyrel, hpend⟩ := entry_rel (M := M) hP (.machine m.name m.key) hshs hjs hE hPE (k, ())
    (keyT := [Term.share b]) (by
      rw [show Term.denotes M [Term.share b] = [zk] by simp [Term.denotes, Term.denote_share, hb]]
      exact machineKey_rel m k hzk hdk) hre hsh hrq (effT := Term.share c)
    (by rw [Term.denote_share, hc]; exact hzx) id dflt
  refine ⟨((id : Nat), y), ⟨_, _, rfl, (by simp only [entrySlot, Term.denote_share]; exact ha), ?_⟩, rfl, req, o, rfl,
    ho, hpend⟩
  simp only [entrySlot, Term.denote_share]
  exact hyrel

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem holds2_append {α : Type} {E : α → List Val → Prop} {ys zs : List α} {sv tv : List (Bool × List Val)}
    (h1 : Holds2 E ys sv) (h2 : Holds2 E zs tv) : Holds2 E (ys ++ zs) (sv ++ tv) := by
  unfold Holds2 at *
  rw [occupied_append]
  exact forall2_append h1 h2

/-- The pending slots hold, where flagged, the entries of the requests written for `effs` at ids from `n0`. -/
def NewsRel (M : Model) (L : Layout) (shs : List (PendingShape e)) (ds : List (String × DeclaredV))
    (news : List PendingSlot) (effs : List (Sender × EffectV e)) (n0 : Nat) : Prop :=
  ∃ sv zs, SlotsDen M (news.map PendingSlot.slot) sv ∧ (∀ p ∈ sv, p.2.length = 2) ∧ Holds2 (ETab L (.dsl .fresh []) (pendingEntry shs)) zs sv ∧
    ∃ xs, xs.Perm (effs.zipIdx n0) ∧ Forall2 (WritesEntry shs ds) xs zs

theorem newsRel_append {shs : List (PendingShape e)} {ds : List (String × DeclaredV)} {S S' : List PendingSlot}
    {effs effs' : List (Sender × EffectV e)} {n0 : Nat} (h : NewsRel M L shs ds S effs n0)
    (h' : NewsRel M L shs ds S' effs' (n0 + effs.length)) : NewsRel M L shs ds (S ++ S') (effs ++ effs') n0 := by
  obtain ⟨sv, zs, hS, hw, hh, xs, hp, hq⟩ := h
  obtain ⟨sv', zs', hS', hw', hh', xs', hp', hq'⟩ := h'
  refine ⟨sv ++ sv', zs ++ zs', by rw [List.map_append]; exact slotsDen_append hS hS', ?_, holds2_append hh hh',
    xs ++ xs', ?_, forall2_append hq hq'⟩
  · intro p hp; rcases List.mem_append.1 hp with hp | hp
    · exact hw p hp
    · exact hw' p hp
  · rw [List.zipIdx_append]; exact hp.append hp'

/-- A machine's start slots hold its effects `effs`, in some order: items with distinct keys `κ`, each starting the
effect option `F`, whose effects in key order are `effs`. -/
def StartSlots (M : Model) (L : Layout) (T : List TypeDecl) (m : MachineV r e) (starts : List (StartSlot))
    (effs : List (Sender × EffectV e)) : Prop :=
  ∃ (α : Type) (κ : α → m.key.den0) (F : α → (Ty.option (.dsl .effect [e])).den) (E items : List α)
    (svX : List (Bool × List Val)), SlotsDen M (starts.map StartSlot.slot) svX ∧
    Holds2 (EOpt (L := L) m κ F) E svX ∧ E.Perm items ∧ items.Pairwise (fun a b => Ty.cmp T m.key (κ a) (κ b) = .lt) ∧
    effs = items.flatMap fun a => (sentBy m κ F a).toList

/-- Each machine's start slots hold its effects. -/
def StartsRel (M : Model) (L : Layout) (T : List TypeDecl) :
    (ms : List (MachineV r e)) → PerMachine (fun _ => List StartSlot) ms →
    PerMachine (fun _ => List (Sender × EffectV e)) ms → Prop
  | [], .nil, .nil => True
  | m :: ms, .cons st sts, .cons effs effss => StartSlots M L T m st effs ∧ StartsRel M L T ms sts effss

/-- The machines' parts of an event step hold the effects each machine's instances start. -/
theorem machines_starts {v : ServiceV} (recs : v.records.den0) (tnow : Int) (ev : v.event.den0) {records now evT : Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L v.event (Ty.up _ v.event_data ev) (evT.denote M)) :
    (ms : List (MachineV v.records v.event)) → (xs : PerMachine (fun _ => Term) ms) →
    (sms : Step.Machines ms) → (outs : PerMachine (fun _ => ReactOut) ms) → {c : Term} →
    MachinesRel M L T ms xs sms → (∀ m ∈ ms, m.key.orderable = true ∧ m.key.ordered T = true) →
    encodeMachines L ms xs records now evT = .ok (outs, c) → Holds M c →
    ∃ effss, StartsRel M L T ms (outs.map (·.starts)) effss ∧
      effss.toList.flatten = (sms.toSigma.map fun sm => (Step.machineStep T recs tnow ev sm.1 sm.2).2).flatten
  | [], .nil, .nil, outs, c, _, _, henc, _ => by
    simp only [encodeMachines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    exact ⟨.nil, trivial, rfl⟩
  | m :: ms, .cons x xs, .cons insts sms, outs, c, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hor, henc, hc => by
    obtain ⟨⟨a, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨as, c2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    obtain ⟨ho, hko⟩ := hor m (by simp)
    subst hsm
    obtain ⟨svX, E, hX, hh, hEp⟩ := machine_starts (T := T) m ho recs tnow ev hrec hnow hevT tbl htbl h1 hc1
    obtain ⟨effss, hst, hfl⟩ :=
      machines_starts recs tnow ev hrec hnow hevT ms xs sms as hrest (fun m' hm => hor m' (by simp [hm])) h2 hc2
    refine ⟨.cons (Step.machineStep T recs tnow ev m (instancesOf T m tbl)).2 effss, ⟨⟨m.key.den0, id, startedOf m (instancesOf T m tbl) recs tnow ev, E, _, svX, hX, hh, hEp,
      sortBy_dedup_lt (T := T) hko (m.instances.fn (recs, ())),
      machineStep_effects (T := T) m (Ty.plain_of_orderable _ ho) (instancesOf T m tbl) recs tnow ev⟩, hst⟩, ?_⟩
    simp [hfl]

/-- The two halves of split start slots hold the requests and the own commands and queries their slots start. -/
theorem startSlots_split {dE nE dopt nopt : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt)) (m : MachineV r e)
    {ws : List (StartSlot)} {effs : List (Sender × EffectV e)} (h : StartSlots M L T m ws effs) :
    StartSlots M L T m (ws.map fun w => (splitStart dE (L.effectsOf e).length (L.ownsOf e).length dopt w).1)
        (Step.reqsOf effs) ∧
      StartSlots M L T m (ws.map fun w => (splitStart dE (L.effectsOf e).length (L.ownsOf e).length dopt w).2)
        (effs.filter (!·.2.isRequest)) := by
  obtain ⟨α, κ, F, E, items, svX, hX, hh, hEp, hks, rfl⟩ := h
  obtain ⟨sv1, h1, hh1⟩ := startSlots_map (M := M) m optReq (fun w => (splitStart dE _ _ dopt w).1.effect)
    (fun v w hv => (splitStart_rel hE hopt w hv).1) ws svX E hX hh
  obtain ⟨sv2, h2, hh2⟩ := startSlots_map (M := M) m optOwn (fun w => (splitStart dE _ _ dopt w).2.effect)
    (fun v w hv => (splitStart_rel hE hopt w hv).2) ws svX E hX hh
  refine ⟨⟨α, κ, _, E, items, sv1, by simp only [List.map_map, Function.comp_def]; exact h1, hh1, hEp, hks, ?_⟩,
    ⟨α, κ, _, E, items, sv2, by simp only [List.map_map, Function.comp_def]; exact h2, hh2, hEp, hks, ?_⟩⟩
  · simp only [Step.reqsOf, List.filter_flatMap, sentBy_optReq]
  · simp only [List.filter_flatMap, sentBy_optOwn]

/-- With no own kinds a machine's start slots start only requests. -/
theorem startSlots_requests (ho : L.ownsOf e = []) (m : MachineV r e) {ws : List (StartSlot)}
    {effs : List (Sender × EffectV e)} (h : StartSlots M L T m ws effs) : ∀ x ∈ effs, x.2.isRequest = true := by
  obtain ⟨α, κ, F, E, items, svX, -, hh, hEp, -, rfl⟩ := h
  intro x hx
  obtain ⟨a, ha, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨vs, -, zk, z, -, -, hz⟩ := forall2_mem_left hh _ (hEp.mem_iff.2 ha)
  unfold sentBy at hx
  generalize hF : F a = o at hz hx
  match o, hz, hx with
  | .inl (x', ()), ⟨d, n, hd, vals, hv, w, ws, hvw, hw, hws⟩, hx =>
    change x ∈ [(Sender.machine m.name ⟨m.key, κ a⟩, x')] at hx
    obtain rfl := List.mem_singleton.1 hx
    exact request_of_rel ho hw
  | .inr (.inl ()), _, hx => change x ∈ [] at hx; cases hx

/-- The own slots of a machine's own start slots ranked from `q0`: each flagged slot holds an own effect the machine
starts, at its place in the queue. -/
theorem own_ranked (m : MachineV r e) {dopt nopt : Nat}
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt)) {ws : List (StartSlot)}
    {effs : List (Sender × EffectV e)} (h : StartSlots M L T m ws effs) {q : Term} {q0 : Nat}
    (hq : q.denote M = .int (q0 : Int)) {S : List RankedStart} (hS : rankStarts L T m dopt q ws = .ok S) :
    (startCount dopt ws).denote M = .int effs.length ∧ OwnRel M L (ownItems S) (effs.map (·.2)) q0 := by
  obtain ⟨α, κ, F, E, items, svX, hX, hh, hEp, hks, rfl⟩ := h
  obtain ⟨hcount, svS, ys, hS', hyp, hy⟩ := rank_starts (T := T) m hopt κ F hX hh hEp hks hq hS
  refine ⟨hcount, ?_⟩
  obtain ⟨sv', zs, h1, -, h3, h4, h5⟩ := mapView_den (M := M) (Q := fun (y : (Sender × EffectV e) × Nat) z =>
    z = (y.1.2, y.2)) (E' := EOwn L e) RankedStart.slot OwnSlot.slot (fun s => ⟨s.flag, s.id, s.effect⟩)
    (fun _ => rfl) (by
      rintro ⟨⟨snd, eff⟩, id⟩ ⟨f, a, b, c⟩ ⟨k, zk, zx, hvs, -, -, hzx⟩
      simp only [RankedStart.slot, Term.denotes, List.cons.injEq, and_true] at hvs
      exact ⟨(eff, id), ⟨zx, by simp [OwnSlot.slot, Term.denotes, hvs.1, hvs.2.2], hzx⟩, rfl⟩) hS' hy
  have key : ∀ (ys : List ((Sender × EffectV e) × Nat)) (zs : List (EffectV e × Nat)),
      Forall2 (fun y z => z = (y.1.2, y.2)) ys zs → zs = ys.map fun y => (y.1.2, y.2) := by
    intro ys zs h
    induction ys generalizing zs with
    | nil => cases zs <;> simp_all [Forall2]
    | cons y ys ih => match zs, h with
      | z :: zs, ⟨hz, h⟩ => simp [hz, ih zs h]
  have hzs := key ys zs h5
  refine ⟨sv', zs, h1, h3, h4, ?_⟩
  rw [hzs, List.zipIdx_map]
  exact hyp.map _

/-- T2 for the slots of what the machines' start slots start: the new pending slots hold, where flagged, the entries
of the requests the step writes for them at their wire ids (each machine's after the machines' before it), the next
id term denotes the next id after them, and the own slots hold the own commands and queries they queue, at their
places from `q0`. -/
theorem starts_rel {P : List AnySite} (hP : SitesUnique P) {shs : List (PendingShape e)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)}
    (senv : StepEnv L shs) :
    (ms : List (MachineV r e)) → (sts : PerMachine (fun _ => List StartSlot) ms) →
    (effss : PerMachine (fun _ => List (Sender × EffectV e)) ms) → StartsRel M L T ms sts effss →
    (∀ x ∈ effss.toList.flatten, x.2.Reach P) → (∀ x ∈ effss.toList.flatten, ShapedFrom shs ds x.1 x.2) →
    {n q : Term} → {n0 q0 : Nat} → n.denote M = .int n0 → q.denote M = .int q0 →
    {news : List PendingSlot} → {n' : Term} → {owns : List OwnSlot} → {q' : Term} →
    encodeStarts L T shs ds senv ms sts n q = .ok (news, n', owns, q') →
    n'.denote M = .int ((n0 + (Step.reqsOf effss.toList.flatten).length : Nat) : Int) ∧
      NewsRel M L shs ds news (Step.reqsOf effss.toList.flatten) n0 ∧
      q'.denote M = .int ((q0 + (Step.queuedOf effss.toList.flatten).length : Nat) : Int) ∧
      OwnRel M L owns (Step.queuedOf effss.toList.flatten) q0
  | [], .nil, .nil, _, _, _, n, q, n0, q0, hn, hq, news, n', owns, q', henc => by
    simp only [encodeStarts, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := henc
    exact ⟨by simpa using hn, ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩,
      by simpa using hq, ownRel_nil q0⟩
  | m :: ms, .cons st sts, .cons effs effss, ⟨hst, hrest⟩, hreach, hshaped, n, q, n0, q0, hn, hq, news, n', owns, q',
    henc => by
    obtain ⟨⟨dk, nk⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨js, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨dflt, -, henc⟩ := bind_ok.1 henc
    obtain ⟨S, h3, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨oS, q1⟩, h5, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, n'', orest, q''⟩, h4, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    -- The requests' start slots, and the own commands and queries' slots with their places.
    have hparts : StartSlots M L T m (if (L.ownsOf e).isEmpty then st else (st.map
          (splitStart senv.dE (L.effectsOf e).length (L.ownsOf e).length senv.dopt)).map (·.1)) (Step.reqsOf effs) ∧
        q1.denote M = .int ((q0 + (Step.queuedOf effs).length : Nat) : Int) ∧
        OwnRel M L oS (Step.queuedOf effs) q0 := by
      by_cases ho : (L.ownsOf e).isEmpty
      · have hall := startSlots_requests (List.isEmpty_iff.1 ho) m hst
        have hr : Step.reqsOf effs = effs := List.filter_eq_self.2 hall
        have hq0 : Step.queuedOf effs = [] := by
          simp only [Step.queuedOf, List.map_eq_nil_iff, List.filter_eq_nil_iff]; intro x hx; simp [hall x hx]
        simp only [ownStarts, ho, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h5 ⊢
        cases h5
        rw [hr, hq0]
        exact ⟨hst, by simpa using hq, ownRel_nil q0⟩
      · simp only [ownStarts, ho, ↓reduceIte, Bool.false_eq_true] at h5 ⊢
        obtain ⟨hreq, hown⟩ := startSlots_split senv.hE senv.hopt m hst
        obtain ⟨SO, hSO, h5⟩ := bind_ok.1 h5
        cases pure_ok.1 h5
        obtain ⟨hcO, hO⟩ := own_ranked m senv.hopt (by simpa only [List.map_map, Function.comp_def] using hown) hq hSO
        refine ⟨by simpa only [List.map_map, Function.comp_def] using hreq, ?_, hO⟩
        simp only [Term.denote, hq, hcO, Val.toInt, Step.queuedOf, List.length_map]; push_cast; rfl
    obtain ⟨hR, hq1, hO1⟩ := hparts
    obtain ⟨α, κ, F, E, items, svX, hX, hh, hEp, hks, heffs⟩ := hR
    obtain ⟨hcount, svS, ys, hS, hyp, hy⟩ := rank_starts (T := T) m senv.hopt κ F hX hh hEp hks hn h3
    rw [← heffs] at hyp hcount
    have hmem : ∀ x ∈ ys, x.1 ∈ Step.reqsOf effs := fun x hx => List.fst_mem_of_mem_zipIdx (hyp.mem_iff.1 hx)
    have hr : ∀ x ∈ ys, x.1.2.Reach P := fun x hx => hreach x.1 (by simp [(List.mem_filter.1 (hmem x hx)).1])
    have hrq : ∀ x ∈ ys, x.1.2.isRequest = true := fun x hx => (List.mem_filter.1 (hmem x hx)).2
    have hat : ∀ x ∈ ys, ShapedFrom shs ds x.1.1 x.1.2 :=
      fun x hx => hshaped x.1 (by simp [(List.mem_filter.1 (hmem x hx)).1])
    obtain ⟨sv1, zs1, hS1, -, hw1, hh1, hq1'⟩ :=
      entrySlots_rel hP m hshs h2 senv.hE senv.hPE (need_ok.1 h1) dflt hS hy hr hat hrq
    have hn' : (Term.add n (startCount senv.dopt (if (L.ownsOf e).isEmpty then st else (st.map
        (splitStart senv.dE (L.effectsOf e).length (L.ownsOf e).length senv.dopt)).map (·.1)))).denote M =
        .int ((n0 + (Step.reqsOf effs).length : Nat) : Int) := by
      simp only [Term.denote, hn, hcount, Val.toInt]; push_cast; rfl
    obtain ⟨hn2, hnews2, hq2, ho2⟩ :=
      starts_rel hP hshs senv ms sts effss hrest (fun x h => hreach x (by simp [h])) (fun x h => hshaped x (by simp [h]))
        hn' hq1 h4
    have hfl : ∀ effs' : List (Sender × EffectV e), Step.reqsOf (effs ++ effs') = Step.reqsOf effs ++ Step.reqsOf effs' ∧
        Step.queuedOf (effs ++ effs') = Step.queuedOf effs ++ Step.queuedOf effs' := fun _ => by
      simp [Step.reqsOf, Step.queuedOf, List.filter_append]
    rw [PerMachine.toList_cons, List.flatten_cons, (hfl _).1, (hfl _).2]
    refine ⟨?_, newsRel_append ⟨sv1, zs1, hS1, hw1, hh1, ys, hyp, hq1'⟩ hnews2, ?_, ownRel_append hO1 ho2⟩
    · rw [hn2, List.length_append]; congr 2; omega
    · rw [hq2, List.length_append]; congr 2; omega

end

section
variable {L : Layout} {M : Model} {e : Ty}

theorem zipIdx_snd {α : Type} : (l : List α) → (n : Nat) → (l.zipIdx n).map (·.2) = List.range' n l.length
  | [], _ => rfl
  | _ :: l, n => by simp [List.zipIdx_cons, zipIdx_snd l (n + 1), List.range'_succ]

/-- T2 for writing the new entries into the pending table: wherever the condition holds, the new table denotes the
state's pending requests with the requests the step writes for the effects (in some order: pending requests are a
multiset), when the state's wire ids are distinct and below the first new id. -/
theorem pending_rel {v : ServiceV} {shs : List (PendingShape v.event)} {ds : List (String × DeclaredV)}
    {pending : Term} {ps0 : List (Step.Pending v.event)} (hpend : PendingRel L shs (pending.denote M) ps0)
    {n0 : Nat} (hbelow : ∀ p ∈ ps0, p.id < n0) (hnd : (ps0.map (·.id)).Nodup)
    {effs : List (Sender × EffectV v.event)} {news : List PendingSlot} {sv : List (Bool × List Val)}
    {zs : List ((Ty.dsl .fresh []).den × (pendingEntry shs).den)} (hS : SlotsDen M (news.map PendingSlot.slot) sv)
    (hw : ∀ p ∈ sv, p.2.length = 2) (hh : Holds2 (ETab L (.dsl .fresh []) (pendingEntry shs)) zs sv)
    {xs : List ((Sender × EffectV v.event) × Nat)} (hxs : xs.Perm (effs.zipIdx n0)) (hq : Forall2 (WritesEntry shs ds) xs zs)
    {pT c : Term} (henc : encodePending L shs pending news = .ok (pT, c)) (hc : Holds M c) :
    ∃ ps, Forall2 (Step.Writes ds) (effs.zipIdx n0) ps ∧
      ∃ ps', ps'.Perm (ps0 ++ ps) ∧ PendingRel L shs (pT.denote M) ps' := by
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨tbl, ⟨d', n', dt', m', sv0, hf, hft, hl, hv, hw0, ys0, hp0, hh0⟩, hlist⟩ := hpend
  obtain ⟨hf1, m1, hft1⟩ := collD_ok h1
  obtain rfl : d = d' := find_det hf1 hf
  obtain rfl : n = n' := by have := hf1.symm.trans hf; cases this; rfl
  obtain rfl : dt = dt' := find_det hft1 hft
  have hT := slotsOf_den d dt 2 pending sv0 hv hw0
  rw [hl] at hT
  obtain ⟨tv', zs', hS', hl', hw', hperm, hh'⟩ := moveAll_rel d dt hS hw hh hT hw0 hh0 hc
  -- The requests in the order of the effects.
  obtain ⟨zs'', hzp, hq'⟩ := forall2_perm hxs (forall2_flip hq)
  have hq'' := forall2_flip hq'
  refine ⟨zs''.map fun y => pendingOf shs y.1 y.2, forall2_map_right (R := fun a y => Step.Writes ds a (pendingOf shs y.1 y.2)) _ (fun _ _ h => h) (forall2_imp (fun _ _ h => h.2) hq''), ?_⟩
  let key : (Ty.dsl .fresh []).den × (pendingEntry shs).den → Nat := fun y => y.1
  have hkeysNew : zs.map key = xs.map (·.2) := (forall2_map_eq (·.2) key (fun _ _ h => h.1.symm) hq).symm
  have hkeysOld : (ys0.map key).Perm (ps0.map (·.id)) := by
    rw [← hlist]
    simp only [pendingList, List.map_map]
    have : ((·.id) ∘ fun y : (Ty.dsl .fresh []).den × (pendingEntry shs).den =>
      pendingOf shs y.1 y.2) = key := funext fun y => pendingOf_id _ _ _
    rw [this]
    exact hp0.map _
  have hnew : (zs.map key).Perm (List.range' n0 effs.length) := by
    rw [hkeysNew, ← zipIdx_snd]
    exact hxs.map _
  have hkeys : (zs'.map key).Nodup := by
    refine (hperm.map _).nodup_iff.2 ?_
    rw [List.map_append, List.nodup_append]
    refine ⟨(hnew.nodup_iff).2 List.nodup_range', (hkeysOld.nodup_iff).2 hnd, ?_⟩
    intro a ha b hb
    have h1 := List.mem_range'_1.1 (hnew.mem_iff.1 ha)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hkeysOld.mem_iff.1 hb)
    have := hbelow p hp
    omega
  let tbl' : (pendingTable shs).den := ⟨zs', by
    refine List.Pairwise.imp ?_ (List.pairwise_map.1 hkeys)
    intro a b hab
    have h1 : ¬ (a.1 : Nat) = b.1 := hab
    refine ⟨?_, ?_⟩
    · change (@BEq.beq Nat _ a.1 b.1) = false
      exact beq_false_of_ne h1
    · change (@BEq.beq Nat _ b.1 a.1) = false
      exact beq_false_of_ne (Ne.symm h1)⟩
  refine ⟨pendingList _ tbl', ?_, tbl', ?_, rfl⟩
  · simp only [pendingList]
    refine (hperm.map _).trans ?_
    rw [List.map_append, ← hlist]
    refine (List.perm_append_comm).trans (List.Perm.append (hp0.map _) ?_)
    exact (hzp.map _).symm
  · exact (table_mk (x := tbl') h1 hS' (by rw [hl', ← hl]) hw' (List.Perm.refl _) hh' :)

end

section
variable {L : Layout} {M : Model}

/-- The condition of writing the new entries is exact: it holds exactly when the pending requests and the new ones
together fit the pending table's slots, so a false condition means the step really outgrows the bound. -/
theorem pending_exact {v : ServiceV} {shs : List (PendingShape v.event)}
    {pending : Term} {ps0 : List (Step.Pending v.event)} (hpend : PendingRel L shs (pending.denote M) ps0)
    {effs : List (Sender × EffectV v.event)} {news : List PendingSlot} {sv : List (Bool × List Val)}
    {zs : List ((Ty.dsl .fresh []).den × (pendingEntry shs).den)} (hS : SlotsDen M (news.map PendingSlot.slot) sv)
    (hw : ∀ p ∈ sv, p.2.length = 2) (hh : Holds2 (ETab L (.dsl .fresh []) (pendingEntry shs)) zs sv)
    {xs : List ((Sender × EffectV v.event) × Nat)} {n0 : Nat} (hxs : xs.Perm (effs.zipIdx n0))
    {ds : List (String × DeclaredV)} (hq : Forall2 (WritesEntry shs ds) xs zs)
    {pT c : Term} (henc : encodePending L shs pending news = .ok (pT, c)) :
    Holds M c ↔ ps0.length + effs.length ≤ L.count (pendingTable shs) := by
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨tbl, ⟨d', n', dt', m', sv0, hf, hft, hl, hv, hw0, ys0, hp0, hh0⟩, hlist⟩ := hpend
  obtain ⟨hf1, m1, hft1⟩ := collD_ok h1
  obtain rfl : d = d' := find_det hf1 hf
  obtain rfl : n = n' := by have := hf1.symm.trans hf; cases this; rfl
  obtain rfl : dt = dt' := find_det hft1 hft
  have hT := slotsOf_den d dt 2 pending sv0 hv hw0
  rw [hl] at hT
  rw [moveAll_exact d dt hS hw hT hw0, ← holds2_length hh, ← holds2_length hh0, ← forall2_length hq, hxs.length_eq,
    List.length_zipIdx, hp0.length_eq, hl, ← hlist, pendingList, List.length_map]
  have hc : L.count (pendingTable shs) = n := by simp [Layout.count, hf1]
  rw [hc]
  omega

end

section
variable (L : Layout) {e : Ty}

/-- Every occupied slot's key is below `n`. -/
def belowT (S : List PendingSlot) (n : Term) : Term := allT (S.map fun s => .or (.not s.flag) (.lt s.id n))

/-- The state invariant a script asserts beside well-formedness: every pending wire id is below the next one
(`Step.Inv`, which every step keeps). -/
def pendingBelowT (shs : List (PendingShape e)) (pending nextId : Term) : Except Refusal Term := do
  let (d, n, dt) ← collD L (pendingTable shs) [.dsl .fresh [], pendingEntry shs]
  pure (belowT (pendingSlotsOf d dt n pending) nextId)

end

section
variable {L : Layout} {M : Model}

theorem belowT_iff {w : Ty} {n : Term} {n0 : Nat} (hn : n.denote M = .int (n0 : Int)) :
    {S : List PendingSlot} → {sv : List (Bool × List Val)} → {ys : List ((Ty.dsl .fresh []).den × w.den)} →
    SlotsDen M (S.map PendingSlot.slot) sv → Holds2 (ETab L (.dsl .fresh []) w) ys sv →
    (Holds M (belowT S n) ↔ ∀ y ∈ ys, (show Nat from y.1) < n0)
  | [], [], ys, _, hy => by
    cases ys with
    | nil => simp [belowT, allT, Holds, Term.denote, tt, Val.toBool]
    | cons _ _ => exact hy.elim
  | ⟨f, a, b'⟩ :: S, (b, vs) :: sv, ys, ⟨hf, hx, hS⟩, hy => by
    have hcons : Holds M (belowT (⟨f, a, b'⟩ :: S) n) ↔
        Holds M (.or (.not f) (.lt a n)) ∧ Holds M (belowT S n) := by
      simp only [belowT, List.map_cons]
      exact holds_and _ _
    rw [hcons]
    cases b with
    | false =>
      rw [belowT_iff hn hS (by simpa [Holds2, occupied] using hy)]
      simp [Holds, Term.denote, hf, Val.toBool]
    | true =>
      match ys, hy with
      | y :: ys, ⟨⟨zk, zv, hvs, hk, _⟩, hy⟩ =>
        rw [belowT_iff hn hS hy]
        have ha : a.denote M = zk := by
          have := hx.trans hvs; simp only [Term.denotes, List.cons.injEq] at this; exact this.1
        change zk = .int (Int.ofNat y.1) at hk
        simp only [Holds, Term.denote, hf, ha, hk, hn, Val.toBool, Val.toInt, List.mem_cons,
          forall_eq_or_imp]
        simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
        exact and_congr_left' Int.ofNat_lt

/-- The asserted invariant is exact: it holds exactly when every pending wire id is below the next one. -/
theorem pendingBelow_iff {v : ServiceV} {shs : List (PendingShape v.event)}
    {pending nextId : Term} {ps0 : List (Step.Pending v.event)} (hpend : PendingRel L shs (pending.denote M) ps0)
    {n0 : Nat} (hn : nextId.denote M = .int (n0 : Int)) {t : Term} (henc : pendingBelowT L shs pending nextId = .ok t) :
    Holds M t ↔ ∀ p ∈ ps0, p.id < n0 := by
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨tbl, ⟨d', n', dt', m', sv0, hf, hft, hl, hv, hw0, ys0, hp0, hh0⟩, hlist⟩ := hpend
  obtain ⟨hf1, m1, hft1⟩ := collD_ok h1
  obtain rfl : d = d' := find_det hf1 hf
  obtain rfl : n = n' := by have := hf1.symm.trans hf; cases this; rfl
  obtain rfl : dt = dt' := find_det hft1 hft
  have hT := slotsOf_den d dt 2 pending sv0 hv hw0
  rw [hl, ← pendingSlotsOf_slot] at hT
  rw [belowT_iff hn hT hh0, ← hlist]
  simp only [pendingList, List.mem_map]
  constructor
  · rintro h _ ⟨y, hy, rfl⟩
    exact lt_of_eq_of_lt (pendingOf_id _ _ _) (h y (hp0.mem_iff.2 hy))
  · intro h y hy
    exact lt_of_eq_of_lt (pendingOf_id shs y.1 y.2).symm (h _ ⟨y, hp0.mem_iff.1 hy, rfl⟩)

end

end Tazuna.Smt
