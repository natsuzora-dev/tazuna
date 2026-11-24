import Tazuna.Smt.PendingWrite
import Tazuna.Smt.Exact

/-! T2 for an event whose machines start requests. The step writes each effect into the pending table at the next
wire id, in its order (machines in declaration order, instances in key order), and sends it as an out line. The
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

/-- Starting requests that externals list writes them into the pending table at the next ids and sends them. -/
theorem start_requests (a : Acc v) : (effs : List (Sender × EffectV v.event)) → (ps : List (Pending v.event)) →
    Tazuna.Smt.Forall2 (Writes v.declared) (effs.zipIdx a.state.nextId) ps →
    start a effs = .ok (a.wrote ps (a.state.nextId + effs.length))
  | [], [], _ => by
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp [start, pure, Except.pure, Acc.wrote]
  | (snd, eff) :: effs, p :: ps, ⟨⟨r, o, he, ho, hp⟩, hs⟩ => by
    simp only at he hp
    subst he hp
    have h1 : start a ((snd, .request r) :: effs) =
        start (a.wrote [⟨a.state.nextId, snd, o, r⟩] (a.state.nextId + 1)) effs := by
      simp only [start, List.foldlM_cons, ho, bind, Except.bind]; rfl
    rw [h1, start_requests _ effs ps hs]
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp only [Acc.wrote, List.append_assoc, List.cons_append, List.nil_append, List.map_cons, List.length_cons,
      Pending.line, Except.ok.injEq]
    congr 2
    omega
  | [], _ :: _, h | _ :: _, [], h => h.elim

end Step

end Tazuna.Ir

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {T : List TypeDecl} {v : ServiceV}

/-- The effects the machines start on an event. -/
abbrev startedBy (T : List TypeDecl) (s : State v) (records : v.records.den0) (ev : v.event.den0) :
    List (Sender × EffectV v.event) :=
  s.machines.flatMap fun ms0 => (Step.machineStep T records s.now ev ms0).2

/-- An event's step on a service without reactions whose machines start requests that externals list, computed: the
requests are written at the next ids and sent. -/
theorem step_event_requests (hx : v.reactions = []) (s : State v) (i : Fin v.subscribes.length)
    (value : (v.subscribes.get i).event.den0) (ps : List (Step.Pending v.event))
    (hps : Forall2 (Step.Writes v.declared) ((startedBy T s (v.apply.fn (s.records, (v.subscribes.get i).wrap.fn
      (value, ()), ())) ((v.subscribes.get i).wrap.fn (value, ()))).zipIdx s.nextId) ps) :
    let ev := (v.subscribes.get i).wrap.fn (value, ())
    let records := v.apply.fn (s.records, ev, ())
    let ms := s.machines.map fun ms0 => (Step.machineStep T records s.now ev ms0).1
    let n := s.nextId + (startedBy T s records ev).length
    let s' : State v := { s with records, machines := ms, pending := s.pending ++ ps, nextId := n }
    step T v s (.event i value) = match Step.invariants s' with
      | n :: _ => ⟨s, .fault (.invariant n), [], []⟩
      | [] => ⟨s', .accepted, [ev], ps.map Step.Pending.line⟩ := by
  intro ev records ms n s'
  simp only [step, Step.finish, Step.applyEvents, List.foldlM, react_plain hx]
  rw [Step.start_requests _ _ ps hps]
  simp only [bind, Except.bind, pure, Except.pure, Step.settle, Step.Acc.wrote]
  rfl

end


section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- The pending table slot of an effect slot: its wire id and its entry. Both are shared, as are the key and the
effect the entry reads several times, because moving the slot into the table copies its items into every slot. -/
def entryItems (dE dP dk : Nat) (js : List Nat) (xs : List Term) : List Term :=
  [Term.share (xs.headD tt), Term.share (entryT dE dP dk (Term.share (xs.getD 1 tt)) (Term.share (xs.getD 2 tt)) 0 js)]

/-- A machine's effect slots as pending table slots: each flagged slot holds its wire id and its entry. -/
def entrySlots (dE dP dk : Nat) (js : List Nat) (S : List Slot) : List Slot :=
  S.map fun (f, xs) => (f, entryItems dE dP dk js xs)

/-- The pending slots of the effects the machines start, each machine's wire ids after the ones of the machines
before it, and the next wire id after them all. -/
def encodeStarts (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (dE dP dopt : Nat) :
    List (MachineV r e) → List MachineOut → Term → Except Refusal (List Slot × Term)
  | [], [], n => pure ([], n)
  | m :: ms, o :: os, n => do
    let (dk, _) ← need "a layout without the sender's key tuple" (L.find? (.tuple [m.key]))
    let js ← shapeIdxs shs ds m.name m.key (L.effectsOf e)
    let S ← rankStarts L T m dopt n o.starts
    let (rest, n') ← encodeStarts shs ds dE dP dopt ms os (.add n (startCount dopt o.starts))
    pure (entrySlots dE dP dk js S ++ rest, n')
  | _, _, _ => .error (.outside "machines and start slots that differ in number")

/-- The pending table with the new entries moved into its free slots, and the condition that they fit. -/
def encodePending (shs : List (PendingShape e)) (pending : Term) (news : List Slot) : Except Refusal (Term × Term) := do
  let (d, n, dt) ← collD L (pendingTable shs) [.dsl .fresh [], pendingEntry shs]
  let (S, c) := moveAll d dt 2 (slotsOf d dt n 2 pending) news
  pure (slotsTerm d dt S, c)

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- Slots whose items a function of the item terms rewrites. -/
theorem mapItems_den {α β : Type} {E : α → List Val → Prop} {E' : β → List Val → Prop} {Q : α → β → Prop}
    (N : List Term → List Term) (w : Nat) (hw : ∀ xs, (N xs).length = w)
    (hN : ∀ y xs, E y (Term.denotes M xs) → ∃ z, E' z (Term.denotes M (N xs)) ∧ Q y z) :
    {S : List Slot} → {sv : List (Bool × List Val)} → {ys : List α} → SlotsDen M S sv → Holds2 E ys sv →
    ∃ sv' zs, SlotsDen M (S.map fun (f, xs) => (f, N xs)) sv' ∧ sv'.length = sv.length ∧
      (∀ p ∈ sv', p.2.length = w) ∧ Holds2 E' zs sv' ∧ Forall2 Q ys zs
  | [], [], ys, _, hy => by
    cases ys with
    | nil => exact ⟨[], [], trivial, rfl, by simp, by simp [Holds2, occupied, Forall2], trivial⟩
    | cons _ _ => exact hy.elim
  | (f, xs) :: S, (b, vs) :: sv, ys, ⟨hf, hx, hS⟩, hy => by
    have hl : ∀ q, q = (b, Term.denotes M (N xs)) → q.2.length = w := by
      intro q hq; subst hq; rw [denotes_eq_map, List.length_map, hw]
    cases b with
    | false =>
      obtain ⟨sv', zs, h1, h2, h3, h4, h5⟩ := mapItems_den N w hw hN hS (by simpa [Holds2, occupied] using hy)
      refine ⟨(false, Term.denotes M (N xs)) :: sv', zs, ⟨hf, rfl, h1⟩, by simp [h2], ?_, by
        simpa [Holds2, occupied] using h4, h5⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hl _ rfl, h3⟩
    | true =>
      match ys, hy with
      | y :: ys, ⟨hey, hy⟩ =>
        obtain ⟨z, hz, hq⟩ := hN y xs (hx ▸ hey)
        obtain ⟨sv', zs, h1, h2, h3, h4, h5⟩ := mapItems_den N w hw hN hS hy
        refine ⟨(true, Term.denotes M (N xs)) :: sv', z :: zs, ⟨hf, rfl, h1⟩, by simp [h2], ?_, ⟨hz, h4⟩, ⟨hq, h5⟩⟩
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨hl _ rfl, h3⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

theorem triple_terms {xs : List Term} {a b c : Val} (h : Term.denotes M xs = [a, b, c]) :
    ∃ x y z, xs = [x, y, z] ∧ x.denote M = a ∧ y.denote M = b ∧ z.denote M = c := by
  match xs, h with
  | [x, y, z], h => simp only [Term.denotes, List.cons.injEq, and_true] at h; exact ⟨x, y, z, rfl, h.1, h.2.1, h.2.2⟩

/-- An entry of the pending table with its wire id is the request the step writes for an effect. -/
def WritesEntry (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (x : (Sender × EffectV e) × Nat)
    (y : (Ty.dsl .fresh []).den × (pendingEntry shs).den) : Prop :=
  y.1 = x.2 ∧ Step.Writes ds x (pendingOf shs y.1 y.2)

/-- A machine's pending slots hold, where flagged, the entries of the requests its effect slots hold. -/
theorem entrySlots_rel {P : List AnySite} (hP : SitesUnique P) (m : MachineV r e)
    {shs : List (PendingShape e)} (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)} {js : List Nat}
    (hjs : shapeIdxs shs ds m.name m.key (L.effectsOf e) = .ok js)
    {dE nE dP nP dk nk : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP)) (hdk : L.find? (.tuple [m.key]) = some (dk, nk))
    {S : List Slot} {sv : List (Bool × List Val)} {ys : List ((Sender × EffectV e) × Nat)}
    (hS : SlotsDen M S sv) (hy : Holds2 (EEff (L := L) m) ys sv) (hr : ∀ x ∈ ys, x.1.2.Reach P) :
    ∃ sv' zs, SlotsDen M (entrySlots dE dP dk js S) sv' ∧ sv'.length = sv.length ∧ (∀ p ∈ sv', p.2.length = 2) ∧
      Holds2 (ETab L (.dsl .fresh []) (pendingEntry shs)) zs sv' ∧ Forall2 (WritesEntry shs ds) ys zs := by
  have hys : Holds2 (fun x vs => EEff (L := L) m x vs ∧ x.1.2.Reach P) ys sv := by
    unfold Holds2 at hy ⊢
    generalize occupied sv = os at hy ⊢
    induction ys generalizing os with
    | nil => cases os <;> simp_all [Forall2]
    | cons x ys ih =>
      match os, hy with
      | o :: os, ⟨h1, h2⟩ => exact ⟨⟨h1, hr x (by simp)⟩, ih (fun x' h => hr x' (by simp [h])) os h2⟩
  refine mapItems_den (entryItems dE dP dk js) 2 (fun _ => rfl) ?_ hS hys
  rintro ⟨⟨snd, eff⟩, id⟩ xs ⟨⟨k, zk, zx, hvs, hsnd, hzk, hzx⟩, hre⟩
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := triple_terms hvs
  simp only at hsnd hre hzx
  subst hsnd
  obtain ⟨req, o, rfl, ho, y, hyrel, hpend⟩ := entry_rel hP m hshs hjs hE hPE hdk k
    (keyT := Term.share b) (by rw [Term.denote_share, hb]; exact hzk) hre (effT := Term.share c)
    (by rw [Term.denote_share, hc]; exact hzx) id
  refine ⟨((id : Nat), y), ⟨_, _, rfl, by simp only [List.headD_cons, Term.denote_share]; exact ha, ?_⟩, rfl, req, o,
    rfl, ho, hpend⟩
  simp only [List.getD_cons_succ, List.getD_cons_zero, Term.denote_share]
  exact hyrel

end


section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem forall2_append {α β : Type} {R : α → β → Prop} : {a a' : List α} → {b b' : List β} → Forall2 R a b →
    Forall2 R a' b' → Forall2 R (a ++ a') (b ++ b')
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, ⟨h1, h2⟩, h => ⟨h1, forall2_append h2 h⟩

theorem holds2_append {α : Type} {E : α → List Val → Prop} {ys zs : List α} {sv tv : List (Bool × List Val)}
    (h1 : Holds2 E ys sv) (h2 : Holds2 E zs tv) : Holds2 E (ys ++ zs) (sv ++ tv) := by
  unfold Holds2 at *
  rw [occupied_append]
  exact forall2_append h1 h2

/-- Each machine's start slots hold the effects its instances start, and the instance tables denote the machines. -/
def StartsRel (M : Model) (L : Layout) (T : List TypeDecl) (recs : r.den0) (tnow : Int) (ev : e.den0) :
    List (MachineV r e) → List MachineOut → List (Step.MachineState r e) → Prop
  | [], [], [] => True
  | m :: ms, o :: os, sm :: sms =>
    (∃ tbl, sm = ⟨m, instancesOf T m tbl⟩ ∧ ∃ svX E, SlotsDen M (o.starts.map fun w => (w.1, [w.2.1, w.2.2])) svX ∧
      Holds2 (EStart (L := L) m (instancesOf T m tbl) recs tnow ev) E svX ∧
      E.Perm (Ty.sortBy T m.key (dedupBy (Ty.semWith Dsl.base m.key).2 (m.instances.fn (recs, ()))))) ∧
    StartsRel M L T recs tnow ev ms os sms
  | _, _, _ => False

/-- The machines' parts of an event step hold the effects each machine's instances start. -/
theorem machines_starts {v : ServiceV} (recs : v.records.den0) (tnow : Int) (ev : v.event.den0) {records now evT : Term}
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L v.event (Ty.up _ hed ev) (evT.denote M)) :
    (ms : List (MachineV v.records v.event)) → (xs : List Term) → (sms : List (Step.MachineState v.records v.event)) →
    (outs : List MachineOut) → {c : Term} → MachinesRel M L T ms xs sms →
    (∀ m ∈ ms, m.key.orderable = true) → encodeMachines L T ms xs records now evT = .ok (outs, c) → Holds M c →
    StartsRel M L T recs tnow ev ms outs sms
  | [], [], [], outs, c, _, _, henc, _ => by
    simp only [encodeMachines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    trivial
  | m :: ms, x :: xs, sm :: sms, outs, c, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hor, henc, hc => by
    obtain ⟨⟨a, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨as, c2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    exact ⟨⟨tbl, hsm, machine_starts (T := T) m (hor m (by simp)) recs tnow ev hrec hnow hevT tbl htbl h1 hc1⟩,
      machines_starts recs tnow ev hrd hed hrec hnow hevT ms xs sms as hrest (fun m' hm => hor m' (by simp [hm])) h2 hc2⟩
  | [], [], _ :: _, _, _, h, _, _, _ | [], _ :: _, _, _, _, h, _, _, _ | _ :: _, [], _, _, _, h, _, _, _
  | _ :: _, _ :: _, [], _, _, h, _, _, _ => h.elim

/-- T2 for the pending slots of the effects the machines start: wherever the start slots hold the effects, the new
slots hold, where flagged, the entries of the requests the step writes for them at their wire ids (each machine's
after the machines' before it), and the next id term denotes the next id after them. -/
theorem starts_rel {P : List AnySite} (hP : SitesUnique P) {shs : List (PendingShape e)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)}
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [e]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt)) (recs : r.den0) (tnow : Int) (ev : e.den0) :
    (ms : List (MachineV r e)) → (outs : List MachineOut) → (sms : List (Step.MachineState r e)) →
    StartsRel M L T recs tnow ev ms outs sms →
    (∀ m ∈ ms, m.key.orderable = true ∧ m.key.ordered T = true ∧ m.Reach P) →
    {n : Term} → {n0 : Nat} → n.denote M = .int n0 →
    {news : List Slot} → {n' : Term} → encodeStarts L T shs ds dE dP dopt ms outs n = .ok (news, n') →
    n'.denote M = .int ((n0 + (sms.flatMap fun sm => (Step.machineStep T recs tnow ev sm).2).length : Nat) : Int) ∧
    ∃ sv zs, SlotsDen M news sv ∧ (∀ p ∈ sv, p.2.length = 2) ∧
      Holds2 (ETab L (.dsl .fresh []) (pendingEntry shs)) zs sv ∧
      ∃ xs, xs.Perm ((sms.flatMap fun sm => (Step.machineStep T recs tnow ev sm).2).zipIdx n0) ∧
        Forall2 (WritesEntry shs ds) xs zs
  | [], [], [], _, _, n, n0, hn, news, n', henc => by
    simp only [encodeStarts, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl⟩ := henc
    exact ⟨by simpa using hn, [], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩
  | m :: ms, o :: os, sm :: sms, ⟨⟨tbl, hsm, svX, E, hX, hh, hEp⟩, hrest⟩, hms, n, n0, hn, news, n', henc => by
    obtain ⟨hor, hko, hreach⟩ := hms m (by simp)
    obtain ⟨⟨dk, nk⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨js, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨S, h3, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, n''⟩, h4, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    subst hsm
    have hks := sortBy_dedup_lt (T := T) hko (m.instances.fn (recs, ()))
    obtain ⟨hcount, svS, ys, hS, hyp, hy⟩ := rank_starts (T := T) m hopt hX hh hEp hks hn h3
    have heffs := machineStep_effects (T := T) m (Ty.plain_of_orderable _ hor) (instancesOf T m tbl) recs tnow ev
    rw [← heffs] at hyp hcount
    have hr : ∀ x ∈ ys, x.1.2.Reach P := by
      intro x hx
      obtain ⟨-, he⟩ := Step.machineStep_reach T recs tnow ev ⟨m, instancesOf T m tbl⟩ hreach
      exact he x.1 (List.fst_mem_of_mem_zipIdx (hyp.mem_iff.1 hx))
    obtain ⟨sv1, zs1, hS1, -, hw1, hh1, hq1⟩ :=
      entrySlots_rel hP m hshs h2 hE hPE (need_ok.1 h1) hS hy hr
    have hn' : (Term.add n (startCount dopt o.starts)).denote M =
        .int ((n0 + (Step.machineStep T recs tnow ev ⟨m, instancesOf T m tbl⟩).2.length : Nat) : Int) := by
      simp only [Term.denote, hn, hcount, Val.toInt]; push_cast; rfl
    obtain ⟨hn2, sv2, zs2, hS2, hw2, hh2, xs2, hp2, hq2⟩ :=
      starts_rel hP hshs hE hPE hopt recs tnow ev ms os sms hrest (fun m' hm => hms m' (by simp [hm])) hn' h4
    refine ⟨?_, sv1 ++ sv2, zs1 ++ zs2, slotsDen_append hS1 hS2, ?_, holds2_append hh1 hh2, ys ++ xs2, ?_,
      forall2_append hq1 hq2⟩
    · rw [hn2, List.flatMap_cons, List.length_append]; congr 2; omega
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hw1 p hp
      · exact hw2 p hp
    · rw [List.flatMap_cons, List.zipIdx_append]
      exact hyp.append hp2
  | [], [], _ :: _, h, _, _, _, _, _, _, _ | [], _ :: _, _, h, _, _, _, _, _, _, _
  | _ :: _, [], _, h, _, _, _, _, _, _, _ | _ :: _, _ :: _, [], h, _, _, _, _, _, _, _ => h.elim

end


section
variable {L : Layout} {M : Model} {e : Ty}

theorem deq_fresh (a b : (Ty.dsl .fresh []).den) : Ty.deq (.dsl .fresh []) a b = true ↔ a = b := by
  change @BEq.beq Nat _ a b = true ↔ a = b
  exact beq_iff_eq

theorem zipIdx_snd {α : Type} : (l : List α) → (n : Nat) → (l.zipIdx n).map (·.2) = List.range' n l.length
  | [], _ => rfl
  | _ :: l, n => by simp [List.zipIdx_cons, zipIdx_snd l (n + 1), List.range'_succ]

theorem forall2_flip {α β : Type} {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs →
    Forall2 (fun b a => R a b) bs as
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨h, forall2_flip hs⟩

theorem forall2_map_r {α β γ : Type} {R : α → γ → Prop} (f : β → γ) : {as : List α} → {bs : List β} →
    Forall2 (fun a b => R a (f b)) as bs → Forall2 R as (bs.map f)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨h, forall2_map_r f hs⟩

theorem forall2_map_eq {α β γ : Type} {R : α → β → Prop} (f : α → γ) (g : β → γ) (h : ∀ a b, R a b → f a = g b) :
    {as : List α} → {bs : List β} → Forall2 R as bs → as.map f = bs.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨hab, hs⟩ => by simp only [List.map_cons, h _ _ hab, forall2_map_eq f g h hs]

/-- T2 for writing the new entries into the pending table: wherever the condition holds, the new table denotes the
state's pending requests with the requests the step writes for the effects (in some order: pending requests are a
multiset), when the state's wire ids are distinct and below the first new id. -/
theorem pending_rel {v : ServiceV} {shs : List (PendingShape v.event)} {ds : List (String × DeclaredV)} (hne : shs ≠ [])
    {pending : Term} {ps0 : List (Step.Pending v.event)} (hpend : PendingRel L shs (pending.denote M) ps0)
    {n0 : Nat} (hbelow : ∀ p ∈ ps0, p.id < n0) (hnd : (ps0.map (·.id)).Nodup)
    {effs : List (Sender × EffectV v.event)} {news : List Slot} {sv : List (Bool × List Val)}
    {zs : List ((Ty.dsl .fresh []).den × (pendingEntry shs).den)} (hS : SlotsDen M news sv)
    (hw : ∀ p ∈ sv, p.2.length = 2) (hh : Holds2 (ETab L (.dsl .fresh []) (pendingEntry shs)) zs sv)
    {xs : List ((Sender × EffectV v.event) × Nat)} (hxs : xs.Perm (effs.zipIdx n0)) (hq : Forall2 (WritesEntry shs ds) xs zs)
    {pT c : Term} (henc : encodePending L shs pending news = .ok (pT, c)) (hc : Holds M c) :
    ∃ ps, Forall2 (Step.Writes ds) (effs.zipIdx n0) ps ∧
      ∃ ps', ps'.Perm (ps0 ++ ps) ∧ PendingRel L shs (pT.denote M) ps' := by
  obtain ⟨sh0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨tbl, ⟨d', n', dt', m', sv0, hf, hft, hl, hv, hw0, ys0, hp0, hh0⟩, hlist⟩ := hpend
  obtain ⟨hf1, m1, hft1⟩ := collD_ok h1
  obtain rfl : d = d' := find_det hf1 hf
  obtain rfl : n = n' := by have := hf1.symm.trans hf; cases this; rfl
  obtain rfl : dt = dt' := find_det hft1 hft
  have hT := slotsOf_den d dt 2 pending sv0 hv hw0
  rw [hl] at hT
  obtain ⟨tv', zs', hS', hl', hw', hperm, hh'⟩ := moveAll_rel d dt 2 hS hw hh hT hw0 hh0 hc
  -- The requests in the order of the effects.
  obtain ⟨zs'', hzp, hq'⟩ := forall2_perm hxs (forall2_flip hq)
  have hq'' := forall2_flip hq'
  refine ⟨zs''.map fun y => pendingOf (sh0 :: rest) y.1 y.2, forall2_map_r _ (forall2_imp (fun _ _ h => h.2) hq''), ?_⟩
  let key : (Ty.dsl .fresh []).den × (pendingEntry (sh0 :: rest)).den → Nat := fun y => y.1
  have hkeysNew : zs.map key = xs.map (·.2) := (forall2_map_eq (·.2) key (fun _ _ h => h.1.symm) hq).symm
  have hkeysOld : (ys0.map key).Perm (ps0.map (·.id)) := by
    rw [← hlist]
    simp only [pendingList, List.map_map]
    have : ((·.id) ∘ fun y : (Ty.dsl .fresh []).den × (pendingEntry (sh0 :: rest)).den =>
      pendingOf (sh0 :: rest) y.1 y.2) = key := funext fun y => pendingOf_id _ _ _
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
  let tbl' : (pendingTable (sh0 :: rest)).den := ⟨zs', by
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
variable {L : Layout} {T : List TypeDecl} {M : Model}

/-- T2 for an event on a service without reactions whose machines start requests: wherever the conditions hold, a
broken invariant's name (the service's first, then each machine's instances in key order) is the step's fault, and
otherwise the step is accepted with the records, the instance tables and the event the terms denote; it writes the
requests `ps` at the next wire ids and sends them as its out lines, the pending table term denotes the pending
requests (as a multiset) and the next id term the next wire id. -/
theorem event_step_effects {P : List AnySite} (hP : SitesUnique P) {v : ServiceV} (hv : v.Reach P)
    (hx : v.reactions = []) {shs : List (PendingShape v.event)} (hne : shs ≠ []) (hshs : ∀ sh ∈ shs, sh.InSites P)
    (s : State v) (hinv : Step.Inv P s) (i : Fin v.subscribes.length)
    (value : (v.subscribes.get i).event.den0) (hd : EventData v i) {ec : EventCode v i} {ce : Term}
    (hec : EventCode.of L v i = .ok (ec, ce)) (hce : Holds M ce) {records sv now nextIdT pending : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) (hnow : now.denote M = .int s.now)
    (hnid : nextIdT.denote M = .int (Int.ofNat s.nextId)) (hpend : PendingRel L shs (pending.denote M) s.pending)
    {xs : List Term} (hms : MachinesRel M L T v.machines xs s.machines)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    {o : EventOut} {cond : Term} (henc : encodeEvent L ec records sv = .ok (o, cond)) (hc : Holds M cond)
    {outs : List MachineOut} {cm : Term} (hm : encodeMachines L T v.machines xs o.records now o.event = .ok (outs, cm))
    (hcm : Holds M cm) {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {news : List Slot} {nT : Term} (hst : encodeStarts L T shs v.declared dE dP dopt v.machines outs nextIdT = .ok (news, nT))
    {pT cp : Term} (hpe : encodePending L shs pending news = .ok (pT, cp)) (hcp : Holds M cp) :
    let r := step T v s (.event i value)
    match brokenIn M o.invariants ++ machinesBroken L T M v.machines outs with
    | n :: _ => r = ⟨s, .fault (.invariant n), [], []⟩
    | [] => r.outcome = .accepted ∧
        (∃ ps, r.out = ps.map Step.Pending.line ∧ r.state.pending = s.pending ++ ps ∧
          r.state.nextId = s.nextId + ps.length ∧ ∃ ps', ps'.Perm r.state.pending ∧ PendingRel L shs (pT.denote M) ps') ∧
        nT.denote M = .int (Int.ofNat r.state.nextId) ∧
        r.state = { s with records := r.state.records, machines := r.state.machines,
                           pending := r.state.pending, nextId := r.state.nextId } ∧
        RelV L v.records (Ty.up _ hd.records r.state.records) (o.records.denote M) ∧
        MachinesRel M L T v.machines (outs.map (·.table)) r.state.machines ∧
        ∃ e, r.events = [e] ∧ RelV L v.event (Ty.up _ hd.event e) (o.event.denote M) := by
  intro r
  obtain ⟨hr', he', hb'⟩ := event_rel i value hd hec hce hrec hsv henc hc
  let ev := (v.subscribes.get i).wrap.fn (value, ())
  let recs' := v.apply.fn (s.records, ev, ())
  obtain ⟨hrel, hbs⟩ := machines_event (T := T) recs' s.now ev hd.records hd.event hr' hnow he' v.machines xs
    s.machines outs hms hor hm hcm
  have hstarts := machines_starts (T := T) recs' s.now ev hd.records hd.event hr' hnow he' v.machines xs s.machines
    outs hms (fun m hm => (hor m hm).1) hm hcm
  obtain ⟨hnT, svN, zs, hSN, hwN, hhN, xs', hxp, hq⟩ := starts_rel hP hshs hE hPE hopt recs' s.now ev v.machines outs
    s.machines hstarts (fun m hm => ⟨(hor m hm).1, (hor m hm).2, hv.1 m hm⟩) hnid hst
  obtain ⟨ps, hps, ps', hperm, hrelP⟩ := pending_rel hne hpend hinv.below hinv.nodup hSN hwN hhN hxp hq hpe hcp
  have hlen : ps.length = (startedBy T s recs' ev).length := by
    rw [← forall2_length hps, List.length_zipIdx]
  simp only [r]
  rw [step_event_requests hx s i value ps hps]
  let ms' := s.machines.map fun ms0 => (Step.machineStep T recs' s.now ev ms0).1
  let s' : State v := { s with records := recs', machines := ms', pending := s.pending ++ ps,
                               nextId := s.nextId + (startedBy T s recs' ev).length }
  have hinvs : Step.invariants s' =
      brokenIn M o.invariants ++ machinesBroken L T M v.machines outs := by
    simp only [Step.invariants]
    rw [hb', hbs]
    rfl
  rw [hinvs]
  cases brokenIn M o.invariants ++ machinesBroken L T M v.machines outs with
  | cons n ns => rfl
  | nil =>
    refine ⟨rfl, ⟨ps, rfl, rfl, by rw [hlen], ps', hperm.trans (List.Perm.refl _), hrelP⟩, ?_, rfl, hr', hrel, _, rfl, he'⟩
    rw [hnT]
    rfl

end


section
variable {L : Layout} {M : Model}

/-- The condition of writing the new entries is exact: it holds exactly when the pending requests and the new ones
together fit the pending table's slots, so a false condition means the step really outgrows the bound. -/
theorem pending_exact {v : ServiceV} {shs : List (PendingShape v.event)} (hne : shs ≠ [])
    {pending : Term} {ps0 : List (Step.Pending v.event)} (hpend : PendingRel L shs (pending.denote M) ps0)
    {effs : List (Sender × EffectV v.event)} {news : List Slot} {sv : List (Bool × List Val)}
    {zs : List ((Ty.dsl .fresh []).den × (pendingEntry shs).den)} (hS : SlotsDen M news sv)
    (hw : ∀ p ∈ sv, p.2.length = 2) (hh : Holds2 (ETab L (.dsl .fresh []) (pendingEntry shs)) zs sv)
    {xs : List ((Sender × EffectV v.event) × Nat)} {n0 : Nat} (hxs : xs.Perm (effs.zipIdx n0))
    {ds : List (String × DeclaredV)} (hq : Forall2 (WritesEntry shs ds) xs zs)
    {pT c : Term} (henc : encodePending L shs pending news = .ok (pT, c)) :
    Holds M c ↔ ps0.length + effs.length ≤ L.count (pendingTable shs) := by
  obtain ⟨sh0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨tbl, ⟨d', n', dt', m', sv0, hf, hft, hl, hv, hw0, ys0, hp0, hh0⟩, hlist⟩ := hpend
  obtain ⟨hf1, m1, hft1⟩ := collD_ok h1
  obtain rfl : d = d' := find_det hf1 hf
  obtain rfl : n = n' := by have := hf1.symm.trans hf; cases this; rfl
  obtain rfl : dt = dt' := find_det hft1 hft
  have hT := slotsOf_den d dt 2 pending sv0 hv hw0
  rw [hl] at hT
  rw [moveAll_exact d dt 2 hS hw hT hw0, ← holds2_length hh, ← holds2_length hh0, ← forall2_length hq, hxs.length_eq,
    List.length_zipIdx, hp0.length_eq, hl, ← hlist, pendingList, List.length_map]
  have hc : L.count (pendingTable (sh0 :: rest)) = n := by simp [Layout.count, hf1]
  rw [hc]
  omega

end


section
variable (L : Layout) {e : Ty}

/-- Every occupied slot's key is below `n`. -/
def belowT (S : List Slot) (n : Term) : Term := allT (S.map fun (f, xs) => .or (.not f) (.lt (xs.headD tt) n))

/-- The state invariant a script asserts beside well-formedness: every pending wire id is below the next one
(`Step.Inv`, which every step keeps). -/
def pendingBelowT (shs : List (PendingShape e)) (pending nextId : Term) : Except Refusal Term := do
  let (d, n, dt) ← collD L (pendingTable shs) [.dsl .fresh [], pendingEntry shs]
  pure (belowT (slotsOf d dt n 2 pending) nextId)

end

section
variable {L : Layout} {M : Model}

theorem belowT_iff {w : Ty} {n : Term} {n0 : Nat} (hn : n.denote M = .int (n0 : Int)) :
    {S : List Slot} → {sv : List (Bool × List Val)} → {ys : List ((Ty.dsl .fresh []).den × w.den)} →
    SlotsDen M S sv → Holds2 (ETab L (.dsl .fresh []) w) ys sv →
    (Holds M (belowT S n) ↔ ∀ y ∈ ys, (show Nat from y.1) < n0)
  | [], [], ys, _, hy => by
    cases ys with
    | nil => simp [belowT, allT, Holds, Term.denote, tt, Val.toBool]
    | cons _ _ => exact hy.elim
  | (f, xs) :: S, (b, vs) :: sv, ys, ⟨hf, hx, hS⟩, hy => by
    have hcons : Holds M (belowT ((f, xs) :: S) n) ↔
        Holds M (.or (.not f) (.lt (xs.headD tt) n)) ∧ Holds M (belowT S n) := by
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
        obtain ⟨a, b', rfl, ha, -⟩ := pair_terms (hx.trans hvs)
        change zk = .int (Int.ofNat y.1) at hk
        simp only [Holds, Term.denote, hf, ha, hk, hn, Val.toBool, Val.toInt, List.headD_cons, List.mem_cons,
          forall_eq_or_imp]
        simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
        exact and_congr_left' Int.ofNat_lt

/-- The asserted invariant is exact: it holds exactly when every pending wire id is below the next one. -/
theorem pendingBelow_iff {v : ServiceV} {shs : List (PendingShape v.event)} (hne : shs ≠ [])
    {pending nextId : Term} {ps0 : List (Step.Pending v.event)} (hpend : PendingRel L shs (pending.denote M) ps0)
    {n0 : Nat} (hn : nextId.denote M = .int (n0 : Int)) {t : Term} (henc : pendingBelowT L shs pending nextId = .ok t) :
    Holds M t ↔ ∀ p ∈ ps0, p.id < n0 := by
  obtain ⟨sh0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨tbl, ⟨d', n', dt', m', sv0, hf, hft, hl, hv, hw0, ys0, hp0, hh0⟩, hlist⟩ := hpend
  obtain ⟨hf1, m1, hft1⟩ := collD_ok h1
  obtain rfl : d = d' := find_det hf1 hf
  obtain rfl : n = n' := by have := hf1.symm.trans hf; cases this; rfl
  obtain rfl : dt = dt' := find_det hft1 hft
  have hT := slotsOf_den d dt 2 pending sv0 hv hw0
  rw [hl] at hT
  rw [belowT_iff hn hT hh0, ← hlist]
  simp only [pendingList, List.mem_map]
  constructor
  · rintro h _ ⟨y, hy, rfl⟩
    exact lt_of_eq_of_lt (pendingOf_id _ _ _) (h y (hp0.mem_iff.2 hy))
  · intro h y hy
    exact lt_of_eq_of_lt (pendingOf_id (sh0 :: rest) y.1 y.2).symm (h _ ⟨y, hp0.mem_iff.1 hy, rfl⟩)

end

end Tazuna.Smt
