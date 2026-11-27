import Tazuna.Smt.Step
import Tazuna.Smt.NoGap

/-! No layout gap in the step: `encodeStep` refuses only for the spec's reasons in each service's layout built from a
checked spec (`encodeStep_ofService`). Each encoder's lemma takes the types it looks up as `Got` or `Avail` facts and
the codes it applies as `CodeOk`, as `NoGap`'s expression encoder takes `Covers`; `ServiceGot` bundles them, and
`serviceGot_ofService` proves the builder supplies every one: the step's types are listed (`stepTys`, `useTys`),
every function the service keeps is a record of the program's sites or effect sites (`ServiceV.Reach`), and every
request kind has an external that lists it (`kinds_owner`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}

theorem ofDataE_sound {t : Ty} (x : Term) (ha : Avail L t) :
    Sound (fun c => CodeOk L P ds H t c) (Code.ofDataE t x) :=
  sound_mono (sound_need fun _ => rfl) fun _ h => codeOk_ofTerm h ha

theorem dataTermE_sound {t : Ty} (c : Code t) : Sound (fun _ => True) (Code.dataTermE t c) :=
  sound_mono (sound_need fun _ => rfl) fun _ _ => trivial

theorem apply_sound {ps : List Ty} {r : Ty} {f : Code (.fn ps r)} (hf : CodeOk L P ds H (.fn ps r) f) {xs : Codes ps}
    (hxs : CodesOk L P ds H ps xs) (hr : Avail L r) : Sound (fun p => CodeOk L P ds H r p.1) (f xs) :=
  hf xs hxs hr

theorem got_rules (h : Got L Ty.rules) : Got L (.tuple [.str, Ty.bool]) := (got_list h).1

theorem ruleTerms_sound (hL : SortedLayout L) (hr : Got L Ty.rules) (rs : Term) :
    Sound (fun _ => True) (ruleTerms L rs) := by
  unfold ruleTerms
  refine sound_bind (collD_sound hL (avail_of_got hr) fun h => ⟨h.2.2, h.2.1⟩) fun _ _ => ?_
  exact sound_bind (tupleD_sound hL (avail_of_got (got_rules hr))) fun _ _ => trivial

mutual
theorem ordT_some (T : List TypeDecl) : (t : Ty) → t.orderable = true → L.Has t → (x y : Term) →
    (ordT L T t x y).isSome = true
  | .int, _, _, _, _ | .date, _, _, _, _ | .str, _, _, _, _ => rfl
  | .id, _, h, _, _ => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (show (L.find? .id).isSome = true from h)
    simp [ordT, hx]
  | .tuple ts, ho, h, x, y => by
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 h.2
    simp only [ordT, hd, Option.bind_some]
    exact ordFields_some T d ts (by simpa [Ty.orderable] using ho) h.1 x y 0
  | .adt 0 _ vs, ho, _, x, y => by
    match vs, ho with
    | [[], []], _ => rfl
  | .adt (i + 1) a [fs], ho, h, x, y => by
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 h.2
    simp only [ordT, hd, Option.bind_some]
    exact ordFields_some T d fs (by simpa [Ty.orderable] using ho) h.1.1 x y 0
  | .adt (i + 1) a [], ho, h, x, y => by
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 h.2
    simp [ordT, hd]
  | .adt (i + 1) a (v1 :: v2 :: vs), ho, h, x, y => by
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 h.2
    have hv : (v1 :: v2 :: vs).all (·.isEmpty) = true := by simpa [Ty.orderable] using ho
    simp only [ordT, hv, ite_true, hd, Option.map_some, Option.isSome_some]
  | .list _, ho, _, _, _ | .bag _, ho, _, _, _ | .table .., ho, _, _, _ | .fn .., ho, _, _, _
  | .param _, ho, _, _, _ | .dsl .., ho, _, _, _ => by simp [Ty.orderable] at ho
theorem ordFields_some (T : List TypeDecl) (d : Nat) : (ts : List Ty) → Ty.orderables ts = true →
    Layout.HasWiths L (Layout.HasDsl L) ts → (x y : Term) → (j : Nat) → (ordFields L T d ts x y j).isSome = true
  | [], _, _, _, _, _ => rfl
  | t :: ts, ho, h, x, y, j => by
    simp only [Ty.orderables, Bool.and_eq_true] at ho
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (ordT_some T t ho.1 h.1 (.sel d 0 j x) (.sel d 0 j y))
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (ordFields_some T d ts ho.2 h.2 x y (j + 1))
    simp [ordFields, ha, hb]
end

/-- A request's admission, from an `accepts` code with no gap behind it, has none. -/
theorem encodeAdmit_sound (hL : SortedLayout L) {i c : Ty} {accepts : Code (Ty.fn [i] Ty.rules)}
    (hacc : CodeOk L P ds H _ accepts) (hc : Avail L c) (hi : Avail L i) (hr : Got L Ty.rules)
    (callers : List Term) (caller input : Term) :
    Sound (fun _ => True) (encodeAdmit (c := c) L accepts callers caller input) := by
  unfold encodeAdmit
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) caller hc) fun cc hcc => ?_
  refine sound_bind (sound_mapM callers fun k _ =>
    sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) k hc) fun _ _ => eqCode_sound hL cc _ hcc) fun _ _ => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) input hi) fun ic hic => ?_
  refine sound_bind (apply_sound hacc ⟨hic, trivial⟩ (avail_of_got hr)) fun _ _ => ?_
  exact sound_bind (ruleTerms_sound hL hr _) fun _ _ => trivial

/-- A command's context, where its type is available, has its code available. -/
theorem encodeCtx_sound {r i c : Ty} (hctx : Avail L (Ty.ctx r i c)) (records now fresh caller input : Term) :
    Sound (fun o => CodeOk L P ds H (Ty.ctx r i c) o) (encodeCtx L records now fresh caller input) := by
  unfold encodeCtx
  refine sound_bind (adtCtor_sound hctx _ _) fun _ _ => ?_
  exact ofDataE_sound (P := P) (ds := ds) (H := H) _ hctx

/-- A query's context, where its type is available, has its code available. -/
theorem encodeQueryCtx_sound {r i c : Ty} (hctx : Avail L (Ty.queryCtx r i c)) (records now caller input : Term) :
    Sound (fun o => CodeOk L P ds H (Ty.queryCtx r i c) o) (encodeQueryCtx L records now caller input) := by
  unfold encodeQueryCtx
  refine sound_bind (adtCtor_sound hctx _ _) fun _ _ => ?_
  exact ofDataE_sound (P := P) (ds := ds) (H := H) _ hctx

/-- The service's invariants on a records term, from a code with no gap behind it, have none. -/
theorem encodeInvariants_sound (hL : SortedLayout L) {r : Ty} {inv : Code (Ty.fn [r] Ty.rules)}
    (hinv : CodeOk L P ds H _ inv) (hr : Avail L r) (hR : Got L Ty.rules) (records : Term) :
    Sound (fun _ => True) (encodeInvariants L inv records) := by
  unfold encodeInvariants
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) records hr) fun rc hrc => ?_
  refine sound_bind (apply_sound hinv ⟨hrc, trivial⟩ (avail_of_got hR)) fun _ _ => ?_
  exact sound_bind (ruleTerms_sound hL hR _) fun _ _ => trivial

theorem encodeQuery_sound (hL : SortedLayout L) {r c : Ty} {v : ServiceV} (q : QueryV r c) (qc : QueryCode q)
    (hacc : CodeOk L P ds H _ qc.accepts) (hres : CodeOk L P ds H _ qc.resolve) (hc : Avail L (Ty.origin c))
    (hi : Avail L q.input) (ho : Avail L q.output) (hr : Got L Ty.rules) (hctx : Avail L (Ty.queryCtx r q.input c))
    (callers : List Term) (S : SymState v) (caller input : Term) :
    Sound (fun _ => True) (encodeQuery L q qc callers S caller input) := by
  unfold encodeQuery
  refine sound_bind (adtCtor_sound hc _ _) fun _ _ => ?_
  refine sound_bind (encodeAdmit_sound hL hacc hc hi hr _ _ _) fun _ _ => ?_
  refine sound_bind (encodeQueryCtx_sound (P := P) (ds := ds) (H := H) hctx _ _ _ _) fun a ha => ?_
  refine sound_bind (apply_sound hres ⟨ha, trivial⟩ ho) fun _ _ => ?_
  exact sound_bind (dataTermE_sound _) fun _ _ => trivial

end


section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {r e : Ty}

/-- The types a machine's step looks up are in the layout. -/
structure MachineGot (L : Layout) (m : MachineV r e) : Prop where
  table : Got L m.table
  ctx : Avail L (Ty.machineCtx m.key m.state r)
  tctx : Avail L (Ty.timerCtx m.key m.state r)
  next : Got L (Ty.next m.state)
  timer : Got L (Ty.option (Ty.timer m.state))
  bag : Got L (.bag m.key)
  orderable : m.key.orderable = true
  slots : ∀ x y, L.find? (.bag m.key) = some x → L.find? m.table = some y → x.2 ≤ y.2
  records : Avail L r
  event : Avail L e
  effect : Got L (Ty.option (.dsl .effect [e]))
  rules : Got L Ty.rules

/-- A machine's kept functions have codes with no gap behind them. -/
structure MachineCodes (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite)
    (m : MachineV r e) : Prop where
  instances : Sound (fun p => CodeOk L P ds H _ p.1) (m.instances.code L)
  on : Sound (fun p => CodeOk L P ds H _ p.1) (m.on.code L)
  timer : Sound (fun p => CodeOk L P ds H _ p.1) (m.timer.code L)
  effect : Sound (fun p => CodeOk L P ds H _ p.1) (m.effect.code L)
  invariants : Sound (fun p => CodeOk L P ds H _ p.1) (m.invariants.code L)

theorem has_find {i : Nat} {a : List Ty} {vs : List (List Ty)} (h : L.Has (.adt (i + 1) a vs)) :
    (L.find? (.adt (i + 1) a vs)).isSome = true := h.2

theorem has_find_tuple {ts : List Ty} (h : L.Has (.tuple ts)) : (L.find? (.tuple ts)).isSome = true := h.2

namespace MachineGot
variable {m : MachineV r e} (h : MachineGot L m)
include h

theorem key : Got L m.key := (got_table h.table).1
theorem entry : Got L m.state := (got_table h.table).2.1
theorem timerOne : Got L (Ty.timer m.state) := got_adt h.timer ⟨0, by simp⟩ _ (by simp)
theorem table_find : (L.find? m.table).isSome = true ∧ (L.find? (.tuple [Ty.bool, m.key, m.state])).isSome = true :=
  ⟨(got_table h.table).2.2.1, (got_table h.table).2.2.2⟩

end MachineGot

theorem collD_table_sound (hL : SortedLayout L) {m : MachineV r e} (h : MachineGot L m) :
    Sound (fun x => L.find? m.table = some (x.1, x.2.1)) (collD L m.table [m.key, m.state]) :=
  sound_mono (collD_sound hL (avail_of_got h.table) fun _ => h.table_find) fun _ hx => hx.1

theorem instCtxT_sound {m : MachineV r e} (h : MachineGot L m) (key state records now : Term) :
    Sound (fun _ => True) (instCtxT L m key state records now) :=
  adtCtor_sound h.ctx _ _

theorem ordKey_sound (T : List TypeDecl) {m : MachineV r e} (h : MachineGot L m) (x y : Term) :
    Sound (fun _ => True) (need (lacks m.key) (ordT L T m.key x y)) := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (ordT_some T m.key h.orderable h.key.1 x y)
  rw [hz]; trivial

theorem encodeInstInvariants_sound (hL : SortedLayout L) (T : List TypeDecl) {m : MachineV r e}
    (h : MachineGot L m) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)} (hinv : CodeOk L P ds H _ inv)
    (tbl records now : Term) : Sound (fun _ => True) (encodeInstInvariants L T m inv tbl records now) := by
  unfold encodeInstInvariants
  refine sound_bind (collD_table_sound hL h) fun _ _ => ?_
  refine sound_bind (sound_mapM _ fun ⟨f, key, entry⟩ _ => ?_) fun _ _ =>
    sound_bind (ordKey_sound T h tt tt) fun _ _ => trivial
  simp only [instCheckAt]
  refine sound_bind (instCtxT_sound h _ _ _ _) fun _ _ => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ h.ctx) fun cx hcx => ?_
  refine sound_bind (apply_sound hinv ⟨hcx, trivial⟩ (avail_of_got h.rules)) fun _ _ => ?_
  exact sound_bind (ruleTerms_sound hL h.rules _) fun _ _ => trivial

theorem reactCode_sound {m : MachineV r e} (hc : MachineCodes L P ds H m) :
    Sound (fun p => CodeOk L P ds H _ p.1.instances ∧ CodeOk L P ds H _ p.1.on ∧
      CodeOk L P ds H _ p.1.effect) (ReactCode.of L m) := by
  unfold ReactCode.of
  exact sound_bind hc.instances fun _ h1 => sound_bind hc.on fun _ h2 =>
    sound_bind hc.effect fun _ h4 => ⟨h1, h2, h4⟩

theorem firstSlots_sound (hL : SortedLayout L) {t : Ty} (ht : Avail L t) :
    (prev S : List (Slot 1)) → Sound (fun _ => True) (firstSlots L t prev S)
  | _, [] => trivial
  | prev, (f, xs) :: rest => by
    simp only [firstSlots]
    refine sound_bind (ofDataE_sound (P := []) (ds := []) (H := []) _ ht) fun k _ => ?_
    refine sound_bind (sound_mapM prev fun ⟨f', xs'⟩ _ => ?_) fun _ _ =>
      sound_bind (firstSlots_sound hL ht _ rest) fun _ _ => trivial
    exact sound_bind (ofDataE_sound (P := []) (ds := []) (H := []) _ ht) fun c hc =>
      sound_bind (eqCode_sound hL c k hc) fun _ _ => trivial

theorem reactAt_sound (hL : SortedLayout L) {m : MachineV r e} (h : MachineGot L m) {rc : ReactCode m}
    (hon : CodeOk L P ds H _ rc.on) (hfx : CodeOk L P ds H _ rc.effect)
    (dn : Nat) (So : List InstSlot) (init : Val) (dflt noneT records now : Term) (evc : Code e)
    (hevc : CodeOk L P ds H e evc) (x : Slot 1 × Term) :
    Sound (fun _ => True) (reactAt L m rc dn So init dflt noneT records now evc x) := by
  obtain ⟨⟨f, xs⟩, first⟩ := x
  simp only [reactAt]
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ (avail_of_got h.key)) fun kc _ => ?_
  refine sound_bind (sound_mapM So fun ⟨g, key, entry⟩ _ => ?_) fun _ _ => ?_
  · simp only [hitAt]
    exact sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ (avail_of_got h.key)) fun c hc =>
      sound_bind (eqCode_sound hL c kc hc) fun _ _ => trivial
  refine sound_bind (instCtxT_sound h _ _ _ _) fun _ _ => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ h.ctx) fun oc hoc => ?_
  refine sound_bind (apply_sound hon ⟨hoc, hevc, trivial⟩ (avail_of_got h.next)) fun _ _ => ?_
  refine sound_bind (dataTermE_sound _) fun _ _ => ?_
  refine sound_bind (instCtxT_sound h _ _ _ _) fun _ _ => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ h.ctx) fun nc hnc => ?_
  refine sound_bind (apply_sound hfx ⟨hnc, trivial⟩ (avail_of_got h.effect)) fun _ _ => ?_
  exact sound_bind (dataTermE_sound _) fun _ _ => trivial

theorem encodeReact_sound (hL : SortedLayout L) {m : MachineV r e} (h : MachineGot L m) {rc : ReactCode m}
    (hin : CodeOk L P ds H _ rc.instances) (hon : CodeOk L P ds H _ rc.on)
    (hfx : CodeOk L P ds H _ rc.effect) (tbl records now ev : Term) :
    Sound (fun _ => True) (encodeReact L m rc tbl records now ev) := by
  unfold encodeReact
  refine sound_bind (collD_table_sound hL h) fun ⟨d, n, dt⟩ hd => ?_
  refine sound_bind (findE_sound hL (avail_of_got h.next) has_find) fun _ _ => ?_
  refine sound_bind (findE_sound hL (avail_of_got h.effect) has_find) fun _ _ => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ h.records) fun rcd hrcd => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ h.event) fun evc hevc => ?_
  refine sound_bind (apply_sound hin ⟨hrcd, trivial⟩ (avail_of_got h.bag)) fun _ _ => ?_
  refine sound_bind (dataTermE_sound _) fun _ _ => ?_
  refine sound_bind (collD_sound hL (avail_of_got h.bag) fun g => ⟨g.2.2, g.2.1⟩) fun ⟨db, nb, dtb⟩ hb => ?_
  dsimp only at hb hd
  dsimp only
  refine sound_bind sound_need_limit fun _ _ => ?_
  obtain ⟨dflt, hdflt⟩ := defaultE_ok hL h.entry
  refine sound_bind_ok hdflt ?_
  refine sound_bind (firstSlots_sound hL (avail_of_got h.key) _ _) fun _ _ => ?_
  refine sound_bind (sound_mapM _ fun x _ => reactAt_sound hL h hon hfx _ _ _ _ _ _ _ _ hevc x) fun _ _ => ?_
  have hle : nb ≤ n := h.slots _ _ hb.1 hd
  simp only [need', hle, decide_true, ite_true]
  obtain ⟨dk, hdk⟩ := defaultE_ok hL h.key
  simp only [bind, Except.bind, hdk]
  trivial

theorem encodeMachine_sound (hL : SortedLayout L) {m : MachineV r e} (h : MachineGot L m)
    (hc : MachineCodes L P ds H m) (tbl records now ev : Term) :
    Sound (fun _ => True) (encodeMachine L m tbl records now ev) := by
  unfold encodeMachine
  exact sound_bind (reactCode_sound hc) fun _ ⟨h1, h2, h4⟩ =>
    sound_bind (encodeReact_sound hL h h1 h2 h4 _ _ _ _) fun _ _ => trivial

theorem encodeMachines_sound (hL : SortedLayout L) :
    (ms : List (MachineV r e)) → (∀ m ∈ ms, MachineGot L m ∧ MachineCodes L P ds H m) →
    (xs : PerMachine (fun _ => Term) ms) → (records now ev : Term) →
    Sound (fun _ => True) (encodeMachines L ms xs records now ev)
  | [], _, .nil, _, _, _ => trivial
  | m :: ms, h, .cons x xs, records, now, ev => by
    simp only [encodeMachines]
    have hm := h m (by simp)
    exact sound_bind (encodeMachine_sound hL hm.1 hm.2 _ _ _ _) fun _ _ =>
      sound_bind (encodeMachines_sound hL ms (fun m' hm' => h m' (by simp [hm'])) xs _ _ _) fun _ _ => trivial

theorem encodeInstChecks_sound (hL : SortedLayout L) (T : List TypeDecl) :
    (ms : List (MachineV r e)) → (∀ m ∈ ms, MachineGot L m ∧ MachineCodes L P ds H m) →
    (xs : PerMachine (fun _ => Term) ms) → (records now : Term) →
    Sound (fun _ => True) (encodeInstChecks L T ms xs records now)
  | [], _, .nil, _, _ => trivial
  | m :: ms, h, .cons x xs, records, now => by
    simp only [encodeInstChecks]
    have hm := h m (by simp)
    exact sound_bind hm.2.invariants fun _ hinv =>
      sound_bind (encodeInstInvariants_sound hL T hm.1 hinv _ _ _) fun _ _ =>
      sound_bind (encodeInstChecks_sound hL T ms (fun m' hm' => h m' (by simp [hm'])) xs _ _) fun _ _ => trivial

end


section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {r e : Ty}

/-- Every request kind of the layout of the event type `e` has an external in `ds`. -/
def OwnersOk (L : Layout) (e : Ty) (ds : List (String × DeclaredV)) : Prop :=
  ∀ key ∈ L.effectsOf e, ∃ x, key.owner ds = some x

theorem shapeIdxs_sound {shs : List (PendingShape e)} {snd : (ks : List Ty) × SenderShape ks}
    (h : OwnersOk L e ds) : Sound (fun _ => True) (shapeIdxs shs ds snd (L.effectsOf e)) := by
  unfold shapeIdxs
  refine sound_mapM _ fun key hk => ?_
  obtain ⟨x, hx⟩ := h key hk
  exact sound_bind_ok (need_ok.2 hx) trivial

theorem rankStarts_sound (T : List TypeDecl) {m : MachineV r e} (h : MachineGot L m) (dopt : Nat) (n : Term)
    (S : List StartSlot) : Sound (fun _ => True) (rankStarts L T m dopt n S) := by
  unfold rankStarts
  refine sound_mapM _ fun s _ => ?_
  unfold rankStart
  refine sound_bind (sound_mapM _ fun s' _ => ?_) fun _ _ => trivial
  exact sound_bind (ordKey_sound T h _ _) fun _ _ => trivial

theorem ownStarts_sound (T : List TypeDecl) {m : MachineV r e} (h : MachineGot L m) (dopt : Nat) (none : Bool)
    (os : List StartSlot) (q : Term) : Sound (fun _ => True) (ownStarts L T m dopt none os q) := by
  unfold ownStarts
  split
  · trivial
  · exact sound_bind (rankStarts_sound T h _ _ _) fun _ _ => trivial

theorem encodeStarts_sound (hL : SortedLayout L) (T : List TypeDecl) {shs : List (PendingShape e)}
    (senv : StepEnv L shs) (hent : Got L (pendingEntry shs)) :
    (ms : List (MachineV r e)) →
    (∀ m ∈ ms, MachineGot L m ∧ Got L (.tuple [m.key]) ∧ OwnersOk L e ds) →
    (sts : PerMachine (fun _ => List StartSlot) ms) → (n q : Term) →
    Sound (fun _ => True) (encodeStarts L T shs ds senv ms sts n q)
  | [], _, .nil, _, _ => trivial
  | m :: ms, h, .cons st sts, n, q => by
    have hm := h m (by simp)
    simp only [encodeStarts]
    refine sound_bind (findE_sound hL (avail_of_got hm.2.1) has_find_tuple) fun _ _ => ?_
    refine sound_bind (shapeIdxs_sound hm.2.2) fun _ _ => ?_
    obtain ⟨dflt, hdflt⟩ := defaultE_ok hL hent
    refine sound_bind_ok hdflt ?_
    refine sound_bind (rankStarts_sound T hm.1 _ _ _) fun _ _ => ?_
    refine sound_bind (ownStarts_sound T hm.1 _ _ _ _) fun _ _ => ?_
    exact sound_bind (encodeStarts_sound hL T senv hent ms (fun m' hm' => h m' (by simp [hm'])) sts _ _) fun _ _ =>
      trivial

theorem encodePending_sound (hL : SortedLayout L) {shs : List (PendingShape e)} (ht : Got L (pendingTable shs))
    (pending : Term) (news : List PendingSlot) : Sound (fun _ => True) (encodePending L shs pending news) := by
  unfold encodePending
  exact sound_bind (collD_sound hL (avail_of_got ht) fun g => ⟨g.2.2.2, g.2.2.1⟩) fun _ _ => trivial

/-- The types and codes a reaction's step needs. -/
structure ReactionOk (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite)
    (shs : List (PendingShape e)) (ds' : List (String × DeclaredV)) (x : ReactionV r e) : Prop where
  code : Sound (fun p => CodeOk L P ds H _ p.1) (x.react.code L)
  shapes : OwnersOk L e ds'
  ctx : Avail L (Ty.reactionCtx r)
  effects : Got L (.list (.dsl .effect [e]))

theorem encodeReactions_sound (hL : SortedLayout L) {shs : List (PendingShape e)} {ds' : List (String × DeclaredV)}
    (dE dP : Nat) (hev : Avail L e) (hu : Got L (.tuple [])) (hent : Got L (pendingEntry shs)) :
    (xs : List (ReactionV r e)) → (∀ x ∈ xs, ReactionOk L P ds H shs ds' x) → (records now ev n q : Term) →
    Sound (fun _ => True) (encodeReactions L shs ds' dE dP xs records now ev n q)
  | [], _, _, _, _, _, _ => trivial
  | x :: xs, h, records, now, ev, n, q => by
    have hx := h x (by simp)
    have hctx := hx.ctx
    have hl := hx.effects
    simp only [encodeReactions]
    refine sound_bind hx.code fun _ hrc => ?_
    refine sound_bind (adtCtor_sound hctx _ _) fun _ _ => ?_
    refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hctx) fun cx hcx => ?_
    refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hev) fun evc hevc => ?_
    refine sound_bind (apply_sound hrc ⟨hcx, hevc, trivial⟩ (avail_of_got hl)) fun _ _ => ?_
    refine sound_bind (dataTermE_sound _) fun _ _ => ?_
    refine sound_bind (collD_sound hL (avail_of_got hl) fun g => ⟨g.2.2, g.2.1⟩) fun _ _ => ?_
    refine sound_bind (findE_sound hL (avail_of_got hu) has_find_tuple) fun _ _ => ?_
    refine sound_bind (shapeIdxs_sound hx.shapes) fun _ _ => ?_
    obtain ⟨dflt, hdflt⟩ := defaultE_ok hL hent
    refine sound_bind_ok hdflt ?_
    exact sound_bind (encodeReactions_sound hL dE dP hev hu hent xs (fun y hy => h y (by simp [hy])) _ _ _ _ _)
      fun _ _ => trivial

end


section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {v : ServiceV}
  {live : Option (List SiteId)}

/-- The types and codes a command's step needs. -/
structure CommandOk (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite)
    (v : ServiceV) (x : CommandV v.records v.event v.caller) : Prop where
  accepts : Sound (fun p => CodeOk L P ds H _ p.1) (x.accepts.code L)
  decide : Sound (fun p => CodeOk L P ds H _ p.1) (x.decide.code L)
  ensures : Sound (fun p => CodeOk L P ds H _ p.1) (x.ensures.code L)
  input : Avail L x.input
  ctx : Avail L (Ty.ctx v.records x.input v.caller)
  result : Avail L (Ty.result (.list v.event) x.rejection)

/-- The types and codes a query's step needs. -/
structure QueryOk (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite)
    (v : ServiceV) (q : QueryV v.records v.caller) : Prop where
  accepts : Sound (fun p => CodeOk L P ds H _ p.1) (q.accepts.code L)
  resolve : Sound (fun p => CodeOk L P ds H _ p.1) (q.resolve.code L)
  input : Avail L q.input
  output : Avail L q.output
  ctx : Avail L (Ty.queryCtx v.records q.input v.caller)

/-- What an own kind's internal step needs: its command's or query's, the captured values' tuple, and its site. -/
def OwnOk (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite) (v : ServiceV)
    (key : OwnKey) : Prop :=
  match ownShape v P key with
  | some (.command x Γ site) => CommandOk L P ds H v x ∧ Got L (.tuple Γ) ∧ SiteCodeOk L P ds H ⟨Γ, _, site⟩ ∧
      Avail L Ty.nil ∧ Avail L (Ty.result Ty.nil x.rejection)
  | some (.query x Γ site) => QueryOk L P ds H v x ∧ Got L (.tuple Γ) ∧ SiteCodeOk L P ds H ⟨Γ, _, site⟩
  | some (.unreached _) => True
  | none => False

/-- Everything a step of the service looks up is in the layout, and every code it applies has no gap behind it. -/
structure ServiceGot (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite)
    (v : ServiceV) (shs : List (PendingShape v.event)) : Prop where
  sorted : SortedLayout L
  records : Got L v.records
  event : Got L v.event
  caller : Got L v.caller
  origin : Got L (Ty.origin v.caller)
  rules : Got L Ty.rules
  events : Got L (.list v.event)
  unit : Got L (.tuple [])
  table : Got L (pendingTable shs)
  apply : Sound (fun p => CodeOk L P ds H _ p.1) (v.apply.code L)
  applyCtx : Avail L (Ty.applyCtx v.records)
  invariants : Sound (fun p => CodeOk L P ds H _ p.1) (v.invariants.code L)
  machines : ∀ m ∈ v.machines, (MachineGot L m ∧ MachineCodes L P ds H m) ∧ Got L (.tuple [m.key]) ∧
    OwnersOk L v.event v.declared
  reactions : ∀ x ∈ v.reactions, ReactionOk L P ds H shs v.declared x
  commands : ∀ x ∈ v.commands, CommandOk L P ds H v x
  queries : ∀ q ∈ v.queries, QueryOk L P ds H v q
  subscribes : ∀ i : Fin v.subscribes.length, Avail L (v.subscribes.get i).event ∧
    Sound (fun p => CodeOk L P ds H _ p.1) ((v.subscribes.get i).wrap.code L)
  owns : ∀ key ∈ L.ownsOf v.event, OwnOk L P ds H v key

namespace ServiceGot
variable {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs)
include h

theorem entry : Got L (pendingEntry shs) := (got_table h.table).2.1

end ServiceGot

theorem encodeEvents_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)} (happ : CodeOk L P ds H _ apply)
    (now : Term) : (S : List (Slot 1)) → (records : Term) → (xs : PerMachine (fun _ => Term) v.machines) →
    (n q : Term) → Sound (fun _ => True) (encodeEvents L T v shs senv apply now S records xs n q)
  | [], _, _, _, _ => trivial
  | (f, ys) :: S, records, xs, n, q => by
    have hL := h.sorted
    simp only [encodeEvents]
    refine sound_bind (adtCtor_sound h.applyCtx _ _) fun _ _ => ?_
    refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ h.applyCtx) fun rc hrc => ?_
    refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ (avail_of_got h.event)) fun ec hec => ?_
    refine sound_bind (apply_sound happ ⟨hrc, hec, trivial⟩ (avail_of_got h.records)) fun _ _ => ?_
    refine sound_bind (dataTermE_sound _) fun _ _ => ?_
    refine sound_bind (encodeMachines_sound hL _ (fun m hm => (h.machines m hm).1) _ _ _ _) fun _ _ => ?_
    refine sound_bind (encodeStarts_sound hL T senv h.entry _
      (fun m hm => ⟨(h.machines m hm).1.1, (h.machines m hm).2⟩) _ _ _) fun _ _ => ?_
    refine sound_bind (encodeReactions_sound hL _ _ (avail_of_got h.event) h.unit h.entry _
      h.reactions _ _ _ _ _) fun _ _ => ?_
    exact sound_bind (encodeEvents_sound h T senv happ now S _ _ _ _) fun _ _ => trivial

theorem commandCode_sound {x : CommandV v.records v.event v.caller} (hx : CommandOk L P ds H v x) :
    Sound (fun p => CodeOk L P ds H _ p.1.accepts ∧ CodeOk L P ds H _ p.1.decide ∧
      CodeOk L P ds H _ p.1.ensures) (CommandCode.of L x) := by
  unfold CommandCode.of
  exact sound_bind hx.accepts fun _ h1 => sound_bind hx.decide fun _ h2 => sound_bind hx.ensures fun _ h3 =>
    ⟨h1, h2, h3⟩

theorem queryCode_sound {q : QueryV v.records v.caller} (hq : QueryOk L P ds H v q) :
    Sound (fun p => CodeOk L P ds H _ p.1.accepts ∧ CodeOk L P ds H _ p.1.resolve) (QueryCode.of L q) := by
  unfold QueryCode.of
  exact sound_bind hq.accepts fun _ h1 => sound_bind hq.resolve fun _ h2 => ⟨h1, h2⟩

theorem encodeDecide_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) {x : CommandV v.records v.event v.caller} (hx : CommandOk L P ds H v x)
    {cc : CommandCode x} (hdec : CodeOk L P ds H _ cc.decide) (hens : CodeOk L P ds H _ cc.ensures)
    {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)} (happ : CodeOk L P ds H _ apply)
    {ctx : Code (Ty.ctx v.records x.input v.caller)} (hctx : CodeOk L P ds H _ ctx) (now records : Term)
    (xs : PerMachine (fun _ => Term) v.machines) (n q : Term) :
    Sound (fun _ => True) (encodeDecide L T v shs senv x cc apply ctx now records xs n q) := by
  have hL := h.sorted
  unfold encodeDecide
  refine sound_bind (apply_sound hdec ⟨hctx, trivial⟩ hx.result) fun _ _ => ?_
  refine sound_bind (dataTermE_sound _) fun _ _ => ?_
  refine sound_bind (findE_sound hL hx.result has_find) fun _ _ => ?_
  refine sound_bind (collD_sound hL (avail_of_got h.events) fun g => ⟨g.2.2, g.2.1⟩) fun _ _ => ?_
  refine sound_bind (encodeEvents_sound h T senv happ _ _ _ _ _ _) fun _ _ => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ (avail_of_got h.records)) fun rfc hrfc => ?_
  refine sound_bind (apply_sound hens ⟨hctx, hrfc, trivial⟩ (avail_of_got h.rules)) fun _ _ => ?_
  exact sound_bind (ruleTerms_sound hL h.rules _) fun _ _ => trivial

end


section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {v : ServiceV}
  {live : Option (List SiteId)}

theorem tupleCodes_ok (d : Nat) (x : Term) : (Γ : List Ty) → (i : Nat) → {σ : Codes Γ} →
    tupleCodes d Γ x i = some σ → (∀ u ∈ Γ, Avail L u) → CodesOk L P ds H Γ σ
  | [], _, (), _, _ => trivial
  | t :: Γ, i, (c, cs), hσ, ha => by
    cases hc : Code.ofTerm? t (Term.sel d 0 i x) with
    | none => simp [tupleCodes, hc] at hσ
    | some c' =>
      cases hcs : tupleCodes d Γ x (i + 1) with
      | none => simp [tupleCodes, hc, hcs] at hσ
      | some cs' =>
        simp only [tupleCodes, hc, hcs, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hσ
        obtain ⟨rfl, rfl⟩ := hσ
        exact ⟨codeOk_ofTerm hc (ha t (by simp)), tupleCodes_ok d x Γ (i + 1) hcs fun u hu => ha u (by simp [hu])⟩

/-- The codes of a site's captured values read from a tuple field have no gap behind them, given the tuple's type. -/
theorem capturedCodes_sound {Γ : List Ty} (hg : Got L (.tuple Γ)) (d : Nat) (x : Term) :
    Sound (fun σ => CodesOk L P ds H Γ σ) (need (.unexpected (.function (.tuple Γ))) (tupleCodes d Γ x 0)) :=
  sound_mono (sound_need fun _ => rfl) fun _ hσ => tupleCodes_ok d x Γ 0 hσ fun u hu => avail_of_got (got_tuple hg u hu)

theorem encodeOwnCommand_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) {x : CommandV v.records v.event v.caller} (hx : CommandOk L P ds H v x)
    {cc : CommandCode x} (hacc : CodeOk L P ds H _ cc.accepts) (hdec : CodeOk L P ds H _ cc.decide)
    (hens : CodeOk L P ds H _ cc.ensures) {Γ : List Ty}
    (site : Site Γ (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) (hs : SiteCodeOk L P ds H ⟨Γ, _, site⟩)
    (hnil : Avail L Ty.nil) (hans : Avail L (Ty.result Ty.nil x.rejection)) {σ : Codes Γ} (hσ : CodesOk L P ds H Γ σ) {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)}
    (happ : CodeOk L P ds H _ apply) (callers : List Term) (records now fresh n q caller input : Term)
    (xs : PerMachine (fun _ => Term) v.machines) :
    Sound (fun _ => True)
      (encodeOwnCommand L T v shs senv x cc site σ apply callers records now fresh n q caller input xs) := by
  have hL := h.sorted
  unfold encodeOwnCommand
  refine sound_bind (encodeAdmit_sound hL hacc (avail_of_got h.origin) hx.input h.rules _ _ _) fun _ _ => ?_
  refine sound_bind (encodeCtx_sound (P := P) (ds := ds) (H := H) hx.ctx _ _ _ _ _) fun a ha => ?_
  refine sound_bind (encodeDecide_sound h T senv hx hdec hens happ ha _ _ _ _ _) fun _ _ => ?_
  refine sound_bind (adtCtor_sound hnil _ _) fun _ _ => ?_
  refine sound_bind (adtCtor_sound hans _ _) fun _ _ => ?_
  refine sound_bind (adtCtor_sound hans _ _) fun _ _ => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hans) fun ac hac => ?_
  refine sound_bind (hs σ hσ) fun _ hoa => ?_
  refine sound_bind (apply_sound hoa ⟨hac, trivial⟩ (avail_of_got h.events)) fun _ _ => ?_
  refine sound_bind (dataTermE_sound _) fun _ _ => ?_
  refine sound_bind (collD_sound hL (avail_of_got h.events) fun g => ⟨g.2.2, g.2.1⟩) fun _ _ => ?_
  exact sound_bind (encodeEvents_sound h T senv happ _ _ _ _ _ _) fun _ _ => trivial

theorem encodeOwnQuery_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) {x : QueryV v.records v.caller} (hx : QueryOk L P ds H v x)
    {qc : QueryCode x} (hacc : CodeOk L P ds H _ qc.accepts) (hres : CodeOk L P ds H _ qc.resolve) {Γ : List Ty}
    (site : Site Γ (Ty.fn [x.output] (.list v.event))) (hs : SiteCodeOk L P ds H ⟨Γ, _, site⟩)
    {σ : Codes Γ} (hσ : CodesOk L P ds H Γ σ) {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)}
    (happ : CodeOk L P ds H _ apply) (callers : List Term) (records now n q caller input : Term)
    (xs : PerMachine (fun _ => Term) v.machines) :
    Sound (fun _ => True)
      (encodeOwnQuery L T v shs senv x qc site σ apply callers records now n q caller input xs) := by
  have hL := h.sorted
  unfold encodeOwnQuery
  refine sound_bind (encodeAdmit_sound hL hacc (avail_of_got h.origin) hx.input h.rules _ _ _) fun _ _ => ?_
  refine sound_bind (encodeQueryCtx_sound (P := P) (ds := ds) (H := H) hx.ctx _ _ _ _) fun a ha => ?_
  refine sound_bind (apply_sound hres ⟨ha, trivial⟩ hx.output) fun _ hout => ?_
  refine sound_bind (hs σ hσ) fun _ hoa => ?_
  refine sound_bind (apply_sound hoa ⟨hout, trivial⟩ (avail_of_got h.events)) fun _ _ => ?_
  refine sound_bind (dataTermE_sound _) fun _ _ => ?_
  refine sound_bind (collD_sound hL (avail_of_got h.events) fun g => ⟨g.2.2, g.2.1⟩) fun _ _ => ?_
  exact sound_bind (encodeEvents_sound h T senv happ _ _ _ _ _ _) fun _ _ => trivial

theorem encodeOwnKind_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) (nR : Nat) {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)}
    (happ : CodeOk L P ds H _ apply) (records now fresh n q eff : Term) (xs : PerMachine (fun _ => Term) v.machines)
    (j : Nat) {key : OwnKey} (hk : key ∈ L.ownsOf v.event) :
    Sound (fun _ => True) (encodeOwnKind L T P v shs senv nR apply records now fresh n q eff xs j key) := by
  have hL := h.sorted
  have ho := h.owns key hk
  unfold OwnOk at ho
  unfold encodeOwnKind
  cases hsh : ownShape v P key with
  | none => rw [hsh] at ho; exact ho.elim
  | some sh =>
  rw [hsh] at ho
  refine sound_bind_ok rfl ?_
  cases sh with
  | unreached _ => trivial
  | command x Γ site =>
    obtain ⟨hx, hg, hs, hnil, hans⟩ := ho
    refine sound_bind (commandCode_sound hx) fun _ ⟨h1, h2, h3⟩ => ?_
    refine sound_bind sound_need_limit fun _ _ => ?_
    refine sound_bind (adtCtor_sound (avail_of_got h.origin) _ _) fun _ _ => ?_
    refine sound_bind (findE_sound hL (avail_of_got hg) has_find_tuple) fun _ _ => ?_
    refine sound_bind (capturedCodes_sound (P := P) (ds := ds) (H := H) hg _ _) fun σ hσ => ?_
    exact sound_bind (encodeOwnCommand_sound h T senv hx h1 h2 h3 site hs hnil hans hσ happ _ _ _ _ _ _ _ _ _)
      fun _ _ => trivial
  | query x Γ site =>
    obtain ⟨hx, hg, hs⟩ := ho
    refine sound_bind (queryCode_sound hx) fun _ ⟨h1, h2⟩ => ?_
    refine sound_bind sound_need_limit fun _ _ => ?_
    refine sound_bind (adtCtor_sound (avail_of_got h.origin) _ _) fun _ _ => ?_
    refine sound_bind (findE_sound hL (avail_of_got hg) has_find_tuple) fun _ _ => ?_
    refine sound_bind (capturedCodes_sound (P := P) (ds := ds) (H := H) hg _ _) fun σ hσ => ?_
    exact sound_bind (encodeOwnQuery_sound h T senv hx h1 h2 site hs hσ happ _ _ _ _ _ _ _ _) fun _ _ => trivial

theorem encodeOwnStep_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)} (happ : CodeOk L P ds H _ apply)
    (records now fresh n q eff : Term) (xs : PerMachine (fun _ => Term) v.machines) :
    Sound (fun _ => True) (encodeOwnStep L T P live v shs senv apply records now fresh n q eff xs) := by
  unfold encodeOwnStep
  refine sound_bind (sound_mapM _ fun ⟨key, j⟩ hkj => ?_) fun _ _ => trivial
  exact sound_bind (encodeOwnKind_sound h T senv _ happ _ _ _ _ _ _ _ _ (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hkj))) fun _ _ => trivial

end


section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {v : ServiceV}
  {live : Option (List SiteId)}

theorem encodeSettle_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)} (happ : CodeOk L P ds H _ apply)
    (dflt now : Term) : (fuel k : Nat) → (S : List OwnSlot) → (t : StepTerms v) →
    Sound (fun _ => True) (encodeSettle L T P live v shs senv apply dflt now fuel k S t)
  | 0, _, _, _ => trivial
  | f + 1, k, S, t => by
    simp only [encodeSettle]
    exact sound_bind (encodeOwnStep_sound h T senv happ _ _ _ _ _ _ _) fun _ _ =>
      sound_bind (encodeSettle_sound h T senv happ dflt now f (k + 1) _ _) fun _ _ => trivial

theorem instFitsT_sound {r e : Ty} : (ms : List (MachineV r e)) → (∀ m ∈ ms, MachineGot L m ∧ MachineCodes L P ds H m) →
    (records : Term) → Sound (fun _ => True) (instFitsT L ms records)
  | [], _, _ => trivial
  | m :: ms, h, records => by
    have hm := h m (List.mem_cons_self ..)
    simp only [instFitsT]
    refine sound_bind hm.2.instances fun ⟨ic, _⟩ hin => ?_
    refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hm.1.records) fun rcd hrcd => ?_
    refine sound_bind (apply_sound hin ⟨hrcd, trivial⟩ (avail_of_got hm.1.bag)) fun _ _ => ?_
    exact sound_bind (instFitsT_sound ms (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) records) fun _ _ => trivial

theorem encodeFinish_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)} (happ : CodeOk L P ds H _ apply)
    {inv : Code (Ty.fn [v.records] Ty.rules)} (hinv : CodeOk L P ds H _ inv) (now fresh pending : Term)
    (o : EventsOut v) : Sound (fun _ => True) (encodeFinish L T P live v shs senv apply inv now fresh pending o) := by
  have hL := h.sorted
  unfold encodeFinish
  refine sound_bind (encodeSettle_sound h T senv happ _ _ _ _ _ _) fun _ _ => ?_
  refine sound_bind (encodePending_sound hL h.table _ _) fun _ _ => ?_
  refine sound_bind (encodeInvariants_sound hL hinv (avail_of_got h.records) h.rules _) fun _ _ => ?_
  exact sound_bind (encodeInstChecks_sound hL T _ (fun m hm => (h.machines m hm).1) _ _ _) fun _ _ =>
    sound_bind (instFitsT_sound _ (fun m hm => (h.machines m hm).1) _) fun _ _ => trivial

theorem encodeCommand_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) {x : CommandV v.records v.event v.caller} (hx : CommandOk L P ds H v x)
    {cc : CommandCode x} (hacc : CodeOk L P ds H _ cc.accepts) (hdec : CodeOk L P ds H _ cc.decide)
    (hens : CodeOk L P ds H _ cc.ensures) {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)}
    (happ : CodeOk L P ds H _ apply) {inv : Code (Ty.fn [v.records] Ty.rules)} (hinv : CodeOk L P ds H _ inv)
    (callers : List Term) (S : SymState v) (caller input : Term) :
    Sound (fun _ => True) (encodeCommand L T P live v shs senv x cc apply inv callers S caller input) := by
  have hL := h.sorted
  unfold encodeCommand
  refine sound_bind (adtCtor_sound (avail_of_got h.origin) _ _) fun _ _ => ?_
  refine sound_bind (encodeAdmit_sound hL hacc (avail_of_got h.origin) hx.input h.rules _ _ _) fun _ _ => ?_
  refine sound_bind (encodeCtx_sound (P := P) (ds := ds) (H := H) hx.ctx _ _ _ _ _) fun a ha => ?_
  refine sound_bind (encodeDecide_sound h T senv hx hdec hens happ ha _ _ _ _ _) fun _ _ => ?_
  exact sound_bind (encodeFinish_sound h T senv happ hinv _ _ _ _) fun _ _ => trivial

theorem encodeWrap_sound {i : Fin v.subscribes.length} {ec : EventCode v i} (hw : CodeOk L P ds H _ ec.wrap)
    (hu : Avail L (v.subscribes.get i).event) (he : Avail L v.event) (value : Term) :
    Sound (fun _ => True) (encodeWrap ec value) := by
  unfold encodeWrap
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hu) fun vc hvc => ?_
  refine sound_bind (apply_sound hw ⟨hvc, trivial⟩ he) fun _ _ => ?_
  exact sound_bind (dataTermE_sound _) fun _ _ => trivial

theorem encodeEvent_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) {i : Fin v.subscribes.length} {ec : EventCode v i} (ha : CodeOk L P ds H _ ec.apply)
    (hw : CodeOk L P ds H _ ec.wrap) (hn : CodeOk L P ds H _ ec.invariants) (S : SymState v) (value : Term) :
    Sound (fun _ => True) (encodeEvent L T P live v shs senv ec S value) := by
  unfold encodeEvent
  refine sound_bind (encodeWrap_sound hw (h.subscribes i).1 (avail_of_got h.event) _) fun _ _ => ?_
  refine sound_bind (encodeEvents_sound h T senv ha _ _ _ _ _ _) fun _ _ => ?_
  exact sound_bind (encodeFinish_sound h T senv ha hn _ _ _ _) fun _ _ => trivial

theorem eventCode_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs)
    (i : Fin v.subscribes.length) :
    Sound (fun p => CodeOk L P ds H _ p.1.apply ∧ CodeOk L P ds H _ p.1.wrap ∧ CodeOk L P ds H _ p.1.invariants)
      (EventCode.of L v i) := by
  unfold EventCode.of
  exact sound_bind h.apply fun _ h1 => sound_bind (h.subscribes i).2 fun _ h2 => sound_bind h.invariants fun _ h3 =>
    ⟨h1, h2, h3⟩

end


section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {v : ServiceV}
  {live : Option (List SiteId)}

/-- What an answer to a request of the shape needs: the captured values' tuples, the input's and answer's types and
the shape's sites. -/
structure AnswerOk (L : Layout) (P : List AnySite) (ds : List (String × DeclaredV)) (H : List HandleSite)
    {e : Ty} (sh : PendingShape e) : Prop where
  answerΓ : Got L (.tuple sh.answerΓ)
  ensuresΓ : Got L (.tuple sh.ensuresΓ)
  input : Avail L sh.input
  answer : Avail L (answerTy sh.output sh.rejection)
  onAnswer : SiteCodeOk L P ds H ⟨sh.answerΓ, _, sh.onAnswer⟩
  ensures : ∀ s ∈ sh.ensures, SiteCodeOk L P ds H ⟨s.1, _, s.2⟩

theorem ensuresTerms_sound (hL : SortedLayout L) (hr : Got L Ty.rules) {e : Ty}
    {sh : PendingShape e} (ha : AnswerOk L P ds H sh) (de k : Nat) (entry : Term)
    {vc : Code (answerTy sh.output sh.rejection)} (hvc : CodeOk L P ds H _ vc) :
    Sound (fun _ => True) (ensuresTerms L sh de k entry vc) := by
  unfold ensuresTerms
  split
  · trivial
  · rename_i Γ es hes
    have hg : Got L (.tuple Γ) := by
      have := ha.ensuresΓ; simp only [RequestShape.ensuresΓ, hes, Option.map_some, Option.getD_some] at this
      exact this
    refine sound_bind (findE_sound hL (avail_of_got hg) has_find_tuple) fun _ _ => ?_
    refine sound_bind (capturedCodes_sound (P := P) (ds := ds) (H := H) hg _ _) fun σ hσ => ?_
    refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ ha.input) fun ic hic => ?_
    refine sound_bind (ha.ensures ⟨Γ, es⟩ (by simp [hes]) σ hσ) fun _ hoe => ?_
    refine sound_bind (apply_sound hoe ⟨hic, hvc, trivial⟩ (avail_of_got hr)) fun _ _ => ?_
    exact sound_bind (ruleTerms_sound hL hr _) fun _ _ => trivial

theorem encodeAnswer_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (k : Nat) {sh : PendingShape v.event} (ha : AnswerOk L P ds H sh) (senv : StepEnv L shs) (j : Fin senv.nT)
    {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)} (happ : CodeOk L P ds H _ apply)
    {inv : Code (Ty.fn [v.records] Ty.rules)} (hinv : CodeOk L P ds H _ inv) (S : SymState v) (to value : Term) :
    Sound (fun _ => True) (encodeAnswer L T P live shs k sh senv j apply inv S to value) := by
  have hL := h.sorted
  unfold encodeAnswer
  refine sound_bind (findE_sound hL (avail_of_got ha.answerΓ) has_find_tuple) fun _ _ => ?_
  refine sound_bind (capturedCodes_sound (P := P) (ds := ds) (H := H) ha.answerΓ _ _) fun σ hσ => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ ha.answer) fun vc hvc => ?_
  refine sound_bind (ha.onAnswer σ hσ) fun _ hoa => ?_
  refine sound_bind (apply_sound hoa ⟨hvc, trivial⟩ (avail_of_got h.events)) fun _ _ => ?_
  refine sound_bind (ensuresTerms_sound hL h.rules ha _ _ _ hvc) fun _ _ => ?_
  refine sound_bind (dataTermE_sound _) fun _ _ => ?_
  refine sound_bind (collD_sound hL (avail_of_got h.events) fun g => ⟨g.2.2, g.2.1⟩) fun _ _ => ?_
  refine sound_bind (encodeEvents_sound h T senv happ _ _ _ _ _ _) fun _ _ => ?_
  exact sound_bind (encodeFinish_sound h T senv happ hinv _ _ _ _) fun _ _ => trivial

end


section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {r e : Ty}

theorem encodeTimers_sound (hL : SortedLayout L) {m : MachineV r e} (h : MachineGot L m)
    {tc : Code (Ty.fn [Ty.timerCtx m.key m.state r] (Ty.option (Ty.timer m.state)))} (htc : CodeOk L P ds H _ tc)
    (tbl records : Term) : Sound (fun _ => True) (encodeTimers L m tc tbl records) := by
  unfold encodeTimers
  refine sound_bind (collD_table_sound hL h) fun _ _ => ?_
  refine sound_bind (sound_mapM _ fun ⟨f, key, st⟩ _ => ?_) fun _ _ => trivial
  simp only [timerSlot]
  refine sound_bind (adtCtor_sound h.tctx _ _) fun _ _ => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ h.tctx) fun cx hcx => ?_
  refine sound_bind (apply_sound htc ⟨hcx, trivial⟩ (avail_of_got h.timer)) fun _ _ => ?_
  exact sound_bind (dataTermE_sound _) fun _ _ => trivial

theorem encodeFire_sound (hL : SortedLayout L) (T : List TypeDecl) {m : MachineV r e} (h : MachineGot L m)
    {fx : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e])))} (hfx : CodeOk L P ds H _ fx)
    (tms : List Term) (tbl done d records now : Term) :
    Sound (fun _ => True) (encodeFire L T m fx tms tbl done d records now) := by
  unfold encodeFire
  refine sound_bind (collD_table_sound hL h) fun _ _ => ?_
  refine sound_bind (findE_sound hL (avail_of_got h.timer) has_find) fun _ _ => ?_
  refine sound_bind (findE_sound hL (avail_of_got h.timerOne) has_find) fun _ _ => ?_
  refine sound_bind (findE_sound hL (avail_of_got h.effect) has_find) fun _ _ => ?_
  refine sound_bind (ordKey_sound T h tt tt) fun _ _ => ?_
  refine sound_bind (sound_mapM _ fun ⟨⟨f, key, entry⟩, tm⟩ _ => ?_) fun _ _ => trivial
  simp only [fireAt]
  refine sound_bind (instCtxT_sound h _ _ _ _) fun _ _ => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ h.ctx) fun nc hnc => ?_
  refine sound_bind (apply_sound hfx ⟨hnc, trivial⟩ (avail_of_got h.effect)) fun _ _ => ?_
  exact sound_bind (dataTermE_sound _) fun _ _ => trivial

theorem timersAll_sound (hL : SortedLayout L) :
    (ms : List (MachineV r e)) → (∀ m ∈ ms, MachineGot L m ∧ MachineCodes L P ds H m) →
    (xs : PerMachine (fun _ => Term) ms) → (records : Term) → Sound (fun _ => True) (timersAll L ms xs records)
  | [], _, .nil, _ => trivial
  | m :: ms, h, .cons x xs, records => by
    have hm := h m (by simp)
    simp only [timersAll]
    refine sound_bind hm.2.timer fun _ htc => ?_
    exact sound_bind (encodeTimers_sound hL hm.1 htc _ _) fun _ _ =>
      sound_bind (timersAll_sound hL ms (fun m' hm' => h m' (by simp [hm'])) xs _) fun _ _ => trivial

theorem encodeFires_sound (hL : SortedLayout L) (T : List TypeDecl) :
    (ms : List (MachineV r e)) → (∀ m ∈ ms, MachineGot L m ∧ MachineCodes L P ds H m) →
    (xs : PerMachine (fun _ => Term) ms) → (tmss : PerMachine (fun _ => List Term) ms) → (done d records now : Term) →
    Sound (fun _ => True) (encodeFires L T ms xs tmss done d records now)
  | [], _, .nil, .nil, _, _, _, _ => trivial
  | m :: ms, h, .cons x xs, .cons tms tmss, done, d, records, now => by
    have hm := h m (by simp)
    simp only [encodeFires]
    refine sound_bind hm.2.effect fun _ hfx => ?_
    exact sound_bind (encodeFire_sound hL T hm.1 hfx _ _ _ _ _ _) fun _ _ =>
      sound_bind (encodeFires_sound hL T ms (fun m' hm' => h m' (by simp [hm'])) xs tmss _ _ _ _) fun _ _ => trivial

theorem dueAll_sound (hL : SortedLayout L) : (ms : List (MachineV r e)) → (∀ m ∈ ms, MachineGot L m) →
    (xs : PerMachine (fun _ => Term) ms) → (tmss : PerMachine (fun _ => List Term) ms) → (now : Term) →
    Sound (fun _ => True) (dueAll L ms xs tmss now)
  | [], _, .nil, .nil, _ => trivial
  | m :: ms, h, .cons x xs, .cons tms tmss, now => by
    have hm := h m (by simp)
    simp only [dueAll]
    refine sound_bind (collD_table_sound hL hm) fun _ _ => ?_
    refine sound_bind (findE_sound hL (avail_of_got hm.timer) has_find) fun _ _ => ?_
    refine sound_bind (findE_sound hL (avail_of_got hm.timerOne) has_find) fun _ _ => ?_
    exact sound_bind (dueAll_sound hL ms (fun m' hm' => h m' (by simp [hm'])) xs tmss now) fun _ _ => trivial

theorem encodeRound_sound (hL : SortedLayout L) (T : List TypeDecl) (ms : List (MachineV r e))
    (h : ∀ m ∈ ms, MachineGot L m ∧ MachineCodes L P ds H m) (xs : PerMachine (fun _ => Term) ms)
    (active records now : Term) : Sound (fun _ => True) (encodeRound L T ms xs active records now) := by
  unfold encodeRound
  exact sound_bind (timersAll_sound hL ms h xs records) fun _ _ =>
    sound_bind (dueAll_sound hL ms (fun m hm => (h m hm).1) xs _ now) fun _ _ =>
    sound_bind (encodeFires_sound hL T ms h xs _ _ _ _ _) fun _ _ => trivial

theorem roundStarts_sound (hL : SortedLayout L) {shs : List (PendingShape e)} (senv : StepEnv L shs)
    (hent : Got L (pendingEntry shs)) : (ms : List (MachineV r e)) →
    (∀ m ∈ ms, Got L (.tuple [m.key]) ∧ OwnersOk L e ds) →
    (sts : PerMachine (fun _ => List StartSlot) ms) → (nid q : Term) →
    Sound (fun _ => True) (roundStarts L shs ds senv ms sts nid q)
  | [], _, .nil, _, _ => trivial
  | m :: ms, h, .cons st sts, nid, q => by
    have hm := h m (by simp)
    simp only [roundStarts]
    refine sound_bind (findE_sound hL (avail_of_got hm.1) has_find_tuple) fun _ _ => ?_
    refine sound_bind (shapeIdxs_sound hm.2) fun _ _ => ?_
    obtain ⟨dflt, hdflt⟩ := defaultE_ok hL hent
    refine sound_bind_ok hdflt ?_
    exact sound_bind (roundStarts_sound hL senv hent ms (fun m' hm' => h m' (by simp [hm'])) sts _ _) fun _ _ =>
      trivial

theorem encodeRounds_sound (hL : SortedLayout L) (T : List TypeDecl) {shs : List (PendingShape e)}
    {ds' : List (String × DeclaredV)}
    (senv : StepEnv L shs) (hent : Got L (pendingEntry shs)) (ms : List (MachineV r e))
    (h : ∀ m ∈ ms, (MachineGot L m ∧ MachineCodes L P ds H m) ∧ Got L (.tuple [m.key]) ∧
      OwnersOk L e ds') (records now : Term) :
    (k : Nat) → (xs : PerMachine (fun _ => Term) ms) → (active nid q : Term) →
    Sound (fun _ => True) (encodeRounds L T shs ds' senv ms records now k xs active nid q)
  | 0, _, _, _, _ => trivial
  | k + 1, xs, active, nid, q => by
    simp only [encodeRounds]
    refine sound_bind (encodeRound_sound hL T ms (fun m hm => (h m hm).1) xs _ _ _) fun _ _ => ?_
    refine sound_bind (roundStarts_sound hL senv hent ms (fun m hm => (h m hm).2) _ _ _) fun _ _ => ?_
    exact sound_bind (encodeRounds_sound hL T senv hent ms h records now k _ _ _ _) fun _ _ => trivial

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {v : ServiceV}
  {live : Option (List SiteId)}

theorem encodeClock_sound {shs : List (PendingShape v.event)} (h : ServiceGot L P ds H v shs) (T : List TypeDecl)
    (senv : StepEnv L shs) {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)} (happ : CodeOk L P ds H _ apply)
    {inv : Code (Ty.fn [v.records] Ty.rules)} (hinv : CodeOk L P ds H _ inv) (S : SymState v) (time : Term) :
    Sound (fun _ => True) (encodeClock L T P live v shs senv apply inv S time) := by
  unfold encodeClock
  refine sound_bind (encodeRounds_sound h.sorted T senv h.entry _ h.machines _ _ _ _ _ _ _) fun _ _ => ?_
  exact sound_bind (encodeFinish_sound h T senv happ hinv _ _ _ _) fun _ _ => trivial

end


section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {v : ServiceV}
  {live : Option (List SiteId)}

/-- The step encoding refuses only for the spec's reasons where the layout has every type the step looks up and the
pending shapes' types and sites. -/
theorem encodeStep_sound (h : ServiceGot L P ds H v (shapes v))
    (hans : ∀ sh ∈ shapes v, AnswerOk L P ds H sh) (T : List TypeDecl) (senv : StepEnv L (shapes v))
    (S : SymState v) (inp : SymInput v (shapes v) senv.nT) :
    Sound (fun _ => True) (encodeStep L T P v senv S inp) := by
  cases inp with
  | command i caller input =>
    have hx := h.commands _ (List.get_mem v.commands i)
    simp only [encodeStep]
    refine sound_bind (commandCode_sound hx) fun _ ⟨h1, h2, h3⟩ => ?_
    refine sound_bind h.apply fun _ happ => sound_bind h.invariants fun _ hinv => ?_
    refine sound_bind sound_need_limit fun _ _ => ?_
    exact sound_bind (encodeCommand_sound h T senv hx h1 h2 h3 happ hinv _ _ _ _) fun _ _ => trivial
  | query i caller input =>
    have hq := h.queries _ (List.get_mem v.queries i)
    simp only [encodeStep]
    refine sound_bind (queryCode_sound hq) fun _ ⟨h1, h2⟩ => ?_
    refine sound_bind sound_need_limit fun _ _ => ?_
    exact sound_bind (encodeQuery_sound h.sorted _ _ h1 h2 (avail_of_got h.origin) hq.input hq.output h.rules hq.ctx
      _ _ _ _) fun _ _ => trivial
  | answer k j to value =>
    simp only [encodeStep]
    refine sound_bind h.apply fun _ happ => sound_bind h.invariants fun _ hinv => ?_
    exact sound_bind (encodeAnswer_sound h T k (hans _ (List.getElem_mem k.2)) senv j happ hinv _ _ _) fun _ _ =>
      trivial
  | unmatched t to value => trivial
  | event i value =>
    simp only [encodeStep]
    refine sound_bind (eventCode_sound h i) fun _ ⟨h1, h2, h3⟩ => ?_
    exact sound_bind (encodeEvent_sound h T senv h1 h2 h3 _ _) fun _ _ => trivial
  | clock time =>
    simp only [encodeStep]
    refine sound_bind h.apply fun _ happ => sound_bind h.invariants fun _ hinv => ?_
    exact sound_bind (encodeClock_sound h T senv happ hinv _ _) fun _ _ => trivial

end


/-! The service's layout has every type the step looks up, and every code it applies has no gap behind it. -/

section
variable (c : CheckedSpec) (v : ServiceV)

theorem avail_use {t : Ty} (ht : t ∈ useTys v (Layout.kindsOf c.program.defs.parts v)) :
    Avail (Layout.ofService c.program.defs v) t := fun hs =>
  ofService_has _ v t (List.mem_filter.2 ⟨List.mem_append_right _ ht, sortable_of_sorted t hs⟩)

theorem avail_stepTy {t : Ty} (ht : t ∈ stepTys v) : Avail (Layout.ofService c.program.defs v) t := fun hs =>
  ofService_has _ v t (List.mem_filter.2 ⟨List.mem_append_left _ (List.mem_append_left _ ht), sortable_of_sorted t hs⟩)

theorem got_of_avail {L : Layout} {t : Ty} (h : Avail L t) (hs : t.sorted = true) : Got L t := ⟨h hs, hs⟩

theorem count_ofService {t : Ty} {x : Nat × Nat} (h : (Layout.ofService c.program.defs v).find? t = some x) :
    x.2 = Layout.effectSlots (listSlots (stepSlots v) c.program.defs.lits) (Layout.kindsOf c.program.defs.parts v) t := by
  have := ofService_count c.program.defs v (t := t) (by simp [h])
  simpa [Layout.count, h] using this

end

theorem sorted_avail_ctx {L : Layout} {r i c : Ty} (h : Avail L (Ty.ctx r i c)) (hr : r.sorted = true)
    (hc : c.sorted = true) : Avail L i := fun hi => by
  have hs : (Ty.ctx r i c).sorted = true := by
    simp [Ty.ctx, Ty.origin, Ty.sorted, Ty.sortedss, Ty.sorteds, hr, hi, hc]
  exact (got_adt ⟨h hs, hs⟩ ⟨0, by simp⟩ i (by simp)).1

theorem sorted_avail_queryCtx {L : Layout} {r i c : Ty} (h : Avail L (Ty.queryCtx r i c)) (hr : r.sorted = true)
    (hc : c.sorted = true) : Avail L i := fun hi => by
  have hs : (Ty.queryCtx r i c).sorted = true := by
    simp [Ty.queryCtx, Ty.origin, Ty.sorted, Ty.sortedss, Ty.sorteds, hr, hi, hc]
  exact (got_adt ⟨h hs, hs⟩ ⟨0, by simp⟩ i (by simp)).1

section
variable {c : CheckedSpec} {v : ServiceV} (hv : v ∈ c.spec.services)
include hv

theorem machineGot_ofService {m : MachineV v.records v.event} (hm : m ∈ v.machines) :
    MachineGot (Layout.ofService c.program.defs v) m := by
  have chk := c.checked v hv
  obtain ⟨⟨her, -⟩, hms, -, -, ⟨hee, -⟩, -⟩ := stateTys_iff.1 chk.stateTys
  have ht := sorted_of_embeddable _ (hms m hm).1
  have hkey : m.key.sorted = true := by simp only [MachineV.table, Ty.sorted, Bool.and_eq_true] at ht; exact ht.1
  have hst : m.state.sorted = true := by
    simp only [MachineV.table, Ty.sorted, Bool.and_eq_true] at ht; exact ht.2
  have hu : ∀ t ∈ [Ty.machineCtx m.key m.state v.records, Ty.next m.state, Ty.option (Ty.timer m.state), .bag m.key,
      Ty.timerCtx m.key m.state v.records],
      t ∈ useTys v (Layout.kindsOf c.program.defs.parts v) := fun t ht => by
    simp only [useTys, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inl (.inl (.inr ⟨m, hm, ht⟩)))))
  refine ⟨got_of_avail (avail_stepTy c v
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (f := (·.table)) hm)))) ht, avail_use c v (hu _ (by simp)),
    avail_use c v (hu _ (by simp)),
    got_of_avail (avail_use c v (hu _ (by simp))) (by simp [Ty.next, Ty.sorted, Ty.sortedss, Ty.sorteds, hst]),
    got_of_avail (avail_use c v (hu _ (by simp)))
      (by simp [Ty.option, Ty.timer, Ty.sorted, Ty.sortedss, Ty.sorteds, hst]),
    got_of_avail (avail_use c v (hu _ (by simp))) (by simp [Ty.sorted, hkey]), (chk.keys m hm).1, ?_,
    avail_stepTy c v (by simp [stepTys]), avail_stepTy c v (by simp [stepTys]),
    got_of_avail (avail_stepTy c v (by simp [stepTys]))
      (by simp [Ty.option, Ty.sorted, Ty.sortedss, Ty.sorteds, sorted_of_embeddable _ hee]),
    got_of_avail (avail_use c v (by simp [useTys])) (by decide)⟩
  intro x y hx hy
  rw [count_ofService c v hx, count_ofService c v hy]
  have hany : v.machines.any (fun m' => (Ty.same m'.table m.table).isSome) = true :=
    List.any_eq_true.2 ⟨m, hm, Ty_same_self _⟩
  have hge : v.bounds.itemsNat ≤ stepSlots v m.table := by
    unfold stepSlots; simp only [hany, ↓reduceIte]; exact Nat.le_max_right _ _
  change stepSlots v (.bag m.key) ≤ stepSlots v m.table
  rw [stepSlots_plain v (by simp)]
  exact hge

end


/-- A request shape of the service's effects has an external in `declared`. -/
theorem kinds_owner {v : ServiceV} {P : List AnySite} {rs : RequestShape v.event}
    (hrs : rs ∈ requestShapesAt v.declared v.event P) : ∃ x, rs.key.owner v.declared = some x := by
  simp only [requestShapesAt, List.mem_flatMap] at hrs
  obtain ⟨⟨x0, d0⟩, hd0, hrs⟩ := hrs
  cases d0 with
  | externalCommand n i o j =>
    simp only [List.mem_filterMap] at hrs
    obtain ⟨⟨aΓ, a⟩, -, hrs⟩ := hrs
    split at hrs
    · obtain rfl := Option.some.inj hrs
      cases hown : (RequestShape.key _ : EffectKey).owner v.declared with
      | none =>
        unfold EffectKey.owner at hown
        rw [Option.map_eq_none_iff, List.find?_eq_none] at hown
        exact absurd (hown _ hd0) (by simp [RequestShape.key, Ty_same_self])
      | some x1 => exact ⟨x1, rfl⟩
    · cases hrs
  | externalQuery n i o f =>
    obtain ⟨s1, -, hrs⟩ := List.mem_flatMap.1 hrs
    obtain ⟨⟨aΓ, a⟩, -, hrs⟩ := List.mem_filterMap.1 hrs
    split at hrs
    · obtain rfl := Option.some.inj hrs
      cases hown : (RequestShape.key _ : EffectKey).owner v.declared with
      | none =>
        unfold EffectKey.owner at hown
        rw [Option.map_eq_none_iff, List.find?_eq_none] at hown
        exact absurd (hown _ hd0) (by simp [RequestShape.key, Ty_same_self])
      | some x1 => exact ⟨x1, rfl⟩
    · cases hrs
  | command _ _ _ _ | query _ _ _ | source _ _ => simp at hrs

theorem ownersOk_ofService (c : CheckedSpec) (v : ServiceV) :
    OwnersOk (Layout.ofService c.program.defs v) v.event v.declared := by
  intro key hk
  simp only [Layout.effectsOf, List.mem_filter] at hk
  obtain ⟨hk, hev⟩ := hk
  rw [(allSorted_ofParts _ v).2.1] at hk
  simp only [Layout.kindsOf] at hk
  rw [mem_dedupBy effectKey_same_iff, List.mem_filter] at hk
  obtain ⟨e, -, hk⟩ := List.mem_flatMap.1 hk.1
  obtain ⟨rs, hrs, rfl⟩ := List.mem_map.1 hk
  obtain rfl : e = v.event := eq_of_same hev
  exact kinds_owner hrs


theorem ownCommand_mem {v : ServiceV} {n : String} {i j : Ty} {x : CommandV v.records v.event v.caller}
    {h : i = x.input ∧ j = x.rejection} (hx : Step.ownCommand (v := v) n i j = some ⟨x, h⟩) : x ∈ v.commands := by
  obtain ⟨y, hy, hf⟩ := List.exists_of_findSome?_eq_some hx
  split at hf
  · split at hf
    · cases hf; exact hy
    · cases hf
  · cases hf

theorem ownShape_command {v : ServiceV} {P : List AnySite} {key : OwnKey} {x : CommandV v.records v.event v.caller}
    {Γ : List Ty} {site : Site Γ (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))}
    (h : ownShape v P key = some (.command x Γ site)) :
    x ∈ v.commands ∧ (⟨Γ, _, site⟩ : AnySite) ∈ P ∧
      ∃ e n c i a, key = .command e n c i x.rejection a ∧ Γ = a.Γ ∧ site.site = a.site := by
  cases key with
  | command e n c i j a =>
    unfold ownShape at h
    dsimp only at h
    revert h
    generalize hoc : Ty.same c v.caller = oc
    generalize hox : Step.ownCommand (v := v) n i j = ox
    intro h
    cases oc with
    | none => cases ox <;> (dsimp only at h; cases h)
    | some hc =>
      cases ox with
      | none => dsimp only at h; cases h
      | some xx =>
        obtain ⟨x', hi, hj⟩ := xx
        dsimp only at h
        revert h
        generalize hsf : siteFor P _ a = sf
        intro h
        cases sf with
        | none => dsimp only at h; cases h
        | some gs =>
          obtain ⟨Γ', s'⟩ := gs
          cases h
          obtain ⟨hm, hsite, hΓ⟩ := siteFor_spec hsf
          exact ⟨ownCommand_mem hox, hm, e, n, c, i, a, by rw [hj], hΓ, hsite⟩
  | query e n c i o a =>
    unfold ownShape at h
    dsimp only at h
    revert h
    generalize Ty.same c v.caller = oc
    generalize Step.ownQuery (v := v) n i o = ox
    intro h
    cases oc with
    | none => cases ox <;> (dsimp only at h; cases h)
    | some hc =>
      cases ox with
      | none => dsimp only at h; cases h
      | some xx =>
        dsimp only at h
        revert h
        generalize siteFor P _ a = sf
        intro h
        cases sf <;> (dsimp only at h; cases h)

theorem ownShape_query {v : ServiceV} {P : List AnySite} {key : OwnKey} {x : QueryV v.records v.caller}
    {Γ : List Ty} {site : Site Γ (Ty.fn [x.output] (.list v.event))} (h : ownShape v P key = some (.query x Γ site)) :
    x ∈ v.queries ∧ (⟨Γ, _, site⟩ : AnySite) ∈ P ∧
      ∃ e n c i o a, key = .query e n c i o a ∧ Γ = a.Γ ∧ site.site = a.site := by
  cases key with
  | query e n c i o a =>
    unfold ownShape at h
    dsimp only at h
    revert h
    generalize hoc : Ty.same c v.caller = oc
    generalize hox : Step.ownQuery (v := v) n i o = ox
    intro h
    cases oc with
    | none => cases ox <;> (dsimp only at h; cases h)
    | some hc =>
      cases ox with
      | none => dsimp only at h; cases h
      | some xx =>
        obtain ⟨x', hi, ho⟩ := xx
        dsimp only at h
        revert h
        generalize hsf : siteFor P _ a = sf
        intro h
        cases sf with
        | none => dsimp only at h; cases h
        | some gs =>
          obtain ⟨Γ', s'⟩ := gs
          cases h
          obtain ⟨hm, hsite, hΓ⟩ := siteFor_spec hsf
          exact ⟨ownQuery_mem hox, hm, e, n, c, i, o, a, rfl, hΓ, hsite⟩
  | command e n c i j a =>
    unfold ownShape at h
    dsimp only at h
    revert h
    generalize Ty.same c v.caller = oc
    generalize Step.ownCommand (v := v) n i j = ox
    intro h
    cases oc with
    | none => cases ox <;> (dsimp only at h; cases h)
    | some hc =>
      cases ox with
      | none => dsimp only at h; cases h
      | some xx =>
        dsimp only at h
        revert h
        generalize siteFor P _ a = sf
        intro h
        cases sf <;> (dsimp only at h; cases h)


section
variable {c : CheckedSpec} {v : ServiceV} (hv : v ∈ c.spec.services)
include hv

theorem commandOk_ofService {x : CommandV v.records v.event v.caller} (hx : x ∈ v.commands) :
    CommandOk (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles v x := by
  have chk := c.checked v hv
  obtain ⟨⟨her, -⟩, -, -, -, -, ⟨hec, -⟩⟩ := stateTys_iff.1 chk.stateTys
  have hu : ∀ t ∈ [Ty.ctx v.records x.input v.caller, Ty.result (.list v.event) x.rejection, x.input],
      t ∈ useTys v (Layout.kindsOf c.program.defs.parts v) := fun t ht => by
    simp only [useTys, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inl (.inr ⟨x, hx, ht⟩))))
  have hr := chk.reach.commands x hx
  have hx' := root_command hx
  exact ⟨Fun.code_ofService c hv _ hr.accepts hx'.1, Fun.code_ofService c hv _ hr.decide hx'.2.1,
    Fun.code_ofService c hv _ hr.ensures hx'.2.2,
    sorted_avail_ctx (avail_use c v (hu _ (by simp))) (sorted_of_embeddable _ her) (sorted_of_embeddable _ hec),
    avail_use c v (hu _ (by simp)), avail_use c v (hu _ (by simp))⟩

theorem queryOk_ofService {q : QueryV v.records v.caller} (hq : q ∈ v.queries) :
    QueryOk (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles v q := by
  have chk := c.checked v hv
  obtain ⟨⟨her, -⟩, -, -, -, -, ⟨hec, -⟩⟩ := stateTys_iff.1 chk.stateTys
  have hu : ∀ t ∈ [Ty.queryCtx v.records q.input v.caller, q.output, q.input],
      t ∈ useTys v (Layout.kindsOf c.program.defs.parts v) := fun t ht => by
    simp only [useTys, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inr ⟨q, hq, ht⟩)))
  have hr := chk.reach.queries q hq
  have hq' := root_query hq
  exact ⟨Fun.code_ofService c hv _ hr.accepts hq'.1, Fun.code_ofService c hv _ hr.resolve hq'.2,
    sorted_avail_queryCtx (avail_use c v (hu _ (by simp))) (sorted_of_embeddable _ her) (sorted_of_embeddable _ hec),
    avail_use c v (hu _ (by simp)), avail_use c v (hu _ (by simp))⟩

theorem Fun.uses_sub {t : Ty} {f : Fun t} (hf : f.asSite ∈ c.P) : ∀ s ∈ f.uses.1, s ∈ c.P := by
  have h := sites_ofService c hv _ hf
  exact (usesOk_of_defsOk h.2.2.2.2 h.2.2.1 h.2.2.2.1).2.1

theorem EffectFun.uses_sub {ps : List Ty} {r : Ty} {f : EffectFun ps r} (hf : f.asSite ∈ c.E) :
    ∀ s ∈ f.uses.1, s ∈ c.P := by
  have h := effectSiteOk_of c.program.defs
    ⟨fun u hu hs => ofService_has c.program.defs v u
      (List.mem_filter.2 ⟨List.mem_append_left _ (List.mem_append_right _ hu), sortable_of_sorted u hs⟩), fun _ h => h,
      fun h hm => handleOk_of_named hv hm (c.handles h hm)⟩ _ hf
  exact (usesOk_of_defsOk h.2.2.2.2 h.2.2.1 h.2.2.2.1).2.1

/-- What the step's and the response goals' functions use is the program's. -/
theorem rootUses_sub : ∀ r ∈ rootUses v, ∀ s ∈ r.1, s ∈ c.P := by
  have chk := c.checked v hv
  intro r hr
  simp only [rootUses, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map, List.not_mem_nil, or_false,
    or_assoc] at hr
  rcases hr with rfl | rfl | ⟨x, hx, rfl | rfl | rfl⟩ | ⟨q, hq, rfl | rfl⟩ | ⟨m, hm, rfl | rfl | rfl | rfl | rfl⟩ |
    ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl | rfl | rfl⟩ | ⟨x, hx, rfl⟩
  · exact Fun.uses_sub hv chk.reach.apply
  · exact Fun.uses_sub hv chk.reach.invariants
  · exact Fun.uses_sub hv (chk.reach.commands x hx).accepts
  · exact Fun.uses_sub hv (chk.reach.commands x hx).decide
  · exact Fun.uses_sub hv (chk.reach.commands x hx).ensures
  · exact Fun.uses_sub hv (chk.reach.queries q hq).accepts
  · exact Fun.uses_sub hv (chk.reach.queries q hq).resolve
  · exact Fun.uses_sub hv (chk.reach.machines m hm).instances
  · exact Fun.uses_sub hv (chk.reach.machines m hm).on
  · exact Fun.uses_sub hv (chk.reach.machines m hm).timer
  · exact Fun.uses_sub hv (chk.reach.machines m hm).invariants
  · exact EffectFun.uses_sub hv (chk.reach.machines m hm).effect.site
  · exact EffectFun.uses_sub hv (chk.reach.reactions x hx).site
  · exact Fun.uses_sub hv (chk.reach.subscribes x hx)
  · exact Fun.uses_sub hv (chk.reach.responses x hx).1
  · exact Fun.uses_sub hv (chk.reach.responses x hx).2.1
  · exact Fun.uses_sub hv (chk.reach.responses x hx).2.2
  · exact Fun.uses_sub hv (chk.reach.creates x hx)

/-- A site of the program at an own kind's `on_answer` is one a function of the step uses: the kind pairs a handle with
a site that function uses, and the program's sites are unique. -/
theorem own_root {key : OwnKey} (hk : key ∈ (Layout.kindsOf c.program.defs.parts v).owns) {Γ : List Ty} {t : Ty}
    {site : Site Γ t} (hm : (⟨Γ, t, site⟩ : AnySite) ∈ c.P) (hsite : site.site = key.answer.site) :
    ∃ r ∈ rootUses v, (⟨Γ, t, site⟩ : AnySite) ∈ r.1 := by
  have chk := c.checked v hv
  simp only [Layout.kindsOf] at hk
  rw [mem_dedupBy ownKey_same_iff, List.mem_filter] at hk
  obtain ⟨r, hr, hk⟩ := List.mem_flatMap.1 hk.1
  obtain ⟨w, -, hk⟩ := List.mem_flatMap.1 hk
  obtain ⟨h, -, hk⟩ := List.mem_flatMap.1 hk
  refine ⟨r, hr, ?_⟩
  have hfin : ∀ {u : Ty} {s' : (Γ : List Ty) × Site Γ u}, s' ∈ sitesOf (w.sitesIn r.1) u →
      s'.2.site = key.answer.site → (⟨Γ, t, site⟩ : AnySite) ∈ r.1 := by
    intro u s' hs' he
    have hs'm := mem_sitesOf (sitesOf_mono (fun _ h => sitesIn_sub h) hs')
    rw [site_eq chk.sites hm (rootUses_sub hv r hr _ hs'm) (hsite.trans he.symm)]
    exact hs'm
  unfold ownKeys at hk
  split at hk
  · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hk
    exact hfin hs' rfl
  · obtain ⟨_, -, hk⟩ := List.mem_flatMap.1 hk
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hk
    exact hfin hs' rfl
  · cases hk

/-- Every own kind of a checked service's layout names a command or query the service lists: the kinds come from the
handles its sends can name, which check's unknownHandle rule compares with what it lists. -/
theorem ownShape_some {key : OwnKey} (hk : key ∈ (Layout.kindsOf c.program.defs.parts v).owns) (P : List AnySite) :
    ownShape v P key ≠ none := by
  have chk := c.checked v hv
  simp only [Layout.kindsOf] at hk
  rw [mem_dedupBy ownKey_same_iff, List.mem_filter] at hk
  obtain ⟨r, hr, hk⟩ := List.mem_flatMap.1 hk.1
  obtain ⟨w, hw, hk⟩ := List.mem_flatMap.1 hk
  obtain ⟨h, hh, hk⟩ := List.mem_flatMap.1 hk
  have hl := chk.sends h (List.mem_flatMap.2 ⟨r, hr, List.mem_flatMap.2 ⟨w, hw, hh⟩⟩)
  unfold ownKeys at hk
  split at hk
  · rename_i n e cc i j hkind hname htys
    obtain ⟨s', -, rfl⟩ := List.mem_map.1 hk
    simp only [ServiceV.lists, hname, hkind, htys, Bool.and_eq_true] at hl
    obtain ⟨⟨hc⟩, ec⟩ := Option.isSome_iff_exists.1 hl.1
    obtain ⟨⟨x, hx⟩, ex⟩ := Option.isSome_iff_exists.1 (ownCommand_isSome hl.2)
    unfold ownShape
    simp only [ec, ex]
    split <;> simp
  · rename_i n cc i o hkind hname htys
    obtain ⟨e, -, hk⟩ := List.mem_flatMap.1 hk
    obtain ⟨s', -, rfl⟩ := List.mem_map.1 hk
    simp only [ServiceV.lists, hname, hkind, htys, Bool.and_eq_true] at hl
    obtain ⟨⟨hc⟩, ec⟩ := Option.isSome_iff_exists.1 hl.1
    obtain ⟨⟨x, hx⟩, ex⟩ := Option.isSome_iff_exists.1 (ownQuery_isSome hl.2)
    unfold ownShape
    simp only [ec, ex]
    split <;> simp
  · cases hk

theorem ownOk_ofService {key : OwnKey} (hk : key ∈ (Layout.ofService c.program.defs v).ownsOf v.event) :
    OwnOk (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles v key := by
  have hkK : key ∈ (Layout.kindsOf c.program.defs.parts v).owns := by
    rw [← (allSorted_ofParts _ v).2.2]; exact (List.mem_filter.1 hk).1
  have hf := ((kindsOf_fields _ v).2 key hkK).1
  have hu : ∀ t ∈ (match key with
      | .command _ _ _ _ j a => [Ty.nil, Ty.result Ty.nil j, .tuple a.Γ]
      | .query _ _ _ _ _ a => [.tuple a.Γ]), t ∈ useTys v (Layout.kindsOf c.program.defs.parts v) := fun t ht => by
    simp only [useTys, List.mem_append, List.mem_flatMap]
    exact .inr ⟨key, hkK, ht⟩
  unfold OwnOk
  split
  · rename_i x Γ site hsh
    obtain ⟨hx, hm, e, n, cc, i, a, rfl, rfl, hsite⟩ := ownShape_command hsh
    simp only [OwnKey.fields, Ty.sorteds, Bool.and_eq_true] at hf
    exact ⟨commandOk_ofService hv hx, got_of_avail (avail_use c v (hu _ (by simp))) (by simpa [Ty.sorted] using hf.2.1),
      Site.code_ofService c hv _ hm (own_root hv hkK hm hsite), avail_use c v (hu _ (by simp)),
      avail_use c v (hu _ (by simp))⟩
  · rename_i x Γ site hsh
    obtain ⟨hx, hm, e, n, cc, i, o, a, rfl, rfl, hsite⟩ := ownShape_query hsh
    simp only [OwnKey.fields, Ty.sorteds, Bool.and_eq_true] at hf
    exact ⟨queryOk_ofService hv hx, got_of_avail (avail_use c v (hu _ (by simp))) (by simpa [Ty.sorted] using hf.2.1),
      Site.code_ofService c hv _ hm (own_root hv hkK hm hsite)⟩
  · trivial
  · rename_i hsh
    exact ownShape_some hv hkK _ hsh

omit hv in
/-- A pending request's `on_answer` and `ensures` sites are ones its sender's effect function uses. -/
theorem shapes_root {sh : PendingShape v.event} (hsh : sh ∈ shapes v) :
    ∃ r ∈ rootUses v, sh.InSites r.1 := by
  obtain ⟨⟨ks, snd, S⟩, hS, hin⟩ := shapes_inSender hsh
  simp only [senderShapes, List.mem_append, List.mem_map] at hS
  rcases hS with ⟨m, hm, he⟩ | ⟨x, hx, he⟩ <;> cases he
  · exact ⟨_, (root_machine hm).2.2.2.2, hin⟩
  · exact ⟨_, root_reaction hx, hin⟩

theorem entry_ofService : Got (Layout.ofService c.program.defs v) (pendingEntry (shapes v)) := by
  have chk := c.checked v hv
  obtain ⟨-, -, hep, -, -, -⟩ := stateTys_iff.1 chk.stateTys
  exact (got_table (got_of_avail (avail_stepTy c v (t := pendingTable (shapes v)) (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))
    (sorted_of_embeddable _ (embeddable_pending hep)))).2.1

theorem answerOk_ofService {sh : PendingShape v.event} (hsh : sh ∈ shapes v) :
    AnswerOk (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles sh := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hsh
  have hf := got_adt (entry_ofService hv) ⟨k, by simpa using hk⟩
  simp only [List.get_eq_getElem, List.getElem_map, PendingShape.fields, RequestShape.fields] at hf
  have hin := shapes_inSites (c.checked v hv).reach hsh
  obtain ⟨r, hr, hr1⟩ := shapes_root hsh
  exact ⟨hf _ (by simp), hf _ (by simp), avail_of_got (hf _ (by simp)),
    avail_use c v (by simp only [useTys, List.mem_append, List.mem_map]; exact .inl (.inr ⟨_, hsh, rfl⟩)),
    Site.code_ofService c hv _ hin.1 ⟨r, hr, hr1.1⟩,
    fun s hs => Site.code_ofService c hv _ (hin.2 s hs) ⟨r, hr, hr1.2 s hs⟩⟩

theorem serviceGot_ofService :
    ServiceGot (Layout.ofService c.program.defs v) c.P v.declared c.program.defs.handles v (shapes v) := by
  have chk := c.checked v hv
  obtain ⟨⟨her, -⟩, hms, hep, -, ⟨hee, -⟩, ⟨hec, -⟩⟩ := stateTys_iff.1 chk.stateTys
  have hev := sorted_of_embeddable _ hee
  refine ⟨sorted_ofParts _ v, got_of_avail (avail_stepTy c v (by simp [stepTys])) (sorted_of_embeddable _ her),
    got_of_avail (avail_stepTy c v (by simp [stepTys])) hev,
    got_of_avail (avail_stepTy c v (by simp [stepTys])) (sorted_of_embeddable _ hec),
    got_of_avail (avail_stepTy c v (by simp [stepTys]))
      (by simp [Ty.origin, Ty.sorted, Ty.sortedss, Ty.sorteds, sorted_of_embeddable _ hec]),
    got_of_avail (avail_use c v (by simp [useTys])) (by decide),
    got_of_avail (avail_use c v (by simp [useTys])) (by simpa [Ty.sorted] using hev),
    got_of_avail (avail_stepTy c v (by simp [stepTys])) rfl,
    got_of_avail (avail_stepTy c v (t := pendingTable (shapes v)) (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))
      (sorted_of_embeddable _ (embeddable_pending hep)),
    Fun.code_ofService c hv _ chk.reach.apply root_apply, avail_use c v (by simp [useTys]),
    Fun.code_ofService c hv _ chk.reach.invariants root_invariants,
    fun m hm => ?_, fun x hx => ?_, fun x hx => commandOk_ofService hv hx, fun q hq => queryOk_ofService hv hq,
    fun i => ?_, fun key hk => ownOk_ofService hv hk⟩
  · have hr := chk.reach.machines m hm
    have hkey : m.key.sorted = true := by
      have ht := sorted_of_embeddable _ (hms m hm).1
      simp only [MachineV.table, Ty.sorted, Bool.and_eq_true] at ht; exact ht.1
    have hm' := root_machine hm
    refine ⟨⟨machineGot_ofService hv hm, Fun.code_ofService c hv _ hr.instances hm'.1,
      Fun.code_ofService c hv _ hr.on hm'.2.1, Fun.code_ofService c hv _ hr.timer hm'.2.2.1,
      EffectFun.code_ofService c hv _ hr.effect.site hm'.2.2.2.2 rfl, Fun.code_ofService c hv _ hr.invariants hm'.2.2.2.1⟩,
      got_of_avail (avail_stepTy c v (List.mem_append_right _ (List.mem_map_of_mem (f := fun m => Ty.tuple [m.key]) hm)))
        (by simp [Ty.sorted, Ty.sorteds, hkey]), ?_⟩
    exact ownersOk_ofService c v
  · have hu : ∀ t ∈ [Ty.reactionCtx v.records, .list (.dsl .effect [v.event])],
        t ∈ useTys v (Layout.kindsOf c.program.defs.parts v) := fun t ht => by
      simp only [useTys, List.mem_append, List.mem_flatMap]
      exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨x, hx, ht⟩))))))
    exact ⟨EffectFun.code_ofService c hv _ (chk.reach.reactions x hx).site (root_reaction hx)
      (by simp [Ty.phFree, Ty.phFrees, phFree_of_data _ v.event_data, Ty.reactionCtx]),
      ownersOk_ofService c v,
      avail_use c v (hu _ (by simp)), got_of_avail (avail_use c v (hu _ (by simp))) (by simpa [Ty.sorted] using hev)⟩
  · exact ⟨avail_use c v (by simp only [useTys, List.mem_append, List.mem_map]; exact .inl (.inl (.inr ⟨_, List.get_mem _ i, rfl⟩))),
      Fun.code_ofService c hv _ (chk.reach.subscribes _ (List.get_mem _ i)) (root_subscribe (List.get_mem _ i))⟩

/-- In each service's layout, built from a checked spec's program, the step encoding never refuses with a layout gap:
every refusal is the spec's (a limit, a string outside SMT-LIB's, a case the types rule out). -/
theorem encodeStep_ofService (T : List TypeDecl) (senv : StepEnv (Layout.ofService c.program.defs v) (shapes v))
    (S : SymState v) (inp : SymInput v (shapes v) senv.nT) :
    Sound (fun _ => True) (encodeStep (Layout.ofService c.program.defs v) T c.P v senv S inp) :=
  encodeStep_sound (serviceGot_ofService hv) (fun _ hsh => answerOk_ofService hv hsh) T senv S inp

end

end Tazuna.Smt
