import Tazuna.Smt.EventStep
import Tazuna.Smt.ReactExact
import Tazuna.Semantics.Fire

/-! One round of timer firing on a machine's instance table. Each slot is encoded alone (`Step.fireFirst_eq`): it
fires where no earlier machine fired, its timer has the round's deadline, and no slot with that deadline has a smaller
key, by the order terms. A slot that fires holds the instance entering its timer's state, with the timer `after` asks
for there. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {M : Model} {r e : Ty}

/-- The terms an entry's timer is read by: whether it has the deadline `d`, and the state it enters. -/
def hitT (dent dp : Nat) (tm d : Term) : Term := .and (.is dent 0 tm) (.eq (.sel dp 0 0 (.sel dent 0 0 tm)) d)
def targetT (dent dp : Nat) (tm : Term) : Term := .sel dp 0 1 (.sel dent 0 0 tm)

theorem timer_terms (m : MachineV r e) {dent n dp np : Nat}
    (hdent : L.find? (Ty.option (.tuple [.int, m.state])) = some (dent, n)) (hdp : L.find? (.tuple [.int, m.state]) = some (dp, np))
    (i : Step.Instance m) {tm d : Term} {dv : Int} (hd : d.denote M = .int dv)
    (ht : RelV L _ (Ty.up _ m.timer_data (timerVal i.timer)) (tm.denote M)) :
    (hitT dent dp tm d).denote M = .bool (Step.hitsAt dv i) ∧
      ∀ dl tg, i.timer = some (dl, tg) → RelV L m.state (Ty.up _ m.state_data tg) ((targetT dent dp tm).denote M) := by
  have hs := m.state_data
  have hent1 : (Ty.tuple [.tuple [.int, m.state]]).isData = true := by simp [Ty.isData, Ty.isDatas, hs]
  have hpair : (Ty.tuple [.int, m.state]).isData = true := by simp [Ty.isData, Ty.isDatas, hs]
  have hnone' : (Ty.adt 3 [.tuple [.int, m.state]] [[]]).isData = true := by simp [Ty.isData, Ty.isDatass, Ty.isDatas]
  obtain ⟨d', n', hf', hra⟩ := ht
  obtain rfl := find_det hf' hdent
  obtain ⟨k, st, t⟩ := i
  cases t with
  | some p =>
    obtain ⟨dl, tg⟩ := p
    change RelAlts L d' 0 _ (Ty.up _ m.timer_data (.inl ((dl, tg, ()), ()))) _ at hra
    erw [Ty.up_inl 3 _ [.tuple [.int, m.state]] [[]] m.timer_data hent1] at hra
    obtain ⟨vals, hv, hvals⟩ := hra
    erw [Ty.up_tuple _ _ _ hpair rfl] at hvals
    obtain ⟨v0, _, rfl, ⟨dp', np', vals7, hf7, hv7, hvals7⟩, rfl⟩ := hvals
    obtain rfl := find_det hf7 hdp
    erw [Ty.up_tuple _ _ _ rfl (by simp [Ty.isData, Ty.isDatas, hs])] at hvals7
    obtain ⟨vd, vs7, rfl, hvd, hvals7⟩ := hvals7
    erw [Ty.up_tuple _ _ _ hs rfl] at hvals7
    obtain ⟨vt, _, rfl, hvt, rfl⟩ := hvals7
    change vd = .int dl at hvd
    subst hvd
    refine ⟨?_, fun dl' tg' h => ?_⟩
    · simp only [hitT, Term.denote, hv, hv7, hd, Val.toBool, Step.hitsAt]
      by_cases h : dl = dv <;> simp [h, BEq.beq, Val.beq]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa [targetT, Term.denote, hv, hv7] using hvt
  | none =>
    change RelAlts L d' 0 _ (Ty.up _ m.timer_data (.inr (.inl ()))) _ at hra
    erw [Ty.up_inr 3 _ [.tuple [.int, m.state]] [[]] m.timer_data hnone', Ty.up_inl 3 _ [] [] hnone' rfl] at hra
    obtain ⟨vals, hv, -⟩ := hra
    exact ⟨by simp [hitT, Term.denote, hv, Val.toBool, Step.hitsAt], fun _ _ h => nomatch h⟩

end

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- The order term `x ≤ y` on keys, true where the key type has none (`encodeFire` refuses those). -/
def leT (t : Ty) (x y : Term) : Term :=
  match ordT L T t x y with
  | some (_, le) => le
  | none => tt

/-- Per slot of a table: whether its timer has the deadline `d`. -/
def hitsT (de dent dp : Nat) (So : List Slot) (d : Term) : List Term :=
  So.map fun (_, xs) => hitT dent dp (.sel de 0 1 (xs.getD 1 tt)) d

/-- One slot's part of a firing round: its new entry, the effect option it starts, and the condition of `after` and
`effect` where the slot fires. It fires where no earlier machine fired (`done`), its timer has the deadline `d`, and
every slot with that deadline has a key no smaller. -/
def fireAt (m : MachineV r e) (after : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (Ty.timer m.state))))
    (fx : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e]))))
    (de dent dp : Nat) (So : List Slot) (done d records now noneT : Term) : Slot → Except Refusal (Term × Term × Term)
  | (_, xs) => do
    let key := xs.headD tt
    let tm := Term.sel de 0 1 (xs.getD 1 tt)
    let les := So.map fun (_, ys) => Term.or (.not (hitT dent dp (.sel de 0 1 (ys.getD 1 tt)) d)) (leT L T m.key key (ys.headD tt))
    let fires := Term.share (.and (.not done) (.and (hitT dent dp tm d) (allSlotT So les)))
    let tg := targetT dent dp tm
    let nctx ← need "a context that has no term" (Code.ofTerm? _ (← instCtxT L m key tg records now))
    let (a, c) ← after (nctx, ())
    let at_ ← need "a timer that has no term" (Code.term? _ a)
    let (x, cx) ← fx (nctx, ())
    let xt ← need "an effect that has no term" (Code.term? _ x)
    pure (.ite fires (.ctor de 0 [tg, ← timerT L m now at_]) (xs.getD 1 tt), .ite fires xt noneT, .ite fires (andT c cx) tt)

/-- What a firing round encodes on one machine: the new instance table, whether some slot has the deadline, and per
slot its flag, key and the effect option it starts. -/
structure FireOut where
  table : Term
  hit : Term
  starts : List (Term × Term × Term)

/-- One firing round on the instance table `tbl` (`Step.fireFirst`), unless `done`, at the deadline `d`, with its
condition. Refused when the key type has no order terms. -/
def encodeFire (m : MachineV r e) (after : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (Ty.timer m.state))))
    (fx : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e]))))
    (tbl done d records now : Term) : Except Refusal (FireOut × Term) := do
  let (dd, n, dt) ← collD L m.table [m.key, instEntry m.state]
  let de ← tupleD L [m.state, Ty.option (.tuple [.int, m.state])]
  let (dent, _) ← need "a layout without the entry's timer" (L.find? (Ty.option (.tuple [.int, m.state])))
  let dp ← tupleD L [.int, m.state]
  let (dopt, _) ← need "a layout without the effect option" (L.find? (Ty.option (.dsl .effect [e])))
  let _ ← need "a key type without order terms" (ordT L T m.key tt tt)
  let So := slotsOf dd dt n 2 tbl
  let outs ← So.mapM (fireAt L T m after fx de dent dp So done d records now (.ctor dopt 1 []))
  pure (⟨slotsTerm dd dt (mapSlots (fun xs q => [xs.headD tt, q]) So (outs.map (·.1))), anySlotT So (hitsT de dent dp So d),
      List.zipWith (fun (f, xs) q => (f, xs.headD tt, q)) So (outs.map (·.2.1))⟩,
    guardsT So (outs.map (·.2.2)))

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- The instance a table entry's values code. -/
def instOfD (m : MachineV r e) (y : m.key.den × (instEntry m.state).den) : Step.Instance m :=
  instOf m (Ty.down _ m.key_data y.1) (Ty.down _ m.entry_data y.2)

theorem instancesOf_perm (m : MachineV r e) (tbl : m.table.den0) {ys : List (m.key.den × (instEntry m.state).den)}
    (hp : ys.Perm (Ty.up _ m.table_data tbl).1) : (ys.map (instOfD m)).Perm (instancesOf T m tbl) := by
  have hup : (Ty.up _ m.table_data tbl).1 = tbl.1.map fun p => (Ty.up _ m.key_data p.1, Ty.up _ m.entry_data p.2) :=
    Ty.up_table m.key (instEntry m.state) m.table_data m.key_data m.entry_data tbl
  rw [hup] at hp
  refine ((hp.map (instOfD m)).trans ?_).trans (List.mergeSort_perm _ _).symm
  rw [List.map_map]
  exact .of_eq (List.map_congr_left fun p _ => by simp [instOfD, Ty.down_up])

theorem instancesOf_ok (m : MachineV r e) (tbl : m.table.den0) : InstancesOk T m (instancesOf T m tbl) := by
  refine ⟨?_, ?_⟩
  · have trans : ∀ a b c : Step.Instance m, keyLE T m a b = true → keyLE T m b c = true → keyLE T m a c = true :=
      fun _ _ _ h1 h2 => Std.TransCmp.isLE_trans (cmp := Ty.cmp T m.key) h1 h2
    have total : ∀ a b : Step.Instance m, (keyLE T m a b || keyLE T m b a) = true := by
      intro a b
      simp only [keyLE]
      rw [Std.OrientedCmp.eq_swap (cmp := Ty.cmp T m.key) (a := a.key) (b := b.key)]
      cases Ty.cmp T m.key b.key a.key <;> rfl
    exact List.pairwise_mergeSort trans total _
  · have hp : (instEntries m (instancesOf T m tbl)).Perm tbl.1 := by
      unfold instEntries instancesOf
      refine ((List.mergeSort_perm _ _).map _).trans (.of_eq ?_)
      rw [List.map_map]
      conv => rhs; rw [← List.map_id tbl.1]
      exact List.map_congr_left fun ⟨k, x0, x1, ()⟩ _ => by simp [instOf, val_timerOf]
    exact (hp.pairwise_iff fun h => ⟨h.2, h.1⟩).2 tbl.2

theorem instancesOk_map (m : MachineV r e) {l : List (Step.Instance m)} (h : InstancesOk T m l)
    (F : Step.Instance m → Step.Instance m) (hF : ∀ i, (F i).key = i.key) : InstancesOk T m (l.map F) := by
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_map]; exact h.1.imp fun {a b} hab => by simpa [keyLE, hF] using hab
  · have := h.2
    unfold KeysUnique instEntries at this ⊢
    simp only [List.map_map, List.pairwise_map] at this ⊢
    exact this.imp fun {a b} hab => by simpa [hF] using hab

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- What a slot's terms read of the table entry it holds: the key, whether the timer has the deadline, the entry, and
the state the timer enters. -/
theorem fire_item (m : MachineV r e) {de nde dent nent dp np : Nat} (hde : L.find? (instEntry m.state) = some (de, nde))
    (hdent : L.find? (Ty.option (.tuple [.int, m.state])) = some (dent, nent)) (hdp : L.find? (.tuple [.int, m.state]) = some (dp, np))
    {d : Term} {dv : Int} (hd : d.denote M = .int dv) (y : m.key.den × (instEntry m.state).den) (xs : List Term)
    (h : ETab L m.key (instEntry m.state) y (Term.denotes M xs)) :
    RelV L m.key (Ty.up _ m.key_data (instOfD m y).key) ((xs.headD tt).denote M) ∧
      (hitT dent dp (.sel de 0 1 (xs.getD 1 tt)) d).denote M = .bool (Step.hitsAt dv (instOfD m y)) ∧
      RelV L (instEntry m.state) (Ty.up _ m.entry_data (entryOf (instOfD m y))) ((xs.getD 1 tt).denote M) ∧
      ∀ dl tg, (instOfD m y).timer = some (dl, tg) →
        RelV L m.state (Ty.up _ m.state_data tg) ((targetT dent dp (.sel de 0 1 (xs.getD 1 tt))).denote M) := by
  obtain ⟨zk, zv, hvs, hk, hv⟩ := h
  obtain ⟨xk, xe, rfl, hxk, hxe⟩ := pair_terms hvs
  have hku : Ty.up _ m.key_data (instOfD m y).key = y.1 := Ty.up_down _ _ _
  have hy2 : Ty.up _ m.entry_data (Ty.down _ m.entry_data y.2) = y.2 := Ty.up_down _ _ _
  generalize hz : Ty.down _ m.entry_data y.2 = z at hy2
  obtain ⟨st, t, u⟩ := z
  cases u
  have hinst : instOfD m y = ⟨Ty.down _ m.key_data y.1, st, timerOf t⟩ := by simp [instOfD, instOf, hz]
  have heu : Ty.up _ m.entry_data (entryOf (instOfD m y)) = y.2 := by
    rw [hinst, ← hy2]; simp [entryOf, val_timerOf]
  rw [← hy2] at hv
  obtain ⟨v0, v1, hzv, -, hv1⟩ := (entry_rel_iff m hde st t zv).1 hv
  have hsel : (Term.sel de 0 1 xe).denote M = v1 := by rw [sel_ctor 1 (hxe.trans hzv)]; rfl
  have ht : RelV L _ (Ty.up _ m.timer_data (timerVal (instOfD m y).timer)) ((Term.sel de 0 1 xe).denote M) := by
    rw [hsel, hinst]; simpa [val_timerOf] using hv1
  obtain ⟨hhit, htg⟩ := timer_terms m hdent hdp (instOfD m y) hd ht
  refine ⟨hku ▸ hxk ▸ hk, hhit, heu ▸ hxe ▸ hy2 ▸ hv, htg⟩
end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem perm_all {α : Type} {l l' : List α} (h : l.Perm l') (p : α → Bool) : l.all p = l'.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H x hx => H x (h.mem_iff.2 hx), fun H x hx => H x (h.mem_iff.1 hx)⟩

theorem perm_any {α : Type} {l l' : List α} (h : l.Perm l') (p : α → Bool) : l.any p = l'.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, h'⟩ => ⟨x, h.mem_iff.1 hx, h'⟩, fun ⟨x, hx, h'⟩ => ⟨x, h.mem_iff.2 hx, h'⟩⟩

/-- A slot's fires term denotes whether its instance fires: no earlier machine fired, and `Step.firesIn`. -/
theorem fires_den (m : MachineV r e) {de nde dent nent dp np : Nat} (hde : L.find? (instEntry m.state) = some (de, nde))
    (hdent : L.find? (Ty.option (.tuple [.int, m.state])) = some (dent, nent)) (hdp : L.find? (.tuple [.int, m.state]) = some (dp, np))
    {done d : Term} {b : Bool} {dv : Int} (hdone : done.denote M = .bool b) (hd : d.denote M = .int dv)
    (hord : ∀ a b, ∃ p, ordT L T m.key a b = some p) (tbl : m.table.den0) {So : List Slot}
    {sv : List (Bool × List Val)} {ys : List (m.key.den × (instEntry m.state).den)} (hS : SlotsDen M So sv)
    (hh : Holds2 (ETab L m.key (instEntry m.state)) ys sv) (hperm : (ys.map (instOfD m)).Perm (instancesOf T m tbl))
    (yi : m.key.den × (instEntry m.state).den) (xsi : List Term) (hi : ETab L m.key (instEntry m.state) yi (Term.denotes M xsi)) :
    (Term.and (.not done) (.and (hitT dent dp (.sel de 0 1 (xsi.getD 1 tt)) d)
      (allSlotT So (So.map fun (_, ys') => Term.or (.not (hitT dent dp (.sel de 0 1 (ys'.getD 1 tt)) d))
        (leT L T m.key (xsi.headD tt) (ys'.headD tt)))))).denote M =
      .bool (!b && Step.firesIn T m dv (instancesOf T m tbl) (instOfD m yi)) := by
  have hitem := fire_item m hde hdent hdp hd
  let insts := instancesOf T m tbl
  obtain ⟨hki, hhi, -, -⟩ := hitem yi xsi hi
  have hal : AlignedV M (ETab L m.key (instEntry m.state)) (fun y v => v = .bool (!Step.hitsAt dv (instOfD m y) ||
      (Ty.cmp T m.key (instOfD m yi).key (instOfD m y).key).isLE)) So
      (So.map fun (_, ys') => Term.or (.not (hitT dent dp (.sel de 0 1 (ys'.getD 1 tt)) d))
        (leT L T m.key (xsi.headD tt) (ys'.headD tt))) sv ys := by
    refine aligned_map (fun ys' => Term.or (.not (hitT dent dp (.sel de 0 1 (ys'.getD 1 tt)) d))
      (leT L T m.key (xsi.headD tt) (ys'.headD tt))) (fun y xs h => ?_) hS hh
    obtain ⟨hk, hhy, -, -⟩ := hitem y xs h
    obtain ⟨pq, hpq⟩ := hord (xsi.headD tt) (xs.headD tt)
    have hod := ordT_rel L T m.key _ _ pq hpq m.key_data _ _ hki hk
    simp only [Term.denote, hhy, leT, hpq, hod.2, Val.toBool]
  have hall := allSlotT_den hal
  have hys : (ys.all fun y => !Step.hitsAt dv (instOfD m y) ||
      (Ty.cmp T m.key (instOfD m yi).key (instOfD m y).key).isLE) =
      insts.all fun i => !Step.hitsAt dv i || (Ty.cmp T m.key (instOfD m yi).key i.key).isLE := by
    rw [← perm_all hperm, List.all_map]; rfl
  rw [hys] at hall
  simp only [Term.denote, hdone, hhi, hall, Val.toBool, Step.firesIn]
  rfl

/-- The effect option an instance starts in a firing round: where it fires, `effect` at the state its timer enters. -/
def firedOpt (m : MachineV r e) (recs : r.den0) (tnow : Int) (fires : Bool) (i : Step.Instance m) :
    (Ty.option (.dsl .effect [e])).den :=
  match fires, i.timer with
  | true, some (_, tg) => m.effect.apply (.inl (i.key, tg, recs, tnow, ()), ())
  | _, _ => .inr (.inl ())

/-- One slot's terms of a firing round, where its condition holds: the new entry is the instance after the round
(entering its timer's state where it fires) and the effect option is the one it starts. -/
theorem fireAt_rel (m : MachineV r e)
    {af : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (Ty.timer m.state)))}
    {fx : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e])))}
    (haf : Smt.Rel M L _ (Ty.up _ m.after.ht m.after.fn) af) (hfx : EffectCodeRel (M := M) (L := L) m fx)
    (recs : r.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {de nde dent nent dp np dopt nopt : Nat} (hde : L.find? (instEntry m.state) = some (de, nde))
    (hdent : L.find? (Ty.option (.tuple [.int, m.state])) = some (dent, nent))
    (hdp : L.find? (.tuple [.int, m.state]) = some (dp, np))
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt))
    {So : List Slot} {done d : Term} {dv : Int} (hd : d.denote M = .int dv) {fb : Bool}
    {f : Term} {xs : List Term} (y : m.key.den × (instEntry m.state).den)
    (hE : ETab L m.key (instEntry m.state) y (Term.denotes M xs))
    (hfy : (Term.and (.not done) (.and (hitT dent dp (.sel de 0 1 (xs.getD 1 tt)) d)
      (allSlotT So (So.map fun (_, ys') => Term.or (.not (hitT dent dp (.sel de 0 1 (ys'.getD 1 tt)) d))
        (leT L T m.key (xs.headD tt) (ys'.headD tt)))))).denote M = .bool fb)
    (hhit : fb = true → Step.hitsAt dv (instOfD m y) = true)
    {q x c : Term} (hg : fireAt L T m af fx de dent dp So done d records now (.ctor dopt 1 []) (f, xs) = .ok (q, x, c))
    (hc : Holds M c) :
    RelV L (instEntry m.state)
      (Ty.up _ m.entry_data (entryOf (if fb then (Step.fired m recs tnow (instOfD m y)).1 else instOfD m y))) (q.denote M) ∧
    RelV L (Ty.option (.dsl .effect [e])) (firedOpt m recs tnow fb (instOfD m y)) (x.denote M) := by
  obtain ⟨ctxT, g1, hg⟩ := bind_ok.1 hg
  obtain ⟨nctx, g2, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨a, ca⟩, g3, hg⟩ := bind_ok.1 hg
  obtain ⟨at_, g4, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨xo, cx⟩, g5, hg⟩ := bind_ok.1 hg
  obtain ⟨xt, g6, hg⟩ := bind_ok.1 hg
  obtain ⟨tmT, g7, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  obtain ⟨hk, -, hent, htg⟩ := fire_item m hde hdent hdp hd y xs hE
  have hite : ∀ c a b : Term, (Term.ite c a b).denote M = if (c.denote M).toBool then a.denote M else b.denote M :=
    fun _ _ _ => rfl
  simp only [Holds] at hc
  rw [hite, Term.denote_share, hfy] at hc
  rw [hite, hite, Term.denote_share, hfy]
  cases fb with
  | false =>
    simp only [Val.toBool, ite_false, Bool.false_eq_true]
    exact ⟨hent, none_rel hopt⟩
  | true =>
    simp only [Val.toBool, ite_true] at hc ⊢
    obtain ⟨hca, hcx⟩ := (holds_andT _ _).1 hc
    generalize instOfD m y = iy at hhit htg hk
    obtain ⟨k0, st0, tm0⟩ := iy
    cases tm0 with
    | none => simp [Step.hitsAt] at hhit
    | some p0 =>
      obtain ⟨dl, tg⟩ := p0
      have htgr := htg dl tg rfl
      have hcx' := ctx_rel m hk htgr hrec hnow g1 (need_ok.1 g2)
      have ha := after_app m haf hcx' g3 hca
      have hat := (rel_term (need_ok.1 g4) _).1 ha
      have htm := timerT_rel m hnow _ hat g7
      refine ⟨(entry_rel_iff m hde _ _ _).2 ⟨_, _, ?_, htgr, htm⟩, ?_⟩
      · simp only [Term.denote, Term.denotes]
      · exact (rel_term (need_ok.1 g6) _).1 (hfx _ _ hcx' _ _ g5 hcx)

/-- T2 for one firing round on a machine's table: wherever the condition holds, the new table term denotes the
instances with the one `Step.firesIn` picks entering its timer's state (none where `done`), the hit term says
whether some instance has the deadline, and the start slots hold each instance's effect option (`firedOpt`). -/
theorem fire_table (m : MachineV r e)
    {af : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (Ty.timer m.state)))}
    {fx : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e])))}
    (haf : Smt.Rel M L _ (Ty.up _ m.after.ht m.after.fn) af) (hfx : EffectCodeRel (M := M) (L := L) m fx)
    (recs : r.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {done d : Term} {b : Bool} {dv : Int} (hdone : done.denote M = .bool b) (hd : d.denote M = .int dv)
    {o : FireOut} {c : Term} (henc : encodeFire L T m af fx x done d records now = .ok (o, c)) (hc : Holds M c) :
    (∃ tbl', RelV L m.table (Ty.up _ m.table_data tbl') (o.table.denote M) ∧
      instancesOf T m tbl' = (instancesOf T m tbl).map fun i =>
        if !b && Step.firesIn T m dv (instancesOf T m tbl) i then (Step.fired m recs tnow i).1 else i) ∧
    o.hit.denote M = .bool ((instancesOf T m tbl).any (Step.hitsAt dv)) ∧
    ∃ svX E, SlotsDen M (o.starts.map fun w => (w.1, [w.2.1, w.2.2])) svX ∧
      Holds2 (EOpt (L := L) m Step.Instance.key
        (fun i => firedOpt m recs tnow (!b && Step.firesIn T m dv (instancesOf T m tbl) i) i)) E svX ∧
      E.Perm (instancesOf T m tbl) := by
  obtain ⟨⟨dd, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨de, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dent, nent⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨dp, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dopt, nopt⟩, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨ord0, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨outs, h7, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨nde, hde⟩ := tupleD_ok h2
  obtain ⟨ndp, hdp⟩ := tupleD_ok h4
  replace h3 := need_ok.1 h3
  replace h5 := need_ok.1 h5
  have hord : ∀ a b, ∃ p, ordT L T m.key a b = some p := by
    intro a b
    have := ordT_isSome L T m.key a b tt tt
    rw [need_ok.1 h6] at this
    exact Option.isSome_iff_exists.1 (by simpa using this)
  have htbl' : Smt.Rel M L (.table m.key (instEntry m.state)) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS, hl, hw, hp, hh⟩ := table_view htbl' h1
  have hperm : (ys.map (instOfD m)).Perm (instancesOf T m tbl) := instancesOf_perm m tbl hp
  have hitem := fire_item m hde h3 hdp hd
  let So := slotsOf dd dt n 2 x
  let F : Step.Instance m → Step.Instance m := fun i =>
    if !b && Step.firesIn T m dv (instancesOf T m tbl) i then (Step.fired m recs tnow i).1 else i
  let Fo : Step.Instance m → (Ty.option (.dsl .effect [e])).den := fun i =>
    firedOpt m recs tnow (!b && Step.firesIn T m dv (instancesOf T m tbl) i) i
  have hfires := fires_den (T := T) m hde h3 hdp hdone hd hord tbl hS hh hperm
  have hguard : ∀ (p : Term × Term × Term → Term), ((guardsT So ((outs.map fun o => (p o, o.2.2)).map (·.2))).denote M).toBool = true := by
    intro p; rw [List.map_map]; exact hc
  have hslot : ∀ (sl : Slot) (r : Term × Term × Term) (y : m.key.den × (instEntry m.state).den),
      fireAt L T m af fx de dent dp So done d records now (.ctor dopt 1 []) sl = .ok r →
      ETab L m.key (instEntry m.state) y (Term.denotes M sl.2) → Holds M r.2.2 →
      RelV L (instEntry m.state) (Ty.up _ m.entry_data (entryOf (F (instOfD m y)))) (r.1.denote M) ∧
      RelV L (Ty.option (.dsl .effect [e])) (Fo (instOfD m y)) (r.2.1.denote M) := by
    rintro ⟨f, xs⟩ ⟨q, xo, cq⟩ y hG hE hcq
    exact fireAt_rel (T := T) m haf hfx recs tnow hrec hnow hde h3 hdp h5 hd y hE (hfires y xs hE)
      (fun h => by simp only [Step.firesIn, Bool.and_eq_true] at h; exact h.2.1) hG hcq
  have hhits : AlignedV M (ETab L m.key (instEntry m.state)) (fun y v => v = .bool (Step.hitsAt dv (instOfD m y)))
      So (hitsT de dent dp So d) sv ys :=
    aligned_map (fun xs => hitT dent dp (.sel de 0 1 (xs.getD 1 tt)) d) (fun y xs h => (hitem y xs h).2.1) hS hh
  have hany : (anySlotT So (hitsT de dent dp So d)).denote M = .bool ((instancesOf T m tbl).any (Step.hitsAt dv)) := by
    rw [anySlotT_den hhits, ← perm_any hperm, List.any_map]; rfl
  have hal : AlignedV M (ETab L m.key (instEntry m.state))
      (fun y v => RelV L (instEntry m.state) (Ty.up _ m.entry_data (entryOf (F (instOfD m y)))) v) So (outs.map (·.1)) sv ys := by
    have := aligned_of (fun sl r => ∃ o, fireAt L T m af fx de dent dp So done d records now (.ctor dopt 1 []) sl = .ok o ∧
      r = (o.1, o.2.2)) (V := fun y v => RelV L (instEntry m.state) (Ty.up _ m.entry_data (entryOf (F (instOfD m y)))) v)
      (fun sl r y hG hE hcq => by
        obtain ⟨o', hG, rfl⟩ := hG
        exact (hslot sl o' y hG hE hcq).1) hS hh (forall2_mapM_map _ _ h7) (hguard _)
    rwa [List.map_map] at this
  have halx : AlignedV M (ETab L m.key (instEntry m.state))
      (fun y v => RelV L (Ty.option (.dsl .effect [e])) (Fo (instOfD m y)) v) So (outs.map (·.2.1)) sv ys := by
    have := aligned_of (fun sl r => ∃ o, fireAt L T m af fx de dent dp So done d records now (.ctor dopt 1 []) sl = .ok o ∧
      r = (o.2.1, o.2.2)) (V := fun y v => RelV L (Ty.option (.dsl .effect [e])) (Fo (instOfD m y)) v)
      (fun sl r y hG hE hcq => by
        obtain ⟨o', hG, rfl⟩ := hG
        exact (hslot sl o' y hG hE hcq).2) hS hh (forall2_mapM_map _ _ h7) (hguard _)
    rwa [List.map_map] at this
  refine ⟨?_, hany, ?_⟩
  · let g : m.key.den × (instEntry m.state).den → m.key.den × (instEntry m.state).den :=
      fun y => (y.1, Ty.up _ m.entry_data (entryOf (F (instOfD m y))))
    obtain ⟨sv', hS', hl', hw', hh'⟩ := mapSlots_den (E' := ETab L m.key (instEntry m.state)) g
      (fun xs q => [xs.headD tt, q]) 2
      (fun y xs q h hq => ⟨_, _, rfl, (Ty.up_down _ m.key_data y.1) ▸ (hitem y xs h).1, hq⟩) (fun _ _ => rfl) hal
    have hkey : ∀ i, (F i).key = i.key := fun i => by
      simp only [F]; split
      · exact Step.fired_key m recs tnow i
      · rfl
    have hOk := instancesOk_map m (instancesOf_ok (T := T) m tbl) F hkey
    refine ⟨m.tableOf ((instancesOf T m tbl).map F) hOk.2, ?_, instancesOf_entries T m _ hOk⟩
    refine table_mk h1 hS' (hl'.trans hl) hw' ?_ hh'
    have hup : (Ty.up _ m.table_data (m.tableOf ((instancesOf T m tbl).map F) hOk.2)).1 =
        (instEntries m ((instancesOf T m tbl).map F)).map fun p => (Ty.up _ m.key_data p.1, Ty.up _ m.entry_data p.2) :=
      Ty.up_table m.key (instEntry m.state) m.table_data m.key_data m.entry_data _
    rw [hup]
    have hg : ys.map g = (ys.map (instOfD m)).map fun i =>
        (Ty.up _ m.key_data (F i).key, Ty.up _ m.entry_data (entryOf (F i))) := by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      simp only [Function.comp_apply, g, hkey]
      rw [show (instOfD m y).key = Ty.down _ m.key_data y.1 from rfl, Ty.up_down]
    rw [hg]
    refine (hperm.map _).trans (.of_eq ?_)
    simp only [instEntries, List.map_map]
    rfl
  · obtain ⟨svX, hSX, -, -, hhX⟩ := mapSlots_den (E' := EOpt (L := L) m Step.Instance.key Fo) (instOfD m)
      (fun xs q => [xs.headD tt, q]) 2
      (fun y xs q h hq => ⟨_, _, rfl, (hitem y xs h).1, hq⟩) (fun _ _ => rfl) halx
    refine ⟨svX, ys.map (instOfD m), ?_, hhX, hperm⟩
    rw [List.map_zipWith]
    exact hSX

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem forall2_guards {γ : Type} (π : γ → Term) {G : Slot → γ → Prop} : {S : List Slot} → {os : List γ} →
    Forall2 G S os → Forall2 (fun sl c' => ∃ q, G sl q ∧ c' = .or (.not sl.1) (π q)) S
      (List.zipWith (fun (f, _) c => Term.or (.not f) c) S (os.map π))
  | [], [], _ => trivial
  | _ :: _, q :: _, ⟨h, hs⟩ => ⟨⟨q, h, rfl⟩, forall2_guards π hs⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- The condition of a firing round is exact: where the codes' own conditions hold, it holds exactly when `after`
and `effect` fit at the state the firing instance enters. -/
theorem fire_exact (m : MachineV r e) {af : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (Ty.timer m.state)))}
    {fx : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e])))}
    {c0 c1 : Term} (hafc : m.after.code L = .ok (af, c0)) (hc0 : Holds M c0)
    (hfxc : m.effect.code L = .ok (fx, c1)) (hc1 : Holds M c1) (recs : r.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {done d : Term} {b : Bool} {dv : Int} (hdone : done.denote M = .bool b) (hd : d.denote M = .int dv)
    {o : FireOut} {c : Term} (henc : encodeFire L T m af fx x done d records now = .ok (o, c)) :
    Holds M c ↔ ∀ i ∈ instancesOf T m tbl, (!b && Step.firesIn T m dv (instancesOf T m tbl) i) = true →
      ∀ dl tg, i.timer = some (dl, tg) → m.after.appFits L.count (.inl (i.key, tg, recs, tnow, ()), ()) ∧
        m.effect.appFits L.count (.inl (i.key, tg, recs, tnow, ()), ()) := by
  obtain ⟨⟨dd, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨de, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dent, nent⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨dp, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dopt, nopt⟩, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨ord0, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨outs, h7, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨nde, hde⟩ := tupleD_ok h2
  obtain ⟨ndp, hdp⟩ := tupleD_ok h4
  replace h3 := need_ok.1 h3
  have hord : ∀ a b, ∃ p, ordT L T m.key a b = some p := by
    intro a b
    have := ordT_isSome L T m.key a b tt tt
    rw [need_ok.1 h6] at this
    exact Option.isSome_iff_exists.1 (by simpa using this)
  have htbl' : Smt.Rel M L (.table m.key (instEntry m.state)) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS, hl, hw, hp, hh⟩ := table_view htbl' h1
  have hperm : (ys.map (instOfD m)).Perm (instancesOf T m tbl) := instancesOf_perm m tbl hp
  have hitem := fire_item m hde h3 hdp hd
  have hfires := fires_den (T := T) m hde h3 hdp hdone hd hord tbl hS hh hperm
  let P : Step.Instance m → Prop := fun i => (!b && Step.firesIn T m dv (instancesOf T m tbl) i) = true →
    ∀ dl tg, i.timer = some (dl, tg) → m.after.appFits L.count (.inl (i.key, tg, recs, tnow, ()), ()) ∧
      m.effect.appFits L.count (.inl (i.key, tg, recs, tnow, ()), ())
  have hex := allT_slots_exact (E := ETab L m.key (instEntry m.state)) (P := fun y => P (instOfD m y))
    (fun sl c' => ∃ q, fireAt L T m af fx de dent dp (slotsOf dd dt n 2 x) done d records now (.ctor dopt 1 []) sl = .ok q ∧
      c' = .or (.not sl.1) q.2.2) ?_ hS hh (cs := List.zipWith (fun (f, _) c => Term.or (.not f) c) (slotsOf dd dt n 2 x)
        (outs.map (·.2.2))) ?_
  · show Holds M (guardsT _ _) ↔ _
    rw [show guardsT (slotsOf dd dt n 2 x) (outs.map (·.2.2)) = allT (List.zipWith (fun (f, _) c => Term.or (.not f) c)
      (slotsOf dd dt n 2 x) (outs.map (·.2.2))) from rfl, hex]
    constructor
    · intro H i hi; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hperm.mem_iff.2 hi); exact H y hy
    · intro H y hy; exact H _ (hperm.mem_iff.1 (List.mem_map.2 ⟨y, hy, rfl⟩))
  · rintro ⟨f, xs⟩ c' ⟨⟨q, xo, cq⟩, hq, rfl⟩
    obtain ⟨ctxT, g1, hq⟩ := bind_ok.1 hq
    obtain ⟨nctx, g2, hq⟩ := bind_ok.1 hq
    obtain ⟨⟨a, ca⟩, g3, hq⟩ := bind_ok.1 hq
    obtain ⟨at_, g4, hq⟩ := bind_ok.1 hq
    obtain ⟨⟨xr, cx⟩, g5, hq⟩ := bind_ok.1 hq
    obtain ⟨xt, g6, hq⟩ := bind_ok.1 hq
    obtain ⟨tmT, g7, hq⟩ := bind_ok.1 hq
    cases pure_ok.1 hq
    refine ⟨fun hf => by simp [Holds, Term.denote, hf, Val.toBool], fun y hf hE => ?_⟩
    have hite : ∀ c a b : Term, (Term.ite c a b).denote M = if (c.denote M).toBool then a.denote M else b.denote M :=
      fun _ _ _ => rfl
    have hor : ∀ a b : Term, (Term.or a b).denote M = .bool ((a.denote M).toBool || (b.denote M).toBool) :=
      fun _ _ => rfl
    have hnot : ∀ a : Term, (Term.not a).denote M = .bool !(a.denote M).toBool := fun _ => rfl
    simp only [Holds]
    rw [hor, hnot, hite, Term.denote_share, hfires y xs hE, hf]
    simp only [Val.toBool, Bool.not_true, Bool.false_or]
    obtain ⟨hk, hhy, -, htg⟩ := hitem y xs hE
    cases hfb : (!b && Step.firesIn T m dv (instancesOf T m tbl) (instOfD m y)) with
    | false =>
      constructor
      · intro _ h; rw [hfb] at h; cases h
      · intro _; simp [tt, Term.denote]
    | true =>
      have hhit : Step.hitsAt dv (instOfD m y) = true := by
        simp only [Step.firesIn, Bool.and_eq_true] at hfb; exact hfb.2.1
      simp only [ite_true, P, hfb, true_implies]
      generalize instOfD m y = iy at hhit htg hk
      obtain ⟨k0, st0, tm0⟩ := iy
      cases tm0 with
      | none => simp [Step.hitsAt] at hhit
      | some p0 =>
        obtain ⟨dl, tg⟩ := p0
        have hctx : ∀ t ∈ [Ty.machineCtx m.key m.state r], t.isFn = false := by simp [Ty.machineCtx, Ty.isFn]
        have hcx := ctx_rel m hk (htg dl tg rfl) hrec hnow g1 (need_ok.1 g2)
        have happ := m.after.app_exact hafc hc0 hctx _ _ (ctx_rels m hcx m.after.args_data) g3
        have happx := m.effect.app_exact hfxc hc1 hctx _ _ (ctx_rels m hcx m.effect.hps) g5
        change Holds M (andT ca cx) ↔ _
        rw [holds_andT]
        constructor
        · intro h dl' tg' ht
          simp only [Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          exact ⟨happ.1 h.1, happx.1 h.2⟩
        · intro h; exact ⟨happ.2 (h dl tg rfl).1, happx.2 (h dl tg rfl).2⟩
  · exact forall2_guards (·.2.2) (mapM_ok _ _ _ h7)

end

section
variable {T : List TypeDecl} {r e : Ty}

theorem filter_flatMap {α β : Type} (p : α → Bool) (g : α → List β) : (l : List α) →
    (l.filter p).flatMap g = l.flatMap fun a => if p a then g a else []
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons, List.flatMap_cons, ← filter_flatMap p g l]
    cases p a <;> simp

/-- Instances in the step's form strictly increase by key. -/
theorem instancesOk_lt (m : MachineV r e) (ho : m.key.ordered T = true) {insts : List (Step.Instance m)}
    (h : InstancesOk T m insts) : insts.Pairwise fun a b => Ty.cmp T m.key a.key b.key = .lt := by
  have hu : insts.Pairwise fun a b => (Ty.semWith Dsl.base m.key).2 a.key b.key = false := by
    have := h.2
    unfold KeysUnique instEntries at this
    exact (List.pairwise_map.1 this).imp fun h => h.1
  refine (h.1.and hu).imp fun ⟨h1, h2⟩ => ?_
  cases e : Ty.cmp T m.key _ _ with
  | lt => rfl
  | eq => rw [(Ty.cmp_eq_iff T ho _ _).1 e] at h2; cases h2
  | gt => simp [keyLE, e] at h1

theorem instancesOk_distinct (m : MachineV r e) {insts : List (Step.Instance m)} (h : InstancesOk T m insts) :
    insts.Pairwise fun a b => (Ty.semWith Dsl.base m.key).2 a.key b.key = false := by
  have := h.2
  unfold KeysUnique instEntries at this
  exact (List.pairwise_map.1 this).imp fun h => h.1

theorem firedOpt_false (m : MachineV r e) (recs : r.den0) (now : Int) (i : Step.Instance m) :
    firedOpt m recs now false i = .inr (.inl ()) := rfl

/-- One machine's part of a firing round, unless an earlier machine fired (`done`): the instance `Step.firesIn`
picks enters its timer's state and starts its effect option (`firedOpt`), and the flag says whether some machine so
far has an instance with the deadline. -/
theorem fireMachines_cons (m : MachineV r e) (ho : m.key.ordered T = true) (recs : r.den0) (now d : Int) (b : Bool)
    {insts : List (Step.Instance m)} (h : InstancesOk T m insts) (rest : List (Step.MachineState r e)) :
    Step.fireMachines recs now d b (⟨m, insts⟩ :: rest) =
      (⟨m, insts.map fun i => if !b && Step.firesIn T m d insts i then (Step.fired m recs now i).1 else i⟩ ::
          (Step.fireMachines recs now d (b || insts.any (Step.hitsAt d)) rest).1,
        insts.flatMap (fun i => (sentBy m Step.Instance.key
          (fun i => firedOpt m recs now (!b && Step.firesIn T m d insts i) i) i).toList) ++
          (Step.fireMachines recs now d (b || insts.any (Step.hitsAt d)) rest).2.1,
        (Step.fireMachines recs now d (b || insts.any (Step.hitsAt d)) rest).2.2) := by
  cases b with
  | true =>
    have hmap : (insts.map fun i => if (!true && Step.firesIn T m d insts i) = true then (Step.fired m recs now i).1 else i) =
        insts := by
      conv => rhs; rw [← List.map_id insts]
      exact List.map_congr_left fun i _ => by simp
    have hnil : (insts.flatMap fun i => (sentBy m Step.Instance.key
        (fun i => firedOpt m recs now (!true && Step.firesIn T m d insts i) i) i).toList) = [] :=
      List.flatMap_eq_nil_iff.2 fun i _ => by
        simp only [Bool.not_true, Bool.false_and, firedOpt_false, sentBy]; rfl
    rw [hmap, hnil, Bool.true_or, Step.fireMachines_true]
    simp only [Step.fireMachines_true, List.nil_append]
  | false =>
    simp only [Step.fireMachines, Bool.false_or, Bool.not_false, Bool.true_and]
    rw [Step.fireFirst_eq T m ho recs now d insts h.1 (instancesOk_distinct m h)]
    simp only [Prod.mk.injEq, true_and, and_true]
    congr 1
    rw [filter_flatMap]
    congr 1; funext i
    cases hf : Step.firesIn T m d insts i with
    | false => simp only [hf, Bool.false_eq_true, ite_false, firedOpt_false, sentBy]; rfl
    | true =>
      obtain ⟨k, st, t⟩ := i
      cases t with
      | none => simp [Step.firesIn, Step.hitsAt] at hf
      | some p =>
        obtain ⟨dl, tg⟩ := p
        have h1 : (Step.fired m recs now ⟨k, st, some (dl, tg)⟩).2 =
            (m.effectAt k tg recs now).toList.map (.machine m.name ⟨m.key, k⟩, ·) := rfl
        have h2 : firedOpt m recs now true ⟨k, st, some (dl, tg)⟩ = m.effect.apply (.inl (k, tg, recs, now, ()), ()) := rfl
        simp only [↓reduceIte]
        rw [h1]
        unfold sentBy
        simp only [hf, h2]
        unfold MachineV.effectAt
        generalize Ty.toOption _ = o
        cases o <;> rfl

end

end Tazuna.Smt
