import Tazuna.Smt.EventMachines
import Tazuna.Smt.ReactExact
import Tazuna.Semantics.Fire

/-! One round of timer firing on a machine's instance table. A slot's timer is the `timer` code at its key, its state
and the records (`encodeTimers`), computed once per round and read by the earliest-deadline search and by the round.
Each slot is encoded alone (`Step.fireFirst_eq`): it fires where no earlier machine fired, its timer has the round's
deadline, and no slot with that deadline has a smaller key, by the order terms. A slot that fires holds the state its
timer enters. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {M : Model} {r e : Ty}

/-- The terms a timer value is read by: whether it has the deadline `d`, and the state it enters. -/
def hitT (dopt dtm : Nat) (tm d : Term) : Term := .and (.is dopt 0 tm) (.eq (.sel dtm 0 0 (.sel dopt 0 0 tm)) d)
def targetT (dopt dtm : Nat) (tm : Term) : Term := .sel dtm 0 1 (.sel dopt 0 0 tm)

theorem timer_terms (m : MachineV r e) {dopt n1 dtm n2 : Nat}
    (h1 : L.find? (Ty.option (Ty.timer m.state)) = some (dopt, n1)) (h2 : L.find? (Ty.timer m.state) = some (dtm, n2))
    (recs : r.den0) (i : Step.Instance m) {tm d : Term} {dv : Int} (hd : d.denote M = .int dv)
    (ht : RelV L _ (Ty.up _ m.timer_data (m.timer.fn (.inl (i.key, i.state, recs, ()), ()))) (tm.denote M)) :
    (hitT dopt dtm tm d).denote M = .bool (Step.hitsAt recs dv i) ∧
      ∀ dl tg, Step.timerOf recs i = some (dl, tg) →
        RelV L m.state (Ty.up _ m.state_data tg) ((targetT dopt dtm tm).denote M) := by
  obtain ⟨his, hsel⟩ := timer_view m h1 h2 _ ht
  refine ⟨?_, fun dl tg h => (hsel dl tg h).2⟩
  have hden : (hitT dopt dtm tm d).denote M = .bool (((Term.is dopt 0 tm).denote M).toBool &&
      ((Term.sel dtm 0 0 (.sel dopt 0 0 tm)).denote M == d.denote M)) := rfl
  rw [hden, his, hd]
  unfold Step.hitsAt Step.timerOf MachineV.timerAt
  cases hv : Step.timerVal (m.timer.fn (.inl (i.key, i.state, recs, ()), ())) with
  | none => simp [Val.toBool]
  | some p =>
    obtain ⟨dl, tg⟩ := p
    rw [(hsel dl tg hv).1]
    by_cases h : dl = dv <;> simp [h, Val.toBool, BEq.beq, Val.beq]

end

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- The order term `x ≤ y` on keys, true where the key type has none (`encodeFire` refuses those). -/
def leT (t : Ty) (x y : Term) : Term :=
  match ordT L T t x y with
  | some (_, le) => le
  | none => tt

/-- A slot's timer: the `timer` code at the slot's key, its state and the records, and its condition, asked where the
slot holds an instance. -/
def timerSlot (m : MachineV r e) (tc : Code (Ty.fn [Ty.timerCtx m.key m.state r] (Ty.option (Ty.timer m.state))))
    (records : Term) : InstSlot → Except Refusal (Term × Term)
  | ⟨f, key, st⟩ => do
    let cx ← Code.ofDataE _ (← timerCtxT L m key st records)
    let (a, c) ← tc (cx, ())
    let at_ ← Code.dataTermE _ a
    pure (Term.share at_, .ite f c tt)

/-- Every slot's timer on the instance table `tbl` at the records, and the condition that `timer` fits at each
instance. -/
def encodeTimers (m : MachineV r e) (tc : Code (Ty.fn [Ty.timerCtx m.key m.state r] (Ty.option (Ty.timer m.state))))
    (tbl records : Term) : Except Refusal (List Term × Term) := do
  let (dd, n, dt) ← collD L m.table [m.key, m.state]
  let outs ← (instSlotsOf dd dt n tbl).mapM (timerSlot L m tc records)
  pure (outs.map (·.1), allT (outs.map (·.2)))

/-- One slot's part of a firing round, with its timer term: its new state, the effect option it starts, and the
condition of `effect` where the slot fires. It fires where no earlier machine fired (`done`), its timer has the
deadline `d`, and every slot with that deadline has a key no smaller. -/
def fireAt (m : MachineV r e) (fx : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e]))))
    (dopt dtm : Nat) (St : List (InstSlot × Term)) (done d records now noneT : Term) :
    InstSlot × Term → Except Refusal (Term × Term × Term)
  | (⟨_, key, entry⟩, tm) => do
    let les := St.map fun (s, t) => Term.or (.not (hitT dopt dtm t d)) (leT L T m.key key s.key)
    let fires := Term.share (.and (.not done) (.and (hitT dopt dtm tm d) (allSlotT (St.map (·.1.slot)) les)))
    let tg := targetT dopt dtm tm
    let nctx ← Code.ofDataE _ (← instCtxT L m key tg records now)
    let (x, cx) ← fx (nctx, ())
    let xt ← Code.dataTermE _ x
    pure (.ite fires tg entry, .ite fires xt noneT, .ite fires cx tt)

/-- What a firing round encodes on one machine: the new instance table, whether some slot has the deadline, and per
slot its flag, key and the effect option it starts. -/
structure FireOut where
  table : Term
  hit : Term
  starts : List StartSlot

/-- One firing round on the instance table `tbl` (`Step.fireFirst`), unless `done`, at the deadline `d`, with the
slots' timer terms `tms` (`encodeTimers`), and its condition. Refused when the key type has no order terms. -/
def encodeFire (m : MachineV r e) (fx : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e]))))
    (tms : List Term) (tbl done d records now : Term) : Except Refusal (FireOut × Term) := do
  let (dd, n, dt) ← collD L m.table [m.key, m.state]
  let (dopt, _) ← L.findE (Ty.option (Ty.timer m.state))
  let (dtm, _) ← L.findE (Ty.timer m.state)
  let (deff, _) ← L.findE (Ty.option (.dsl .effect [e]))
  let _ ← need (lacks m.key) (ordT L T m.key tt tt)
  let St := (instSlotsOf dd dt n tbl).zip tms
  let outs ← St.mapM (fireAt L T m fx dopt dtm St done d records now (.ctor deff 1 []))
  pure (⟨slotsTerm dd dt ((List.zipWith (fun s q => { s.1 with entry := q }) St (outs.map (·.1))).map InstSlot.slot),
      anySlotT (St.map (·.1.slot)) (St.map fun (_, t) => hitT dopt dtm t d),
      List.zipWith (fun s q => ⟨s.1.flag, s.1.key, q⟩) St (outs.map (·.2.1))⟩,
    guardsT (St.map (·.1.slot)) (outs.map (·.2.2)))

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- The instance a table entry's values code. -/
def instOfD (m : MachineV r e) (y : m.key.den × m.state.den) : Step.Instance m :=
  instOf m (Ty.down _ m.key_data y.1) (Ty.down _ m.state_data y.2)

/-- A slot's timer term denotes the timer that the instance it holds waits for at the records. -/
def TimerOk (M : Model) (L : Layout) (m : MachineV r e) (recs : r.den0) (sl : InstSlot) (tm : Term) : Prop :=
  sl.flag.denote M = .bool true → ∀ y, ETab L m.key m.state y (Term.denotes M sl.slot.2.1) →
    RelV L _ (Ty.up _ m.timer_data (m.timer.fn (.inl ((instOfD m y).key, (instOfD m y).state, recs, ()), ())))
      (tm.denote M)

theorem instancesOf_perm (m : MachineV r e) (tbl : m.table.den0) {ys : List (m.key.den × m.state.den)}
    (hp : ys.Perm (Ty.up _ m.table_data tbl).1) : (ys.map (instOfD m)).Perm (instancesOf T m tbl) := by
  have hup : (Ty.up _ m.table_data tbl).1 = tbl.1.map fun p => (Ty.up _ m.key_data p.1, Ty.up _ m.state_data p.2) :=
    Ty.up_table m.key m.state m.table_data m.key_data m.state_data tbl
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
      exact List.map_congr_left fun _ _ => rfl
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

/-- What a slot's terms read of the instance it holds: the key, whether its timer has the deadline, its state, and the
state its timer enters. -/
theorem fire_item (m : MachineV r e) {dopt n1 dtm n2 : Nat}
    (h1 : L.find? (Ty.option (Ty.timer m.state)) = some (dopt, n1)) (h2 : L.find? (Ty.timer m.state) = some (dtm, n2))
    (recs : r.den0) {d : Term} {dv : Int} (hd : d.denote M = .int dv) (y : m.key.den × m.state.den) (sl : InstSlot)
    (tm : Term) (hfl : sl.flag.denote M = .bool true) (h : ETab L m.key m.state y (Term.denotes M sl.slot.2.1))
    (ht : TimerOk M L m recs sl tm) :
    RelV L m.key (Ty.up _ m.key_data (instOfD m y).key) (sl.key.denote M) ∧
      (hitT dopt dtm tm d).denote M = .bool (Step.hitsAt recs dv (instOfD m y)) ∧
      RelV L m.state (Ty.up _ m.state_data (instOfD m y).state) (sl.entry.denote M) ∧
      ∀ dl tg, Step.timerOf recs (instOfD m y) = some (dl, tg) →
        RelV L m.state (Ty.up _ m.state_data tg) ((targetT dopt dtm tm).denote M) := by
  have htm := ht hfl y h
  obtain ⟨zk, zv, hvs, hk, hv⟩ := h
  obtain ⟨f, xk, xe⟩ := sl
  simp only [InstSlot.slot, Term.denotes, List.cons.injEq, and_true] at hvs
  obtain ⟨hxk, hxe⟩ := hvs
  have hku : Ty.up _ m.key_data (instOfD m y).key = y.1 := Ty.up_down _ _ _
  have hsu : Ty.up _ m.state_data (instOfD m y).state = y.2 := Ty.up_down _ _ _
  obtain ⟨hhit, htg⟩ := timer_terms m h1 h2 recs (instOfD m y) hd htm
  exact ⟨hku ▸ hxk ▸ hk, hhit, hsu ▸ hxe ▸ hv, htg⟩
end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem perm_all {α : Type} {l l' : List α} (h : l.Perm l') (p : α → Bool) : l.all p = l'.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H x hx => H x (h.mem_iff.2 hx), fun H x hx => H x (h.mem_iff.1 hx)⟩

theorem perm_any {α : Type} {l l' : List α} (h : l.Perm l') (p : α → Bool) : l.any p = l'.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, h'⟩ => ⟨x, h.mem_iff.1 hx, h'⟩, fun ⟨x, hx, h'⟩ => ⟨x, h.mem_iff.2 hx, h'⟩⟩

/-- The slots of a table zipped with their timer terms, as slots: the table's. -/
theorem zip_slots {So : List InstSlot} {tms : List Term} {R : InstSlot → Term → Prop} (h : Forall2 R So tms) :
    (So.zip tms).map (·.1.slot) = So.map InstSlot.slot := by
  have : (So.zip tms).map (·.1.slot) = ((So.zip tms).map Prod.fst).map InstSlot.slot := by simp
  rw [this, List.map_fst_zip (by rw [forall2_length h]; exact Nat.le_refl _)]

/-- A slot's fires term denotes whether its instance fires: no earlier machine fired, and `Step.firesIn`. -/
theorem fires_den (m : MachineV r e) {dopt n1 dtm n2 : Nat}
    (h1 : L.find? (Ty.option (Ty.timer m.state)) = some (dopt, n1)) (h2 : L.find? (Ty.timer m.state) = some (dtm, n2))
    (recs : r.den0) {done d : Term} {b : Bool} {dv : Int} (hdone : done.denote M = .bool b) (hd : d.denote M = .int dv)
    (hord : ∀ a b, ∃ p, ordT L T m.key a b = some p) (tbl : m.table.den0) {St : List (InstSlot × Term)}
    {sv : List (Bool × List Val)} {ys : List (m.key.den × m.state.den)}
    (hS : SlotsDen M (St.map (·.1.slot)) sv) (hT : ∀ p ∈ St, TimerOk M L m recs p.1 p.2)
    (hh : Holds2 (ETab L m.key m.state) ys sv) (hperm : (ys.map (instOfD m)).Perm (instancesOf T m tbl))
    (yi : m.key.den × m.state.den) (si : InstSlot) (ti : Term) (hti : TimerOk M L m recs si ti)
    (hfl : si.flag.denote M = .bool true) (hi : ETab L m.key m.state yi (Term.denotes M si.slot.2.1)) :
    (Term.and (.not done) (.and (hitT dopt dtm ti d)
      (allSlotT (St.map (·.1.slot)) (St.map fun (s, t) => Term.or (.not (hitT dopt dtm t d))
        (leT L T m.key si.key s.key))))).denote M =
      .bool (!b && Step.firesIn T m recs dv (instancesOf T m tbl) (instOfD m yi)) := by
  let insts := instancesOf T m tbl
  obtain ⟨hki, hhi, -, -⟩ := fire_item m h1 h2 recs hd yi si ti hfl hi hti
  have hal : AlignedV M (ETab L m.key m.state) (fun y v => v = .bool (!Step.hitsAt recs dv (instOfD m y) ||
      (Ty.cmp T m.key (instOfD m yi).key (instOfD m y).key).isLE)) (St.map (·.1.slot))
      (St.map fun (s, t) => Term.or (.not (hitT dopt dtm t d)) (leT L T m.key si.key s.key)) sv ys := by
    refine aligned_mapView_mem (·.1.slot) (fun (p : InstSlot × Term) => Term.or (.not (hitT dopt dtm p.2 d))
      (leT L T m.key si.key p.1.key)) (fun p hp y hf h => ?_) hS hh
    obtain ⟨hk, hhy, -, -⟩ := fire_item m h1 h2 recs hd y p.1 p.2 hf h (hT p hp)
    obtain ⟨pq, hpq⟩ := hord si.key p.1.key
    have hod := ordT_rel L T m.key _ _ pq hpq m.key_data _ _ hki hk
    simp only [Term.denote, hhy, leT, hpq, hod.2, Val.toBool]
  have hall := allSlotT_den hal
  have hys : (ys.all fun y => !Step.hitsAt recs dv (instOfD m y) ||
      (Ty.cmp T m.key (instOfD m yi).key (instOfD m y).key).isLE) =
      insts.all fun i => !Step.hitsAt recs dv i || (Ty.cmp T m.key (instOfD m yi).key i.key).isLE := by
    rw [← perm_all hperm, List.all_map]; rfl
  rw [hys] at hall
  simp only [Term.denote, hdone, hhi, hall, Val.toBool, Step.firesIn]
  rfl

/-- The effect option an instance starts in a firing round: where it fires, `effect` at the state its timer enters. -/
def firedOpt (m : MachineV r e) (recs : r.den0) (tnow : Int) (fires : Bool) (i : Step.Instance m) :
    (Ty.option (.dsl .effect [e])).den :=
  match fires, Step.timerOf recs i with
  | true, some (_, tg) => m.effect.apply (.inl (i.key, tg, recs, tnow, ()), ())
  | _, _ => .inr (.inl ())

/-- One slot's terms of a firing round, where its condition holds: the new state is the instance's after the round
(entering its timer's state where it fires) and the effect option is the one it starts. -/
theorem fireAt_rel (m : MachineV r e)
    {fx : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e])))}
    (hfx : EffectCodeRel (M := M) (L := L) m fx)
    (recs : r.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {dopt n1 dtm n2 deff neff : Nat}
    (h1 : L.find? (Ty.option (Ty.timer m.state)) = some (dopt, n1)) (h2 : L.find? (Ty.timer m.state) = some (dtm, n2))
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (deff, neff))
    {St : List (InstSlot × Term)} {done d : Term} {dv : Int} (hd : d.denote M = .int dv) {fb : Bool}
    {sl : InstSlot} {tm : Term} (htm : TimerOk M L m recs sl tm) (y : m.key.den × m.state.den)
    (hfl : sl.flag.denote M = .bool true) (hE : ETab L m.key m.state y (Term.denotes M sl.slot.2.1))
    (hfy : (Term.and (.not done) (.and (hitT dopt dtm tm d)
      (allSlotT (St.map (·.1.slot)) (St.map fun (s, t) => Term.or (.not (hitT dopt dtm t d))
        (leT L T m.key sl.key s.key))))).denote M = .bool fb)
    (hhit : fb = true → Step.hitsAt recs dv (instOfD m y) = true)
    {q x c : Term} (hg : fireAt L T m fx dopt dtm St done d records now (.ctor deff 1 []) (sl, tm) = .ok (q, x, c))
    (hc : Holds M c) :
    RelV L m.state
      (Ty.up _ m.state_data (if fb then (Step.fired m recs tnow (instOfD m y)).1 else instOfD m y).state) (q.denote M) ∧
    RelV L (Ty.option (.dsl .effect [e])) (firedOpt m recs tnow fb (instOfD m y)) (x.denote M) := by
  obtain ⟨ctxT, g1, hg⟩ := bind_ok.1 hg
  obtain ⟨nctx, g2, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨xo, cx⟩, g5, hg⟩ := bind_ok.1 hg
  obtain ⟨xt, g6, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  obtain ⟨hk, -, hent, htg⟩ := fire_item m h1 h2 recs hd y sl tm hfl hE htm
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
    have hh := hhit rfl
    unfold Step.fired firedOpt
    unfold Step.hitsAt at hh
    split at hh
    · next dl tg ht =>
      rw [ht]
      have htgr := htg dl tg ht
      have hcx' := ctx_rel m hk htgr hrec hnow g1 (need_ok.1 g2)
      exact ⟨htgr, (rel_term (need_ok.1 g6) _).1 (hfx _ _ hcx' _ _ g5 hc)⟩
    · cases hh

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem forall2_guards {γ : Type} {w : Nat} (π : γ → Term) {G : Slot w → γ → Prop} : {S : List (Slot w)} →
    {os : List γ} →
    Forall2 G S os → Forall2 (fun sl c' => ∃ q, G sl q ∧ c' = .or (.not sl.1) (π q)) S
      (List.zipWith (fun (f, _) c => Term.or (.not f) c) S (os.map π))
  | [], [], _ => trivial
  | _ :: _, q :: _, ⟨h, hs⟩ => ⟨⟨q, h, rfl⟩, forall2_guards π hs⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- One firing round on a machine's table, with timer terms that denote each slot's timer: where the effect code's own
condition holds, the condition holds exactly when `effect` fits at the state the firing instance enters, and wherever
it holds the new table term denotes the instances with the one `Step.firesIn` picks entering its timer's state (none
where `done`), the hit term says whether some instance has the deadline, and the start slots hold each instance's
effect option (`firedOpt`). -/
theorem fire_encode (m : MachineV r e)
    {fx : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e])))}
    {c1 : Term} (hfxc : m.effect.code L = .ok (fx, c1)) (hc1 : Holds M c1) (recs : r.den0) (tnow : Int)
    {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {tms : List Term}
    (htms : ∀ dd n dt, collD L m.table [m.key, m.state] = .ok (dd, n, dt) →
      Forall2 (TimerOk M L m recs) (instSlotsOf dd dt n x) tms)
    {done d : Term} {b : Bool} {dv : Int} (hdone : done.denote M = .bool b) (hd : d.denote M = .int dv)
    {o : FireOut} {c : Term} (henc : encodeFire L T m fx tms x done d records now = .ok (o, c)) :
    (Holds M c ↔ ∀ i ∈ instancesOf T m tbl, (!b && Step.firesIn T m recs dv (instancesOf T m tbl) i) = true →
      ∀ dl tg, Step.timerOf recs i = some (dl, tg) → m.effect.appFits L.count (.inl (i.key, tg, recs, tnow, ()), ())) ∧
    (Holds M c →
      (∃ tbl', RelV L m.table (Ty.up _ m.table_data tbl') (o.table.denote M) ∧
        instancesOf T m tbl' = (instancesOf T m tbl).map fun i =>
          if !b && Step.firesIn T m recs dv (instancesOf T m tbl) i then (Step.fired m recs tnow i).1 else i) ∧
      o.hit.denote M = .bool ((instancesOf T m tbl).any (Step.hitsAt recs dv)) ∧
      ∃ svX E, SlotsDen M (o.starts.map StartSlot.slot) svX ∧
        Holds2 (EOpt (L := L) m Step.Instance.key
          (fun i => firedOpt m recs tnow (!b && Step.firesIn T m recs dv (instancesOf T m tbl) i) i)) E svX ∧
        E.Perm (instancesOf T m tbl)) := by
  obtain ⟨⟨dd, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dopt, n1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dtm, n2⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨deff, neff⟩, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨ord0, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨outs, h7, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  replace h2 := need_ok.1 h2
  replace h3 := need_ok.1 h3
  replace h5 := need_ok.1 h5
  have hT2 := htms dd n dt h1
  let So := instSlotsOf dd dt n x
  let St := So.zip tms
  have hT : ∀ p ∈ St, TimerOk M L m recs p.1 p.2 := forall2_zip hT2
  have hord : ∀ a b, ∃ p, ordT L T m.key a b = some p := by
    intro a b
    have := ordT_isSome L T m.key a b tt tt
    rw [need_ok.1 h6] at this
    exact Option.isSome_iff_exists.1 (by simpa using this)
  have htbl' : Smt.Rel M L (.table m.key m.state) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS0, hl, -, hp, hh⟩ := table_view htbl' h1
  rw [← instSlotsOf_slot] at hS0
  have hzs : St.map (·.1.slot) = So.map InstSlot.slot := zip_slots hT2
  have hS : SlotsDen M (St.map (·.1.slot)) sv := by rw [hzs]; exact hS0
  have hperm : (ys.map (instOfD m)).Perm (instancesOf T m tbl) := instancesOf_perm m tbl hp
  have hfires := fires_den (T := T) m h2 h3 recs hdone hd hord tbl hS hT hh hperm
  have hF7 : Forall2 (fun p q => TimerOk M L m recs p.1 p.2 ∧
      fireAt L T m fx dopt dtm St done d records now (.ctor deff 1 []) p = .ok q) St outs :=
    forall2_and_left (mapM_ok _ _ _ h7) hT
  refine ⟨?_, fun hc => ?_⟩
  · let P : Step.Instance m → Prop := fun i => (!b && Step.firesIn T m recs dv (instancesOf T m tbl) i) = true →
      ∀ dl tg, Step.timerOf recs i = some (dl, tg) → m.effect.appFits L.count (.inl (i.key, tg, recs, tnow, ()), ())
    have hex := allT_slots_exact (E := ETab L m.key m.state) (P := fun y => P (instOfD m y))
      (fun sl c' => ∃ q, (∃ s : InstSlot × Term, TimerOk M L m recs s.1 s.2 ∧ s.1.slot = sl ∧
        fireAt L T m fx dopt dtm St done d records now (.ctor deff 1 []) s = .ok q) ∧ c' = .or (.not sl.1) q.2.2)
        ?_ hS hh
        (cs := List.zipWith (fun (f, _) c => Term.or (.not f) c) (St.map (·.1.slot)) (outs.map (·.2.2))) ?_
    · show Holds M (guardsT _ _) ↔ _
      rw [show guardsT (St.map (·.1.slot)) (outs.map (·.2.2)) =
        allT (List.zipWith (fun (f, _) c => Term.or (.not f) c) (St.map (·.1.slot)) (outs.map (·.2.2))) from rfl, hex]
      constructor
      · intro H i hi; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hperm.mem_iff.2 hi); exact H y hy
      · intro H y hy; exact H _ (hperm.mem_iff.1 (List.mem_map.2 ⟨y, hy, rfl⟩))
    · rintro _ c' ⟨⟨q, xo, cq⟩, ⟨⟨⟨f, tk, te⟩, tmi⟩, hti, rfl, hq⟩, rfl⟩
      obtain ⟨ctxT, g1, hq⟩ := bind_ok.1 hq
      obtain ⟨nctx, g2, hq⟩ := bind_ok.1 hq
      obtain ⟨⟨xr, cx⟩, g5, hq⟩ := bind_ok.1 hq
      obtain ⟨xt, g6, hq⟩ := bind_ok.1 hq
      cases pure_ok.1 hq
      refine ⟨fun hf => by simp [Holds, Term.denote, hf, Val.toBool], fun y hf hE => ?_⟩
      have hite : ∀ c a b : Term, (Term.ite c a b).denote M = if (c.denote M).toBool then a.denote M else b.denote M :=
        fun _ _ _ => rfl
      have hor : ∀ a b : Term, (Term.or a b).denote M = .bool ((a.denote M).toBool || (b.denote M).toBool) :=
        fun _ _ => rfl
      have hnot : ∀ a : Term, (Term.not a).denote M = .bool !(a.denote M).toBool := fun _ => rfl
      simp only [Holds]
      rw [hor, hnot, hite, Term.denote_share, hfires y ⟨f, tk, te⟩ tmi hti hf hE, hf]
      simp only [Val.toBool, Bool.not_true, Bool.false_or]
      obtain ⟨hk, hhy, -, htg⟩ := fire_item m h2 h3 recs hd y ⟨f, tk, te⟩ tmi hf hE hti
      cases hfb : (!b && Step.firesIn T m recs dv (instancesOf T m tbl) (instOfD m y)) with
      | false =>
        constructor
        · intro _ h; rw [hfb] at h; cases h
        · intro _; simp [tt, Term.denote]
      | true =>
        have hhit : Step.hitsAt recs dv (instOfD m y) = true := by
          simp only [Step.firesIn, Bool.and_eq_true] at hfb; exact hfb.2.1
        simp only [ite_true, P, hfb, true_implies]
        unfold Step.hitsAt at hhit
        split at hhit
        · next dl tg ht =>
          have hctx : ∀ t ∈ [Ty.machineCtx m.key m.state r], t.isFn = false := by simp [Ty.machineCtx, Ty.isFn]
          have hcx := ctx_rel m hk (htg dl tg ht) hrec hnow g1 (need_ok.1 g2)
          have happx := m.effect.app_exact hfxc hc1 hctx _ _ (ctx_rels m hcx m.effect.hps) g5
          constructor
          · intro h dl' tg' ht'
            rw [ht] at ht'
            simp only [Option.some.injEq, Prod.mk.injEq] at ht'
            obtain ⟨rfl, rfl⟩ := ht'
            exact happx.1 h
          · intro h; exact happx.2 (h dl tg ht)
        · cases hhit
    · exact forall2_guards (·.2.2) (forall2_map (·.1.slot)
        (R' := fun sl q => ∃ s : InstSlot × Term, TimerOk M L m recs s.1 s.2 ∧ s.1.slot = sl ∧
          fireAt L T m fx dopt dtm St done d records now (.ctor deff 1 []) s = .ok q)
        (fun s q h => ⟨s, h.1, rfl, h.2⟩) hF7)
  · have hfx := effect_codeRel (M := M) m hfxc hc1
    let F : Step.Instance m → Step.Instance m := fun i =>
      if !b && Step.firesIn T m recs dv (instancesOf T m tbl) i then (Step.fired m recs tnow i).1 else i
    let Fo : Step.Instance m → (Ty.option (.dsl .effect [e])).den := fun i =>
      firedOpt m recs tnow (!b && Step.firesIn T m recs dv (instancesOf T m tbl) i) i
    have hguard : ∀ (p : Term × Term × Term → Term),
        ((guardsT (St.map (·.1.slot)) ((outs.map fun o => (p o, o.2.2)).map (·.2))).denote M).toBool = true := by
      intro p; rw [List.map_map]; exact hc
    have hslot : ∀ (sl : InstSlot × Term) (r : Term × Term × Term) (y : m.key.den × m.state.den),
        TimerOk M L m recs sl.1 sl.2 →
        fireAt L T m fx dopt dtm St done d records now (.ctor deff 1 []) sl = .ok r →
        sl.1.flag.denote M = .bool true →
        ETab L m.key m.state y (Term.denotes M sl.1.slot.2.1) → Holds M r.2.2 →
        RelV L m.state (Ty.up _ m.state_data (F (instOfD m y)).state) (r.1.denote M) ∧
        RelV L (Ty.option (.dsl .effect [e])) (Fo (instOfD m y)) (r.2.1.denote M) := by
      rintro ⟨sl, tmi⟩ ⟨q, xo, cq⟩ y hti hG hfl hE hcq
      exact fireAt_rel (T := T) m hfx recs tnow hrec hnow h2 h3 h5 hd hti y hfl hE (hfires y sl tmi hti hfl hE)
        (fun h => by simp only [Step.firesIn, Bool.and_eq_true] at h; exact h.2.1) hG hcq
    have hhits : AlignedV M (ETab L m.key m.state) (fun y v => v = .bool (Step.hitsAt recs dv (instOfD m y)))
        (St.map (·.1.slot)) (St.map fun (_, t) => hitT dopt dtm t d) sv ys :=
      aligned_mapView_mem (·.1.slot) (fun (p : InstSlot × Term) => hitT dopt dtm p.2 d)
        (fun p hp y hf h => (fire_item m h2 h3 recs hd y p.1 p.2 hf h (hT p hp)).2.1) hS hh
    have hany : (anySlotT (St.map (·.1.slot)) (St.map fun (_, t) => hitT dopt dtm t d)).denote M =
        .bool ((instancesOf T m tbl).any (Step.hitsAt recs dv)) := by
      rw [anySlotT_den hhits, ← perm_any hperm, List.any_map]; rfl
    have hal : AlignedV M (ETab L m.key m.state)
        (fun y v => RelV L m.state (Ty.up _ m.state_data (F (instOfD m y)).state) v) (St.map (·.1.slot))
        (outs.map (·.1)) sv ys := by
      have := aligned_of (fun sl r => ∃ s : InstSlot × Term, TimerOk M L m recs s.1 s.2 ∧ s.1.slot = sl ∧ ∃ o,
        fireAt L T m fx dopt dtm St done d records now (.ctor deff 1 []) s = .ok o ∧ r = (o.1, o.2.2))
        (V := fun y v => RelV L m.state (Ty.up _ m.state_data (F (instOfD m y)).state) v)
        (fun sl r y hG hfl hE hcq => by
          obtain ⟨s, hti, rfl, o', hG, rfl⟩ := hG
          exact (hslot s o' y hti hG hfl hE hcq).1) hS hh
        (forall2_map (·.1.slot) (fun s r h => ⟨s, h.1, rfl, h.2⟩)
          (forall2_and_left (forall2_mapM_map _ _ h7) hT)) (hguard _)
      rwa [List.map_map] at this
    have halx : AlignedV M (ETab L m.key m.state)
        (fun y v => RelV L (Ty.option (.dsl .effect [e])) (Fo (instOfD m y)) v) (St.map (·.1.slot))
        (outs.map (·.2.1)) sv ys := by
      have := aligned_of (fun sl r => ∃ s : InstSlot × Term, TimerOk M L m recs s.1 s.2 ∧ s.1.slot = sl ∧ ∃ o,
        fireAt L T m fx dopt dtm St done d records now (.ctor deff 1 []) s = .ok o ∧ r = (o.2.1, o.2.2))
        (V := fun y v => RelV L (Ty.option (.dsl .effect [e])) (Fo (instOfD m y)) v)
        (fun sl r y hG hfl hE hcq => by
          obtain ⟨s, hti, rfl, o', hG, rfl⟩ := hG
          exact (hslot s o' y hti hG hfl hE hcq).2) hS hh
        (forall2_map (·.1.slot) (fun s r h => ⟨s, h.1, rfl, h.2⟩)
          (forall2_and_left (forall2_mapM_map _ _ h7) hT)) (hguard _)
      rwa [List.map_map] at this
    have hkeyrel : ∀ y (s : InstSlot × Term), ETab L m.key m.state y (Term.denotes M s.1.slot.2.1) →
        RelV L m.key y.1 (s.1.key.denote M) := by
      rintro y ⟨⟨f, xk, xe⟩, tmi⟩ ⟨zk, zv, hvs, hk, -⟩
      simp only [InstSlot.slot, Term.denotes, List.cons.injEq, and_true] at hvs
      exact hvs.1 ▸ hk
    refine ⟨?_, hany, ?_⟩
    · let g : m.key.den × m.state.den → m.key.den × m.state.den :=
        fun y => (y.1, Ty.up _ m.state_data (F (instOfD m y)).state)
      obtain ⟨sv', hS', hl', hw', hh'⟩ := zipView_den (E' := ETab L m.key m.state) g (·.1.slot)
        InstSlot.slot (fun s q => { s.1 with entry := q }) (fun _ _ => rfl)
        (fun y s q h hq => ⟨_, _, rfl, hkeyrel y s h, hq⟩) hal
      have hkey : ∀ i, (F i).key = i.key := fun i => by
        simp only [F]; split
        · exact Step.fired_key m recs tnow i
        · rfl
      have hOk := instancesOk_map m (instancesOf_ok (T := T) m tbl) F hkey
      refine ⟨m.tableOf ((instancesOf T m tbl).map F) hOk.2, ?_, instancesOf_entries T m _ hOk⟩
      refine table_mk h1 hS' (hl'.trans hl) hw' ?_ hh'
      · have hup : (Ty.up _ m.table_data (m.tableOf ((instancesOf T m tbl).map F) hOk.2)).1 =
            (instEntries m ((instancesOf T m tbl).map F)).map
              fun p => (Ty.up _ m.key_data p.1, Ty.up _ m.state_data p.2) :=
          Ty.up_table m.key m.state m.table_data m.key_data m.state_data _
        rw [hup]
        have hg : ys.map g = (ys.map (instOfD m)).map fun i =>
            (Ty.up _ m.key_data (F i).key, Ty.up _ m.state_data (F i).state) := by
          rw [List.map_map]
          refine List.map_congr_left fun y _ => ?_
          simp only [Function.comp_apply, g, hkey]
          rw [show (instOfD m y).key = Ty.down _ m.key_data y.1 from rfl, Ty.up_down]
        rw [hg]
        refine (hperm.map _).trans (.of_eq ?_)
        simp only [instEntries, List.map_map]
        rfl
    · obtain ⟨svX, hSX, -, -, hhX⟩ := zipView_den (E' := EOpt (L := L) m Step.Instance.key Fo) (instOfD m)
        (·.1.slot) StartSlot.slot (fun s q => (⟨s.1.flag, s.1.key, q⟩ : StartSlot)) (fun _ _ => rfl)
        (fun y s q h hq => ⟨_, _, rfl, (Ty.up_down _ m.key_data y.1).symm ▸ hkeyrel y s h, hq⟩) halx
      exact ⟨svX, ys.map (instOfD m), hSX, hhX, hperm⟩
end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- A table's timers: the condition holds exactly when `timer` fits at every instance, and wherever it holds each
occupied slot's timer term denotes the timer its instance waits for at the records. -/
theorem timers_encode (m : MachineV r e)
    {tc : Code (Ty.fn [Ty.timerCtx m.key m.state r] (Ty.option (Ty.timer m.state)))} {c0 : Term}
    (htc : m.timer.code L = .ok (tc, c0)) (hc0 : Holds M c0) (recs : r.den0) {records : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {tms : List Term} {c : Term} (henc : encodeTimers L m tc x records = .ok (tms, c)) :
    (Holds M c ↔ ∀ i ∈ instancesOf T m tbl, m.timer.appFits L.count (.inl (i.key, i.state, recs, ()), ())) ∧
    (Holds M c → ∀ dd n dt, collD L m.table [m.key, m.state] = .ok (dd, n, dt) →
      Forall2 (TimerOk M L m recs) (instSlotsOf dd dt n x) tms) := by
  obtain ⟨⟨dd, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨outs, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have htbl' : Smt.Rel M L (.table m.key m.state) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS, -, -, hp, hh⟩ := table_view htbl' h1
  rw [← instSlotsOf_slot] at hS
  have hperm : (ys.map (instOfD m)).Perm (instancesOf T m tbl) := instancesOf_perm m tbl hp
  have hctx : ∀ t ∈ [Ty.timerCtx m.key m.state r], t.isFn = false := by simp [Ty.timerCtx, Ty.isFn]
  have hrec' : RelV L r (Ty.up _ m.records_data recs) (records.denote M) := hrec
  -- What one slot's terms say of the instance it holds.
  have hslot : ∀ (sl : InstSlot) (q : Term × Term) (y : m.key.den × m.state.den),
      timerSlot L m tc records sl = .ok q → ETab L m.key m.state y (Term.denotes M sl.slot.2.1) →
      ∃ (cx : Code _) (a : Code (Ty.option (Ty.timer m.state))) (c1 at_ : Term), Smt.Rel M L _ (Ty.up _ m.tctx_data (.inl ((instOfD m y).key, (instOfD m y).state, recs, ())))
        cx ∧ tc (cx, ()) = .ok (a, c1) ∧ Code.dataTermE _ a = .ok at_ ∧ q = (Term.share at_, Term.ite sl.flag c1 tt) := by
    rintro ⟨f, key, st⟩ q y hq ⟨zk, zv, hvs, hk, hv⟩
    simp only [InstSlot.slot, Term.denotes, List.cons.injEq, and_true] at hvs
    obtain ⟨hxk, hxs⟩ := hvs
    obtain ⟨ctxT, g1, hq⟩ := bind_ok.1 hq
    obtain ⟨cx, g2, hq⟩ := bind_ok.1 hq
    obtain ⟨⟨a, c1⟩, g3, hq⟩ := bind_ok.1 hq
    obtain ⟨at_, g4, hq⟩ := bind_ok.1 hq
    cases pure_ok.1 hq
    refine ⟨cx, a, c1, at_, ?_, g3, g4, rfl⟩
    have hku : Ty.up _ m.key_data (instOfD m y).key = y.1 := Ty.up_down _ _ _
    have hsu : Ty.up _ m.state_data (instOfD m y).state = y.2 := Ty.up_down _ _ _
    exact tctx_rel m (hku ▸ hxk ▸ hk) (hsu ▸ hxs ▸ hv) hrec' g1 (need_ok.1 g2)
  refine ⟨?_, fun hc dd' n' dt' hcol => ?_⟩
  · have hF : Forall2 (fun sl c' => ∃ s, s.slot = sl ∧ ∃ q1, timerSlot L m tc records s = .ok (q1, c'))
        ((instSlotsOf dd dt n x).map InstSlot.slot) (outs.map (·.2)) :=
      forall2_map _ (fun s c h => ⟨s, rfl, h⟩) (forall2_snd (mapM_ok _ _ _ h2))
    rw [allT_slots_exact (P := fun y => m.timer.appFits L.count
      (.inl ((instOfD m y).key, (instOfD m y).state, recs, ()), ())) _ ?_ hS hh hF]
    · constructor
      · intro h i hi
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hperm.mem_iff.2 hi)
        exact h y hy
      · intro h y hy
        exact h (instOfD m y) (hperm.mem_iff.1 (List.mem_map.2 ⟨y, hy, rfl⟩))
    · rintro _ cj ⟨sl, rfl, q1, hg⟩
      refine ⟨fun hf => ?_, fun y hf hey => ?_⟩
      · obtain ⟨f, key, st⟩ := sl
        obtain ⟨_, _, hg⟩ := bind_ok.1 hg
        obtain ⟨_, _, hg⟩ := bind_ok.1 hg
        obtain ⟨_, _, hg⟩ := bind_ok.1 hg
        obtain ⟨_, _, hg⟩ := bind_ok.1 hg
        cases pure_ok.1 hg
        simp only [InstSlot.slot] at hf
        simp [holds_ite, hf, Val.toBool, holds_tt]
      · obtain ⟨cx, a, c1, at_, hcx, g3, -, hq⟩ := hslot sl _ y hg hey
        simp only [Prod.mk.injEq] at hq
        rw [hq.2]
        have hf' : sl.flag.denote M = .bool true := hf
        rw [show Holds M (Term.ite sl.flag c1 tt) ↔ Holds M c1 by simp [holds_ite, hf', Val.toBool]]
        exact m.timer.app_exact htc hc0 hctx _ _ (tctx_rels m hcx _) g3
  · rw [h1] at hcol
    cases hcol
    have hall : ∀ q ∈ outs, Holds M q.2 := fun q hq => (holds_allT _).1 hc q.2 (List.mem_map.2 ⟨q, hq, rfl⟩)
    have hF := forall2_flip (forall2_and_left (forall2_flip (mapM_ok _ _ _ h2)) hall)
    refine forall2_map_right (·.1) (fun sl q ⟨hcq, hg⟩ => ?_) hF
    intro hfl y hey
    obtain ⟨cx, a, c1, at_, hcx, g3, g4, hq⟩ := hslot sl q y hg hey
    subst hq
    have hc1 : Holds M c1 := by
      have := hcq; simp only at this; simpa [holds_ite, hfl, Val.toBool] using this
    have ha := timer_app m (m.timer.code_fn m.timer.ht htc hc0) hcx g3 hc1
    rw [Term.denote_share]
    exact (rel_term (need_ok.1 g4) _).1 ha

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
    {insts : List (Step.Instance m)} (h : InstancesOk T m insts) {ms : List (MachineV r e)} (rest : Step.Machines ms) :
    Step.fireMachines recs now d b (.cons insts rest) =
      (.cons (insts.map fun i => if !b && Step.firesIn T m recs d insts i then (Step.fired m recs now i).1 else i)
          (Step.fireMachines recs now d (b || insts.any (Step.hitsAt recs d)) rest).1,
        insts.flatMap (fun i => (sentBy m Step.Instance.key
          (fun i => firedOpt m recs now (!b && Step.firesIn T m recs d insts i) i) i).toList) ++
          (Step.fireMachines recs now d (b || insts.any (Step.hitsAt recs d)) rest).2.1,
        (Step.fireMachines recs now d (b || insts.any (Step.hitsAt recs d)) rest).2.2) := by
  cases b with
  | true =>
    have hmap : (insts.map fun i => if (!true && Step.firesIn T m recs d insts i) = true then (Step.fired m recs now i).1 else i) =
        insts := by
      conv => rhs; rw [← List.map_id insts]
      exact List.map_congr_left fun i _ => by simp
    have hnil : (insts.flatMap fun i => (sentBy m Step.Instance.key
        (fun i => firedOpt m recs now (!true && Step.firesIn T m recs d insts i) i) i).toList) = [] :=
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
    cases hf : Step.firesIn T m recs d insts i with
    | false => simp only [hf, Bool.false_eq_true, ite_false, firedOpt_false, sentBy]; rfl
    | true =>
      cases ht : Step.timerOf recs i with
      | none => simp [Step.firesIn, Step.hitsAt, ht] at hf
      | some p =>
        obtain ⟨dl, tg⟩ := p
        have h1 : (Step.fired m recs now i).2 =
            (m.effectAt i.key tg recs now).toList.map (.machine m.name ⟨m.key, i.key⟩, ·) := by
          unfold Step.fired; rw [ht]; rfl
        have h2 : firedOpt m recs now true i = m.effect.apply (.inl (i.key, tg, recs, now, ()), ()) := by
          unfold firedOpt; rw [ht]
        simp only [↓reduceIte]
        rw [h1]
        unfold sentBy
        simp only [hf, h2]
        unfold MachineV.effectAt
        generalize Ty.toOption _ = o
        cases o <;> rfl

end

end Tazuna.Smt
