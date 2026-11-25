import Tazuna.Smt.Fire
import Tazuna.Smt.Finish

/-! A clock line's step. Time moves to the line's time, then rounds fire, at most `cascade + 1`:
each round finds the earliest deadline among the due timers of every machine (`minDueT`, a fold over all slots, so
the order of slots does not matter), then the machines in order fire their first instance at that deadline, each
unless an earlier machine fired (`encodeFires`, the done flag threading `Step.fireMachines`). A round with no due
timer, and every round after it, changes nothing. When every round fires the step exceeds the cascade bound. A round
fires one instance, so it starts at most one effect, which takes the round's next id (`roundStarts`); the requests are
written into the pending table in round order.

The condition is exact (run-log entry 63): it fails only where a function the step really applies outgrows a slot
count. Every round asks for each machine's `after` and `effect` sources, and for both applied where an instance fires;
the step's end asks what `finishFits` says. Rounds past the first that fired nothing, and everything after a step that
exceeds the cascade bound, ask nothing. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {M : Model} {r e : Ty}

/-- An entry's timer terms: whether it has a timer, and its deadline. -/
theorem timer_view (m : MachineV r e) {dent n dp np : Nat}
    (hdent : L.find? (Ty.option (.tuple [.int, m.state])) = some (dent, n)) (hdp : L.find? (.tuple [.int, m.state]) = some (dp, np))
    (i : Step.Instance m) {tm : Term}
    (ht : RelV L _ (Ty.up _ m.timer_data (timerVal i.timer)) (tm.denote M)) :
    (Term.is dent 0 tm).denote M = .bool i.timer.isSome ∧
      ∀ dl tg, i.timer = some (dl, tg) → (Term.sel dp 0 0 (Term.sel dent 0 0 tm)).denote M = .int dl := by
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
    obtain ⟨vd, vs7, rfl, hvd, -⟩ := hvals7
    change vd = .int dl at hvd
    subst hvd
    refine ⟨by simp [Term.denote, hv], fun dl' tg' h => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Term.denote, hv, hv7]
  | none =>
    change RelAlts L d' 0 _ (Ty.up _ m.timer_data (.inr (.inl ()))) _ at hra
    erw [Ty.up_inr 3 _ [.tuple [.int, m.state]] [[]] m.timer_data hnone', Ty.up_inl 3 _ [] [] hnone' rfl] at hra
    obtain ⟨vals, hv, -⟩ := hra
    exact ⟨by simp [Term.denote, hv], fun _ _ h => nomatch h⟩

end

/-! The earliest due deadline. -/

/-- The deadline of an instance's timer where it is due at `now`. -/
def dueOf {r e : Ty} {m : MachineV r e} (now : Int) (i : Step.Instance m) : Option Int :=
  i.timer.bind fun (d, _) => if d ≤ now then some d else none

/-- Per slot of a table, whether it holds a timer due at `now`, and its deadline. -/
def dueSlots (de dent dp : Nat) (So : List InstSlot) (now : Term) : List (Term × Term) :=
  So.map fun ⟨f, _, entry⟩ =>
    let tm := Term.sel de 0 1 entry
    let dl := Term.sel dp 0 0 (Term.sel dent 0 0 tm)
    (.and f (.and (.is dent 0 tm) (.le dl now)), dl)

/-- Whether some slot is due, and the least deadline among the due ones. -/
def minDueT : List (Term × Term) → Term × Term
  | [] => (.bool false, .int 0)
  | (u, x) :: rest =>
    let h := Term.share (minDueT rest).1
    let v := Term.share (minDueT rest).2
    (.or u h, .ite (.and u (.or (.not h) (.lt x v))) x v)

section
variable {M : Model}

/-- A slot's due term and deadline denote the option `o`: due exactly when it holds a deadline, which is then the
deadline term's value. -/
def DueRel (M : Model) (t : Term × Term) (o : Option Int) : Prop :=
  t.1.denote M = .bool o.isSome ∧ ∀ d, o = some d → t.2.denote M = .int d

theorem foldl_min_assoc (a : Int) : (l : List Int) → (c : Int) → l.foldl min (min a c) = min a (l.foldl min c)
  | [], _ => rfl
  | x :: l, c => by simp only [List.foldl_cons]; rw [Int.min_assoc, foldl_min_assoc a l]

theorem minDue_int : {ts : List (Term × Term)} → {os : List (Option Int)} → Forall2 (DueRel M) ts os →
    ∃ dv, (minDueT ts).2.denote M = .int dv
  | [], [], _ => ⟨0, rfl⟩
  | (u, x) :: ts, o :: os, ⟨⟨hu, hx⟩, hs⟩ => by
    obtain ⟨dv, hdv⟩ := minDue_int hs
    have hite : ∀ c a b : Term, (Term.ite c a b).denote M = if (c.denote M).toBool then a.denote M else b.denote M :=
      fun _ _ _ => rfl
    simp only [minDueT]
    rw [hite]
    cases o with
    | none => simp only [Term.denote, hu, Val.toBool, Option.isSome_none, Bool.false_and]; exact ⟨dv, by simpa using hdv⟩
    | some a =>
      split
      · exact ⟨a, hx a rfl⟩
      · exact ⟨dv, by simpa using hdv⟩

theorem minDue_den : {ts : List (Term × Term)} → {os : List (Option Int)} → Forall2 (DueRel M) ts os →
    (minDueT ts).1.denote M = .bool (os.filterMap id).min?.isSome ∧
      ∀ d, (os.filterMap id).min? = some d → (minDueT ts).2.denote M = .int d
  | [], [], _ => ⟨rfl, fun _ h => nomatch h⟩
  | (u, x) :: ts, o :: os, ⟨⟨hu, hx⟩, hs⟩ => by
    obtain ⟨h1, h2⟩ := minDue_den hs
    simp only [minDueT]
    have hor : ∀ a b : Term, (Term.or a b).denote M = .bool ((a.denote M).toBool || (b.denote M).toBool) := fun _ _ => rfl
    have hite : ∀ c a b : Term, (Term.ite c a b).denote M = if (c.denote M).toBool then a.denote M else b.denote M :=
      fun _ _ _ => rfl
    cases o with
    | none =>
      simp only [List.filterMap_cons, id, Option.isSome_none] at hu ⊢
      refine ⟨by rw [hor, hu, Term.denote_share, h1]; simp [Val.toBool], fun d hd => ?_⟩
      rw [hite]
      simp only [Term.denote, hu, Val.toBool, Bool.false_and, Bool.false_eq_true, ite_false, Term.denote_share]
      exact h2 d hd
    | some a =>
      simp only [List.filterMap_cons, id, Option.isSome_some] at hu ⊢
      refine ⟨by rw [hor, hu]; simp [Val.toBool, List.min?], fun d hd => ?_⟩
      have hxa := hx a rfl
      rw [hite]
      simp only [Term.denote, hu, Val.toBool, Bool.true_and, Term.denote_share]
      cases hrest : (os.filterMap id).min? with
      | none =>
        have hnil : os.filterMap id = [] := List.min?_eq_none_iff.1 hrest
        rw [hnil] at hd
        simp only [List.min?, Option.some.injEq] at hd
        subst hd
        rw [h1, hrest]
        simp [hxa]
      | some b =>
        have hb := h2 b hrest
        rw [h1, hrest, hb]
        have hne : os.filterMap id ≠ [] := fun h => by rw [h] at hrest; cases hrest
        obtain ⟨c, l, hcl⟩ := List.exists_cons_of_ne_nil hne
        rw [hcl] at hrest hd
        have hmin : d = min a b := by
          simp only [List.min?, Option.some.injEq] at hrest hd
          rw [← hd, ← hrest, List.foldl_cons, foldl_min_assoc]
        subst hmin
        rw [hxa]
        by_cases hab : a < b
        · simp [Val.toInt, hab, Int.min_def, Int.le_of_lt hab]
        · have : min a b = b := Int.min_eq_right (by omega)
          simp [Val.toInt, hab, this]

theorem min?_perm {l l' : List Int} (h : l.Perm l') : l.min? = l'.min? := by
  cases hl : l.min? with
  | none =>
    have : l = [] := List.min?_eq_none_iff.1 hl
    subst this
    rw [List.perm_nil.1 h.symm]; rfl
  | some a =>
    obtain ⟨h1, h2⟩ := List.min?_eq_some_iff.1 hl
    exact (List.min?_eq_some_iff.2 ⟨h.mem_iff.1 h1, fun b hb => h2 b (h.mem_iff.2 hb)⟩).symm

end

section
variable {L : Layout} {M : Model} {r e : Ty}

/-- The timer term of a table slot denotes the timer of the instance it holds. -/
theorem item_timer (m : MachineV r e) {de nde : Nat} (hde : L.find? (instEntry m.state) = some (de, nde))
    (y : m.key.den × (instEntry m.state).den) (sl : InstSlot)
    (h : ETab L m.key (instEntry m.state) y (Term.denotes M sl.slot.2.1)) :
    RelV L _ (Ty.up _ m.timer_data (timerVal (instOfD m y).timer)) ((Term.sel de 0 1 sl.entry).denote M) := by
  obtain ⟨zk, zv, hvs, hk, hv⟩ := h
  obtain ⟨f, xk, xe⟩ := sl
  simp only [InstSlot.slot, Term.denotes, List.cons.injEq, and_true] at hvs
  obtain ⟨hxk, hxe⟩ := hvs
  have hy2 : Ty.up _ m.entry_data (Ty.down _ m.entry_data y.2) = y.2 := Ty.up_down _ _ _
  generalize hz : Ty.down _ m.entry_data y.2 = z at hy2
  obtain ⟨st, t, u⟩ := z
  cases u
  have hinst : instOfD m y = ⟨Ty.down _ m.key_data y.1, st, timerOf t⟩ := by simp [instOfD, instOf, hz]
  rw [← hy2] at hv
  obtain ⟨v0, v1, hzv, -, hv1⟩ := (entry_rel_iff m hde st t zv).1 hv
  have hsel : (Term.sel de 0 1 xe).denote M = v1 := by rw [sel_ctor 1 (hxe.trans hzv)]; rfl
  rw [hsel, hinst]; simpa [val_timerOf] using hv1

/-- The due terms of a table's slots denote, slot by slot, the due deadlines of the instances they hold. -/
theorem dueSlots_rel (m : MachineV r e) {de nde dent nent dp np : Nat} (hde : L.find? (instEntry m.state) = some (de, nde))
    (hdent : L.find? (Ty.option (.tuple [.int, m.state])) = some (dent, nent))
    (hdp : L.find? (.tuple [.int, m.state]) = some (dp, np)) {now : Term} {tnow : Int} (hnow : now.denote M = .int tnow) :
    {So : List InstSlot} → {sv : List (Bool × List Val)} → {ys : List (m.key.den × (instEntry m.state).den)} →
    SlotsDen M (So.map InstSlot.slot) sv → Holds2 (ETab L m.key (instEntry m.state)) ys sv →
    ∃ os, Forall2 (DueRel M) (dueSlots de dent dp So now) os ∧
      os.filterMap id = (ys.map (instOfD m)).filterMap (dueOf tnow)
  | [], [], ys, _, hy => by
    cases ys with
    | nil => exact ⟨[], trivial, rfl⟩
    | cons _ _ => exact hy.elim
  | ⟨f, tk, te⟩ :: So, (b, vs) :: sv, ys, ⟨hf, hx, hS⟩, hy => by
    have hand : ∀ a c : Term, (Term.and a c).denote M = .bool ((a.denote M).toBool && (c.denote M).toBool) :=
      fun _ _ => rfl
    cases b with
    | false =>
      obtain ⟨os, h1, h2⟩ := dueSlots_rel m hde hdent hdp hnow hS (by simpa [Holds2, occupied] using hy)
      refine ⟨none :: os, ⟨⟨?_, fun _ h => nomatch h⟩, h1⟩, by simpa using h2⟩
      show (Term.and f _).denote M = _
      rw [hand, hf]; rfl
    | true =>
      match ys, hy with
      | y :: ys, ⟨hey, hy⟩ =>
        obtain ⟨os, h1, h2⟩ := dueSlots_rel m hde hdent hdp hnow hS hy
        have ht := item_timer m hde y ⟨f, tk, te⟩ (hx ▸ hey)
        obtain ⟨his, hdl⟩ := timer_view m hdent hdp (instOfD m y) ht
        refine ⟨dueOf tnow (instOfD m y) :: os, ⟨⟨?_, fun d hd => ?_⟩, h1⟩, ?_⟩
        · show (Term.and f (.and (.is dent 0 _) (.le _ now))).denote M = _
          rw [hand, hand, hf, his]
          unfold dueOf
          cases htm : (instOfD m y).timer with
          | none => simp [Val.toBool]
          | some p =>
            obtain ⟨dl, tg⟩ := p
            have hX := hdl dl tg htm
            generalize Term.sel dp 0 0 (Term.sel dent 0 0 (Term.sel de 0 1 te)) = X at hX ⊢
            simp only [Term.denote, hX, hnow, Val.toBool, Val.toInt, Option.isSome_some, Bool.true_and,
              Option.bind_some]
            by_cases hle : dl ≤ tnow <;> simp [hle]
        · unfold dueOf at hd
          cases htm : (instOfD m y).timer with
          | none => rw [htm] at hd; cases hd
          | some p =>
            obtain ⟨dl, tg⟩ := p
            rw [htm] at hd
            simp only [Option.bind_some] at hd
            split at hd
            · cases hd; exact hdl _ _ htm
            · cases hd
        · simp only [List.filterMap_cons, id, List.map_cons, h2]
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

end

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- Every machine's part of a firing round, machines in order: each fires unless `done`, and passes on whether some
machine so far has an instance with the deadline. -/
def encodeFires : (ms : List (MachineV r e)) → PerMachine (fun _ => Term) ms → (done d records now : Term) →
    Except Refusal (PerMachine (fun _ => FireOut) ms × Term)
  | [], .nil, _, _, _, _ => pure (.nil, tt)
  | m :: ms, .cons x xs, done, d, records, now => do
    let (af, c0) ← m.after.code L
    let (fx, c1) ← m.effect.code L
    let (o, c) ← encodeFire L T m af fx x done d records now
    let (os, cs) ← encodeFires ms xs (.share (.or done o.hit)) d records now
    pure (.cons o os, andT c0 (andT c1 (andT c cs)))

/-- The due slots of every machine's table, machines in order. -/
def dueAll : (ms : List (MachineV r e)) → PerMachine (fun _ => Term) ms → Term → Except Refusal (List (Term × Term))
  | [], .nil, _ => pure []
  | m :: ms, .cons x xs, now => do
    let (dd, n, dt) ← collD L m.table [m.key, instEntry m.state]
    let de ← tupleD L [m.state, Ty.option (.tuple [.int, m.state])]
    let (dent, _) ← L.findE (Ty.option (.tuple [.int, m.state]))
    let dp ← tupleD L [.int, m.state]
    let rest ← dueAll ms xs now
    pure (dueSlots de dent dp (instSlotsOf dd dt n x) now ++ rest)

/-- What a firing round encodes: every machine's part, and whether the round fires (it is active and some timer is
due). -/
structure RoundOut (ms : List (MachineV r e)) where
  fires : PerMachine (fun _ => FireOut) ms
  go : Term

/-- One firing round, where `active`: at the earliest due deadline, every machine's part in order. A round that is
not active, or has no due timer, fires nothing. -/
def encodeRound (ms : List (MachineV r e)) (xs : PerMachine (fun _ => Term) ms) (active records now : Term) :
    Except Refusal (RoundOut ms × Term) := do
  let dues ← dueAll L ms xs now
  let go := Term.share (.and active (minDueT dues).1)
  let (os, c) ← encodeFires L T ms xs (.not go) (Term.share (minDueT dues).2) records now
  pure (⟨os, go⟩, c)

end

/-- A round where `active`: no due timer fires nothing, else `Step.fireMachines` at the earliest due deadline. -/
def _root_.Tazuna.Ir.Step.roundOf {r e : Ty} (recs : r.den0) (now : Int) (active : Bool) {ms : List (MachineV r e)}
    (sms : Step.Machines ms) : Step.Machines ms × List (Sender × EffectV e) :=
  if active then
    match (Step.dues sms.toSigma now).min? with
    | none => (sms, [])
    | some d => let x := Step.fireMachines recs now d false sms; (x.1, x.2.1)
  else (sms, [])

theorem roundOf_effs {r e : Ty} (recs : r.den0) (now : Int) (active : Bool) {ms : List (MachineV r e)}
    (sms : Step.Machines ms) :
    (Step.roundOf recs now active sms).2.length ≤ 1 := by
  unfold Step.roundOf
  split
  · split
    · simp
    · exact Step.fireMachines_effs recs now _ false sms
  · simp

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- The due terms of every machine's table denote the due deadlines of the machines' instances, in some order. -/
theorem dueAll_rel {now : Term} {tnow : Int} (hnow : now.denote M = .int tnow) :
    (ms : List (MachineV v.records v.event)) → (xs : PerMachine (fun _ => Term) ms) → (sms : Step.Machines ms) →
    MachinesRel M L T ms xs sms → {dues : List (Term × Term)} → dueAll L ms xs now = .ok dues →
    ∃ os, Forall2 (DueRel M) dues os ∧ (os.filterMap id).Perm (Step.dues sms.toSigma tnow)
  | [], .nil, .nil, _, dues, henc => by
    simp only [dueAll, pure, Except.pure, Except.ok.injEq] at henc
    subst henc
    exact ⟨[], trivial, by simp [Step.dues]⟩
  | m :: ms, .cons x xs, .cons insts sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, dues, henc => by
    obtain ⟨⟨dd, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨de, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨dent, nent⟩, h3, henc⟩ := bind_ok.1 henc
    obtain ⟨dp, h4, henc⟩ := bind_ok.1 henc
    obtain ⟨rest, h5, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    subst hsm
    obtain ⟨nde, hde⟩ := tupleD_ok h2
    obtain ⟨ndp, hdp⟩ := tupleD_ok h4
    have htbl' : Smt.Rel M L (.table m.key (instEntry m.state)) (Ty.up _ m.table_data tbl) x := htbl
    obtain ⟨sv, ys, hS, -, -, hp, hh⟩ := table_view htbl' h1
    rw [← instSlotsOf_slot] at hS
    have hperm : (ys.map (instOfD m)).Perm (instancesOf T m tbl) := instancesOf_perm m tbl hp
    obtain ⟨os1, hf1, he1⟩ := dueSlots_rel m hde (need_ok.1 h3) hdp hnow hS hh
    obtain ⟨os2, hf2, he2⟩ := dueAll_rel hnow ms xs sms hrest h5
    refine ⟨os1 ++ os2, forall2_append hf1 hf2, ?_⟩
    rw [List.filterMap_append, he1]
    exact (hperm.filterMap _).append he2

end

section
variable {P : List AnySite} {E : List AnyEffectSite} {r e : Ty}

theorem roundOf_reach (recs : r.den0) (now : Int) (ab : Bool) {ms : List (MachineV r e)} (sms : Step.Machines ms)
    (h : ∀ m ∈ ms, m.Reach P E) : Step.EffsReach P (Step.roundOf recs now ab sms).2 := by
  unfold Step.roundOf
  split
  · split
    · exact fun _ h => nomatch h
    · rename_i d _
      intro x hx
      obtain ⟨sm, hsm, k, st, hx⟩ := Step.mem_fireMachines_effs recs now d false sms x hx
      exact Step.enter_reach sm.1 (h _ (PerMachine.fst_mem hsm)) _ _ _ _ x hx
  · exact fun _ h => nomatch h

theorem roundOf_from {v : ServiceV} (recs : v.records.den0) (now : Int) (ab : Bool) (sms : Step.Machines v.machines)
    (h : ∀ m ∈ v.machines, m.Reach P E) : Step.EffsFrom v (Step.roundOf recs now ab sms).2 := by
  unfold Step.roundOf
  split
  · split
    · exact fun _ h => nomatch h
    · rename_i d _
      intro x hx
      obtain ⟨sm, hsm, k, st, hx⟩ := Step.mem_fireMachines_effs recs now d false sms x hx
      exact Step.enter_from (PerMachine.fst_mem hsm) (h _ (PerMachine.fst_mem hsm)) _ _ _ _ x hx
  · exact fun _ h => nomatch h

end

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- What the firing rounds encode: the final instance tables, the pending slots of the requests the rounds start (each
round's wire ids after the earlier rounds'), the next wire id after them, whether every round fired, and the own
slots of the own commands and queries the rounds queue with the queue place after them. -/
structure RoundsOut (ms : List (MachineV r e)) where
  tables : PerMachine (fun _ => Term) ms
  news : List PendingSlot
  nextId : Term
  over : Term
  owns : List OwnSlot
  queued : Term

/-- The pending slots of the requests a round's start slots start, machine by machine, with how many, and the own
slots of the own commands and queries they queue, with how many. A round fires at most one instance, so every request
slot takes the round's next id `nid` and every own slot the round's queue place `q`. -/
def roundStarts (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (senv : StepEnv L shs) :
    (ms : List (MachineV r e)) → PerMachine (fun _ => List StartSlot) ms → (nid q : Term) →
    Except Refusal (List PendingSlot × Term × List OwnSlot × Term)
  | [], .nil, _, _ => pure ([], .int 0, [], .int 0)
  | m :: ms, .cons st sts, nid, q => do
    let (dk, _) ← L.findE (.tuple [m.key])
    let js ← shapeIdxs shs ds ⟨[m.key], .machine m.name m.key⟩ (L.effectsOf e)
    let dflt ← defaultE L (pendingEntry shs)
    let sp := st.map (splitStart senv.dE (L.effectsOf e).length (L.ownsOf e).length senv.dopt)
    let rq := if (L.ownsOf e).isEmpty then st else sp.map (·.1)
    let oq := if (L.ownsOf e).isEmpty then [] else sp.map (·.2)
    let (rest, k, orest, ko) ← roundStarts shs ds senv ms sts nid q
    pure (entrySlots senv.dE senv.dP dk dflt js (rq.map (onceStart senv.dopt nid)) ++ rest, .add (startCount senv.dopt rq) k,
      ownItems (oq.map (onceStart senv.dopt q)) ++ orest, .add (startCount senv.dopt oq) ko)

/-- `k` firing rounds from the tables `xs`, the first where `active`, each next one where the one before fired. -/
def encodeRounds (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (senv : StepEnv L shs)
    (ms : List (MachineV r e)) (records now : Term) : Nat → PerMachine (fun _ => Term) ms → (active nid q : Term) →
    Except Refusal (RoundsOut ms × Term)
  | 0, xs, active, nid, q => pure (⟨xs, [], nid, active, [], q⟩, tt)
  | k + 1, xs, active, nid, q => do
    let (ro, c) ← encodeRound L T ms xs active records now
    let (news, n, owns, no) ← roundStarts L shs ds senv ms (ro.fires.map (·.starts)) nid q
    let (rest, c') ← encodeRounds shs ds senv ms records now k (ro.fires.map (·.table)) ro.go
      (.share (.add nid n)) (.share (.add q no))
    pure (⟨rest.tables, news ++ rest.news, rest.nextId, rest.over, owns ++ rest.owns, rest.queued⟩, andT c c')

end

/-- `Step.fire` where `active`; otherwise nothing fires. -/
def _root_.Tazuna.Ir.Step.fireFrom {v : ServiceV} (s : State v) (active : Bool) (k : Nat) :
    Option (State v × List (Sender × EffectV v.event)) :=
  if active then Step.fire s k else some (s, [])

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- A machine's own start slots where they start at most one effect: each flagged slot holds it at the queue place
`q0`. -/
theorem own_once (m : MachineV v.records v.event) {dopt nopt : Nat}
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt)) {ws : List StartSlot}
    {effs : List (Sender × EffectV v.event)} (h : StartSlots M L T m ws effs) (hone : effs.length ≤ 1) {q : Term}
    {q0 : Nat} (hq : q.denote M = .int (q0 : Int)) :
    (startCount dopt ws).denote M = .int effs.length ∧
      OwnRel M L (ownItems (ws.map (onceStart dopt q))) (effs.map (·.2)) q0 := by
  obtain ⟨α, κ, F, E, items, svX, hX, hh, hEp, -, rfl⟩ := h
  have hcount := startCount_den m hopt κ F hX hh hEp
  obtain ⟨svS, ys, hS', hyp, hy⟩ := once_starts m hopt κ F hX hh hEp hone hq
  refine ⟨hcount, ?_⟩
  obtain ⟨sv', zs, h1, -, h3, h4, h5⟩ := mapView_den (M := M) (Q := fun (y : (Sender × EffectV v.event) × Nat) z =>
    z = (y.1.2, y.2)) (E' := EOwn L v.event) RankedStart.slot OwnSlot.slot (fun s => ⟨s.flag, s.id, s.effect⟩)
    (fun _ => rfl) (by
      rintro ⟨⟨snd, eff⟩, id⟩ ⟨f, a, b, c⟩ ⟨k, zk, zx, hvs, -, -, hzx⟩
      simp only [RankedStart.slot, Term.denotes, List.cons.injEq, and_true] at hvs
      exact ⟨(eff, id), ⟨zx, by simp [OwnSlot.slot, Term.denotes, hvs.1, hvs.2.2], hzx⟩, rfl⟩) hS' hy
  have key : ∀ (ys : List ((Sender × EffectV v.event) × Nat)) (zs : List (EffectV v.event × Nat)),
      Forall2 (fun y z => z = (y.1.2, y.2)) ys zs → zs = ys.map fun y => (y.1.2, y.2) := by
    intro ys zs h
    induction ys generalizing zs with
    | nil => cases zs <;> simp_all [Forall2]
    | cons y ys ih => match zs, h with
      | z :: zs, ⟨hz, h⟩ => simp [hz, ih zs h]
  refine ⟨sv', zs, by simpa [ownItems, List.map_map, Function.comp_def] using h1, h3, h4, ?_⟩
  rw [key ys zs h5, List.zipIdx_map]
  exact hyp.map _

/-- T2 for a round's start slots: where they start at most one effect in all, the pending slots hold, where flagged,
the request for it at the id `nid`, the own slots the own command or query at the place `q`, and the count terms
denote how many of each there are. -/
theorem roundStarts_rel {P : List AnySite} (hP : SitesUnique P) {shs : List (PendingShape v.event)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)}
    (senv : StepEnv L shs) {nid q : Term} {n0 q0 : Nat}
    (hn : nid.denote M = .int n0) (hq : q.denote M = .int q0) :
    (ms : List (MachineV v.records v.event)) → (sts : PerMachine (fun _ => List StartSlot) ms) →
    (effss : PerMachine (fun _ => List (Sender × EffectV v.event)) ms) → StartsRel M L T ms sts effss →
    effss.toList.flatten.length ≤ 1 → (∀ x ∈ effss.toList.flatten, x.2.Reach P) →
    (∀ x ∈ effss.toList.flatten, ShapedFrom shs ds x.1 x.2) →
    {news : List PendingSlot} → {cnt : Term} → {owns : List OwnSlot} → {ocnt : Term} →
    roundStarts L shs ds senv ms sts nid q = .ok (news, cnt, owns, ocnt) →
    cnt.denote M = .int (Step.reqsOf effss.toList.flatten).length ∧
      NewsRel M L shs ds news (Step.reqsOf effss.toList.flatten) n0 ∧
      ocnt.denote M = .int (Step.queuedOf effss.toList.flatten).length ∧
      OwnRel M L owns (Step.queuedOf effss.toList.flatten) q0
  | [], .nil, .nil, _, _, _, _, news, cnt, owns, ocnt, henc => by
    simp only [roundStarts, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := henc
    exact ⟨rfl, ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩, rfl, ownRel_nil q0⟩
  | m :: ms, .cons st sts, .cons effs effss, ⟨hst, hrest⟩, hone, hreach, hshaped, news, cnt, owns, ocnt, henc => by
    obtain ⟨⟨dk, nk⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨js, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨dflt, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, k, orest, ko⟩, h3, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    rw [PerMachine.toList_cons, List.flatten_cons, List.length_append] at hone
    have hparts : StartSlots M L T m (if (L.ownsOf v.event).isEmpty then st else (st.map
          (splitStart senv.dE (L.effectsOf v.event).length (L.ownsOf v.event).length senv.dopt)).map (·.1)) (Step.reqsOf effs) ∧
        (startCount senv.dopt (if (L.ownsOf v.event).isEmpty then [] else (st.map
          (splitStart senv.dE (L.effectsOf v.event).length (L.ownsOf v.event).length senv.dopt)).map (·.2))).denote M =
          .int (Step.queuedOf effs).length ∧
        OwnRel M L (ownItems ((if (L.ownsOf v.event).isEmpty then [] else (st.map
          (splitStart senv.dE (L.effectsOf v.event).length (L.ownsOf v.event).length senv.dopt)).map (·.2)).map
          (onceStart senv.dopt q))) (Step.queuedOf effs) q0 := by
      by_cases ho : (L.ownsOf v.event).isEmpty
      · have hall := startSlots_requests (List.isEmpty_iff.1 ho) m hst
        have hr : Step.reqsOf effs = effs := List.filter_eq_self.2 hall
        have hq0 : Step.queuedOf effs = [] := by
          simp only [Step.queuedOf, List.map_eq_nil_iff, List.filter_eq_nil_iff]; intro x hx; simp [hall x hx]
        simp only [ho, ↓reduceIte]
        rw [hr, hq0]
        exact ⟨hst, rfl, ownRel_nil q0⟩
      · simp only [ho, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hreq, hown⟩ := startSlots_split senv.hE senv.hopt m hst
        have hlen : (effs.filter (!·.2.isRequest)).length ≤ 1 :=
          Nat.le_trans (List.length_filter_le _ _) (by omega)
        obtain ⟨hcO, hO⟩ := own_once m senv.hopt (by simpa only [List.map_map, Function.comp_def] using hown) hlen hq
        refine ⟨by simpa only [List.map_map, Function.comp_def] using hreq, ?_, ?_⟩
        · simpa only [List.map_map, Function.comp_def, Step.queuedOf, List.length_map] using hcO
        · simpa only [List.map_map, Function.comp_def, Step.queuedOf] using hO
    obtain ⟨hR, hcO, hO⟩ := hparts
    obtain ⟨α, κ, F, E, items, svX, hX, hh, hEp, _, heffs⟩ := hR
    have hcount := startCount_den m senv.hopt κ F hX hh hEp
    have hreqlen : (Step.reqsOf effs).length ≤ 1 := Nat.le_trans (List.length_filter_le _ _) (by omega)
    obtain ⟨svS, ys, hS, hyp, hy⟩ := once_starts m senv.hopt κ F hX hh hEp (heffs ▸ hreqlen) hn
    rw [← heffs] at hyp hcount
    have hmem : ∀ x ∈ ys, x.1 ∈ Step.reqsOf effs := fun x hx => List.fst_mem_of_mem_zipIdx (hyp.mem_iff.1 hx)
    have hr : ∀ x ∈ ys, x.1.2.Reach P := fun x hx => hreach x.1 (by simp [(List.mem_filter.1 (hmem x hx)).1])
    have hrq : ∀ x ∈ ys, x.1.2.isRequest = true := fun x hx => (List.mem_filter.1 (hmem x hx)).2
    have hat : ∀ x ∈ ys, ShapedFrom shs ds x.1.1 x.1.2 :=
      fun x hx => hshaped x.1 (by simp [(List.mem_filter.1 (hmem x hx)).1])
    obtain ⟨sv1, zs1, hS1, -, hw1, hh1, hq1⟩ :=
      entrySlots_rel hP m hshs h2 senv.hE senv.hPE (need_ok.1 h1) dflt hS hy hr hat hrq
    obtain ⟨hk, hnews, hko, hown⟩ := roundStarts_rel hP hshs senv hn hq ms sts effss hrest (by omega)
      (fun x h => hreach x (by simp [h])) (fun x h => hshaped x (by simp [h])) h3
    have hor : effs.length = 0 ∨ effss.toList.flatten.length = 0 := by omega
    simp only [Step.reqsOf, Step.queuedOf, PerMachine.toList_cons, List.flatten_cons, List.filter_append, List.map_append,
      List.length_append] at hk hnews hko hown ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Term.denote, hcount, hk, Val.toInt]; push_cast; rfl
    · have h1 : NewsRel M L shs ds _ (Step.reqsOf effs) n0 := ⟨sv1, zs1, hS1, hw1, hh1, ys, hyp, hq1⟩
      obtain ⟨a, b, c, d, e, f, g, h⟩ := hnews
      rcases hor with h0 | h0
      · rw [List.length_eq_zero_iff.1 h0] at h1 ⊢
        exact newsRel_append h1 ⟨a, b, c, d, e, f, g, h⟩
      · rw [List.length_eq_zero_iff.1 h0] at g ⊢
        exact newsRel_append h1 ⟨a, b, c, d, e, f, g, h⟩
    · simp only [Term.denote, hcO, hko, Val.toInt]; push_cast; rfl
    · rcases hor with h0 | h0
      · rw [List.length_eq_zero_iff.1 h0] at hO ⊢
        exact ownRel_append hO (by simpa using hown)
      · rw [List.length_eq_zero_iff.1 h0] at hown ⊢
        obtain ⟨a, b, c, d, e, f⟩ := hown
        exact ownRel_append hO ⟨a, b, c, d, e, by simpa using f⟩

end

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- What a clock line's step encodes: whether time moves forward, whether every round fired (the cascade bound is
exceeded), the firing rounds, and the step's end. -/
structure ClockOut (v : ServiceV) where
  forward : Term
  over : Term
  rounds : RoundsOut v.machines
  finish : FinishOut v

/-- A clock line's step from the state terms: `cascade + 1` firing rounds at the line's time `time`, then the step's end
from the requests and own effects the rounds start. Each part's condition is asked only where the step reaches it;
the second term is the codes' condition. -/
def encodeClock (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (invariants : Code (Ty.fn [v.records] Ty.rules))
    (S : SymState v) (time : Term) : Except Refusal (Encoded (ClockOut v)) := do
  let (ro, cr) ← encodeRounds L T shs v.declared senv v.machines S.records time (v.bounds.cascadeNat + 1) S.machines tt
    S.nextId (.int 0)
  let ⟨fo, cf, cfx⟩ ← encodeFinish L T P v shs senv apply invariants time S.fresh S.pending
    ⟨S.records, ro.tables, ro.nextId, ro.news, ro.owns, ro.queued⟩
  let forward := Term.le S.now time
  pure ⟨⟨forward, ro.over, ro, fo⟩, .ite forward (andT cr (.ite ro.over tt cf)) tt, cfx⟩

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- What the firing rounds leave, in the form the step's end continues: the requests among the effects written at the
next ids and the own commands and queries queued, from the state at the line's time. -/
theorem rounds_done {shs : List (PendingShape v.event)} (s : State v) (time : Int)
    {s' : State v} {effs : List (Sender × EffectV v.event)} (hs' : s' = { s with now := time, machines := s'.machines })
    {o : RoundsOut v.machines} {records fresh : Term} (hrec : RelV L v.records (Ty.up _ v.records_data s.records) (records.denote M))
    (hfresh : fresh.denote M = .int (Int.ofNat s.fresh)) (hms : MachinesRel M L T v.machines o.tables s'.machines)
    (hn : o.nextId.denote M = .int ((s.nextId + (Step.reqsOf effs).length : Nat) : Int))
    (hnews : NewsRel M L shs v.declared o.news (Step.reqsOf effs) s.nextId)
    (hq : o.queued.denote M = .int ((0 + (Step.queuedOf effs).length : Nat) : Int))
    (hown : OwnRel M L o.owns (Step.queuedOf effs) 0) :
    AccRel M L T shs { state := { s with now := time } } ⟨records, o.tables, o.nextId, o.news, o.owns, o.queued⟩ fresh 0
      (Step.start { state := s' } effs) := by
  refine ⟨s.records, s'.machines, s.fresh, [], Step.reqsOf effs, Step.queuedOf effs, fun ps hps => ?_, hrec, hms,
    hfresh, hn, hnews, by simpa using hq, by simpa using hown⟩
  have hn' : s'.nextId = s.nextId := by rw [hs']
  rw [Step.start_requests _ effs ps (by rw [hn']; exact hps)]
  have hl := forall2_zipIdx_length _ _ hps
  rw [hs']
  simp [Step.Acc.wrote, Step.Acc.queued, hl]

end

section
variable (S : Ty → Nat) (T : List TypeDecl) {r e : Ty}

/-- Whether a firing round's functions fit, machines in order: each machine's `after` and `effect` sources, and both
applied at the state the firing instance enters (none where an earlier machine fired). -/
def firesFit (recs : r.den0) (now d : Int) : Bool → {ms : List (MachineV r e)} → Step.Machines ms → Prop
  | _, _, .nil => True
  | b, m :: _, .cons insts rest => (m.after.fits S).1 ∧ (m.effect.fits S).1 ∧
      (∀ i ∈ insts, (!b && Step.firesIn T m d insts i) = true → ∀ dl tg, i.timer = some (dl, tg) →
        m.after.appFits S (.inl (i.key, tg, recs, now, ()), ()) ∧ m.effect.appFits S (.inl (i.key, tg, recs, now, ()), ())) ∧
      firesFit recs now d (b || insts.any (Step.hitsAt d)) rest

/-- Whether a round's functions fit: at the earliest due deadline where it is active and a timer is due, else only the
sources. -/
def roundFit (recs : r.den0) (now : Int) (ab : Bool) {ms : List (MachineV r e)} (sms : Step.Machines ms) : Prop :=
  match (if ab then (Step.dues sms.toSigma now).min? else none) with
  | some d => firesFit S T recs now d false sms
  | none => firesFit S T recs now 0 true sms

/-- Whether `k` rounds' functions fit, each round on the machines the one before left. -/
def roundsFit {v : ServiceV} (s : State v) : Bool → Nat → Prop
  | _, 0 => True
  | ab, k + 1 => roundFit S T s.records s.now ab s.machines ∧
      roundsFit { s with machines := (Step.roundOf s.records s.now ab s.machines).1 }
        (ab && (Step.dues s.machines.toSigma s.now).min?.isSome) k

theorem firesFit_true (recs : r.den0) (now d d' : Int) : {ms : List (MachineV r e)} → (sms : Step.Machines ms) →
    (firesFit S T recs now d true sms ↔ firesFit S T recs now d' true sms)
  | _, .nil => Iff.rfl
  | _, .cons insts rest => by
    simp only [firesFit, Bool.not_true, Bool.false_and, Bool.false_eq_true, false_implies, implies_true, Bool.true_or,
      true_and]
    rw [firesFit_true recs now d d' rest]

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- Every machine's part of a firing round: the condition holds exactly when its functions fit (`firesFit`), and
wherever it holds the new tables denote the machines after `Step.fireMachines` and the start slots hold its effects,
machine by machine. -/
theorem fires_encode (recs : v.records.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {d : Term} {dv : Int} (hd : d.denote M = .int dv) :
    (ms : List (MachineV v.records v.event)) → (xs : PerMachine (fun _ => Term) ms) → (sms : Step.Machines ms) →
    MachinesRel M L T ms xs sms → (∀ m ∈ ms, m.key.ordered T = true) →
    {done : Term} → {b : Bool} → done.denote M = .bool b →
    {os : PerMachine (fun _ => FireOut) ms} → {c : Term} → encodeFires L T ms xs done d records now = .ok (os, c) →
    (Holds M c ↔ firesFit L.count T recs tnow dv b sms) ∧
    (Holds M c → MachinesRel M L T ms (os.map (·.table)) (Step.fireMachines recs tnow dv b sms).1 ∧
      ∃ effss, StartsRel M L T ms (os.map (·.starts)) effss ∧
        effss.toList.flatten = (Step.fireMachines recs tnow dv b sms).2.1)
  | [], .nil, .nil, _, _, done, b, hdone, os, c, henc => by
    simp only [encodeFires, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl⟩ := henc
    exact ⟨by simp [firesFit, holds_tt], fun _ => ⟨trivial, .nil, trivial, by simp [Step.fireMachines]⟩⟩
  | m :: ms, .cons x xs, .cons insts sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hord, done, b, hdone, os, c, henc => by
    obtain ⟨⟨af, c0⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨fx, c1⟩, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c2⟩, h3, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨os', c3⟩, h4, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    subst hsm
    refine ⟨?_, fun hc => ?_⟩
    · have hrec' : RelV L v.records (Ty.up _ m.records_data recs) (records.denote M) := hrec
      have e0 := (m.after.code_exact (M := M) h1).1
      have e1 := (m.effect.code_exact (M := M) h2).1
      simp only [firesFit]
      rw [holds_andT, holds_andT, holds_andT, e0, e1]
      constructor
      · rintro ⟨p0, p1, p2, p3⟩
        have F := fire_encode (T := T) m h1 (e0.2 p0) h2 (e1.2 p1) recs tnow hrec' hnow tbl htbl hdone hd h3
        obtain ⟨-, hhit, -⟩ := F.2 p2
        have hdone' : (Term.share (.or done o.hit)).denote M = .bool (b || (instancesOf T m tbl).any (Step.hitsAt dv)) := by
          rw [Term.denote_share]; show Val.bool _ = _; rw [hdone, hhit]; rfl
        exact ⟨p0, p1, F.1.1 p2,
          (fires_encode recs tnow hrec hnow hd ms xs sms hrest (fun m' hm => hord m' (by simp [hm])) hdone' h4).1.1 p3⟩
      · rintro ⟨p0, p1, p2, p3⟩
        have F := fire_encode (T := T) m h1 (e0.2 p0) h2 (e1.2 p1) recs tnow hrec' hnow tbl htbl hdone hd h3
        have hc2 := F.1.2 p2
        obtain ⟨-, hhit, -⟩ := F.2 hc2
        have hdone' : (Term.share (.or done o.hit)).denote M = .bool (b || (instancesOf T m tbl).any (Step.hitsAt dv)) := by
          rw [Term.denote_share]; show Val.bool _ = _; rw [hdone, hhit]; rfl
        exact ⟨p0, p1, hc2, (fires_encode recs tnow hrec hnow hd ms xs sms hrest (fun m' hm => hord m' (by simp [hm])) hdone' h4).1.2 p3⟩
    · obtain ⟨hc0, hc123⟩ := (holds_andT _ _).1 hc
      obtain ⟨hc1, hc23⟩ := (holds_andT _ _).1 hc123
      obtain ⟨hc2, hc3⟩ := (holds_andT _ _).1 hc23
      have ho := hord m (by simp)
      have hrec' : RelV L v.records (Ty.up _ m.records_data recs) (records.denote M) := hrec
      obtain ⟨⟨tbl', ht', hi'⟩, hhit, svX, E, hX, hhX, hEp⟩ :=
        (fire_encode (T := T) m h1 hc0 h2 hc1 recs tnow hrec' hnow tbl htbl hdone hd h3).2 hc2
      have hdone' : (Term.share (.or done o.hit)).denote M = .bool (b || (instancesOf T m tbl).any (Step.hitsAt dv)) := by
        rw [Term.denote_share]; show Val.bool _ = _; rw [hdone, hhit]; rfl
      obtain ⟨hrel, effss, hst, hfl⟩ := (fires_encode recs tnow hrec hnow hd ms xs sms hrest
        (fun m' hm => hord m' (by simp [hm])) hdone' h4).2 hc3
      rw [fireMachines_cons (T := T) m ho recs tnow dv b (instancesOf_ok (T := T) m tbl) sms]
      refine ⟨⟨⟨tbl', ht', ?_⟩, hrel⟩, .cons ((instancesOf T m tbl).flatMap fun a => (sentBy m Step.Instance.key
        (fun i => firedOpt m recs tnow (!b && Step.firesIn T m dv (instancesOf T m tbl) i) i) a).toList) effss, ⟨⟨_, Step.Instance.key, _, E, _, svX, hX, hhX, hEp,
        instancesOk_lt (T := T) m ho (instancesOf_ok (T := T) m tbl), rfl⟩, hst⟩, ?_⟩
      · rw [hi']
      · rw [PerMachine.toList_cons, List.flatten_cons, hfl]

/-- A firing round: the condition holds exactly when its functions fit (`roundFit`), and wherever it holds whether it
fires, the new tables, and the effects of `Step.roundOf`, machine by machine. -/
theorem round_encode (recs : v.records.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {ms : List (MachineV v.records v.event)} {xs : PerMachine (fun _ => Term) ms} {sms : Step.Machines ms}
    (hms : MachinesRel M L T ms xs sms) (hord : ∀ m ∈ ms, m.key.ordered T = true)
    {active : Term} {ab : Bool} (hact : active.denote M = .bool ab)
    {ro : RoundOut ms} {c : Term} (henc : encodeRound L T ms xs active records now = .ok (ro, c)) :
    (Holds M c ↔ roundFit L.count T recs tnow ab sms) ∧
    (Holds M c → ro.go.denote M = .bool (ab && (Step.dues sms.toSigma tnow).min?.isSome) ∧
      MachinesRel M L T ms (ro.fires.map (·.table)) (Step.roundOf recs tnow ab sms).1 ∧
      ∃ effss, StartsRel M L T ms (ro.fires.map (·.starts)) effss ∧
        effss.toList.flatten = (Step.roundOf recs tnow ab sms).2) := by
  obtain ⟨dues, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨os, c'⟩, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨odues, hF, hP⟩ := dueAll_rel (T := T) hnow ms xs sms hms h1
  obtain ⟨hhas, hmin⟩ := minDue_den hF
  obtain ⟨dv, hdv⟩ := minDue_int hF
  rw [min?_perm hP] at hhas hmin
  have hgo : (Term.share (.and active (minDueT dues).1)).denote M = .bool (ab && (Step.dues sms.toSigma tnow).min?.isSome) := by
    rw [Term.denote_share]; show Val.bool _ = _; rw [hact, hhas]; rfl
  have hngo : (Term.not (Term.share (.and active (minDueT dues).1))).denote M =
      .bool !(ab && (Step.dues sms.toSigma tnow).min?.isSome) := by
    show Val.bool _ = _; rw [hgo]; rfl
  have hd : (Term.share (minDueT dues).2).denote M = .int dv := by rw [Term.denote_share, hdv]
  refine ⟨?_, fun hc => ?_⟩
  · rw [(fires_encode recs tnow hrec hnow hd ms xs sms hms hord hngo h2).1]
    unfold roundFit
    cases ab with
    | false => simp only [Bool.false_and, Bool.not_false, Bool.false_eq_true, ite_false]; exact firesFit_true _ T recs tnow dv 0 sms
    | true =>
      simp only [Bool.true_and, ite_true]
      cases hm : (Step.dues sms.toSigma tnow).min? with
      | none => simp only [Option.isSome_none, Bool.not_false]; exact firesFit_true _ T recs tnow dv 0 sms
      | some dmin =>
        have hdm : dv = dmin := by have := hmin dmin hm; rw [hdv] at this; cases this; rfl
        subst hdm
        simp only [Option.isSome_some, Bool.not_true]
  · obtain ⟨hrel, effss, hst, hfl⟩ := (fires_encode recs tnow hrec hnow hd ms xs sms hms hord hngo h2).2 hc
    refine ⟨hgo, ?_⟩
    unfold Step.roundOf
    cases ab with
    | false =>
      simp only [Bool.false_and, Bool.not_false, Step.fireMachines_true] at hrel hfl
      exact ⟨hrel, effss, hst, hfl⟩
    | true =>
      simp only [ite_true]
      cases hm : (Step.dues sms.toSigma tnow).min? with
      | none =>
        simp only [hm, Option.isSome_none, Bool.and_false, Bool.not_false, Step.fireMachines_true] at hrel hfl
        exact ⟨hrel, effss, hst, hfl⟩
      | some dmin =>
        have hdm : dv = dmin := by have := hmin dmin hm; rw [hdv] at this; cases this; rfl
        subst hdm
        simp only [hm, Option.isSome_some, Bool.and_true, Bool.not_true] at hrel hfl
        exact ⟨hrel, effss, hst, hfl⟩

/-- The firing rounds: the condition holds exactly when every round's functions fit (`roundsFit`), and wherever it
holds, where `Step.fireFrom` gives none (every round fired) the over term holds; otherwise it does not, the tables denote the machines after the rounds, the pending slots hold the requests among their effects at
ids from the next id, the own slots the own commands and queries at places from the queue place, and the next id and
queue place terms are past them. Only the machines change. -/
theorem rounds_encode {P : List AnySite} {E : List AnyEffectSite} (hP : SitesUnique P) {shs : List (PendingShape v.event)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)} (hshp : ShapesHold shs ds)
    (senv : StepEnv L shs)
    {records now : Term} (hord : ∀ m ∈ v.machines, m.key.ordered T = true) :
    (k : Nat) → (s : State v) → RelV L v.records (Ty.up _ v.records_data s.records) (records.denote M) →
    now.denote M = .int s.now → (∀ m ∈ v.machines, m.Reach P E) →
    {xs : PerMachine (fun _ => Term) v.machines} → MachinesRel M L T v.machines xs s.machines →
    {active : Term} → {ab : Bool} → active.denote M = .bool ab →
    {nid q : Term} → {o : RoundsOut v.machines} → {c : Term} →
    encodeRounds L T shs ds senv v.machines records now k xs active nid q = .ok (o, c) →
    (Holds M c ↔ roundsFit L.count T s ab k) ∧
    (∀ {n0 q0 : Nat}, nid.denote M = .int n0 → q.denote M = .int q0 → Holds M c →
      match Step.fireFrom s ab k with
      | none => o.over.denote M = .bool true
      | some (s', effs) => o.over.denote M = .bool false ∧ MachinesRel M L T v.machines o.tables s'.machines ∧
          s' = { s with machines := s'.machines } ∧
          o.nextId.denote M = .int ((n0 + (Step.reqsOf effs).length : Nat) : Int) ∧
          NewsRel M L shs ds o.news (Step.reqsOf effs) n0 ∧
          o.queued.denote M = .int ((q0 + (Step.queuedOf effs).length : Nat) : Int) ∧
          OwnRel M L o.owns (Step.queuedOf effs) q0)
  | 0, s, _, _, _, xs, hms, active, ab, hact, nid, q, o, c, henc => by
    simp only [encodeRounds, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl⟩ := henc
    refine ⟨by simp [roundsFit, holds_tt], fun {n0 q0} hnid hq _ => ?_⟩
    cases ab with
    | true => exact hact
    | false =>
      refine ⟨hact, hms, rfl, by simpa using hnid, ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [],
        by simp, trivial⟩, by simpa using hq, ownRel_nil q0⟩
  | k + 1, s, hrec, hnow, hreach, xs, hms, active, ab, hact, nid, q, o, c, henc => by
    obtain ⟨⟨ro, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨news, n, owns, no⟩, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2⟩, h3, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    refine ⟨?_, fun {n0 q0} hnid hq hc => ?_⟩
    · have E1 := round_encode (T := T) s.records s.now hrec hnow hms hord hact h1
      have e1 := E1.1
      simp only [roundsFit]
      rw [holds_andT, e1]
      have ih : roundFit L.count T s.records s.now ab s.machines → (Holds M c2 ↔
          roundsFit L.count T { s with machines := (Step.roundOf s.records s.now ab s.machines).1 }
            (ab && (Step.dues s.machines.toSigma s.now).min?.isSome) k) := fun hf => by
        obtain ⟨hgo, hrel, -⟩ := E1.2 (e1.2 hf)
        exact (rounds_encode hP hshs hshp senv hord k ({ s with machines := (Step.roundOf s.records s.now ab s.machines).1 } :
          State v) hrec hnow hreach hrel hgo h3).1
      exact ⟨fun ⟨p1, p2⟩ => ⟨p1, (ih p1).1 p2⟩, fun ⟨p1, p2⟩ => ⟨p1, (ih p1).2 p2⟩⟩
    · obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
      obtain ⟨hgo, hrel, effss, hst, hfl⟩ := (round_encode s.records s.now hrec hnow hms hord hact h1).2 hc1
      have hr1 := roundOf_reach s.records s.now ab s.machines hreach
      have hreff : ∀ x ∈ effss.toList.flatten, x.2.Reach P := fun x hx => hr1 x (hfl ▸ hx)
      have hf1 := roundOf_from s.records s.now ab s.machines hreach
      obtain ⟨hcnt, hnews, hcntO, hown⟩ := roundStarts_rel hP hshs senv hnid hq v.machines _ effss hst
        (hfl ▸ roundOf_effs s.records s.now ab s.machines) hreff (fun x hx => hshp x (hf1 x (hfl ▸ hx))) h2
      rw [hfl] at hcnt hnews hcntO hown
      have hnid' : (Term.share (.add nid n)).denote M =
          .int ((n0 + (Step.reqsOf (Step.roundOf s.records s.now ab s.machines).2).length : Nat) : Int) := by
        rw [Term.denote_share]; simp only [Term.denote, hnid, hcnt, Val.toInt]; push_cast; rfl
      have hq' : (Term.share (.add q no)).denote M =
          .int ((q0 + (Step.queuedOf (Step.roundOf s.records s.now ab s.machines).2).length : Nat) : Int) := by
        rw [Term.denote_share]; simp only [Term.denote, hq, hcntO, Val.toInt]; push_cast; rfl
      let s1 : State v := { s with machines := (Step.roundOf s.records s.now ab s.machines).1 }
      have ih := (rounds_encode hP hshs hshp senv hord k s1 hrec hnow hreach hrel hgo h3).2 hnid' hq' hc2
      -- Rounds that fire nothing: the rest fires nothing either.
      have hidle : (Step.roundOf s.records s.now ab s.machines) = (s.machines, []) →
          (ab && (Step.dues s.machines.toSigma s.now).min?.isSome) = false →
          Step.fireFrom s ab (k + 1) = some (s, []) →
          match Step.fireFrom s ab (k + 1) with
          | none => rest.over.denote M = .bool true
          | some (s', effs) => rest.over.denote M = .bool false ∧ MachinesRel M L T v.machines rest.tables s'.machines ∧
              s' = { s with machines := s'.machines } ∧
              rest.nextId.denote M = .int ((n0 + (Step.reqsOf effs).length : Nat) : Int) ∧
              NewsRel M L shs ds (news ++ rest.news) (Step.reqsOf effs) n0 ∧
              rest.queued.denote M = .int ((q0 + (Step.queuedOf effs).length : Nat) : Int) ∧
              OwnRel M L (owns ++ rest.owns) (Step.queuedOf effs) q0 := by
        intro hro hg hff
        rw [hff]
        have hs1 : s1 = s := by simp only [s1, hro]
        rw [hg, hs1] at ih
        simp only [Step.fireFrom, Bool.false_eq_true, ite_false] at ih
        obtain ⟨ho, hm, -, hn, hnw, hqq, how⟩ := ih
        simp only [hro, Step.reqsOf, Step.queuedOf, List.filter_nil, List.map_nil, List.length_nil,
          Nat.add_zero] at hn hnw hqq how hnews hown ⊢
        refine ⟨ho, hm, by first | rfl | trivial, hn, ?_, hqq, ?_⟩
        · simpa using newsRel_append hnews (by simpa using hnw)
        · simpa using ownRel_append hown (by simpa using how)
      cases ab with
      | false =>
        exact hidle (by simp [Step.roundOf]) (by simp) (by simp [Step.fireFrom])
      | true =>
        cases hm : (Step.dues s.machines.toSigma s.now).min? with
        | none =>
          exact hidle (by simp [Step.roundOf, hm]) (by simp [hm]) (by simp [Step.fireFrom, Step.fire, hm])
        | some d =>
          have hro : Step.roundOf s.records s.now true s.machines =
              ((Step.fireMachines s.records s.now d false s.machines).1, (Step.fireMachines s.records s.now d false s.machines).2.1) := by
            simp [Step.roundOf, hm]
          have hff : Step.fireFrom s true (k + 1) = (Step.fire s1 k).map fun (s', es) =>
              (s', (Step.fireMachines s.records s.now d false s.machines).2.1 ++ es) := by
            simp only [Step.fireFrom, ite_true, Step.fire, hm, s1, hro]
          rw [hff]
          simp only [hm, Option.isSome_some, Bool.and_self, Step.fireFrom, ite_true] at ih
          cases hf : Step.fire s1 k with
          | none => rw [hf] at ih; exact ih
          | some p =>
            obtain ⟨s', es⟩ := p
            rw [hf] at ih
            obtain ⟨ho, hm', hs', hn, hnw, hqq, how⟩ := ih
            rw [hro] at hnews hown
            rw [hro] at hnw how hn hqq
            have hnw' := newsRel_append hnews hnw
            have how' := ownRel_append hown (by simpa [Step.queuedOf] using how)
            refine ⟨ho, hm', ?_, ?_, by simpa [List.filter_append] using hnw', ?_,
              by simpa [Step.queuedOf, List.filter_append] using how'⟩
            · rw [hs']
            · rw [hn]; simp [List.filter_append, Nat.add_assoc]
            · rw [hqq]; simp [List.filter_append, Nat.add_assoc]

/-- A clock line: where the codes' conditions hold, the condition holds exactly when, for a time not before the
state's, the rounds' functions fit and the step's end fits; wherever it holds, a time before the state's is Invalid,
a step where every one of the `cascade + 1` rounds fires is the cascade fault, and otherwise time moves to the line's
and the step ends as its end terms say (`Finished`). -/
theorem clock_encode {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P) (hshp : ShapesHold shs v.declared)
    (s : State v) (hinv : Step.Inv P s) (time : Int)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci : Term} (hci : v.invariants.code L = .ok (inv, ci)) (hcinv : Holds M ci)
    {S : SymState v} (hR : StateRel M L T shs S s) {st : Term} (hst : st.denote M = .int time)
    (senv : StepEnv L shs)
    {o : ClockOut v} {cond cfx : Term}
    (henc : encodeClock L T P v shs senv apply inv S st = .ok ⟨o, cond, cfx⟩)
    (hcfx : Holds M cfx) :
    let r := step T v s (.clock time)
    (Holds M cond ↔ (s.now ≤ time →
      roundsFit L.count T { s with now := time } true (v.bounds.cascadeNat + 1) ∧
      ∀ s' effs, Step.fire { s with now := time } (v.bounds.cascadeNat + 1) = some (s', effs) →
        finishFits L.count T shs (Step.start { state := s' } effs))) ∧
    (Holds M cond →
      if (o.forward.denote M).toBool then
        if (o.over.denote M).toBool then r = ⟨s, .fault .cascadeLimit, [], []⟩
        else Finished M L T shs o.finish s { state := { s with now := time } } .accepted r
      else r = ⟨s, .invalid ["time moves forward"], [], []⟩) := by
  intro r
  obtain ⟨⟨ro, cr⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨fo, cf, cfx'⟩, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  refine ⟨?_, fun hc => ?_⟩
  · have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
    have hfw : ((Term.le S.now st).denote M).toBool = decide (s.now ≤ time) := by
      simp only [Term.denote, hR.now, hst, Val.toInt, Val.toBool]
    rw [holds_ite_tt hfw]
    by_cases ht : s.now ≤ time
    · simp only [ht, decide_true, true_implies]
      let s0 : State v := { s with now := time }
      have hinv0 : Step.Inv P s0 := hinv.congr rfl rfl
      have hrec0 : RelV L v.records (Ty.up _ v.records_data s0.records) (S.records.denote M) := hR.records
      have ER := rounds_encode chk.sites hshs hshp senv hord (v.bounds.cascadeNat + 1) s0 hrec0 hst chk.machines
        hR.machines (ab := true) rfl h1
      have er := ER.1
      rw [holds_andT, er]
      have rest : roundsFit L.count T s0 true (v.bounds.cascadeNat + 1) →
          (Holds M (.ite ro.over tt cf) ↔ ∀ s' effs,
            Step.fire s0 (v.bounds.cascadeNat + 1) = some (s', effs) →
            finishFits L.count T shs (Step.start { state := s' } effs)) := fun hf => by
        have hro := ER.2 hR.nextId (q0 := 0) rfl (er.2 hf)
        simp only [Step.fireFrom, ite_true] at hro
        cases hfire : Step.fire s0 (v.bounds.cascadeNat + 1) with
        | none =>
          rw [hfire] at hro
          rw [holds_ite]
          simp only [hro, Val.toBool, ite_true, holds_tt, true_iff]
          intro s' effs h; cases h
        | some p =>
          obtain ⟨s', effs⟩ := p
          rw [hfire] at hro
          obtain ⟨hover, hmach, hs', hnT, hnews, hq, hown⟩ := hro
          rw [holds_ite, hover]
          simp only [Val.toBool, Bool.false_eq_true, ite_false]
          obtain ⟨hinv', hreach, hfrom⟩ := Step.fire_inv chk.machines s0 hinv0 _ hfire
          have hdone := rounds_done (shs := shs) s time hs' hR.records hR.fresh hmach hnT hnews hq hown
          rw [(finish_encode chk hshs hshp happ hca hci hcinv senv s
            .accepted { state := s0 } rfl hinv0 hst hR.pending hdone
            (fun a1 h => ⟨Step.start_inv { state := s' } effs hinv' hreach hfrom h,
              Step.start_queue { state := s' } effs h (by simp [Step.QueueOk]) hreach⟩) h2 hcfx).1]
          constructor
          · intro h s'' effs' heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact h
          · intro h; exact h s' effs rfl
      exact ⟨fun ⟨p1, p2⟩ => ⟨p1, (rest p1).1 p2⟩, fun ⟨p1, p2⟩ => ⟨p1, (rest p1).2 p2⟩⟩
    · simp only [ht, decide_false, Bool.false_eq_true, false_implies]
  · have hfw : (Term.le S.now st).denote M = .bool (decide (s.now ≤ time)) := by
      simp only [Term.denote, hR.now, hst, Val.toInt]
    simp only
    rw [hfw]
    by_cases ht : s.now ≤ time
    · have hlt : ¬time < s.now := by omega
      simp only [ht, decide_true, Val.toBool, ite_true]
      rw [holds_ite, hfw] at hc
      simp only [ht, decide_true, toBool_bool, ite_true] at hc
      obtain ⟨hcr, hrest⟩ := (holds_andT _ _).1 hc
      let s0 : State v := { s with now := time }
      have hinv0 : Step.Inv P s0 := hinv.congr rfl rfl
      have hrec0 : RelV L v.records (Ty.up _ v.records_data s0.records) (S.records.denote M) := hR.records
      have hro := (rounds_encode chk.sites hshs hshp senv (fun m hm => (chk.keys m hm).2) (v.bounds.cascadeNat + 1) s0
        hrec0 hst chk.machines hR.machines (ab := true) rfl h1).2 hR.nextId (q0 := 0) rfl hcr
      simp only [Step.fireFrom, ite_true] at hro
      cases hfire : Step.fire s0 (v.bounds.cascadeNat + 1) with
      | none =>
        rw [hfire] at hro
        simp only [hro, ite_true, r, step, hlt, ite_false]
        rw [show ({ s with now := time } : State v) = s0 from rfl, hfire]
      | some p =>
        obtain ⟨s', effs⟩ := p
        rw [hfire] at hro
        obtain ⟨hover, hmach, hs', hnT, hnews, hq, hown⟩ := hro
        simp only [hover, Bool.false_eq_true, ite_false]
        rw [holds_ite, hover] at hrest
        simp only [toBool_bool, Bool.false_eq_true, ite_false] at hrest
        have hr : r = Step.finish T s (Step.start { state := s' } effs) .accepted := by
          simp only [r, step, hlt, ite_false]
          rw [show ({ s with now := time } : State v) = s0 from rfl, hfire]
        rw [hr]
        obtain ⟨hinv', hreach, -⟩ := Step.fire_inv chk.machines s0 hinv0 _ hfire
        have hdone := rounds_done (shs := shs) s time hs' hR.records hR.fresh hmach hnT hnews hq hown
        exact (finish_encode chk hshs hshp happ hca hci hcinv senv s
          .accepted { state := s0 } rfl hinv0 hst hR.pending hdone
          (fun a1 h => ⟨Step.start_inv { state := s' } effs hinv' hreach (Step.fire_inv chk.machines s0 hinv0 _ hfire).2.2 h,
            Step.start_queue { state := s' } effs h (by simp [Step.QueueOk]) hreach⟩) h2 hcfx).2 hrest
    · have hlt : time < s.now := by omega
      simp only [ht, decide_false, Val.toBool, Bool.false_eq_true, ite_false, r, step, hlt, ite_true]

end

end Tazuna.Smt
