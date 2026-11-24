import Tazuna.Smt.Fire
import Tazuna.Smt.EventPending

/-! A clock line's step with machine timers. Time moves to the line's time, then rounds fire, at most `cascade + 1`:
each round finds the earliest deadline among the due timers of every machine (`minDueT`, a fold over all slots, so
the order of slots does not matter), then the machines in order fire their first instance at that deadline, each
unless an earlier machine fired (`encodeFires`, the done flag threading `Step.fireMachines`). A round with no due
timer, and every round after it, changes nothing. When every round fires the step exceeds the cascade bound. A round
fires one instance, so it starts at most one effect, which takes the round's next id (`roundStarts`); the requests are
written into the pending table in round order. -/

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
def dueSlots (de dent dp : Nat) (So : List Slot) (now : Term) : List (Term × Term) :=
  So.map fun (f, xs) =>
    let tm := Term.sel de 0 1 (xs.getD 1 tt)
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
    (y : m.key.den × (instEntry m.state).den) (xs : List Term) (h : ETab L m.key (instEntry m.state) y (Term.denotes M xs)) :
    RelV L _ (Ty.up _ m.timer_data (timerVal (instOfD m y).timer)) ((Term.sel de 0 1 (xs.getD 1 tt)).denote M) := by
  obtain ⟨zk, zv, hvs, hk, hv⟩ := h
  obtain ⟨xk, xe, rfl, hxk, hxe⟩ := pair_terms hvs
  have hy2 : Ty.up _ m.entry_data (Ty.down _ m.entry_data y.2) = y.2 := Ty.up_down _ _ _
  generalize hz : Ty.down _ m.entry_data y.2 = z at hy2
  obtain ⟨st, t, u⟩ := z
  cases u
  have hinst : instOfD m y = ⟨Ty.down _ m.key_data y.1, st, timerOf t⟩ := by simp [instOfD, instOf, hz]
  rw [← hy2] at hv
  obtain ⟨v0, v1, hzv, -, hv1⟩ := (entry_rel_iff m hde st t zv).1 hv
  have hsel : (Term.sel de 0 1 xe).denote M = v1 := by rw [sel_ctor 1 (hxe.trans hzv)]; rfl
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [hsel, hinst]; simpa [val_timerOf] using hv1

/-- The due terms of a table's slots denote, slot by slot, the due deadlines of the instances they hold. -/
theorem dueSlots_rel (m : MachineV r e) {de nde dent nent dp np : Nat} (hde : L.find? (instEntry m.state) = some (de, nde))
    (hdent : L.find? (Ty.option (.tuple [.int, m.state])) = some (dent, nent))
    (hdp : L.find? (.tuple [.int, m.state]) = some (dp, np)) {now : Term} {tnow : Int} (hnow : now.denote M = .int tnow) :
    {So : List Slot} → {sv : List (Bool × List Val)} → {ys : List (m.key.den × (instEntry m.state).den)} →
    SlotsDen M So sv → Holds2 (ETab L m.key (instEntry m.state)) ys sv →
    ∃ os, Forall2 (DueRel M) (dueSlots de dent dp So now) os ∧
      os.filterMap id = (ys.map (instOfD m)).filterMap (dueOf tnow)
  | [], [], ys, _, hy => by
    cases ys with
    | nil => exact ⟨[], trivial, rfl⟩
    | cons _ _ => exact hy.elim
  | (f, xs) :: So, (b, vs) :: sv, ys, ⟨hf, hx, hS⟩, hy => by
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
        have ht := item_timer m hde y xs (hx ▸ hey)
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
            generalize Term.sel dp 0 0 (Term.sel dent 0 0 (Term.sel de 0 1 (xs.getD 1 tt))) = X at hX ⊢
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
def encodeFires : List (MachineV r e) → List Term → (done d records now : Term) → Except Refusal (List FireOut × Term)
  | [], [], _, _, _, _ => pure ([], tt)
  | m :: ms, x :: xs, done, d, records, now => do
    let (af, c0) ← m.after.code L
    let (fx, c1) ← m.effect.code L
    let (o, c) ← encodeFire L T m af fx x done d records now
    let (os, cs) ← encodeFires ms xs (.share (.or done o.hit)) d records now
    pure (o :: os, andT c0 (andT c1 (andT c cs)))
  | _, _, _, _, _, _ => .error (.outside "machines and instance tables that differ in number")

/-- The due slots of every machine's table, machines in order. -/
def dueAll : List (MachineV r e) → List Term → Term → Except Refusal (List (Term × Term))
  | [], [], _ => pure []
  | m :: ms, x :: xs, now => do
    let (dd, n, dt) ← collD L m.table [m.key, instEntry m.state]
    let de ← tupleD L [m.state, Ty.option (.tuple [.int, m.state])]
    let (dent, _) ← need "a layout without the entry's timer" (L.find? (Ty.option (.tuple [.int, m.state])))
    let dp ← tupleD L [.int, m.state]
    let rest ← dueAll ms xs now
    pure (dueSlots de dent dp (slotsOf dd dt n 2 x) now ++ rest)
  | _, _, _ => .error (.outside "machines and instance tables that differ in number")

/-- What a firing round encodes: every machine's part, and whether the round fires (it is active and some timer is
due). -/
structure RoundOut where
  fires : List FireOut
  go : Term

/-- One firing round, where `active`: at the earliest due deadline, every machine's part in order. A round that is
not active, or has no due timer, fires nothing. -/
def encodeRound (ms : List (MachineV r e)) (xs : List Term) (active records now : Term) :
    Except Refusal (RoundOut × Term) := do
  let dues ← dueAll L ms xs now
  let go := Term.share (.and active (minDueT dues).1)
  let (os, c) ← encodeFires L T ms xs (.not go) (Term.share (minDueT dues).2) records now
  pure (⟨os, go⟩, c)

end

/-- A round where `active`: no due timer fires nothing, else `Step.fireMachines` at the earliest due deadline. -/
def _root_.Tazuna.Ir.Step.roundOf {r e : Ty} (recs : r.den0) (now : Int) (active : Bool)
    (sms : List (Step.MachineState r e)) : List (Step.MachineState r e) × List (Sender × EffectV e) :=
  if active then
    match (Step.dues sms now).min? with
    | none => (sms, [])
    | some d => let x := Step.fireMachines recs now d false sms; (x.1, x.2.1)
  else (sms, [])

theorem roundOf_effs {r e : Ty} (recs : r.den0) (now : Int) (active : Bool) (sms : List (Step.MachineState r e)) :
    (Step.roundOf recs now active sms).2.length ≤ 1 := by
  unfold Step.roundOf
  split
  · split
    · simp
    · exact Step.fireMachines_effs recs now _ false sms
  · simp

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- T2 for every machine's part of a firing round: the new tables denote the machines after `Step.fireMachines`, and
the start slots hold its effects, machine by machine. -/
theorem fires_rel (recs : v.records.den0) (tnow : Int) {records now : Term} (hrd : v.records.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {d : Term} {dv : Int} (hd : d.denote M = .int dv) :
    (ms : List (MachineV v.records v.event)) → (xs : List Term) → (sms : List (Step.MachineState v.records v.event)) →
    MachinesRel M L T ms xs sms → (∀ m ∈ ms, m.key.ordered T = true) →
    {done : Term} → {b : Bool} → done.denote M = .bool b →
    {os : List FireOut} → {c : Term} → encodeFires L T ms xs done d records now = .ok (os, c) → Holds M c →
    MachinesRel M L T ms (os.map (·.table)) (Step.fireMachines recs tnow dv b sms).1 ∧
      ∃ effss, StartsRel M L T ms (os.map (·.starts)) effss ∧ effss.flatten = (Step.fireMachines recs tnow dv b sms).2.1
  | [], [], [], _, _, done, b, hdone, os, c, henc, _ => by
    simp only [encodeFires, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    exact ⟨trivial, [], trivial, by simp [Step.fireMachines]⟩
  | m :: ms, x :: xs, sm :: sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hord, done, b, hdone, os, c, henc, hc => by
    obtain ⟨⟨af, c0⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨fx, c1⟩, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c2⟩, h3, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨os', c3⟩, h4, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc0, hc123⟩ := (holds_andT _ _).1 hc
    obtain ⟨hc1, hc23⟩ := (holds_andT _ _).1 hc123
    obtain ⟨hc2, hc3⟩ := (holds_andT _ _).1 hc23
    subst hsm
    have ho := hord m (by simp)
    have haf := m.after.code_fn m.after.ht h1 hc0
    have hfx := effect_codeRel (M := M) m h2 hc1
    have hrec' : RelV L v.records (Ty.up _ m.records_data recs) (records.denote M) := hrec
    obtain ⟨⟨tbl', ht', hi'⟩, hhit, svX, E, hX, hhX, hEp⟩ :=
      fire_table (T := T) m haf hfx recs tnow hrec' hnow tbl htbl hdone hd h3 hc2
    have hdone' : (Term.share (.or done o.hit)).denote M = .bool (b || (instancesOf T m tbl).any (Step.hitsAt dv)) := by
      rw [Term.denote_share]; show Val.bool _ = _; rw [hdone, hhit]; rfl
    obtain ⟨hrel, effss, hst, hfl⟩ := fires_rel recs tnow hrd hrec hnow hd ms xs sms hrest
      (fun m' hm => hord m' (by simp [hm])) hdone' h4 hc3
    rw [fireMachines_cons (T := T) m ho recs tnow dv b (instancesOf_ok (T := T) m tbl) sms]
    refine ⟨⟨⟨tbl', ht', ?_⟩, hrel⟩, _ :: effss, ⟨⟨_, Step.Instance.key, _, E, _, svX, hX, hhX, hEp,
      instancesOk_lt (T := T) m ho (instancesOf_ok (T := T) m tbl), rfl⟩, hst⟩, ?_⟩
    · rw [hi']
    · rw [List.flatten_cons, hfl]
  | [], [], _ :: _, h, _, _, _, _, _, _, _, _ | [], _ :: _, _, h, _, _, _, _, _, _, _, _
  | _ :: _, [], _, h, _, _, _, _, _, _, _, _ | _ :: _, _ :: _, [], h, _, _, _, _, _, _, _, _ => h.elim

/-- The due terms of every machine's table denote the due deadlines of the machines' instances, in some order. -/
theorem dueAll_rel {now : Term} {tnow : Int} (hnow : now.denote M = .int tnow) :
    (ms : List (MachineV v.records v.event)) → (xs : List Term) → (sms : List (Step.MachineState v.records v.event)) →
    MachinesRel M L T ms xs sms → {dues : List (Term × Term)} → dueAll L ms xs now = .ok dues →
    ∃ os, Forall2 (DueRel M) dues os ∧ (os.filterMap id).Perm (Step.dues sms tnow)
  | [], [], [], _, dues, henc => by
    simp only [dueAll, pure, Except.pure, Except.ok.injEq] at henc
    subst henc
    exact ⟨[], trivial, by simp [Step.dues]⟩
  | m :: ms, x :: xs, sm :: sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, dues, henc => by
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
    have hperm : (ys.map (instOfD m)).Perm (instancesOf T m tbl) := instancesOf_perm m tbl hp
    obtain ⟨os1, hf1, he1⟩ := dueSlots_rel m hde (need_ok.1 h3) hdp hnow hS hh
    obtain ⟨os2, hf2, he2⟩ := dueAll_rel hnow ms xs sms hrest h5
    refine ⟨os1 ++ os2, forall2_append hf1 hf2, ?_⟩
    rw [List.filterMap_append, he1]
    exact (hperm.filterMap _).append he2
  | [], [], _ :: _, h, _, _ | [], _ :: _, _, h, _, _ | _ :: _, [], _, h, _, _ | _ :: _, _ :: _, [], h, _, _ => h.elim

/-- T2 for a firing round: whether it fires, the new tables, and the effects of `Step.roundOf`, machine by machine. -/
theorem round_rel (recs : v.records.den0) (tnow : Int) {records now : Term} (hrd : v.records.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {ms : List (MachineV v.records v.event)} {xs : List Term} {sms : List (Step.MachineState v.records v.event)}
    (hms : MachinesRel M L T ms xs sms) (hord : ∀ m ∈ ms, m.key.ordered T = true)
    {active : Term} {ab : Bool} (hact : active.denote M = .bool ab)
    {ro : RoundOut} {c : Term} (henc : encodeRound L T ms xs active records now = .ok (ro, c)) (hc : Holds M c) :
    ro.go.denote M = .bool (ab && (Step.dues sms tnow).min?.isSome) ∧
      MachinesRel M L T ms (ro.fires.map (·.table)) (Step.roundOf recs tnow ab sms).1 ∧
      ∃ effss, StartsRel M L T ms (ro.fires.map (·.starts)) effss ∧ effss.flatten = (Step.roundOf recs tnow ab sms).2 := by
  obtain ⟨dues, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨os, c'⟩, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨odues, hF, hP⟩ := dueAll_rel (T := T) hnow ms xs sms hms h1
  obtain ⟨hhas, hmin⟩ := minDue_den hF
  obtain ⟨dv, hdv⟩ := minDue_int hF
  rw [min?_perm hP] at hhas hmin
  have hgo : (Term.share (.and active (minDueT dues).1)).denote M = .bool (ab && (Step.dues sms tnow).min?.isSome) := by
    rw [Term.denote_share]; show Val.bool _ = _; rw [hact, hhas]; rfl
  have hngo : (Term.not (Term.share (.and active (minDueT dues).1))).denote M =
      .bool !(ab && (Step.dues sms tnow).min?.isSome) := by
    show Val.bool _ = _; rw [hgo]; rfl
  have hd : (Term.share (minDueT dues).2).denote M = .int dv := by rw [Term.denote_share, hdv]
  obtain ⟨hrel, effss, hst, hfl⟩ := fires_rel recs tnow hrd hrec hnow hd ms xs sms hms hord hngo h2 hc
  refine ⟨hgo, ?_⟩
  unfold Step.roundOf
  cases ab with
  | false =>
    simp only [Bool.false_and, Bool.not_false, Step.fireMachines_true] at hrel hfl
    exact ⟨hrel, effss, hst, hfl⟩
  | true =>
    simp only [ite_true]
    cases hm : (Step.dues sms tnow).min? with
    | none =>
      simp only [hm, Option.isSome_none, Bool.and_false, Bool.not_false, Step.fireMachines_true] at hrel hfl
      exact ⟨hrel, effss, hst, hfl⟩
    | some dmin =>
      have hdm : dv = dmin := by have := hmin dmin hm; rw [hdv] at this; cases this; rfl
      subst hdm
      simp only [hm, Option.isSome_some, Bool.and_true, Bool.not_true] at hrel hfl
      exact ⟨hrel, effss, hst, hfl⟩

end

section
variable {P : List AnySite} {r e : Ty}

theorem fireFirst_reach (m : MachineV r e) (hm : m.Reach P) (recs : r.den0) (now d : Int) :
    (insts : List (Step.Instance m)) → Step.EffsReach P (Step.fireFirst m recs now d insts).2.1
  | [] => (fun _ h => nomatch h)
  | i :: is => by
    unfold Step.fireFirst
    split
    · unfold Step.fired
      split
      · exact Step.enter_reach (P := P) m hm recs now _ _
      · exact (fun _ h => nomatch h)
    · exact fireFirst_reach m hm recs now d is

/-- The effects a firing round starts reach the program's sites, and the machines stay the same. -/
theorem fireMachines_reach (recs : r.den0) (now d : Int) : (b : Bool) → (sms : List (Step.MachineState r e)) →
    (∀ ms ∈ sms, ms.1.Reach P) →
      Step.EffsReach P (Step.fireMachines recs now d b sms).2.1 ∧ (Step.fireMachines recs now d b sms).1.map (·.1) = sms.map (·.1)
  | b, [], _ => by cases b <;> exact ⟨(fun _ h => nomatch h), rfl⟩
  | true, ms :: rest, _ => by rw [Step.fireMachines_true]; exact ⟨(fun _ h => nomatch h), rfl⟩
  | false, ⟨m, insts⟩ :: rest, h => by
    obtain ⟨h1, h2⟩ := fireMachines_reach recs now d (Step.fireFirst m recs now d insts).2.2 rest
      fun ms hm => h ms (by simp [hm])
    simp only [Step.fireMachines, List.map_cons, h2]
    refine ⟨fun x hx => ?_, trivial⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact fireFirst_reach m (h ⟨m, insts⟩ (by simp)) recs now d insts x hx
    · exact h1 x hx

theorem roundOf_reach (recs : r.den0) (now : Int) (ab : Bool) (sms : List (Step.MachineState r e))
    (h : ∀ ms ∈ sms, ms.1.Reach P) :
    Step.EffsReach P (Step.roundOf recs now ab sms).2 ∧ ∀ ms ∈ (Step.roundOf recs now ab sms).1, ms.1.Reach P := by
  unfold Step.roundOf
  split
  · split
    · exact ⟨(fun _ h => nomatch h), h⟩
    · rename_i d _
      obtain ⟨h1, h2⟩ := fireMachines_reach recs now d false sms h
      refine ⟨h1, fun ms hm => ?_⟩
      have : ms.1 ∈ sms.map (·.1) := h2 ▸ List.mem_map_of_mem hm
      obtain ⟨ms', hms', heq⟩ := List.mem_map.1 this
      exact heq ▸ h ms' hms'
  · exact ⟨(fun _ h => nomatch h), h⟩

end

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- What the firing rounds encode: the final instance tables, the pending slots of the effects the rounds start (each
round's wire ids after the earlier rounds'), the next wire id after them, and whether every round fired. -/
structure RoundsOut where
  tables : List Term
  news : List Slot
  nextId : Term
  over : Term

/-- The pending slots of a round's start slots, machine by machine, and how many effects they start. A round fires at
most one instance, so every slot takes the round's next id `nid`. -/
def roundStarts (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (dE dP dopt : Nat) :
    List (MachineV r e) → List (List (Term × Term × Term)) → Term → Except Refusal (List Slot × Term)
  | [], [], _ => pure ([], .int 0)
  | m :: ms, st :: sts, nid => do
    let (dk, _) ← need "a layout without the sender's key tuple" (L.find? (.tuple [m.key]))
    let js ← shapeIdxs shs ds ⟨[m.key], .machine m.name m.key⟩ (L.effectsOf e)
    let (rest, k) ← roundStarts shs ds dE dP dopt ms sts nid
    pure (entrySlots dE dP dk js (st.map (onceStart dopt nid)) ++ rest, .add (startCount dopt st) k)
  | _, _, _ => .error (.outside "machines and start slots that differ in number")

/-- `k` firing rounds from the tables `xs`, the first where `active`, each next one where the one before fired. -/
def encodeRounds (shs : List (PendingShape e)) (ds : List (String × DeclaredV)) (dE dP dopt : Nat)
    (ms : List (MachineV r e)) (records now : Term) : Nat → List Term → (active nid : Term) →
    Except Refusal (RoundsOut × Term)
  | 0, xs, active, nid => pure (⟨xs, [], nid, active⟩, tt)
  | k + 1, xs, active, nid => do
    let (ro, c) ← encodeRound L T ms xs active records now
    let (news, n) ← roundStarts L shs ds dE dP dopt ms (ro.fires.map (·.starts)) nid
    let (rest, c') ← encodeRounds shs ds dE dP dopt ms records now k (ro.fires.map (·.table)) ro.go
      (.share (.add nid n))
    pure (⟨rest.tables, news ++ rest.news, rest.nextId, rest.over⟩, andT c c')

end

/-- `Step.fire` where `active`; otherwise nothing fires. -/
def _root_.Tazuna.Ir.Step.fireFrom {v : ServiceV} (s : State v) (active : Bool) (k : Nat) :
    Option (State v × List (Sender × EffectV v.event)) :=
  if active then Step.fire s k else some (s, [])

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- The pending slots hold, where flagged, the entries of the requests written for `effs` at ids from `n0`. -/
def NewsRel (M : Model) (L : Layout) (shs : List (PendingShape v.event)) (ds : List (String × DeclaredV))
    (news : List Slot) (effs : List (Sender × EffectV v.event)) (n0 : Nat) : Prop :=
  ∃ sv zs, SlotsDen M news sv ∧ (∀ p ∈ sv, p.2.length = 2) ∧ Holds2 (ETab L (.dsl .fresh []) (pendingEntry shs)) zs sv ∧
    ∃ xs, xs.Perm (effs.zipIdx n0) ∧ Forall2 (WritesEntry shs ds) xs zs

theorem newsRel_append {shs : List (PendingShape v.event)} {ds : List (String × DeclaredV)} {S S' : List Slot}
    {effs effs' : List (Sender × EffectV v.event)} {n0 : Nat} (h : NewsRel M L shs ds S effs n0)
    (h' : NewsRel M L shs ds S' effs' (n0 + effs.length)) : NewsRel M L shs ds (S ++ S') (effs ++ effs') n0 := by
  obtain ⟨sv, zs, hS, hw, hh, xs, hp, hq⟩ := h
  obtain ⟨sv', zs', hS', hw', hh', xs', hp', hq'⟩ := h'
  refine ⟨sv ++ sv', zs ++ zs', slotsDen_append hS hS', ?_, holds2_append hh hh', xs ++ xs', ?_, forall2_append hq hq'⟩
  · intro p hp; rcases List.mem_append.1 hp with hp | hp
    · exact hw p hp
    · exact hw' p hp
  · rw [List.zipIdx_append]; exact hp.append hp'

/-- T2 for a round's start slots: where they start at most one effect in all, the pending slots hold, where flagged,
the request for it at the id `nid`, and the count term denotes how many there are. -/
theorem roundStarts_rel {P : List AnySite} (hP : SitesUnique P) {shs : List (PendingShape v.event)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)}
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt)) {nid : Term} {n0 : Nat}
    (hn : nid.denote M = .int n0) :
    (ms : List (MachineV v.records v.event)) → (sts : List (List (Term × Term × Term))) →
    (effss : List (List (Sender × EffectV v.event))) → StartsRel M L T ms sts effss → effss.flatten.length ≤ 1 →
    (∀ effs ∈ effss, ∀ x ∈ effs, x.2.Reach P) →
    {news : List Slot} → {cnt : Term} → roundStarts L shs ds dE dP dopt ms sts nid = .ok (news, cnt) →
    cnt.denote M = .int (effss.flatten.length : Int) ∧ NewsRel M L shs ds news effss.flatten n0
  | [], [], [], _, _, _, news, cnt, henc => by
    simp only [roundStarts, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl⟩ := henc
    exact ⟨rfl, [], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩
  | m :: ms, st :: sts, effs :: effss, ⟨⟨α, κ, F, E, items, svX, hX, hh, hEp, _, heffs⟩, hrest⟩, hone, hreach,
      news, cnt, henc => by
    obtain ⟨⟨dk, nk⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨js, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, k⟩, h3, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    rw [List.flatten_cons, List.length_append] at hone
    have hcount := startCount_den m hopt κ F hX hh hEp
    obtain ⟨svS, ys, hS, hyp, hy⟩ := once_starts m hopt κ F hX hh hEp (heffs ▸ by omega) hn
    rw [← heffs] at hyp hcount
    have hr : ∀ x ∈ ys, x.1.2.Reach P := fun x hx =>
      hreach effs (by simp) x.1 (List.fst_mem_of_mem_zipIdx (hyp.mem_iff.1 hx))
    obtain ⟨sv1, zs1, hS1, -, hw1, hh1, hq1⟩ := entrySlots_rel hP m hshs h2 hE hPE (need_ok.1 h1) hS hy hr
    obtain ⟨hk, hnews⟩ := roundStarts_rel hP hshs hE hPE hopt hn ms sts effss hrest (by omega)
      (fun effs' h => hreach effs' (by simp [h])) h3
    refine ⟨?_, ?_⟩
    · simp only [Term.denote, hcount, hk, Val.toInt, List.flatten_cons, List.length_append]; push_cast; rfl
    · rw [List.flatten_cons]
      have h1 : NewsRel M L shs ds _ effs n0 := ⟨sv1, zs1, hS1, hw1, hh1, ys, hyp, hq1⟩
      have hor : effs.length = 0 ∨ effss.flatten.length = 0 := by omega
      obtain ⟨a, b, c, d, e, f, g, h⟩ := hnews
      rcases hor with h0 | h0
      · rw [List.length_eq_zero_iff.1 h0] at h1 ⊢
        exact newsRel_append h1 ⟨a, b, c, d, e, f, g, h⟩
      · rw [List.length_eq_zero_iff.1 h0] at g ⊢
        exact newsRel_append h1 ⟨a, b, c, d, e, f, g, h⟩
  | [], [], _ :: _, h, _, _, _, _, _ | [], _ :: _, _, h, _, _, _, _, _
  | _ :: _, [], _, h, _, _, _, _, _ | _ :: _, _ :: _, [], h, _, _, _, _, _ => h.elim

/-- T2 for the firing rounds: where `Step.fireFrom` gives none (every round fired) the over term holds; otherwise it
does not, the tables denote the machines after the rounds, the pending slots hold the requests for their effects at
ids from the next id, and the next id term is past them. Only the machines change. -/
theorem rounds_rel {P : List AnySite} (hP : SitesUnique P) {shs : List (PendingShape v.event)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) {ds : List (String × DeclaredV)}
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {records now : Term} (hrd : v.records.isData = true) (hord : ∀ m ∈ v.machines, m.key.ordered T = true) :
    (k : Nat) → (s : State v) → RelV L v.records (Ty.up _ hrd s.records) (records.denote M) →
    now.denote M = .int s.now → (∀ ms ∈ s.machines, ms.1.Reach P) →
    {xs : List Term} → MachinesRel M L T v.machines xs s.machines →
    {active : Term} → {ab : Bool} → active.denote M = .bool ab →
    {nid : Term} → {n0 : Nat} → nid.denote M = .int n0 →
    {o : RoundsOut} → {c : Term} → encodeRounds L T shs ds dE dP dopt v.machines records now k xs active nid = .ok (o, c) →
    Holds M c →
    match Step.fireFrom s ab k with
    | none => o.over.denote M = .bool true
    | some (s', effs) => o.over.denote M = .bool false ∧ MachinesRel M L T v.machines o.tables s'.machines ∧
        s' = { s with machines := s'.machines } ∧ o.nextId.denote M = .int ((n0 + effs.length : Nat) : Int) ∧
        NewsRel M L shs ds o.news effs n0
  | 0, s, _, _, _, xs, hms, active, ab, hact, nid, n0, hnid, o, c, henc, _ => by
    simp only [encodeRounds, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    cases ab with
    | true => exact hact
    | false =>
      refine ⟨hact, hms, rfl, by simpa using hnid, [], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp,
        trivial⟩
  | k + 1, s, hrec, hnow, hreach, xs, hms, active, ab, hact, nid, n0, hnid, o, c, henc, hc => by
    obtain ⟨⟨ro, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨news, n⟩, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2⟩, h3, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    obtain ⟨hgo, hrel, effss, hst, hfl⟩ := round_rel s.records s.now hrd hrec hnow hms hord hact h1 hc1
    obtain ⟨hr1, hr2⟩ := roundOf_reach s.records s.now ab s.machines hreach
    have hreff : ∀ effs ∈ effss, ∀ x ∈ effs, x.2.Reach P := fun effs he x hx =>
      hr1 x (hfl ▸ List.mem_flatten.2 ⟨effs, he, hx⟩)
    obtain ⟨hcnt, hnews⟩ := roundStarts_rel hP hshs hE hPE hopt hnid v.machines _ effss hst
      (hfl ▸ roundOf_effs s.records s.now ab s.machines) hreff h2
    rw [hfl] at hcnt hnews
    have hnid' : (Term.share (.add nid n)).denote M =
        .int ((n0 + (Step.roundOf s.records s.now ab s.machines).2.length : Nat) : Int) := by
      rw [Term.denote_share]; simp only [Term.denote, hnid, hcnt, Val.toInt]; push_cast; rfl
    let s1 : State v := { s with machines := (Step.roundOf s.records s.now ab s.machines).1 }
    have ih := rounds_rel hP hshs hE hPE hopt hrd hord k s1 hrec hnow hr2 hrel hgo hnid' h3 hc2
    -- Rounds that fire nothing: the rest fires nothing either.
    have hidle : (Step.roundOf s.records s.now ab s.machines) = (s.machines, []) →
        (ab && (Step.dues s.machines s.now).min?.isSome) = false →
        Step.fireFrom s ab (k + 1) = some (s, []) →
        match Step.fireFrom s ab (k + 1) with
        | none => rest.over.denote M = .bool true
        | some (s', effs) => rest.over.denote M = .bool false ∧ MachinesRel M L T v.machines rest.tables s'.machines ∧
            s' = { s with machines := s'.machines } ∧ rest.nextId.denote M = .int ((n0 + effs.length : Nat) : Int) ∧
            NewsRel M L shs ds (news ++ rest.news) effs n0 := by
      intro hro hg hff
      rw [hff]
      have hs1 : s1 = s := by simp only [s1, hro]
      rw [hg, hs1] at ih
      simp only [Step.fireFrom, Bool.false_eq_true, ite_false] at ih
      obtain ⟨ho, hm, -, hn, hnw⟩ := ih
      simp only [hro, List.length_nil, Nat.add_zero] at hn hnw
      rw [hro] at hnews
      refine ⟨ho, hm, rfl, by simpa using hn, ?_⟩
      have := newsRel_append hnews (by simpa using hnw)
      simpa using this
    cases ab with
    | false =>
      exact hidle (by simp [Step.roundOf]) (by simp) (by simp [Step.fireFrom])
    | true =>
      cases hm : (Step.dues s.machines s.now).min? with
      | none =>
        exact hidle (by simp [Step.roundOf, hm]) (by simp [hm]) (by simp [Step.fireFrom, Step.fire_succ, hm])
      | some d =>
        have hro : Step.roundOf s.records s.now true s.machines =
            ((Step.fireMachines s.records s.now d false s.machines).1, (Step.fireMachines s.records s.now d false s.machines).2.1) := by
          simp [Step.roundOf, hm]
        have hff : Step.fireFrom s true (k + 1) = (Step.fire s1 k).map fun (s', es) =>
            (s', (Step.fireMachines s.records s.now d false s.machines).2.1 ++ es) := by
          simp only [Step.fireFrom, ite_true, Step.fire_succ, hm, s1, hro]
        rw [hff]
        simp only [hm, Option.isSome_some, Bool.and_self, Step.fireFrom, ite_true] at ih
        cases hf : Step.fire s1 k with
        | none => rw [hf] at ih; exact ih
        | some p =>
          obtain ⟨s', es⟩ := p
          rw [hf] at ih
          obtain ⟨ho, hm', hs', hn, hnw⟩ := ih
          rw [hro] at hnews
          refine ⟨ho, hm', ?_, ?_, newsRel_append hnews ?_⟩
          · rw [hs']
          · rw [hn]; simp only [hro, List.length_append]; congr 2; omega
          · rw [hro] at hnw; exact hnw

end

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- Every machine's instance invariant checks on the tables `xs`, machines in order. -/
def encodeInstChecks : List (MachineV r e) → List Term → (records now : Term) → Except Refusal (List (List InstCheck) × Term)
  | [], [], _, _ => pure ([], tt)
  | m :: ms, x :: xs, records, now => do
    let (inv, c0) ← m.invariants.code L
    let (cs, c1) ← encodeInstInvariants L T m inv x records now
    let (rest, c2) ← encodeInstChecks ms xs records now
    pure (cs :: rest, andT c0 (andT c1 c2))
  | _, _, _, _ => .error (.outside "machines and instance tables that differ in number")

/-- The names of the broken instance invariants the checks read from the model, machines in order. -/
def checksBroken (M : Model) (ms : List (MachineV r e)) (checks : List (List InstCheck)) : List String :=
  (ms.zip checks).flatMap fun (m, cs) => instBroken L T M m.key cs

/-- What a clock line's step with timers encodes: whether time moves forward, whether every round fired (the cascade
bound is exceeded), the instance tables after the rounds, the service's invariants and every instance's checks at the
line's time, and the pending table and next wire id after the rounds' requests. -/
structure ClockFireOut where
  forward : Term
  over : Term
  tables : List Term
  invariants : List (Term × Term)
  checks : List (List InstCheck)
  pending : Term
  nextId : Term

/-- A clock line's step from the state terms: `cascade + 1` firing rounds at the line's time `time`, the requests
they start written into the pending table, then the invariants. Each part's condition is asked only where the step
reaches it. -/
def encodeClockFire (v : ServiceV) (shs : List (PendingShape v.event)) (dE dP dopt : Nat)
    (invariants : Code (Ty.fn [v.records] Ty.rules)) (records now time pending nextId : Term) (xs : List Term) :
    Except Refusal (ClockFireOut × Term) := do
  let (ro, cr) ← encodeRounds L T shs v.declared dE dP dopt v.machines records time (v.bounds.cascade.toNat + 1) xs tt
    nextId
  let (pT, cp) ← encodePending L shs pending ro.news
  let rc ← need "records that have no term" (Code.ofTerm? _ records)
  let (invs, ci) ← invariants (rc, ())
  let rules ← ruleTerms L invs
  let (checks, cm) ← encodeInstChecks L T v.machines ro.tables records time
  let forward := Term.le now time
  pure (⟨forward, ro.over, ro.tables, rules, checks, pT, ro.nextId⟩,
    .ite forward (andT cr (.ite ro.over tt (andT cp (andT ci cm)))) tt)

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- The instance checks name the broken invariants of the machines the tables denote. -/
theorem instChecks_rel (recs : v.records.den0) (tnow : Int) {records now : Term} (hrd : v.records.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow) :
    (ms : List (MachineV v.records v.event)) → (xs : List Term) → (sms : List (Step.MachineState v.records v.event)) →
    MachinesRel M L T ms xs sms → (∀ m ∈ ms, m.key.ordered T = true) →
    {checks : List (List InstCheck)} → {c : Term} → encodeInstChecks L T ms xs records now = .ok (checks, c) →
    Holds M c → checksBroken L T M ms checks = instancesBroken recs tnow sms
  | [], [], [], _, _, checks, c, henc, _ => by
    simp only [encodeInstChecks, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -⟩ := henc
    rfl
  | m :: ms, x :: xs, sm :: sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hord, checks, c, henc, hc => by
    obtain ⟨⟨inv, c0⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨cs, c1⟩, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2⟩, h3, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc0, hc12⟩ := (holds_andT _ _).1 hc
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc12
    subst hsm
    have hinv := m.invariants.code_fn m.inv_data h1 hc0
    have hrec' : RelV L v.records (Ty.up _ m.records_data recs) (records.denote M) := hrec
    have hb := instBroken_eq m (hord m (by simp)) hinv recs tnow hrec' hnow tbl htbl h2 hc1
    have ih := instChecks_rel recs tnow hrd hrec hnow ms xs sms hrest (fun m' hm => hord m' (by simp [hm])) h3 hc2
    simp only [checksBroken, List.zip_cons_cons, List.flatMap_cons, instancesBroken] at ih ⊢
    rw [hb]
    exact congrArg _ ih
  | [], [], _ :: _, h, _, _, _, _, _ | [], _ :: _, _, h, _, _, _, _, _ | _ :: _, [], _, h, _, _, _, _, _
  | _ :: _, _ :: _, [], h, _, _, _, _, _ => h.elim

/-- A clock line's step whose rounds fire and whose requests externals list, computed: the requests are written at
the next ids and sent, then the invariants are checked at the line's time. -/
theorem step_clock_requests (s : State v) (time : Int) (ht : ¬time < s.now) {s' : State v}
    {effs : List (Sender × EffectV v.event)} (hf : Step.fire { s with now := time } (v.bounds.cascade.toNat + 1) = some (s', effs))
    (ps : List (Step.Pending v.event)) (hps : Forall2 (Step.Writes v.declared) (effs.zipIdx s'.nextId) ps) :
    let s'' : State v := { s' with pending := s'.pending ++ ps, nextId := s'.nextId + effs.length }
    step T v s (.clock time) = match Step.invariants s'' with
      | n :: _ => ⟨s, .fault (.invariant n), [], []⟩
      | [] => ⟨s'', .accepted, [], ps.map Step.Pending.line⟩ := by
  intro s''
  simp only [step, ht, ite_false, hf]
  rw [Step.finish, Step.start_requests _ _ ps hps]
  simp only [bind, Except.bind, Step.settle, Step.Acc.wrote]
  rfl

/-- T2 for a clock line with machine timers, on a service whose requests have pending shapes: wherever the
conditions hold, a time before the state's is Invalid; when every one of the `cascade + 1` rounds fires the step is
the cascade fault; else a broken invariant's name (the service's first, then each machine's instances in key order)
is the step's fault, and otherwise the step is accepted: time moves to the line's, the machines are the ones the
tables denote, the rounds' requests are written at the next wire ids and sent, the pending table term denotes the
pending requests (as a multiset) and the next id term the next wire id. -/
theorem clock_fire_step {P : List AnySite} (hP : SitesUnique P) {shs : List (PendingShape v.event)} (hne : shs ≠ [])
    (hshs : ∀ sh ∈ shs, sh.InSites P) (s : State v) (hinv : Step.Inv P s) (time : Int) (hrd : v.records.isData = true)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci : Term} (hci : v.invariants.code L = .ok (inv, ci)) (hcinv : Holds M ci)
    {records now st pending nextIdT : Term} (hrec : RelV L v.records (Ty.up _ hrd s.records) (records.denote M))
    (hnow : now.denote M = .int s.now) (hst : st.denote M = .int time)
    (hnid : nextIdT.denote M = .int (Int.ofNat s.nextId)) (hpend : PendingRel L shs (pending.denote M) s.pending)
    {xs : List Term} (hms : MachinesRel M L T v.machines xs s.machines) (hord : ∀ m ∈ v.machines, m.key.ordered T = true)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {o : ClockFireOut} {cond : Term} (henc : encodeClockFire L T v shs dE dP dopt inv records now st pending nextIdT xs = .ok (o, cond))
    (hc : Holds M cond) :
    let r := step T v s (.clock time)
    if (o.forward.denote M).toBool then
      if (o.over.denote M).toBool then r = ⟨s, .fault .cascadeLimit, [], []⟩
      else match brokenIn M o.invariants ++ checksBroken L T M v.machines o.checks with
        | n :: _ => r = ⟨s, .fault (.invariant n), [], []⟩
        | [] => r.outcome = .accepted ∧ r.events = [] ∧
            (∃ ps, r.out = ps.map Step.Pending.line ∧ r.state.pending = s.pending ++ ps ∧
              r.state.nextId = s.nextId + ps.length ∧ ∃ ps', ps'.Perm r.state.pending ∧ PendingRel L shs (o.pending.denote M) ps') ∧
            o.nextId.denote M = .int (Int.ofNat r.state.nextId) ∧
            r.state = { s with now := time, machines := r.state.machines, pending := r.state.pending,
                               nextId := r.state.nextId } ∧
            MachinesRel M L T v.machines o.tables r.state.machines
    else r = ⟨s, .invalid ["time moves forward"], [], []⟩ := by
  intro r
  obtain ⟨⟨ro, cr⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨pT, cp⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨rc, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨invs, ci'⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨rules, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, cm⟩, h6, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hite : ∀ c a b : Term, (Term.ite c a b).denote M = if (c.denote M).toBool then a.denote M else b.denote M :=
    fun _ _ _ => rfl
  have hfw : (Term.le now st).denote M = .bool (decide (s.now ≤ time)) := by
    simp only [Term.denote, hnow, hst, Val.toInt]
  simp only
  rw [hfw]
  by_cases ht : s.now ≤ time
  · have hlt : ¬time < s.now := by omega
    simp only [ht, decide_true, Val.toBool, ite_true]
    simp only [Holds] at hc
    rw [hite, hfw] at hc
    simp only [ht, decide_true, Val.toBool, ite_true] at hc
    obtain ⟨hcr, hrest⟩ := (holds_andT _ _).1 hc
    let s0 : State v := { s with now := time }
    have hrec0 : RelV L v.records (Ty.up _ hrd s0.records) (records.denote M) := hrec
    have hro := rounds_rel hP hshs hE hPE hopt hrd hord (v.bounds.cascade.toNat + 1) s0 hrec0 hst hinv.machines hms
      (ab := true) rfl hnid h1 hcr
    simp only [Step.fireFrom, ite_true] at hro
    cases hfire : Step.fire s0 (v.bounds.cascade.toNat + 1) with
    | none =>
      rw [hfire] at hro
      simp only [hro, ite_true, r, step, hlt, ite_false]
      rw [show ({ s with now := time } : State v) = s0 from rfl, hfire]
    | some p =>
      obtain ⟨s', effs⟩ := p
      rw [hfire] at hro
      obtain ⟨hover, hmach, hs', hnT, hnews⟩ := hro
      simp only [hover, Bool.false_eq_true, ite_false]
      simp only [Holds] at hrest
      rw [hite, hover] at hrest
      simp only [Val.toBool, Bool.false_eq_true, ite_false] at hrest
      obtain ⟨hcp, hci'⟩ := (holds_andT _ _).1 hrest
      obtain ⟨hci2, hcm⟩ := (holds_andT _ _).1 hci'
      obtain ⟨svN, zsN, hSN, hwN, hhN, xsN, hpN, hqN⟩ := hnews
      obtain ⟨ps, hps, ps', hperm, hrelP⟩ := pending_rel hne hpend hinv.below hinv.nodup hSN hwN hhN hpN hqN h2 hcp
      have hs'n : s'.nextId = s.nextId := by rw [hs']
      have hs'p : s'.pending = s.pending := by rw [hs']
      have hs'r : s'.records = s.records := by rw [hs']
      have hs'now : s'.now = time := by rw [hs']
      rw [← hs'n] at hps
      have hstep := step_clock_requests (T := T) s time hlt hfire ps hps
      simp only [r]
      rw [hstep]
      -- The invariants.
      have hcinvf := v.invariants.code_fn (by simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hrd]) hci hcinv
      have hrc : Smt.Rel M L _ (Ty.up _ hrd s.records) rc := (rel_ofTerm (need_ok.1 h3) _).2 hrec
      have hargs : Smt.Rels M L [v.records] (Ty.up (.tuple [v.records]) (by simp [Ty.isData, Ty.isDatas, hrd])
          (s.records, ())) (rc, ()) := by
        show Smt.Rel M L _ (Ty.up (.tuple [v.records]) (by simp [Ty.isData, Ty.isDatas, hrd]) (s.records, ())).1 rc ∧ True
        erw [Ty.up_tuple _ _ _ hrd rfl]; exact ⟨hrc, trivial⟩
      have hi := hcinvf _ _ hargs invs ci' h4 hci2
      erw [Ty.up_fn _ Ty.rules _ (by simp [Ty.isData, Ty.isDatas, hrd]) rfl] at hi
      have hsvc := rules_broken h5 _ hi
      have hchk := instChecks_rel s.records time hrd hrec hst v.machines ro.tables s'.machines hmach hord h6 hcm
      let s'' : State v := { s' with pending := s'.pending ++ ps, nextId := s'.nextId + effs.length }
      have hinvs : Step.invariants s'' = brokenIn M rules ++ checksBroken L T M v.machines checks := by
        simp only [Step.invariants, s'', hs'r, hs'now]
        rw [hsvc, hchk]
        rfl
      rw [hinvs]
      cases brokenIn M rules ++ checksBroken L T M v.machines checks with
      | cons n ns => rfl
      | nil =>
        have hlen : ps.length = effs.length := by rw [← forall2_length hps, List.length_zipIdx]
        refine ⟨rfl, rfl, ⟨ps, rfl, by simp [hs'p], by simp [hs'n, hlen], ps', ?_, hrelP⟩, ?_, ?_, hmach⟩
        · simpa [hs'p] using hperm
        · rw [hnT]; simp [hs'n]
        · rw [hs']
  · have hlt : time < s.now := by omega
    simp only [ht, decide_false, Val.toBool, Bool.false_eq_true, ite_false, r, step, hlt, ite_true]

end

end Tazuna.Smt
