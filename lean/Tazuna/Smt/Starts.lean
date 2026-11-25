import Tazuna.Smt.Machines

/-! The effects a machine's instances start on an event, with their wire ids. The step starts them in the canonical
order of the keys and gives each the next wire id, so the effect of the key `k` gets the state's next id plus the
number of effects of keys below `k`. The start slots of the reaction (`ReactOut.starts`) have no order, so each slot's
id is that count, taken over every slot with the order terms (`ordT`); `rank_starts` proves the flagged slots hold
exactly the step's effects, each with the id the step gives it. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- Whether a start slot starts an effect: it holds the first occurrence of its key, and its option holds one. -/
def startFlag (dopt : Nat) (s : StartSlot) : Term := .and s.flag (.is dopt 0 s.effect)

/-- A start slot's effect slot: whether it starts an effect, the wire id (or queue place) the effect gets, the key and
the effect. -/
structure RankedStart where
  flag : Term
  id : Term
  key : Term
  effect : Term

/-- A ranked start as a slot of width three. -/
def RankedStart.slot (s : RankedStart) : Slot 3 := (s.flag, ⟨[s.id, s.key, s.effect], rfl⟩)

/-- One start slot's effect slot, from all the start slots: flagged by `startFlag`, it holds the wire id (`nextId`
plus the number of flagged slots with a smaller key), the key and the effect. -/
def rankStart (m : MachineV r e) (dopt : Nat) (nextId : Term) (all : List (StartSlot))
    (s : StartSlot) : Except Refusal RankedStart := do
  let below ← all.mapM fun s' => do
    let (lt, _) ← need (lacks m.key) (ordT L T m.key s'.key s.key)
    pure (Term.ite (.and (startFlag dopt s') lt) (.int 1) (.int 0))
  pure ⟨startFlag dopt s, Term.share (.add nextId (sumT below)), s.key, .sel dopt 0 0 s.effect⟩

/-- The effect slots of a machine's start slots. -/
def rankStarts (m : MachineV r e) (dopt : Nat) (nextId : Term) (starts : List (StartSlot)) :
    Except Refusal (List RankedStart) :=
  starts.mapM (rankStart L T m dopt nextId starts)

/-- A start slot's effect slot where at most one slot starts an effect, so the id needs no rank: flagged by
`startFlag`, it holds `nextId`, the key and the effect. -/
def onceStart (dopt : Nat) (nextId : Term) (s : StartSlot) : RankedStart :=
  ⟨startFlag dopt s, nextId, s.key, .sel dopt 0 0 s.effect⟩

/-- How many effects the start slots start. -/
def startCount (dopt : Nat) (starts : List (StartSlot)) : Term :=
  sumT (starts.map fun s => .ite (startFlag dopt s) (.int 1) (.int 0))

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- An effect the step starts with its wire id, and its effect slot's items: the id, the sender's key and the effect. -/
def EEff (m : MachineV r e) : (Sender × EffectV e) × Nat → List Val → Prop := fun p vs =>
  ∃ k zk zx, vs = [.int (p.2 : Int), zk, zx] ∧ p.1.1 = .machine m.name ⟨m.key, k⟩ ∧
    RelV L m.key (Ty.up _ m.key_data k) zk ∧ RelV L (.dsl .effect [e]) p.1.2 zx

theorem filterMap_congr' {α β : Type} {f g : α → Option β} : (l : List α) → (∀ a ∈ l, f a = g a) →
    l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp), filterMap_congr' l fun b hb => h b (by simp [hb])]

/-- Optional items of distinct keys in increasing order, numbered from `n0` in order: each item's number is `n0`
plus the number of keys below its own that have an item. -/
theorem zipIdx_ranked {α β : Type} (cmp : α → α → Ordering) [Std.OrientedCmp cmp] (F : α → Option β) :
    (l : List α) → l.Pairwise (fun a b => cmp a b = .lt) → (n0 : Nat) →
    (l.flatMap fun a => (F a).toList).zipIdx n0 =
      l.filterMap fun a => (F a).map fun x => (x, n0 + l.countP fun b => (F b).isSome && cmp b a == .lt)
  | [], _, _ => rfl
  | a :: l, hp, n0 => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 hp
    have ih := zipIdx_ranked cmp F l hl
    have hself : (cmp a a == .lt) = false := by
      have := Std.OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := a)
      cases h : cmp a a <;> simp_all [Ordering.swap]
    have hzero : (l.countP fun b => (F b).isSome && cmp b a == .lt) = 0 :=
      List.countP_eq_zero.2 fun b hb => by
        have := Std.OrientedCmp.gt_iff_lt.2 (ha b hb); simp [this]
    rw [List.flatMap_cons, List.filterMap_cons]
    cases hFa : F a with
    | none =>
      simp only [Option.toList_none, List.nil_append, Option.map_none]
      rw [ih n0]
      exact filterMap_congr' _ fun b hb => by simp [hFa]
    | some x =>
      simp only [Option.toList_some, List.singleton_append, List.zipIdx_cons, Option.map_some]
      rw [ih (n0 + 1), List.countP_cons, hzero, hself, hFa]
      simp only [Bool.and_false, Bool.false_eq_true, ite_false, Nat.add_zero, List.cons.injEq, true_and]
      exact filterMap_congr' _ fun b hb => by
        simp only [List.countP_cons, hFa, ha b hb, Option.isSome_some, beq_self_eq_true, Bool.and_self, ite_true]
        congr 1; funext y; congr 1; omega

theorem length_flatMap_toList {α β : Type} (F : α → Option β) :
    (l : List α) → (l.flatMap fun a => (F a).toList).length = l.countP fun a => (F a).isSome
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_toList F l, List.countP_cons]
    cases F a <;> simp; omega

/-- An effect option and its value: some effect is constructor 0 with the effect's value, none constructor 1. -/
theorem opt_view {dopt nopt : Nat} (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt))
    {v : (Ty.option (.dsl .effect [e])).den} {z : Val} (h : RelV L (Ty.option (.dsl .effect [e])) v z) :
    (∃ x zx, v = .inl (x, ()) ∧ z = .ctor dopt 0 [zx] ∧ RelV L (.dsl .effect [e]) x zx) ∨
      (v = .inr (.inl ()) ∧ z = .ctor dopt 1 []) := by
  obtain ⟨d, n, hd, h⟩ := h
  have : d = dopt := by
    have := hd.symm.trans hopt
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1
  subst this
  match v, h with
  | .inl (x, ()), ⟨vals, hz, v1, vs, hv, hx, hvs⟩ =>
    subst hz; subst hv
    simp only [RelVs] at hvs
    subst hvs
    exact .inl ⟨x, v1, rfl, rfl, hx⟩
  | .inr (.inl ()), ⟨vals, hz, hvs⟩ =>
    simp only [RelVs] at hvs
    subst hvs
    exact .inr ⟨rfl, hz⟩
  | .inr (.inr y), _ => nomatch y

/-- Whether an effect option holds an effect, and the `is` term on its value. -/
theorem is_opt {dopt nopt : Nat} (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt))
    {v : (Ty.option (.dsl .effect [e])).den} {x : Term} (h : RelV L (Ty.option (.dsl .effect [e])) v (x.denote M)) :
    (Term.is dopt 0 x).denote M = .bool (Ty.toOption v).isSome := by
  rcases opt_view hopt h with ⟨x', zx, rfl, hz, -⟩ | ⟨rfl, hz⟩
  · simp [Term.denote, hz, Ty.toOption]
  · simp [Term.denote, hz, Ty.toOption]

/-- A sum of 0/1 terms, one per slot, each 1 exactly where its slot is occupied by an item that `Q` holds of, counts
those items. -/
theorem sum_countP {α : Type} {R : α → List Val → Prop} {Q : α → Bool} :
    (ws : List (StartSlot)) → (sv : List (Bool × List Val)) → (E : List α) → (ts : List Term) →
    SlotsDen M (ws.map StartSlot.slot) sv → Holds2 R E sv →
    Forall2 (fun w t => ∃ g, t = .ite g (.int 1) (.int 0) ∧ (w.1.denote M = .bool false → g.denote M = .bool false) ∧
      ∀ a, w.1.denote M = .bool true → R a (Term.denotes M [w.key, w.effect]) → g.denote M = .bool (Q a)) ws ts →
    (sumT ts).denote M = .int (E.countP Q)
  | [], [], E, [], _, hE, _ => by
    cases E with
    | nil => rfl
    | cons _ _ => exact hE.elim
  | w :: ws, (b, vs) :: sv, E, t :: ts, ⟨hf, hvs, hS⟩, hE, ⟨⟨g, ht, h0, h1⟩, hts⟩ => by
    subst ht
    cases b with
    | false =>
      have ih := sum_countP ws sv E ts hS (by simpa [Holds2, occupied] using hE) hts
      simp [sumT, Term.denote, h0 hf, ih, Val.toBool, Val.toInt]
    | true =>
      match E, hE with
      | a :: E, ⟨ha, hE⟩ =>
        have ih := sum_countP ws sv E ts hS hE hts
        have hg := h1 a hf (by rw [hvs]; exact ha)
        simp only [sumT, Term.denote, hg, ih, Val.toBool, Val.toInt, List.countP_cons]
        cases Q a <;> (simp; try omega)
  | [], _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _ => h.elim
  | [], [], _, _ :: _, _, _, h | _ :: _, _ :: _, _, [], _, _, h => h.elim

/-- The effect an item starts, with its sender: the instance of the item's key. -/
abbrev sentBy (m : MachineV r e) {α : Type} (κ : α → m.key.den0) (F : α → (Ty.option (.dsl .effect [e])).den) (a : α) :
    Option (Sender × EffectV e) :=
  (Ty.toOption (F a)).map (.machine m.name ⟨m.key, κ a⟩, ·)

/-- The effect the instance of key `a` starts on an event, with its sender. -/
abbrev sentOf (m : MachineV r e) (insts : List (Step.Instance m)) (recs : r.den0) (tnow : Int) (ev : e.den0)
    (a : m.key.den0) : Option (Sender × EffectV e) :=
  sentBy m id (startedOf m insts recs tnow ev) a

/-- A machine's effects on an event: each key's, in the canonical order of the keys. -/
theorem machineStep_effects (m : MachineV r e) (hpl : m.key.plain = true) (insts : List (Step.Instance m))
    (recs : r.den0) (tnow : Int) (ev : e.den0) :
    (Step.machineStep T recs tnow ev m insts).2 =
      (Ty.sortBy T m.key (dedupBy (Ty.semWith Dsl.base m.key).2 (m.instances.fn (recs, ())))).flatMap
        fun k => (sentOf m insts recs tnow ev k).toList := by
  simp only [Step.machineStep, List.flatMap_map]
  congr 1; funext k; rw [reactKey_effects m hpl]; unfold sentOf sentBy
  cases Ty.toOption (startedOf m insts recs tnow ev k) <;> rfl

/-- How many items with a key below `a`'s start an effect: the effect of `a` is that many after the machine's first. -/
def rankBy (m : MachineV r e) {α : Type} (κ : α → m.key.den0) (F : α → (Ty.option (.dsl .effect [e])).den)
    (items : List α) (a : α) : Nat :=
  items.countP fun b => (sentBy m κ F b).isSome && Ty.cmp T m.key (κ b) (κ a) == .lt

section
variable (m : MachineV r e) {dopt nopt : Nat} (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt))
  {α : Type} (κ : α → m.key.den0) (F : α → (Ty.option (.dsl .effect [e])).den)
  {all : List (StartSlot)} {svAll : List (Bool × List Val)} {Eall items : List α}
  (hX : SlotsDen M (all.map StartSlot.slot) svAll)
  (hh : Holds2 (EOpt (L := L) m κ F) Eall svAll) (hEp : Eall.Perm items)
include hopt hX hh hEp

/-- The count term denotes how many effects the items start. -/
theorem startCount_den : (startCount dopt all).denote M = .int (items.flatMap fun a => (sentBy m κ F a).toList).length := by
  have := sum_countP (Q := fun a => (sentBy m κ F a).isSome) all svAll Eall _ hX hh
    (forall2_map_self _ all fun w _ => ⟨startFlag dopt w, rfl, fun hf => by simp [startFlag, Term.denote, hf, Val.toBool],
      fun a hf hE => by
        obtain ⟨zk, z, hvs, -, hz⟩ := hE
        simp only [Term.denotes, List.cons.injEq, and_true] at hvs
        have his := is_opt (M := M) hopt (x := w.effect) (hvs.2 ▸ hz)
        rw [show Term.denote M (startFlag dopt w) =
          .bool ((w.1.denote M).toBool && (Term.denote M (.is dopt 0 w.effect)).toBool) from rfl, hf, his]
        simp only [Val.toBool, Bool.true_and]
        unfold sentBy
        cases Ty.toOption (F a) <;> rfl⟩)
  rw [hEp.countP_eq] at this
  rw [startCount, this, length_flatMap_toList]

/-- The sum of a start slot's effect slot denotes the rank of its item. -/
theorem below_sum {s : StartSlot} {a : α}
    (ha : EOpt (L := L) m κ F a (Term.denotes M [s.key, s.effect])) {below : List Term}
    (hb : Forall2 (fun s' t => (do
      let (lt, _) ← need (lacks m.key) (ordT L T m.key s'.key s.key)
      pure (Term.ite (.and (startFlag dopt s') lt) (.int 1) (.int 0))) = Except.ok (ε := Refusal) t) all below) :
    (sumT below).denote M = .int (rankBy (T := T) m κ F items a) := by
  obtain ⟨zk, z, hvs, hk, -⟩ := ha
  simp only [Term.denotes, List.cons.injEq, and_true] at hvs
  rw [rankBy, ← hEp.countP_eq]
  refine sum_countP all svAll Eall below hX hh (forall2_imp (fun s' t h => ?_) hb)
  obtain ⟨⟨lt, le⟩, h1, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  refine ⟨_, rfl, fun hf => by simp [startFlag, Term.denote, hf, Val.toBool], fun b hf hE => ?_⟩
  obtain ⟨zk', z', hvs', hk', hz'⟩ := hE
  simp only [Term.denotes, List.cons.injEq, and_true] at hvs'
  have hord := ordT_rel (M := M) L T m.key _ _ _ (need_ok.1 h1) m.key_data (κ b) (κ a) (hvs'.1 ▸ hk') (hvs.1 ▸ hk)
  have his := is_opt (M := M) hopt (x := s'.effect) (hvs'.2 ▸ hz')
  show Term.denote M (.and (.and s'.flag (.is dopt 0 s'.effect)) lt) = _
  rw [show Term.denote M (.and (.and s'.flag (.is dopt 0 s'.effect)) lt) =
    .bool (((s'.1.denote M).toBool && (Term.denote M (.is dopt 0 s'.effect)).toBool) && (lt.denote M).toBool) from rfl,
    hf, his, hord.1]
  simp only [Val.toBool, Bool.true_and]
  unfold sentBy
  cases Ty.toOption (F b) <;> rfl

/-- The effect slots of start slots hold, where flagged, each effect an item starts, with its wire id. -/
theorem rank_slots {nextId : Term} {n0 : Nat} (hn : nextId.denote M = .int (n0 : Int)) :
    (ws : List (StartSlot)) → (sv : List (Bool × List Val)) → (E : List α) → (S : List RankedStart) →
    SlotsDen M (ws.map StartSlot.slot) sv → Holds2 (EOpt (L := L) m κ F) E sv →
    Forall2 (fun s o => rankStart L T m dopt nextId all s = .ok o) ws S →
    ∃ svS, SlotsDen M (S.map RankedStart.slot) svS ∧ Holds2 (EEff (L := L) m) (E.filterMap fun a => (sentBy m κ F a).map
      fun x => (x, n0 + rankBy (T := T) m κ F items a)) svS
  | [], [], E, [], _, hE, _ => by
    cases E with
    | nil => exact ⟨[], trivial, trivial⟩
    | cons _ _ => exact hE.elim
  | w :: ws, (b, vs) :: sv, E, o :: S, ⟨hf, hvs, hS⟩, hE, ⟨ho, hos⟩ => by
    obtain ⟨below, hbel, ho⟩ := bind_ok.1 ho
    cases pure_ok.1 ho
    have hden : ∀ x y : Term, Term.denotes M [x, y] = [x.denote M, y.denote M] := fun _ _ => rfl
    cases b with
    | false =>
      obtain ⟨svS, hS', hh'⟩ := rank_slots hn ws sv E S hS (by simpa [Holds2, occupied] using hE) hos
      refine ⟨(false, _) :: svS, ⟨by simp [startFlag, Term.denote, hf, Val.toBool], rfl, hS'⟩, ?_⟩
      simpa [Holds2, occupied] using hh'
    | true =>
      match E, hE with
      | a :: E, ⟨ha, hE⟩ =>
        have hsum := below_sum m hopt κ F hX hh hEp (s := w) (by rw [hvs]; exact ha) (mapM_ok _ _ _ hbel)
        obtain ⟨svS, hS', hh'⟩ := rank_slots hn ws sv E S hS hE hos
        obtain ⟨zk, z, rfl, hk, hz⟩ := ha
        simp only [hden, List.cons.injEq, and_true] at hvs
        rcases opt_view hopt hz with ⟨x', zx, hv, hzv, hx'⟩ | ⟨hv, hzv⟩
        · have hsent : sentBy m κ F a = some (.machine m.name ⟨m.key, κ a⟩, x') := by
            simp only [sentBy, hv, Ty.toOption]; rfl
          refine ⟨(true, [.int ((n0 + rankBy (T := T) m κ F items a : Nat) : Int), zk, zx]) :: svS,
            ⟨?_, ?_, hS'⟩, ?_⟩
          · simp [startFlag, Term.denote, hf, hvs.2, hzv, Val.toBool]
          · simp only [Term.denotes, Term.denote_share, Term.denote, hn, hsum, Val.toInt, hvs.1, hvs.2, hzv]
            simp
          · simp only [List.filterMap_cons, hsent]
            exact ⟨⟨κ a, zk, zx, rfl, rfl, hk, hx'⟩, hh'⟩
        · have hsent : sentBy m κ F a = none := by simp only [sentBy, hv, Ty.toOption]; rfl
          refine ⟨(false, _) :: svS, ⟨by simp [startFlag, Term.denote, hf, hvs.2, hzv, Val.toBool], rfl, hS'⟩, ?_⟩
          simp only [List.filterMap_cons, hsent, Option.map_none]
          simpa [Holds2, occupied] using hh'
  | [], _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _ => h.elim
  | [], [], _, _ :: _, _, _, h | _ :: _, _ :: _, _, [], _, _, h => h.elim

end

/-- T2 for the effects start slots start: wherever the condition holds, the effect slots hold, where flagged, the
effects of the items (distinct keys, taken in key order), each with its wire id (`nextId` plus its place among them),
and the count term denotes how many there are. -/
theorem rank_starts (m : MachineV r e) {dopt nopt : Nat}
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt))
    {α : Type} (κ : α → m.key.den0) (F : α → (Ty.option (.dsl .effect [e])).den)
    {starts : List (StartSlot)} {svX : List (Bool × List Val)} {E items : List α}
    (hX : SlotsDen M (starts.map StartSlot.slot) svX)
    (hh : Holds2 (EOpt (L := L) m κ F) E svX) (hEp : E.Perm items)
    (hks : items.Pairwise fun a b => Ty.cmp T m.key (κ a) (κ b) = .lt)
    {nextId : Term} {n0 : Nat} (hn : nextId.denote M = .int (n0 : Int))
    {S : List RankedStart} (hS : rankStarts L T m dopt nextId starts = .ok S) :
    let effs := items.flatMap fun a => (sentBy m κ F a).toList
    (startCount dopt starts).denote M = .int effs.length ∧
      ∃ svS ys, SlotsDen M (S.map RankedStart.slot) svS ∧ ys.Perm (effs.zipIdx n0) ∧
        Holds2 (EEff (L := L) m) ys svS := by
  intro effs
  refine ⟨startCount_den m hopt κ F hX hh hEp, ?_⟩
  · obtain ⟨svS, hS', hh'⟩ := rank_slots (T := T) m hopt κ F hX hh hEp hn starts svX E S hX hh (mapM_ok _ _ _ hS)
    refine ⟨svS, _, hS', ?_, hh'⟩
    haveI : Std.OrientedCmp (fun a b : α => Ty.cmp T m.key (κ a) (κ b)) :=
      ⟨fun {_ _} => Std.OrientedCmp.eq_swap (cmp := Ty.cmp T m.key)⟩
    have hz := zipIdx_ranked (fun a b : α => Ty.cmp T m.key (κ a) (κ b)) (sentBy m κ F) items hks n0
    rw [hz]
    exact hEp.filterMap _

theorem once_slots (m : MachineV r e) {dopt nopt : Nat}
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt))
    {α : Type} (κ : α → m.key.den0) (F : α → (Ty.option (.dsl .effect [e])).den)
    {nextId : Term} {n0 : Nat} (hn : nextId.denote M = .int (n0 : Int)) :
    (ws : List (StartSlot)) → (sv : List (Bool × List Val)) → (E : List α) →
    SlotsDen M (ws.map StartSlot.slot) sv → Holds2 (EOpt (L := L) m κ F) E sv →
    ∃ svS, SlotsDen M ((ws.map (onceStart dopt nextId)).map RankedStart.slot) svS ∧
      Holds2 (EEff (L := L) m) (E.filterMap fun a => (sentBy m κ F a).map fun x => (x, n0)) svS
  | [], [], E, _, hE => by
    cases E with
    | nil => exact ⟨[], trivial, trivial⟩
    | cons _ _ => exact hE.elim
  | w :: ws, (b, vs) :: sv, E, ⟨hf, hvs, hS⟩, hE => by
    have hden : ∀ x y : Term, Term.denotes M [x, y] = [x.denote M, y.denote M] := fun _ _ => rfl
    cases b with
    | false =>
      obtain ⟨svS, hS', hh'⟩ := once_slots m hopt κ F hn ws sv E hS (by simpa [Holds2, occupied] using hE)
      refine ⟨(false, _) :: svS, ⟨by simp [onceStart, startFlag, Term.denote, hf, Val.toBool], rfl, hS'⟩, ?_⟩
      simpa [Holds2, occupied] using hh'
    | true =>
      match E, hE with
      | a :: E, ⟨ha, hE⟩ =>
        obtain ⟨svS, hS', hh'⟩ := once_slots m hopt κ F hn ws sv E hS hE
        obtain ⟨zk, z, rfl, hk, hz⟩ := ha
        simp only [hden, List.cons.injEq, and_true] at hvs
        rcases opt_view hopt hz with ⟨x', zx, hv, hzv, hx'⟩ | ⟨hv, hzv⟩
        · have hsent : sentBy m κ F a = some (.machine m.name ⟨m.key, κ a⟩, x') := by
            simp only [sentBy, hv, Ty.toOption]; rfl
          refine ⟨(true, [.int (n0 : Int), zk, zx]) :: svS, ⟨?_, ?_, hS'⟩, ?_⟩
          · simp [onceStart, startFlag, Term.denote, hf, hvs.2, hzv, Val.toBool]
          · simp [onceStart, Term.denotes, Term.denote, hn, hvs.1, hvs.2, hzv]
          · simp only [List.filterMap_cons, hsent]
            exact ⟨⟨κ a, zk, zx, rfl, rfl, hk, hx'⟩, hh'⟩
        · have hsent : sentBy m κ F a = none := by simp only [sentBy, hv, Ty.toOption]; rfl
          refine ⟨(false, _) :: svS, ⟨by simp [onceStart, startFlag, Term.denote, hf, hvs.2, hzv, Val.toBool], rfl, hS'⟩, ?_⟩
          simp only [List.filterMap_cons, hsent, Option.map_none]
          simpa [Holds2, occupied] using hh'
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

theorem filterMap_toList {α β : Type} (F : α → Option β) :
    (l : List α) → l.filterMap F = l.flatMap fun a => (F a).toList
  | [] => rfl
  | a :: l => by rw [List.filterMap_cons, List.flatMap_cons, filterMap_toList F l]; cases F a <;> rfl

/-- T2 for the effects start slots start where at most one does: the effect slots hold, where flagged, that effect
with the id `nextId`. -/
theorem once_starts (m : MachineV r e) {dopt nopt : Nat}
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt))
    {α : Type} (κ : α → m.key.den0) (F : α → (Ty.option (.dsl .effect [e])).den)
    {starts : List (StartSlot)} {svX : List (Bool × List Val)} {E items : List α}
    (hX : SlotsDen M (starts.map StartSlot.slot) svX)
    (hh : Holds2 (EOpt (L := L) m κ F) E svX) (hEp : E.Perm items)
    (hone : (items.flatMap fun a => (sentBy m κ F a).toList).length ≤ 1)
    {nextId : Term} {n0 : Nat} (hn : nextId.denote M = .int (n0 : Int)) :
    ∃ svS ys, SlotsDen M ((starts.map (onceStart dopt nextId)).map RankedStart.slot) svS ∧
      ys.Perm ((items.flatMap fun a => (sentBy m κ F a).toList).zipIdx n0) ∧ Holds2 (EEff (L := L) m) ys svS := by
  obtain ⟨svS, hS, hh'⟩ := once_slots m hopt κ F hn starts svX E hX hh
  refine ⟨svS, _, hS, ?_, hh'⟩
  have hz : ∀ l : List (Sender × EffectV e), l.length ≤ 1 → l.zipIdx n0 = l.map fun x => (x, n0) := by
    intro l hl
    match l, hl with
    | [], _ => rfl
    | [_], _ => rfl
  rw [hz _ hone, ← filterMap_toList, ← List.map_filterMap]
  exact (hEp.filterMap _).map _

end

end Tazuna.Smt
