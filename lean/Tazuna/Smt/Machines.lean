import Tazuna.Smt.AnswerStep
import Tazuna.Smt.Order

/-! The step encoding of machine instances. A machine's instances are one table from key to entry
(`MachineV.table`), whose slots have no order, while the step visits instances in the canonical order of their keys.
So each slot is encoded alone, and where the step's order shows in the outcome, as the name of the first broken
invariant, it is read from the model by sorting the occupied slots with the order terms (`ordT`), which denote the
canonical order. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- One slot of a machine's instance table as the invariant check reads it: whether it holds an instance, the key's
term, and the name and holds terms of the instance's invariants. -/
structure InstCheck where
  occupied : Term
  key : Term
  rules : List (Term × Term)

section
variable (L : Layout) (T : List TypeDecl) {r e : Ty}

/-- The context a machine's functions see of the instance with these terms. -/
def instCtxT (m : MachineV r e) (key state records now : Term) : Except Refusal Term :=
  adtCtor L 8 [m.key, m.state, r] [[m.key, m.state, r, .int]] 0 [key, state, records, now]

/-- The invariant check of one slot of an instance table, and its condition, which asks for the invariants'
condition only where the slot holds an instance. `de` is the entry's tuple datatype. -/
def instCheckAt (m : MachineV r e) (inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)) (de : Nat)
    (records now : Term) : Slot → Except Refusal (InstCheck × Term)
  | (f, xs) => do
    let key := xs.headD tt
    let ctx ← instCtxT L m key (.sel de 0 0 (xs.getD 1 tt)) records now
    let cx ← need "a context that has no term" (Code.ofTerm? _ ctx)
    let (rs, c) ← inv (cx, ())
    pure (⟨f, key, ← ruleTerms L rs⟩, Term.ite f c tt)

/-- The invariant check of each slot of the instance table `tbl`, and their condition. Refused when the key type has
no order terms. -/
def encodeInstInvariants (m : MachineV r e) (inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules))
    (tbl records now : Term) : Except Refusal (List InstCheck × Term) := do
  let (d, n, dt) ← collD L m.table [m.key, instEntry m.state]
  let de ← tupleD L [m.state, Ty.option (.tuple [.int, m.state])]
  let checks ← (slotsOf d dt n 2 tbl).mapM (instCheckAt L m inv de records now)
  let _ ← need "a key type without order terms" (ordT L T m.key tt tt)
  pure (checks.map (·.1), allT (checks.map (·.2)))

/-- The codes of the functions a machine's reaction to an event reads. -/
structure ReactCode (m : MachineV r e) where
  instances : Code (Ty.fn [r] (.bag m.key))
  on : Code (Ty.fn [Ty.machineCtx m.key m.state r, e] (Ty.next m.state))
  after : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (Ty.timer m.state)))
  effect : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e])))

/-- A machine's reaction codes, from the sources it keeps, with their condition. -/
def ReactCode.of (m : MachineV r e) : Except Refusal (ReactCode m × Term) := do
  let (i, c1) ← m.instances.code L
  let (o, c2) ← m.on.code L
  let (a, c3) ← m.after.code L
  let (x, c4) ← m.effect.code L
  pure (⟨i, o, a, x⟩, andT c1 (andT c2 (andT c3 c4)))

/-- The terms of `n` slots, each `(f, [k])` with the flag `f` and that no earlier occupied slot holds an equal item:
the slots that hold the first occurrence of their item. -/
def firstSlots (t : Ty) : List Slot → List Slot → Except Refusal (List Term)
  | _, [] => pure []
  | prev, (f, xs) :: rest => do
    let k ← need "an item that has no term" (Code.ofTerm? t (xs.headD tt))
    let eqs ← prev.mapM fun (f', xs') => do
      pure (Term.and f' (← eqCode L t (← need "an item that has no term" (Code.ofTerm? t (xs'.headD tt))) k))
    pure (Term.and f (allT (eqs.map .not)) :: (← firstSlots t (prev ++ [(f, xs)]) rest))

/-- The timer `after` starts, as an entry holds it: the deadline `now` plus the delay, and the state it enters. -/
def timerT (m : MachineV r e) (now a : Term) : Except Refusal Term := do
  let (dopt, _) ← need "a layout without the timer option" (L.find? (Ty.option (Ty.timer m.state)))
  let (dtm, _) ← need "a layout without the timer" (L.find? (Ty.timer m.state))
  let (dent, _) ← need "a layout without the entry's timer" (L.find? (Ty.option (.tuple [.int, m.state])))
  let dp ← tupleD L [.int, m.state]
  let tm := Term.sel dopt 0 0 a
  pure (.ite (.is dopt 0 a) (.ctor dent 0 [.ctor dp 0 [.add now (.sel dtm 0 0 tm), .sel dtm 0 1 tm]]) (.ctor dent 1 []))

/-- Whether an old table slot holds the key `kc`: its flag, the equality term, and its entry. -/
def hitAt (m : MachineV r e) (kc : Code m.key) : Slot → Except Refusal (Term × Term × Term)
  | (g, ys) => do
    pure (g, ← eqCode L m.key (← need "a key that has no term" (Code.ofTerm? m.key (ys.headD tt))) kc, ys.getD 1 tt)

/-- The new table's slot for one slot of the instances bag, the effect it starts, and its condition: flagged by
`first`, it holds the key and the entry of the instance after the event. The effect is the `effect` code's option
where the instance enters a state (it starts, or `on` gives Enter), else `noneT`. -/
def reactAt (m : MachineV r e) (rc : ReactCode m) (de dn : Nat) (So : List Slot) (init : Val) (dflt noneT records now : Term)
    (evc : Code e) : Slot × Term → Except Refusal ((Slot × Term) × Term)
  | ((f, xs), first) => do
    let key := xs.headD tt
    let kc ← need "a key that has no term" (Code.ofTerm? m.key key)
    let hits ← So.mapM (hitAt L m kc)
    let found := anyT (hits.map fun (g, h, _) => .and g h)
    let old := pickT dflt hits
    let oldS := Term.sel de 0 0 old
    let octx ← need "a context that has no term" (Code.ofTerm? _ (← instCtxT L m key oldS records now))
    let (o, c1) ← rc.on (octx, evc, ())
    let ot ← need "a next state that has no term" (Code.term? _ o)
    let st := Term.ite found (.ite (.is dn 1 ot) (.sel dn 1 0 ot) oldS) init.term
    let nctx ← need "a context that has no term" (Code.ofTerm? _ (← instCtxT L m key st records now))
    let (a, c2) ← rc.after (nctx, ())
    let at_ ← need "a timer that has no term" (Code.term? _ a)
    let entered := Term.or (.not found) (.is dn 1 ot)
    let tm := Term.ite entered (← timerT L m now at_) (.sel de 0 1 old)
    let (x, c3) ← rc.effect (nctx, ())
    let xt ← need "an effect that has no term" (Code.term? _ x)
    pure (((first, [key, .ctor de 0 [st, tm]]), .ite entered xt noneT),
      Term.ite f (andT (.ite found c1 tt) (.ite entered (andT c2 c3) tt)) tt)

/-- What a machine's reaction encodes: the new instance table, and per slot of the instances bag its flag (the
first occurrence of a key), its key and the effect option it starts. -/
structure ReactOut where
  table : Term
  starts : List (Term × Term × Term)

/-- The new instance table of a machine after an event, the effects it starts, and its condition, from the instance
table `tbl`, the records after the event, the time and the event. One slot per slot of the bag `instances` returns:
occupied where the slot holds the first occurrence of a key; the instance with that key, if any, reacts with `on` (a
state it enters starts `after`'s timer and its effect), else one starts at `initial`. The bag has at most the
table's slots, else the encoding is refused. -/
def encodeReact (m : MachineV r e) (rc : ReactCode m) (tbl records now ev : Term) : Except Refusal (ReactOut × Term) := do
  let (d, n, dt) ← collD L m.table [m.key, instEntry m.state]
  let de ← tupleD L [m.state, Ty.option (.tuple [.int, m.state])]
  let (dn, _) ← need "a layout without the next state" (L.find? (Ty.next m.state))
  let (dopt, _) ← need "a layout without the effect option" (L.find? (Ty.option (.dsl .effect [e])))
  let rcd ← need "records that have no term" (Code.ofTerm? r records)
  let evc ← need "an event that has no term" (Code.ofTerm? e ev)
  let (bag, c0) ← rc.instances (rcd, ())
  let bagT ← need "a bag that has no term" (Code.term? _ bag)
  let (db, nb, dtb) ← collD L (.bag m.key) [m.key]
  let SB := slotsOf db dtb nb 1 bagT
  let So := slotsOf d dt n 2 tbl
  let init ← need "an initial state without a constant" (embedV L m.state (Ty.up _ m.state_data m.initial))
  let dflt ← need "an entry without a default term" (defaultT L (instEntry m.state))
  let firsts ← firstSlots L m.key [] SB
  let slots ← (SB.zip firsts).mapM (reactAt L m rc de dn So init dflt (.ctor dopt 1 []) records now evc)
  let _ ← need' "an instance bag with more slots than the instance table" (nb ≤ n) ()
  let pad := List.replicate (n - nb) (Term.bool false, [← need "a key without a default term" (defaultT L m.key), dflt])
  pure (⟨slotsTerm d dt (slots.map (·.1.1) ++ pad), slots.map fun ((sl, x), _) => (sl.1, sl.2.headD tt, x)⟩,
    andT c0 (allT (slots.map (·.2))))

/-- Whether every instance's invariants hold. -/
def instOkT (checks : List InstCheck) : Term :=
  allT (checks.map fun c => .or (.not c.occupied) (allT (c.rules.map (·.2))))

/-- Whether the key of `a` comes no later than the key of `b` in the model, by the order terms. -/
def keyLEIn (M : Model) (t : Ty) (a b : InstCheck) : Bool :=
  match ordT L T t a.key b.key with
  | some (_, le) => (le.denote M).toBool
  | none => true

/-- The names of the broken invariants of the instances the model's table holds, in the canonical order of their
keys: the order the step checks them in. -/
def instBroken (M : Model) (t : Ty) (checks : List InstCheck) : List String :=
  ((checks.filter fun c => (c.occupied.denote M).toBool).mergeSort (keyLEIn L T M t)).flatMap (brokenIn M ·.rules)

end

end Tazuna.Smt

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {α β γ : Type}

theorem forall2_zip {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs →
    ∀ p ∈ as.zip bs, R p.1 p.2
  | [], [], _, _, hp => by simp at hp
  | _ :: _, _ :: _, ⟨h, hs⟩, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h
    · exact forall2_zip hs p hp

theorem forall2_of_pairs {R : α → β → Prop} : (ps : List (α × β)) → (∀ p ∈ ps, R p.1 p.2) →
    Forall2 R (ps.map (·.1)) (ps.map (·.2))
  | [], _ => trivial
  | p :: ps, h => ⟨h p (by simp), forall2_of_pairs ps fun q hq => h q (by simp [hq])⟩

/-- Sorting two related lists by orders that agree on related items keeps them related. -/
theorem forall2_mergeSort {R : α → β → Prop} {le : α → α → Bool} {le' : β → β → Bool} {as : List α} {bs : List β}
    (h : Forall2 R as bs) (hle : ∀ a b a' b', R a a' → R b b' → le a b = le' a' b') :
    Forall2 R (as.mergeSort le) (bs.mergeSort le') := by
  have hl := forall2_length h
  have hz := forall2_zip h
  let P := as.zip bs
  have h1 : (P.mergeSort fun p q => le p.1 q.1).map (·.1) = as.mergeSort le := by
    rw [List.map_mergeSort (s := le) (fun _ _ _ _ => rfl)]
    simp [P, List.map_fst_zip, hl]
  have h2 : (P.mergeSort fun p q => le p.1 q.1).map (·.2) = bs.mergeSort le' := by
    rw [List.map_mergeSort (s := le') (fun p hp q hq => hle _ _ _ _ (hz p hp) (hz q hq))]
    simp [List.map_snd_zip, hl]
  rw [← h1, ← h2]
  exact forall2_of_pairs _ fun p hp => hz p ((List.mem_mergeSort).1 hp)

theorem forall2_flatMap {R : α → β → Prop} {f : α → List γ} {g : β → List γ} (hfg : ∀ a b, R a b → f a = g b) :
    {as : List α} → {bs : List β} → Forall2 R as bs → as.flatMap f = bs.flatMap g
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h, hs⟩ => by simp only [List.flatMap_cons]; rw [hfg _ _ h, forall2_flatMap hfg hs]

/-- In a list with no key twice, two items whose keys are equal are the same item. -/
theorem eq_of_keysUnique {κ ν : Type} (f : κ → κ → Bool) (g : κ × ν → β) (key : β → κ) (hkey : ∀ p, key (g p) = p.1) :
    (l : List (κ × ν)) → KeysUnique f l → {a b : β} → a ∈ l.map g → b ∈ l.map g → f (key a) (key b) = true → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | p :: l, hu, a, b, ha, hb, hab => by
    unfold KeysUnique at hu
    rw [List.pairwise_cons] at hu
    simp only [List.map_cons, List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hb
      rw [hkey, hkey] at hab
      exact absurd hab (by simp [(hu.1 q hq).1])
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
      rw [hkey, hkey] at hab
      exact absurd hab (by simp [(hu.1 q hq).2])
    · exact eq_of_keysUnique f g key hkey l hu.2 ha hb hab

end

mutual
/-- Whether the order terms exist depends on the type alone, not on the compared terms. -/
theorem ordT_isSome (L : Layout) (T : List TypeDecl) : (t : Ty) → (x y x' y' : Term) → (ordT L T t x y).isSome = (ordT L T t x' y').isSome
  | .int, _, _, _, _ | .date, _, _, _, _ | .str, _, _, _, _ => rfl
  | .id, _, _, _, _ => by simp only [ordT]; cases L.find? .id <;> rfl
  | .tuple ts, x, y, x', y' => by
    simp only [ordT]
    cases L.find? (.tuple ts) with
    | none => rfl
    | some p => exact ordFields_isSome L T p.1 ts x y x' y' 0
  | .adt 0 _ vs, x, y, x', y' => by
    rcases vs with _ | ⟨_ | ⟨_, _⟩, _ | ⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩⟩⟩ <;> rfl
  | .adt (i + 1) a vs, x, y, x', y' => by
    rcases vs with _ | ⟨fs, _ | ⟨_, _⟩⟩
    · simp only [ordT]; cases L.find? (.adt (i + 1) a []) <;> rfl
    · simp only [ordT]
      cases L.find? (.adt (i + 1) a [fs]) with
      | none => rfl
      | some p => exact ordFields_isSome L T p.1 fs x y x' y' 0
    · simp only [ordT]; split <;> simp [Option.isSome_map]
  | .list _, _, _, _, _ | .bag _, _, _, _, _ | .table .., _, _, _, _ | .fn .., _, _, _, _ | .param _, _, _, _, _
  | .dsl .., _, _, _, _ => by simp [ordT]
theorem ordFields_isSome (L : Layout) (T : List TypeDecl) (d : Nat) : (ts : List Ty) → (x y x' y' : Term) → (j : Nat) →
    (ordFields L T d ts x y j).isSome = (ordFields L T d ts x' y' j).isSome
  | [], _, _, _, _, _ => rfl
  | t :: ts, x, y, x', y', j => by
    simp only [ordFields]
    have h1 := ordT_isSome L T t (.sel d 0 j x) (.sel d 0 j y) (.sel d 0 j x') (.sel d 0 j y')
    have h2 := ordFields_isSome L T d ts x y x' y' (j + 1)
    cases ha : ordT L T t (.sel d 0 j x) (.sel d 0 j y) <;> cases hb : ordT L T t (.sel d 0 j x') (.sel d 0 j y') <;>
      simp_all
    all_goals cases hc : ordFields L T d ts x y (j + 1) <;> cases hd : ordFields L T d ts x' y' (j + 1) <;> simp_all
end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- The context of an instance, read at the level codes relate to. -/
theorem up_mctx (m : MachineV r e) (h : (Ty.machineCtx m.key m.state r).isData = true) (k : m.key.den0)
    (st : m.state.den0) (recs : r.den0) (now : Int) :
    Ty.up _ h (.inl (k, st, recs, now, ()) : (Ty.machineCtx m.key m.state r).den0) =
      Alts.inj (vs := [[m.key, m.state, r, .int]]) ⟨0, by simp⟩
        (Ty.up _ m.key_data k, Ty.up _ m.state_data st, Ty.up _ m.records_data recs, now, ()) := by
  refine (Ty.up_inl 8 [m.key, m.state, r] [m.key, m.state, r, .int] [] h
    (by simp [Ty.isData, Ty.isDatas, m.key_data, m.state_data, m.records_data]) _).trans ?_
  show Sum.inl _ = Sum.inl _
  congr 1
  refine (Ty.up_tuple _ _ _ m.key_data (by simp [Ty.isData, Ty.isDatas, m.state_data, m.records_data]) _).trans
    (congrArg _ ?_)
  refine (Ty.up_tuple _ _ _ m.state_data (by simp [Ty.isData, Ty.isDatas, m.records_data]) _).trans (congrArg _ ?_)
  refine (Ty.up_tuple _ _ _ m.records_data (by simp [Ty.isData, Ty.isDatas]) _).trans (congrArg _ ?_)
  exact (Ty.up_tuple _ _ _ rfl rfl _)

theorem _root_.Tazuna.Ir.MachineV.inv_data (m : MachineV r e) : (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules).isData = true :=
  m.invariants.ht

theorem _root_.Tazuna.Ir.MachineV.ctx_data (m : MachineV r e) : (Ty.machineCtx m.key m.state r).isData = true := by
  have h := m.invariants.ht
  simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at h
  exact h.1.1

/-- One occupied slot's check: its key term denotes the slot's key, and its rules' names and holds terms the
instance's invariants. -/
theorem inst_check (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)}
    (hinv : Smt.Rel M L _ (Ty.up _ m.inv_data m.invariants.fn) inv) (recs : r.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {de : Nat} (hde : tupleD L [m.state, Ty.option (.tuple [.int, m.state])] = .ok de)
    {f : Term} {xs : List Term} {zk zv : Val} (hf : f.denote M = .bool true) (hxs : Term.denotes M xs = [zk, zv])
    (k0 : m.key.den0) (e0 : (instEntry m.state).den0)
    (hk : RelV L m.key (Ty.up _ m.key_data k0) zk)
    (he : RelV L (instEntry m.state) (Ty.up _ (by simp [instEntry, Ty.option, Ty.isData, Ty.isDatas, Ty.isDatass,
      m.state_data]) e0) zv)
    {c : InstCheck} {cj : Term} (hg : instCheckAt L m inv de records now (f, xs) = .ok (c, cj))
    (hcj : Holds M cj) :
    c.occupied = f ∧ c.key.denote M = zk ∧
      brokenIn M c.rules = Step.broken (m.invariants.fn (.inl (k0, e0.1, recs, tnow, ()), ())) := by
  obtain ⟨tk, te, rfl⟩ : ∃ tk te, xs = [tk, te] := by
    match xs, hxs with
    | [tk, te], _ => exact ⟨tk, te, rfl⟩
  simp only [Term.denotes, List.cons.injEq, and_true] at hxs
  obtain ⟨htk, hte⟩ := hxs
  obtain ⟨ctx, h1, hg⟩ := bind_ok.1 hg
  obtain ⟨cx, h2, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨rs, c1⟩, h3, hg⟩ := bind_ok.1 hg
  obtain ⟨rules, h4, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero] at h1
  refine ⟨rfl, htk, ?_⟩
  have hc1 : Holds M c1 := by
    have := (holds_ite _ _ _).1 hcj; simpa [hf, Val.toBool] using this
  -- The entry's state field.
  have hst : Ty.isData m.state = true := m.state_data
  have hopt : (Ty.tuple [Ty.option (.tuple [.int, m.state])]).isData = true := by
    simp [Ty.option, Ty.isData, Ty.isDatas, Ty.isDatass, hst]
  obtain ⟨d', n', vals, hfd, hzv, hvals⟩ := he
  obtain ⟨n'', hfd'⟩ := tupleD_ok hde
  have := find_det hfd hfd'
  subst this
  erw [Ty.up_tuple _ _ _ hst hopt] at hvals
  obtain ⟨v0, vs0, rfl, hv0, -⟩ := hvals
  have hsel : (Term.sel d' 0 0 te).denote M = v0 := by rw [sel_ctor _ (hte.trans hzv)]; rfl
  have hctx := adtCtor_rel (L := L) (M := M) (vs := [[m.key, m.state, r, .int]]) ⟨0, by simp⟩ _ _ h1
    (Ty.up _ m.key_data k0, Ty.up _ m.state_data e0.1, Ty.up _ m.records_data recs, tnow, ())
    ⟨_, _, rfl, htk ▸ hk, _, _, rfl, hsel ▸ hv0, _, _, rfl, hrec, _, _, rfl, hnow, rfl⟩
  rw [← up_mctx m m.ctx_data] at hctx
  have hcx : Smt.Rel M L _ (Ty.up _ m.ctx_data (.inl (k0, e0.1, recs, tnow, ()))) cx :=
    (rel_ofTerm (need_ok.1 h2) _).2 hctx
  have hargs : (Ty.tuple [Ty.machineCtx m.key m.state r]).isData = true := by
    simp [Ty.isData, Ty.isDatas, m.ctx_data]
  have hrels : Smt.Rels M L [Ty.machineCtx m.key m.state r]
      (Ty.up (.tuple [Ty.machineCtx m.key m.state r]) hargs (.inl (k0, e0.1, recs, tnow, ()), ())) (cx, ()) := by
    show Smt.Rel M L _ (Ty.up (.tuple [Ty.machineCtx m.key m.state r]) hargs
      (.inl (k0, e0.1, recs, tnow, ()), ())).1 cx ∧ True
    erw [Ty.up_tuple _ _ _ m.ctx_data rfl]; exact ⟨hcx, trivial⟩
  have hrs := hinv _ _ hrels rs c1 h3 hc1
  erw [Ty.up_fn _ Ty.rules _ hargs rfl] at hrs
  exact rules_broken h4 _ hrs

theorem instCheckAt_occupied (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)}
    {de : Nat} {records now f : Term} {xs : List Term} {c : InstCheck} {cj : Term}
    (hg : instCheckAt L m inv de records now (f, xs) = .ok (c, cj)) : c.occupied = f := by
  obtain ⟨_, _, hg⟩ := bind_ok.1 hg
  obtain ⟨_, _, hg⟩ := bind_ok.1 hg
  obtain ⟨_, _, hg⟩ := bind_ok.1 hg
  obtain ⟨_, _, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  rfl

theorem _root_.Tazuna.Ir.MachineV.entry_data (m : MachineV r e) : (instEntry m.state).isData = true := by
  simp [instEntry, Ty.option, Ty.isData, Ty.isDatas, Ty.isDatass, m.state_data]

/-- The occupied slots' checks, in slot order, relate to the table's entries in that order. -/
theorem occupied_checks (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)}
    (hinv : Smt.Rel M L _ (Ty.up _ m.inv_data m.invariants.fn) inv) (recs : r.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {de : Nat} (hde : tupleD L [m.state, Ty.option (.tuple [.int, m.state])] = .ok de) :
    (S : List Slot) → (sv : List (Bool × List Val)) → (cs : List (InstCheck × Term)) →
    (ys : List (m.key.den × (instEntry m.state).den)) → SlotsDen M S sv → (∀ p ∈ sv, p.2.length = 2) →
    Forall2 (fun sl y => instCheckAt L m inv de records now sl = .ok y) S cs → (∀ y ∈ cs, Holds M y.2) →
    Forall2 (ETab L m.key (instEntry m.state)) ys (occupied sv) →
    Forall2 (fun c y => RelV L m.key y.1 (c.key.denote M) ∧ brokenIn M c.rules =
        Step.broken (m.invariants.fn (.inl (Ty.down _ m.key_data y.1, (Ty.down _ m.entry_data y.2).1, recs, tnow, ()), ())))
      ((cs.map (·.1)).filter fun c => (c.occupied.denote M).toBool) ys
  | [], [], [], ys, _, _, _, _, hy => by
    cases ys with
    | nil => trivial
    | cons _ _ => exact hy.elim
  | (f, xs) :: S, (b, vs) :: sv, (c, cj) :: cs, ys, ⟨hf, hxs, hS⟩, hw, ⟨hg, hgs⟩, hcs, hy => by
    have hw' : ∀ p ∈ sv, p.2.length = 2 := fun p hp => hw p (by simp [hp])
    have hcs' : ∀ y ∈ cs, Holds M y.2 := fun y hy => hcs y (by simp [hy])
    have hocc := instCheckAt_occupied m hg
    cases b with
    | false =>
      have ih := occupied_checks m hinv recs tnow hrec hnow hde S sv cs ys hS hw' hgs hcs' (by simpa [occupied] using hy)
      simpa [List.filter_cons, hocc, hf, Val.toBool] using ih
    | true =>
      match ys, hy with
      | y :: ys, ⟨⟨zk, zv, hz, hk, he⟩, hys⟩ =>
        have ih := occupied_checks m hinv recs tnow hrec hnow hde S sv cs ys hS hw' hgs hcs' hys
        obtain ⟨_, hkey, hb⟩ := inst_check m hinv recs tnow hrec hnow hde hf (hxs.trans hz) (Ty.down _ m.key_data y.1)
          (Ty.down _ m.entry_data y.2) (by rw [Ty.up_down]; exact hk) (by rw [Ty.up_down]; exact he) hg
          (hcs (c, cj) (by simp))
        simp only [List.map_cons, List.filter_cons, hocc, hf, Val.toBool, ite_true]
        exact ⟨⟨hkey ▸ hk, hb⟩, ih⟩
  | [], _ :: _, _, _, h, _, _, _, _ | _ :: _, [], _, _, h, _, _, _, _ => h.elim
  | [], [], _ :: _, _, _, _, h, _, _ | _ :: _, _ :: _, [], _, _, _, h, _, _ => h.elim

theorem forall2_map_right {α β β' : Type} {R : α → β → Prop} {R' : α → β' → Prop} (f : β → β')
    (hf : ∀ a b, R a b → R' a (f b)) : {as : List α} → {bs : List β} → Forall2 R as bs → Forall2 R' as (bs.map f)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨hf _ _ h, forall2_map_right f hf hs⟩

/-- T2 for machine invariants: wherever the condition holds, the names `instBroken` reads from the model are the
broken invariants of the table's instances, in the order the step checks them. -/
theorem instBroken_eq (m : MachineV r e) (hko : m.key.ordered T = true)
    {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)}
    (hinv : Smt.Rel M L _ (Ty.up _ m.inv_data m.invariants.fn) inv) (recs : r.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {x : Term} (tbl : m.table.den0) (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {checks : List InstCheck} {cond : Term} (henc : encodeInstInvariants L T m inv x records now = .ok (checks, cond))
    (hc : Holds M cond) :
    instBroken L T M m.key checks =
      (instancesOf T m tbl).flatMap fun i => Step.broken (m.invariants.fn (.inl (i.key, i.state, recs, tnow, ()), ())) := by
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨de, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨cs, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨p0, h4, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have htbl' : Smt.Rel M L (.table m.key (instEntry m.state)) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS, -, hw, hp, hh⟩ := table_view htbl' h1
  have hQ := occupied_checks m hinv recs tnow hrec hnow h2 _ sv cs ys hS hw (mapM_ok _ _ _ h3)
    (fun y hy => (holds_allT _).1 hc y.2 (List.mem_map.2 ⟨y, hy, rfl⟩)) hh
  let inst : m.key.den × (instEntry m.state).den → Step.Instance m :=
    fun y => instOf m (Ty.down _ m.key_data y.1) (Ty.down _ m.entry_data y.2)
  have hQ' := forall2_map_right inst (R' := fun c (i : Step.Instance m) =>
      RelV L m.key (Ty.up _ m.key_data i.key) (c.key.denote M) ∧
      brokenIn M c.rules = Step.broken (m.invariants.fn (.inl (i.key, i.state, recs, tnow, ()), ())))
    (fun c y ⟨hk, hb⟩ => ⟨by simp only [inst, instOf]; rw [Ty.up_down]; exact hk, hb⟩) hQ
  have hsort := forall2_mergeSort (le := keyLEIn L T M m.key) (le' := keyLE T m) hQ' (by
    intro a b i j ⟨ha, _⟩ ⟨hb, _⟩
    have hs : (ordT L T m.key a.key b.key).isSome = true := by
      rw [ordT_isSome L T m.key a.key b.key tt tt]; exact Option.isSome_iff_exists.2 ⟨_, need_ok.1 h4⟩
    obtain ⟨p, hpp⟩ := Option.isSome_iff_exists.1 hs
    have ho := ordT_rel L T m.key a.key b.key p hpp m.key_data i.key j.key ha hb
    simp only [keyLEIn, hpp, keyLE, ho.2, Val.toBool])
  unfold instBroken
  rw [forall2_flatMap (fun c i h => h.2) hsort]
  congr 1
  -- The table's instances sort to the same list from either order, since no key occurs twice.
  have hperm : (ys.map inst).Perm (tbl.1.map fun (k, x) => instOf m k x) := by
    have := hp.map inst
    erw [Ty.up_table m.key (instEntry m.state) m.table_data m.key_data m.entry_data tbl, List.map_map] at this
    refine this.trans (List.Perm.of_eq (List.map_congr_left fun q _ => ?_))
    simp [inst, Ty.down_up]
  have trans : ∀ a b c : Step.Instance m, keyLE T m a b = true → keyLE T m b c = true → keyLE T m a c = true :=
    fun _ _ _ h1 h2 => Std.TransCmp.isLE_trans (cmp := Ty.cmp T m.key) h1 h2
  have total : ∀ a b : Step.Instance m, (keyLE T m a b || keyLE T m b a) = true := by
    intro a b
    simp only [keyLE]
    rw [Std.OrientedCmp.eq_swap (cmp := Ty.cmp T m.key) (a := a.key) (b := b.key)]
    cases Ty.cmp T m.key b.key a.key <;> rfl
  refine List.Perm.eq_of_pairwise (le := fun a b => keyLE T m a b = true) ?_
    (List.pairwise_mergeSort trans total _) (List.pairwise_mergeSort trans total _)
    ((List.mergeSort_perm _ _).trans (hperm.trans (List.mergeSort_perm _ _).symm))
  intro a b ha hb hab hba
  unfold instancesOf at hb
  have heq : Ty.cmp T m.key a.key b.key = .eq := Std.OrientedCmp.isLE_antisymm (cmp := Ty.cmp T m.key) hab hba
  exact eq_of_keysUnique _ (fun (k, x) => instOf m k x) Step.Instance.key (fun _ => rfl) tbl.1 tbl.2
    (hperm.mem_iff.1 ((List.mergeSort_perm _ _).mem_iff.1 ha)) ((List.mergeSort_perm _ _).mem_iff.1 hb)
    ((Ty.cmp_eq_iff T hko _ _).1 heq)

theorem instOkT_filter (M : Model) (checks : List InstCheck) :
    (instOkT checks).denote M =
      .bool ((checks.filter fun c => (c.occupied.denote M).toBool).all fun c => (brokenIn M c.rules).isEmpty) := by
  unfold instOkT
  rw [allT_denote, List.all_map]
  congr 1
  induction checks with
  | nil => rfl
  | cons c cs ih =>
    have hb : (brokenIn M c.rules).isEmpty = (c.rules.map (·.2)).all (fun t => (t.denote M).toBool) := by
      rw [Bool.eq_iff_iff, List.isEmpty_iff]; exact brokenIn_nil c.rules
    have hc : (Term.denote M (.or (.not c.occupied) (allT (c.rules.map (·.2))))).toBool =
        (!(c.occupied.denote M).toBool || (brokenIn M c.rules).isEmpty) := by
      show (!(c.occupied.denote M).toBool || ((allT _).denote M).toBool) = _
      rw [allT_denote, hb]; rfl
    rw [List.all_cons, List.filter_cons]
    simp only [Function.comp_apply] at ih ⊢
    rw [hc, ih]
    cases (c.occupied.denote M).toBool <;> simp

/-- The term `instOkT` holds exactly when the model's table has no broken invariant. -/
theorem instOkT_denote (L : Layout) (T : List TypeDecl) (M : Model) (t : Ty) (checks : List InstCheck) :
    (instOkT checks).denote M = .bool (instBroken L T M t checks).isEmpty := by
  rw [instOkT_filter]
  congr 1
  unfold instBroken
  rw [Bool.eq_iff_iff, List.all_eq_true, List.isEmpty_iff, List.flatMap_eq_nil_iff]
  constructor
  · intro h c hc; exact List.isEmpty_iff.1 (h c ((List.mergeSort_perm _ _).mem_iff.1 hc))
  · intro h c hc; exact List.isEmpty_iff.2 (h c ((List.mergeSort_perm _ _).mem_iff.2 hc))

end

end Tazuna.Smt

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem find?_perm_unique {α : Type} {p : α → Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂)
    (hu : ∀ a ∈ l₁, ∀ b ∈ l₁, p a = true → p b = true → a = b) : l₁.find? p = l₂.find? p := by
  cases h1 : l₁.find? p with
  | some a =>
    have ha := List.mem_of_find?_eq_some h1
    have hpa := List.find?_some h1
    cases h2 : l₂.find? p with
    | some b => exact congrArg some (hu a ha b (h.mem_iff.2 (List.mem_of_find?_eq_some h2)) hpa (List.find?_some h2))
    | none => exact absurd hpa (by simpa using List.find?_eq_none.1 h2 a (h.mem_iff.1 ha))
  | none =>
    cases h2 : l₂.find? p with
    | some b =>
      have hb := List.mem_of_find?_eq_some h2
      exact absurd (List.find?_some h2) (by simpa using List.find?_eq_none.1 h1 b (h.mem_iff.2 hb))
    | none => rfl

/-- Looking a key up in the old table's slots: some occupied slot's key equals it exactly when the table's entries
hold it, and the picked entry is the first such entry's. -/
theorem lookup_slots (m : MachineV r e) {kc : Code m.key} {k : m.key.den} (hk : Smt.Rel M L m.key k kc) (dflt : Term) :
    (So : List Slot) → (sv : List (Bool × List Val)) → (hits : List (Term × Term × Term)) →
    (ys : List (m.key.den × (instEntry m.state).den)) → SlotsDen M So sv → (∀ p ∈ sv, p.2.length = 2) →
    Forall2 (fun sl h => hitAt L m kc sl = .ok h) So hits → Forall2 (ETab L m.key (instEntry m.state)) ys (occupied sv) →
    (anyT (hits.map fun (g, h, _) => .and g h)).denote M = .bool (ys.any fun y => Ty.deq m.key y.1 k) ∧
      ∀ y, ys.find? (fun y => Ty.deq m.key y.1 k) = some y →
        RelV L (instEntry m.state) y.2 ((pickT dflt hits).denote M)
  | [], [], [], ys, _, _, _, hy => by
    cases ys with
    | nil => exact ⟨rfl, fun _ h => by simp at h⟩
    | cons _ _ => exact hy.elim
  | (g, xs) :: So, (b, vs) :: sv, (g', hq, ent) :: hits, ys, ⟨hg, hxs, hS⟩, hw, ⟨hh, hhs⟩, hy => by
    have hw' : ∀ p ∈ sv, p.2.length = 2 := fun p hp => hw p (by simp [hp])
    obtain ⟨kt, h1, hh⟩ := bind_ok.1 hh
    obtain ⟨q, h2, hh⟩ := bind_ok.1 hh
    cases pure_ok.1 hh
    cases b with
    | false =>
      obtain ⟨ih1, ih2⟩ := lookup_slots m hk dflt So sv hits ys hS hw' hhs (by simpa [occupied] using hy)
      refine ⟨?_, fun y hy' => ?_⟩
      · simp only [List.map_cons, anyT_denote, List.any_cons, Term.denote, hg, Val.toBool, Bool.false_and,
          Bool.false_or] at ih1 ⊢
        exact ih1
      · simp only [pickT, Term.denote, hg, Val.toBool, Bool.false_and]; exact ih2 y hy'
    | true =>
      match ys, hy with
      | y :: ys, ⟨⟨zk, zv, hz, hyk, hye⟩, hys⟩ =>
        obtain ⟨ih1, ih2⟩ := lookup_slots m hk dflt So sv hits ys hS hw' hhs hys
        obtain ⟨tk, te, rfl⟩ : ∃ tk te, xs = [tk, te] := by
          have := hxs.trans hz
          match xs, this with
          | [tk, te], _ => exact ⟨tk, te, rfl⟩
        rw [hz] at hxs
        simp only [Term.denotes, List.cons.injEq, and_true] at hxs
        obtain ⟨htk, hte⟩ := hxs
        simp only [List.headD_cons] at h1
        have hkt : Smt.Rel M L m.key y.1 kt := (rel_ofTerm (need_ok.1 h1) _).2 (htk ▸ hyk)
        have hq := eqCode_rel hkt hk h2
        refine ⟨?_, fun y' hy' => ?_⟩
        · simp only [List.map_cons, anyT_denote, List.any_cons, Term.denote, hg, hq, Val.toBool, Bool.true_and]
            at ih1 ⊢
          rw [Val.bool.inj ih1]
        · simp only [pickT, Term.denote, hg, hq, Val.toBool, Bool.true_and, List.getD_cons_succ,
            List.getD_cons_zero]
          simp only [List.find?_cons] at hy'
          cases hd : Ty.deq m.key y.1 k with
          | true =>
            rw [hd] at hy'; cases hy'
            simp only [ite_true]; rw [hte]; exact hye
          | false =>
            rw [hd] at hy'
            simp only [Bool.false_eq_true, ite_false]; exact ih2 y' hy'
  | [], _ :: _, _, _, h, _, _, _ | _ :: _, [], _, _, h, _, _, _ => h.elim
  | [], [], _ :: _, _, _, _, h, _ | _ :: _, _ :: _, [], _, _, _, h, _ => h.elim

theorem val_timerOf {st : Ty} : (t : (Ty.option (.tuple [.int, st])).den0) → timerVal (timerOf t) = t
  | .inl ((_, _, ()), ()) => rfl
  | .inr (.inl ()) => rfl
  | .inr (.inr x) => nomatch x

theorem beq_symm_plain {t : Ty} (h : t.plain = true) (a b : t.den0) :
    (Ty.semWith Dsl.base t).2 a b = (Ty.semWith Dsl.base t).2 b a := by
  rw [Bool.eq_iff_iff, Ty.beq_plain t h, Ty.beq_plain t h]; exact eq_comm

/-- The entry an instance is, as a table holds it. -/
def entryOf {m : MachineV r e} (i : Step.Instance m) : (instEntry m.state).den0 := (i.state, timerVal i.timer, ())

/-- The old table's entries looked up by a key, in any order of them, find the instance the step finds. -/
theorem lookup_eq (m : MachineV r e) (hpl : m.key.plain = true) (tbl : m.table.den0)
    {ys : List (m.key.den × (instEntry m.state).den)} (hp : ys.Perm (Ty.up _ m.table_data tbl).1) (k : m.key.den0) :
    ys.find? (fun y => Ty.deq m.key y.1 (Ty.up _ m.key_data k)) =
      ((instancesOf T m tbl).find? (fun i => (Ty.semWith Dsl.base m.key).2 k i.key)).map fun i =>
        (Ty.up _ m.key_data i.key, Ty.up _ m.entry_data (entryOf i)) := by
  let U : m.key.den0 × (instEntry m.state).den0 → m.key.den × (instEntry m.state).den :=
    fun p => (Ty.up _ m.key_data p.1, Ty.up _ m.entry_data p.2)
  have hup : (Ty.up _ m.table_data tbl).1 = tbl.1.map U :=
    Ty.up_table m.key (instEntry m.state) m.table_data m.key_data m.entry_data tbl
  rw [hup] at hp
  have hbeq : ∀ a, Ty.deq m.key (Ty.up _ m.key_data a) (Ty.up _ m.key_data k) = (Ty.semWith Dsl.base m.key).2 k a := by
    intro a; show (Ty.semWith Dsl.val m.key).2 _ _ = _; rw [Ty.deq_up, beq_symm_plain hpl]
  have huniq : ∀ a ∈ tbl.1, ∀ b ∈ tbl.1, (Ty.semWith Dsl.base m.key).2 k a.1 = true →
      (Ty.semWith Dsl.base m.key).2 k b.1 = true → a = b := by
    intro a ha b hb hka hkb
    rw [Ty.beq_plain _ hpl] at hka hkb
    exact eq_of_keysUnique _ id Prod.fst (fun _ => rfl) tbl.1 tbl.2 (by simpa using ha) (by simpa using hb)
      (by rw [← hka, ← hkb]; exact (Ty.beq_plain _ hpl _ _).2 rfl)
  rw [find?_perm_unique hp (fun a ha b hb h1 h2 => by
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 (hp.mem_iff.1 ha)
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 (hp.mem_iff.1 hb)
    simp only [U, hbeq] at h1 h2
    rw [huniq a0 ha0 b0 hb0 h1 h2]), List.find?_map]
  unfold instancesOf
  have hms := List.mergeSort_perm (tbl.1.map fun (k, x) => instOf m k x) (keyLE T m)
  rw [find?_perm_unique hms (fun a ha b hb h1 h2 => by
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 (hms.mem_iff.1 ha)
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 (hms.mem_iff.1 hb)
    rw [huniq a0 ha0 b0 hb0 h1 h2]), List.find?_map, Option.map_map]
  have hf : (fun y => Ty.deq m.key y.1 (Ty.up _ m.key_data k)) ∘ U = fun p => (Ty.semWith Dsl.base m.key).2 k p.1 := by
    funext p; simp only [Function.comp_apply, U, hbeq]
  rw [hf]
  congr 1
  funext p
  obtain ⟨a, x0, x1, ⟨⟩⟩ := p
  simp only [Function.comp_apply, U, instOf, entryOf, val_timerOf]

theorem _root_.Tazuna.Ir.MachineV.after_data (m : MachineV r e) : (Ty.option (Ty.timer m.state)).isData = true := by
  simp [Ty.option, Ty.timer, Ty.isData, Ty.isDatas, Ty.isDatass, m.state_data]

theorem _root_.Tazuna.Ir.MachineV.timer_data (m : MachineV r e) : (Ty.option (.tuple [.int, m.state])).isData = true := by
  simp [Ty.option, Ty.isData, Ty.isDatas, Ty.isDatass, m.state_data]

/-- The timer term denotes the timer `after`'s value asks for. -/
theorem timerT_rel (m : MachineV r e) {now at_ t : Term} {tnow : Int} (hnow : now.denote M = .int tnow)
    (a : (Ty.option (Ty.timer m.state)).den0) (ha : RelV L _ (Ty.up _ m.after_data a) (at_.denote M))
    (h : timerT L m now at_ = .ok t) :
    RelV L (Ty.option (.tuple [.int, m.state])) (Ty.up _ m.timer_data (timerVal (Step.timerAt tnow a))) (t.denote M) := by
  have hs := m.state_data
  obtain ⟨⟨dopt, n1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨⟨dtm, n2⟩, h2, h⟩ := bind_ok.1 h
  obtain ⟨⟨dent, n3⟩, h3, h⟩ := bind_ok.1 h
  obtain ⟨dp, h4, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  replace h1 := need_ok.1 h1
  replace h2 := need_ok.1 h2
  replace h3 := need_ok.1 h3
  obtain ⟨n4, h4⟩ := tupleD_ok h4
  have htm1 : (Ty.tuple [Ty.timer m.state]).isData = true := by simp [Ty.timer, Ty.isData, Ty.isDatas, Ty.isDatass, hs]
  have hent1 : (Ty.tuple [.tuple [.int, m.state]]).isData = true := by simp [Ty.isData, Ty.isDatas, hs]
  have hpair : (Ty.tuple [.int, m.state]).isData = true := by simp [Ty.isData, Ty.isDatas, hs]
  have hnone : (Ty.adt 3 [Ty.timer m.state] [[]]).isData = true := by simp [Ty.isData, Ty.isDatass, Ty.isDatas]
  have hnone' : (Ty.adt 3 [.tuple [.int, m.state]] [[]]).isData = true := by simp [Ty.isData, Ty.isDatass, Ty.isDatas]
  obtain ⟨d', n', hf', hra⟩ := ha
  obtain rfl := find_det hf' h1
  match a with
  | .inl (.inl (dl, target, ()), ()) =>
    erw [Ty.up_inl 3 _ [Ty.timer m.state] [[]] m.after_data htm1] at hra
    obtain ⟨vals, hv, hvals⟩ := hra
    erw [Ty.up_tuple _ _ _ (by simp [Ty.timer, Ty.isData, Ty.isDatas, Ty.isDatass, hs]) rfl] at hvals
    obtain ⟨v0, _, rfl, hv0, rfl⟩ := hvals
    obtain ⟨d7, n7, hf7, hr7⟩ := hv0
    obtain rfl := find_det hf7 h2
    erw [Ty.up_inl 7 _ [.int, m.state] [] (by simp [Ty.isData, Ty.isDatas, Ty.isDatass, hs]) hpair] at hr7
    obtain ⟨vals7, hv7, hvals7⟩ := hr7
    erw [Ty.up_tuple _ _ _ rfl (by simp [Ty.isData, Ty.isDatas, hs])] at hvals7
    obtain ⟨vd, vs7, rfl, hvd, hvals7⟩ := hvals7
    erw [Ty.up_tuple _ _ _ hs rfl] at hvals7
    obtain ⟨vt, _, rfl, hvt, rfl⟩ := hvals7
    change vd = .int dl at hvd
    subst hvd
    have hden : (Term.ite (.is d' 0 at_)
        (.ctor dent 0 [.ctor dp 0 [.add now (.sel d7 0 0 (.sel d' 0 0 at_)), .sel d7 0 1 (.sel d' 0 0 at_)]])
        (.ctor dent 1 [])).denote M = .ctor dent 0 [.ctor dp 0 [.int (tnow + (show Int from dl)), vt]] := by
      simp [Term.denote, hv, hv7, hnow, Val.toBool, Term.denotes, Val.toInt]
    rw [hden]
    refine ⟨dent, n3, h3, ?_⟩
    show RelAlts L dent 0 _ (Ty.up _ m.timer_data (.inl ((tnow + (show Int from dl), target, ()), ()))) _
    erw [Ty.up_inl 3 _ [.tuple [.int, m.state]] [[]] m.timer_data hent1]
    refine ⟨_, rfl, ?_⟩
    erw [Ty.up_tuple _ _ _ hpair rfl]
    refine ⟨_, _, rfl, ⟨dp, n4, _, h4, rfl, ?_⟩, rfl⟩
    erw [Ty.up_tuple _ _ _ rfl (by simp [Ty.isData, Ty.isDatas, hs])]
    refine ⟨_, _, rfl, rfl, ?_⟩
    erw [Ty.up_tuple _ _ _ hs rfl]
    exact ⟨_, _, rfl, hvt, rfl⟩
  | .inr (.inl ()) =>
    erw [Ty.up_inr 3 _ [Ty.timer m.state] [[]] m.after_data hnone, Ty.up_inl 3 _ [] [] hnone rfl] at hra
    obtain ⟨vals, hv, -⟩ := hra
    have hden : (Term.ite (.is d' 0 at_)
        (.ctor dent 0 [.ctor dp 0 [.add now (.sel dtm 0 0 (.sel d' 0 0 at_)), .sel dtm 0 1 (.sel d' 0 0 at_)]])
        (.ctor dent 1 [])).denote M = .ctor dent 1 [] := by
      simp [Term.denote, hv, Val.toBool, Term.denotes]
    rw [hden]
    refine ⟨dent, n3, h3, ?_⟩
    show RelAlts L dent 0 _ (Ty.up _ m.timer_data (.inr (.inl ()))) _
    erw [Ty.up_inr 3 _ [.tuple [.int, m.state]] [[]] m.timer_data hnone', Ty.up_inl 3 _ [] [] hnone' rfl]
    exact ⟨[], rfl, rfl⟩
  | .inr (.inr x) => nomatch x

theorem entry_up (m : MachineV r e) (st : m.state.den0) (t : (Ty.option (.tuple [.int, m.state])).den0) :
    Ty.up (instEntry m.state) m.entry_data (st, t, ()) = (Ty.up _ m.state_data st, Ty.up _ m.timer_data t, ()) := by
  erw [Ty.up_tuple _ _ _ m.state_data (by simp [Ty.isData, Ty.isDatas, m.timer_data]),
    Ty.up_tuple _ _ _ m.timer_data rfl]
  rfl

/-- An entry's value is its datatype's constructor with the state's and the timer's values. -/
theorem entry_rel_iff (m : MachineV r e) {de n : Nat} (hde : L.find? (instEntry m.state) = some (de, n))
    (st : m.state.den0) (t : (Ty.option (.tuple [.int, m.state])).den0) (w : Val) :
    RelV L (instEntry m.state) (Ty.up _ m.entry_data (st, t, ())) w ↔
      ∃ v0 v1, w = .ctor de 0 [v0, v1] ∧ RelV L m.state (Ty.up _ m.state_data st) v0 ∧
        RelV L _ (Ty.up _ m.timer_data t) v1 := by
  rw [entry_up]
  constructor
  · rintro ⟨d', n', vals, hf, rfl, v0, _, rfl, h0, v1, _, rfl, h1, rfl⟩
    obtain rfl := find_det hf hde
    exact ⟨v0, v1, rfl, h0, h1⟩
  · rintro ⟨v0, v1, rfl, h0, h1⟩
    exact ⟨de, n, _, hde, rfl, v0, _, rfl, h0, v1, _, rfl, h1, rfl⟩

theorem any_find? {α : Type} (p : α → Bool) (l : List α) : l.any p = (l.find? p).isSome := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.find?_isSome]

theorem _root_.Tazuna.Ir.MachineV.next_data (m : MachineV r e) : (Ty.next m.state).isData = true := by
  simp [Ty.next, Ty.isData, Ty.isDatas, Ty.isDatass, m.state_data]

theorem _root_.Tazuna.Ir.MachineV.event_data (m : MachineV r e) : e.isData = true := by
  have h := m.on.ht
  simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at h
  exact h.1.2.1

/-- What `on` answers, as its value's constructor: Stay is constructor 0, Enter(s) constructor 1 with the state. -/
theorem next_rel (m : MachineV r e) {dn nn : Nat} (hdn : L.find? (Ty.next m.state) = some (dn, nn))
    (x : (Ty.next m.state).den0) (w : Val) (h : RelV L _ (Ty.up _ m.next_data x) w) :
    match x with
    | .inr (.inl (s, ())) => ∃ v, w = .ctor dn 1 [v] ∧ RelV L m.state (Ty.up _ m.state_data s) v
    | _ => w = .ctor dn 0 [] := by
  have hs := m.state_data
  obtain ⟨d', n', hf, hr⟩ := h
  obtain rfl := find_det hf hdn
  have h1 : (Ty.adt 6 [m.state] [[m.state]]).isData = true := by simp [Ty.isData, Ty.isDatas, Ty.isDatass, hs]
  match x with
  | .inl () =>
    erw [Ty.up_inl 6 _ [] [[m.state]] m.next_data rfl] at hr
    obtain ⟨vals, hv, hvals⟩ := hr
    cases hvals; exact hv
  | .inr (.inl (s, ())) =>
    erw [Ty.up_inr 6 _ [] [[m.state]] m.next_data h1, Ty.up_inl 6 _ [m.state] [] h1 (by simp [Ty.isData, Ty.isDatas, hs])]
      at hr
    obtain ⟨vals, hv, hvals⟩ := hr
    erw [Ty.up_tuple _ _ _ hs rfl] at hvals
    obtain ⟨v, _, rfl, hvr, rfl⟩ := hvals
    exact ⟨v, hv, hvr⟩
  | .inr (.inr x) => nomatch x

theorem ctx_rel (m : MachineV r e) {key st records now ctxT : Term} {k : m.key.den0} {sv : m.state.den0} {recs : r.den0}
    {tnow : Int} (hk : RelV L m.key (Ty.up _ m.key_data k) (key.denote M))
    (hs : RelV L m.state (Ty.up _ m.state_data sv) (st.denote M))
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (h : instCtxT L m key st records now = .ok ctxT) {cx : Code (Ty.machineCtx m.key m.state r)}
    (hcx : Code.ofTerm? _ ctxT = some cx) :
    Smt.Rel M L _ (Ty.up _ m.ctx_data (.inl (k, sv, recs, tnow, ()))) cx := by
  have hctx := adtCtor_rel (L := L) (M := M) (vs := [[m.key, m.state, r, .int]]) ⟨0, by simp⟩ _ _ h
    (Ty.up _ m.key_data k, Ty.up _ m.state_data sv, Ty.up _ m.records_data recs, tnow, ())
    ⟨_, _, rfl, hk, _, _, rfl, hs, _, _, rfl, hrec, _, _, rfl, hnow, rfl⟩
  rw [← up_mctx m m.ctx_data] at hctx
  exact (rel_ofTerm hcx _).2 hctx

/-- The after code applied to an instance's context. -/
theorem after_app (m : MachineV r e) {af : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (Ty.timer m.state)))}
    (haf : Smt.Rel M L _ (Ty.up _ m.after.ht m.after.fn) af) {x : (Ty.machineCtx m.key m.state r).den0}
    {cx : Code _} (hcx : Smt.Rel M L _ (Ty.up _ m.ctx_data x) cx) {a : Code _} {c : Term}
    (h : af (cx, ()) = .ok (a, c)) (hc : Holds M c) : Smt.Rel M L _ (Ty.up _ m.after_data (m.after.fn (x, ()))) a := by
  have hargs : (Ty.tuple [Ty.machineCtx m.key m.state r]).isData = true := by simp [Ty.isData, Ty.isDatas, m.ctx_data]
  have hrels : Smt.Rels M L [Ty.machineCtx m.key m.state r] (Ty.up (.tuple [_]) hargs (x, ())) (cx, ()) := by
    show Smt.Rel M L _ (Ty.up (.tuple [Ty.machineCtx m.key m.state r]) hargs (x, ())).1 cx ∧ True
    erw [Ty.up_tuple _ _ _ m.ctx_data rfl]; exact ⟨hcx, trivial⟩
  have := haf _ _ hrels a c h hc
  erw [Ty.up_fn _ _ _ hargs m.after_data] at this
  exact this

/-- The on code applied to an instance's context and the event. -/
theorem on_app (m : MachineV r e) {oc : Code (Ty.fn [Ty.machineCtx m.key m.state r, e] (Ty.next m.state))}
    (hon : Smt.Rel M L _ (Ty.up _ m.on.ht m.on.fn) oc) {x : (Ty.machineCtx m.key m.state r).den0} {ev : e.den0}
    {cx : Code _} (hcx : Smt.Rel M L _ (Ty.up _ m.ctx_data x) cx) {evc : Code e}
    (hev : Smt.Rel M L e (Ty.up _ m.event_data ev) evc) {o : Code _} {c : Term}
    (h : oc (cx, evc, ()) = .ok (o, c)) (hc : Holds M c) : Smt.Rel M L _ (Ty.up _ m.next_data (m.on.fn (x, ev, ()))) o := by
  have hargs : (Ty.tuple [Ty.machineCtx m.key m.state r, e]).isData = true := by
    simp [Ty.isData, Ty.isDatas, m.ctx_data, m.event_data]
  have hrels : Smt.Rels M L [Ty.machineCtx m.key m.state r, e] (Ty.up (.tuple [_, _]) hargs (x, ev, ())) (cx, evc, ()) := by
    show Smt.Rel M L _ (Ty.up (.tuple [Ty.machineCtx m.key m.state r, e]) hargs (x, ev, ())).1 cx ∧
      Smt.Rels M L [e] (Ty.up (.tuple [Ty.machineCtx m.key m.state r, e]) hargs (x, ev, ())).2 (evc, ())
    erw [Ty.up_tuple _ _ _ m.ctx_data (by simp [Ty.isData, Ty.isDatas, m.event_data])]
    refine ⟨hcx, ?_⟩
    show Smt.Rel M L _ (Ty.up (.tuple [e]) (by simp [Ty.isData, Ty.isDatas, m.event_data]) (ev, ())).1 evc ∧ True
    erw [Ty.up_tuple _ _ _ m.event_data rfl]; exact ⟨hev, trivial⟩
  have := hon _ _ hrels o c h hc
  erw [Ty.up_fn _ _ _ hargs m.next_data] at this
  exact this

/-- The effect option the instance of key `k` starts on an event, as the effect code returns it: the effect of the
state it enters (an instance starts at `initial`, or `on` gives Enter), else none. -/
def startedOf (m : MachineV r e) (insts : List (Step.Instance m)) (recs : r.den0) (tnow : Int) (ev : e.den0)
    (k : m.key.den0) : (Ty.option (.dsl .effect [e])).den :=
  match insts.find? ((Ty.semWith Dsl.base m.key).2 k ·.key) with
  | some i => match m.on.fn (.inl (i.key, i.state, recs, tnow, ()), ev, ()) with
    | .inr (.inl (s, ())) => m.effect.apply (.inl (i.key, s, recs, tnow, ()), ())
    | _ => .inr (.inl ())
  | none => m.effect.apply (.inl (k, m.initial, recs, tnow, ()), ())

/-- The effects the step starts for the key `k` are the option `startedOf` gives, sent by the instance of `k`. -/
theorem reactKey_effects (m : MachineV r e) (hpl : m.key.plain = true) (insts : List (Step.Instance m)) (recs : r.den0)
    (tnow : Int) (ev : e.den0) (k : m.key.den0) :
    (Step.reactKey m insts recs tnow ev k).2 =
      (Ty.toOption (startedOf m insts recs tnow ev k)).toList.map (.machine m.name ⟨m.key, k⟩, ·) := by
  unfold Step.reactKey startedOf
  cases h : insts.find? (fun i => (Ty.semWith Dsl.base m.key).2 k i.key) with
  | none => rfl
  | some i =>
    have hki : i.key = k := by
      have := List.find?_some h
      exact ((Ty.beq_plain _ hpl _ _).1 this).symm
    subst hki
    simp only
    cases hon : m.on.fn (.inl (i.key, i.state, recs, tnow, ()), ev, ()) with
    | inl _ => rfl
    | inr x => match x with
      | .inl (s, ()) => rfl
      | .inr y => nomatch y

/-- The effect code relates to the machine's effect at every context. -/
def EffectCodeRel (m : MachineV r e) (xc : Code (Ty.fn [Ty.machineCtx m.key m.state r] (Ty.option (.dsl .effect [e]))))
    : Prop :=
  ∀ (x : (Ty.machineCtx m.key m.state r).den0) (cx : Code _), Smt.Rel M L _ (Ty.up _ m.ctx_data x) cx →
    ∀ o c, xc (cx, ()) = .ok (o, c) → Holds M c → Smt.Rel M L _ (m.effect.apply (x, ())) o

theorem effect_codeRel (m : MachineV r e) {xc : Code _} {c : Term} (h : m.effect.code L = .ok (xc, c)) (hc : Holds M c) :
    EffectCodeRel (M := M) (L := L) m xc := by
  intro x cx hcx o c' ho hc'
  have hargs : (Ty.tuple [Ty.machineCtx m.key m.state r]).isData = true := m.effect.hps
  have hrels : Smt.Rels M L [Ty.machineCtx m.key m.state r] (Ty.up (.tuple [_]) m.effect.hps (x, ())) (cx, ()) := by
    show Smt.Rel M L _ (Ty.up (.tuple [Ty.machineCtx m.key m.state r]) hargs (x, ())).1 cx ∧ True
    erw [Ty.up_tuple _ _ _ m.ctx_data rfl]; exact ⟨hcx, trivial⟩
  exact m.effect.code_apply h hc (x, ()) (cx, ()) hrels ho hc'

/-- The none value of an effect option and its term. -/
theorem none_rel {dopt nopt : Nat} (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt)) :
    RelV L (Ty.option (.dsl .effect [e])) (.inr (.inl ())) (.ctor dopt 1 []) :=
  ⟨dopt, nopt, hopt, [], rfl, by simp [RelVs]⟩

/-- One occupied slot of the instances bag, holding the key `k`: its new table slot holds `k` and the entry of the
instance the step gives that key. -/
theorem react_at (m : MachineV r e) (hpl : m.key.plain = true) (rc : ReactCode m)
    (hon : Smt.Rel M L _ (Ty.up _ m.on.ht m.on.fn) rc.on) (haf : Smt.Rel M L _ (Ty.up _ m.after.ht m.after.fn) rc.after)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {evc : Code e} (hev : Smt.Rel M L e (Ty.up _ m.event_data ev) evc)
    (tbl : m.table.den0) {So : List Slot} {sv : List (Bool × List Val)} {ys : List (m.key.den × (instEntry m.state).den)}
    (hS : SlotsDen M So sv) (hw : ∀ p ∈ sv, p.2.length = 2) (hp : ys.Perm (Ty.up _ m.table_data tbl).1)
    (hh : Holds2 (ETab L m.key (instEntry m.state)) ys sv)
    {de nde dn nn : Nat} (hde : L.find? (instEntry m.state) = some (de, nde)) (hdn : L.find? (Ty.next m.state) = some (dn, nn))
    {init : Val} (hinit : embedV L m.state (Ty.up _ m.state_data m.initial) = some init) (dflt : Term)
    (hfx : EffectCodeRel (M := M) (L := L) m rc.effect) {dopt nopt : Nat}
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt))
    {f first : Term} {xs : List Term} {zk : Val} (hf : f.denote M = .bool true) (hxs : Term.denotes M xs = [zk])
    (k : m.key.den0) (hk : RelV L m.key (Ty.up _ m.key_data k) zk)
    {sl : Slot} {fx cj : Term}
    (hg : reactAt L m rc de dn So init dflt (.ctor dopt 1 []) records now evc ((f, xs), first) = .ok ((sl, fx), cj))
    (hcj : Holds M cj) :
    ∃ kt et, sl = (first, [kt, et]) ∧ kt.denote M = zk ∧
      RelV L (instEntry m.state)
        (Ty.up _ m.entry_data (entryOf (Step.reactKey m (instancesOf T m tbl) recs tnow ev k).1)) (et.denote M) ∧
      (Step.reactKey m (instancesOf T m tbl) recs tnow ev k).1.key = k ∧
      RelV L (Ty.option (.dsl .effect [e])) (startedOf m (instancesOf T m tbl) recs tnow ev k) (fx.denote M) := by
  obtain ⟨kt, rfl⟩ : ∃ kt, xs = [kt] := by
    match xs, hxs with
    | [kt], _ => exact ⟨kt, rfl⟩
  simp only [Term.denotes, List.cons.injEq, and_true] at hxs
  obtain ⟨kc, h1, hg⟩ := bind_ok.1 hg
  obtain ⟨hits, h2, hg⟩ := bind_ok.1 hg
  obtain ⟨octxT, h3, hg⟩ := bind_ok.1 hg
  obtain ⟨octx, h4, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨o, c1⟩, h5, hg⟩ := bind_ok.1 hg
  obtain ⟨ot, h6, hg⟩ := bind_ok.1 hg
  obtain ⟨nctxT, h7, hg⟩ := bind_ok.1 hg
  obtain ⟨nctx, h8, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨a, c2⟩, h9, hg⟩ := bind_ok.1 hg
  obtain ⟨at_, h10, hg⟩ := bind_ok.1 hg
  obtain ⟨tmT, h11, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨xo, c3⟩, h12, hg⟩ := bind_ok.1 hg
  obtain ⟨xt, h13, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  simp only [List.headD_cons] at h1 h3 h7
  refine ⟨kt, _, rfl, hxs, ?_⟩
  have hkr : RelV L m.key (Ty.up _ m.key_data k) (kt.denote M) := hxs ▸ hk
  have hkc : Smt.Rel M L m.key (Ty.up _ m.key_data k) kc := (rel_ofTerm (need_ok.1 h1) _).2 hkr
  obtain ⟨hfound, hpick⟩ := lookup_slots m hkc dflt So sv hits ys hS hw (mapM_ok _ _ _ h2) hh
  have hlook := lookup_eq (T := T) m hpl tbl hp k
  rw [any_find?, hlook] at hfound
  have hc' := (holds_ite _ _ _).1 hcj
  simp only [hf, Val.toBool, ite_true] at hc'
  obtain ⟨hc1', hc23'⟩ := (holds_andT _ _).1 hc'
  cases hfind : (instancesOf T m tbl).find? (fun i => (Ty.semWith Dsl.base m.key).2 k i.key) with
  | none =>
    rw [hfind] at hfound
    have hfd : (anyT (hits.map fun (g, h, _) => .and g h)).denote M = .bool false := hfound
    have hreact : Step.reactKey m (instancesOf T m tbl) recs tnow ev k = Step.enter m recs tnow k m.initial := by
      unfold Step.reactKey; rw [hfind]
    have hstarted : startedOf m (instancesOf T m tbl) recs tnow ev k =
        m.effect.apply (.inl (k, m.initial, recs, tnow, ()), ()) := by
      unfold startedOf; rw [hfind]
    rw [hreact, hstarted]
    have hst : (Term.ite (anyT (hits.map fun (g, h, _) => .and g h)) (.ite (.is dn 1 ot) (.sel dn 1 0 ot)
        (.sel de 0 0 (pickT dflt hits))) init.term).denote M = init := by
      simp only [Term.denote, hfd, Val.toBool, Bool.false_eq_true, ite_false, Val.denote_term]
    have hstr : RelV L m.state (Ty.up _ m.state_data m.initial) init := embed_rel _ _ _ hinit
    have hcx := ctx_rel m hkr (hst ▸ hstr) hrec hnow h7 (need_ok.1 h8)
    obtain ⟨hc2, hc3⟩ : Holds M c2 ∧ Holds M c3 := by
      have := (holds_ite _ _ _).1 hc23'; simp [Term.denote, hfd, Val.toBool] at this; exact (holds_andT _ _).1 this
    have ha := after_app m haf hcx h9 hc2
    have hat := (rel_term (need_ok.1 h10) _).1 ha
    have htm := timerT_rel m hnow _ hat h11
    have hxo := (rel_term (need_ok.1 h13) _).1 (hfx _ _ hcx _ _ h12 hc3)
    refine ⟨?_, rfl, ?_⟩
    · simp only [entryOf, Step.enter]
      rw [entry_rel_iff m hde]
      refine ⟨_, _, rfl, by rw [hst]; exact hstr, ?_⟩
      simp only [Term.denote, hfd, Val.toBool, Bool.not_false, Bool.true_or, ite_true]
      exact htm
    · simp only [Term.denote, hfd, Val.toBool, Bool.not_false, Bool.true_or, ite_true]
      exact hxo
  | some i =>
    rw [hfind] at hfound hlook
    have hfd : (anyT (hits.map fun (g, h, _) => .and g h)).denote M = .bool true := hfound
    have hki : i.key = k := by
      have := List.find?_some hfind
      exact ((Ty.beq_plain _ hpl _ _).1 this).symm
    subst hki
    have hc1 : Holds M c1 := by
      have := (holds_ite _ _ _).1 hc1'; simpa [hfd, Val.toBool] using this
    have hold := hpick _ (by rw [hlook]; rfl)
    obtain ⟨v0, v1, hv, hv0, hv1⟩ := (entry_rel_iff m hde _ _ _).1 hold
    have hsel0 : (Term.sel de 0 0 (pickT dflt hits)).denote M = v0 := by rw [sel_ctor _ hv]; rfl
    have hsel1 : (Term.sel de 0 1 (pickT dflt hits)).denote M = v1 := by rw [sel_ctor _ hv]; rfl
    have hocx := ctx_rel m hkr (hsel0 ▸ hv0) hrec hnow h3 (need_ok.1 h4)
    have hoo := on_app m hon hocx hev h5 hc1
    have hot := (rel_term (need_ok.1 h6) _).1 hoo
    unfold Step.reactKey startedOf
    rw [hfind]
    simp only
    cases hon' : m.on.fn (.inl (i.key, i.state, recs, tnow, ()), ev, ()) with
    | inl u =>
      rw [hon'] at hot
      have hnext : ot.denote M = .ctor dn 0 [] := next_rel m hdn _ _ hot
      show RelV L (instEntry m.state) (Ty.up _ m.entry_data (entryOf i)) _ ∧ i.key = i.key ∧ _
      refine ⟨?_, rfl, ?_⟩
      · simp only [entryOf]
        rw [entry_rel_iff m hde]
        exact ⟨v0, v1, by simp [Term.denote, hfd, hnext, Val.toBool, hv, Term.denotes], hv0, hv1⟩
      · simp [Term.denote, hfd, hnext, Val.toBool, Term.denotes]
        exact none_rel hopt
    | inr x =>
      match x with
      | .inl (s', ()) =>
        rw [hon'] at hot
        obtain ⟨vs, hvs, hvsr⟩ := next_rel m hdn _ _ hot
        have hst : (Term.ite (anyT (hits.map fun (g, h, _) => .and g h)) (.ite (.is dn 1 ot) (.sel dn 1 0 ot)
            (.sel de 0 0 (pickT dflt hits))) init.term).denote M = vs := by
          simp [Term.denote, hfd, hvs, Val.toBool]
        have hcx := ctx_rel m hkr (by rw [hst]; exact hvsr) hrec hnow h7 (need_ok.1 h8)
        obtain ⟨hc2, hc3⟩ : Holds M c2 ∧ Holds M c3 := by
          have := (holds_ite _ _ _).1 hc23'
          simp [Term.denote, hfd, hvs, Val.toBool] at this; exact (holds_andT _ _).1 this
        have ha := after_app m haf hcx h9 hc2
        have hat := (rel_term (need_ok.1 h10) _).1 ha
        have htm := timerT_rel m hnow _ hat h11
        have hxo := (rel_term (need_ok.1 h13) _).1 (hfx _ _ hcx _ _ h12 hc3)
        refine ⟨?_, rfl, ?_⟩
        · simp only [entryOf, Step.enter]
          rw [entry_rel_iff m hde]
          exact ⟨vs, tmT.denote M, by simp [Term.denote, Term.denotes, hfd, hvs, Val.toBool], hvsr, htm⟩
        · simpa [Term.denote, hfd, hvs, Val.toBool] using hxo
      | .inr y => nomatch y

theorem reactAt_shape (m : MachineV r e) {rc : ReactCode m} {de dn : Nat} {So : List Slot} {init : Val}
    {dflt noneT records now : Term} {evc : Code e} {f first : Term} {xs : List Term} {sl : Slot} {fx cj : Term}
    (hg : reactAt L m rc de dn So init dflt noneT records now evc ((f, xs), first) = .ok ((sl, fx), cj)) :
    ∃ kt et, sl = (first, [kt, et]) ∧ xs.headD tt = kt := by
  repeat obtain ⟨_, _, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  exact ⟨_, _, rfl, rfl⟩

/-- Deduplicating one more value: it is kept when no earlier value equals it. -/
theorem dedupBy_append_one {α : Type} (eq : α → α → Bool) (xs : List α) (x : α) :
    dedupBy eq (xs ++ [x]) = if (dedupBy eq xs).any (eq x) then dedupBy eq xs else dedupBy eq xs ++ [x] := by
  simp [dedupBy, List.foldl_append]

/-- The terms that no earlier occupied slot holds the key: each earlier occupied item compared with it. -/
theorem prev_eqs (m : MachineV r e) {kc : Code m.key} {k : m.key.den} (hk : Smt.Rel M L m.key k kc) :
    (prevS : List Slot) → (svP : List (Bool × List Val)) → (ysP : List m.key.den) → SlotsDen M prevS svP →
    (∀ p ∈ svP, p.2.length = 1) → Holds2 (EBag L m.key) ysP svP → {eqs : List Term} →
    prevS.mapM (fun (f', xs') => do
      pure (Term.and f' (← eqCode L m.key (← need "an item that has no term" (Code.ofTerm? m.key (xs'.headD tt))) kc)))
      = .ok eqs →
    (allT (eqs.map .not)).denote M = .bool !(ysP.any fun y => Ty.deq m.key y k)
  | [], [], ysP, _, _, hy, eqs, h => by
    cases ysP with
    | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
    | cons _ _ => exact hy.elim
  | (f, xs) :: prevS, (b, vs) :: svP, ysP, ⟨hf, hxs, hS⟩, hw, hy, eqs, h => by
    have hw' : ∀ p ∈ svP, p.2.length = 1 := fun p hp => hw p (by simp [hp])
    rw [List.mapM_cons] at h
    obtain ⟨q, h1, h⟩ := bind_ok.1 h
    obtain ⟨qs, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨kt, h3, h1⟩ := bind_ok.1 h1
    obtain ⟨e', h4, h1⟩ := bind_ok.1 h1
    cases pure_ok.1 h1
    cases b with
    | false =>
      have ih := prev_eqs m hk prevS svP ysP hS hw' (by simpa [Holds2, occupied] using hy) h2
      simp only [List.map_cons, allT, Term.denote, hf, Val.toBool, Bool.false_and, Bool.not_false, Bool.true_and]
      rw [ih]
    | true =>
      match ysP, hy with
      | y :: ysP, ⟨⟨z, hz, hyz⟩, hys⟩ =>
        have ih := prev_eqs m hk prevS svP ysP hS hw' hys h2
        obtain ⟨t0, rfl⟩ : ∃ t0, xs = [t0] := by
          have := hxs.trans hz
          match xs, this with
          | [t0], _ => exact ⟨t0, rfl⟩
        rw [hz] at hxs
        simp only [Term.denotes, List.cons.injEq, and_true] at hxs
        simp only [List.headD_cons] at h3
        have hkt : Smt.Rel M L m.key y kt := (rel_ofTerm (need_ok.1 h3) _).2 (hxs ▸ hyz)
        have he := eqCode_rel hkt hk h4
        simp only [List.map_cons, allT, Term.denote, hf, he, Val.toBool, Bool.true_and, List.any_cons]
        rw [ih]
        cases Ty.deq m.key y k <;> rfl
  | [], _ :: _, _, h, _, _, _, _ | _ :: _, [], _, h, _, _, _, _ => h.elim

theorem deq_down (m : MachineV r e) (a b : m.key.den) :
    Ty.deq m.key a b = (Ty.semWith Dsl.base m.key).2 (Ty.down _ m.key_data a) (Ty.down _ m.key_data b) := by
  rw [← Ty.deq_up m.key m.key_data, Ty.up_down, Ty.up_down]

theorem holds2_append_unoccupied {α : Type} {E : α → List Val → Prop} {ys : List α} {sv : List (Bool × List Val)}
    (h : Holds2 E ys sv) (vs : List Val) : Holds2 E ys (sv ++ [(false, vs)]) := by
  simpa [Holds2, occupied, List.filterMap_append] using h

theorem forall2_append_one {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    {as : List α} → {bs : List β} → Forall2 R as bs → Forall2 R (as ++ [a]) (bs ++ [b])
  | [], [], _ => ⟨hab, trivial⟩
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨h, forall2_append_one hab hs⟩

theorem holds2_append_occupied {α : Type} {E : α → List Val → Prop} {ys : List α} {sv : List (Bool × List Val)}
    (h : Holds2 E ys sv) {y : α} {vs : List Val} (hy : E y vs) : Holds2 E (ys ++ [y]) (sv ++ [(true, vs)]) := by
  unfold Holds2 at h ⊢
  rw [show occupied (sv ++ [(true, vs)]) = occupied sv ++ [vs] by simp [occupied, List.filterMap_append]]
  exact forall2_append_one hy h

/-- A key's new entry, as a table's slot relates to it: the key and the entry of the instance the step gives it. -/
def entryUp (m : MachineV r e) (insts : List (Step.Instance m)) (recs : r.den0) (tnow : Int) (ev : e.den0)
    (k : m.key.den0) : m.key.den × (instEntry m.state).den :=
  (Ty.up _ m.key_data k, Ty.up _ m.entry_data (entryOf (Step.reactKey m insts recs tnow ev k).1))

/-- A key's start, as a start slot relates to it: the key and the effect option the step starts for it. -/
def EStart (m : MachineV r e) (insts : List (Step.Instance m)) (recs : r.den0) (tnow : Int) (ev : e.den0) :
    m.key.den0 → List Val → Prop := fun k vs => ∃ zk z, vs = [zk, z] ∧ RelV L m.key (Ty.up _ m.key_data k) zk ∧
      RelV L (Ty.option (.dsl .effect [e])) (startedOf m insts recs tnow ev k) z

/-- The new table's slots for the bag's slots after `prevS`: occupied, in order, by the keys whose first occurrence
they hold, each with the entry the step gives it; the start slots alike, each with the effect option it starts. -/
theorem assemble (m : MachineV r e) (hpl : m.key.plain = true) (rc : ReactCode m)
    (hon : Smt.Rel M L _ (Ty.up _ m.on.ht m.on.fn) rc.on) (haf : Smt.Rel M L _ (Ty.up _ m.after.ht m.after.fn) rc.after)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {evc : Code e} (hev : Smt.Rel M L e (Ty.up _ m.event_data ev) evc)
    (tbl : m.table.den0) {So : List Slot} {sv : List (Bool × List Val)} {ys : List (m.key.den × (instEntry m.state).den)}
    (hS : SlotsDen M So sv) (hw : ∀ p ∈ sv, p.2.length = 2) (hp : ys.Perm (Ty.up _ m.table_data tbl).1)
    (hh : Holds2 (ETab L m.key (instEntry m.state)) ys sv)
    {de nde dn nn : Nat} (hde : L.find? (instEntry m.state) = some (de, nde)) (hdn : L.find? (Ty.next m.state) = some (dn, nn))
    {init : Val} (hinit : embedV L m.state (Ty.up _ m.state_data m.initial) = some init) (dflt : Term)
    (hfx : EffectCodeRel (M := M) (L := L) m rc.effect) {dopt nopt : Nat}
    (hopt : L.find? (Ty.option (.dsl .effect [e])) = some (dopt, nopt)) :
    (SB : List Slot) → (svB : List (Bool × List Val)) → (ysB : List m.key.den) →
    (prevS : List Slot) → (svP : List (Bool × List Val)) → (ysP : List m.key.den) →
    {firsts : List Term} → {outs : List ((Slot × Term) × Term)} →
    SlotsDen M SB svB → (∀ p ∈ svB, p.2.length = 1) → Holds2 (EBag L m.key) ysB svB →
    SlotsDen M prevS svP → (∀ p ∈ svP, p.2.length = 1) → Holds2 (EBag L m.key) ysP svP →
    firstSlots L m.key prevS SB = .ok firsts →
    Forall2 (fun p o => reactAt L m rc de dn So init dflt (.ctor dopt 1 []) records now evc p = .ok o) (SB.zip firsts)
      outs →
    (∀ o ∈ outs, Holds M o.2) →
    ∃ svN svX E, SlotsDen M (outs.map (·.1.1)) svN ∧ svN.length = SB.length ∧ (∀ p ∈ svN, p.2.length = 2) ∧
      dedupBy (Ty.semWith Dsl.base m.key).2 ((ysP ++ ysB).map (Ty.down _ m.key_data)) =
        dedupBy (Ty.semWith Dsl.base m.key).2 (ysP.map (Ty.down _ m.key_data)) ++ E ∧
      Holds2 (ETab L m.key (instEntry m.state)) (E.map (entryUp m (instancesOf T m tbl) recs tnow ev)) svN ∧
      SlotsDen M (outs.map fun ((sl, x), _) => (sl.1, [sl.2.headD tt, x])) svX ∧
      Holds2 (EStart (L := L) m (instancesOf T m tbl) recs tnow ev) E svX
  | [], [], ysB, prevS, svP, ysP, firsts, outs, _, _, hyB, _, _, _, hfs, ho, _ => by
    cases ysB with
    | cons _ _ => exact hyB.elim
    | nil =>
      simp only [firstSlots, pure, Except.pure, Except.ok.injEq] at hfs
      subst hfs
      cases outs with
      | cons _ _ => exact ho.elim
      | nil => exact ⟨[], [], [], trivial, rfl, by simp, by simp, trivial, trivial, trivial⟩
  | (f, xs) :: SB, (b, vs) :: svB, ysB, prevS, svP, ysP, firsts, outs, ⟨hf, hxs, hSB⟩, hwB, hyB, hSP, hwP, hyP, hfs,
      ho, hc => by
    have hwB' : ∀ p ∈ svB, p.2.length = 1 := fun p hp => hwB p (by simp [hp])
    have hwv : vs.length = 1 := hwB (b, vs) (by simp)
    obtain ⟨kc, h1, hfs⟩ := bind_ok.1 hfs
    obtain ⟨eqs, h2, hfs⟩ := bind_ok.1 hfs
    obtain ⟨rest, h3, hfs⟩ := bind_ok.1 hfs
    cases pure_ok.1 hfs
    match outs, ho with
    | o :: outs, ⟨ho1, hos⟩ =>
    have hc' : ∀ o ∈ outs, Holds M o.2 := fun o h => hc o (by simp [h])
    obtain ⟨⟨sl, fx⟩, cj⟩ := o
    obtain ⟨kt, et, hsl, -⟩ := reactAt_shape m ho1
    subst hsl
    have hwP' : ∀ p ∈ svP ++ [(b, vs)], p.2.length = 1 := by
      intro p hp; rcases List.mem_append.1 hp with hp | hp
      · exact hwP p hp
      · simp at hp; subst hp; exact hwv
    have hSP' : SlotsDen M (prevS ++ [(f, xs)]) (svP ++ [(b, vs)]) := slotsDen_append hSP ⟨hf, hxs, trivial⟩
    have hden2 : Term.denotes M [kt, et] = [kt.denote M, et.denote M] := rfl
    cases b with
    | false =>
      obtain ⟨svN, svX, E, hN, hl, hwN, hE, hhN, hX, hhX⟩ := assemble m hpl rc hon haf recs tnow ev hrec hnow hev tbl hS hw
        hp hh hde hdn hinit dflt hfx hopt SB svB ysB _ _ ysP hSB hwB' (by simpa [Holds2, occupied] using hyB) hSP' hwP'
        (holds2_append_unoccupied hyP vs) h3 hos hc'
      have hf0 : (Term.and f (allT (eqs.map .not))).denote M = .bool false := by simp [Term.denote, hf, Val.toBool]
      refine ⟨(false, [kt.denote M, et.denote M]) :: svN, (false, [kt.denote M, fx.denote M]) :: svX, E, ⟨hf0, hden2, hN⟩,
        by simp [hl], ?_, hE, ?_, ⟨hf0, rfl, hX⟩, by simpa [Holds2, occupied] using hhX⟩
      · intro p hp; rcases List.mem_cons.1 hp with rfl | hp
        · rfl
        · exact hwN p hp
      · simpa [Holds2, occupied] using hhN
    | true =>
      match ysB, hyB with
      | y :: ysB, ⟨⟨z, hz, hyz⟩, hys⟩ =>
      subst hz
      obtain ⟨t0, rfl⟩ : ∃ t0, xs = [t0] := by
        match xs, hxs with
        | [t0], _ => exact ⟨t0, rfl⟩
      simp only [Term.denotes, List.cons.injEq, and_true] at hxs
      simp only [List.headD_cons] at h1
      have hkc : Smt.Rel M L m.key y kc := (rel_ofTerm (need_ok.1 h1) _).2 (hxs ▸ hyz)
      have hprev := prev_eqs m hkc prevS svP ysP hSP hwP hyP h2
      obtain ⟨svN, svX, E, hN, hl, hwN, hE, hhN, hX, hhX⟩ := assemble m hpl rc hon haf recs tnow ev hrec hnow hev tbl hS hw
        hp hh hde hdn hinit dflt hfx hopt SB svB ysB _ _ (ysP ++ [y]) hSB hwB' hys hSP' hwP'
        (holds2_append_occupied hyP ⟨z, rfl, hyz⟩) h3 hos hc'
      have hany : (dedupBy (Ty.semWith Dsl.base m.key).2 (ysP.map (Ty.down _ m.key_data))).any
          ((Ty.semWith Dsl.base m.key).2 (Ty.down _ m.key_data y)) = ysP.any fun y' => Ty.deq m.key y' y := by
        rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
        constructor
        · rintro ⟨a, ha, hya⟩
          obtain ⟨y', hy', rfl⟩ := List.mem_map.1 ((mem_dedupBy (Ty.beq_plain _ hpl) _ _).1 ha)
          exact ⟨y', hy', by rw [deq_down, beq_symm_plain hpl]; exact hya⟩
        · rintro ⟨y', hy', hd⟩
          refine ⟨_, (mem_dedupBy (Ty.beq_plain _ hpl) _ _).2 (List.mem_map.2 ⟨y', hy', rfl⟩), ?_⟩
          rw [deq_down, beq_symm_plain hpl] at hd; exact hd
      have hsplit : (ysP ++ y :: ysB).map (Ty.down _ m.key_data) =
          ((ysP ++ [y]) ++ ysB).map (Ty.down _ m.key_data) := by simp
      rw [hsplit, hE, List.map_append, List.map_singleton, dedupBy_append_one, hany]
      have hfirst : (Term.and f (allT (eqs.map .not))).denote M = .bool !(ysP.any fun y' => Ty.deq m.key y' y) := by
        simp only [Term.denote, hf, hprev, Val.toBool, Bool.true_and]
      cases hb : ysP.any fun y' => Ty.deq m.key y' y with
      | true =>
        have hf0 : (Term.and f (allT (eqs.map .not))).denote M = .bool false := by rw [hfirst, hb]; rfl
        refine ⟨(false, [kt.denote M, et.denote M]) :: svN, (false, [kt.denote M, fx.denote M]) :: svX, E,
          ⟨hf0, hden2, hN⟩, by simp [hl], ?_, by simp, ?_, ⟨hf0, rfl, hX⟩, by simpa [Holds2, occupied] using hhX⟩
        · intro p hp; rcases List.mem_cons.1 hp with rfl | hp
          · rfl
          · exact hwN p hp
        · simpa [Holds2, occupied] using hhN
      | false =>
        have hk : RelV L m.key (Ty.up _ m.key_data (Ty.down _ m.key_data y)) z := by rw [Ty.up_down]; exact hyz
        obtain ⟨kt', et', hsl, hkt, het, -, hfxr⟩ := react_at (T := T) m hpl rc hon haf recs tnow ev hrec hnow hev tbl hS
          hw hp hh hde hdn hinit dflt hfx hopt hf (by simp [Term.denotes, hxs]) _ hk ho1
          (hc (((f.and (allT (eqs.map .not)), [kt, et]), fx), cj) (by simp))
        simp only [Prod.mk.injEq, List.cons.injEq, and_true] at hsl
        obtain ⟨-, rfl, rfl⟩ := hsl
        have hf1 : (Term.and f (allT (eqs.map .not))).denote M = .bool true := by rw [hfirst, hb]; rfl
        refine ⟨(true, [z, et.denote M]) :: svN, (true, [z, fx.denote M]) :: svX, Ty.down _ m.key_data y :: E,
          ⟨hf1, by simp [Term.denotes, hkt], hN⟩, by simp [hl], ?_, by simp, ?_,
          ⟨hf1, by simp [Term.denotes, hkt], hX⟩, ⟨⟨z, fx.denote M, rfl, hk, hfxr⟩, hhX⟩⟩
        · intro p hp; rcases List.mem_cons.1 hp with rfl | hp
          · rfl
          · exact hwN p hp
        · exact ⟨⟨z, et.denote M, rfl, hk, het⟩, hhN⟩
  | [], _ :: _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _ | _ :: _, [], _, _, _, _, _, _, h, _, _, _, _, _, _, _, _ =>
    h.elim

theorem reactKey_key (m : MachineV r e) (hpl : m.key.plain = true) (insts : List (Step.Instance m)) (recs : r.den0)
    (tnow : Int) (ev : e.den0) (k : m.key.den0) : (Step.reactKey m insts recs tnow ev k).1.key = k := by
  unfold Step.reactKey
  cases h : insts.find? (fun i => (Ty.semWith Dsl.base m.key).2 k i.key) with
  | none => rfl
  | some i =>
    have hki : i.key = k := by
      have := List.find?_some h
      exact ((Ty.beq_plain _ hpl _ _).1 this).symm
    simp only
    split <;> simp [Step.enter, hki]

theorem slotsDen_replicate (b : Bool) (ts : List Term) (hb : Term.denote M (.bool b) = .bool b) :
    (j : Nat) → SlotsDen M (List.replicate j (Term.bool b, ts)) (List.replicate j (b, Term.denotes M ts))
  | 0 => trivial
  | j + 1 => ⟨hb, rfl, slotsDen_replicate b ts hb j⟩

/-- T2 for a machine's reaction to an event: wherever the condition holds, the new table term denotes a table whose
instances, in key order, are the machine's instances after the step. -/
theorem react_step (m : MachineV r e) (hor : m.key.orderable = true) {rc : ReactCode m}
    {crc : Term} (hrc : ReactCode.of L m = .ok (rc, crc)) (hcrc : Holds M crc) (recs : r.den0) (tnow : Int) (ev : e.den0)
    {records now evT : Term} (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M))
    (hnow : now.denote M = .int tnow) (hevT : RelV L e (Ty.up _ m.event_data ev) (evT.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {o : ReactOut} {cond : Term} (henc : encodeReact L m rc x records now evT = .ok (o, cond)) (hc : Holds M cond) :
    (∃ tbl', RelV L m.table (Ty.up _ m.table_data tbl') (o.table.denote M) ∧
      instancesOf T m tbl' = (Step.machineStep T recs tnow ev ⟨m, instancesOf T m tbl⟩).1.2) ∧
    ∃ svX E, SlotsDen M (o.starts.map fun (f, k, x) => (f, [k, x])) svX ∧
      Holds2 (EStart (L := L) m (instancesOf T m tbl) recs tnow ev) E svX ∧
      E.Perm (Ty.sortBy T m.key (dedupBy (Ty.semWith Dsl.base m.key).2 (m.instances.fn (recs, ())))) := by
  have hpl := Ty.plain_of_orderable _ hor
  have hkd := m.key_data
  -- The codes.
  obtain ⟨⟨ic, c1⟩, g1, hrc⟩ := bind_ok.1 hrc
  obtain ⟨⟨oc, c2⟩, g2, hrc⟩ := bind_ok.1 hrc
  obtain ⟨⟨ac, c3⟩, g3, hrc⟩ := bind_ok.1 hrc
  obtain ⟨⟨xc, c4⟩, g4, hrc⟩ := bind_ok.1 hrc
  cases pure_ok.1 hrc
  obtain ⟨hc1, hc23⟩ := (holds_andT _ _).1 hcrc
  obtain ⟨hc2, hc34⟩ := (holds_andT _ _).1 hc23
  obtain ⟨hc3, hc4⟩ := (holds_andT _ _).1 hc34
  have hfx := effect_codeRel (M := M) m g4 hc4
  have hbagd : (Ty.fn [r] (.bag m.key)).isData = true := m.instances.ht
  have hi := m.instances.code_fn hbagd g1 hc1
  have hon := m.on.code_fn m.on.ht g2 hc2
  have haf := m.after.code_fn m.after.ht g3 hc3
  -- The encoding's parts.
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨de, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dn, nn⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dopt, nopt⟩, h3', henc⟩ := bind_ok.1 henc
  obtain ⟨rcd, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨evc, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨bag, c0⟩, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨bagT, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨db, nb, dtb⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨init, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨dflt, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨firsts, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨slots, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨_, h13, henc⟩ := bind_ok.1 henc
  obtain ⟨kd, h14, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hc0, hcs⟩ := (holds_andT _ _).1 hc
  have hnb : nb ≤ n := by unfold need' at h13; split at h13 <;> simp_all
  obtain ⟨nde, hde⟩ := tupleD_ok h2
  have hrcd : Smt.Rel M L r (Ty.up _ m.records_data recs) rcd := (rel_ofTerm (need_ok.1 h4) _).2 hrec
  have hevc : Smt.Rel M L e (Ty.up _ m.event_data ev) evc := (rel_ofTerm (need_ok.1 h5) _).2 hevT
  -- The bag `instances` returns.
  have hargs : (Ty.tuple [r]).isData = true := by simp [Ty.isData, Ty.isDatas, m.records_data]
  have hbagT : (Ty.bag m.key).isData = true := by simp [Ty.isData, hkd]
  have hbag : Smt.Rel M L (.bag m.key) (Ty.up _ hbagT (m.instances.fn (recs, ()))) bag := by
    have hrels : Smt.Rels M L [r] (Ty.up (.tuple [r]) hargs (recs, ())) (rcd, ()) := by
      show Smt.Rel M L _ (Ty.up (.tuple [r]) hargs (recs, ())).1 rcd ∧ True
      erw [Ty.up_tuple _ _ _ m.records_data rfl]; exact ⟨hrcd, trivial⟩
    have := hi _ _ hrels bag c0 h6 hc0
    erw [Ty.up_fn _ _ _ hargs hbagT] at this
    exact this
  have hbag' : Smt.Rel M L (.bag m.key) (Ty.up _ hbagT (m.instances.fn (recs, ()))) bagT :=
    (rel_term (need_ok.1 h7) _).1 hbag
  obtain ⟨svB, ysB, hSB, hlB, hwB, hpB, hyB⟩ := bag_view hbag' h8
  -- The old table.
  have htbl' : Smt.Rel M L (.table m.key (instEntry m.state)) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS, -, hw, hp, hh⟩ := table_view htbl' h1
  -- The new slots.
  obtain ⟨svN, svX, E, hN, hlN, hwN, hE, hhN, hX, hhX⟩ := assemble (T := T) m hpl _ hon haf recs tnow ev hrec hnow hevc
    tbl hS hw hp hh hde (need_ok.1 h3) (need_ok.1 h9) dflt hfx (need_ok.1 h3') _ svB ysB [] [] [] hSB hwB hyB trivial (by simp) trivial h11
    (mapM_ok _ _ _ h12) (fun o ho => (holds_allT _).1 hcs o.2 (List.mem_map.2 ⟨o, ho, rfl⟩))
  simp only [List.nil_append, List.map_nil] at hE
  rw [show dedupBy (Ty.semWith Dsl.base m.key).2 [] = [] from rfl, List.nil_append] at hE
  -- The step's instances.
  let keys := Ty.sortBy T m.key (dedupBy (Ty.semWith Dsl.base m.key).2 (m.instances.fn (recs, ())))
  let O := keys.map fun k => (Step.reactKey m (instancesOf T m tbl) recs tnow ev k).1
  have hO : (Step.machineStep T recs tnow ev ⟨m, instancesOf T m tbl⟩).1.2 = O := by
    simp [Step.machineStep, O, keys, List.map_map]
  have hentries : instEntries m O = keys.map fun k => (k, entryOf (Step.reactKey m (instancesOf T m tbl) recs tnow ev k).1) := by
    simp only [instEntries, O, List.map_map]
    exact List.map_congr_left fun k _ => by simp [Function.comp_apply, reactKey_key m hpl, entryOf]
  have hnd : keys.Nodup := by
    have : (dedupBy (Ty.semWith Dsl.base m.key).2 (m.instances.fn (recs, ()))).Nodup :=
      (dedupBy_pairwise (Ty.semWith Dsl.base m.key).2 _).imp fun {a _} hab heq => by
        subst heq; rw [(Ty.beq_plain _ hpl a a).2 rfl] at hab; cases hab
    exact (List.mergeSort_perm _ _).nodup_iff.2 this
  have hU : KeysUnique (Ty.semWith Dsl.base m.key).2 (instEntries m O) := by
    rw [hentries]
    unfold KeysUnique
    rw [List.pairwise_map]
    exact hnd.imp fun {a b} hab => ⟨by
      cases h : (Ty.semWith Dsl.base m.key).2 a b
      · rfl
      · exact absurd ((Ty.beq_plain _ hpl _ _).1 h) hab, by
      cases h : (Ty.semWith Dsl.base m.key).2 b a
      · rfl
      · exact absurd ((Ty.beq_plain _ hpl _ _).1 h).symm hab⟩
  have hsorted : O.Pairwise fun a b => keyLE T m a b = true := by
    have trans : ∀ a b c : m.key.den0, (Ty.cmp T m.key a b).isLE = true → (Ty.cmp T m.key b c).isLE = true →
        (Ty.cmp T m.key a c).isLE = true := fun _ _ _ h1 h2 => Std.TransCmp.isLE_trans (cmp := Ty.cmp T m.key) h1 h2
    have total : ∀ a b : m.key.den0, ((Ty.cmp T m.key a b).isLE || (Ty.cmp T m.key b a).isLE) = true := by
      intro a b
      rw [Std.OrientedCmp.eq_swap (cmp := Ty.cmp T m.key) (a := a) (b := b)]
      cases Ty.cmp T m.key b a <;> rfl
    have := List.pairwise_mergeSort trans total (dedupBy (Ty.semWith Dsl.base m.key).2 (m.instances.fn (recs, ())))
    simp only [O, List.pairwise_map, keyLE, reactKey_key m hpl]
    exact this
  have hb : (ysB.map (Ty.down _ hkd)).Perm (m.instances.fn (recs, ())) := by
    have := hpB.map (Ty.down _ hkd)
    rw [Ty.up_bag _ hbagT hkd] at this
    erw [map_down_up m.key hkd] at this
    exact this
  have hEp : E.Perm keys := by
    rw [← hE]
    exact (dedupBy_perm (Ty.beq_plain _ hpl) hb).trans
      (List.mergeSort_perm _ (fun a b => (Ty.cmp T m.key a b).isLE)).symm
  refine ⟨⟨m.tableOf O hU, ?_, by rw [hO]; exact instancesOf_entries T m O ⟨hsorted, hU⟩⟩, svX, E,
    by simpa [List.map_map, Function.comp_def] using hX, hhX, hEp⟩
  -- The new table term.
  obtain ⟨hf1, m1, hft1⟩ := collD_ok h1
  have hpad := slotsDen_replicate (M := M) false [kd, dflt] rfl (n - nb)
  have hlS : (slotsOf db dtb nb 1 bagT).length = nb := by simp [slotsOf]
  refine ⟨d, n, dt, m1, svN ++ List.replicate (n - nb) (false, Term.denotes M [kd, dflt]), hf1, hft1, ?_,
    slotsTerm_den d dt (slotsDen_append hN hpad), ?_, E.map (entryUp m (instancesOf T m tbl) recs tnow ev), ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, hlN, hlS]; omega
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hwN p hp
    · obtain ⟨-, rfl⟩ := List.mem_replicate.1 hp; rfl
  · -- The new entries are the step's, in another order.
    have hup : (Ty.up _ m.table_data (m.tableOf O hU)).1 =
        (instEntries m O).map fun p => (Ty.up _ hkd p.1, Ty.up _ m.entry_data p.2) :=
      Ty.up_table m.key (instEntry m.state) m.table_data hkd m.entry_data (m.tableOf O hU)
    rw [hup, hentries, List.map_map]
    exact hEp.map _
  · have hocc : occupied (svN ++ List.replicate (n - nb) (false, Term.denotes M [kd, dflt])) = occupied svN := by
      simp [occupied, List.filterMap_append]
    unfold Holds2; rw [hocc]; exact hhN

end

end Tazuna.Smt
