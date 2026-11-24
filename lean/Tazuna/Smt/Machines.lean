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

theorem forall2_length {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => congrArg (· + 1) (forall2_length h)

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
