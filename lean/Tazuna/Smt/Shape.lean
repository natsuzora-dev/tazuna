import Tazuna.Smt.StepNoGap

/-! The shape of each machine's instances that a step question assumes: an instance for exactly the keys `instances`
gives at the records. Every state a run reaches has it (`Step.KeysOk`), so assuming it rules out no step of a run,
and without it a question could start from a state whose records name a key with no instance. The term compares the
instance table's slots with the bag's slots in both directions, as `encodeReact` looks a key up. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) {r e : Ty}

/-- Whether some occupied slot of the bag slots `SB` holds an item equal to `kc`: none of the comparisons fails to
hold, as `prev_eqs` reads them. -/
def bagHasT (m : MachineV r e) (SB : List (Slot 1)) (kc : Code m.key) : Except Refusal Term := do
  let eqs ← SB.mapM fun (f', xs') => do
    pure (Term.and f' (← eqCode L m.key (← Code.ofDataE m.key xs'[0]) kc))
  pure (.not (allT (eqs.map .not)))

/-- An instance table slot is empty or its key is in the bag. -/
def inBagAt (m : MachineV r e) (SB : List (Slot 1)) (sl : InstSlot) : Except Refusal Term := do
  pure (.or (.not sl.flag) (← bagHasT L m SB (← Code.ofDataE m.key sl.key)))

/-- A bag slot is empty or its item is the key of an occupied instance table slot. -/
def inTableAt (m : MachineV r e) (So : List InstSlot) (sl : Slot 1) : Except Refusal Term := do
  let hits ← So.mapM (hitAt L m (← Code.ofDataE m.key sl.2[0]))
  pure (.or (.not sl.1) (anyT (hits.map fun (f, h, _) => .and f h)))

/-- Whether the instance table `tbl` holds an instance for exactly the keys `instances` gives at `records`. Where the
`instances` code's condition fails the term is true: it claims nothing there. -/
def shapeT (m : MachineV r e) (tbl records : Term) : Except Refusal Term := do
  let (ic, c1) ← m.instances.code L
  let rcd ← Code.ofDataE r records
  let (bag, c0) ← ic (rcd, ())
  let bagT ← Code.dataTermE _ bag
  let (db, nb, dtb) ← collD L (.bag m.key) [m.key]
  let SB := slotsOf db dtb nb 1 bagT
  let (d, n, dt) ← collD L m.table [m.key, m.state]
  let So := instSlotsOf d dt n tbl
  let inBag ← So.mapM (inBagAt L m SB)
  let inTable ← SB.mapM (inTableAt L m So)
  pure (.ite (andT c1 c0) (allT (inBag ++ inTable)) tt)

/-- The shape term of every machine's instance table. -/
def shapesT : (ms : List (MachineV r e)) → PerMachine (fun _ => Term) ms → Term → Except Refusal Term
  | [], .nil, _ => pure tt
  | m :: ms, .cons x xs, records => do pure (andT (← shapeT L m x records) (← shapesT ms xs records))

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {r e : Ty}

theorem deq_iff (m : MachineV r e) (hpl : m.key.plain = true) (a b : m.key.den) :
    Ty.deq m.key a b = true ↔ a = b := by
  rw [deq_down m, Ty.beq_plain _ hpl]
  exact ⟨fun h => by rw [← Ty.up_down _ m.key_data a, h, Ty.up_down], fun h => h ▸ rfl⟩

/-- On a key type with the canonical order and `==` as equality, keys equal as Erlang terms are equal. -/
theorem keys_of_erls (m : MachineV r e) (hor : m.key.orderable = true) (ho : m.key.ordered T = true)
    {l : List (Step.Instance m)} {ks : List m.key.den0}
    (h : l.map (fun i => Ty.erl T m.key i.key) = ks.map (Ty.erl T m.key)) : l.map (·.key) = ks := by
  have hinj : Function.Injective (Ty.erl T m.key) := fun a b hab =>
    (Ty.beq_plain _ (Ty.plain_of_orderable _ hor) a b).1 ((Ty.erl_iff T m.key ho a b).2 hab)
  induction l generalizing ks with
  | nil => cases ks <;> simp_all
  | cons i l ih =>
    cases ks with
    | nil => simp at h
    | cons k ks =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨hinj h.1, ih h.2⟩

theorem holds_or_unflagged {f b : Term} (h : f.denote M = .bool false) : Holds M (.or (.not f) b) := by
  simp [Holds, Term.denote, h, Val.toBool]

theorem holds_or_of {a b : Term} (h : (b.denote M).toBool = true) : Holds M (.or a b) := by
  show ((a.denote M).toBool || (b.denote M).toBool) = true
  rw [h, Bool.or_true]

/-- Every table slot's term holds where every entry's key is in the bag. -/
theorem inBag_holds (m : MachineV r e) {SB : List (Slot 1)} {svB : List (Bool × List Val)} {ysB : List m.key.den}
    (hSB : SlotsDen M SB svB) (hyB : Holds2 (EBag L m.key) ysB svB) :
    (So : List InstSlot) → (sv : List (Bool × List Val)) → (ys : List (m.key.den × m.state.den)) →
    SlotsDen M (So.map InstSlot.slot) sv → Holds2 (ETab L m.key m.state) ys sv →
    (∀ y ∈ ys, ysB.any (fun b => Ty.deq m.key b y.1) = true) → {ts : List Term} →
    So.mapM (inBagAt L m SB) = .ok ts → ∀ t ∈ ts, Holds M t
  | [], [], ys, _, _, _, ts, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | ⟨g, tk, te⟩ :: So, (b, vs) :: sv, ys, ⟨hg, hxs, hS⟩, hy, hall, ts, h => by
    rw [List.mapM_cons] at h
    obtain ⟨t, h1, h⟩ := bind_ok.1 h
    obtain ⟨ts', h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    unfold inBagAt at h1
    obtain ⟨kc, hk, h1⟩ := bind_ok.1 h1
    obtain ⟨q, hq, h1⟩ := bind_ok.1 h1
    cases pure_ok.1 h1
    unfold bagHasT at hq
    obtain ⟨eqs, he, hq⟩ := bind_ok.1 hq
    cases pure_ok.1 hq
    cases b with
    | false =>
      intro t' ht'
      rcases List.mem_cons.1 ht' with rfl | ht'
      · exact holds_or_unflagged hg
      · exact inBag_holds m hSB hyB So sv ys hS (by simpa [Holds2, occupied] using hy) hall h2 t' ht'
    | true =>
      match ys, hy with
      | y :: ys, ⟨⟨zk, zv, hz, hyk, _⟩, hys⟩ =>
        intro t' ht'
        rcases List.mem_cons.1 ht' with rfl | ht'
        · rw [hz] at hxs
          simp only [Term.denotes, List.cons.injEq, and_true] at hxs
          have hkt : Smt.Rel M L m.key y.1 kc := (rel_ofTerm (need_ok.1 hk) _).2 (hxs.1 ▸ hyk)
          have hp := prev_eqs m hkt SB svB ysB hSB hyB he
          have ha := hall y (List.mem_cons_self ..)
          refine holds_or_of ?_
          simp only [Term.denote, hp, Val.toBool, ha, Bool.not_not]
        · exact inBag_holds m hSB hyB So sv ys hS hys (fun y' hy' => hall y' (List.mem_cons_of_mem _ hy')) h2 t' ht'
  | [], _ :: _, _, h, _, _, _, _ | _ :: _, [], _, h, _, _, _, _ => h.elim

/-- Every bag slot's term holds where every item is a key of the table. -/
theorem inTable_holds (m : MachineV r e) {So : List InstSlot} {sv : List (Bool × List Val)}
    {ys : List (m.key.den × m.state.den)} (hS : SlotsDen M (So.map InstSlot.slot) sv)
    (hh : Holds2 (ETab L m.key m.state) ys sv) :
    (SB : List (Slot 1)) → (svB : List (Bool × List Val)) → (ysB : List m.key.den) → SlotsDen M SB svB →
    Holds2 (EBag L m.key) ysB svB → (∀ b ∈ ysB, ys.any (fun y => Ty.deq m.key y.1 b) = true) → {ts : List Term} →
    SB.mapM (inTableAt L m So) = .ok ts → ∀ t ∈ ts, Holds M t
  | [], [], ysB, _, _, _, ts, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | (f, xs) :: SB, (b, vs) :: svB, ysB, ⟨hf, hxs, hSB⟩, hy, hall, ts, h => by
    rw [List.mapM_cons] at h
    obtain ⟨t, h1, h⟩ := bind_ok.1 h
    obtain ⟨ts', h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    unfold inTableAt at h1
    obtain ⟨kc, hk, h1⟩ := bind_ok.1 h1
    obtain ⟨hits, hhits, h1⟩ := bind_ok.1 h1
    cases pure_ok.1 h1
    cases b with
    | false =>
      intro t' ht'
      rcases List.mem_cons.1 ht' with rfl | ht'
      · exact holds_or_unflagged hf
      · exact inTable_holds m hS hh SB svB ysB hSB (by simpa [Holds2, occupied] using hy) hall h2 t' ht'
    | true =>
      match ysB, hy with
      | y :: ysB, ⟨⟨z, hz, hyz⟩, hys⟩ =>
        intro t' ht'
        rcases List.mem_cons.1 ht' with rfl | ht'
        · obtain ⟨t0, rfl⟩ := xs.one
          rw [hz] at hxs
          simp only [Term.denotes, List.cons.injEq, and_true] at hxs
          simp only [SlotItems.getElem_mk, List.getElem_cons_zero] at hk
          have hkt : Smt.Rel M L m.key y kc := (rel_ofTerm (need_ok.1 hk) _).2 (hxs ▸ hyz)
          have hl := (lookup_slots m hkt tt So sv hits ys hS (mapM_ok _ _ _ hhits) hh).1
          have ha := hall y (List.mem_cons_self ..)
          exact holds_or_of ((congrArg Val.toBool hl).trans (by simpa [Val.toBool] using ha))
        · exact inTable_holds m hS hh SB svB ysB hSB hys (fun y' hy' => hall y' (List.mem_cons_of_mem _ hy')) h2 t' ht'
  | [], _ :: _, _, h, _, _, _, _ | _ :: _, [], _, h, _, _, _, _ => h.elim

/-- A machine's shape term holds where the instances the table holds have the keys `instances` gives at the records. -/
theorem shape_holds (m : MachineV r e) (hor : m.key.orderable = true) (recs : r.den0) {records : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (tbl : m.table.den0) {x : Term}
    (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    (hk : (instancesOf T m tbl).map (·.key) = m.keysAt T recs) {c : Term} (henc : shapeT L m x records = .ok c) :
    Holds M c := by
  have hpl := Ty.plain_of_orderable _ hor
  have hkd := m.key_data
  obtain ⟨⟨ic, c1⟩, g1, henc⟩ := bind_ok.1 henc
  obtain ⟨rcd, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨bag, c0⟩, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨bagT, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨db, nb, dtb⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨inBag, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨inTable, h10, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  refine holds_ite_hit.2 fun hc => ?_
  obtain ⟨hc1, hc0⟩ := (holds_andT _ _).1 hc
  have hbagd : (Ty.fn [r] (.bag m.key)).isData = true := m.instances.ht
  have hi := m.instances.code_fn hbagd g1 hc1
  have hrcd : Smt.Rel M L r (Ty.up _ m.records_data recs) rcd := (rel_ofTerm (need_ok.1 h4) _).2 hrec
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
  obtain ⟨svB, ysB, hSB, -, -, hpB, hyB⟩ := bag_view hbag' h8
  have htbl' : Smt.Rel M L (.table m.key m.state) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS, -, -, hp, hh⟩ := table_view htbl' h1
  rw [← instSlotsOf_slot] at hS
  have hb : (ysB.map (Ty.down _ hkd)).Perm (m.instances.fn (recs, ())) := by
    have := hpB.map (Ty.down _ hkd)
    rw [Ty.up_bag _ hbagT hkd] at this
    erw [map_down_up m.key hkd] at this
    exact this
  have hkeys : ∀ k, k ∈ (ys.map (instOfD m)).map (·.key) ↔ k ∈ ysB.map (Ty.down _ hkd) := fun k => by
    rw [((instancesOf_perm (T := T) m tbl hp).map (fun i : Step.Instance m => i.key)).mem_iff, hk, MachineV.keysAt, Ty.sortBy,
      (List.mergeSort_perm _ _).mem_iff, hb.mem_iff]
    exact mem_dedupBy (Ty.beq_plain _ hpl) _ k
  rw [holds_allT]
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · refine inBag_holds m hSB hyB _ sv ys hS hh (fun y hy => ?_) h9 t ht
    have hin : Ty.down _ hkd y.1 ∈ ysB.map (Ty.down _ hkd) :=
      (hkeys _).1 (List.mem_map.2 ⟨instOfD m y, List.mem_map_of_mem hy, rfl⟩)
    obtain ⟨b, hbm, hbe⟩ := List.mem_map.1 hin
    refine List.any_eq_true.2 ⟨b, hbm, (deq_iff m hpl _ _).2 ?_⟩
    rw [← Ty.up_down _ hkd b, hbe, Ty.up_down]
  · refine inTable_holds m hS hh _ svB ysB hSB hyB (fun b hbm => ?_) h10 t ht
    obtain ⟨i, hi, hik⟩ := List.mem_map.1 ((hkeys _).2 (List.mem_map_of_mem hbm))
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hi
    refine List.any_eq_true.2 ⟨y, hy, (deq_iff m hpl _ _).2 ?_⟩
    rw [← Ty.up_down _ hkd y.1, ← Ty.up_down _ hkd b]
    exact congrArg _ hik

/-- The shape term holds at a state whose instances have the keys `instances` gives at its records, as every state a
run reaches (`Step.KeysOk`). -/
theorem shapes_holds {v : ServiceV} (recs : v.records.den0) {records : Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data recs) (records.denote M)) :
    (ms : List (MachineV v.records v.event)) → (xs : PerMachine (fun _ => Term) ms) → (sms : Step.Machines ms) →
    MachinesRel M L T ms xs sms → (∀ m ∈ ms, m.key.orderable = true ∧ m.key.ordered T = true) →
    (∀ sm ∈ sms.toSigma, sm.2.map (fun i => Ty.erl T sm.1.key i.key) = (sm.1.keysAt T recs).map (Ty.erl T sm.1.key)) →
    {c : Term} → shapesT L ms xs records = .ok c → Holds M c
  | [], .nil, .nil, _, _, _, c, h => by
    simp only [shapesT, pure, Except.pure, Except.ok.injEq] at h; subst h; exact holds_tt
  | m :: ms, .cons x xs, .cons insts sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hk, hsh, c, h => by
    obtain ⟨c1, h1, h⟩ := bind_ok.1 h
    obtain ⟨c2, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    subst hsm
    have hm := hk m (List.mem_cons_self ..)
    rw [holds_andT]
    refine ⟨shape_holds m hm.1 recs hrec tbl htbl
      (keys_of_erls m hm.1 hm.2 (hsh ⟨m, instancesOf T m tbl⟩ (by simp [PerMachine.toSigma_cons]))) h1,
      shapes_holds recs hrec ms xs sms hrest (fun m' h' => hk m' (List.mem_cons_of_mem _ h'))
        (fun sm h' => hsh sm (by simp [PerMachine.toSigma_cons, h'])) h2⟩

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {r e : Ty}

theorem shapeT_sound (hL : SortedLayout L) {m : MachineV r e} (h : MachineGot L m) (hc : MachineCodes L P ds H m)
    (tbl records : Term) : Sound (fun _ => True) (shapeT L m tbl records) := by
  have hkey := avail_of_got h.key
  unfold shapeT
  refine sound_bind hc.instances fun ⟨ic, c1⟩ hin => ?_
  refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ h.records) fun rcd hrcd => ?_
  refine sound_bind (apply_sound hin ⟨hrcd, trivial⟩ (avail_of_got h.bag)) fun _ _ => ?_
  refine sound_bind (dataTermE_sound _) fun _ _ => ?_
  refine sound_bind (collD_sound hL (avail_of_got h.bag) fun g => ⟨g.2.2, g.2.1⟩) fun _ _ => ?_
  refine sound_bind (collD_table_sound hL h) fun _ _ => ?_
  refine sound_bind (sound_mapM _ fun sl _ => ?_) fun _ _ => sound_bind (sound_mapM _ fun sl _ => ?_) fun _ _ => trivial
  · simp only [inBagAt, bagHasT]
    refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hkey) fun kc _ => ?_
    refine sound_bind (p := fun _ => True) (sound_bind (sound_mapM _ fun ⟨f', xs'⟩ _ => ?_) fun _ _ => trivial)
      fun _ _ => trivial
    exact sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hkey) fun c hc' =>
      sound_bind (eqCode_sound hL c kc hc') fun _ _ => trivial
  · simp only [inTableAt]
    refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hkey) fun kc _ => ?_
    refine sound_bind (sound_mapM _ fun ⟨g, key, entry⟩ _ => ?_) fun _ _ => trivial
    simp only [hitAt]
    exact sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hkey) fun c hc' =>
      sound_bind (eqCode_sound hL c kc hc') fun _ _ => trivial

theorem shapesT_sound (hL : SortedLayout L) :
    (ms : List (MachineV r e)) → (∀ m ∈ ms, MachineGot L m ∧ MachineCodes L P ds H m) →
    (xs : PerMachine (fun _ => Term) ms) → (records : Term) → Sound (fun _ => True) (shapesT L ms xs records)
  | [], _, .nil, _ => trivial
  | m :: ms, h, .cons x xs, records => by
    simp only [shapesT]
    have hm := h m (List.mem_cons_self ..)
    exact sound_bind (shapeT_sound hL hm.1 hm.2 x records) fun _ _ =>
      sound_bind (shapesT_sound hL ms (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) xs records) fun _ _ => trivial

end

end Tazuna.Smt
