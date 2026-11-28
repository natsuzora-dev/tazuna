import Tazuna.Explore.Search
import Tazuna.Explore.KeyRead
import Tazuna.Semantics.StepRen
import Tazuna.Smt.PendingWrite

/-! Nodes with equal keys are related by a renaming `step_ren` takes (`key_link`): the renaming that relates the
counters, and the wire ids, each key renames alike, with instants moved from one state's time to the other's. -/

namespace Tazuna.Explore

open Tazuna.Ir Tazuna.Ir.Step

variable {v : ServiceV}

/-- Waiting triggers related by `R`, item by item, the times moved by its shift. -/
def WatchRel (R : PBij) : Option (List (List (v.event.den0 × Int))) → Option (List (List (v.event.den0 × Int))) →
    Prop :=
  Option.Rel (Forall2 (Forall2 fun a b => Ty.rel0 R v.event a.1 b.1 ∧ R.point .ms a.2 b.2))

/-- Nodes related by `R`: their states, their shown ids and their waiting triggers. -/
structure NodeRen (R : Ren) (a b : Node v) : Prop where
  state : StateRen R a.state b.state
  shown : Forall2 (IdV.Rel R.ctr) a.shown b.shown
  watch : WatchRel R.ctr a.watch b.watch

/-- Nodes related by a renaming that keeps the counters' order: no step tells them apart (`step_ren`). -/
def Link (a b : Node v) : Prop := ∃ R : Ren, R.ctr.Mono ∧ NodeRen R a b

/-- What a pending request's key reads back from: the types of its values are comparable, and its kept functions
are records of the sites `P` capturing values of comparable types. -/
structure PendingKeyable (P : List AnySite) {e : Ty} (p : Pending e) : Prop where
  sender : ∀ n t k, p.sender = .machine n ⟨t, k⟩ → t.comparable = true
  input : p.request.input.comparable = true
  ensures : ∀ f ∈ p.request.ensures, f.asSite ∈ P ∧ (Ty.tuple f.Γ).comparable = true
  onAnswer : p.request.onAnswer.asSite ∈ P ∧ (Ty.tuple p.request.onAnswer.Γ).comparable = true

theorem embeddables_of_mem : {vs : List (List Ty)} → Ty.embeddabless vs = true → ∀ fs ∈ vs, Ty.embeddables fs = true
  | _ :: vs, h, fs, hm => by
    simp only [Ty.embeddabless, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h.1
    · exact embeddables_of_mem h.2 fs hm

theorem senderShape_comparable {n : String} {t : Ty} {k : t.den0} : {ks : List Ty} → (sd : SenderShape ks) →
    (y : (Ty.tuple ks).den0) → (Ty.tuple ks).comparable = true → sd.sender y = .machine n ⟨t, k⟩ →
    t.comparable = true
  | _, .machine _ key, (_, ()), hc, h => by
    simp only [SenderShape.sender, Sender.machine.injEq] at h
    obtain ⟨-, h⟩ := h
    cases h
    simpa [Ty.comparable, Ty.comparables] using hc
  | _, .reaction _, (), _, h => by simp [SenderShape.sender] at h

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
theorem ensuresFn_comparable {t : Ty} : (ens : Option ((Γ : List Ty) × Site Γ t)) →
    (env : (Ty.tuple ((ens.map (·.1)).getD [])).den0) → (Ty.tuple ((ens.map (·.1)).getD [])).comparable = true →
    ∀ f ∈ ensuresFn ens env, (Ty.tuple f.Γ).comparable = true
  | none, _, _, f, hf => by simp [ensuresFn] at hf
  | some ⟨_, _⟩, _, hc, f, hf => by
    simp only [ensuresFn, Option.mem_def, Option.some.injEq] at hf
    subst hf
    exact hc

/-- The pending requests of a checked service's reachable states read back from their keys. -/
theorem keyable {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} (chk : Smt.Checked P E T v)
    {s : State v} (hs : Inv P s) : ∀ p ∈ s.pending, PendingKeyable P p := by
  intro p hp
  have hreach := hs.reach p hp
  have hty := chk.stateTys
  simp only [ServiceV.stateTys, Bool.and_eq_true] at hty
  have hemb : Ty.embeddabless ((shapes v).map PendingShape.fields) = true := by
    have := hty.1.1.2.1
    simpa [pendingEntry, Ty.embeddable] using this
  obtain ⟨x, hx⟩ := hs.shaped p hp
  obtain ⟨sh, hsh, fx, e⟩ := Smt.pendingOf_mem (shapes v) p.id x
  rw [hx] at e
  rw [e] at hreach ⊢
  obtain ⟨hon, hens, -, -⟩ := hreach
  have hc := Smt.comparables_of_embeddables _ (embeddables_of_mem hemb _ (List.mem_map_of_mem hsh))
  simp only [PendingShape.fields, RequestShape.fields, Ty.comparables, Bool.and_eq_true] at hc
  obtain ⟨hks, hin, hens', hans, -⟩ := hc
  exact ⟨fun n t k hk => senderShape_comparable sh.sender _ hks hk, hin,
    fun f hf => ⟨hens f hf, ensuresFn_comparable sh.ensures _ hens' f hf⟩, ⟨hon, hans⟩⟩

section Read
variable {σ σ' ω ω' : Nat → Nat} {δ δ' : Int} {A B W W' : Nat → Prop} {R : Ren}

theorem senderKey_read (hR : ∀ c c', A c → B c' → σ c = σ' c' → R.ctr.rel c c')
    (hsh : R.ctr.shift = some (δ - δ')) {a b : Sender}
    (ha : ∀ n t k, a = .machine n ⟨t, k⟩ → t.comparable = true) (hx : ∀ c ∈ senderCtrs a, A c)
    (hy : ∀ c ∈ senderCtrs b, B c) (h : senderKey σ δ a = senderKey σ' δ' b) : Sender.Rel R.ctr a b := by
  match a, b, h with
  | .machine n ⟨t, k⟩, .machine n' ⟨t', k'⟩, h =>
    simp only [senderKey, Erl.tuple.injEq, List.cons.injEq, Erl.bin.injEq, and_true] at h
    obtain ⟨rfl, ht, hk⟩ := h
    obtain rfl := tyKey_inj _ _ ht
    exact .machine n (.mk (keyBy_read hR hsh t (ha n t k rfl) k k' hx hy hk))
  | .reaction n, .reaction n', h =>
    simp only [senderKey, Erl.bin.injEq] at h
    subst h
    exact .reaction n
  | .machine .., .reaction _, h | .reaction _, .machine .., h => simp [senderKey] at h

theorem pendingKey_read {P : List AnySite} (hP : SitesUnique P) (hR : ∀ c c', A c → B c' → σ c = σ' c' → R.ctr.rel c c')
    (hW : ∀ w w', W w → W' w' → ω w = ω' w' → R.wire.rel w w') (hsh : R.ctr.shift = some (δ - δ')) {e : Ty}
    {p q : Pending e} (hp : PendingKeyable P p) (hq : PendingKeyable P q) (hx : ∀ c ∈ pendingCtrs p, A c)
    (hy : ∀ c ∈ pendingCtrs q, B c) (hpw : W p.id) (hqw : W' q.id)
    (h : pendingKey σ ω δ p = pendingKey σ' ω' δ' q) : Pending.Rel R p q := by
  obtain ⟨id, snd, ext, name, input, output, rej, value, ens, onA⟩ := p
  obtain ⟨id', snd', ext', name', input', output', rej', value', ens', onA'⟩ := q
  simp only [pendingKey, Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.natCast_inj, Erl.bin.injEq,
    Erl.list.injEq, and_true] at h
  obtain ⟨hid, hsnd, rfl, rfl, ⟨hin, hout, hrej⟩, hval, hens, hon⟩ := h
  obtain rfl := tyKey_inj _ _ hin
  obtain rfl := tyKey_inj _ _ hout
  have hopt : ∀ a b : Option Ty, a.toList.map tyKey = b.toList.map tyKey → a = b := by
    intro a b h
    cases a <;> cases b <;> simp only [Option.toList_none, Option.toList_some, List.map_nil, List.map_cons,
      List.cons.injEq, and_true, reduceCtorEq] at h ⊢
    · rw [tyKey_inj _ _ h]
  obtain rfl := hopt rej rej' hrej
  simp only [pendingCtrs, List.mem_append, List.mem_flatMap] at hx hy
  refine ⟨hW _ _ hpw hqw hid, senderKey_read hR hsh hp.sender (fun c h => hx c (.inl (.inl (.inl h))))
    (fun c h => hy c (.inl (.inl (.inl h)))) hsnd, rfl, .mk _ _ _ _ ?_ ?_ ?_⟩
  · exact keyBy_read hR hsh input hp.input value value' (fun c h => hx c (.inl (.inl (.inr h))))
      (fun c h => hy c (.inl (.inl (.inr h)))) hval
  · cases ens with
    | none => cases ens' with
      | none => exact .none
      | some _ => simp [funKey] at hens
    | some f => cases ens' with
      | none => simp [funKey] at hens
      | some g =>
        simp only [Option.map_some, Option.getD_some] at hens
        exact .some (funKey_read hP hR hsh (hp.ensures f rfl).1 (hq.ensures g rfl).1 (hp.ensures f rfl).2
          (fun c h => hx c (.inl (.inr ⟨f, by simp, h⟩))) (fun c h => hy c (.inl (.inr ⟨g, by simp, h⟩))) hens)
  · exact funKey_read hP hR hsh hp.onAnswer.1 hq.onAnswer.1 hp.onAnswer.2 (fun c h => hx c (.inr h))
      (fun c h => hy c (.inr h)) hon

theorem machines_read {r e : Ty} (hR : ∀ c c', A c → B c' → σ c = σ' c' → R.ctr.rel c c')
    (hsh : R.ctr.shift = some (δ - δ')) : {ms : List (MachineV r e)} →
    (∀ m ∈ ms, m.key.comparable = true ∧ m.state.comparable = true) → (xs ys : Machines ms) →
    (∀ x ∈ xs.toSigma, ∀ i ∈ x.2, ∀ c ∈ ctrsIn x.1.key i.key ++ ctrsIn x.1.state i.state, A c) →
    (∀ x ∈ ys.toSigma, ∀ i ∈ x.2, ∀ c ∈ ctrsIn x.1.key i.key ++ ctrsIn x.1.state i.state, B c) →
    (xs.toSigma.map fun ⟨m, insts⟩ =>
      Erl.list (insts.map fun (i : Instance m) => .tuple [keyBy σ δ m.key i.key, keyBy σ δ m.state i.state])) =
      (ys.toSigma.map fun ⟨m, insts⟩ =>
        Erl.list (insts.map fun (i : Instance m) => .tuple [keyBy σ' δ' m.key i.key, keyBy σ' δ' m.state i.state])) →
    Machines.Ren R.ctr xs ys
  | _, _, .nil, .nil, _, _, _ => trivial
  | m :: _, hms, .cons l rest, .cons l' rest', hx, hy, h => by
    simp only [PerMachine.toSigma_cons, List.map_cons, List.cons.injEq, Erl.list.injEq] at h
    have hm := hms m List.mem_cons_self
    refine ⟨forall2_of_map_eq2 h.1 fun i hi j hj e => ?_,
      machines_read hR hsh (fun m' h' => hms m' (List.mem_cons_of_mem _ h')) rest rest'
        (fun x hx' => hx x (List.mem_cons_of_mem _ hx')) (fun x hx' => hy x (List.mem_cons_of_mem _ hx')) h.2⟩
    simp only [Erl.tuple.injEq, List.cons.injEq, and_true] at e
    have hxi := hx ⟨m, l⟩ List.mem_cons_self i hi
    have hyj := hy ⟨m, l'⟩ List.mem_cons_self j hj
    exact ⟨keyBy_read hR hsh m.key hm.1 i.key j.key (fun c h => hxi c (List.mem_append_left _ h))
        (fun c h => hyj c (List.mem_append_left _ h)) e.1,
      keyBy_read hR hsh m.state hm.2 i.state j.state (fun c h => hxi c (List.mem_append_right _ h))
        (fun c h => hyj c (List.mem_append_right _ h)) e.2⟩

end Read

section Ctrs
variable {n : Node v} {c : Nat}

theorem ctrs_records (h : c ∈ ctrsIn v.records n.state.records) : c ∈ n.ctrs := by
  simp [Node.ctrs, stateCtrs, h]

theorem ctrs_inst {x : (m : MachineV v.records v.event) × List (Instance m)} (hx : x ∈ n.state.machines.toSigma)
    {i : Instance x.1} (hi : i ∈ x.2) (h : c ∈ ctrsIn x.1.key i.key ++ ctrsIn x.1.state i.state) : c ∈ n.ctrs := by
  simp only [Node.ctrs, stateCtrs, List.mem_append, List.mem_flatMap]
  exact .inl (.inl (.inl (.inr ⟨x, hx, i, hi, List.mem_append.1 h⟩)))

theorem ctrs_pending {p : Pending v.event} (hp : p ∈ n.state.pending) (h : c ∈ pendingCtrs p) : c ∈ n.ctrs := by
  simp only [Node.ctrs, stateCtrs, List.mem_append, List.mem_flatMap]
  exact .inl (.inl (.inr ⟨p, hp, h⟩))

theorem ctrs_shown {x : IdV} (hx : x ∈ n.shown) (h : c ∈ ctrsIn .id x) : c ∈ n.ctrs := by
  simp only [Node.ctrs, List.mem_append]
  exact .inr (List.mem_flatMap.2 ⟨x, hx, h⟩)

theorem ctrs_watch {ws : List (List (v.event.den0 × Int))} (hw : n.watch = some ws) {trs : List (v.event.den0 × Int)}
    (htrs : trs ∈ ws) {e : v.event.den0 × Int} (he : e ∈ trs) (h : c ∈ ctrsIn v.event e.1) : c ∈ n.ctrs := by
  simp only [Node.ctrs, hw, List.mem_append, List.mem_flatMap, Option.map_some, Option.toList_some,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  exact .inl (.inr ⟨trs, htrs, e, he, h⟩)

end Ctrs

theorem comparable_records {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl}
    (chk : Smt.Checked P E T v) : v.records.comparable = true ∧ v.event.comparable = true := by
  have hty := chk.stateTys
  simp only [ServiceV.stateTys, Bool.and_eq_true] at hty
  exact ⟨Smt.comparable_of_embeddable _ hty.1.1.1.1.1, Smt.comparable_of_embeddable _ hty.1.2.1⟩

theorem renameBelow_from {cs : Array Nat} {base : Nat} (k : Nat) : renameBelow cs base (base + k) = cs.size + k := by
  unfold renameBelow
  rw [ite_eq_right_iff.2 (fun h => absurd h (by omega))]
  omega

/-- Nodes of reachable states with equal keys are related by a renaming that keeps the counters' order: the renaming
relating the counters, and the wire ids, each key renames alike, with instants moved from one state's time to the
other's. -/
theorem key_link {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} (chk : Smt.Checked P E T v)
    (hv : v.Equivariant) {a b : Node v} (ha : Inv P a.state) (hb : Inv P b.state) (h : a.key = b.key) : Link a b := by
  have hca := belowOf_sorted a.ctrs a.state.fresh
  have hcb := belowOf_sorted b.ctrs b.state.fresh
  have hwa := belowOf_sorted (a.state.pending.map (·.id)) a.state.nextId
  have hwb := belowOf_sorted (b.state.pending.map (·.id)) b.state.nextId
  let R : Ren := ⟨keyRen a.ctrRen b.ctrRen (InRename (belowOf a.ctrs a.state.fresh) a.state.fresh)
      (InRename (belowOf b.ctrs b.state.fresh) b.state.fresh) (fun _ _ => renameBelow_compare hca)
      (fun _ _ => renameBelow_compare hcb) (some (-a.state.now - -b.state.now)),
    keyRen a.wireRen b.wireRen (InRename (belowOf (a.state.pending.map (·.id)) a.state.nextId) a.state.nextId)
      (InRename (belowOf (b.state.pending.map (·.id)) b.state.nextId) b.state.nextId)
      (fun _ _ => renameBelow_compare hwa) (fun _ _ => renameBelow_compare hwb) none⟩
  have hR : ∀ c c', InRename (belowOf a.ctrs a.state.fresh) a.state.fresh c →
      InRename (belowOf b.ctrs b.state.fresh) b.state.fresh c' → a.ctrRen c = b.ctrRen c' → R.ctr.rel c c' :=
    fun _ _ h1 h2 e => ⟨h1, h2, e⟩
  have hW : ∀ w w', InRename (belowOf (a.state.pending.map (·.id)) a.state.nextId) a.state.nextId w →
      InRename (belowOf (b.state.pending.map (·.id)) b.state.nextId) b.state.nextId w' → a.wireRen w = b.wireRen w' →
      R.wire.rel w w' :=
    fun _ _ h1 h2 e => ⟨h1, h2, e⟩
  have hsh : R.ctr.shift = some (-a.state.now - -b.state.now) := rfl
  have hA : ∀ c ∈ a.ctrs, InRename (belowOf a.ctrs a.state.fresh) a.state.fresh c := fun _ hc hlt => mem_belowOf hc hlt
  have hB : ∀ c ∈ b.ctrs, InRename (belowOf b.ctrs b.state.fresh) b.state.fresh c := fun _ hc hlt => mem_belowOf hc hlt
  have hcmp := comparable_records chk
  unfold Node.key at h
  simp only [Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, Int.natCast_inj, Erl.list.injEq, and_true] at h
  obtain ⟨hcs, hws, hrec, hmach, hpend, hshown, hwatch⟩ := h
  refine ⟨R, keyRen_mono (fun _ _ => renameBelow_compare hca) (fun _ _ => renameBelow_compare hcb) _, ⟨⟨?_, ?_, ?_, ?_, fun k => ?_, fun k => ?_⟩, ?_, ?_⟩⟩
  · exact keyBy_read hR hsh v.records hcmp.1 _ _ (fun c h => hA c (ctrs_records h))
      (fun c h => hB c (ctrs_records h)) hrec
  · exact machines_read hR hsh (fun m hm => ⟨hv.keys m hm, hv.states m hm⟩) _ _
      (fun x hx i hi c h => hA c (ctrs_inst hx hi h)) (fun x hx i hi c h => hB c (ctrs_inst hx hi h)) hmach
  · exact forall2_of_map_eq2 hpend fun p hp q hq e =>
      pendingKey_read chk.sites hR hW hsh (keyable chk ha p hp) (keyable chk hb q hq)
        (fun c h => hA c (ctrs_pending hp h)) (fun c h => hB c (ctrs_pending hq h))
        (fun hlt => mem_belowOf (List.mem_map_of_mem hp) hlt) (fun hlt => mem_belowOf (List.mem_map_of_mem hq) hlt) e
  · show R.ctr.point .ms a.state.now b.state.now
    simp only [PBij.point, hsh]
    omega
  · refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), ?_⟩
    show renameBelow _ _ _ = renameBelow _ _ _
    rw [renameBelow_from, renameBelow_from, hcs]
  · refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), ?_⟩
    show renameBelow _ _ _ = renameBelow _ _ _
    rw [renameBelow_from, renameBelow_from, hws]
  · exact forall2_of_map_eq2 hshown fun x hx y hy e =>
      keyBy_read hR hsh .id rfl x y (fun c h => hA c (ctrs_shown hx h)) (fun c h => hB c (ctrs_shown hy h)) e
  · revert hwatch
    cases hwa' : a.watch <;> cases hwb' : b.watch <;> intro hwatch
    · exact .none
    · simp at hwatch
    · simp at hwatch
    · rename_i ws ws'
      simp only [Erl.list.injEq] at hwatch
      refine .some (forall2_of_map_eq2 hwatch fun trs htrs trs' htrs' e => forall2_of_map_eq2 (Erl.list.inj e)
        fun x hx y hy e' => ?_)
      simp only [Erl.tuple.injEq, List.cons.injEq, Erl.int.injEq, and_true] at e'
      refine ⟨keyBy_read hR hsh v.event hcmp.2 _ _ (fun c h => hA c (ctrs_watch hwa' htrs hx h))
        (fun c h => hB c (ctrs_watch hwb' htrs' hy h)) e'.1, ?_⟩
      show R.ctr.point .ms x.2 y.2
      simp only [PBij.point, hsh]
      omega

end Tazuna.Explore
