import Tazuna.Smt.Verdict

/-! A counterexample line is honest: a model of a target question decodes to a state with what the question asserted
of it, the step invariant (`Step.Inv`) and every invariant holding, and the step `prove` recomputes in Lean from that
state and input is the one the question's terms say (`cti_sound`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {v : ServiceV}

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
theorem ensuresFn_mem {t : Ty} : (ens : Option ((Γ : List Ty) × Site Γ t)) → (env : (Ty.tuple ((ens.map (·.1)).getD [])).den0) →
    ∀ f ∈ ensuresFn ens env, ∃ s ∈ ens, f.asSite = ⟨s.1, t, s.2⟩
  | none, _, _, hf => by cases hf
  | some ⟨_, _⟩, _, _, hf => by cases hf; exact ⟨_, rfl, rfl⟩

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
theorem ensuresFn_isNone {t : Ty} : (ens : Option ((Γ : List Ty) × Site Γ t)) →
    (env : (Ty.tuple ((ens.map (·.1)).getD [])).den0) → (ensuresFn ens env).isNone = ens.isNone
  | none, _ | some _, _ => rfl

/-- A request of a service's shape keeps its functions within the program's sites. -/
theorem shape_reach {P : List AnySite} {E : List AnyEffectSite} (hv : v.Reach P E) {sh : PendingShape v.event}
    (h : sh ∈ shapes v) (id : Nat)
    (fx : Ty.dens sh.fields) : (EffectV.request (sh.pending id fx).request).Reach P := by
  have hin := shapes_inSites hv h
  have hd := sh.hfields
  simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at hd
  refine ⟨hin.1, fun f hf => ?_, hd.1, (shapes_rejection h).trans (ensuresFn_isNone _ _).symm⟩
  obtain ⟨s, hs, e⟩ := ensuresFn_mem _ _ f hf
  rw [e]
  exact hin.2 s hs

theorem pendingOf_reach {P : List AnySite} {E : List AnyEffectSite} (hv : v.Reach P E) : (shs : List (PendingShape v.event)) → (∀ sh ∈ shs, sh ∈ shapes v) →
    (id : Nat) → (x : Ty.alts (shs.map PendingShape.fields)) → (EffectV.request (pendingOf shs id x).request).Reach P
  | sh :: _, h, id, .inl fx => shape_reach hv (h sh (List.mem_cons_self ..)) id fx
  | _ :: shs, h, id, .inr y => pendingOf_reach hv shs (fun sh hs => h sh (List.mem_cons_of_mem _ hs)) id y

variable {M : Model} {L : Layout} {T : List TypeDecl}

/-- A decoded state whose wire ids are below the next one keeps the step invariant: its pending requests come from a
table, so their ids differ, and from the service's shapes, so they reach only the program's sites. -/
theorem decode_inv {P : List AnySite} {E : List AnyEffectSite} (hv : v.Reach P E) {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    (hbelow : ∀ p ∈ s.pending, p.id < s.nextId) : Step.Inv P s := by
  obtain ⟨tbl, -, htbl⟩ := (decode_state hS).pending
  refine ⟨hbelow, ?_, fun p hp => ?_, fun p hp => ?_⟩
  · have e : (pendingList (shapes v) tbl).map (·.id) = tbl.1.map (·.1) := by
      rw [pendingList, List.map_map]
      exact List.map_congr_left fun y _ => pendingOf_id _ y.1 y.2
    rw [← htbl, e]
    have hu : List.Pairwise (fun a b => (@BEq.beq Nat _ a.1 b.1) = false ∧ (@BEq.beq Nat _ b.1 a.1) = false) tbl.1 :=
      tbl.2
    refine List.pairwise_map.2 (hu.imp fun h e => ?_)
    have h1 : (@BEq.beq Nat _ _ _) = false := h.1
    exact Nat.ne_of_beq_eq_false h1 e
  · rw [← htbl] at hp
    obtain ⟨⟨id, x⟩, -, rfl⟩ := List.mem_map.1 hp
    exact pendingOf_reach hv _ (fun _ h => h) id x
  · rw [← htbl] at hp
    obtain ⟨⟨id, x⟩, -, rfl⟩ := List.mem_map.1 hp
    exact ⟨x, congrArg (fun n => pendingOf (shapes v) n x) (pendingOf_id (shapes v) id x)⟩

/-- A counterexample is honest: wherever a model satisfies a target question of an input kind and its values decode
to a state and an input, the state keeps the step invariant, every invariant holds there, and the step from it is the
one the question's terms say. So the state, step, outcome and broken rules `prove` recomputes in Lean from the decoded
values are the solver's counterexample. -/
theorem cti_sound {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v))
    (inp : SymInput v (shapes v) senv.nT) {gs : List Target} {qs : List (Question v (shapes v) senv.nT)}
    (hq : questions L T P v senv inp = .ok (gs, qs)) {q : Question v (shapes v) senv.nT} (hmem : q ∈ qs)
    {g : Target} (hg : q.target = some g) (hM : ∀ a ∈ q.script.asserts, Holds M a)
    {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    {hc : v.caller.isData = true} {x : Input v} (hx : inp.decode M L hc = some x) :
    Step.Inv P s ∧ Step.invariants s = [] ∧
      ∀ t, encodeStep L T P v senv (SymState.vars 0) inp = .ok t → t.out.Rel M L T (shapes v) s x (step T v s x) := by
  obtain ⟨t, ht, hq⟩ := bind_ok.1 hq
  obtain ⟨wf, -, hq⟩ := bind_ok.1 hq
  obtain ⟨below, hbelow, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨inv, ci0⟩, hinvc, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨rules, ci⟩, hrules, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨checks, ck⟩, hchecks, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, -, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  rcases List.mem_cons.1 hmem with rfl | hmem
  · cases hg
  obtain ⟨g', -, rfl⟩ := List.mem_map.1 hmem
  have hA := fun a (h : a ∈ [wf, below, t.out.case, andT t.codes (andT t.sites (andT ci0 (andT ci ck))),
    andT (allT (rules.map (·.2))) (allT (checks.toList.map instHoldT)), t.cond, t.out.breaks inp.command? g']) =>
    hM a (by simpa using h)
  have hbelowH := hA below (by simp)
  have hcaseH := hA t.out.case (by simp)
  have hside := hA (andT t.codes (andT t.sites (andT ci0 (andT ci ck)))) (by simp)
  have hheldH := hA (andT (allT (rules.map (·.2))) (allT (checks.toList.map instHoldT))) (by simp)
  have hcond := hA t.cond (by simp)
  simp only [holds_andT] at hside hheldH
  obtain ⟨hcodes, hsites, hci0, hci, hck⟩ := hside
  have hR := decode_state hS
  have hinv := decode_inv chk.reach hS ((pendingBelow_iff hR.pending hR.nextId hbelow).1 hbelowH)
  have hfd : (Ty.fn [v.records] Ty.rules).isData = true := by
    simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, v.records_data]
  have hb := invariants_rel v.invariants v.records_data hfd (v.invariants.code_fn hfd hinvc hci0) s.records hR.records
    hrules hci
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  have hbs := (instChecks_encode s.records s.now hR.records hR.now v.machines _ s.machines hR.machines hord hchecks).2 hck
  refine ⟨hinv, ?_, fun t' ht' => ?_⟩
  · show Step.broken (v.invariants.fn (s.records, ())) ++ instancesBroken s.records s.now s.machines = []
    rw [← hb, ← hbs, (holds_allT_rules _).1 hheldH.1, nil_of_instHold _ _ hheldH.2]
    rfl
  · rw [ht] at ht'
    cases ht'
    exact ((step_encode chk senv hS hinv hx ht).2 hcodes hsites hcaseH).2 hcond

end

end Tazuna.Smt
