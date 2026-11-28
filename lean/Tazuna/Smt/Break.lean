import Tazuna.Smt.Cube

/-! search's search for a run that breaks one of prove's targets that a fault falls under (an invariant, an `ensures`
rule, an own effect's acceptance, the cascade bound): steps from the initial state that fault nowhere, then one step
that faults by a fault the target covers. Its depths are cubes as `noModel_cubes` splits them, but the last step of a
cube is a break step (`breakOne`): an unrolled step whose assertion says the step breaks the target (`breakT`) in place
of saying it does not fault. Where the cubes cover a depth with no model, no such run of that many inputs exists
(`noModel_breaks`). A cube needs no question where the step question (`stepAsk`) whether a step breaks the target is
unsat for every kind of its last step's pick (`BreakCover.deadLast`): no state a run reaches has a step of that kind
that breaks the target. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- Whether some fault falls under both targets: the same kind of fault, and the same rule or own kind where both name
one. -/
def Target.meets : Target → Target → Bool
  | .invariant _ r, .invariant _ r' | .ensures _ r, .ensures _ r' => r.isNone || r'.isNone || r == r'
  | .cascade, .cascade => true
  | .effect c, .effect c' => c == c'
  | _, _ => false

theorem Target.meets_of_covers {g g' : Target} {f : Fault} (h : g.covers f = true) (h' : g'.covers f = true) :
    g'.meets g = true := by
  cases f <;> cases g <;> cases g' <;> simp only [Target.covers, Target.meets] at h h' ⊢ <;>
    (try split at h <;> split at h') <;> simp_all

theorem Target.covers_unmatched (g : Target) : g.covers .answerUnmatched = false := by
  cases g <;> simp [Target.covers]

/-- Whether a fault breaks the target, so explore and search look for a run that breaks it: an invariant, an `ensures` rule,
an own effect's acceptance, the cascade bound. A response's, a timer machine's and a pair's line is about deadlines and
orders, which no fault of one step shows. -/
def Target.byFault : Target → Bool
  | .invariant .. | .ensures .. | .cascade | .effect _ => true
  | .timer _ | .pair .. | .response _ => false

theorem Target.byFault_of_covers {g : Target} {f : Fault} (h : g.covers f = true) : g.byFault = true := by
  cases g <;> simp_all [Target.covers, Target.byFault]

theorem Target.byFault_of_meets {g g' : Target} (h : g'.meets g = true) : g'.byFault = g.byFault := by
  cases g <;> cases g' <;> simp_all [Target.meets, Target.byFault]

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}

/-- Whether a step of the kind faults by a fault that falls under `g`, by its terms: it breaks one of its targets that
meets `g` (`StepOut.breaks`, the terms prove's questions ask about). -/
def breakT (g : Target) (inp : SymInput v shs n) (out : StepOut v) : Term :=
  anyT (((out.targets inp.command?).filter (·.meets g)).map (out.breaks inp.command?))

/-- Where a step's terms say what its result is and the result faults by a fault `g` covers, the step's break term
holds. -/
theorem breakT_holds {M : Model} {L : Layout} {T : List TypeDecl} {s : State v} {out : StepOut v}
    {inp : SymInput v shs n} {x : Input v} {f : Fault} {g : Target}
    (hcmd : ∀ i c y, x = .command i c y → inp.command? = some (v.commands.get i).name)
    (hrel : out.Rel M L T shs s x (step T v s x)) (ho : (step T v s x).outcome = .fault f) (hg : g.covers f = true) :
    Holds M (breakT g inp out) := by
  have hf : f ≠ .answerUnmatched := by rintro rfl; rw [Target.covers_unmatched] at hg; cases hg
  obtain ⟨g', hg', hcov, hb⟩ := rel_faults hcmd hrel ho hf
  exact (holds_anyT _).2 ⟨_, List.mem_map_of_mem (List.mem_filter.2 ⟨hg', Target.meets_of_covers hg hcov⟩), hb⟩

/-- Whether a step of the kind faults by a fault that falls under any target a fault breaks, by its terms. One question
with this goal per input kind rules the kind out for every such target at once where it is unsat. -/
def breakAnyT (inp : SymInput v shs n) (out : StepOut v) : Term :=
  anyT (((out.targets inp.command?).filter (·.byFault)).map (out.breaks inp.command?))

theorem breakAnyT_holds {M : Model} {g : Target} {inp : SymInput v shs n} {out : StepOut v} (hg : g.byFault = true)
    (h : Holds M (breakT g inp out)) : Holds M (breakAnyT inp out) := by
  obtain ⟨t, ht, hh⟩ := (holds_anyT _).1 h
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 ht
  obtain ⟨hmem, hm⟩ := List.mem_filter.1 hg'
  exact (holds_anyT _).2 ⟨_, List.mem_map_of_mem (List.mem_filter.2 ⟨hmem, (Target.byFault_of_meets hm).trans hg⟩), hh⟩

end

section
variable (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))

/-- What one input kind adds to a break step from `S` with the selector `sel`, after the steps whose out lines show
`shown`: the kind and the condition that it is the one taken, and the assertion that where it is taken its step from
`S` holds with a well-formed input of valid names whose made ids are shown, stays within the slots and breaks `g`;
or the refusal of its encoding. `unrollKind` with `breakT` in place of the step not faulting. -/
def breakKind (S : SymState v) (shown : List (Term × Term)) (sel : Term) (g : Target)
    (inp : SymInput v (shapes v) senv.nT) :
    Except (SymInput v (shapes v) senv.nT × Refusal) ((SymInput v (shapes v) senv.nT × EncodedStep v) × Term × Term) :=
  match encodeStep L T P v senv S inp, inp.validT L S.fresh, need (lacksDatas inp.dataTys) (inp.wf L) with
  | .ok t, .ok valid, .ok wf =>
    let picks := selectsT sel (inp, t)
    .ok ((inp, t), picks,
      .or (.not picks) (andT wf (andT t.codes (andT t.sites (andT t.cond (andT (breakT g inp t.out)
        (andT valid (inp.knownT L shown))))))))
  | .error r, _, _ | _, .error r, _ | _, _, .error r => .error (inp, r)

/-- A break step, step `i` (from 0) from `S` after steps whose out lines show `shown`, with its selector at the constant
`b` and its pick fixed to `p` where one is: `unrollOne` whose kinds assert that the step breaks `g` (`breakKind`). Its
constants are those of an unrolled step (`breakOne_tys`). The state after it is never read: no step follows. -/
def breakOne (S : SymState v) (shown : List (Term × Term)) (i b : Nat) (p : Option Nat) (g : Target) :
    List Ty × List Term × UnrollStep v senv.nT × List (SymInput v (shapes v) senv.nT × Refusal) :=
  let sel : Term := .var b
  let (inps, _) := placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1)
  let rs := (inps.filter fun inp => p.all (· == inp.pick)).map fun inp => breakKind L T P v senv S shown sel g inp
  let oks := rs.filterMap fun | .ok x => some x | .error _ => none
  let refused := rs.filterMap fun | .error x => some x | .ok _ => none
  ([.int] ++ inps.flatMap (·.tys), oks.map (·.2.2) ++ [anyT (oks.map (·.2.1))], ⟨sel, S, S, oks.map (·.1), []⟩,
    refused)

-- With no step in `B`, the break step starts at the initial state `S0`.
set_option linter.tazuna.silentDefault false in
/-- The break step after the run `B`, from the state its last step leaves (`S0`, the initial state, where it has none),
with its pick fixed to `k`. -/
def breakAfter (S0 : SymState v) (B : UnrollBase v senv.nT) (k : Nat) (g : Target) :
    List Ty × List Term × UnrollStep v senv.nT × List (SymInput v (shapes v) senv.nT × Refusal) :=
  breakOne L T P v senv ((B.steps.getLast?.map (·.after)).getD S0) (B.steps.flatMap (·.shows)) B.steps.length
    B.tys.length (some k) g

end

/-- What a break cube asks after the run of its unfixed steps `Bj`: the assertions of its fixed steps before the last,
which `B` adds to `Bj`, and the break step's (`breakAfter`). -/
def breakGoal {v : ServiceV} {n : Nat} (Bj B : UnrollBase v n) (brk : List Term) : Term :=
  andT (allT (B.asserts.drop Bj.asserts.length)) (allT brk)

section
variable {L : Layout} {T : List TypeDecl} {P : List AnySite} {v : ServiceV} {senv : StepEnv L (shapes v)}

theorem breakKind_ok {S : SymState v} {shown : List (Term × Term)} {sel : Term} {g : Target}
    {inp : SymInput v (shapes v) senv.nT} {x : (SymInput v (shapes v) senv.nT × EncodedStep v) × Term × Term}
    (h : breakKind L T P v senv S shown sel g inp = .ok x) :
    ∃ t valid wf, encodeStep L T P v senv S inp = .ok t ∧ inp.validT L S.fresh = .ok valid ∧ inp.wf L = some wf ∧
      x = ((inp, t), selectsT sel (inp, t),
        .or (.not (selectsT sel (inp, t)))
          (andT wf (andT t.codes (andT t.sites (andT t.cond (andT (breakT g inp t.out) (andT valid
            (inp.knownT L shown)))))))) := by
  unfold breakKind at h
  split at h
  · rename_i t valid wf he hv hw
    cases h
    exact ⟨t, valid, wf, he, hv, need_ok.1 hw, rfl⟩
  all_goals cases h

/-- A break step's constants are an unrolled step's. -/
theorem breakOne_tys (S : SymState v) (shown : List (Term × Term)) (i b : Nat) (p : Option Nat) (g : Target) :
    (breakOne L T P v senv S shown i b p g).1 = (unrollOne L T P v senv S shown i b p).1 := rfl

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}
  (chk : Checked P E T v) (senv : StepEnv L (shapes v))

/-- A break step from terms that denote the run's state `s`, whose constants hold the values of a step `x` can take
that faults by a fault `g` covers, holds its assertions and decodes to `x` (`unrollOne_covers` for a break step). -/
theorem breakOne_covers (hL : SortedLayout L) (S : SymState v) (shown : List (Term × Term)) (i b : Nat) (f : Option Nat)
    (g : Target) {s : State v} {seen : List IdV} (hR : StateRel M L T (shapes v) S s) (hinv : Step.Inv P s)
    (h0 : i = 0 → s.pending = []) (hs : IdsExact M L shown seen)
    (hsrt : ∀ t ∈ (breakOne L T P v senv S shown i b f g).1, (L.srt? t).isSome = true)
    (hnr : (breakOne L T P v senv S shown i b f g).2.2.2 = []) {x : Input v}
    (hvs : (unrollVals L chk.callerData x).isSome) (hfit : StepFits L T P v s x) (hsh : x.Shown T seen s) {fl : Fault}
    (ho : (step T v s x).outcome = .fault fl) (hg : g.covers fl = true) (hf : f.all (· == x.pick) = true)
    (hvars : ∀ q (h : q < (stepVals L v chk.callerData senv.nT i b x).length),
      M.vars (b + q) = (stepVals L v chk.callerData senv.nT i b x)[q]) :
    (∀ a ∈ (breakOne L T P v senv S shown i b f g).2.1, Holds M a) ∧
      (breakOne L T P v senv S shown i b f g).2.2.1.decode M L chk.callerData = some x := by
  have hc := chk.callerData
  obtain ⟨hval, hkn⟩ := hsh
  have hno : (step T v s x).outcome ≠ .fault .answerUnmatched := by
    rw [ho]; intro h; cases h; rw [Target.covers_unmatched] at hg; cases hg
  obtain ⟨vs, hvs'⟩ := Option.isSome_iff_exists.1 hvs
  obtain ⟨hcf, hsf, -, -, -, hstf⟩ := hfit
  have hterms := unrollKinds_terms senv (ans := i != 0)
  have hsplit := placeKinds_split _ (b + 1) hterms
  have hat := placeKinds_at _ (b + 1) hterms
  have hmem := placeKinds_mem (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1)
  rcases hp : placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1) with ⟨inps, e⟩
  rw [hp] at hsplit hat hmem
  dsimp only at hsplit hat hmem
  simp only [breakOne, hp] at hsrt hnr ⊢
  simp only [stepVals, hp] at hvars
  have hb : M.vars b = .int (x.pick : Int) := by simpa using hvars 0 (by simp)
  have hlen : ∀ y ∈ inps, (kindVals L hc x y).length = y.tys.length := fun y hy => by
    obtain ⟨⟨p, hpk, c, rfl⟩, -⟩ := hat.2 y hy
    exact (forall2_length (kindVals_sorted hc hpk c x)).symm
  -- Each placed kind's constants hold its values, and its types have sorts.
  have hplaced : ∀ y ∈ inps, ∃ p ∈ unrollKinds v (shapes v) senv.nT (i != 0), ∃ c, y = p.2 c ∧
      (∀ q (h : q < (kindVals L hc x (p.2 c)).length), M.vars (c + q) = (kindVals L hc x (p.2 c))[q]) ∧
      ∀ t ∈ (p.2 c).tys, (L.srt? t).isSome = true := fun y hy => by
    obtain ⟨pre, post, c, hsp, hcb, p, hpk, rfl⟩ := hsplit y hy
    refine ⟨p, hpk, c, rfl, fun q hq => ?_, fun t ht => hsrt t (by
      simp only [List.singleton_append, List.mem_cons, List.mem_flatMap]; exact .inr ⟨_, hy, ht⟩)⟩
    have hpre : (pre.flatMap (kindVals L hc x)).length = (pre.flatMap SymInput.tys).length :=
      length_flatMap_congr pre fun z hz => hlen z (by rw [hsp]; simp [hz])
    have hidx : (inps.flatMap (kindVals L hc x))[(pre.flatMap (kindVals L hc x)).length + q]? =
        some (kindVals L hc x (p.2 c))[q] := by
      rw [hsp, List.flatMap_append, List.flatMap_cons, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left hq]
      exact List.getElem?_eq_getElem hq
    have hl := (List.getElem?_eq_some_iff.1 hidx).1
    have h := hvars (1 + ((pre.flatMap (kindVals L hc x)).length + q)) (by rw [List.length_cons]; omega)
    rw [show b + (1 + ((pre.flatMap (kindVals L hc x)).length + q)) = c + q by omega] at h
    rw [h]
    have e1 : 1 + ((pre.flatMap (kindVals L hc x)).length + q) = ((pre.flatMap (kindVals L hc x)).length + q) + 1 := by
      omega
    simp only [e1, List.getElem_cons_succ]
    exact (List.getElem?_eq_some_iff.1 hidx).2
  generalize hfil : inps.filter (fun inp => f.all (· == inp.pick)) = kept at hnr
  generalize hoks : (kept.map fun inp => breakKind L T P v senv S shown (.var b) g inp).filterMap
    (fun | .ok x => some x | .error _ => none) = oks
  have hok : ∀ y ∈ oks, ∃ inp ∈ inps, breakKind L T P v senv S shown (.var b) g inp = .ok y := fun y hy => by
    rw [← hoks] at hy
    obtain ⟨r, hrm, hro⟩ := List.mem_filterMap.1 hy
    obtain ⟨inp, hi, rfl⟩ := List.mem_map.1 hrm
    refine ⟨inp, (List.mem_filter.1 (hfil ▸ hi)).1, ?_⟩
    cases hu : breakKind L T P v senv S shown (.var b) g inp with
    | error _ => simp [hu] at hro
    | ok x0 => simp [hu] at hro; rw [hro]
  have hall : ∀ inp ∈ kept, ∃ y, breakKind L T P v senv S shown (.var b) g inp = .ok y ∧ y ∈ oks := fun inp hi => by
    cases hu : breakKind L T P v senv S shown (.var b) g inp with
    | error r =>
      have := (List.filterMap_eq_nil_iff.1 hnr) _ (List.mem_map_of_mem (f := fun inp =>
        breakKind L T P v senv S shown (.var b) g inp) hi)
      simp [hu] at this
    | ok y => exact ⟨y, rfl, hoks ▸ List.mem_filterMap.2 ⟨_, List.mem_map_of_mem hi, by simp [hu]⟩⟩
  -- A kind the model picks is the input's, and decodes to it.
  have hpicked : ∀ inp ∈ inps, ∀ t, encodeStep L T P v senv S inp = .ok t →
      Holds M (selectsT (.var b) (inp, t)) → inp.decode M L hc = some x := by
    intro inp hi t ht hpk
    obtain ⟨p, hpk', c, rfl, hv, -⟩ := hplaced inp hi
    exact decode_of_isOf hc hpk' c hvs' hv (isOf_of_picks hc senv hpk' c hR hno hvs hv hb ht hpk)
  have hassert : ∀ y ∈ oks, Holds M y.2.2 := by
    intro y hy
    obtain ⟨inp, hi, hu⟩ := hok y hy
    obtain ⟨t, valid, wf, ht, hvt, hwf, rfl⟩ := breakKind_ok hu
    simp only [holds_or, holds_not]
    by_cases hpk : Holds M (selectsT (.var b) (inp, t))
    · right
      obtain ⟨p, hpk', c, rfl, hv, hs'⟩ := hplaced inp hi
      have hio := isOf_of_picks hc senv hpk' c hR hno hvs hv hb ht hpk
      have hdec := decode_of_isOf hc hpk' c hvs' hv hio
      have ex := step_encode chk senv hR hinv hdec ht
      have hcodes := ex.1.2 (codesFit_of_decode hdec hcf)
      have hsites := sites_of_decode senv ht hdec hsf
      have hcase := ((holds_andT _ _).1 hpk).2
      have hcond := ((ex.2 hcodes hsites hcase).1).2 hstf
      have hrel := ((ex.2 hcodes hsites hcase).2.1) hcond
      have hokH := breakT_holds (command?_of_decode hdec) hrel ho hg
      have hvalid := valid_of_isOf hc hL hpk' c hvs' hv hio hs' hval hR.fresh hvt
      have hknown := known_of_isOf hc T hpk' c hvs' hv hio hs hkn
      simp only [holds_andT]
      exact ⟨SymInput.wf_of_decode hwf hdec, hcodes, hsites, hcond, hokH, hvalid, hknown⟩
    · exact .inl hpk
  -- The input's own kind is picked.
  have hpickEq : ∀ inp : SymInput v (shapes v) senv.nT, inp.pick = x.pick → Holds M (.eq (.var b) (.int inp.pick)) :=
    fun inp he => by
      simp only [Holds, Term.denote, hb, he, Val.toBool]
      show Val.beq (.int _) (.int _) = true
      simp [Val.beq]
  have hfound : ∃ inp ∈ inps, inp.pick = x.pick ∧ ∀ t, encodeStep L T P v senv S inp = .ok t →
      Holds M (selectsT (.var b) (inp, t)) := by
    have hone : ∀ inp : SymInput v (shapes v) senv.nT, inp.pick = x.pick → (∀ k j to w, inp ≠ .answer k j to w) →
        (∀ ty to w, inp ≠ .unmatched ty to w) → ∀ t, encodeStep L T P v senv S inp = .ok t →
        Holds M (selectsT (.var b) (inp, t)) := fun inp he ha hu t ht => by
      rw [selectsT, holds_andT, encodeStep_case_tt ht ha hu]
      exact ⟨hpickEq inp he, holds_tt⟩
    cases x with
    | command i' caller input =>
      obtain ⟨c, hc'⟩ := hmem (2, fun b => .command i' (.var b) (.var (b + 1))) (by simp [unrollKinds])
      exact ⟨_, hc', rfl, hone _ rfl (by simp) (by simp)⟩
    | query i' caller input =>
      obtain ⟨c, hc'⟩ := hmem (2, fun b => .query i' (.var b) (.var (b + 1))) (by simp [unrollKinds])
      exact ⟨_, hc', rfl, hone _ rfl (by simp) (by simp)⟩
    | event i' value =>
      obtain ⟨c, hc'⟩ := hmem (1, fun b => .event i' (.var b)) (by simp [unrollKinds])
      exact ⟨_, hc', rfl, hone _ rfl (by simp) (by simp)⟩
    | clock time =>
      obtain ⟨c, hc'⟩ := hmem (1, fun b => .clock (.var b)) (by simp [unrollKinds])
      exact ⟨_, hc', rfl, hone _ rfl (by simp) (by simp)⟩
    | answer to w =>
      obtain ⟨ty, value⟩ := w
      obtain ⟨p0, hf, hty⟩ := answer_found hno
      have hi0 : (i != 0) = true := by
        cases i with
        | zero => rw [h0 rfl] at hf; cases hf
        | succ => rfl
      obtain ⟨k, j, hout, hrej, hhit⟩ := answer_hit s to (toT := .int (Int.ofNat to)) hR.pending (by simp [Term.denote])
        senv hf
      have htk : answerTy (shapes v)[k].output (shapes v)[k].rejection = ty := by rw [hty, hout, hrej]
      have htd : ty.isData = true := by
        simp only [unrollVals, inputVals] at hvs
        split at hvs
        · assumption
        · cases hvs
      have hkm : k ∈ answerShapes (shapes v) := by
        simp only [answerShapes, List.mem_filter, List.mem_finRange, true_and]
        rw [htk]; exact htd
      obtain ⟨c, hc'⟩ := hmem (2, fun b => .answer k j (.var b) (.var (b + 1))) (by
        unfold unrollKinds
        rw [ite_eq_left hi0]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.2 ⟨k, hkm, List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩⟩))))
      refine ⟨_, hc', rfl, fun t ht => ?_⟩
      obtain ⟨p', hp', c', heq, hv, -⟩ := hplaced _ hc'
      have heq' : SymInput.answer k j (.var c) (.var (c + 1)) = p'.2 c' := heq
      have hcc : c = c' := by
        have hl := (hterms p' hp' c').1
        have ht' := (hterms p' hp' c').2
        rw [← heq'] at hl ht'
        simp only [SymInput.tys, List.length_cons, List.length_nil] at hl
        rw [← hl] at ht'
        simpa [SymInput.terms, List.range_succ] using ht'
      subst hcc
      have hk0 := kindVals_answer (k := k) (j := j) (toT := .var c) (valT := .var (c + 1)) hc hvs
      rw [heq'] at hk0
      have h0' := hv 0 (List.getElem?_eq_some_iff.1 hk0).1
      rw [(List.getElem?_eq_some_iff.1 hk0).2, Nat.add_zero] at h0'
      rw [selectsT, holds_andT, encodeStep_answer_case ht]
      refine ⟨hpickEq _ rfl, ?_⟩
      simpa [Holds, Term.denote, h0'] using hhit
  obtain ⟨inp0, hi0, hpe0, hpk0⟩ := hfound
  obtain ⟨y0, hu0, hy0⟩ := hall inp0 (hfil ▸ List.mem_filter.2 ⟨hi0, by rw [hpe0]; exact hf⟩)
  obtain ⟨t0, _, _, ht0, _, _, hy0e⟩ := breakKind_ok hu0
  have hpick0 : Holds M y0.2.1 := by rw [hy0e]; exact hpk0 t0 ht0
  have hpick1 : Holds M (selectsT (.var b) y0.1) := by
    rw [hy0e]; exact hpk0 t0 ht0
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at ha
    rcases ha with ⟨y, hy, rfl⟩ | rfl
    · exact hassert y hy
    · exact (holds_anyT _).2 ⟨_, List.mem_map_of_mem hy0, hpick0⟩
  · simp only [UnrollStep.decode, UnrollStep.taken, UnrollStep.picks, Option.bind_eq_bind]
    obtain ⟨k', hk'⟩ : ∃ k', (oks.map (·.1)).find? (fun k =>
        ((selectsT (.var b) k).denote M).toBool) = some k' :=
      Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨_, List.mem_map_of_mem hy0, hpick1⟩)
    rw [hk']
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hk')
    obtain ⟨inp, hi, hu⟩ := hok y hy
    obtain ⟨t, _, _, ht, _, _, hye⟩ := breakKind_ok hu
    have hf := List.find?_some hk'
    rw [hye] at hf ⊢
    exact hpicked inp hi t ht hf


end

section
variable {L : Layout} {T : List TypeDecl} {P : List AnySite} {v : ServiceV} {E : List AnyEffectSite}

/-- What search shows of the break cube `ps` (its picks in step order, the break step's last, `ps.length`
at most `d`) at depth `d` for the target `g`: it has no model, as an unsat answer to its question (`cubeAsk` with
`breakGoal`) or a goal false by its shape says, and refuses no input kind; or for every kind of its last pick, the step
question (`stepAsk`) whether its step breaks `g` (`breakT`), or any target a fault breaks (`breakAnyT`), is unsat, or
`breakT` is false by its terms; or it splits on the step before its fixed ones, into one cube per pick. -/
inductive BreakCover (senv : StepEnv L (shapes v)) (g : Target) (d : Nat) : List Nat → Prop
  | leaf {ps : List Nat} {k : Nat} {Bj Bd B : UnrollBase v senv.nT} {S0 : SymState v} {ls : List String} :
    ps.length ≤ d → ps.getLast? = some k →
    unrollBase L T P v senv (List.replicate (d - ps.length) none) = .ok Bj →
    unrollBase L T P v senv (List.replicate d none) = .ok Bd → initState L v = some S0 →
    extendBase L T P v senv S0 Bj (ps.dropLast.map some) = .ok B → B.refused = [] →
    (breakAfter L T P v senv S0 B k g).2.2.2 = [] →
    Unsat L (cubeAsk Bj Bd ls (breakGoal Bj B (breakAfter L T P v senv S0 B k g).2.1)) ∨
      (breakGoal Bj B (breakAfter L T P v senv S0 B k g).2.1).falsy = true →
    BreakCover senv g d ps
  | deadLast {ps : List Nat} {k : Nat} :
    ps.getLast? = some k → v.Equivariant → Step.invariants (Step.State.init v) = [] → initFits L v = true →
    (∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), ∃ a, stepAsk L T P v senv inp = .ok a ∧
      (inp.pick = k → Unsat L (a.ask (breakT g inp a.t.out)) ∨ Unsat L (a.ask (breakAnyT inp a.t.out)) ∨
        (breakT g inp a.t.out).const?.map Val.toBool = some false)) →
    BreakCover senv g d ps
  | split {ps : List Nat} : ps.length < d → (∀ k < pickCount v, BreakCover senv g d (k :: ps)) →
    BreakCover senv g d ps

theorem shownRun_last {x : Input v} : (ys : List (Input v)) → (seen : List IdV) → (s : State v) →
    Step.ShownRun T seen s (ys ++ [x]) →
    Step.ShownRun T seen s ys ∧ x.Shown T (runSeen T v seen s ys) (run T v s ys).1
  | [], _, _, h => ⟨trivial, by simpa [runSeen, run] using h.1⟩
  | _ :: ys, _, _, ⟨h1, h2⟩ => by
    have ih := shownRun_last ys _ _ h2
    exact ⟨⟨h1, ih.1⟩, by simpa [runSeen, run] using ih.2⟩

/-- A run of `n + 1` steps has the constants of a run of `n` steps and then one unrolled step's. -/
theorem unrollBase_tys_succ (senv : StepEnv L (shapes v)) {fs : List (Option Nat)} {B Bd : UnrollBase v senv.nT}
    (hB : unrollBase L T P v senv fs = .ok B) (hBd : unrollBase L T P v senv (List.replicate (fs.length + 1) none) = .ok Bd)
    (S : SymState v) (shown : List (Term × Term)) (p : Option Nat) :
    Bd.tys = B.tys ++ (unrollOne L T P v senv S shown fs.length B.tys.length p).1 := by
  simp only [unrollBase] at hB hBd
  obtain ⟨S0, hS0, hB⟩ := bind_ok.1 hB
  obtain ⟨_, -, hB⟩ := bind_ok.1 hB
  obtain ⟨_, -, hB⟩ := bind_ok.1 hB
  cases pure_ok.1 hB
  obtain ⟨S0', hS0', hBd⟩ := bind_ok.1 hBd
  obtain ⟨_, -, hBd⟩ := bind_ok.1 hBd
  obtain ⟨_, -, hBd⟩ := bind_ok.1 hBd
  cases pure_ok.1 hBd
  dsimp only
  rw [unrollSteps_tys (List.replicate (fs.length + 1) none) (fs ++ [none]) (by simp) S0' S0 [] [] 0 0,
    unrollSteps_append]
  simp only [Nat.zero_add, unrollSteps, List.append_nil]
  exact congrArg _ (unrollOne_tys (T := T) (P := P) (senv := senv) _ S _ shown fs.length _ none p).1

-- With no step before the break step, it starts at the initial state `S0`.
set_option linter.tazuna.silentDefault false in
/-- T6b for a break target at depth `d`: where search's break cubes cover the depth (`BreakCover` from no fixed step),
no run from the initial state of `d` inputs that fit the slots and are valid, whose steps stay within the slots and
whose steps before the last fault nowhere, faults at its last step by a fault `g` covers. search's "unsettled within
k steps" is this at every depth up to k. -/
theorem noModel_breaks (chk : Checked P E T v) (senv : StepEnv L (shapes v)) (hL : SortedLayout L)
    {g : Target} {d : Nat} (hc : BreakCover (T := T) (P := P) senv g d [])
    {ys : List (Input v)} {x : Input v} (hlen : ys.length + 1 = d)
    (hin : RunIn L T P v chk.callerData (Step.State.init v) (ys ++ [x]))
    (hshown : Step.ShownRun T [] (Step.State.init v) (ys ++ [x]))
    (hno : Step.NoFaultRun T (Step.State.init v) ys) {f : Fault}
    (hf : (step T v (run T v (Step.State.init v) ys).1 x).outcome = .fault f) : g.covers f = false := by
  have hxl : (ys ++ [x]).length = d := by simp [hlen]
  obtain ⟨hinYs, hinX⟩ := eachStep_last ys _ hin
  obtain ⟨hshYs, hshX⟩ := shownRun_last ys _ _ hshown
  refine Bool.eq_false_iff.2 fun hg => ?_
  suffices h : ∀ ps, BreakCover (T := T) (P := P) senv g d ps →
      ((ys ++ [x]).drop (d - ps.length)).map (·.pick) = ps → False from
    h [] hc (by simp; omega)
  intro ps hcov
  induction hcov with
  | @leaf ps k Bj Bd B S0 ls hp hk hBj hBd hS0 hB hnr hnr' hun =>
    intro hx
    have hne : ps ≠ [] := by rintro rfl; cases hk
    have hp1 : 1 ≤ ps.length := List.length_pos_iff.2 hne
    -- The picks of the run before the break step are the cube's before its last, and the break step's is its last.
    have hsplit : (ys.drop (d - ps.length)).map (·.pick) = ps.dropLast ∧ x.pick = k := by
      rw [List.drop_append_of_le_length (by omega), List.map_append] at hx
      have h1 := congrArg List.dropLast hx
      have h2 := congrArg List.getLast? hx
      simp only [List.map_cons, List.map_nil, List.dropLast_concat] at h1
      simp only [List.map_cons, List.map_nil, List.getLast?_concat, hk, Option.some.injEq] at h2
      exact ⟨h1, h2⟩
    have hfs : List.replicate (d - ps.length) none ++ ps.dropLast.map some = cubeFilters ys.length ps.dropLast := by
      simp only [cubeFilters, List.length_dropLast]
      congr 2
      omega
    have hBc : unrollBase L T P v senv (List.replicate (d - ps.length) none ++ ps.dropLast.map some) = .ok B :=
      extendBase_ok hBj hS0 hB
    have hpk : PicksFit (List.replicate (d - ps.length) none ++ ps.dropLast.map some) ys := by
      rw [hfs]
      refine picksFit_cube rfl ?_
      rw [List.length_dropLast, show ys.length - (ps.length - 1) = d - ps.length by omega]
      exact hsplit.1
    have hflen : (List.replicate (d - ps.length) none ++ ps.dropLast.map some).length = ys.length := by
      simp only [List.length_append, List.length_replicate, List.length_map, List.length_dropLast]; omega
    have htys := unrollBase_tys_succ senv hBc (by rw [hflen, hlen]; exact hBd)
      ((B.steps.getLast?.map (·.after)).getD S0) (B.steps.flatMap (·.shows)) (some k)
    -- The model: the run's values, then the break step's.
    simp only [unrollBase] at hBc
    obtain ⟨S0', hS0', hBc⟩ := bind_ok.1 hBc
    have e0 : S0' = S0 := by rw [need_ok.1 hS0'] at hS0; exact Option.some.inj hS0
    subst e0
    obtain ⟨dts, hdts, hBc⟩ := bind_ok.1 hBc
    rcases hr : unrollSteps L T P v senv S0' [] 0 0 (List.replicate (d - ps.length) none ++ ps.dropLast.map some) with
      ⟨tys, asserts, steps, refused⟩
    rw [hr] at hBc
    obtain ⟨vars, hvars, hBc⟩ := bind_ok.1 hBc
    cases pure_ok.1 hBc
    simp only [breakAfter] at hnr' hun
    dsimp only at htys hnr hnr' hun
    have hc := chk.callerData
    let M := coverModel L (runVals L v hc senv.nT 0 0 ys ++
      stepVals L v hc senv.nT ys.length tys.length x)
    have hv := unrollSteps_vals chk senv ys _ hflen S0' [] 0 0
    rw [hr] at hv
    dsimp only at hv
    have hvl : (runVals L v hc senv.nT 0 0 ys).length = tys.length := (forall2_length hv.1).symm
    have hsl : steps.length = ys.length := by
      have := unrollSteps_length (L := L) (T := T) (P := P) (senv := senv) S0' [] 0 0
        (List.replicate (d - ps.length) none ++ ps.dropLast.map some)
      rw [hr] at this; simp at this; omega
    rw [hflen] at htys
    have hsrtBd : ∀ t ∈ Bd.tys, (L.srt? t).isSome = true :=
      mapM_some_mem (by rw [unrollBase_vars L T P v senv hBd]; rfl)
    have hsrt : ∀ t ∈ tys, (L.srt? t).isSome = true := fun t ht => hsrtBd t (by rw [htys]; exact List.mem_append_left _ ht)
    have hfits : RunFits L T P v hc [] (Step.State.init v) ys := runFits_shown L T P v hc [] _ ys hinYs hshYs hno
    have hcov := unrollSteps_covers (M := M) chk senv hL ys _ hpk S0' [] 0 0 (init_rel (need_ok.1 hS0'))
      Step.init_inv (fun _ => rfl) IdsExact.nil (by rw [hr]; exact hsrt) (by rw [hr]; exact hnr) hfits fun q h => by
        rw [Nat.zero_add]
        exact coverModel_vars (by rw [List.getElem?_append_left h]; exact List.getElem?_eq_getElem h)
    rw [hr] at hcov
    dsimp only at hcov
    obtain ⟨hA, -, hRend, hsEnd⟩ := hcov
    rw [List.nil_append] at hsEnd
    rw [hsl] at hnr' hun
    have hsrtB : ∀ t ∈ (breakOne L T P v senv ((steps.getLast?.map (·.after)).getD S0') (steps.flatMap (·.shows))
        ys.length tys.length (some k) g).1, (L.srt? t).isSome = true := by
      intro t ht
      rw [breakOne_tys] at ht
      exact hsrtBd t (by rw [htys]; exact List.mem_append_right _ ht)
    have hbrk := breakOne_covers chk senv hL ((steps.getLast?.map (·.after)).getD S0') (steps.flatMap (·.shows))
      ys.length tys.length (some k) g hRend (run_inv T chk.reach _ Step.init_inv ys)
      (fun h => by rw [List.length_eq_zero_iff.1 h]; rfl) hsEnd
    have hbrk := hbrk (by exact hsrtB) (by exact hnr') hinX.1 hinX.2 hshX hf hg
      (by simp [hsplit.2]) fun q h => coverModel_vars (by
        rw [List.getElem?_append_right (by omega), show tys.length + q - (runVals L v hc senv.nT 0 0 ys).length = q
          by omega]
        exact List.getElem?_eq_getElem h)
    -- Every variable of the cube's question holds a value of its sort.
    have hvb := (unrollOne_vals chk senv ((steps.getLast?.map (·.after)).getD S0') (steps.flatMap (·.shows))
      ys.length tys.length (some k) x)
    have hall : Forall2 (SortedIf L) Bd.tys (runVals L v hc senv.nT 0 0 ys ++ stepVals L v hc senv.nT ys.length tys.length x) := by
      rw [htys]; exact forall2_append hv.1 hvb.1
    have hdata : ∀ t ∈ Bd.tys, t.isData = true := fun t ht => by
      rw [htys] at ht
      rcases List.mem_append.1 ht with ht | ht
      · exact hv.2 t ht
      · exact hvb.2 t ht
    have hsorted := forall2_sorted_of hall fun t ht => sorted_exists (unrollBase_dts L T P v senv hBd) t (hsrtBd t ht)
      (hdata t ht)
    have hM : ∀ n (h : n < Bd.tys.length), VarSorted L Bd.tys[n] (M.vars n) :=
      fun n h => varSorted_of_sorted (forall2_sorted_vars (forall2_imp (fun _ _ h => h.1) hsorted) n h)
    have hS : LayoutSorted L Bd.tys M := layoutSorted_coverModel (forall2_imp (fun _ _ h => h.2) hsorted) hdata
    have hgoal : Holds M (breakGoal Bj ⟨dts, tys, vars, asserts, steps, refused⟩
        (breakOne L T P v senv ((steps.getLast?.map (·.after)).getD S0') (steps.flatMap (·.shows)) ys.length
          tys.length (some k) g).2.1) := by
      rw [breakGoal, holds_andT, holds_allT, holds_allT]
      exact ⟨fun c hc' => hA c (List.mem_of_mem_drop hc'), hbrk.1⟩
    have hBa : asserts = Bj.asserts ++ asserts.drop Bj.asserts.length := by
      simp only [extendBase] at hB
      obtain ⟨_, -, hB⟩ := bind_ok.1 hB
      have := congrArg UnrollBase.asserts (pure_ok.1 hB)
      simp only at this
      rw [← this]; simp
    rcases hun with hun | hfal
    · obtain ⟨a, ha, hna⟩ := hun.noModel_at (tys := Bd.tys) (by simp [cubeAsk])
        (unrollBase_dts L T P v senv hBd) (unrollBase_vars L T P v senv hBd) M hM hS
      refine hna ((?_ : ∀ a ∈ Bj.asserts ++ [litsFact ls, breakGoal Bj ⟨dts, tys, vars, asserts, steps, refused⟩
        (breakOne L T P v senv ((steps.getLast?.map (·.after)).getD S0') (steps.flatMap (·.shows)) ys.length
          tys.length (some k) g).2.1], Holds M a) a (by simpa [cubeAsk, TypedScript.script] using ha))
      intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ha | rfl | rfl
      · exact hA a (hBa ▸ List.mem_append_left _ ha)
      · simp [litsFact, Holds, Term.denote, Val.toBool, tt]
      · exact hgoal
    · exact Term.not_holds_of_falsy _ hfal hgoal
  | @deadLast ps k hk he hinit h0 hasks =>
    intro hx
    have hne : ps ≠ [] := by rintro rfl; cases hk
    have hxk : x.pick = k := by
      have h1 := congrArg List.getLast? hx
      rw [List.getLast?_map, hk, List.getLast?_drop, List.getLast?_concat] at h1
      split at h1
      · simp at h1
      · simpa using h1
    have hW := within_runIn chk he senv (fun inp hm => (hasks inp hm).imp fun _ h => h.1) hinit h0 ys hshYs.valid hinYs
    have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
    have hsupp := Step.run_supp T he chk.reach _ Step.init_inv (Step.init_supp he) ys hshYs.valid
    have hkeys := run_keys T _ (Step.init_keys T hord chk.idle) ys
    have hfault : f ≠ .answerUnmatched := by rintro rfl; rw [Target.covers_unmatched] at hg; cases hg
    obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.1 (inputVals_isSome hinX.1)
    rcases covered chk senv hkeys hW x hivs with ⟨inp, hmem, hc, M, hM, hsel, hS, hxd, hcase⟩ | h
    · have hpk : inp.pick = k := (SymInput.pick_of_decode hxd).trans hxk
      obtain ⟨a, ha, hun⟩ := hasks inp hmem
      have hinvs := run_inv T chk.reach _ Step.init_inv ys
      obtain ⟨hside, hheld, hcond, hrel⟩ := stepAsk_step chk senv ha hS hinvs hsupp hkeys
        (Tazuna.Ir.run_invariants T _ ys hinit) hxd hcase (.inr hinX.2)
      have hbrk := breakT_holds (command?_of_decode hxd) hrel hf hg
      have hnone : ∀ goal, Unsat L (a.ask goal) → ¬ Holds M goal := fun goal hu =>
        stepAsk_goal chk senv ha hS hinvs hsupp hkeys hxd hcase hside hheld hcond
          (hu.noModel_at (stepAsk_tys L T P v senv ha _) (stepAsk_dts L T P v senv ha _)
            (stepAsk_vars L T P v senv ha _) M (fun n h => varSorted_of_sorted (hM n h)) hsel)
      rcases hun hpk with hu | hu | hf0
      · exact hnone _ hu hbrk
      · exact hnone _ hu (breakAnyT_holds (Target.byFault_of_covers hg) hbrk)
      · cases hk : (breakT g inp a.t.out).const? with
        | none => rw [hk] at hf0; cases hf0
        | some w =>
          rw [hk] at hf0
          simp only [Option.map_some, Option.some.injEq] at hf0
          simp only [Holds, Term.const?_denote M _ hk, hf0] at hbrk
          cases hbrk
    · exact h.1 f hfault hf
  | @split ps hp _ ih =>
    intro hx
    have hj : 0 < d - ps.length := by omega
    have hk : ((ys ++ [x])[d - ps.length - 1]'(by omega)).pick < pickCount v := Input.pick_lt _
    refine ih _ hk ?_
    rw [List.length_cons, show d - (ps.length + 1) = d - ps.length - 1 by omega,
      List.drop_eq_getElem_cons (by omega), List.map_cons, show d - ps.length - 1 + 1 = d - ps.length by omega, hx]

end

end Tazuna.Smt
