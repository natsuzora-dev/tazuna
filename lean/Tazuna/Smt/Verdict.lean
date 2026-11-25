import Tazuna.Smt.Prove
import Tazuna.Semantics.After
import Tazuna.Smt.StepSites

/-! T4 for a step: where the solver finds no model of an input kind's bound question and of its questions about the
targets a fault `f` falls under (the invariant or `ensures` rules of its name, the cascade bound, the own command or
query it names), no step of that kind from a state of the right shape whose invariants hold faults with `f`. Steps that fault leave the state they began with, and the others commit only states whose invariants hold, so
every state a run reaches from an initial state whose invariants hold is such a state. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- A value of an effect type's datatype: one of its variants, request kinds then own kinds, with fields of their
sorts, or the one constructor the datatype gets when no kind exists. `Sorted` holds of no effect value: only a pair
question has variables of an effect type. -/
def EffSorted (L : Layout) (e : Ty) (w : Val) : Prop :=
  ∃ d n k vals, L.find? (.dsl .effect [e]) = some (d, n) ∧ w = .ctor d k vals ∧
    ((∃ fs, (L.effectFields e)[k]? = some fs ∧ SortedVs L fs vals) ∨ (L.effectFields e = [] ∧ k = 0 ∧ vals = []))

/-- A value of the sort a script declares a variable of the type at. -/
def VarSorted (L : Layout) : Ty → Val → Prop
  | .dsl .effect [e], w => EffSorted L e w
  | t, w => Sorted L t w

theorem varSorted_of_sorted {L : Layout} {t : Ty} {w : Val} (h : Sorted L t w) : VarSorted L t w := by
  unfold VarSorted
  split
  · simp [Sorted] at h
  · exact h

/-- Every variable's sort holds a value, as SMT-LIB requires of every sort a script declares. -/
def SortsInhabited (L : Layout) (tys : List Ty) : Prop :=
  ∃ M : Model, ∀ n (h : n < tys.length), VarSorted L tys[n] (M.vars n)

/-- The solver found no model of the script: no model whose variables hold values of the sorts of the types `tys`
satisfies every assertion. A model of the script as SMT-LIB reads it is such a model (`Term.denote` states the
standard's meaning), so this is what an unsat answer says. The sorts hold values, as SMT-LIB's do, so an unsat answer
is never free: a script with no assertion is not unsat (run-log 147, where a sort with no value made every pair
question unsat whatever it asked). `sorts_inhabited` proves the sorts of every script an encoder builds hold values. -/
structure Unsat (L : Layout) (tys : List Ty) (s : Script) : Prop where
  sorts : SortsInhabited L tys
  noModel : ∀ M : Model, (∀ n (h : n < tys.length), VarSorted L tys[n] (M.vars n)) → ∃ a ∈ s.asserts, ¬ Holds M a

section
variable {M : Model}

theorem holds_not (a : Term) : Holds M (.not a) ↔ ¬ Holds M a := by
  simp [Holds, Term.denote, Val.toBool]

theorem holds_or (a b : Term) : Holds M (.or a b) ↔ Holds M a ∨ Holds M b := by
  simp [Holds, Term.denote, Val.toBool]

theorem holds_anyT (ts : List Term) : Holds M (anyT ts) ↔ ∃ t ∈ ts, Holds M t := by
  simp [Holds, anyT_denote, Val.toBool]

theorem holds_allT_rules (rules : List (Term × Term)) : Holds M (allT (rules.map (·.2))) ↔ brokenIn M rules = [] := by
  rw [brokenIn_nil]; simp [Holds, allT_denote, Val.toBool]

/-- A name `brokenIn` reports is a rule whose holds term is false and whose name term has that string. -/
theorem mem_brokenIn {rules : List (Term × Term)} {n : String} (h : n ∈ brokenIn M rules) :
    ∃ rule ∈ rules, ¬ Holds M rule.2 ∧ (rule.1.denote M).toStr = n := by
  simp only [brokenIn, List.mem_filterMap] at h
  obtain ⟨⟨a, b⟩, hm, h⟩ := h
  split at h
  · cases h
  · rename_i hb
    cases h
    exact ⟨(a, b), hm, by simpa [Holds] using hb, rfl⟩

theorem mem_dedup {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {x : α} (h : x ∈ xs) : x ∈ dedup xs := by
  have key : ∀ (ys acc : List α), (x ∈ acc ∨ x ∈ ys) →
      x ∈ ys.foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) acc := by
    intro ys
    induction ys with
    | nil => intro acc h; simpa using h
    | cons y ys ih =>
      intro acc h
      apply ih
      by_cases hy : acc.contains y = true
      · simp only [hy, ite_true]
        rcases h with h | h
        · exact .inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inl (by simpa using hy)
          · exact .inr h
      · simp only [hy, Bool.false_eq_true, ite_false]
        rcases h with h | h
        · exact .inl (List.mem_append_left _ h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inl (by simp)
          · exact .inr h
  exact key xs [] (.inr h)

theorem mem_ruleNames {rules : List (Term × Term)} {rule : Term × Term} {g : Option String} (hm : rule ∈ rules)
    (hg : ruleName? rule = some g) : g ∈ ruleNames rules :=
  mem_dedup (List.mem_filterMap.2 ⟨rule, hm, hg⟩)

/-- A broken rule's name, as its terms give it, is the string the model gives or one the model decides. -/
theorem ruleName_of_broken {rule : Term × Term} {r : String} (hb : ¬ Holds M rule.2) (hn : (rule.1.denote M).toStr = r) :
    ∃ g, (g = some r ∨ g = none) ∧ ruleName? rule = some g := by
  unfold ruleName?
  split
  · rename_i ht
    obtain ⟨w, hw, hwt⟩ := Option.map_eq_some_iff.1 ht
    exact absurd (by simp [Holds, Term.const?_denote M _ hw, hwt]) hb
  · split
    · rename_i s hs
      refine ⟨some s, .inl ?_, rfl⟩
      rw [Term.const?_denote M _ hs] at hn
      simpa [Val.toStr] using hn
    · exact ⟨none, .inr rfl, rfl⟩

theorem holds_brokenT {rules : List (Term × Term)} {rule : Term × Term} {g : Option String} (hm : rule ∈ rules)
    (hg : ruleName? rule = some g) (hb : ¬ Holds M rule.2) : Holds M (brokenT g rules) := by
  unfold brokenT
  rw [holds_anyT]
  exact ⟨.not rule.2, List.mem_filterMap.2 ⟨rule, hm, by simp [hg]⟩, (holds_not _).2 hb⟩

/-- A broken rule named `r` makes the question of its name true: the literal's when the terms hold it, else the
question of the names the model decides. -/
theorem brokenT_of_mem {rules : List (Term × Term)} {r : String} (h : r ∈ brokenIn M rules) :
    ∃ g, (g = some r ∨ g = none) ∧ g ∈ ruleNames rules ∧ Holds M (brokenT g rules) := by
  obtain ⟨rule, hm, hb, hn⟩ := mem_brokenIn h
  obtain ⟨g, hg, hr⟩ := ruleName_of_broken hb hn
  exact ⟨g, hg, mem_ruleNames hm hr, holds_brokenT hm hr hb⟩

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem mem_instBroken {t : Ty} {cs : List InstCheck} {n : String} (h : n ∈ instBroken L T M t cs) :
    ∃ c ∈ cs, Holds M c.occupied ∧ n ∈ brokenIn M c.rules := by
  simp only [instBroken, List.mem_flatMap, List.mem_mergeSort, List.mem_filter] at h
  obtain ⟨c, ⟨hc, ho⟩, hn⟩ := h
  exact ⟨c, hc, ho, hn⟩

theorem instBroken_nil {t : Ty} {cs : List InstCheck} (h : instBroken L T M t cs = []) :
    ∀ c ∈ cs, Holds M c.occupied → brokenIn M c.rules = [] := by
  intro c hc ho
  apply List.eq_nil_iff_forall_not_mem.2
  intro n hn
  have : n ∈ instBroken L T M t cs := by
    simp only [instBroken, List.mem_flatMap, List.mem_mergeSort, List.mem_filter]
    exact ⟨c, ⟨hc, ho⟩, hn⟩
  rw [h] at this
  cases this

/-- Where no instance's rule is broken, every instance's rules hold. -/
theorem instHold_of_nil : (ms : List (MachineV r e)) → (checks : PerMachine (fun _ => List InstCheck) ms) →
    checksBroken L T M ms checks = [] → Holds M (allT (checks.toList.map instHoldT))
  | [], .nil, _ => holds_tt
  | m :: ms, .cons cs rest, h => by
    simp only [checksBroken, List.append_eq_nil_iff] at h
    simp only [PerMachine.toList, List.map_cons]
    rw [show allT (instHoldT cs :: rest.toList.map instHoldT) = .and (instHoldT cs) (allT (rest.toList.map instHoldT))
      from rfl, holds_and]
    refine ⟨?_, instHold_of_nil ms rest h.2⟩
    unfold instHoldT
    rw [holds_allT]
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    rw [holds_or, holds_not, holds_allT_rules]
    by_cases ho : Holds M c.occupied
    · exact .inr (instBroken_nil h.1 c hc ho)
    · exact .inl ho

/-- Where every instance's rules hold, no instance's rule is broken. -/
theorem nil_of_instHold : (ms : List (MachineV r e)) → (checks : PerMachine (fun _ => List InstCheck) ms) →
    Holds M (allT (checks.toList.map instHoldT)) → checksBroken L T M ms checks = []
  | [], .nil, _ => rfl
  | m :: ms, .cons cs rest, h => by
    simp only [PerMachine.toList, List.map_cons] at h
    rw [show allT (instHoldT cs :: rest.toList.map instHoldT) = .and (instHoldT cs) (allT (rest.toList.map instHoldT))
      from rfl, holds_and] at h
    simp only [checksBroken, List.append_eq_nil_iff]
    refine ⟨List.eq_nil_iff_forall_not_mem.2 fun n hn => ?_, nil_of_instHold ms rest h.2⟩
    obtain ⟨c, hc, ho, hn⟩ := mem_instBroken hn
    have hhold := (holds_allT _).1 h.1 _ (List.mem_map_of_mem hc)
    rw [holds_or, holds_not, holds_allT_rules] at hhold
    rcases hhold with hno | hnil
    · exact hno ho
    · rw [hnil] at hn; cases hn

/-- An instance rule named `n` broken at a step's end makes the question of its machine and name true. -/
theorem instBrokenT_of_mem : (ms : List (MachineV r e)) → (checks : PerMachine (fun _ => List InstCheck) ms) →
    {n : String} → n ∈ checksBroken L T M ms checks →
    ∃ mc ∈ checks.toSigma, ∃ g, (g = some n ∨ g = none) ∧ g ∈ ruleNames (mc.2.flatMap (·.rules)) ∧
      Holds M (instBrokenT g mc.2)
  | [], .nil, _, h => by cases h
  | m :: ms, .cons cs rest, n, h => by
    simp only [checksBroken, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨c, hc, ho, hn⟩ := mem_instBroken h
      obtain ⟨rule, hm, hb, hname⟩ := mem_brokenIn hn
      obtain ⟨g, hg, hr⟩ := ruleName_of_broken hb hname
      refine ⟨⟨m, cs⟩, by simp [PerMachine.toSigma], g, hg,
        mem_ruleNames (List.mem_flatMap.2 ⟨c, hc, hm⟩) hr, ?_⟩
      unfold instBrokenT
      rw [holds_anyT]
      exact ⟨_, List.mem_map_of_mem hc, (holds_and _ _).2 ⟨ho, holds_brokenT hm hr hb⟩⟩
    · obtain ⟨mc, hmc, rest'⟩ := instBrokenT_of_mem ms rest h
      exact ⟨mc, by simp [hmc], rest'⟩

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

theorem instBrokenT_mono {g : Option String} {cs cs' : List InstCheck} (hsub : ∀ c ∈ cs, c ∈ cs')
    (h : Holds M (instBrokenT g cs)) : Holds M (instBrokenT g cs') := by
  unfold instBrokenT at h ⊢
  rw [holds_anyT] at h ⊢
  obtain ⟨x, hx, hh⟩ := h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  exact ⟨_, List.mem_map_of_mem (hsub c hc), hh⟩

/-- An internal step's fault breaks one of its kind's targets, as the kind's terms say. -/
theorem kind_breaks {f : Fault} : (k : OwnKindOut v) → k.fault? M = some f →
    ∃ g ∈ k.targets, g.covers f = true ∧ Holds M (k.breaks g)
  | .command name o, h => by
    simp only [OwnKindOut.fault?] at h
    split at h
    · rename_i hcall
      split at h
      · rename_i n ns hl
        cases h
        refine ⟨.effect name, by simp [OwnKindOut.targets], by simp [Target.covers], ?_⟩
        simp only [OwnKindOut.breaks, ite_true, holds_or, holds_not, holds_allT_rules, hl]
        exact .inr (by simp)
      · rename_i hl
        split at h
        · rename_i n rest hok hens
          cases h
          obtain ⟨g, hg, hmem, hb⟩ := brokenT_of_mem (M := M) (r := n) (by rw [hens]; simp)
          refine ⟨.ensures name g, by simp [OwnKindOut.targets, hmem], by rcases hg with rfl | rfl <;> simp [Target.covers], ?_⟩
          simp only [OwnKindOut.breaks, ite_true]
          exact (holds_andT _ _).2 ⟨by simpa [Holds] using hcall, (holds_andT _ _).2 ⟨(holds_allT_rules _).2 hl,
            (holds_andT _ _).2 ⟨by simpa [Holds] using hok, hb⟩⟩⟩
        · cases h
    · rename_i hcall
      cases h
      refine ⟨.effect name, by simp [OwnKindOut.targets], by simp [Target.covers], ?_⟩
      simp only [OwnKindOut.breaks, ite_true, holds_or, holds_not]
      exact .inl (by simpa [Holds] using hcall)
  | .query name o, h => by
    simp only [OwnKindOut.fault?] at h
    split at h
    · split at h
      · rename_i n ns hl
        cases h
        refine ⟨.effect name, by simp [OwnKindOut.targets], by simp [Target.covers], ?_⟩
        simp only [OwnKindOut.breaks, ite_true, holds_or, holds_not, holds_allT_rules, hl]
        exact .inr (by simp)
      · cases h
    · rename_i hcall
      cases h
      refine ⟨.effect name, by simp [OwnKindOut.targets], by simp [Target.covers], ?_⟩
      simp only [OwnKindOut.breaks, ite_true, holds_or, holds_not]
      exact .inl (by simpa [Holds] using hcall)
  | .missing name, h => by
    simp only [OwnKindOut.fault?, Option.some.injEq] at h
    subst h
    exact ⟨.effect name, by simp [OwnKindOut.targets], by simp [Target.covers], by simp [OwnKindOut.breaks, holds_tt]⟩

theorem kind_breaks_ne {k : OwnKindOut v} {g : Target} (h : Holds M (k.breaks g)) : g ≠ .cascade ∧ ∀ m r, g ≠ .invariant m r := by
  refine ⟨?_, fun m r => ?_⟩ <;> rintro rfl <;> cases k <;> simp [OwnKindOut.breaks, Holds, Term.denote, Val.toBool] at h

/-- The cascade's fault breaks one of its targets, as its terms say: an internal step it runs breaks one of its
kind's, or a place past the bound is occupied. -/
theorem settle_breaks {f : Fault} (o : SettleOut v) (h : o.fault? M = some f) :
    ∃ g ∈ o.targets, g.covers f = true ∧ Holds M (o.breaks g) := by
  unfold SettleOut.fault? at h
  split at h
  · rename_i st hst
    have hmem := List.mem_of_find?_eq_some hst
    have hpred := List.find?_some hst
    simp only [Bool.and_eq_true] at hpred
    obtain ⟨k, hk, hkf⟩ := Option.bind_eq_some_iff.1 h
    have hkm := List.mem_of_find?_eq_some hk
    have htest := List.find?_some hk
    obtain ⟨g, hg, hcov, hbr⟩ := kind_breaks k.2 hkf
    refine ⟨g, List.mem_append_left _ (List.mem_flatMap.2 ⟨st, hmem, List.mem_flatMap.2 ⟨k, hkm, hg⟩⟩), hcov, ?_⟩
    have hb : Holds M (anyT (o.steps.map fun st => andT st.1 (anyT (st.2.kinds.map fun k => andT k.1 (k.2.breaks g))))) :=
      (holds_anyT _).2 ⟨_, List.mem_map_of_mem hmem, (holds_andT _ _).2 ⟨hpred.1,
        (holds_anyT _).2 ⟨_, List.mem_map_of_mem hkm, (holds_andT _ _).2 ⟨htest, hbr⟩⟩⟩⟩
    obtain ⟨hnc, hni⟩ := kind_breaks_ne hbr
    cases g with
    | cascade => exact absurd rfl hnc
    | invariant m r => exact absurd rfl (hni m r)
    | _ => exact hb
  · split at h
    · rename_i hover
      cases h
      exact ⟨.cascade, by simp [SettleOut.targets], rfl, hover⟩
    · cases h

theorem settle_targets_ne {o : SettleOut v} {g : Target} (h : g ∈ o.targets) : ∀ m r, g ≠ .invariant m r := by
  intro m r hg
  subst hg
  simp only [SettleOut.targets, List.mem_append, List.mem_flatMap, List.mem_singleton] at h
  rcases h with ⟨_, _, k, _, hk⟩ | h
  · cases hk' : k.2 <;> simp [hk', OwnKindOut.targets] at hk
  · cases h

/-- Where a step's end faults with `f` other than its own outcome, the cascade breaks one of its targets, or the
cascade does not fault and the end breaks an invariant target. -/
theorem finished_faults {shs : List (PendingShape v.event)} {fo : FinishOut v} {s0 : State v} {a : Step.Acc v}
    {outcome : Outcome} {res : Result v} {f : Fault} (hf : Finished M L T shs fo s0 a outcome res)
    (ho : res.outcome = .fault f) (hacc : outcome ≠ .fault f) :
    (∃ g ∈ fo.settle.targets, g.covers f = true ∧ Holds M (fo.settle.breaks g)) ∨
    (¬ Holds M fo.settle.faultT ∧ ∃ g ∈ invariantTargets fo.invariants fo.checks, g.covers f = true ∧
      ∃ mach rule, g = .invariant mach rule ∧ Holds M (fo.broken mach rule)) := by
  obtain ⟨hF, hm⟩ := hf
  cases hfo : fo.settle.fault? M with
  | some f' =>
    rw [hfo] at hm
    simp only at hm
    subst hm
    cases ho
    exact .inl (settle_breaks _ hfo)
  | none =>
    rw [hfo] at hm hF
    refine .inr ⟨by simp [Holds, hF, Val.toBool], ?_⟩
    simp only at hm
    split at hm
    · rename_i n rest hl
      subst hm
      cases ho
      have hmem : n ∈ brokenIn M fo.invariants ++ checksBroken L T M v.machines fo.checks := by rw [hl]; simp
      rcases List.mem_append.1 hmem with h | h
      · obtain ⟨g, hg, hmemg, hb⟩ := brokenT_of_mem h
        refine ⟨.invariant none g, List.mem_append_left _ (List.mem_map_of_mem hmemg), ?_, none, g, rfl, hb⟩
        rcases hg with rfl | rfl <;> simp [Target.covers]
      · obtain ⟨mc, hmc, g, hg, hmemg, hb⟩ := instBrokenT_of_mem v.machines fo.checks h
        refine ⟨.invariant (some mc.1.name) g,
          List.mem_append_right _ (List.mem_flatMap.2 ⟨mc, hmc, List.mem_map_of_mem hmemg⟩), ?_, some mc.1.name, g, rfl, ?_⟩
        · rcases hg with rfl | rfl <;> simp [Target.covers]
        · refine instBrokenT_mono (fun c hc => ?_) hb
          simp only [machineChecks, List.mem_flatMap]
          exact ⟨mc, hmc, by simp [hc]⟩
    · obtain ⟨_, _, _, _, _, hr, -⟩ := hm
      rw [hr] at ho
      exact absurd ho hacc

theorem breaks_of_finished {o : StepOut v} {cmd : Option String} {fo : FinishOut v} (hfo : o.finish? = some fo)
    (hreach : Holds M o.reached) {shs : List (PendingShape v.event)} {s0 : State v} {a : Step.Acc v} {res : Result v}
    {f : Fault} (hf : Finished M L T shs fo s0 a .accepted res) (ho : res.outcome = .fault f) :
    ∃ g ∈ o.targets cmd, g.covers f = true ∧ Holds M (o.breaks cmd g) := by
  rcases finished_faults hf ho (by simp) with ⟨g, hg, hcov, hb⟩ | ⟨hF, g, hg, hcov, mach, rule, rfl, hb⟩
  · refine ⟨g, by simp [StepOut.targets, hfo, hg], hcov, ?_⟩
    have hs : Holds M (anyT (o.topBreaks cmd g ++ [andT o.reached (fo.settle.breaks g)])) :=
      (holds_anyT _).2 ⟨_, List.mem_append_right _ (List.mem_singleton_self _), (holds_andT _ _).2 ⟨hreach, hb⟩⟩
    cases g with
    | invariant m r => exact absurd rfl (settle_targets_ne hg m r)
    | _ => simpa only [StepOut.breaks, hfo] using hs
  · refine ⟨_, by simp [StepOut.targets, StepOut.invTargets, hfo, hg], hcov, ?_⟩
    simp only [StepOut.breaks, hfo]
    exact (holds_andT _ _).2 ⟨hreach, (holds_andT _ _).2 ⟨(holds_not _).2 hF, hb⟩⟩

/-- Where a step's terms say what its result is and the result faults with `f`, other than an answer naming no
request, the step breaks one of its targets that `f` falls under. `cmd` is the command the input names. -/
theorem rel_faults {shs : List (PendingShape v.event)} {s : State v} {o : StepOut v} {x : Input v} {res : Result v}
    {f : Fault} {cmd : Option String} (hcmd : ∀ i c y, x = .command i c y → cmd = some (v.commands.get i).name)
    (hrel : o.Rel M L T shs s x res) (ho : res.outcome = .fault f) (hf : f ≠ .answerUnmatched) :
    ∃ g ∈ o.targets cmd, g.covers f = true ∧ Holds M (o.breaks cmd g) := by
  cases o with
  | command co =>
    cases x with
    | command i caller input =>
      have hc := hcmd i caller input rfl
      simp only [StepOut.Rel] at hrel
      split at hrel
      · rename_i hcall
        split at hrel
        · subst hrel; cases ho
        · rename_i hrules
          split at hrel
          · rename_i hok
            split at hrel
            · rename_i n rest hens
              subst hrel; cases ho
              obtain ⟨g, hg, hmem, hb⟩ := brokenT_of_mem (M := M) (r := n) (by rw [hens]; simp)
              refine ⟨.ensures (v.commands.get i).name g, by simp [StepOut.targets, StepOut.topTargets, hc, hmem],
                by rcases hg with rfl | rfl <;> simp [Target.covers], ?_⟩
              simp only [StepOut.breaks, StepOut.topBreaks, hc, ite_true]
              exact (holds_anyT _).2 ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
                (holds_andT _ _).2 ⟨hcall, (holds_andT _ _).2 ⟨(holds_allT_rules _).2 hrules,
                  (holds_andT _ _).2 ⟨hok, hb⟩⟩⟩⟩
            · rename_i hens
              refine breaks_of_finished rfl ?_ hrel ho
              simp only [StepOut.reached]
              exact (holds_andT _ _).2 ⟨hcall, (holds_andT _ _).2 ⟨(holds_allT_rules _).2 hrules,
                (holds_andT _ _).2 ⟨hok, (holds_allT_rules _).2 hens⟩⟩⟩
          · obtain ⟨-, j, hj, -⟩ := hrel
            rw [hj] at ho; cases ho
      · subst hrel; cases ho
    | _ => cases hrel
  | query qo =>
    cases x with
    | query i caller input =>
      obtain ⟨-, hq⟩ := hrel
      rw [ho] at hq
      cases hq
    | _ => cases hrel
  | answer ao =>
    cases x with
    | answer to value =>
      simp only [StepOut.Rel] at hrel
      split at hrel
      · subst hrel; cases ho
      · rename_i hrules
        exact breaks_of_finished rfl ((holds_allT_rules _).2 hrules) hrel ho
    | _ => cases hrel
  | unmatched u =>
    cases x with
    | answer to value => simp only [StepOut.Rel] at hrel; subst hrel; cases ho; exact absurd rfl hf
    | _ => cases hrel
  | event eo =>
    cases x with
    | event i value => exact breaks_of_finished rfl holds_tt hrel ho
    | _ => cases hrel
  | clock co =>
    cases x with
    | clock time =>
      simp only [StepOut.Rel] at hrel
      split at hrel
      · rename_i hfw
        split at hrel
        · rename_i hover
          subst hrel; cases ho
          refine ⟨.cascade, by simp [StepOut.targets, StepOut.topTargets], rfl, ?_⟩
          simp only [StepOut.breaks, StepOut.topBreaks]
          exact (holds_anyT _).2 ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
            (holds_andT _ _).2 ⟨hfw, by simpa [Holds] using hover⟩⟩
        · rename_i hover
          refine breaks_of_finished rfl ?_ hrel ho
          simp only [StepOut.reached]
          exact (holds_andT _ _).2 ⟨hfw, (holds_not _).2 (by simpa [Holds] using hover)⟩
      · subst hrel; cases ho
    | _ => cases hrel

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

theorem bound_holds {side held cond : Term} (h : ¬ Holds M (.or (.not side) (andT held (.not cond)))) :
    Holds M side ∧ (Holds M held → Holds M cond) := by
  rw [holds_or, holds_not, holds_andT, holds_not] at h
  exact ⟨Classical.byContradiction fun h' => h (.inl h'),
    fun hh => Classical.byContradiction fun h' => h (.inr ⟨hh, h'⟩)⟩

/-- A command input decodes from the symbolic input of its command. -/
theorem command?_of_decode {shs : List (PendingShape v.event)} {n : Nat} {hc : v.caller.isData = true}
    {inp : SymInput v shs n} {x : Input v} (hx : inp.decode M L hc = some x) :
    ∀ i c y, x = .command i c y → inp.command? = some (v.commands.get i).name := by
  intro i c y hxc
  subst hxc
  cases inp with
  | command i' sc si =>
    obtain ⟨_, _, h, -, -⟩ := decode_command hx
    cases h; rfl
  | query i' sc si => obtain ⟨_, _, h, -, -⟩ := decode_query hx; cases h
  | answer k j to w => obtain ⟨_, _, _, h, -, -⟩ := decode_answer hx; cases h
  | unmatched t to w => obtain ⟨_, _, _, h, -, -⟩ := decode_answer hx; cases h
  | event i' sv => obtain ⟨_, h, -⟩ := decode_event hx; cases h
  | clock st => obtain ⟨_, h, -⟩ := decode_clock hx; cases h

/-- T4 for one input kind, in one model: where the symbolic state and input decode to a state of the right shape
whose invariants hold and to an input of the kind, and the model satisfies the bound question of the kind or a
question about a target `f` falls under nowhere, the step does not fault with `f`. -/
theorem question_sound {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v)
    (senv : StepEnv L (shapes v)) (inp : SymInput v (shapes v) senv.nT)
    {gs : List Target} {qs : List (Question v (shapes v) senv.nT)} (hq : questions L T P v senv inp = .ok (gs, qs))
    {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    (hinv : Step.Inv P s) (hheld : Step.invariants s = [])
    {hc : v.caller.isData = true} {x : Input v} (hx : inp.decode M L hc = some x)
    (hcase : ∀ t, encodeStep L T P v senv (SymState.vars 0) inp = .ok t → Holds M t.out.case)
    (f : Fault) (hf : f ≠ .answerUnmatched)
    (hun : ∀ q ∈ qs, (q.target = none ∨ ∃ g, q.target = some g ∧ g.covers f = true) →
      ∃ a ∈ q.script.asserts, ¬ Holds M a) :
    (step T v s x).outcome ≠ .fault f := by
  intro hfault
  obtain ⟨t, ht, hq⟩ := bind_ok.1 hq
  obtain ⟨wf, hwf, hq⟩ := bind_ok.1 hq
  obtain ⟨below, hbelow, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨inv, ci0⟩, hinvc, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨rules, ci⟩, hrules, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨checks, ck⟩, hchecks, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, -, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have hR := decode_state hS
  have hwfH : Holds M wf := wf_of_decodeState (need_ok.1 hwf) hS
  have hbelowH : Holds M below := (pendingBelow_iff hR.pending hR.nextId hbelow).2 hinv.below
  have hcaseH := hcase t ht
  obtain ⟨a, ha, hna⟩ := hun _ (List.mem_cons_self ..) (.inl rfl)
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact hna hwfH
  · exact hna hbelowH
  · exact hna hcaseH
  obtain ⟨hside, hcondOf⟩ := bound_holds hna
  obtain ⟨hcodes, hsites, hci0, hci, hck⟩ : Holds M t.codes ∧ Holds M t.sites ∧ Holds M ci0 ∧ Holds M ci ∧ Holds M ck := by
    simpa only [holds_andT] using hside
  have hfd : (Ty.fn [v.records] Ty.rules).isData = true := by
    simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, v.records_data]
  have hb := invariants_rel v.invariants v.records_data hfd (v.invariants.code_fn hfd hinvc hci0) s.records hR.records
    hrules hci
  have hbs := (instChecks_encode s.records s.now hR.records hR.now v.machines _ s.machines hR.machines
    (fun m hm => (chk.keys m hm).2) hchecks).2 hck
  have hsplit : Step.invariants s = Step.broken (v.invariants.fn (s.records, ())) ++ instancesBroken s.records s.now s.machines := rfl
  rw [hsplit, List.append_eq_nil_iff] at hheld
  have hheldH : Holds M (andT (allT (rules.map (·.2))) (allT (checks.toList.map instHoldT))) :=
    (holds_andT _ _).2 ⟨(holds_allT_rules _).2 (hb.trans hheld.1), instHold_of_nil _ _ (hbs.trans hheld.2)⟩
  have hcond := hcondOf hheldH
  have hrel := ((step_encode chk senv hS hinv hx ht).2 hcodes hsites hcaseH).2.1 hcond
  obtain ⟨g, hg, hn, hbr⟩ := rel_faults (command?_of_decode hx) hrel hfault hf
  have hkeep : ((t.out.breaks inp.command? g).const?.map Val.toBool != some false) = true := by
    cases hk : (t.out.breaks inp.command? g).const? with
    | none => rfl
    | some w =>
      have hw := Term.const?_denote M _ hk
      simp only [Holds, hw] at hbr
      simp [hbr]
  obtain ⟨a, ha, hna⟩ := hun ⟨inp, some g, _⟩
    (List.mem_cons_of_mem _ (List.mem_map.2 ⟨g, List.mem_filter.2 ⟨mem_dedup hg, hkeep⟩, rfl⟩)) (.inr ⟨g, rfl, hn⟩)
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hna hwfH
  · exact hna hbelowH
  · exact hna hcaseH
  · exact hna hside
  · exact hna hheldH
  · exact hna hcond
  · exact hna hbr

end

section
variable (S : Ty → Nat) {v : ServiceV}

/-- Whether the codes of the functions a step on the input applies fit their slots: `codesFit` of its kind. -/
def inputCodesFit : Input v → Prop
  | .command i _ _ =>
    let x := v.commands.get i
    ((x.accepts.fits S).1 ∧ (x.decide.fits S).1 ∧ (x.ensures.fits S).1) ∧ (v.apply.fits S).1 ∧ (v.invariants.fits S).1
  | .query i _ _ => ((v.queries.get i).accepts.fits S).1 ∧ ((v.queries.get i).resolve.fits S).1
  | .answer .. => (v.apply.fits S).1 ∧ (v.invariants.fits S).1
  | .event i _ => (v.apply.fits S).1 ∧ ((v.subscribes.get i).wrap.fits S).1 ∧ (v.invariants.fits S).1
  | .clock _ => (v.apply.fits S).1 ∧ (v.invariants.fits S).1

end

/-- Whether the own kinds' codes fit where a step on the input runs a cascade: every kind's step but a query's. -/
def inputSitesFit (L : Layout) (P : List AnySite) {v : ServiceV} : Input v → Prop
  | .query .. => True
  | _ => SitesFit L P v

/-- Whether the step from `s` on `x` stays within the slots: the codes of what it applies, the cascade's own kinds'
codes (no query runs a cascade), the invariants at `s`, and what the step applies all fit. -/
def StepFits (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (s : State v) (x : Input v) : Prop :=
  inputCodesFit L.count x ∧ inputSitesFit L P x ∧
    (v.invariants.fits L.count).1 ∧ v.invariants.appFits L.count (s.records, ()) ∧
    instChecksFit L.count s.records s.now s.machines ∧ stepFits L.count T (shapes v) s x

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

theorem codesFit_of_decode {shs : List (PendingShape v.event)} {n : Nat} {hc : v.caller.isData = true}
    {inp : SymInput v shs n} {x : Input v} (hx : inp.decode M L hc = some x) (h : inputCodesFit L.count x) :
    codesFit L.count inp := by
  cases inp with
  | command => obtain ⟨_, _, rfl, -, -⟩ := decode_command hx; exact h
  | query => obtain ⟨_, _, rfl, -, -⟩ := decode_query hx; exact h
  | answer => obtain ⟨_, _, _, rfl, -, -⟩ := decode_answer hx; exact h
  | unmatched => trivial
  | event => obtain ⟨_, rfl, -⟩ := decode_event hx; exact h
  | clock => obtain ⟨_, rfl, -⟩ := decode_clock hx; exact h

theorem sites_of_decode {P : List AnySite} (senv : StepEnv L (shapes v)) {S : SymState v}
    {inp : SymInput v (shapes v) senv.nT} {t : EncodedStep v} (henc : encodeStep L T P v senv S inp = .ok t)
    {hc : v.caller.isData = true} {x : Input v} (hx : inp.decode M L hc = some x) (h : inputSitesFit L P x) :
    Holds M t.sites := by
  have hs := step_sites (M := M) senv S henc
  cases inp with
  | command => obtain ⟨_, _, rfl, -, -⟩ := decode_command hx; exact hs.2 h
  | query => exact hs.2 trivial
  | answer => obtain ⟨_, _, _, rfl, -, -⟩ := decode_answer hx; exact hs.2 h
  | unmatched => exact hs.2 trivial
  | event => obtain ⟨_, rfl, -⟩ := decode_event hx; exact hs.2 h
  | clock => obtain ⟨_, rfl, -⟩ := decode_clock hx; exact hs.2 h

/-- T4 for one input kind within the slots, in one model: where the symbolic state and input decode to a state of the
right shape whose invariants hold and to an input of the kind whose step stays within the slots, and the model
satisfies no question about a target `f` falls under, the step does not fault with `f`. No bound question is needed:
within the slots every side condition is exact, so it holds. -/
theorem question_within {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v)
    (senv : StepEnv L (shapes v)) (inp : SymInput v (shapes v) senv.nT)
    {gs : List Target} {qs : List (Question v (shapes v) senv.nT)} (hq : questions L T P v senv inp = .ok (gs, qs))
    {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    (hinv : Step.Inv P s) (hheld : Step.invariants s = [])
    {hc : v.caller.isData = true} {x : Input v} (hx : inp.decode M L hc = some x)
    (hcase : ∀ t, encodeStep L T P v senv (SymState.vars 0) inp = .ok t → Holds M t.out.case)
    (hfit : StepFits L T P v s x) (f : Fault) (hf : f ≠ .answerUnmatched)
    (hun : ∀ q ∈ qs, (∃ g, q.target = some g ∧ g.covers f = true) → ∃ a ∈ q.script.asserts, ¬ Holds M a) :
    (step T v s x).outcome ≠ .fault f := by
  intro hfault
  obtain ⟨hcf, hsf, hif, haf, hkf, hstf⟩ := hfit
  obtain ⟨t, ht, hq⟩ := bind_ok.1 hq
  obtain ⟨wf, hwf, hq⟩ := bind_ok.1 hq
  obtain ⟨below, hbelow, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨inv, ci0⟩, hinvc, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨rules, ci⟩, hrules, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨checks, ck⟩, hchecks, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, -, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have hR := decode_state hS
  have hwfH : Holds M wf := wf_of_decodeState (need_ok.1 hwf) hS
  have hbelowH : Holds M below := (pendingBelow_iff hR.pending hR.nextId hbelow).2 hinv.below
  have hcaseH := hcase t ht
  have henc := step_encode chk senv hS hinv hx ht
  have hcodes := henc.1.2 (codesFit_of_decode hx hcf)
  have hsites := sites_of_decode senv ht hx hsf
  have hci0 := (v.invariants.code_exact (M := M) hinvc).1.2 hif
  have hci := (invariants_exact v.invariants v.records_data hinvc hci0 s.records hR.records hrules).2 haf
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  have hbs := instChecks_encode s.records s.now hR.records hR.now v.machines _ s.machines hR.machines hord hchecks
  have hck := hbs.1.2 hkf
  have hside : Holds M (andT t.codes (andT t.sites (andT ci0 (andT ci ck)))) := by
    simp only [holds_andT]; exact ⟨hcodes, hsites, hci0, hci, hck⟩
  have hcond := ((henc.2 hcodes hsites hcaseH).1).2 hstf
  have hfd : (Ty.fn [v.records] Ty.rules).isData = true := by
    simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, v.records_data]
  have hb := invariants_rel v.invariants v.records_data hfd (v.invariants.code_fn hfd hinvc hci0) s.records hR.records
    hrules hci
  have hsplit : Step.invariants s = Step.broken (v.invariants.fn (s.records, ())) ++ instancesBroken s.records s.now s.machines := rfl
  rw [hsplit, List.append_eq_nil_iff] at hheld
  have hheldH : Holds M (andT (allT (rules.map (·.2))) (allT (checks.toList.map instHoldT))) :=
    (holds_andT _ _).2 ⟨(holds_allT_rules _).2 (hb.trans hheld.1), instHold_of_nil _ _ ((hbs.2 hck).trans hheld.2)⟩
  have hrel := ((henc.2 hcodes hsites hcaseH).2.1) hcond
  obtain ⟨g, hg, hn, hbr⟩ := rel_faults (command?_of_decode hx) hrel hfault hf
  have hkeep : ((t.out.breaks inp.command? g).const?.map Val.toBool != some false) = true := by
    cases hk : (t.out.breaks inp.command? g).const? with
    | none => rfl
    | some w =>
      have hw := Term.const?_denote M _ hk
      simp only [Holds, hw] at hbr
      simp [hbr]
  obtain ⟨a, ha, hna⟩ := hun ⟨inp, some g, _⟩
    (List.mem_cons_of_mem _ (List.mem_map.2 ⟨g, List.mem_filter.2 ⟨mem_dedup hg, hkeep⟩, rfl⟩)) ⟨g, rfl, hn⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hna hwfH
  · exact hna hbelowH
  · exact hna hcaseH
  · exact hna hside
  · exact hna hheldH
  · exact hna hcond
  · exact hna hbr

/-- The questions about the input kind `inp` cover the step from `s` on `x`: some model whose variables hold values of
their sorts holds the state and the input, in the case the questions ask about. A state and an input within the slots
are some model's (`decode_reachable`, T3). -/
def Covered (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))
    (inp : SymInput v (shapes v) senv.nT) (s : State v) (x : Input v) : Prop :=
  ∃ (hc : v.caller.isData = true) (M : Model),
    (∀ j (h : j < (stateTys v (shapes v) ++ inp.tys).length), Sorted L (stateTys v (shapes v) ++ inp.tys)[j] (M.vars j)) ∧
    (SymState.vars 0).decode M L T (shapes v) = some s ∧ inp.decode M L hc = some x ∧
    ∀ t, encodeStep L T P v senv (SymState.vars 0) inp = .ok t → Holds M t.out.case

/-- T4 at the states and inputs the questions cover: where the solver answers unsat to an input kind's bound
question and to its questions about the targets the fault `f` falls under, no step of a run from an initial state
whose invariants hold faults with `f` at a state and input those questions cover. The proved invariants are assumed of
the state before each step, which is sound because every state such a run reaches has them (`run_invariants`: a step
that breaks one leaves the state it began with). -/
theorem verdict_covered {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v))
    (f : Fault) (hf : f ≠ .answerUnmatched) (hinit : Step.invariants (Step.State.init v) = [])
    (inp : SymInput v (shapes v) senv.nT) {gs : List Target} {qs : List (Question v (shapes v) senv.nT)}
    (hq : questions L T P v senv inp = .ok (gs, qs))
    (hun : ∀ q ∈ qs, (q.target = none ∨ ∃ g, q.target = some g ∧ g.covers f = true) →
      Unsat L (stateTys v (shapes v) ++ inp.tys) q.script)
    (is : List (Input v)) (x : Input v) (hcov : Covered L T P v senv inp (run T v (Step.State.init v) is).1 x) :
    (step T v (run T v (Step.State.init v) is).1 x).outcome ≠ .fault f := by
  obtain ⟨hc, M, hM, hS, hx, hcase⟩ := hcov
  exact question_sound chk senv inp hq hS (run_inv T chk.reach _ Step.init_inv is)
    (Tazuna.Ir.run_invariants T _ is hinit) hx hcase f hf fun q hq' hrel => (hun q hq' hrel).noModel M fun n h => varSorted_of_sorted (hM n h)

end

end Tazuna.Smt
