import Tazuna.Smt.InternalStep

/-! The internal step for whichever own effect a queue place holds: `Step.runOwn` picks the service's command or query
by the effect's name and types, and the encoder makes the same choice per own kind, statically (`ownShape`), with the
program's site of the kind's `on_answer`. Each kind's internal step is encoded from the effect term's fields, and the
kinds are merged by the variant test of the effect term: exactly one kind's test holds for an own effect, so the
merged terms denote that kind's (precedent: the pending entry, whose shape the encoder fixes per kind). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- What an own kind runs, fixed from its name and types: the service's command or query with the program's site of
its `on_answer`; nothing the service lists, which `Step.runOwn` makes `Fault.invalidEffect`; or a listed one whose
`on_answer` site `P` lacks, which no effect that reaches `P` has (`siteFor_reach`). -/
inductive OwnShape (v : ServiceV) where
  | command (x : CommandV v.records v.event v.caller) (Γ : List Ty)
      (site : Site Γ (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event)))
  | query (x : QueryV v.records v.caller) (Γ : List Ty) (site : Site Γ (Ty.fn [x.output] (.list v.event)))
  | unlisted (name : String)
  | unreached (name : String)

/-- The site of `P` of the type `t` that a kept function's code names. -/
def siteFor (P : List AnySite) (t : Ty) (k : SiteKey) : Option ((Γ : List Ty) × Site Γ t) :=
  (sitesOf P t).find? fun s => siteMatch s.2 k

/-- The shape of an own kind: the command or query `Step.runOwn` runs for its effects, and the site of `P` its
`on_answer` is written at. A layout may list kinds the program never builds. -/
def ownShape (v : ServiceV) (P : List AnySite) : OwnKey → OwnShape v
  | .command _ name c i j a =>
    match Ty.same c v.caller, Step.ownCommand (v := v) name i j with
    | some _, some ⟨x, _, _⟩ =>
      match siteFor P (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event)) a with
      | some gs => .command x gs.1 gs.2
      | none => .unreached name
    | _, _ => .unlisted name
  | .query _ name c i o a =>
    match Ty.same c v.caller, Step.ownQuery (v := v) name i o with
    | some _, some ⟨x, _, _⟩ =>
      match siteFor P (Ty.fn [x.output] (.list v.event)) a with
      | some gs => .query x gs.1 gs.2
      | none => .unreached name
    | _, _ => .unlisted name

/-- The outcome terms of one own kind's internal step. -/
inductive OwnKindOut (v : ServiceV) where
  | command (name : String) (o : OwnCommandOut v)
  | query (name : String) (o : OwnQueryOut v)
  | missing (name : String)

/-- The fault the outcome terms name in the model, or none when the internal step runs to its end. -/
def OwnKindOut.fault? {v : ServiceV} (M : Model) : OwnKindOut v → Option Fault
  | .command name o =>
    if (o.callerOk.denote M).toBool then
      match brokenIn M o.rules with
      | n :: ns => some (.invalidEffect name (n :: ns))
      | [] =>
        match (o.decided.ok.denote M).toBool, brokenIn M o.decided.ensures with
        | true, n :: _ => some (.ensures n)
        | _, _ => none
    else some (.invalidEffect name ["callers"])
  | .query name o =>
    if (o.callerOk.denote M).toBool then
      match brokenIn M o.rules with
      | n :: ns => some (.invalidEffect name (n :: ns))
      | [] => none
    else some (.invalidEffect name ["callers"])
  | .missing name => some (.invalidEffect name ["service"])

/-- What an internal step leaves: whether it faults, the events loop's terms after it (any terms on a fault), with
the news and own slots of every loop it ran, and the fresh counter. -/
structure StepTerms (v : ServiceV) where
  fault : Term
  done : EventsOut v
  fresh : Term

/-- One own kind's internal step: its outcome terms and what it leaves. -/
structure OwnKindStep (v : ServiceV) where
  kind : OwnKindOut v
  terms : StepTerms v

/-- The terms of `a` where `c` holds and of `b` elsewhere; the slots of `a` count only where `c` holds. -/
def pickTerms {v : ServiceV} (c : Term) (a b : StepTerms v) : StepTerms v :=
  let p (x y : Term) := Term.share (.ite c x y)
  ⟨p a.fault b.fault,
    ⟨p a.done.records b.done.records, PerMachine.zipWith p a.done.tables b.done.tables,
      p a.done.nextId b.done.nextId, gatePending c a.done.news ++ b.done.news, gateOwns c a.done.owns ++ b.done.owns,
      p a.done.queued b.done.queued⟩,
    p a.fresh b.fresh⟩

/-- The terms of an own effect's internal step: each own kind's variant test with its outcome terms, and the merged
terms. -/
structure OwnStepOut (v : ServiceV) where
  kinds : List (Term × OwnKindOut v)
  terms : StepTerms v

/-- The fault the model's kind names: the outcome terms of the kind whose test holds. -/
def OwnStepOut.fault? {v : ServiceV} (M : Model) (o : OwnStepOut v) : Option Fault :=
  (o.kinds.find? fun k => (k.1.denote M).toBool).bind fun k => k.2.fault? M

section
variable (L : Layout) (T : List TypeDecl)

/-- One own kind's internal step for the effect term `eff`, read as the kind's variant `nR + j`: its outcome and step
terms, its condition, and the condition of the command's or query's codes. -/
def encodeOwnKind (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs) (nR : Nat)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (records now fresh n q eff : Term) (xs : PerMachine (fun _ => Term) v.machines)
    (j : Nat) (key : OwnKey) : Except Refusal (Encoded (OwnKindStep v)) := do
  let sel (i : Nat) := Term.sel senv.dE (nR + j) i eff
  match ownShape v P key with
  -- An unreached kind's terms are never read, so it takes the unlisted kind's constant terms.
  | .unlisted name | .unreached name => pure ⟨⟨.missing name, ⟨tt, ⟨records, xs, n, [], [], q⟩, fresh⟩⟩, tt, tt⟩
  | .command x Γ site =>
    let (cc, cx) ← CommandCode.of L x
    let ks ← need (lacks v.caller) (callerTerms L x.data.caller x.callers)
    let (da, _) ← L.findE (.tuple Γ)
    let σ ← need (.limit (.function (.tuple Γ))) (tupleCodes da Γ (sel 2) 0)
    let (o, c) ← encodeOwnCommand L T v shs senv x cc site σ apply ks records now fresh n q (sel 0) (sel 1) xs
    let fault := Term.or (.not o.callerOk)
      (.or (.not (allT (o.rules.map (·.2)))) (.and o.decided.ok (.not (allT (o.decided.ensures.map (·.2))))))
    pure ⟨⟨.command x.name o,
      ⟨fault, o.done, .add fresh (.int 1)⟩⟩, c, cx⟩
  | .query x Γ site =>
    let (qc, cq) ← QueryCode.of L x
    let ks ← need (lacks v.caller) (callerTerms L x.data.caller x.callers)
    let (da, _) ← L.findE (.tuple Γ)
    let σ ← need (.limit (.function (.tuple Γ))) (tupleCodes da Γ (sel 2) 0)
    let (o, c) ← encodeOwnQuery L T v shs senv x qc site σ apply ks records now fresh n q (sel 0) (sel 1) xs
    pure ⟨⟨.query x.name o, ⟨.or (.not o.callerOk) (.not (allT (o.rules.map (·.2)))), o.answered, fresh⟩⟩, c, cq⟩

/-- The internal step for the own effect term `eff`: every own kind's, merged by the variant tests; its condition
asks each kind's only where its test holds. The second term is the codes' condition, which holds statically. -/
def encodeOwnStep (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (records now fresh n q eff : Term) (xs : PerMachine (fun _ => Term) v.machines) :
    Except Refusal (Encoded (OwnStepOut v)) := do
  let nR := (L.effectsOf v.event).length
  let eff := Term.share eff
  let ks ← (L.ownsOf v.event).zipIdx.mapM fun (key, j) => do
    pure (Term.share (.is senv.dE (nR + j) eff), ← encodeOwnKind L T P v shs senv nR apply records now fresh n q eff xs j key)
  let base : StepTerms v := ⟨tt, ⟨records, xs, n, [], [], q⟩, fresh⟩
  pure ⟨⟨ks.map fun k => (k.1, k.2.out.kind), ks.foldr (fun k t => pickTerms k.1 k.2.out.terms t) base⟩,
    allT (ks.map fun k => .ite k.1 k.2.cond tt), allT (ks.map (·.2.codes))⟩

end

/-! What fits for an own effect's internal step, in `Step.runOwn`'s terms. -/

section
variable {v : ServiceV}

/-- Whether an own command's internal step fits from `s`: what `ownCommand_encode` says its condition holds for. -/
def ownCommandFits (S : Ty → Nat) (T : List TypeDecl) (s : State v) (x : CommandV v.records v.event v.caller)
    (caller : v.caller.den0) (input : x.input.den0)
    (oa : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) : Prop :=
  let ctx := Step.ctx s s.records caller input
  x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
    x.accepts.appFits S (input, ()) ∧
    (Step.broken (x.accepts.fn (input, ())) = [] →
      x.decide.appFits S (ctx, ()) ∧ ownDecidedFits S T { s with fresh := s.fresh + 1 } x ctx oa (x.decide.fn (ctx, ())))

/-- Whether an own query's internal step fits from `s`: what `ownQuery_encode` says its condition holds for. -/
def ownQueryFits (S : Ty → Nat) (T : List TypeDecl) (s : State v) (x : QueryV v.records v.caller)
    (caller : v.caller.den0) (input : x.input.den0) (oa : Fun (Ty.fn [x.output] (.list v.event))) : Prop :=
  let ctx := Step.ctx s s.records caller input
  x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
    x.accepts.appFits S (input, ()) ∧
    (Step.broken (x.accepts.fn (input, ())) = [] →
      x.resolve.appFits S (ctx, ()) ∧ (oa.fits S).1 ∧ oa.appFits S ⟨x.resolve.fn (ctx, ()), ()⟩ ∧
        eventsFit S T s (oa.fn ⟨x.resolve.fn (ctx, ()), ()⟩))

/-- Whether an own effect's internal step fits from `s`, for the command or query `Step.runOwn` runs. -/
def ownFits (S : Ty → Nat) (T : List TypeDecl) (s : State v) : EffectV v.event → Prop
  | .request _ => True
  | .command name c i j caller value onAnswer =>
    match Ty.same c v.caller, Step.ownCommand (v := v) name i j with
    | some ⟨hc⟩, some ⟨x, hi, hj⟩ =>
      ownCommandFits S T s x (cast (congrArg Ty.den0 hc) caller) (cast (congrArg Ty.den0 hi) value) (hj ▸ onAnswer)
    | _, _ => True
  | .query name c i o caller value onAnswer =>
    match Ty.same c v.caller, Step.ownQuery (v := v) name i o with
    | some ⟨hc⟩, some ⟨x, hi, ho⟩ =>
      ownQueryFits S T s x (cast (congrArg Ty.den0 hc) caller) (cast (congrArg Ty.den0 hi) value) (ho ▸ onAnswer)
    | _, _ => True

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- A function that reaches `P` is found at its own site and captures' types: a kind of an effect that reaches `P`
always has its site. -/
theorem siteFor_reach {P : List AnySite} {t : Ty} {k : SiteKey} {f : Fun t} (hP : f.asSite ∈ P)
    (hs : f.site = k.site) (hΓ : f.Γ = k.Γ) : siteFor P t k ≠ none := by
  intro h
  have := List.find?_eq_none.1 h _ (mem_sitesOf_self hP)
  simp only [siteMatch, Fun.toSite, hs, beq_self_eq_true, Bool.true_and] at this
  exact this (hΓ ▸ Ty_sames_self _)

theorem siteFor_spec {P : List AnySite} {t : Ty} {k : SiteKey} {Γ : List Ty} {s : Site Γ t}
    (h : siteFor P t k = some ⟨Γ, s⟩) : (⟨Γ, t, s⟩ : AnySite) ∈ P ∧ s.site = k.site ∧ Γ = k.Γ := by
  have hm := List.mem_of_find?_eq_some h
  have hs := List.find?_some h
  simp only [siteMatch, Bool.and_eq_true, beq_iff_eq] at hs
  exact ⟨mem_sitesOf hm, hs.1, eq_of_sames hs.2⟩

theorem ownCommand_mem {name : String} {i j : Ty} {x : CommandV v.records v.event v.caller}
    {h : i = x.input ∧ j = x.rejection} (hx : Step.ownCommand (v := v) name i j = some ⟨x, h⟩) : x ∈ v.commands := by
  obtain ⟨y, hy, hf⟩ := List.exists_of_findSome?_eq_some hx
  split at hf
  · split at hf
    · cases hf; exact hy
    · cases hf
  · cases hf

theorem ownQuery_mem {name : String} {i o : Ty} {x : QueryV v.records v.caller}
    {h : i = x.input ∧ o = x.output} (hx : Step.ownQuery (v := v) name i o = some ⟨x, h⟩) : x ∈ v.queries := by
  obtain ⟨y, hy, hf⟩ := List.exists_of_findSome?_eq_some hx
  split at hf
  · split at hf
    · cases hf; exact hy
    · cases hf
  · cases hf

theorem fault_command (name : String) (o : OwnCommandOut v) :
    Term.denote M (.or (.not o.callerOk) (.or (.not (allT (o.rules.map (·.2))))
      (.and o.decided.ok (.not (allT (o.decided.ensures.map (·.2))))))) = .bool ((OwnKindOut.command name o).fault? M).isSome := by
  simp only [Term.denote, allT_rules, OwnKindOut.fault?, toBool_bool]
  cases (o.callerOk.denote M).toBool
  · rfl
  · cases brokenIn M o.rules with
    | cons n ns => rfl
    | nil => cases (o.decided.ok.denote M).toBool <;> cases brokenIn M o.decided.ensures <;> rfl

theorem fault_query (name : String) (o : OwnQueryOut v) :
    Term.denote M (.or (.not o.callerOk) (.not (allT (o.rules.map (·.2))))) =
      .bool ((OwnKindOut.query name o).fault? M).isSome := by
  simp only [Term.denote, allT_rules, OwnKindOut.fault?, toBool_bool]
  cases (o.callerOk.denote M).toBool
  · rfl
  · cases brokenIn M o.rules <;> rfl

/-- One own kind's internal step, for an own effect of the kind: where the codes' condition holds, the condition
holds exactly when the internal step `Step.runOwn` runs fits (`ownFits`); wherever it holds, the fault term holds
exactly when the outcome terms name a fault, which is `Step.runOwn`'s, and otherwise the internal step runs to its end
with what the step terms denote (`AccRel`). -/
theorem ownKind_encode {P : List AnySite} (chk : Checked P T v)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (a : Step.Acc v)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    (senv : StepEnv L shs)
    {records now fresh n q eff : Term} {xs : PerMachine (fun _ => Term) v.machines} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ v.records_data a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    {j : Nat} {key : OwnKey} (x : EffectV v.event) (hreach : x.Reach P) {vals : List Val}
    (heff : eff.denote M = .ctor senv.dE ((L.effectsOf v.event).length + j) vals) (hkey : key.Holds L x vals)
    {ko : OwnKindOut v} {st : StepTerms v} {c cx : Term}
    (henc : encodeOwnKind L T P v shs senv (L.effectsOf v.event).length apply records now fresh n q eff xs j key =
      .ok ⟨⟨ko, st⟩, c, cx⟩)
    (hcx : Holds M cx) :
    (Holds M c ↔ ownFits L.count T a.state x) ∧
    (Holds M c → st.fault.denote M = .bool (ko.fault? M).isSome ∧
      match ko.fault? M with
      | some f => Step.runOwn T a x = .error f
      | none => AccRel M L T shs a st.done st.fresh q0 (Step.runOwn T a x)) := by
  have hsel : ∀ i, (Term.sel senv.dE ((L.effectsOf v.event).length + j) i eff).denote M = vals[i]?.getD default :=
    fun i => sel_ctor i heff
  unfold encodeOwnKind at henc
  generalize hsh : ownShape v P key = sh at henc
  cases key with
  | command e name c0 i jj a0 =>
    cases x with
    | request => exact hkey.elim
    | query => exact hkey.elim
    | command name' c' i' j' caller value onAnswer =>
    obtain ⟨rfl, rfl, rfl, rfl, hsite, hΓ, vc, vi, va, rfl, hvc, hvi, hva⟩ := hkey
    unfold ownShape at hsh
    unfold Step.runOwn ownFits
    dsimp only at hsh ⊢
    revert hsh
    generalize hoc : Ty.same c' v.caller = oc
    generalize hox : Step.ownCommand (v := v) name' i' j' = ox
    intro hsh
    have miss : ∀ (h : sh = .unlisted name'), Holds M c ∧ Term.denote M st.fault = .bool (ko.fault? M).isSome ∧
        ko.fault? M = some (.invalidEffect name' ["service"]) := by
      intro h; subst h; cases pure_ok.1 henc; exact ⟨holds_tt, rfl, rfl⟩
    cases oc with
    | none =>
      cases ox <;>
      · dsimp only at hsh ⊢
        obtain ⟨h0, h1, h2⟩ := miss hsh.symm
        exact ⟨iff_of_true h0 trivial, fun _ => by rw [h2]; exact ⟨h1.trans (by rw [h2]), rfl⟩⟩
    | some hc =>
    cases ox with
    | none =>
      dsimp only at hsh ⊢
      obtain ⟨h0, h1, h2⟩ := miss hsh.symm
      exact ⟨iff_of_true h0 trivial, fun _ => by rw [h2]; exact ⟨h1.trans (by rw [h2]), rfl⟩⟩
    | some xx =>
    obtain ⟨hc⟩ := hc
    obtain ⟨x, hi, hj⟩ := xx
    subst hc hi hj
    dsimp only at hsh ⊢
    revert hsh
    generalize hsf : siteFor P _ a0 = sf
    intro hsh
    cases sf with
    | none => exact absurd hsf (siteFor_reach hreach hsite hΓ)
    | some gs =>
    obtain ⟨Γ, s⟩ := gs
    subst hsh
    obtain ⟨⟨cc, cx'⟩, hcc, henc⟩ := bind_ok.1 henc
    obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨da, dn⟩, hda, henc⟩ := bind_ok.1 henc
    obtain ⟨σ, hσ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c'⟩, hoe, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have hd := CommandV.data x
    obtain ⟨hsP, hss, hsΓ⟩ := siteFor_spec hsf
    obtain ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ := onAnswer
    dsimp only at hsite hΓ
    obtain ⟨e, hA⟩ := Fun.eq_siteFn chk.sites ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ s hreach hsP (hsite.trans hss.symm)
    dsimp only at e hA
    subst e
    obtain ⟨d', n', vals', hd', rfl, hrds⟩ := hva
    obtain rfl := find_det hd' (need_ok.1 hda)
    have hσ' : Rels M L _ (Ty.up _ s.hΓ oenv) σ :=
      tupleCodes_rels _ [] vals' _ σ (by rw [hsel]; rfl) (relDs_up _ s.hΓ oenv vals' hrds) (need_ok.1 hσ)
    have hks' : callerTerms L hd.caller x.callers = some ks := need_ok.1 hks
    have hsc : RelV L v.caller (Ty.up _ hd.caller caller)
        ((Term.sel senv.dE ((L.effectsOf v.event).length + j) 0 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvc
    have hsi : RelV L x.input (Ty.up _ hd.input value)
        ((Term.sel senv.dE ((L.effectsOf v.event).length + j) 1 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvi
    have E := ownCommand_encode chk hshs a x caller value hcc hcx happ hca s oenv hσ'
      (tupleCodes_notFn _ _ _ (need_ok.1 hσ)) hks' senv hrec hnow hfresh hn hq hms hsc hsi hoe
    simp only [cast_eq]
    rw [show (⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ : Fun _) = s.fn oenv from hA]
    refine ⟨E.1, fun hc => ?_⟩
    have H := E.2 hc
    refine ⟨fault_command x.name o, ?_⟩
    simp only [OwnKindOut.fault?]
    split at H
    · rename_i hco
      simp only [hco, ite_true]
      split at H
      · rename_i n ns hb
        simp only [hb]
        exact H
      · rename_i hb
        simp only [hb]
        split at H
        · rename_i n ns hok hb'
          simp only [hok, hb']
          exact H
        · rename_i hne
          have hnone : (match (o.decided.ok.denote M).toBool, brokenIn M o.decided.ensures with
              | true, n :: _ => some (Fault.ensures n)
              | _, _ => none) = none := by
            split
            · rename_i n ns hok hb'; exact (hne n ns hok hb').elim
            · rfl
          rw [hnone]
          exact H
    · rename_i hco
      simp only [hco, Bool.false_eq_true, ite_false]
      exact H
  | query e name c0 i o a0 =>
    cases x with
    | request => exact hkey.elim
    | command => exact hkey.elim
    | query name' c' i' j' caller value onAnswer =>
    obtain ⟨rfl, rfl, rfl, rfl, hsite, hΓ, vc, vi, va, rfl, hvc, hvi, hva⟩ := hkey
    unfold ownShape at hsh
    unfold Step.runOwn ownFits
    dsimp only at hsh ⊢
    revert hsh
    generalize hoc : Ty.same c' v.caller = oc
    generalize hox : Step.ownQuery (v := v) name' i' j' = ox
    intro hsh
    have miss : ∀ (h : sh = .unlisted name'), Holds M c ∧ Term.denote M st.fault = .bool (ko.fault? M).isSome ∧
        ko.fault? M = some (.invalidEffect name' ["service"]) := by
      intro h; subst h; cases pure_ok.1 henc; exact ⟨holds_tt, rfl, rfl⟩
    cases oc with
    | none =>
      cases ox <;>
      · dsimp only at hsh ⊢
        obtain ⟨h0, h1, h2⟩ := miss hsh.symm
        exact ⟨iff_of_true h0 trivial, fun _ => by rw [h2]; exact ⟨h1.trans (by rw [h2]), rfl⟩⟩
    | some hc =>
    cases ox with
    | none =>
      dsimp only at hsh ⊢
      obtain ⟨h0, h1, h2⟩ := miss hsh.symm
      exact ⟨iff_of_true h0 trivial, fun _ => by rw [h2]; exact ⟨h1.trans (by rw [h2]), rfl⟩⟩
    | some xx =>
    obtain ⟨hc⟩ := hc
    obtain ⟨x, hi, hj⟩ := xx
    subst hc hi hj
    dsimp only at hsh ⊢
    revert hsh
    generalize hsf : siteFor P _ a0 = sf
    intro hsh
    cases sf with
    | none => exact absurd hsf (siteFor_reach hreach hsite hΓ)
    | some gs =>
    obtain ⟨Γ, s⟩ := gs
    subst hsh
    obtain ⟨⟨qc, cx'⟩, hqc, henc⟩ := bind_ok.1 henc
    obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨da, dn⟩, hda, henc⟩ := bind_ok.1 henc
    obtain ⟨σ, hσ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c'⟩, hoe, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have hd := QueryV.data x
    obtain ⟨hsP, hss, hsΓ⟩ := siteFor_spec hsf
    obtain ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ := onAnswer
    dsimp only at hsite hΓ
    obtain ⟨e, hA⟩ := Fun.eq_siteFn chk.sites ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ s hreach hsP (hsite.trans hss.symm)
    dsimp only at e hA
    subst e
    obtain ⟨d', n', vals', hd', rfl, hrds⟩ := hva
    obtain rfl := find_det hd' (need_ok.1 hda)
    have hσ' : Rels M L _ (Ty.up _ s.hΓ oenv) σ :=
      tupleCodes_rels _ [] vals' _ σ (by rw [hsel]; rfl) (relDs_up _ s.hΓ oenv vals' hrds) (need_ok.1 hσ)
    have hks' : callerTerms L hd.caller x.callers = some ks := need_ok.1 hks
    have hsc : RelV L v.caller (Ty.up _ hd.caller caller)
        ((Term.sel senv.dE ((L.effectsOf v.event).length + j) 0 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvc
    have hsi : RelV L x.input (Ty.up _ hd.input value)
        ((Term.sel senv.dE ((L.effectsOf v.event).length + j) 1 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvi
    have E := ownQuery_encode chk hshs a x caller value hqc hcx happ hca s oenv hσ'
      (tupleCodes_notFn _ _ _ (need_ok.1 hσ)) (chk.outputs x (ownQuery_mem hox)) hks' senv
      hrec hnow hfresh hn hq hms hsc hsi hoe
    simp only [cast_eq]
    rw [show (⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ : Fun _) = s.fn oenv from hA]
    refine ⟨E.1, fun hc => ?_⟩
    have H := E.2 hc
    refine ⟨fault_query x.name o, ?_⟩
    simp only [OwnKindOut.fault?]
    split at H
    · rename_i hco
      simp only [hco, ite_true]
      split at H
      · rename_i n ns hb
        simp only [hb]
        exact H
      · rename_i hb
        simp only [hb]
        exact H
    · rename_i hco
      simp only [hco, Bool.false_eq_true, ite_false]
      exact H

theorem machinesRel_congr : (ms : List (MachineV v.records v.event)) → (xs ys : PerMachine (fun _ => Term) ms) →
    (sms : Step.Machines ms) → Term.denotes M xs.toList = Term.denotes M ys.toList →
    MachinesRel M L T ms xs sms → MachinesRel M L T ms ys sms
  | [], .nil, .nil, .nil, _, h => h
  | _ :: ms, .cons _ xs, .cons _ ys, .cons _ sms, he, h => by
    obtain ⟨⟨tbl, ht, hs⟩, h⟩ := h
    simp only [PerMachine.toList_cons, Term.denotes, List.cons.injEq] at he
    exact ⟨⟨tbl, he.1 ▸ ht, hs⟩, machinesRel_congr ms xs ys sms he.2 h⟩

/-- Two step terms say the same in the model: the same values, and slots holding the same news and own effects. -/
structure Agrees (M : Model) (L : Layout) (e : Ty) (a b : StepTerms v) : Prop where
  fault : a.fault.denote M = b.fault.denote M
  fresh : a.fresh.denote M = b.fresh.denote M
  records : a.done.records.denote M = b.done.records.denote M
  nextId : a.done.nextId.denote M = b.done.nextId.denote M
  queued : a.done.queued.denote M = b.done.queued.denote M
  news : ∀ (shs : List (PendingShape e)) ds effs n0, NewsRel M L shs ds b.done.news effs n0 →
    NewsRel M L shs ds a.done.news effs n0
  owns : ∀ (os : List (EffectV e)) q0, OwnRel M L b.done.owns os q0 → OwnRel M L a.done.owns os q0

theorem AccRel.congr {a b : StepTerms v} (hab : Agrees M L v.event a b)
    (ht : Term.denotes M a.done.tables.toList = Term.denotes M b.done.tables.toList)
    {shs : List (PendingShape v.event)} {acc : Step.Acc v} {q0 : Nat}
    {r : Except Fault (Step.Acc v)} (h : AccRel M L T shs acc b.done b.fresh q0 r) :
    AccRel M L T shs acc a.done a.fresh q0 r := by
  obtain ⟨recs, ms, fr, evs, effs, os, hr, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨recs, ms, fr, evs, effs, os, hr, hab.records ▸ h1, machinesRel_congr _ _ _ _ ht.symm h2, hab.fresh ▸ h3,
    hab.nextId ▸ h4, hab.news _ _ _ _ h5, hab.queued ▸ h6, hab.owns _ _ h7⟩

theorem pick_tables {r e : Ty} {c : Term} {bc : Bool} (hc : c.denote M = .bool bc) : {ms : List (MachineV r e)} →
    (A B : PerMachine (fun _ => Term) ms) →
    Term.denotes M (PerMachine.zipWith (fun x y => Term.share (.ite c x y)) A B).toList =
      Term.denotes M (if bc then A else B).toList
  | _, .nil, .nil => by cases bc <;> rfl
  | _, .cons x A, .cons y B => by
    have ih := pick_tables hc A B
    cases bc <;> simp_all [PerMachine.zipWith, Term.denotes, Term.denote, toBool_bool]

theorem pick_tables_false {r e : Ty} {c : Term} (hc : c.denote M = .bool false) {ms : List (MachineV r e)}
    (A B : PerMachine (fun _ => Term) ms) :
    Term.denotes M (PerMachine.zipWith (fun x y => Term.share (.ite c x y)) A B).toList = Term.denotes M B.toList := by
  simpa using pick_tables hc A B

/-- The terms picked where the flag holds, over terms that write nothing, say of a run what the picked terms say. -/
theorem AccRel.pick {c : Term} (hc : c.denote M = .bool true) {o b : StepTerms v}
    (hb : b.done.news = [] ∧ b.done.owns = []) {shs : List (PendingShape v.event)} {acc : Step.Acc v} {q0 : Nat}
    {r : Except Fault (Step.Acc v)} (h : AccRel M L T shs acc o.done o.fresh q0 r) :
    AccRel M L T shs acc (pickTerms c o b).done (pickTerms c o b).fresh q0 r := by
  obtain ⟨recs, ms, fr, evs, effs, os, hr, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hp (x y : Term) : (Term.share (.ite c x y)).denote M = x.denote M := by simp [Term.denote, hc, toBool_bool]
  refine ⟨recs, ms, fr, evs, effs, os, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [pickTerms, hb.1, hb.2, hp]
  · exact h1
  · exact machinesRel_congr _ _ _ _ (pick_tables hc _ _).symm h2
  · exact h3
  · exact h4
  · simpa using newsRel_gate hc h5
  · exact h6
  · simpa using ownRel_gate hc h7

/-- Step terms of kinds whose tests all fail write no news and no own effect. -/
theorem fold_none {e : Ty} (base : StepTerms v) (hb : base.done.news = [] ∧ base.done.owns = []) :
    (ks : List (Term × StepTerms v)) → (∀ k ∈ ks, k.1.denote M = .bool false) →
    let t := ks.foldr (fun k t => pickTerms k.1 k.2 t) base
    t.fault.denote M = base.fault.denote M ∧ t.fresh.denote M = base.fresh.denote M ∧
      t.done.records.denote M = base.done.records.denote M ∧ t.done.nextId.denote M = base.done.nextId.denote M ∧
      t.done.queued.denote M = base.done.queued.denote M ∧
      Term.denotes M t.done.tables.toList = Term.denotes M base.done.tables.toList ∧
      (∀ (shs : List (PendingShape e)) ds n0, NewsRel M L shs ds t.done.news [] n0) ∧
      ∀ q0, OwnRel M L t.done.owns ([] : List (EffectV e)) q0
  | [], _ => by
    simp only [List.foldr_nil, hb, true_and]
    exact ⟨fun _ _ _ => ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩,
      fun q0 => ownRel_nil q0⟩
  | (c, a) :: ks, hf => by
    have hc : c.denote M = .bool false := hf (c, a) (by simp)
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := fold_none (e := e) base hb ks (fun k h => hf k (List.mem_cons_of_mem _ h))
    have hpick : ∀ x y : Term, (Term.share (.ite c x y)).denote M = y.denote M := fun x y => by
      simp [Term.denote, hc, toBool_bool]
    simp only [List.foldr_cons, pickTerms, hpick]
    refine ⟨i1, i2, i3, i4, i5, ?_, fun shs ds n0 => ?_, fun q0 => ?_⟩
    · rw [pick_tables_false hc]; exact i6
    · exact newsRel_append (newsRel_gate_false (L := L) (shs := shs) (ds := ds) hc n0) (i7 shs ds n0)
    · exact ownRel_append (ownRel_gate_false (L := L) (e := e) hc q0) (i8 q0)

/-- Merged step terms agree with those of the one kind whose test holds. -/
theorem fold_hit {e : Ty} (base : StepTerms v) (hb : base.done.news = [] ∧ base.done.owns = []) :
    (ks : List (Term × StepTerms v)) → (k : Nat) → {c : Term} → {st : StepTerms v} → ks[k]? = some (c, st) →
    (∀ (i : Nat) (kk : Term × StepTerms v), ks[i]? = some kk → kk.1.denote M = .bool (decide (i = k))) →
    let t := ks.foldr (fun k t => pickTerms k.1 k.2 t) base
    Agrees M L e t st ∧
      Term.denotes M t.done.tables.toList = Term.denotes M st.done.tables.toList
  | [], _, _, _, h, _ => by simp at h
  | (c', a) :: ks, 0, c, st, hk, ht => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hc : c'.denote M = .bool true := by simpa using ht 0 (c', a) rfl
    obtain ⟨-, -, -, -, -, -, i7, i8⟩ := fold_none (e := e) base hb ks
      (fun kk h => by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
        simpa using ht (i + 1) ks[i] (by simp))
    have hpick : ∀ x y : Term, (Term.share (.ite c' x y)).denote M = x.denote M := fun x y => by
      simp [Term.denote, hc, toBool_bool]
    refine ⟨⟨hpick _ _, hpick _ _, hpick _ _, hpick _ _, hpick _ _, fun shs ds effs n0 h => ?_, fun os q0 h => ?_⟩,
      ?_⟩
    · have := newsRel_append (newsRel_gate (L := L) hc h) (i7 shs ds (n0 + effs.length))
      rw [List.append_nil] at this
      exact this
    · have := ownRel_append (ownRel_gate (L := L) hc h) (i8 (q0 + os.length))
      rw [List.append_nil] at this
      exact this
    · show Term.denotes M (PerMachine.zipWith (fun x y => Term.share (.ite c' x y)) a.done.tables
        (List.foldr (fun k t => pickTerms k.1 k.2 t) base ks).done.tables).toList = _
      rw [pick_tables hc]
      rfl
  | (c', a) :: ks, j + 1, c, st, hk, ht => by
    have hc : c'.denote M = .bool false := by simpa using ht 0 (c', a) rfl
    obtain ⟨h1, h2⟩ := fold_hit (e := e) base hb ks j (by simpa using hk)
      (fun i kk h => by simpa using ht (i + 1) kk (by simpa using h))
    have hpick : ∀ x y : Term, (Term.share (.ite c' x y)).denote M = y.denote M := fun x y => by
      simp [Term.denote, hc, toBool_bool]
    refine ⟨⟨(hpick _ _).trans h1.fault, (hpick _ _).trans h1.fresh, (hpick _ _).trans h1.records,
      (hpick _ _).trans h1.nextId, (hpick _ _).trans h1.queued, fun shs ds effs n0 h => ?_, fun os q0 h => ?_⟩,
      ?_⟩
    · exact newsRel_append (newsRel_gate_false (L := L) (shs := shs) (ds := ds) hc n0) (h1.news shs ds effs n0 h)
    · exact ownRel_append (ownRel_gate_false (L := L) (e := e) hc q0) (h1.owns os q0 h)
    · show Term.denotes M (PerMachine.zipWith (fun x y => Term.share (.ite c' x y)) a.done.tables
        (List.foldr (fun k t => pickTerms k.1 k.2 t) base ks).done.tables).toList = _
      rw [pick_tables_false hc]
      exact h2

theorem find_hit {α : Type} {k : Nat} : (l : List (Term × α)) → {y : Term × α} → l[k]? = some y →
    (∀ (i : Nat) (kk : Term × α), l[i]? = some kk → kk.1.denote M = .bool (decide (i = k))) →
    l.find? (fun kk => (kk.1.denote M).toBool) = some y
  | [], _, h, _ => by simp at h
  | z :: l, y, hy, ht => by
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      simp [ht 0 z rfl, toBool_bool]
    | succ k =>
      have hz : (z.1.denote M).toBool = false := by simp [ht 0 z rfl, toBool_bool]
      rw [List.find?_cons, hz]
      exact find_hit (k := k) l (by simpa using hy) (fun i kk h => by simpa using ht (i + 1) kk (by simpa using h))

/-- An own effect's internal step: where the codes' condition holds, the condition holds exactly when the internal
step `Step.runOwn` runs fits (`ownFits`); wherever it holds, the fault term holds exactly when the model's kind names a
fault, which is `Step.runOwn`'s, and otherwise the internal step runs to its end with what the merged terms denote. -/
theorem ownStep_encode {P : List AnySite} (chk : Checked P T v)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (a : Step.Acc v)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    (senv : StepEnv L shs)
    {records now fresh n q eff : Term} {xs : PerMachine (fun _ => Term) v.machines} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ v.records_data a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    (x : EffectV v.event) (hx : RelV L (.dsl .effect [v.event]) x (eff.denote M)) (hown : x.isRequest = false)
    (hreach : x.Reach P)
    {o : OwnStepOut v} {cond codes : Term}
    (henc : encodeOwnStep L T P v shs senv apply records now fresh n q eff xs = .ok ⟨o, cond, codes⟩)
    (hcodes : Holds M codes) :
    (Holds M cond ↔ ownFits L.count T a.state x) ∧
    (Holds M cond → o.terms.fault.denote M = .bool (o.fault? M).isSome ∧
    match o.fault? M with
    | some f => Step.runOwn T a x = .error f
    | none => AccRel M L T shs a o.terms.done o.terms.fresh q0 (Step.runOwn T a x)) := by
  obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hx' : EffRel L x (eff.denote M) := hx
  obtain ⟨d, nn, hd, hx'⟩ := hx'
  cases (Prod.mk.inj (Option.some.inj (senv.hE.symm.trans hd))).1
  rcases hx' with ⟨k, key, vals, -, -, hh⟩ | ⟨k, key, vals, hk, heff, hkey⟩
  · cases x with
    | request => simp [EffectV.isRequest] at hown
    | command => exact hh.elim
    | query => exact hh.elim
  have hF := mapM_ok _ _ _ hks
  have heff' : (Term.share eff).denote M = .ctor senv.dE ((L.effectsOf v.event).length + k) vals := by
    rw [Term.denote_share]; exact heff
  have hzk : ((L.ownsOf v.event).zipIdx)[k]? = some (key, k) := by
    rw [List.getElem?_zipIdx, hk]; simp
  obtain ⟨kk, hkk, hR⟩ := forall2_getElem? hF hzk
  obtain ⟨⟨⟨ko, st⟩, c, cx⟩, hkind, hR⟩ := bind_ok.1 hR
  cases pure_ok.1 hR
  have htests : ∀ (i : Nat) (y : Term × Encoded (OwnKindStep v)), ks[i]? = some y →
      y.1.denote M = .bool (decide (i = k)) := by
    intro i y hy
    obtain ⟨⟨key', i'⟩, hz, hR'⟩ := forall2_getElem? (forall2_flip hF) hy
    obtain ⟨_, -, hR'⟩ := bind_ok.1 hR'
    cases pure_ok.1 hR'
    rw [List.getElem?_zipIdx] at hz
    obtain ⟨key'', -, he⟩ := Option.map_eq_some_iff.1 hz
    cases he
    simp only [Term.denote_share, Term.denote, heff', beq_self_eq_true, Bool.true_and, Nat.zero_add]
    congr 1
    by_cases h : i = k
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcxk : Holds M cx := (holds_allT _).1 hcodes _ (List.mem_map.2 ⟨_, List.mem_of_getElem? hkk, rfl⟩)
  refine ⟨?_, fun hc => ?_⟩
  · rw [← (ownKind_encode chk hshs a happ hca senv hrec hnow hfresh hn hq hms x
      hreach heff' hkey hkind hcxk).1, holds_allT]
    have htk := htests k _ hkk
    simp only [decide_true] at htk
    constructor
    · intro h
      have := (holds_ite _ _ _).1 (h _ (List.mem_map.2 ⟨_, List.mem_of_getElem? hkk, rfl⟩))
      simpa [htk, toBool_bool] using this
    · intro h t ht
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      have hti := htests i ks[i] (List.getElem?_eq_getElem hi)
      rw [holds_ite, hti, toBool_bool]
      by_cases hik : i = k
      · subst hik
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hkk
        simp only [decide_true, ite_true]
        rw [hkk]; exact h
      · simp only [hik, decide_false, Bool.false_eq_true, ite_false]
        exact holds_tt
  · have hcall := (holds_allT _).1 hc _ (List.mem_map.2 ⟨_, List.mem_of_getElem? hkk, rfl⟩)
    have htk := htests k _ hkk
    simp only [decide_true] at htk
    have hck : Holds M c := by
      have := (holds_ite _ _ _).1 hcall
      simpa [htk, toBool_bool] using this
    obtain ⟨hfault, hrun⟩ := (ownKind_encode chk hshs a happ hca senv hrec hnow hfresh hn hq
      hms x hreach heff' hkey hkind hcxk).2 hck
    obtain ⟨hag, htab⟩ := fold_hit (e := v.event) (M := M) (L := L) ⟨tt, ⟨records, xs, n, [], [], q⟩, fresh⟩ ⟨rfl, rfl⟩
      (ks.map fun k => (k.1, k.2.out.terms)) k (c := Term.share (.is senv.dE ((L.effectsOf v.event).length + k) (Term.share eff)))
      (st := st) (by simp [hkk])
      (fun i y hy => by
        rw [List.getElem?_map] at hy
        obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hy
        exact htests i z hz)
    rw [List.foldr_map] at hag htab
    have hfk : (OwnStepOut.fault? M ⟨ks.map fun k => (k.1, k.2.out.kind),
        ks.foldr (fun k t => pickTerms k.1 k.2.out.terms t) ⟨tt, ⟨records, xs, n, [], [], q⟩, fresh⟩⟩) = ko.fault? M := by
      unfold OwnStepOut.fault?
      rw [find_hit (k := k) (ks.map fun k => (k.1, k.2.out.kind))
        (y := (Term.share (.is senv.dE ((L.effectsOf v.event).length + k) (Term.share eff)), ko)) (by simp [hkk])
        (fun i y hy => by
          rw [List.getElem?_map] at hy
          obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hy
          exact htests i z hz)]
      rfl
    rw [hfk]
    refine ⟨hag.fault.trans hfault, ?_⟩
    revert hrun
    cases ko.fault? M with
    | some f => exact id
    | none =>
      intro hdone
      exact AccRel.congr hag htab hdone

end

end Tazuna.Smt
