import Tazuna.Smt.Internal

/-! The internal step for whichever own effect a queue place holds: `Step.runOwn` picks the service's command or query
by the effect's name and types, and the encoder makes the same choice per own kind, statically (`ownShape`), with the
program's site of the kind's `on_answer`. Each kind's internal step is encoded from the effect term's fields, and the
kinds are merged by the variant test of the effect term: exactly one kind's test holds for an own effect, so the
merged terms denote that kind's (precedent: the pending entry, whose shape the encoder fixes per kind). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- What an own kind runs, fixed from its name and types: the service's command or query with the program's site of
its `on_answer`, or nothing the service lists, which `Step.runOwn` makes `Fault.invalidEffect`. -/
inductive OwnShape (v : ServiceV) where
  | command (x : CommandV v.records v.event v.caller) (Γ : List Ty)
      (site : Site Γ (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event)))
  | query (x : QueryV v.records v.caller) (Γ : List Ty) (site : Site Γ (Ty.fn [x.output] (.list v.event)))
  | missing (name : String)

/-- The site of `P` of the type `t` that a kept function's code names. -/
def siteFor (P : List AnySite) (t : Ty) (k : SiteKey) : Option ((Γ : List Ty) × Site Γ t) :=
  (sitesOf P t).find? fun s => siteMatch s.2 k

/-- The shape of an own kind: the command or query `Step.runOwn` runs for its effects, and the site of `P` its
`on_answer` is written at. A kind whose site `P` lacks is refused: no effect that reaches `P` is of that kind. -/
def ownShape (v : ServiceV) (P : List AnySite) : OwnKey → Except Refusal (OwnShape v)
  | .command _ name c i j a =>
    match Ty.same c v.caller, Step.ownCommand (v := v) name i j with
    | some _, some ⟨x, _, _⟩ => do
      let ⟨Γ, s⟩ ← need "an own command whose on_answer site the program lacks"
        (siteFor P (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event)) a)
      pure (.command x Γ s)
    | _, _ => pure (.missing name)
  | .query _ name c i o a =>
    match Ty.same c v.caller, Step.ownQuery (v := v) name i o with
    | some _, some ⟨x, _, _⟩ => do
      let ⟨Γ, s⟩ ← need "an own query whose on_answer site the program lacks"
        (siteFor P (Ty.fn [x.output] (.list v.event)) a)
      pure (.query x Γ s)
    | _, _ => pure (.missing name)

/-- The outcome terms of one own kind's internal step. -/
inductive OwnKindOut where
  | command (name : String) (o : OwnCommandOut)
  | query (name : String) (o : OwnQueryOut)
  | missing (name : String)

/-- The fault the outcome terms name in the model, or none when the internal step runs to its end. -/
def OwnKindOut.fault? (M : Model) : OwnKindOut → Option Fault
  | .command name o =>
    if (o.callerOk.denote M).toBool then
      match brokenIn M o.rules with
      | n :: ns => some (.invalidEffect name (n :: ns))
      | [] =>
        match (o.ok.denote M).toBool, brokenIn M o.ensures with
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
structure StepTerms where
  fault : Term
  done : EventsOut
  fresh : Term

/-- The terms of `a` where `c` holds and of `b` elsewhere; the slots of `a` count only where `c` holds. -/
def pickTerms (c : Term) (a b : StepTerms) : StepTerms :=
  let p (x y : Term) := Term.share (.ite c x y)
  ⟨p a.fault b.fault,
    ⟨p a.done.records b.done.records, b.done.tables.mapIdx fun i y => p (a.done.tables.getD i tt) y,
      p a.done.nextId b.done.nextId, gateSlots c a.done.news ++ b.done.news, gateSlots c a.done.owns ++ b.done.owns,
      p a.done.queued b.done.queued⟩,
    p a.fresh b.fresh⟩

/-- The terms of an own effect's internal step: each own kind's variant test with its outcome terms, and the merged
terms. -/
structure OwnStepOut where
  kinds : List (Term × OwnKindOut)
  terms : StepTerms

/-- The fault the model's kind names: the outcome terms of the kind whose test holds. -/
def OwnStepOut.fault? (M : Model) (o : OwnStepOut) : Option Fault :=
  (o.kinds.find? fun k => (k.1.denote M).toBool).bind fun k => k.2.fault? M

section
variable (L : Layout) (T : List TypeDecl)

/-- One own kind's internal step for the effect term `eff`, read as the kind's variant `nR + j`: its outcome and step
terms, its condition, and the condition of the command's or query's codes. -/
def encodeOwnKind (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (dE dP dopt nR : Nat)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (records now fresh n q eff : Term) (xs : List Term)
    (j : Nat) (key : OwnKey) : Except Refusal (OwnKindOut × StepTerms × Term × Term) := do
  let sel (i : Nat) := Term.sel dE (nR + j) i eff
  match ← ownShape v P key with
  | .missing name => pure (.missing name, ⟨tt, ⟨records, xs, n, [], [], q⟩, fresh⟩, tt, tt)
  | .command x Γ site =>
    let (cc, cx) ← CommandCode.of L x
    let ks ← need "callers that have no term"
      (if h : v.caller.isData = true then callerTerms L h x.callers else none)
    let (da, _) ← need "a layout without the captures' tuple" (L.find? (.tuple Γ))
    let σ ← need "captures that have no term" (tupleCodes da Γ (sel 2) 0)
    let (o, c) ← encodeOwnCommand L T v shs dE dP dopt x cc site σ apply ks records now fresh n q (sel 0) (sel 1) xs
    let fault := Term.or (.not o.callerOk)
      (.or (.not (allT (o.rules.map (·.2)))) (.and o.ok (.not (allT (o.ensures.map (·.2))))))
    pure (.command x.name o,
      ⟨fault, { o.answered with news := o.decided.news ++ o.answered.news, owns := o.decided.owns ++ o.answered.owns },
        .add fresh (.int 1)⟩, c, cx)
  | .query x Γ site =>
    let (qc, cq) ← QueryCode.of L x
    let ks ← need "callers that have no term"
      (if h : v.caller.isData = true then callerTerms L h x.callers else none)
    let (da, _) ← need "a layout without the captures' tuple" (L.find? (.tuple Γ))
    let σ ← need "captures that have no term" (tupleCodes da Γ (sel 2) 0)
    let (o, c) ← encodeOwnQuery L T v shs dE dP dopt x qc site σ apply ks records now fresh n q (sel 0) (sel 1) xs
    pure (.query x.name o, ⟨.or (.not o.callerOk) (.not (allT (o.rules.map (·.2)))), o.answered, fresh⟩, c, cq)

/-- The internal step for the own effect term `eff`: every own kind's, merged by the variant tests; its condition
asks each kind's only where its test holds. The second term is the codes' condition, which holds statically. -/
def encodeOwnStep (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (dE dP dopt : Nat)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (records now fresh n q eff : Term) (xs : List Term) :
    Except Refusal (OwnStepOut × Term × Term) := do
  let nR := (L.effectsOf v.event).length
  let eff := Term.share eff
  let ks ← (L.ownsOf v.event).zipIdx.mapM fun (key, j) => do
    let (ko, st, c, cx) ← encodeOwnKind L T P v shs dE dP dopt nR apply records now fresh n q eff xs j key
    pure (Term.share (.is dE (nR + j) eff), ko, st, c, cx)
  let base : StepTerms := ⟨tt, ⟨records, xs, n, [], [], q⟩, fresh⟩
  pure (⟨ks.map fun k => (k.1, k.2.1), ks.foldr (fun k t => pickTerms k.1 k.2.2.1 t) base⟩,
    allT (ks.map fun k => .ite k.1 k.2.2.2.1 tt), allT (ks.map (·.2.2.2.2)))

end

/-! What fits for an own effect's internal step, in `Step.runOwn`'s terms. -/

section
variable {v : ServiceV}

/-- Whether an own command's internal step fits from `s`: what `ownCommand_exact` says its condition holds for. -/
def commandFits (S : Ty → Nat) (T : List TypeDecl) (s : State v) (x : CommandV v.records v.event v.caller)
    (caller : v.caller.den0) (input : x.input.den0)
    (oa : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) : Prop :=
  let ctx := Step.ctx s s.records caller input
  x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
    x.accepts.appFits S (input, ()) ∧
    (Step.broken (x.accepts.fn (input, ())) = [] →
      x.decide.appFits S (ctx, ()) ∧ ownDecidedFits S T { s with fresh := s.fresh + 1 } x ctx oa (x.decide.fn (ctx, ())))

/-- Whether an own query's internal step fits from `s`: what `ownQuery_exact` says its condition holds for. -/
def queryFits (S : Ty → Nat) (T : List TypeDecl) (s : State v) (x : QueryV v.records v.caller)
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
      commandFits S T s x (cast (congrArg Ty.den0 hc) caller) (cast (congrArg Ty.den0 hi) value) (hj ▸ onAnswer)
    | _, _ => True
  | .query name c i o caller value onAnswer =>
    match Ty.same c v.caller, Step.ownQuery (v := v) name i o with
    | some ⟨hc⟩, some ⟨x, hi, ho⟩ =>
      queryFits S T s x (cast (congrArg Ty.den0 hc) caller) (cast (congrArg Ty.den0 hi) value) (ho ▸ onAnswer)
    | _, _ => True

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- Every slot an events loop writes, news or own, holds two items. -/
theorem encodeEvents_width {shs : List (PendingShape v.event)} {dE dP dopt : Nat}
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {now : Term} :
    (S : List Slot) → {records : Term} → {xs : List Term} → {n q : Term} → {o : EventsOut} → {c : Term} →
    encodeEvents L T v shs dE dP dopt apply now S records xs n q = .ok (o, c) →
    (∀ sl ∈ o.news, sl.2.length = 2) ∧ ∀ sl ∈ o.owns, sl.2.length = 2
  | [], _, _, _, _, _, _, h => by
    simp only [encodeEvents, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | (f, ys) :: S, _, _, _, _, _, _, h => by
    obtain ⟨rc, -, h⟩ := bind_ok.1 h
    obtain ⟨ec, -, h⟩ := bind_ok.1 h
    obtain ⟨⟨r', ca⟩, -, h⟩ := bind_ok.1 h
    obtain ⟨rt, -, h⟩ := bind_ok.1 h
    obtain ⟨⟨outs, cm⟩, -, h⟩ := bind_ok.1 h
    obtain ⟨⟨news, nT, oS, qT⟩, h6, h⟩ := bind_ok.1 h
    obtain ⟨⟨rnews, nR, rown, qR, cr⟩, h7, h⟩ := bind_ok.1 h
    obtain ⟨⟨o', c'⟩, h8, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have hw6 := encodeStarts_width _ _ h6
    have hw7 := encodeReactions_width _ h7
    have ih := encodeEvents_width S h8
    have hg : ∀ (A B : List Slot), (∀ sl ∈ A, sl.2.length = 2) → (∀ sl ∈ B, sl.2.length = 2) →
        ∀ sl ∈ gateSlots f A ++ B, sl.2.length = 2 := by
      intro A B hA hB sl hsl
      rcases List.mem_append.1 hsl with hsl | hsl
      · obtain ⟨sl', hsl', rfl⟩ := List.mem_map.1 hsl
        exact hA sl' hsl'
      · exact hB sl hsl
    refine ⟨hg _ _ ?_ ih.1, hg _ _ ?_ ih.2⟩
    · intro sl hsl
      rcases List.mem_append.1 hsl with hsl | hsl
      · exact hw6.1 sl hsl
      · exact hw7.1 sl hsl
    · intro sl hsl
      rcases List.mem_append.1 hsl with hsl | hsl
      · exact hw6.2 sl hsl
      · exact hw7.2 sl hsl

theorem width_append {A B : List Slot} (hA : ∀ sl ∈ A, sl.2.length = 2) (hB : ∀ sl ∈ B, sl.2.length = 2) :
    ∀ sl ∈ A ++ B, sl.2.length = 2 := by
  intro sl hsl
  rcases List.mem_append.1 hsl with hsl | hsl
  · exact hA sl hsl
  · exact hB sl hsl

theorem width_gate (f : Term) {A : List Slot} (hA : ∀ sl ∈ A, sl.2.length = 2) : ∀ sl ∈ gateSlots f A, sl.2.length = 2 := by
  intro sl hsl
  obtain ⟨sl', hsl', rfl⟩ := List.mem_map.1 hsl
  exact hA sl' hsl'

/-- The step terms of one own kind write slots of two items. -/
theorem encodeOwnKind_width {P : List AnySite} {shs : List (PendingShape v.event)} {dE dP dopt nR : Nat}
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {records now fresh n q eff : Term} {xs : List Term}
    {j : Nat} {key : OwnKey} {ko : OwnKindOut} {st : StepTerms} {c cx : Term}
    (h : encodeOwnKind L T P v shs dE dP dopt nR apply records now fresh n q eff xs j key = .ok (ko, st, c, cx)) :
    (∀ sl ∈ st.done.news, sl.2.length = 2) ∧ ∀ sl ∈ st.done.owns, sl.2.length = 2 := by
  obtain ⟨sh, -, h⟩ := bind_ok.1 h
  cases sh with
  | missing name => cases pure_ok.1 h; simp
  | command x Γ site =>
    obtain ⟨⟨cc, cx'⟩, -, h⟩ := bind_ok.1 h
    obtain ⟨ks, -, h⟩ := bind_ok.1 h
    obtain ⟨⟨da, dn⟩, -, h⟩ := bind_ok.1 h
    obtain ⟨σ, -, h⟩ := bind_ok.1 h
    obtain ⟨⟨o, c'⟩, henc, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    unfold encodeOwnCommand at henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o1, _⟩, h12, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o2, _⟩, h23, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have w1 := encodeEvents_width _ h12
    have w2 := encodeEvents_width _ h23
    exact ⟨width_append w1.1 w2.1, width_append w1.2 w2.2⟩
  | query x Γ site =>
    obtain ⟨⟨qc, cq⟩, -, h⟩ := bind_ok.1 h
    obtain ⟨ks, -, h⟩ := bind_ok.1 h
    obtain ⟨⟨da, dn⟩, -, h⟩ := bind_ok.1 h
    obtain ⟨σ, -, h⟩ := bind_ok.1 h
    obtain ⟨⟨o, c'⟩, henc, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    unfold encodeOwnQuery at henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨_, _, _⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o1, _⟩, h13, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    exact encodeEvents_width _ h13

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

theorem allT_rules (rules : List (Term × Term)) :
    (allT (rules.map (·.2))).denote M = .bool (brokenIn M rules).isEmpty := by
  rw [allT_denote]
  congr 1
  cases h : brokenIn M rules with
  | nil => exact (brokenIn_nil rules).1 h
  | cons n ns =>
    have : ¬ (rules.map (·.2)).all (fun t => (t.denote M).toBool) = true := fun h' => by
      rw [(brokenIn_nil rules).2 h'] at h; cases h
    simpa using this

theorem toBool_bool (b : Bool) : (Val.bool b).toBool = b := rfl

theorem fault_command (name : String) (o : OwnCommandOut) :
    Term.denote M (.or (.not o.callerOk) (.or (.not (allT (o.rules.map (·.2))))
      (.and o.ok (.not (allT (o.ensures.map (·.2))))))) = .bool ((OwnKindOut.command name o).fault? M).isSome := by
  simp only [Term.denote, allT_rules, OwnKindOut.fault?, toBool_bool]
  cases (o.callerOk.denote M).toBool
  · rfl
  · cases brokenIn M o.rules with
    | cons n ns => rfl
    | nil => cases (o.ok.denote M).toBool <;> cases brokenIn M o.ensures <;> rfl

theorem fault_query (name : String) (o : OwnQueryOut) :
    Term.denote M (.or (.not o.callerOk) (.not (allT (o.rules.map (·.2))))) =
      .bool ((OwnKindOut.query name o).fault? M).isSome := by
  simp only [Term.denote, allT_rules, OwnKindOut.fault?, toBool_bool]
  cases (o.callerOk.denote M).toBool
  · rfl
  · cases brokenIn M o.rules <;> rfl

/-- T2 for one own kind's internal step, for an own effect of the kind: the fault term holds exactly when the
outcome terms name a fault, which is `Step.runOwn`'s; otherwise the internal step runs to its end with what the step
terms denote (`InternalDone`), at the fresh counter the fresh term denotes. -/
theorem ownKind_rel {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (a : Step.Acc v) (hinv : Step.Inv P a.state)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {records now fresh n q eff : Term} {xs : List Term} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ hrd a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    {j : Nat} {key : OwnKey} (x : EffectV v.event) (hreach : x.Reach P) {vals : List Val}
    (heff : eff.denote M = .ctor dE ((L.effectsOf v.event).length + j) vals) (hkey : key.Holds L x vals)
    {ko : OwnKindOut} {st : StepTerms} {c cx : Term}
    (henc : encodeOwnKind L T P v shs dE dP dopt (L.effectsOf v.event).length apply records now fresh n q eff xs j key =
      .ok (ko, st, c, cx))
    (hc : Holds M c) (hcx : Holds M cx) :
    st.fault.denote M = .bool (ko.fault? M).isSome ∧
    match ko.fault? M with
    | some f => Step.runOwn T a x = .error f
    | none => ∃ fr : Nat, st.fresh.denote M = .int (fr : Int) ∧
        InternalDone M L T hrd shs a fr st.done st.done.news st.done.owns q0 (Step.runOwn T a x) := by
  have hsel : ∀ i, (Term.sel dE ((L.effectsOf v.event).length + j) i eff).denote M = vals[i]?.getD default :=
    fun i => sel_ctor i heff
  obtain ⟨sh, hsh, henc⟩ := bind_ok.1 henc
  cases key with
  | command e name c0 i jj a0 =>
    cases x with
    | request => exact hkey.elim
    | query => exact hkey.elim
    | command name' c' i' j' caller value onAnswer =>
    obtain ⟨rfl, rfl, rfl, rfl, hsite, hΓ, vc, vi, va, rfl, hvc, hvi, hva⟩ := hkey
    unfold ownShape at hsh
    unfold Step.runOwn
    dsimp only at hsh ⊢
    revert hsh
    generalize hoc : Ty.same c' v.caller = oc
    generalize hox : Step.ownCommand (v := v) name' i' j' = ox
    intro hsh
    have miss : ∀ (h : sh = .missing name'), Term.denote M st.fault = .bool (ko.fault? M).isSome ∧
        ko.fault? M = some (.invalidEffect name' ["service"]) := by
      intro h; subst h; cases pure_ok.1 henc; exact ⟨rfl, rfl⟩
    cases oc with
    | none =>
      cases ox <;>
      · dsimp only at hsh ⊢
        obtain ⟨h1, h2⟩ := miss (pure_ok.1 hsh).symm
        rw [h2]; exact ⟨h1.trans (by rw [h2]), rfl⟩
    | some hc =>
    cases ox with
    | none =>
      dsimp only at hsh ⊢
      obtain ⟨h1, h2⟩ := miss (pure_ok.1 hsh).symm
      rw [h2]; exact ⟨h1.trans (by rw [h2]), rfl⟩
    | some xx =>
    obtain ⟨hc⟩ := hc
    obtain ⟨x, hi, hj⟩ := xx
    subst hc hi hj
    dsimp only at hsh ⊢
    obtain ⟨⟨Γ, s⟩, hsf, hsh⟩ := bind_ok.1 hsh
    cases pure_ok.1 hsh
    obtain ⟨⟨cc, cx'⟩, hcc, henc⟩ := bind_ok.1 henc
    obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨da, dn⟩, hda, henc⟩ := bind_ok.1 henc
    obtain ⟨σ, hσ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c'⟩, hoe, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have hd := hcd x (ownCommand_mem hox)
    obtain ⟨hsP, hss, hsΓ⟩ := siteFor_spec (need_ok.1 hsf)
    obtain ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ := onAnswer
    dsimp only at hsite hΓ
    obtain ⟨e, hA⟩ := Fun.eq_siteFn hP ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ s hreach hsP (hsite.trans hss.symm)
    dsimp only at e hA
    subst e
    obtain ⟨d', n', vals', hd', rfl, hrds⟩ := hva
    obtain rfl := find_det hd' (need_ok.1 hda)
    have hσ' : Rels M L _ (Ty.up _ s.hΓ oenv) σ :=
      tupleCodes_rels _ [] vals' _ σ (by rw [hsel]; rfl) (relDs_up _ s.hΓ oenv vals' hrds) (need_ok.1 hσ)
    have hks' : callerTerms L hd.caller x.callers = some ks := by
      have h := need_ok.1 hks
      split at h
      · exact h
      · cases h
    have hsc : RelV L v.caller (Ty.up _ hd.caller caller)
        ((Term.sel dE ((L.effectsOf v.event).length + j) 0 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvc
    have hsi : RelV L x.input (Ty.up _ hd.input value)
        ((Term.sel dE ((L.effectsOf v.event).length + j) 1 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvi
    have H := ownCommand_rel hP hvx hshs hor a hinv x caller value hd hcc hcx happ hca s oenv hσ' hks' hE hPE hopt
      hrec hnow hfresh hn hq hms hsc hsi hoe hc
    simp only [cast_eq]
    rw [show (⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ : Fun _) = s.fn oenv from hA]
    refine ⟨fault_command x.name o, ?_⟩
    simp only [OwnKindOut.fault?]
    dsimp only at H
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
          have hnone : (match (o.ok.denote M).toBool, brokenIn M o.ensures with
              | true, n :: _ => some (Fault.ensures n)
              | _, _ => none) = none := by
            split
            · rename_i n ns hok hb'; exact (hne n ns hok hb').elim
            · rfl
          rw [hnone]
          refine ⟨a.state.fresh + 1, ?_, H⟩
          simp only [Term.denote, hfresh]
          rfl
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
    unfold Step.runOwn
    dsimp only at hsh ⊢
    revert hsh
    generalize hoc : Ty.same c' v.caller = oc
    generalize hox : Step.ownQuery (v := v) name' i' j' = ox
    intro hsh
    have miss : ∀ (h : sh = .missing name'), Term.denote M st.fault = .bool (ko.fault? M).isSome ∧
        ko.fault? M = some (.invalidEffect name' ["service"]) := by
      intro h; subst h; cases pure_ok.1 henc; exact ⟨rfl, rfl⟩
    cases oc with
    | none =>
      cases ox <;>
      · dsimp only at hsh ⊢
        obtain ⟨h1, h2⟩ := miss (pure_ok.1 hsh).symm
        rw [h2]; exact ⟨h1.trans (by rw [h2]), rfl⟩
    | some hc =>
    cases ox with
    | none =>
      dsimp only at hsh ⊢
      obtain ⟨h1, h2⟩ := miss (pure_ok.1 hsh).symm
      rw [h2]; exact ⟨h1.trans (by rw [h2]), rfl⟩
    | some xx =>
    obtain ⟨hc⟩ := hc
    obtain ⟨x, hi, hj⟩ := xx
    subst hc hi hj
    dsimp only at hsh ⊢
    obtain ⟨⟨Γ, s⟩, hsf, hsh⟩ := bind_ok.1 hsh
    cases pure_ok.1 hsh
    obtain ⟨⟨qc, cx'⟩, hqc, henc⟩ := bind_ok.1 henc
    obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨da, dn⟩, hda, henc⟩ := bind_ok.1 henc
    obtain ⟨σ, hσ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c'⟩, hoe, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have hd := hqd x (ownQuery_mem hox)
    obtain ⟨hsP, hss, hsΓ⟩ := siteFor_spec (need_ok.1 hsf)
    obtain ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ := onAnswer
    dsimp only at hsite hΓ
    obtain ⟨e, hA⟩ := Fun.eq_siteFn hP ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ s hreach hsP (hsite.trans hss.symm)
    dsimp only at e hA
    subst e
    obtain ⟨d', n', vals', hd', rfl, hrds⟩ := hva
    obtain rfl := find_det hd' (need_ok.1 hda)
    have hσ' : Rels M L _ (Ty.up _ s.hΓ oenv) σ :=
      tupleCodes_rels _ [] vals' _ σ (by rw [hsel]; rfl) (relDs_up _ s.hΓ oenv vals' hrds) (need_ok.1 hσ)
    have hks' : callerTerms L hd.caller x.callers = some ks := by
      have h := need_ok.1 hks
      split at h
      · exact h
      · cases h
    have hsc : RelV L v.caller (Ty.up _ hd.caller caller)
        ((Term.sel dE ((L.effectsOf v.event).length + j) 0 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvc
    have hsi : RelV L x.input (Ty.up _ hd.input value)
        ((Term.sel dE ((L.effectsOf v.event).length + j) 1 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvi
    have hvm : ∀ m ∈ v.machines, m.Reach P := by
      intro m hm
      rw [← hinv.machinesOf] at hm
      obtain ⟨sm, hsm, rfl⟩ := List.mem_map.1 hm
      exact hinv.machines sm hsm
    have H := ownQuery_rel hP hvx hvm hshs hor hed a x caller value hd hqc hcx happ hca s oenv hσ' hks' hE hPE hopt
      hrec hnow hfresh hn hq hms hsc hsi hoe hc
    simp only [cast_eq]
    rw [show (⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ : Fun _) = s.fn oenv from hA]
    refine ⟨fault_query x.name o, ?_⟩
    simp only [OwnKindOut.fault?]
    dsimp only at H
    split at H
    · rename_i hco
      simp only [hco, ite_true]
      split at H
      · rename_i n ns hb
        simp only [hb]
        exact H
      · rename_i hb
        simp only [hb]
        exact ⟨a.state.fresh, hfresh, H⟩
    · rename_i hco
      simp only [hco, Bool.false_eq_true, ite_false]
      exact H

theorem machinesRel_congr : (ms : List (MachineV v.records v.event)) → (xs ys : List Term) →
    (sms : List (Step.MachineState v.records v.event)) → Term.denotes M xs = Term.denotes M ys →
    MachinesRel M L T ms xs sms → MachinesRel M L T ms ys sms
  | [], [], [], [], _, h => h
  | [], [], _ :: _, _, he, _ | _ :: _, _ :: _, [], _, he, _ => by simp [Term.denotes] at he
  | [], _ :: _, _, _, _, h | [], [], [], _ :: _, _, h | _ :: _, [], _, _, _, h | _ :: _, _ :: _, _ :: _, [], _, h =>
    h.elim
  | _ :: ms, _ :: xs, _ :: ys, _ :: sms, he, ⟨⟨tbl, ht, hs⟩, h⟩ => by
    simp only [Term.denotes, List.cons.injEq] at he
    exact ⟨⟨tbl, he.1 ▸ ht, hs⟩, machinesRel_congr ms xs ys sms he.2 h⟩

/-- Two step terms say the same in the model: the same values, and slots holding the same news and own effects. -/
structure Agrees (M : Model) (L : Layout) (e : Ty) (a b : StepTerms) : Prop where
  fault : a.fault.denote M = b.fault.denote M
  fresh : a.fresh.denote M = b.fresh.denote M
  records : a.done.records.denote M = b.done.records.denote M
  nextId : a.done.nextId.denote M = b.done.nextId.denote M
  queued : a.done.queued.denote M = b.done.queued.denote M
  news : ∀ (shs : List (PendingShape e)) ds effs n0, NewsRel M L shs ds b.done.news effs n0 →
    NewsRel M L shs ds a.done.news effs n0
  owns : ∀ (os : List (EffectV e)) q0, OwnRel M L b.done.owns os q0 → OwnRel M L a.done.owns os q0

theorem internalDone_agrees {a b : StepTerms} (hab : Agrees M L v.event a b)
    (ht : Term.denotes M a.done.tables = Term.denotes M b.done.tables)
    {hrd : v.records.isData = true} {shs : List (PendingShape v.event)} {acc : Step.Acc v} {fr q0 : Nat}
    {r : Except Fault (Step.Acc v)} (h : InternalDone M L T hrd shs acc fr b.done b.done.news b.done.owns q0 r) :
    InternalDone M L T hrd shs acc fr a.done a.done.news a.done.owns q0 r := by
  obtain ⟨recs, ms, evs, effs, os, hr, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨recs, ms, evs, effs, os, hr, hab.records ▸ h1, machinesRel_congr _ _ _ _ ht.symm h2, hab.nextId ▸ h3,
    hab.news _ _ _ _ h4, hab.queued ▸ h5, hab.owns _ _ h6⟩

theorem pick_tables_length (c : Term) (a b : StepTerms) :
    (pickTerms c a b).done.tables.length = b.done.tables.length := by
  simp [pickTerms]

theorem fold_tables_length (base : StepTerms) : (ks : List (Term × StepTerms)) →
    (ks.foldr (fun k t => pickTerms k.1 k.2 t) base).done.tables.length = base.done.tables.length
  | [] => rfl
  | k :: ks => by simp only [List.foldr_cons, pick_tables_length, fold_tables_length base ks]

theorem pick_tables {c : Term} {bc : Bool} (hc : c.denote M = .bool bc) (A B : List Term) (hl : A.length = B.length) :
    Term.denotes M (B.mapIdx fun i y => Term.share (.ite c (A.getD i tt) y)) =
      Term.denotes M (if bc then A else B) := by
  rw [denotes_eq_map, denotes_eq_map]
  apply List.ext_getElem
  · cases bc <;> simp [hl]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_mapIdx, Term.denote_share, Term.denote, hc, toBool_bool]
    cases bc
    · rfl
    · simp only [ite_true]
      have : i < A.length := by simp at h2; exact h2
      simp [List.getD, List.getElem?_eq_getElem this]

theorem pick_tables_false {c : Term} (hc : c.denote M = .bool false) (A B : List Term) :
    Term.denotes M (B.mapIdx fun i y => Term.share (.ite c (A.getD i tt) y)) = Term.denotes M B := by
  rw [denotes_eq_map, denotes_eq_map]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [Term.denote, hc, toBool_bool]

/-- Step terms of kinds whose tests all fail write no news and no own effect. -/
theorem fold_none {e : Ty} (base : StepTerms) (hb : base.done.news = [] ∧ base.done.owns = []) :
    (ks : List (Term × StepTerms)) → (∀ k ∈ ks, k.1.denote M = .bool false) →
    (∀ k ∈ ks, (∀ sl ∈ k.2.done.news, sl.2.length = 2) ∧ ∀ sl ∈ k.2.done.owns, sl.2.length = 2) →
    let t := ks.foldr (fun k t => pickTerms k.1 k.2 t) base
    t.fault.denote M = base.fault.denote M ∧ t.fresh.denote M = base.fresh.denote M ∧
      t.done.records.denote M = base.done.records.denote M ∧ t.done.nextId.denote M = base.done.nextId.denote M ∧
      t.done.queued.denote M = base.done.queued.denote M ∧
      Term.denotes M t.done.tables = Term.denotes M base.done.tables ∧
      (∀ (shs : List (PendingShape e)) ds n0, NewsRel M L shs ds t.done.news [] n0) ∧
      ∀ q0, OwnRel M L t.done.owns ([] : List (EffectV e)) q0
  | [], _, _ => by
    simp only [List.foldr_nil, hb, true_and]
    exact ⟨fun _ _ _ => ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩,
      fun q0 => ownRel_nil q0⟩
  | (c, a) :: ks, hf, hw => by
    have hc : c.denote M = .bool false := hf (c, a) (by simp)
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := fold_none (e := e) base hb ks (fun k h => hf k (List.mem_cons_of_mem _ h))
      (fun k h => hw k (List.mem_cons_of_mem _ h))
    have hwa := hw (c, a) (by simp)
    have hpick : ∀ x y : Term, (Term.share (.ite c x y)).denote M = y.denote M := fun x y => by
      simp [Term.denote, hc, toBool_bool]
    simp only [List.foldr_cons, pickTerms, hpick]
    refine ⟨i1, i2, i3, i4, i5, ?_, fun shs ds n0 => ?_, fun q0 => ?_⟩
    · rw [pick_tables_false hc]; exact i6
    · have := newsRel_append (newsRel_gate_false (L := L) (shs := shs) (ds := ds) hc hwa.1 n0) (i7 shs ds n0)
      exact this
    · have := ownRel_append (ownRel_gate_false (L := L) (e := e) hc hwa.2 q0) (i8 q0)
      exact this

/-- Merged step terms agree with those of the one kind whose test holds. -/
theorem fold_hit {e : Ty} (base : StepTerms) (hb : base.done.news = [] ∧ base.done.owns = []) :
    (ks : List (Term × StepTerms)) → (k : Nat) → {c : Term} → {st : StepTerms} → ks[k]? = some (c, st) →
    (∀ (i : Nat) (kk : Term × StepTerms), ks[i]? = some kk → kk.1.denote M = .bool (decide (i = k))) →
    (∀ kk ∈ ks, (∀ sl ∈ kk.2.done.news, sl.2.length = 2) ∧ ∀ sl ∈ kk.2.done.owns, sl.2.length = 2) →
    let t := ks.foldr (fun k t => pickTerms k.1 k.2 t) base
    Agrees M L e t st ∧
      (st.done.tables.length = base.done.tables.length → Term.denotes M t.done.tables = Term.denotes M st.done.tables)
  | [], _, _, _, h, _, _ => by simp at h
  | (c', a) :: ks, 0, c, st, hk, ht, hw => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hc : c'.denote M = .bool true := by simpa using ht 0 (c', a) rfl
    obtain ⟨-, -, -, -, -, -, i7, i8⟩ := fold_none (e := e) base hb ks
      (fun kk h => by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
        simpa using ht (i + 1) ks[i] (by simp))
      (fun kk h => hw kk (List.mem_cons_of_mem _ h))
    have hpick : ∀ x y : Term, (Term.share (.ite c' x y)).denote M = x.denote M := fun x y => by
      simp [Term.denote, hc, toBool_bool]
    refine ⟨⟨hpick _ _, hpick _ _, hpick _ _, hpick _ _, hpick _ _, fun shs ds effs n0 h => ?_, fun os q0 h => ?_⟩,
      fun hl => ?_⟩
    · have := newsRel_append (newsRel_gate (L := L) hc h) (i7 shs ds (n0 + effs.length))
      rw [List.append_nil] at this
      exact this
    · have := ownRel_append (ownRel_gate (L := L) hc h) (i8 (q0 + os.length))
      rw [List.append_nil] at this
      exact this
    · show Term.denotes M ((List.foldr (fun k t => pickTerms k.1 k.2 t) base ks).done.tables.mapIdx
        fun i y => Term.share (.ite c' (a.done.tables.getD i tt) y)) = _
      rw [pick_tables hc _ _ (by rw [fold_tables_length]; exact hl)]
      rfl
  | (c', a) :: ks, j + 1, c, st, hk, ht, hw => by
    have hc : c'.denote M = .bool false := by simpa using ht 0 (c', a) rfl
    obtain ⟨h1, h2⟩ := fold_hit (e := e) base hb ks j (by simpa using hk)
      (fun i kk h => by simpa using ht (i + 1) kk (by simpa using h))
      (fun kk h => hw kk (List.mem_cons_of_mem _ h))
    have hwa := hw (c', a) (by simp)
    have hpick : ∀ x y : Term, (Term.share (.ite c' x y)).denote M = y.denote M := fun x y => by
      simp [Term.denote, hc, toBool_bool]
    refine ⟨⟨(hpick _ _).trans h1.fault, (hpick _ _).trans h1.fresh, (hpick _ _).trans h1.records,
      (hpick _ _).trans h1.nextId, (hpick _ _).trans h1.queued, fun shs ds effs n0 h => ?_, fun os q0 h => ?_⟩,
      fun hl => ?_⟩
    · exact newsRel_append (newsRel_gate_false (L := L) (shs := shs) (ds := ds) hc hwa.1 n0) (h1.news shs ds effs n0 h)
    · exact ownRel_append (ownRel_gate_false (L := L) (e := e) hc hwa.2 q0) (h1.owns os q0 h)
    · show Term.denotes M ((List.foldr (fun k t => pickTerms k.1 k.2 t) base ks).done.tables.mapIdx
        fun i y => Term.share (.ite c' (a.done.tables.getD i tt) y)) = _
      rw [pick_tables_false hc]
      exact h2 hl

theorem forall2_getElem?_r {α β : Type} {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs →
    {i : Nat} → {b : β} → bs[i]? = some b → ∃ a, as[i]? = some a ∧ R a b
  | [], [], _, _, _, h => by cases h
  | _ :: _, _ :: _, ⟨hab, _⟩, 0, _, h => by cases h; exact ⟨_, rfl, hab⟩
  | _ :: _, _ :: _, ⟨_, hs⟩, i + 1, _, h => forall2_getElem?_r hs (i := i) (by simpa using h)

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

/-- T2 for an own effect's internal step: the fault term holds exactly when the model's kind names a fault, which is
`Step.runOwn`'s; otherwise the internal step runs to its end with what the merged terms denote. -/
theorem ownStep_rel {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (a : Step.Acc v) (hinv : Step.Inv P a.state)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {records now fresh n q eff : Term} {xs : List Term} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ hrd a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    (x : EffectV v.event) (hx : RelV L (.dsl .effect [v.event]) x (eff.denote M)) (hown : x.isRequest = false)
    (hreach : x.Reach P)
    {o : OwnStepOut} {cond codes : Term}
    (henc : encodeOwnStep L T P v shs dE dP dopt apply records now fresh n q eff xs = .ok (o, cond, codes))
    (hc : Holds M cond) (hcodes : Holds M codes) :
    o.terms.fault.denote M = .bool (o.fault? M).isSome ∧
    match o.fault? M with
    | some f => Step.runOwn T a x = .error f
    | none => ∃ fr : Nat, o.terms.fresh.denote M = .int (fr : Int) ∧
        InternalDone M L T hrd shs a fr o.terms.done o.terms.done.news o.terms.done.owns q0 (Step.runOwn T a x) := by
  obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hx' : EffRel L x (eff.denote M) := hx
  obtain ⟨d, nn, hd, hx'⟩ := hx'
  cases (Prod.mk.inj (Option.some.inj (hE.symm.trans hd))).1
  rcases hx' with ⟨k, key, vals, -, -, hh⟩ | ⟨k, key, vals, hk, heff, hkey⟩
  · cases x with
    | request => simp [EffectV.isRequest] at hown
    | command => exact hh.elim
    | query => exact hh.elim
  have hF := mapM_ok _ _ _ hks
  have heff' : (Term.share eff).denote M = .ctor dE ((L.effectsOf v.event).length + k) vals := by
    rw [Term.denote_share]; exact heff
  have hzk : ((L.ownsOf v.event).zipIdx)[k]? = some (key, k) := by
    rw [List.getElem?_zipIdx, hk]; simp
  obtain ⟨kk, hkk, hR⟩ := forall2_getElem? hF hzk
  obtain ⟨⟨ko, st, c, cx⟩, hkind, hR⟩ := bind_ok.1 hR
  cases pure_ok.1 hR
  have htests : ∀ (i : Nat) (y : Term × OwnKindOut × StepTerms × Term × Term), ks[i]? = some y →
      y.1.denote M = .bool (decide (i = k)) := by
    intro i y hy
    obtain ⟨⟨key', i'⟩, hz, hR'⟩ := forall2_getElem?_r hF hy
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
  have hcall := (holds_allT _).1 hc _ (List.mem_map.2 ⟨_, List.mem_of_getElem? hkk, rfl⟩)
  have htk := htests k _ hkk
  simp only [decide_true] at htk
  have hck : Holds M c := by
    have := (holds_ite _ _ _).1 hcall
    simpa [htk, toBool_bool] using this
  have hcxk : Holds M cx := (holds_allT _).1 hcodes _ (List.mem_map.2 ⟨_, List.mem_of_getElem? hkk, rfl⟩)
  obtain ⟨hfault, hrun⟩ := ownKind_rel hP hvx hshs hor a hinv hcd hqd hrd hed happ hca hE hPE hopt hrec hnow hfresh hn hq
    hms x hreach heff' hkey hkind hck hcxk
  have hwid : ∀ y ∈ ks.map (fun k => (k.1, k.2.2.1)),
      (∀ sl ∈ y.2.done.news, sl.2.length = 2) ∧ ∀ sl ∈ y.2.done.owns, sl.2.length = 2 := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    obtain ⟨⟨key', i'⟩, -, hR'⟩ := forall2_mem' hF z hz
    obtain ⟨⟨ko', st', c', cx'⟩, hkind', hR'⟩ := bind_ok.1 hR'
    cases pure_ok.1 hR'
    exact encodeOwnKind_width hkind'
  obtain ⟨hag, htab⟩ := fold_hit (e := v.event) (M := M) (L := L) ⟨tt, ⟨records, xs, n, [], [], q⟩, fresh⟩ ⟨rfl, rfl⟩
    (ks.map fun k => (k.1, k.2.2.1)) k (c := Term.share (.is dE ((L.effectsOf v.event).length + k) (Term.share eff)))
    (st := st) (by simp [hkk])
    (fun i y hy => by
      rw [List.getElem?_map] at hy
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hy
      exact htests i z hz)
    hwid
  rw [List.foldr_map] at hag htab
  have hfk : (OwnStepOut.fault? M ⟨ks.map fun k => (k.1, k.2.1),
      ks.foldr (fun k t => pickTerms k.1 k.2.2.1 t) ⟨tt, ⟨records, xs, n, [], [], q⟩, fresh⟩⟩) = ko.fault? M := by
    unfold OwnStepOut.fault?
    rw [find_hit (k := k) (ks.map fun k => (k.1, k.2.1))
      (y := (Term.share (.is dE ((L.effectsOf v.event).length + k) (Term.share eff)), ko)) (by simp [hkk])
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
    rintro ⟨fr, hfr, hdone⟩
    obtain ⟨-, ms, -, -, -, -, -, hms', -⟩ := id hdone
    refine ⟨fr, hag.fresh.trans hfr, internalDone_agrees hag (htab ?_) hdone⟩
    rw [machinesRel_length hms', machinesRel_length hms]

/-- The condition of one own kind's internal step is exact: for an own effect of the kind, it holds exactly when the
internal step `Step.runOwn` runs fits (`ownFits`). -/
theorem ownKind_exact {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    (hvm : ∀ m ∈ v.machines, m.Reach P) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true) (a : Step.Acc v)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hqout : ∀ x ∈ v.queries, x.output.isFn = false)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {records now fresh n q eff : Term} {xs : List Term} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ hrd a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    {j : Nat} {key : OwnKey} (x : EffectV v.event) (hreach : x.Reach P) {vals : List Val}
    (heff : eff.denote M = .ctor dE ((L.effectsOf v.event).length + j) vals) (hkey : key.Holds L x vals)
    {ko : OwnKindOut} {st : StepTerms} {c cx : Term}
    (henc : encodeOwnKind L T P v shs dE dP dopt (L.effectsOf v.event).length apply records now fresh n q eff xs j key =
      .ok (ko, st, c, cx))
    (hcx : Holds M cx) :
    Holds M c ↔ ownFits L.count T a.state x := by
  have hsel : ∀ i, (Term.sel dE ((L.effectsOf v.event).length + j) i eff).denote M = vals[i]?.getD default :=
    fun i => sel_ctor i heff
  obtain ⟨sh, hsh, henc⟩ := bind_ok.1 henc
  cases key with
  | command e name c0 i jj a0 =>
    cases x with
    | request => exact hkey.elim
    | query => exact hkey.elim
    | command name' c' i' j' caller value onAnswer =>
    obtain ⟨rfl, rfl, rfl, rfl, hsite, hΓ, vc, vi, va, rfl, hvc, hvi, hva⟩ := hkey
    unfold ownShape at hsh
    unfold ownFits
    dsimp only at hsh ⊢
    revert hsh
    generalize hoc : Ty.same c' v.caller = oc
    generalize hox : Step.ownCommand (v := v) name' i' j' = ox
    intro hsh
    have miss : ∀ (h : sh = .missing name'), Holds M c := by
      intro h; subst h; cases pure_ok.1 henc; exact holds_tt
    cases oc with
    | none =>
      cases ox <;>
      · dsimp only at hsh ⊢
        exact iff_of_true (miss (pure_ok.1 hsh).symm) trivial
    | some hc =>
    cases ox with
    | none =>
      dsimp only at hsh ⊢
      exact iff_of_true (miss (pure_ok.1 hsh).symm) trivial
    | some xx =>
    obtain ⟨hc⟩ := hc
    obtain ⟨x, hi, hj⟩ := xx
    subst hc hi hj
    dsimp only at hsh ⊢
    obtain ⟨⟨Γ, s⟩, hsf, hsh⟩ := bind_ok.1 hsh
    cases pure_ok.1 hsh
    obtain ⟨⟨cc, cx'⟩, hcc, henc⟩ := bind_ok.1 henc
    obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨da, dn⟩, hda, henc⟩ := bind_ok.1 henc
    obtain ⟨σ, hσ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c'⟩, hoe, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have hd := hcd x (ownCommand_mem hox)
    obtain ⟨hsP, hss, hsΓ⟩ := siteFor_spec (need_ok.1 hsf)
    obtain ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ := onAnswer
    dsimp only at hsite hΓ
    obtain ⟨e, hA⟩ := Fun.eq_siteFn hP ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ s hreach hsP (hsite.trans hss.symm)
    dsimp only at e hA
    subst e
    obtain ⟨d', n', vals', hd', rfl, hrds⟩ := hva
    obtain rfl := find_det hd' (need_ok.1 hda)
    have hσ' : Rels M L _ (Ty.up _ s.hΓ oenv) σ :=
      tupleCodes_rels _ [] vals' _ σ (by rw [hsel]; rfl) (relDs_up _ s.hΓ oenv vals' hrds) (need_ok.1 hσ)
    have hks' : callerTerms L hd.caller x.callers = some ks := by
      have h := need_ok.1 hks
      split at h
      · exact h
      · cases h
    have hsc : RelV L v.caller (Ty.up _ hd.caller caller)
        ((Term.sel dE ((L.effectsOf v.event).length + j) 0 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvc
    have hsi : RelV L x.input (Ty.up _ hd.input value)
        ((Term.sel dE ((L.effectsOf v.event).length + j) 1 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvi
    simp only [cast_eq]
    rw [show (⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ : Fun _) = s.fn oenv from hA]
    exact ownCommand_exact hP hvx hvm hshs hor a x caller value hd hcc hcx happ hca s oenv hσ'
      (tupleCodes_notFn _ _ _ (need_ok.1 hσ)) hks' hE hPE hopt hrec hnow hfresh hn hq hms hsc hsi hoe
  | query e name c0 i jj a0 =>
    cases x with
    | request => exact hkey.elim
    | command => exact hkey.elim
    | query name' c' i' j' caller value onAnswer =>
    obtain ⟨rfl, rfl, rfl, rfl, hsite, hΓ, vc, vi, va, rfl, hvc, hvi, hva⟩ := hkey
    unfold ownShape at hsh
    unfold ownFits
    dsimp only at hsh ⊢
    revert hsh
    generalize hoc : Ty.same c' v.caller = oc
    generalize hox : Step.ownQuery (v := v) name' i' j' = ox
    intro hsh
    have miss : ∀ (h : sh = .missing name'), Holds M c := by
      intro h; subst h; cases pure_ok.1 henc; exact holds_tt
    cases oc with
    | none =>
      cases ox <;>
      · dsimp only at hsh ⊢
        exact iff_of_true (miss (pure_ok.1 hsh).symm) trivial
    | some hc =>
    cases ox with
    | none =>
      dsimp only at hsh ⊢
      exact iff_of_true (miss (pure_ok.1 hsh).symm) trivial
    | some xx =>
    obtain ⟨hc⟩ := hc
    obtain ⟨x, hi, hj⟩ := xx
    subst hc hi hj
    dsimp only at hsh ⊢
    obtain ⟨⟨Γ, s⟩, hsf, hsh⟩ := bind_ok.1 hsh
    cases pure_ok.1 hsh
    obtain ⟨⟨cc, cx'⟩, hcc, henc⟩ := bind_ok.1 henc
    obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨da, dn⟩, hda, henc⟩ := bind_ok.1 henc
    obtain ⟨σ, hσ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c'⟩, hoe, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have hd := hqd x (ownQuery_mem hox)
    obtain ⟨hsP, hss, hsΓ⟩ := siteFor_spec (need_ok.1 hsf)
    obtain ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ := onAnswer
    dsimp only at hsite hΓ
    obtain ⟨e, hA⟩ := Fun.eq_siteFn hP ⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ s hreach hsP (hsite.trans hss.symm)
    dsimp only at e hA
    subst e
    obtain ⟨d', n', vals', hd', rfl, hrds⟩ := hva
    obtain rfl := find_det hd' (need_ok.1 hda)
    have hσ' : Rels M L _ (Ty.up _ s.hΓ oenv) σ :=
      tupleCodes_rels _ [] vals' _ σ (by rw [hsel]; rfl) (relDs_up _ s.hΓ oenv vals' hrds) (need_ok.1 hσ)
    have hks' : callerTerms L hd.caller x.callers = some ks := by
      have h := need_ok.1 hks
      split at h
      · exact h
      · cases h
    have hsc : RelV L v.caller (Ty.up _ hd.caller caller)
        ((Term.sel dE ((L.effectsOf v.event).length + j) 0 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvc
    have hsi : RelV L x.input (Ty.up _ hd.input value)
        ((Term.sel dE ((L.effectsOf v.event).length + j) 1 eff).denote M) := by
      rw [hsel]; exact relD_up _ _ _ _ hvi
    simp only [cast_eq]
    rw [show (⟨os, oG, odefs, oΓ, oenv, ohΓ, oht, obody⟩ : Fun _) = s.fn oenv from hA]
    exact ownQuery_exact a (fun m hm => (hor m hm).1) hed x caller value hd hcc hcx happ hca s oenv hσ'
      (tupleCodes_notFn _ _ _ (need_ok.1 hσ)) (hqout x (ownQuery_mem hox)) hks' hrec hnow hfresh hms hsc hsi hoe

/-- The condition of an own effect's internal step is exact: it holds exactly when the internal step `Step.runOwn`
runs fits (`ownFits`). -/
theorem ownStep_exact {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    (hvm : ∀ m ∈ v.machines, m.Reach P) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true) (a : Step.Acc v)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hqout : ∀ x ∈ v.queries, x.output.isFn = false)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {records now fresh n q eff : Term} {xs : List Term} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ hrd a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    (x : EffectV v.event) (hx : RelV L (.dsl .effect [v.event]) x (eff.denote M)) (hown : x.isRequest = false)
    (hreach : x.Reach P)
    {o : OwnStepOut} {cond codes : Term}
    (henc : encodeOwnStep L T P v shs dE dP dopt apply records now fresh n q eff xs = .ok (o, cond, codes))
    (hcodes : Holds M codes) :
    Holds M cond ↔ ownFits L.count T a.state x := by
  obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hx' : EffRel L x (eff.denote M) := hx
  obtain ⟨d, nn, hd, hx'⟩ := hx'
  cases (Prod.mk.inj (Option.some.inj (hE.symm.trans hd))).1
  rcases hx' with ⟨k, key, vals, -, -, hh⟩ | ⟨k, key, vals, hk, heff, hkey⟩
  · cases x with
    | request => simp [EffectV.isRequest] at hown
    | command => exact hh.elim
    | query => exact hh.elim
  have hF := mapM_ok _ _ _ hks
  have heff' : (Term.share eff).denote M = .ctor dE ((L.effectsOf v.event).length + k) vals := by
    rw [Term.denote_share]; exact heff
  have hzk : ((L.ownsOf v.event).zipIdx)[k]? = some (key, k) := by
    rw [List.getElem?_zipIdx, hk]; simp
  obtain ⟨kk, hkk, hR⟩ := forall2_getElem? hF hzk
  obtain ⟨⟨ko, st, c, cx⟩, hkind, hR⟩ := bind_ok.1 hR
  cases pure_ok.1 hR
  have htests : ∀ (i : Nat) (y : Term × OwnKindOut × StepTerms × Term × Term), ks[i]? = some y →
      y.1.denote M = .bool (decide (i = k)) := by
    intro i y hy
    obtain ⟨⟨key', i'⟩, hz, hR'⟩ := forall2_getElem?_r hF hy
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
  rw [← ownKind_exact hP hvx hvm hshs hor a hcd hqd hqout hrd hed happ hca hE hPE hopt hrec hnow hfresh hn hq hms x
    hreach heff' hkey hkind hcxk, holds_allT]
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

end

end Tazuna.Smt
