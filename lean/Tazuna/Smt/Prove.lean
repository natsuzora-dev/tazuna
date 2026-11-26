import Tazuna.Smt.Step
import Tazuna.Smt.Solver

/-! The questions `prove` asks the solver. A target is one named rule: a service invariant, a machine's instance
invariant, or a command's `ensures`. For each kind of input that can break it, one question asks for a state of the
right shape (its slots well-formed, every wire id below the next, every invariant holding) and an input whose step
breaks the target: induction's step, with the counterexample to induction read from the model (Ivy, Apalache's
`--inv` induction checks). The initial state is concrete, so the base case is evaluation, not a question. A second
question per input kind asks whether such a state can make the step leave the slots or a side condition fail; then
the step questions do not cover every step, and the verdict cannot be Proved. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- A term with the value of field `j` of constructor `k` of datatype `d` of `a` in every model, found within `fuel`
steps. -/
def Term.fieldF : Nat → (d k j : Nat) → Term → Option Term
  | 0, _, _, _, _ => none
  | f + 1, d, k, j, a => match a with
    | .ctor d' k' args => if d' = d ∧ k' = k then args[j]? else none
    | .shared _ b => Term.fieldF f d k j b
    | .sel d2 k2 j2 b => (Term.fieldF f d2 k2 j2 b).bind (Term.fieldF f d k j)
    | _ => none

/-- The value a term has in every model, found within `fuel` steps: literals, constructors of such terms, a
selector on a constructor term (its argument, whatever the others are), branches and connectives one argument
decides. -/
def Term.constF : Nat → Term → Option Val
  | 0, _ => none
  | f + 1, t => match t with
    | .int n => some (.int n)
    | .str s => some (.str s)
    | .bool b => some (.bool b)
    | .not a => (a.constF f).map fun w => .bool !w.toBool
    | .and a b => match a.constF f, b.constF f with
      | some x, some y => some (.bool (x.toBool && y.toBool))
      | some x, none => if x.toBool then none else some (.bool false)
      | none, some y => if y.toBool then none else some (.bool false)
      | none, none => none
    | .or a b => match a.constF f, b.constF f with
      | some x, some y => some (.bool (x.toBool || y.toBool))
      | some x, none => if x.toBool then some (.bool true) else none
      | none, some y => if y.toBool then some (.bool true) else none
      | none, none => none
    | .ite c a b => (c.constF f).bind fun w => if w.toBool then a.constF f else b.constF f
    | .ctor d k args => (args.mapM (Term.constF f)).map (.ctor d k)
    | .sel d k j a => (Term.fieldF f d k j a).bind (Term.constF f)
    | .shared _ a => a.constF f
    | _ => none

/-- `Term.constF` with fuel for any term `prove` reads a name from. -/
def Term.const? (t : Term) : Option Val := t.constF 256

theorem Term.denotes_getElem (M : Model) : (ts : List Term) → {j : Nat} → {x : Term} → ts[j]? = some x →
    (Term.denotes M ts)[j]? = some (x.denote M)
  | [], _, _, h => by simp at h
  | t :: ts, 0, _, h => by simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; rfl
  | _ :: ts, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h
    simpa [Term.denotes] using Term.denotes_getElem M ts h

theorem Term.fieldF_denote (M : Model) : (f d k j : Nat) → (a : Term) → {x : Term} → Term.fieldF f d k j a = some x →
    (Term.sel d k j a).denote M = x.denote M
  | 0, _, _, _, _, _, h => by simp [Term.fieldF] at h
  | f + 1, d, k, j, a, x, h => by
    cases a with
    | ctor d' k' args =>
      simp only [Term.fieldF] at h
      split at h
      · rename_i hdk
        obtain ⟨rfl, rfl⟩ := hdk
        simp [Term.denote, Term.denotes_getElem M args h]
      · cases h
    | shared hh b =>
      simp only [Term.fieldF] at h
      simpa [Term.denote] using Term.fieldF_denote M f d k j b h
    | sel d2 k2 j2 b =>
      simp only [Term.fieldF] at h
      obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.1 h
      have e1 := Term.fieldF_denote M f d2 k2 j2 b hy
      have e2 := Term.fieldF_denote M f d k j y h
      simp only [Term.denote] at e1 e2 ⊢
      rw [e1, e2]
    | _ => simp [Term.fieldF] at h

theorem Term.constF_denote (M : Model) : (f : Nat) → (t : Term) → {w : Val} → t.constF f = some w → t.denote M = w
  | 0, _, _, h => by simp [Term.constF] at h
  | f + 1, t, w, h => by
    have ih := Term.constF_denote M f
    cases t with
    | int _ | str _ | bool _ => simp only [Term.constF, Option.some.injEq] at h; subst h; rfl
    | not a =>
      simp only [Term.constF] at h
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
      simp [Term.denote, ih a hx]
    | and a b =>
      simp only [Term.constF] at h
      split at h
      · rename_i x y hx hy
        cases h; simp [Term.denote, ih a hx, ih b hy]
      · rename_i x hx _
        split at h
        · cases h
        · cases h; simp_all [Term.denote, ih a hx]
      · rename_i y _ hy
        split at h
        · cases h
        · cases h; simp_all [Term.denote, ih b hy]
      · cases h
    | or a b =>
      simp only [Term.constF] at h
      split at h
      · rename_i x y hx hy
        cases h; simp [Term.denote, ih a hx, ih b hy]
      · rename_i x hx _
        split at h
        · cases h; simp_all [Term.denote, ih a hx]
        · cases h
      · rename_i y _ hy
        split at h
        · cases h; simp_all [Term.denote, ih b hy]
        · cases h
      · cases h
    | ite c a b =>
      simp only [Term.constF] at h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
      simp only [Term.denote, ih c hx]
      split at h
      · simp_all [ih a h]
      · simp_all [ih b h]
    | ctor d k args =>
      simp only [Term.constF] at h
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.1 h
      clear h
      have : Term.denotes M args = ws := by
        induction args generalizing ws with
        | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hws; subst hws; rfl
        | cons a as iha =>
          simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at hws
          obtain ⟨y, hy, hws⟩ := Option.bind_eq_some_iff.1 hws
          obtain ⟨ys, hys, hws⟩ := Option.bind_eq_some_iff.1 hws
          cases hws
          simp [Term.denotes, ih a hy, iha _ hys]
      simp [Term.denote, this]
    | sel d k j a =>
      simp only [Term.constF] at h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
      rw [Term.fieldF_denote M f d k j a hx, ih x h]
    | shared _ a => simp only [Term.constF] at h; simp [Term.denote, ih a h]
    | _ => simp [Term.constF] at h

theorem Term.const?_denote (M : Model) (t : Term) {w : Val} (h : t.const? = some w) : t.denote M = w :=
  Term.constF_denote M 256 t h

/-- What `prove` shows a step never does: fault by breaking one named rule, or by a spec bug the cascade can make. A
rule is named by the literal the spec gives it; `none` stands for every rule whose name the spec computes from
values. -/
inductive Target where
  /-- A service invariant (`machine` none) or an instance invariant of the machine `machine`. -/
  | invariant (machine : Option String) (rule : Option String)
  /-- An `ensures` rule of the command, run as the input or as an internal step. -/
  | ensures (command : String) (rule : Option String)
  /-- More internal steps than the cascade bound: `Fault.cascadeLimit`. -/
  | cascade
  /-- An own effect asking the service's command or query `name` for what it does not accept, or the service lacking
  it: `Fault.invalidEffect`. -/
  | effect (name : String)
  /-- The machine's `after` setting a timer before the time it sets it at, which would let the timers due at one
  deadline of a clock line fire out of the order their deadlines give (T5's `Step.FiresForward`). -/
  | timer (machine : String)
  /-- Two waiting own effects of these kinds, `first` running first, ending otherwise than the other order (T5's
  `Step.PairCommutes`). `widened` names those of the two that only a send whose handle or `on_answer` is not written
  in place makes: such a send stands for every handle or site of its type, so no send may make the kind. -/
  | pair (first second : String) (widened : List String)
deriving DecidableEq, Repr

/-- Whether a step that faults with `f` breaks the target. -/
def Target.covers : Target → Fault → Bool
  | .invariant _ (some r), .invariant n => r == n
  | .invariant _ none, .invariant _ => true
  | .ensures _ (some r), .ensures n => r == n
  | .ensures _ none, .ensures _ => true
  | .cascade, .cascadeLimit => true
  | .effect c, .invalidEffect c' _ => c == c'
  | _, _ => false

/-- The name a rule's terms give it: none for a rule that holds in every model, the literal, or `some none` for a
name the model decides. -/
def ruleName? (rule : Term × Term) : Option (Option String) :=
  if rule.2.const?.map Val.toBool = some true then none
  else match rule.1.const? with
    | some (.str s) => some (some s)
    | _ => some none

/-- The items, each once, in their order. -/
def dedup {α : Type} [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) []

/-- The names of the rules, each once, in their order. -/
def ruleNames (rules : List (Term × Term)) : List (Option String) := dedup (rules.filterMap ruleName?)

/-- Whether a rule of the name `sel` is broken. -/
def brokenT (sel : Option String) (rules : List (Term × Term)) : Term :=
  anyT (rules.filterMap fun r => if ruleName? r = some sel then some (.not r.2) else none)

/-- Whether an instance's rule of the name `sel` is broken. -/
def instBrokenT (sel : Option String) (checks : List InstCheck) : Term :=
  anyT (checks.map fun c => .and c.occupied (brokenT sel c.rules))

/-- Whether every instance's rules hold. -/
def instHoldT (checks : List InstCheck) : Term :=
  allT (checks.map fun c => .or (.not c.occupied) (allT (c.rules.map (·.2))))

/-- The invariant targets of a step's end: the names of the service's rules, then each machine's. They are read from
the end, not from the state before, since a rule broken there is what the step's fault names. -/
def invariantTargets {v : ServiceV} (rules : List (Term × Term)) (checks : PerMachine (fun _ => List InstCheck) v.machines) :
    List Target :=
  (ruleNames rules).map (.invariant none) ++
    checks.toSigma.flatMap fun ⟨m, cs⟩ => (ruleNames (cs.flatMap (·.rules))).map (.invariant (some m.name))

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}

/-- The types of an input's terms, in the order of its constants. -/
def SymInput.tys : SymInput v shs n → List Ty
  | .command i .. => [v.caller, (v.commands.get i).input]
  | .query i .. => [v.caller, (v.queries.get i).input]
  | .answer k .. => [.int, answerTy shs[k].output shs[k].rejection]
  | .unmatched t .. => [.int, t]
  | .event i _ => [(v.subscribes.get i).event]
  | .clock _ => [.int]

/-- The inputs whose step can break a rule, with their terms the constants from `v<b>` on: each command, an answer
at each pending shape and slot, each subscription, a clock line. A query or an answer that matches no request leaves
the state as it is. -/
def stepInputs (v : ServiceV) (shs : List (PendingShape v.event)) (n b : Nat) : List (SymInput v shs n) :=
  (List.finRange v.commands.length).map (fun i => .command i (.var b) (.var (b + 1))) ++
    (List.finRange shs.length).flatMap (fun k => (List.finRange n).map fun j => .answer k j (.var b) (.var (b + 1))) ++
    (List.finRange v.subscribes.length).map (fun i => .event i (.var b)) ++ [.clock (.var b)]

end

/-- Where a step gets to the check of its end, so a rule broken there is the step's fault: a command admitted,
accepted and with its `ensures` holding; an answer whose rules hold; a clock line forward and within the cascade
bound. -/
def StepOut.reached {v : ServiceV} : StepOut v → Term
  | .command o => andT o.callerOk (andT (allT (o.rules.map (·.2)))
      (andT o.decided.ok (allT (o.decided.ensures.map (·.2)))))
  | .answer o => allT (o.rules.map (·.2))
  | .clock o => andT o.forward (.not o.over)
  | _ => tt

/-- The end of the step, where it has one. -/
def StepOut.finish? {v : ServiceV} : StepOut v → Option (FinishOut v)
  | .command o => some o.finish
  | .answer o => some o.finish
  | .event o => some o.finish
  | .clock o => some o.finish
  | _ => none

/-- The rules of the machine `name` the checks of a step's end read. -/
def machineChecks {v : ServiceV} (name : String) (checks : PerMachine (fun _ => List InstCheck) v.machines) :
    List InstCheck :=
  checks.toSigma.flatMap fun ⟨m, cs⟩ => if m.name = name then cs else []

/-- Whether a step's end breaks the invariant rule `rule` of the service (`mach` none) or of the machine `mach`. -/
def FinishOut.broken {v : ServiceV} (fo : FinishOut v) (mach rule : Option String) : Term :=
  match mach with
  | none => brokenT rule fo.invariants
  | some m => instBrokenT rule (machineChecks m fo.checks)

/-- The invariant targets of a step's terms: those of its end. -/
def StepOut.invTargets {v : ServiceV} (o : StepOut v) : List Target :=
  match o.finish? with
  | some fo => invariantTargets fo.invariants fo.checks
  | none => []

section
variable {v : ServiceV}

/-- What an own kind's internal step can break: its `ensures` rules, and its input, caller or presence. -/
def OwnKindOut.targets : OwnKindOut v → List Target
  | .command name o => (ruleNames o.decided.ensures).map (.ensures name) ++ [.effect name]
  | .query name _ | .missing name => [.effect name]

/-- Whether the internal step breaks the target, as its fault names it (`OwnKindOut.fault?`). -/
def OwnKindOut.breaks : OwnKindOut v → Target → Term
  | .command name o, .ensures c rule =>
    if name = c then andT o.callerOk (andT (allT (o.rules.map (·.2))) (andT o.decided.ok (brokenT rule o.decided.ensures)))
    else .bool false
  | .command name o, .effect c => if name = c then .or (.not o.callerOk) (.not (allT (o.rules.map (·.2)))) else .bool false
  | .query name o, .effect c => if name = c then .or (.not o.callerOk) (.not (allT (o.rules.map (·.2)))) else .bool false
  | .missing name, .effect c => if name = c then tt else .bool false
  | _, _ => .bool false

/-- What the cascade can break: each own kind's targets, and its bound. -/
def SettleOut.targets (o : SettleOut v) : List Target :=
  o.steps.flatMap (fun st => st.2.kinds.flatMap (·.2.targets)) ++ [.cascade]

/-- Whether the cascade faults by the target: a place past the bound is occupied, or an internal step that runs
breaks it in the kind its effect is. -/
def SettleOut.breaks (o : SettleOut v) : Target → Term
  | .cascade => o.over
  | g => anyT (o.steps.map fun st => andT st.1 (anyT (st.2.kinds.map fun k => andT k.1 (k.2.breaks g))))

/-- What the input itself can break, where it is the command `cmd`: the command's `ensures` rules, or a clock line's
bound on firing rounds. -/
def StepOut.topTargets (o : StepOut v) (cmd : Option String) : List Target :=
  match o, cmd with
  | .command co, some c => (ruleNames co.decided.ensures).map (.ensures c)
  | .clock _, _ => [.cascade]
  | _, _ => []

/-- Whether the input itself breaks the target. -/
def StepOut.topBreaks (o : StepOut v) (cmd : Option String) : Target → List Term
  | .ensures c rule => match o with
    | .command co => if cmd = some c then
        [andT co.callerOk (andT (allT (co.rules.map (·.2))) (andT co.decided.ok (brokenT rule co.decided.ensures)))]
      else []
    | _ => []
  | .cascade => match o with
    | .clock co => [andT co.forward co.over]
    | _ => []
  | _ => []

/-- What the step can break, where its input is the command `cmd`. -/
def StepOut.targets (o : StepOut v) (cmd : Option String) : List Target :=
  o.invTargets ++ o.topTargets cmd ++ match o.finish? with
    | some fo => fo.settle.targets
    | none => []

/-- Whether the step breaks the target, where its input is the command `cmd`: an invariant at the step's end, or a
fault of the input itself or of the cascade once the step gets to its end. -/
def StepOut.breaks (o : StepOut v) (cmd : Option String) : Target → Term
  | .invariant mach rule => match o.finish? with
    | some fo => andT o.reached (andT (.not fo.settle.faultT) (fo.broken mach rule))
    | none => .bool false
  | g => anyT (o.topBreaks cmd g ++ match o.finish? with
    | some fo => [andT o.reached (fo.settle.breaks g)]
    | none => [])

end

/-- The command an input names. -/
def SymInput.command? {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat} : SymInput v shs n → Option String
  | .command i .. => some (v.commands.get i).name
  | _ => none

/-- A question's script with the types its variables hold, and the context its family assumes kept apart from the
question's own assertions: `Unsat` reads the types from it, and smt-check asks the context alone to be sat. The
builders declare `vars` as the sorts of `tys`. -/
structure TypedScript where
  datatypes : List Datatype
  tys : List Ty
  vars : List Srt
  context : List Term
  asserts : List Term

/-- The script the solver reads: the context, then the question's assertions; a sat answer shows every variable. -/
def TypedScript.script (q : TypedScript) : Script :=
  { datatypes := q.datatypes, vars := q.vars, asserts := q.context ++ q.asserts, shows := List.range q.tys.length }

/-- The script of the context alone. -/
def TypedScript.contextScript (q : TypedScript) : Script := { q.script with asserts := q.context }

/-- One question to the solver: the input kind it is about, the target it asks to break (none: whether a step of
the kind can leave the slots or a side condition fail), and its script. -/
structure Question (v : ServiceV) (shs : List (PendingShape v.event)) (n : Nat) where
  input : SymInput v shs n
  target : Option Target
  ask : TypedScript

abbrev Question.script {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat} (q : Question v shs n) : Script :=
  q.ask.script

/-- The types of the state's terms, in the order of `SymState.vars`. -/
def stateTys (v : ServiceV) (shs : List (PendingShape v.event)) : List Ty :=
  [v.records, .int, .int, .int, pendingTable shs] ++ v.machines.map (·.table)

/-- How many variables the state takes: an input's variables, and a pair's effects, come after them. -/
def stateWidth (v : ServiceV) : Nat := (stateTys v (shapes v)).length

theorem stateWidth_eq (v : ServiceV) : stateWidth v = 5 + v.machines.length := by
  simp [stateWidth, stateTys]; omega

section
variable (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))

/-- The targets of a service and their questions for one input kind, from the state at `v0` on and the input's
terms after it. Every question asserts the state's and the input's shape (well-formed slots, wire ids below the
next), so each model decodes, and the case it is about; a step question also the side conditions, the invariants on the state and the step's condition, and
the target broken; the bound question that the side conditions fail or, with the invariants, the step's condition.
So where every question is unsat, no state of that shape with its invariants holding has a step of the kind that
breaks the target. -/
def questions (inp : SymInput v (shapes v) senv.nT) :
    Except Refusal (List Target × List (Question v (shapes v) senv.nT)) := do
  let S : SymState v := SymState.vars 0
  let t ← encodeStep L T P v senv S inp
  let wf ← need (.layout (.type v.records)) (S.wf L (shapes v))
  let iwf ← need (.layout (.type v.records)) (inp.wf L)
  let below ← pendingBelowT L (shapes v) S.pending S.nextId
  let (inv, ci0) ← v.invariants.code L
  let (rules, ci) ← encodeInvariants L inv S.records
  let (checks, ck) ← encodeInstChecks L T v.machines S.machines S.records S.now
  let held := andT (allT (rules.map (·.2))) (allT (checks.toList.map instHoldT))
  let side := andT t.codes (andT t.sites (andT ci0 (andT ci ck)))
  let tys := stateTys v (shapes v) ++ inp.tys
  let vars ← tys.mapM fun ty => need (.layout (.type ty)) (L.srt? ty)
  let dts ← need (.layout (.type v.records)) L.datatypes?
  let script (asserts : List Term) : TypedScript := ⟨dts, tys, vars, [wf, iwf, below, t.out.case], asserts⟩
  let cmd := inp.command?
  let targets := (dedup (t.out.targets cmd)).filter
    fun g => (t.out.breaks cmd g).const?.map Val.toBool != some false
  pure (targets, ⟨inp, none, script [.or (.not side) (andT held (.not t.cond))]⟩ ::
    targets.map fun g => ⟨inp, some g, script [side, held, t.cond, t.out.breaks cmd g]⟩)

/-- Every question about an input kind has the state's variables and then the input's. -/
theorem questions_tys {inp : SymInput v (shapes v) senv.nT} {gs : List Target} {qs : List (Question v (shapes v) senv.nT)}
    (hq : questions L T P v senv inp = .ok (gs, qs)) : ∀ q ∈ qs, q.ask.tys = stateTys v (shapes v) ++ inp.tys := by
  simp only [questions] at hq
  repeat (obtain ⟨_, -, hq⟩ := bind_ok.1 hq)
  cases pure_ok.1 hq
  intro q hq'
  simp only [List.mem_cons, List.mem_map] at hq'
  rcases hq' with rfl | ⟨g, -, rfl⟩ <;> rfl

end

end Tazuna.Smt
