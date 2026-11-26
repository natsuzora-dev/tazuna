import Tazuna.Smt.ShownStep

/-! The unrolled run: a script whose models are runs of `d` inputs from the initial state (bounded model checking,
as CBMC and Kani unroll). The initial state is constants, so the solver folds the first step. Each step is one input
kind chosen by a selector: the chosen kind's step encoding (`encodeStep`, T2) holds from the state before, its input
carries only names the service made or names from outside (`namesT`, `Input.Valid`), every id it carries that the
service made is one an earlier step's out lines showed (`SymInput.knownT`, `Input.Shown`), the step stays within the
slots (its condition) and does not fault. The state after is the chosen kind's end terms, one shared term per component,
which the next step reads as its state. A script stays linear in `d` because each component is defined once however
often later steps read it, and its only constants are the selectors and the inputs, whose values a run fixes one by
one: so every run is a model without any argument about which constants a term reads (`runs_covered`). An answer's
kinds (one per pending shape and slot) share one selector value and are told apart by the case each asks about, so
the selector's value is the input's kind, whichever slot holds the request. A goal on the steps (what generate or a
response asks) is the only part callers add, as the last assertion (`UnrollBase.withGoal`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}

/-- The input kinds a step of an unrolled run can take, each with how many constants its terms take and its terms
from a given constant on: each command, each query (which writes nothing, but answers), an answer at each pending
shape an answer can be to and slot where requests can wait (`answers`), each subscription, a clock line. An answer that matches no request
always faults, so it is no kind. -/
def unrollKinds (v : ServiceV) (shs : List (PendingShape v.event)) (n : Nat) (answers : Bool) :
    List (Nat × (Nat → SymInput v shs n)) :=
  (List.finRange v.commands.length).map (fun i => (2, fun b => .command i (.var b) (.var (b + 1)))) ++
    (List.finRange v.queries.length).map (fun i => (2, fun b => .query i (.var b) (.var (b + 1)))) ++
    (if answers then (answerShapes shs).flatMap fun k => (List.finRange n).map fun j =>
      (2, fun b => .answer k j (.var b) (.var (b + 1))) else []) ++
    (List.finRange v.subscribes.length).map (fun i => (1, fun b => .event i (.var b))) ++ [(1, fun b => .clock (.var b))]

/-- What an unrolled step's selector tells apart: a command, query or subscription by its index, an answer (any shape
and slot), a clock line. -/
inductive PickKind where
  | command (i : Nat)
  | query (i : Nat)
  | answer
  | event (i : Nat)
  | clock

/-- The selector's value for the kind. -/
def PickKind.pick (v : ServiceV) : PickKind → Nat
  | .command i => i
  | .query i => v.commands.length + i
  | .answer => v.commands.length + v.queries.length
  | .event i => v.commands.length + v.queries.length + 1 + i
  | .clock => v.commands.length + v.queries.length + 1 + v.subscribes.length

def SymInput.kind : SymInput v shs n → PickKind
  | .command i _ _ => .command i
  | .query i _ _ => .query i
  | .answer .. | .unmatched .. => .answer
  | .event i _ => .event i
  | .clock _ => .clock

/-- The value an unrolled step's selector takes for the input kind. -/
def SymInput.pick (x : SymInput v shs n) : Nat := x.kind.pick v

def _root_.Tazuna.Ir.Input.kind : Input v → PickKind
  | .command i _ _ => .command i
  | .query i _ _ => .query i
  | .answer .. => .answer
  | .event i _ => .event i
  | .clock _ => .clock

/-- The value a step's selector takes for the input's kind, as `SymInput.pick` reads a kind. -/
def _root_.Tazuna.Ir.Input.pick (x : Input v) : Nat := x.kind.pick v

/-- The kinds with their terms at consecutive constants from `b` on, and the constant after the last. -/
def placeKinds : List (Nat × (Nat → SymInput v shs n)) → Nat → List (SymInput v shs n) × Nat
  | [], b => ([], b)
  | (w, f) :: ks, b => let (xs, e) := placeKinds ks (b + w); (f b :: xs, e)

end

/-- The terms that each component of the state is `a`'s where `c` holds and `b`'s elsewhere. -/
def SymState.ite {v : ServiceV} (c : Term) (a b : SymState v) : SymState v :=
  ⟨.ite c a.records b.records, .ite c a.now b.now, .ite c a.fresh b.fresh, .ite c a.nextId b.nextId,
    .ite c a.pending b.pending, PerMachine.zipWith (Term.ite c) a.machines b.machines⟩

/-- Each component of the state as one shared term, which a script defines once however often it is read. -/
def SymState.share {v : ServiceV} (S : SymState v) : SymState v :=
  ⟨S.records.share, S.now.share, S.fresh.share, S.nextId.share, S.pending.share, S.machines.map Term.share⟩

/-- The state a step's end leaves where it does not fault: what the cascade leaves, the pending table it writes, and
the time `now`. -/
def FinishOut.state {v : ServiceV} (fo : FinishOut v) (now : Term) : SymState v :=
  ⟨fo.settle.terms.done.records, now, fo.settle.terms.fresh, fo.settle.terms.done.nextId, fo.pending,
    fo.settle.terms.done.tables⟩

/-- Whether a step's end does not fault: no internal step faults and no place past the bound is taken, and every
invariant of the service and every instance's holds on the state the cascade leaves. -/
def FinishOut.ok {v : ServiceV} (fo : FinishOut v) : Term :=
  andT (.not fo.settle.faultT) (andT (allT (fo.invariants.map (·.2))) (allT (fo.checks.toList.map instHoldT)))

/-- What a step of the kind does to the state `S`, read off its terms: whether it does not fault, and the state after
it. Where the step reaches its end the state is the end's; elsewhere it is Invalid or rejected (a command's still
takes a counter) or a query, and the state stays. -/
def StepOut.after {v : ServiceV} {n : Nat} (S : SymState v) : StepOut v → SymInput v (shapes v) n → Term × SymState v
  | .command o, _ =>
    let admitted := andT o.callerOk (andT (allT (o.rules.map (·.2))) o.decided.ok)
    let reached := andT admitted (allT (o.decided.ensures.map (·.2)))
    (andT (.or (.not admitted) (allT (o.decided.ensures.map (·.2)))) (.or (.not reached) o.finish.ok),
      SymState.ite reached (o.finish.state S.now) { S with fresh := .add S.fresh (.int 1) })
  | .query _, _ => (tt, S)
  | .answer o, _ =>
    let reached := allT (o.rules.map (·.2))
    (.or (.not reached) o.finish.ok, SymState.ite reached (o.finish.state S.now) S)
  | .unmatched _, _ => (.bool false, S)
  | .event o, _ => (o.finish.ok, o.finish.state S.now)
  | .clock o, .clock time =>
    (.or (.not o.forward) (andT (.not o.over) o.finish.ok), SymState.ite o.forward (o.finish.state time) S)
  | .clock _, _ => (.bool false, S)

section
variable (L : Layout) {v : ServiceV} {n : Nat}

/-- Every name the input's terms carry was made below the counter `fresh` or is from outside (`Input.Valid`). -/
def SymInput.validT (fresh : Term) : SymInput v (shapes v) n → Except Refusal Term
  | .command i caller input => do
    let c ← need (lacksData v.caller) (namesT L fresh v.caller caller)
    let x ← need (lacksData (v.commands.get i).input) (namesT L fresh (v.commands.get i).input input)
    pure (andT c x)
  | .query .. | .clock _ | .unmatched .. => pure tt
  | .answer k _ _ value =>
    let t := answerTy (shapes v)[k].output (shapes v)[k].rejection
    need (lacksData t) (namesT L fresh t value)
  | .event i value => need (lacksData (v.subscribes.get i).event) (namesT L fresh (v.subscribes.get i).event value)

/-- Every id the input's terms carry that the service made is the value of a position of `shown` whose condition
holds (`Input.Shown`). -/
def SymInput.knownT (shown : List (Term × Term)) : SymInput v (shapes v) n → Term
  | .command i caller input => andT (Smt.knownT L shown v.caller caller) (Smt.knownT L shown (v.commands.get i).input input)
  | .query i caller input => andT (Smt.knownT L shown v.caller caller) (Smt.knownT L shown (v.queries.get i).input input)
  | .answer k _ _ value => Smt.knownT L shown (answerTy (shapes v)[k].output (shapes v)[k].rejection) value
  | .event i value => Smt.knownT L shown (v.subscribes.get i).event value
  | .clock _ | .unmatched .. => tt

end

/-- Each condition and-ed with none of the ones before it holding: the first that holds is the only one whose result
holds. -/
def firstPicks : List Term → Term → List Term
  | [], _ => []
  | p :: ps, before => andT before p :: firstPicks ps (Term.share (andT before (.not p)))

/-- One step of an unrolled run: its selector, the states before and after, each kind it may take, with the kind's
terms, and the id positions its out lines show, each under the condition that the step takes the kind that shows it. -/
structure UnrollStep (v : ServiceV) (n : Nat) where
  sel : Term
  before : SymState v
  after : SymState v
  kinds : List (SymInput v (shapes v) n × EncodedStep v)
  shows : List (Term × Term)

/-- Whether the selector `sel` takes the kind: it names the kind's input kind and the model is in the case the kind's
terms ask about (for an answer, that its slot holds the request). -/
def selectsT {v : ServiceV} {n : Nat} (sel : Term) (k : SymInput v (shapes v) n × EncodedStep v) : Term :=
  andT (.eq sel (.int k.1.pick)) k.2.out.case

/-- Whether the step takes the kind (`selectsT` of its selector). -/
def UnrollStep.picks {v : ServiceV} {n : Nat} (st : UnrollStep v n) (k : SymInput v (shapes v) n × EncodedStep v) :
    Term :=
  selectsT st.sel k

/-- An unrolled run's script, its steps (what a goal reads and decoding needs) and the input kinds whose encoding was
refused, which the script therefore lacks. -/
structure Unrolled (v : ServiceV) (n : Nat) where
  ask : TypedScript
  steps : List (UnrollStep v n)
  refused : List (SymInput v (shapes v) n × Refusal)

/-- An unrolled run before its goal: the datatypes, the types and sorts of its constants, its assertions, its steps
and the input kinds refused. -/
structure UnrollBase (v : ServiceV) (n : Nat) where
  datatypes : List Datatype
  tys : List Ty
  vars : List Srt
  asserts : List Term
  steps : List (UnrollStep v n)
  refused : List (SymInput v (shapes v) n × Refusal)

/-- The script of the run alone; `withGoal`'s script is it with the goal's assertion added. -/
def UnrollBase.script {v : ServiceV} {n : Nat} (B : UnrollBase v n) : Script :=
  ({ datatypes := B.datatypes, tys := B.tys, vars := B.vars, context := [], asserts := B.asserts } : TypedScript).script

/-- The unrolled run with `goal`, a term on its steps, as its last assertion. -/
def UnrollBase.withGoal {v : ServiceV} {n : Nat} (B : UnrollBase v n) (goal : Term) : Unrolled v n :=
  ⟨⟨B.datatypes, B.tys, B.vars, [], B.asserts ++ [goal]⟩, B.steps, B.refused⟩

/-- The goal is the unrolled script's last assertion: a model of the script's assertions is one of the run's and of the
goal, and back. -/
theorem UnrollBase.holds_withGoal {v : ServiceV} {n : Nat} {M : Model} (B : UnrollBase v n) (goal : Term) :
    (∀ a ∈ (B.withGoal goal).ask.script.asserts, Holds M a) ↔ (∀ a ∈ B.asserts, Holds M a) ∧ Holds M goal := by
  simp [UnrollBase.withGoal, TypedScript.script, or_imp, forall_and]

section
variable (L : Layout)

/-- The collection of type `c` holding the items, in its slots, with the default items in the free ones; none when
they do not fit. -/
def collT (c : Ty) (item : List Ty) (xs : List (SlotItems item.length)) : Option Term := do
  let (d, n) ← L.find? c
  let (dt, _) ← L.find? (.tuple (Ty.bool :: item))
  let dflt ← (defaultItems L item).toOption
  if xs.length ≤ n then some (slotsTerm d dt (xs.map (tt, ·) ++ List.replicate (n - xs.length) (.bool false, dflt)))
  else none

mutual
/-- The constant term of a value: what `embedV` gives, as a term, with every free slot holding its sort's default
items, so the term is well sorted. -/
def dataT : (t : Ty) → t.den → Option Term
  | .int, n => some (.int n)
  | .str, s => some (.str s)
  | .date, n => some (.int n)
  | .dsl .fresh _, n => some (.int (Int.ofNat n))
  | .id, x => (L.find? .id).map fun (d, _) => (idVal d x).term
  | .adt 0 _ [[], []], x => some (.bool (altsBool x))
  | .adt (i + 1) a vs, x => match L.find? (.adt (i + 1) a vs) with
    | some (d, _) => dataAlts d 0 vs x
    | none => none
  | .tuple ts, x => match L.find? (.tuple ts) with
    | some (d, _) => (dataTs ts x).map (.ctor d 0)
    | none => none
  | .bag t, xs => (xs.mapM fun x => (dataT t x).map fun a => (⟨[a], rfl⟩ : SlotItems 1)).bind (collT L (.bag t) [t])
  | .list t, xs => (xs.mapM fun x => (dataT t x).map fun a => (⟨[a], rfl⟩ : SlotItems 1)).bind (collT L (.list t) [t])
  | .table k w, x =>
    (x.1.mapM fun e => (dataT k e.1).bind fun a => (dataT w e.2).map fun b => (⟨[a, b], rfl⟩ : SlotItems 2)).bind
      (collT L (.table k w) [k, w])
  | _, _ => none
def dataTs : (ts : List Ty) → Ty.dens ts → Option (List Term)
  | [], _ => some []
  | t :: ts, (x, xs) => (dataT t x).bind fun a => (dataTs ts xs).map (a :: ·)
def dataAlts (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Ty.alts vs → Option Term
  | k, fs :: _, .inl x => (dataTs fs x).map (.ctor d k)
  | k, _ :: vs, .inr y => dataAlts d (k + 1) vs y
end

/-- The initial state as constants: the initial records, no instance, no pending request, time and counters 0. -/
def initState (v : ServiceV) : Option (SymState v) := do
  let r ← dataT L v.records (Ty.up _ v.records_data v.init)
  let p ← collT L (pendingTable (shapes v)) [.dsl .fresh [], pendingEntry (shapes v)] []
  let tables ← tablesOf v.machines
  pure ⟨r, .int 0, .int 0, .int 0, p, tables⟩
where
  tablesOf : (ms : List (MachineV v.records v.event)) → Option (PerMachine (fun _ => Term) ms)
    | [] => some .nil
    | m :: ms => match m.table with
      | .table k w => (collT L (.table k w) [k, w] []).bind fun t => (tablesOf ms).map (.cons t)
      | _ => none

end

section
variable (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))

/-- What one input kind adds to a step of an unrolled run from `S` with the selector `sel`, after the steps whose out
lines show `shown`: the kind and the condition that it is the one taken (`picks`), the assertion that where it is taken
its step from `S` holds with a well-formed input of valid names whose made ids are shown, stays within the slots and
does not fault, and the state its step leaves; or the refusal of its encoding. -/
def unrollKind (S : SymState v) (shown : List (Term × Term)) (sel : Term) (inp : SymInput v (shapes v) senv.nT) :
    Except (SymInput v (shapes v) senv.nT × Refusal) ((SymInput v (shapes v) senv.nT × EncodedStep v) × Term × Term ×
      SymState v) :=
  match encodeStep L T P v senv S inp, inp.validT L S.fresh, need (lacksDatas inp.dataTys) (inp.wf L) with
  | .ok t, .ok valid, .ok wf =>
    let (ok, after) := t.out.after S inp
    let picks := selectsT sel (inp, t)
    .ok ((inp, t), picks,
      .or (.not picks) (andT wf (andT t.codes (andT t.sites (andT t.cond (andT ok (andT valid (inp.knownT L shown))))))),
      after)
  | .error r, _, _ | _, .error r, _ | _, _, .error r => .error (inp, r)

/-- One step of an unrolled run, step `i` (from 0) from `S` after steps whose out lines show `shown`, with its selector
at the constant `b`, then its kinds' inputs: the types of its constants, its assertions (each kind's, then that one
kind is taken), the step, the kinds refused, and the constant after its last. The state after is the taken kind's (`S`
where none is, which the last assertion rules out), and so are the ids it shows. Answers are no kind of the first
step, since no request waits in the initial state. -/
def unrollOne (S : SymState v) (shown : List (Term × Term)) (i b : Nat) :
    List Ty × List Term × UnrollStep v senv.nT × List (SymInput v (shapes v) senv.nT × Refusal) × Nat :=
  let sel : Term := .var b
  let (inps, e) := placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1)
  let rs := inps.map fun inp => unrollKind L T P v senv S shown sel inp
  let oks := rs.filterMap fun | .ok x => some x | .error _ => none
  let refused := rs.filterMap fun | .error x => some x | .ok _ => none
  let S' := (oks.foldr (fun x r => SymState.ite x.2.1 x.2.2.2 r) S).share
  let shows := (oks.zip (firstPicks (oks.map (·.2.1)) tt)).flatMap fun (x, g) => guardIds g (x.1.2.out.shownT L x.1.1)
  ([.int] ++ inps.flatMap (·.tys), oks.map (·.2.2.1) ++ [anyT (oks.map (·.2.1))], ⟨sel, S, S', oks.map (·.1), shows⟩,
    refused, e)

/-- The `d` steps of an unrolled run from step `i`, from `S` after steps whose out lines show `shown`, with the first
selector at the constant `b`. -/
def unrollSteps (S : SymState v) (shown : List (Term × Term)) (i b : Nat) :
    Nat → List Ty × List Term × List (UnrollStep v senv.nT) × List (SymInput v (shapes v) senv.nT × Refusal)
  | 0 => ([], [], [], [])
  | d + 1 =>
    let (tys, asserts, st, refused, b') := unrollOne L T P v senv S shown i b
    let (tys', asserts', sts, refused') := unrollSteps st.after (shown ++ st.shows) (i + 1) b' d
    (tys ++ tys', asserts ++ asserts', st :: sts, refused ++ refused')

/-- The runs of `d` inputs from the initial state, before a goal: what every goal at that depth shares. -/
def unrollBase (d : Nat) : Except Refusal (UnrollBase v senv.nT) := do
  -- The initial records have a term where they fit the slots (`embedV`); else a bound is below them.
  let S0 ← need (if (embedV L v.records (Ty.up _ v.records_data v.init)).isSome then .layout (.type v.records)
    else .limit (.slots v.records)) (initState L v)
  let dts ← need (.layout (.type v.records)) L.datatypes?
  let r := unrollSteps L T P v senv S0 [] 0 0 d
  let vars ← r.1.mapM fun ty => need (lacks ty) (L.srt? ty)
  pure ⟨dts, r.1, vars, r.2.1, r.2.2.1, r.2.2.2⟩

end

/-- The kind a step of an unrolled run takes in the model: the first it picks. The state after the step is that
kind's, and a goal reads that kind's terms. -/
def UnrollStep.taken {v : ServiceV} {n : Nat} (M : Model) (st : UnrollStep v n) :
    Option (SymInput v (shapes v) n × EncodedStep v) :=
  st.kinds.find? fun k => (st.picks k).denote M |>.toBool

/-- The input each step of an unrolled run took in the model: the kind it takes, decoded. -/
def UnrollStep.decode {v : ServiceV} {n : Nat} (M : Model) (L : Layout) (hc : v.caller.isData = true)
    (st : UnrollStep v n) : Option (Input v) := do
  let (inp, _) ← st.taken M
  inp.decode M L hc

end Tazuna.Smt
