import Tazuna.Smt.Prove
import Tazuna.Smt.Names

/-! The unrolled run: a script whose models are runs of `d` inputs from the initial state (bounded model checking,
as CBMC and Kani unroll). The initial state is constants, so the solver folds the first step. Each later state is a
fresh set of constants (`SymState.vars` at its own offset), and each step is one input kind chosen by a selector:
the chosen kind's step encoding (`encodeStep`, T2) holds from the state before, its input carries only names the
service made or names from outside (`namesT`, `Input.Valid`), the step stays within the slots (its condition), does
not fault, and the state after equals the terms the step ends with. Fresh constants per state, instead of the next
step reading the terms of the one before, keep every depth one copy of each kind's terms, so a script grows linearly
in `d`; each depth is a step question's assertions with its state and input at other offsets. A goal on the steps
(what generate or a response asks) is the only part callers add. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}

/-- The input kinds a step of an unrolled run can take, each with how many constants its terms take and its terms
from a given constant on: each command, each query (which writes nothing, but answers), an answer at each pending
shape and slot where requests can wait (`answers`), each subscription, a clock line. An answer that matches no request
always faults, so it is no kind. -/
def unrollKinds (v : ServiceV) (shs : List (PendingShape v.event)) (n : Nat) (answers : Bool) :
    List (Nat × (Nat → SymInput v shs n)) :=
  (List.finRange v.commands.length).map (fun i => (2, fun b => .command i (.var b) (.var (b + 1)))) ++
    (List.finRange v.queries.length).map (fun i => (2, fun b => .query i (.var b) (.var (b + 1)))) ++
    (if answers then (List.finRange shs.length).flatMap fun k => (List.finRange n).map fun j =>
      (2, fun b => .answer k j (.var b) (.var (b + 1))) else []) ++
    (List.finRange v.subscribes.length).map (fun i => (1, fun b => .event i (.var b))) ++ [(1, fun b => .clock (.var b))]

/-- The kinds with their terms at consecutive constants from `b` on, and the constant after the last. -/
def placeKinds : List (Nat × (Nat → SymInput v shs n)) → Nat → List (SymInput v shs n) × Nat
  | [], b => ([], b)
  | (w, f) :: ks, b => let (xs, e) := placeKinds ks (b + w); (f b :: xs, e)

end

/-- The terms that each component of the state is `a`'s where `c` holds and `b`'s elsewhere. -/
def SymState.ite {v : ServiceV} (c : Term) (a b : SymState v) : SymState v :=
  ⟨.ite c a.records b.records, .ite c a.now b.now, .ite c a.fresh b.fresh, .ite c a.nextId b.nextId,
    .ite c a.pending b.pending, PerMachine.zipWith (Term.ite c) a.machines b.machines⟩

/-- Whether each component of the state is the other's. -/
def SymState.eqT {v : ServiceV} (a b : SymState v) : Term :=
  allT ([.eq a.records b.records, .eq a.now b.now, .eq a.fresh b.fresh, .eq a.nextId b.nextId, .eq a.pending b.pending] ++
    (PerMachine.zipWith Term.eq a.machines b.machines).toList)

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
    let c ← need (.layout (.type v.caller)) (namesT L fresh v.caller caller)
    let x ← need (.layout (.type (v.commands.get i).input)) (namesT L fresh (v.commands.get i).input input)
    pure (andT c x)
  | .query .. | .clock _ | .unmatched .. => pure tt
  | .answer k _ _ value =>
    let t := answerTy (shapes v)[k].output (shapes v)[k].rejection
    need (.layout (.type t)) (namesT L fresh t value)
  | .event i value => need (.layout (.type (v.subscribes.get i).event)) (namesT L fresh (v.subscribes.get i).event value)

end

/-- One step of an unrolled run: its selector, the states before and after, and each kind it may take, with the
selector's value that picks it and the kind's terms. -/
structure UnrollStep (v : ServiceV) (n : Nat) where
  sel : Term
  before : SymState v
  after : SymState v
  kinds : List (Nat × SymInput v (shapes v) n × EncodedStep v)

/-- An unrolled run's script, its steps (what a goal reads and decoding needs) and the input kinds whose encoding was
refused, which the script therefore lacks. -/
structure Unrolled (v : ServiceV) (n : Nat) where
  ask : TypedScript
  steps : List (UnrollStep v n)
  refused : List (SymInput v (shapes v) n × Refusal)

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

/-- The script of runs of `d` inputs from the initial state, with `goal` on its steps. Step `i` (from 0) has its
selector at the constant `b`, then its kinds' inputs, then the state after it. Answers are no kind of the first step,
since no request waits in the initial state. -/
def unroll (d : Nat) (goal : List (UnrollStep v senv.nT) → Term) : Except Refusal (Unrolled v senv.nT) := do
  let S0 ← need (.layout (.type v.records)) (initState L v)
  let dts ← need (.layout (.type v.records)) L.datatypes?
  let mut S := S0
  let mut b := 0
  let mut tys : List Ty := []
  let mut asserts : List Term := []
  let mut steps : List (UnrollStep v senv.nT) := []
  let mut refused : List (SymInput v (shapes v) senv.nT × Refusal) := []
  for i in List.range d do
    let sel : Term := .var b
    let (inps, e) := placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1)
    let S' : SymState v := SymState.vars e
    let mut kinds : List (Nat × SymInput v (shapes v) senv.nT × EncodedStep v) := []
    let mut picks : List Term := []
    for (inp, k) in inps.zipIdx do
      match encodeStep L T P v senv S inp, inp.validT L S.fresh, need (.layout (.type v.records)) (inp.wf L) with
      | .ok t, .ok valid, .ok wf =>
        let (ok, after) := t.out.after S inp
        kinds := kinds ++ [(k, inp, t)]
        picks := picks ++ [.eq sel (.int k)]
        asserts := asserts ++ [.or (.not (.eq sel (.int k)))
          (andT wf (andT t.codes (andT t.sites (andT t.out.case (andT t.cond (andT ok (andT valid (S'.eqT after))))))))]
      | .error r, _, _ | _, .error r, _ | _, _, .error r => refused := refused ++ [(inp, r)]
    asserts := asserts ++ [anyT picks]
    tys := tys ++ [.int] ++ inps.flatMap (·.tys) ++ stateTys v (shapes v)
    steps := steps ++ [⟨sel, S, S', kinds⟩]
    S := S'
    b := e + stateWidth v
  let vars ← tys.mapM fun ty => need (.layout (.type ty)) (L.srt? ty)
  pure ⟨⟨dts, tys, vars, [], asserts ++ [goal steps]⟩, steps, refused⟩

end

/-- The input each step of an unrolled run took in the model: the kind its selector names, decoded. -/
def UnrollStep.decode {v : ServiceV} {n : Nat} (M : Model) (L : Layout) (hc : v.caller.isData = true)
    (st : UnrollStep v n) : Option (Input v) := do
  let .int k := st.sel.denote M | none
  let (_, inp, _) ← st.kinds.find? (·.1 == k.toNat)
  inp.decode M L hc

end Tazuna.Smt
