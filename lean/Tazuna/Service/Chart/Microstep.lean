import Tazuna.Service.Chart.Done
import Tazuna.Service.Chart.Deadline
import Tazuna.Service.Chart.Request
import Tazuna.Service.Note

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

def setEntered (entered : List (String × Time)) (n : String) (t : Time) : List (String × Time) :=
  if entered.any (·.1 == n) then entered.map fun (k, v) => if k == n then (k, t) else (k, v)
  else entered ++ [(n, t)]

def holdersOf (chosen : List (InstanceId × Transition)) : List InstanceId := dedupe (chosen.map (·.1))

/-- The states that transition `c` exits, by resource (SCXML computeExitSet). -/
def State.exitPairsOf (s : State) (c : InstanceId × Transition) : List (InstanceId × String) :=
  match s.machine? c.1 with
  | some i => (i.chart.exitsOf i.active c.2).map (c.1, ·)
  | none => []

def State.exitPairs (s : State) (chosen : List (InstanceId × Transition)) : List (InstanceId × String) := chosen.flatMap s.exitPairsOf

/-- The states that transition `c` enters, by resource (SCXML computeEntrySet). -/
def State.entryPairsOf (s : State) (c : InstanceId × Transition) : List (InstanceId × String) :=
  match s.machine? c.1 with
  | some i =>
    ((c.2.target.toList.flatMap (i.chart.tree.historyTargets i.chart.initial i.lastChildren)).flatMap (i.chart.tree.entrySet i.active i.depth)).map
      (c.1, ·)
  | none => []

def State.entryPairs (s : State) (chosen : List (InstanceId × Transition)) : List (InstanceId × String) :=
  chosen.flatMap s.entryPairsOf

def sharedMap (a b : InstanceId × Transition) : Option String :=
  match a.1.map?, b.1.map? with
  | some ma, some mb => if a.1 != b.1 && ma == mb then some ma else none
  | _, _ => none

def regionPairOf (c : Chart) (a b : InstanceId × Transition) (j k : Nat) : Option RegionPair :=
  let pair (state : String) : RegionPair := { first := j, second := k, firstRef := a.2.ref, secondRef := b.2.ref, state }
  match sharedMap a b with
  | some map => some (pair map)
  | none =>
    match a.2.source, b.2.source with
    | some x, some y => (c.tree.parallelBetween x y).map pair
    | _, _ => none

/--
The pairs of transitions in different regions or copies within one microstep, which the run checks for conflicts.
SCXML lets the later write win, but regions act simultaneously and copies have no order, so write order has no meaning;
instead, as in Statemate (two writes, or a write and a read, of one value in a step conflict) and Esterel (a
single-valued signal emitted twice in a reaction is rejected), such pairs are conflicts.
-/
def regionPairs (c : Chart) (chosen : List (InstanceId × Transition)) : List RegionPair :=
  chosen.zipIdx.flatMap fun (b, k) => (chosen.zipIdx.take k).filterMap fun (a, j) => regionPairOf c a b j k

/-- Each pair of each set with the index of its set, so that `lookup` finds the first set that contains a pair. -/
def transitionIndexOf (sets : List (List (InstanceId × String))) : List ((InstanceId × String) × Nat) :=
  sets.zipIdx.flatMap fun (set, k) => set.map (·, k)

def indexedInOrder (order : List (InstanceId × String)) (index : List ((InstanceId × String) × Nat)) :
    List ((InstanceId × String) × Nat) :=
  order.filterMap fun e => (index.lookup e).map (e, ·)

section

variable [Monad m] [MonadNote m] (fs : Functions m)

/--
The processing after the edge `edge` of instance `name` fills the parameters of state `n`, which it enters, with its
`with`; `held` replaces the parameters that the expressions read, as in runAssign.
-/
def fillHeld (st : Service) (name : InstanceId) (n : String) (edge : Edge) (scope : Option String) (held : Option Value)
    (extra : Extra) : Processing → m Processing :=
  withMachine name fun i r => do
    let sc := r.state.scopeOf i scope
    match ← fs.held { sc with held := held.getD sc.held } r.state.records n edge extra with
    | .error e => pure (r.report (.fault (issueViolation (st.ref i.chart.name) e)))
    | .ok v =>
      pure ⟨r.state.setMachine name fun i => { i with held := i.held ++ [(n, v)] }, r.queue⟩

/--
The processing after transition `c` fills the parameters of its target with its `with`, when `entered`, the states that
`c` enters, holds a target that has parameters. The microstep runs it after the exits, so `held` holds the source's
parameters as the microstep began.
-/
def fillByTransition (st : Service) (c : InstanceId × Transition) (entered : List (InstanceId × String)) (held : Value)
    (extra : Extra) : Processing → m Processing :=
  withMachine c.1 fun i r =>
    match c.2.target with
    | none => pure r
    | some n =>
      if (i.chart.state? n).any (·.spec.hasParameters) && entered.contains (c.1, n) then
        fillHeld fs st c.1 n (.transition c.2) c.2.source (some held) extra r
      else pure r

/--
The processing after the parent's initial edge fills the parameters of state `n`, which it enters, unless `filled`: a
transition of the microstep targets `n` and filled them.
-/
def fillByInitial (st : Service) (filled : Bool) (name : InstanceId) (n : String) : Processing → m Processing :=
  withMachine name fun i r =>
    match i.chart.state? n with
    | some cs =>
      match cs.spec.parent with
      | some p => if cs.spec.hasParameters && !filled then fillHeld fs st name n (.initial p) (some p) none .none r else pure r
      | none => pure r
    | none => pure r

/-- The processing after instance `name` enters state `n`; `filled` is as in fillByInitial. -/
def enterOne (st : Service) (step : Nat) (filled : Bool) (name : InstanceId) (n : String) : Processing → m Processing :=
  withMachine name fun i r => do
    MonadNote.note (.wroteState name n)
    let r := ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩
    MonadNote.note (.reached (.state (st.ref i.chart.name) n))
    let r ← fillByInitial fs st filled name n r
    if r.halted then pure r else
    let r ← runAssign fs st name (.entry n) (some n) .none none r
    if r.halted then pure r else
    match i.chart.state? n with
    | none => pure r
    | some cs =>
      if cs.spec.kind == .final then
        match cs.spec.parent with
        | none =>
          if i.chart.screen then closeFinal fs st step name r
          else endWith (exitOne fs st st.exitFuel) name r
        | some parent => pure (enterFinal step name parent r)
      else do
      let s ← addDeadlines st fs step name n cs.spec.deadlines r.state
      pure ⟨s, if cs.activities.isEmpty then r.queue else r.queue.enter name n step⟩

/--
The processing after the content of the `k`-th chosen transition `c`: its `with` fills the parameters of its target,
then its assign runs. Both read `sourceHeld`, the parameters of each chosen transition's source as the microstep began.
`entries` holds the states that each chosen transition enters.
-/
def transitionContent (st : Service) (extra : Extra) (sourceHeld : List Value) (entries : List (List (InstanceId × String)))
    (r : Processing) (ck : (InstanceId × Transition) × Nat) : m Processing := do
  MonadNote.note (.transitionPart ck.2)
  let held := sourceHeld.getD ck.2 (.obj [])
  let r ← unlessHalted (fillByTransition fs st ck.1 (entries.getD ck.2 []) held extra) r
  unlessHalted (runAssign fs st ck.1.1 (.transition ck.1.2) ck.1.2.source extra (some held)) r

/-- Whether the `k`-th chosen transition targets state `e.2` of `e.1`, so that its `with` filled it. -/
def targetedBy (chosen : List (InstanceId × Transition)) (e : InstanceId × String) (k : Nat) : Bool :=
  chosen[k]?.any fun c => c.1 == e.1 && c.2.target == some e.2

/-- The processing after instance `name` enters `targets` (SCXML enterStates). -/
def enter (st : Service) (step : Nat) (name : InstanceId) (targets : List String) : Processing → m Processing :=
  withMachine name fun i r =>
    (i.chart.tree.entryOrder (targets.flatMap (i.chart.tree.entrySet i.active i.depth))).foldlM
      (fun r n => unlessHalted (enterOne fs st step false name n) r) r

/--
The processing after one microstep of instance `name` (SCXML microstep). `chosen` holds each transition with the
resource (instance or copy) that takes it, in selection order. Owner and copy transitions run in one microstep,
including transitions of states that an earlier transition exited.
-/
def microstep (st : Service) (step : Nat) (name : InstanceId) (chosen : List (InstanceId × Transition)) (extra : Extra) :
    Processing → m Processing :=
  withMachine name fun i r => do
    if i.closed then pure r else
    chosen.forM fun c => MonadNote.note (.reached (.transition (st.ref i.chart.name) c.2.ref))
    let holders := holdersOf chosen
    let pairs := regionPairs i.chart chosen
    let sourceHeld := chosen.map fun c => ((r.state.machine? c.1).map (·.heldAt c.2.source)).getD (.obj [])
    let exiting :=
      (indexedInOrder i.documentOrder (transitionIndexOf (chosen.map r.state.exitPairsOf))).reverse
    let s := holders.foldl (fun s h => s.setMachine h (recordHistory ((exiting.filter (·.1.1 == h)).map (·.1.2)))) r.state
    let r ← exiting.foldlM (fun r (e, k) => do
      MonadNote.note (.transitionPart k)
      unlessHalted (exitOne fs st st.exitFuel e.1 e.2) r) ⟨s, r.queue⟩
    let entries := chosen.map r.state.entryPairsOf
    let r ← chosen.zipIdx.foldlM (transitionContent fs st extra sourceHeld entries) r
    let entering := indexedInOrder i.documentOrder (transitionIndexOf entries)
    let r ← entering.foldlM (fun r (e, k) => do
      MonadNote.note (.transitionPart k)
      unlessHalted (enterOne fs st step (targetedBy chosen e k) e.1 e.2) r) r
    MonadNote.note (.microstepEnds
      { chart := st.ref i.chart.name, pairs, halted := r.halted })
    pure r

end

end Tazuna.Service
