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

def holdersOf (chosen : List (String × Transition)) : List String := dedupe (chosen.map (·.1))

/-- The states that transition `c` exits, by resource (SCXML computeExitSet). -/
def State.exitPairsOf (s : State) (c : String × Transition) : List (String × String) :=
  match s.machine? c.1 with
  | some i => (i.chart.exitsOf i.active c.2).map (c.1, ·)
  | none => []

def State.exitPairs (s : State) (chosen : List (String × Transition)) : List (String × String) := chosen.flatMap s.exitPairsOf

/-- The states that transition `c` enters, by resource (SCXML computeEntrySet). -/
def State.entryPairsOf (s : State) (c : String × Transition) : List (String × String) :=
  match s.machine? c.1 with
  | some i =>
    ((c.2.target.toList.flatMap (i.chart.tree.historyTargets i.chart.initial i.lastChildren)).flatMap (i.chart.tree.entrySet i.active i.depth)).map
      (c.1, ·)
  | none => []

def State.entryPairs (s : State) (chosen : List (String × Transition)) : List (String × String) :=
  chosen.flatMap s.entryPairsOf

def State.sharedMap (s : State) (a b : String × Transition) : Option String :=
  match ((s.machine? a.1).bind (·.copyOf)).map (·.map), ((s.machine? b.1).bind (·.copyOf)).map (·.map) with
  | some ma, some mb => if a.1 != b.1 && ma == mb then some ma else none
  | _, _ => none

def State.regionPairOf (s : State) (c : Chart) (a b : String × Transition) (j k : Nat) : Option RegionPair :=
  let pair (state : String) : RegionPair := { first := j, second := k, firstRef := a.2.ref, secondRef := b.2.ref, state }
  match s.sharedMap a b with
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
def State.regionPairs (s : State) (c : Chart) (chosen : List (String × Transition)) : List RegionPair :=
  chosen.zipIdx.flatMap fun (b, k) => (chosen.zipIdx.take k).filterMap fun (a, j) => s.regionPairOf c a b j k

/-- Each pair of each set with the index of its set, so that `lookup` finds the first set that contains a pair. -/
def transitionIndexOf (sets : List (List (String × String))) : List ((String × String) × Nat) :=
  sets.zipIdx.flatMap fun (set, k) => set.map (·, k)

def indexedInOrder (order : List (String × String)) (index : List ((String × String) × Nat)) :
    List ((String × String) × Nat) :=
  order.filterMap fun e => (index.lookup e).map (e, ·)

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def enterOne (st : Service) (step : Nat) (name n : String) : Processing → m Processing :=
  withMachine name fun i r => do
    MonadNote.note (.wroteState name n)
    let r := ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩
    let r ← runAssign fs st name (.entry n) (some n) .none r
    if r.halted then pure r else
    match i.chart.state? n with
    | none => pure r
    | some cs =>
      if cs.kind == .final then
        match cs.parent with
        | none =>
          if i.chart.screen then closeFinal fs st step name r
          else endWith (exitOne fs st Limit.exitDepth.max) name r
        | some parent => pure (enterFinal step name parent r)
      else do
      let deadlines ← fs.deadlines i.chart.name n
      pure ⟨addDeadlines name n deadlines r.state, if cs.activities.isEmpty then r.queue else r.queue.enter name n step⟩

/-- The processing after instance `name` enters `targets` (SCXML enterStates). -/
def enter (st : Service) (step : Nat) (name : String) (targets : List String) : Processing → m Processing :=
  withMachine name fun i r =>
    (i.chart.tree.entryOrder (targets.flatMap (i.chart.tree.entrySet i.active i.depth))).foldlM
      (fun r n => unlessHalted (enterOne fs st step name n) r) r

/--
The processing after one microstep of instance `name` (SCXML microstep). `chosen` holds each transition with the
resource (instance or copy) that takes it, in selection order. Owner and copy transitions run in one microstep,
including transitions of states that an earlier transition exited.
-/
def microstep (st : Service) (step : Nat) (name : String) (chosen : List (String × Transition)) (extra : Extra) :
    Processing → m Processing :=
  withMachine name fun i r => do
    if i.closed then pure r else
    let holders := holdersOf chosen
    let pairs := r.state.regionPairs i.chart chosen
    let exiting :=
      (indexedInOrder i.documentOrder (transitionIndexOf (chosen.map r.state.exitPairsOf))).reverse
    let s := holders.foldl (fun s h => s.setMachine h (recordHistory ((exiting.filter (·.1.1 == h)).map (·.1.2)))) r.state
    let r ← exiting.foldlM (fun r (e, k) => do
      MonadNote.note (.transitionPart k)
      unlessHalted (exitOne fs st Limit.exitDepth.max e.1 e.2) r) ⟨s, r.queue⟩
    let r ← chosen.zipIdx.foldlM (fun r (c, k) => do
      MonadNote.note (.transitionPart k)
      unlessHalted (runAssign fs st c.1 (.transition c.2) c.2.source extra) r) r
    let entering := indexedInOrder i.documentOrder (transitionIndexOf (chosen.map r.state.entryPairsOf))
    let r ← entering.foldlM (fun r (e, k) => do
      MonadNote.note (.transitionPart k)
      unlessHalted (enterOne fs st step e.1 e.2) r) r
    MonadNote.note (.microstepEnds
      { chart := st.ref i.chart.name, pairs, halted := r.halted })
    pure r

end

end Tazuna.Service
