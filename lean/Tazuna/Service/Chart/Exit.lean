import Tazuna.Service.Chart.Queue

namespace Tazuna.Semantics

open Tazuna.Data

variable {m : Type → Type}

/-- The state with subscription `p` ended. Only a stale mock can answer an ended subscription. -/
def State.endSubscription (s : State) (p : Pending) : State :=
  let s : State := { s with pending := s.pending.map fun q => if q.id == p.id then { q with stale := true } else q }
  (s.write .out none (.unsubscribe p.id)).1

def State.openShows (s : State) (owner : String) : List Pending :=
  s.pending.filter fun p => p.requester.machine? == some owner && p.requester.slot?.isSome && !p.stale

def setLastChildren (table : List (String × List String)) (n : String) (children : List String) :
    List (String × List String) :=
  if table.any (·.1 == n) then table.map fun (k, v) => if k == n then (k, children) else (k, v)
  else table ++ [(n, children)]

/--
Instance `i` with the history of each exiting state recorded. As in SCXML exitStates, the history is recorded before
any state is exited.
-/
def recordHistory (exiting : List String) (i : Instance) : Instance :=
  exiting.foldl (fun i n =>
    match i.chart.tree.recordedChildren i.active n with
    | some children => { i with lastChildren := setLastChildren i.lastChildren n children }
    | none => i) i

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def runAssign (st : Service) (name : String) (a : Assignment) (scope : Option String) (extra : Extra) :
    Processing → m Processing :=
  withMachine name fun i r => do
    match ← fs.assign (r.state.scopeOf i scope) r.state.records a extra r.state.nextKeys with
    | .error e =>
      pure (r.report (.fault (issueViolation st (st.ref i.chart.name) e fun
        | .mapContext _ map => .copyContextSchema (st.ref i.chart.name) map
        | _ => .contextSchema (st.ref i.chart.name))))
    | .ok (context, copyContext, keys) =>
      let s := r.state.createKeys keys
      match i.copyOf with
      | some c =>
        pure ⟨(s.setMachine c.owner fun o => { o with context }).setMachine name fun i =>
          { i with context := copyContext.getD i.context }, r.queue⟩
      | none => pure ⟨s.setMachine name fun i => { i with context }, r.queue⟩

/--
The processing after instance `c` exits every active state in exitOrder and then stops, as in SCXML exitInterpreter. A
closed instance stays in State, so an assign of a transition chosen by a copy that closed in the same microstep reads
the copy's values at exit.
-/
def endWith (exit : String → String → Processing → m Processing) (c : String) : Processing → m Processing :=
  withMachine c fun ci r => do
    let r ← (ci.chart.tree.exitOrder ci.active).foldlM (fun r n => unlessHalted (exit c n) r) r
    if r.halted then pure r else
    let s := r.state.setMachine c fun i => { i with closed := true }
    pure ⟨((s.openShows c).foldl (fun s p => s.endSubscription p) s).removeFromStack c, r.queue⟩

def leaveMark (name n : String) (p : Pending) : Pending :=
  if p.requester = .state name n then { p with stale := true } else p

def State.leaveState (s : State) (name n : String) : State :=
  let s := s.setMachine name fun i => { i with entered := i.entered.filter (·.1 != n) }
  { s with
    deadlines := s.deadlines.filter (fun t => !(t.machine == name && t.state == n)),
    pending := s.pending.map (leaveMark name n),
    queued := s.queued.map (fun q => if q.machine == name && q.state == n then { q with stale := true } else q) }

def State.childrenOf (s : State) (name n : String) : List String :=
  (s.machines.filter fun (c : Instance) => !c.closed && c.opener.any fun o => o.parent == name && o.state == n).map
    (·.resource)

def leaveWith (st : Service) (exit : String → String → Processing → m Processing) (name n : String)
    (r : Processing) : m Processing := do
  let r ← runAssign fs st name (.exit n) (some n) .none r
  if r.halted then pure r else
  MonadNote.note (.wroteState name n)
  let s := r.state.leaveState name n
  (s.childrenOf name n).foldlM (fun r c => unlessHalted (endWith exit c) r) ⟨s, r.queue⟩

/--
The processing after instance `name` exits state `n`, after the copies of `n`. The fuel is the remaining nesting depth
of exits.
-/
def exitOne (st : Service) : Nat → String → String → Processing → m Processing
  | 0, _, _, r => pure (r.report (.fault (.exceededExitDepth Limit.exitDepth.max)))
  | fuel + 1, name, n, r =>
    withMachine name (fun i r => do
      let r : Processing ←
        (i.copyKeysOf n).reverse.foldlM
          (fun r k => unlessHalted (endWith (exitOne st fuel) (copyName i.resource n k)) r) r
      if r.halted then pure r else
      leaveWith fs st (exitOne st fuel) name n
        ⟨r.state.setMachine name fun i => { i with copyKeys := i.copyKeys.filter (·.1 != n) }, r.queue⟩) r

end

end Tazuna.Semantics
