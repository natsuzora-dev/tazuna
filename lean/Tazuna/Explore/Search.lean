import Tazuna.Explore.Key
import Tazuna.Semantics.GenTarget
import Tazuna.Semantics.Response

/-! `explore`: breadth-first search over the states a service reaches from its initial state on the inputs a model's
scope generates (`Tazuna.Explore.Inputs`), as TLC searches a TLA+ spec (Specifying Systems, sec 14.3.1). Each state
reached is kept once per key (`Tazuna.Explore.Key`), the first time, so at its least depth. Every transition from a
state of a complete level is checked: the classes of out line its step shows, the fault it ends in, and each response
it breaks. A faulted step ends its run, as generate's runs end at their first fault. The search stops at the scope's
depth or once its state cap is reached, never by wall time, so what it covers is a function of the spec and the
model. -/

namespace Tazuna.Explore

open Tazuna.Ir Tazuna.Ir.Step

variable {v : ServiceV}

/-- A state explore keeps, with what a run that reached it may still use and what its responses wait for. -/
structure Node (v : ServiceV) where
  state : State v
  /-- The ids the service made that an out line showed and the state still holds, sorted and distinct: the only ones
  an input may carry (`Assumption.validInputs`). -/
  shown : List IdV
  /-- Per response, in the service's order, each trigger that waits for its answer with the time of the step that
  applied it; none once a clock line passed a waiting timer, as no response claims anything of such a run
  (`Assumption.timelyClock`). -/
  watch : Option (List (List (v.event.den0 × Int)))

/-- The initial node: the initial state, no id shown, no trigger waiting. -/
def Node.init (v : ServiceV) : Node v := ⟨State.init v, [], some (v.responses.map fun _ => [])⟩

/-- The order on ids explore keeps its lists in: the service's own before outside ones, each by its parts. -/
def IdV.le : IdV → IdV → Bool
  | .fresh c i, .fresh c' i' => c < c' || (c == c' && i ≤ i')
  | .fresh .., .named _ => true
  | .named _, .fresh .. => false
  | .named a, .named b => a.1 ≤ b.1

/-- Sorted and distinct. -/
def sortIds (xs : List IdV) : List IdV := (xs.mergeSort IdV.le).eraseDups

/-- The scope's value set for the input kind `kind` named `name`; none where it gives none, which tries no Int and no
String. -/
def valuesOf (sc : ScopeV) (kind name : String) : Option ValuesV :=
  sc.values.find? fun vs => vs.input.kind == kind && vs.input.name == name

/-- The first outside id whose name the ids do not use: the code names generate gives outside ids. -/
def newId (held : List IdV) : IdV :=
  let used := held.filterMap fun | .named s => some s.1 | .fresh .. => none
  let rec go : Nat → Nat → IdV
    | 0, _ => .named ⟨"", rfl⟩
    | fuel + 1, k =>
      let n := Smt.nameOf k
      if used.contains n then go fuel (k + 1) else match Str.of? n with
        | some s => .named s
        | none => go fuel (k + 1)
  go (used.length + 1) 0

/-- The ids an input may carry from a node: the shown ones, the outside ones its state holds, and a new outside one. -/
def Node.ids (n : Node v) : List IdV :=
  let held := n.shown ++ sortIds ((stateIds n.state).filter fun | .named _ => true | .fresh .. => false)
  held ++ [newId held]

-- A kind with no value set tries no Int and no String: the empty list is the meaning, as `tazuna.values` says.
set_option linter.tazuna.silentDefault false in
/-- The leaves an input of the kind tries from the node. -/
def domainOf (sc : ScopeV) (n : Node v) (kind name : String) : Domain :=
  let vs := valuesOf sc kind name
  { ints := (vs.map (·.ints)).getD [], strs := (vs.map (·.strings)).getD [], ids := n.ids,
    instants := n.state.now :: sc.waits.map (n.state.now + ·), items := sc.items.toNat }

/-- Whether a request kind is a command's: it has a rejection type. -/
def requestKind {e : Ty} (r : RequestV e) : String := if r.rejection.isSome then "external command" else "external query"

/-- The times explore moves the clock to from the node, ascending: the state's time plus each wait, and each deadline
the state holds and the millisecond after it, where a deadline is a timer's or the end of a waiting trigger's
`within`. A timer fires, and a response comes due, only as time reaches or passes such a deadline, so these times
tell apart every set of timers a clock line can fire and every response it can break (the region construction of
timed automata, Alur and Dill 1994). A time before the state's moves to the state's time, which fires every overdue
timer. -/
def clockTimes (sc : ScopeV) (n : Node v) : List Int :=
  let s := n.state
  let timers := s.machines.toSigma.flatMap fun ⟨_, insts⟩ => insts.filterMap fun i =>
    (timerOf s.records i).map (·.1)
  let dues := match n.watch with
    | none => []
    | some ws => (v.responses.zip ws).flatMap fun (resp, trs) => trs.map fun (_, t) => t + (resp.withinNat : Int)
  let times := sc.waits.map (s.now + ·) ++ (timers ++ dues).flatMap fun d => [d, d + 1]
  ((times.map (max s.now)).mergeSort (· ≤ ·)).eraseDups

/-- Every input explore tries from the node, in a fixed order: each command with each caller and input, each query
likewise, an answer of each value to each pending request in the order of their wire ids, each subscribed event,
then a clock line to each of `clockTimes`. -/
def inputsOf (sc : ScopeV) (n : Node v) : List (Input v) :=
  let s := n.state
  let commands := (List.finRange v.commands.length).flatMap fun i =>
    let d := domainOf sc n "command" (v.commands.get i).name
    (cands d v.caller).flatMap fun c => (cands d (v.commands.get i).input).map (.command i c ·)
  let queries := (List.finRange v.queries.length).flatMap fun i =>
    let d := domainOf sc n "query" (v.queries.get i).name
    (cands d v.caller).flatMap fun c => (cands d (v.queries.get i).input).map (.query i c ·)
  let answers := s.pending.flatMap fun p =>
    let t := answerTy p.request.output p.request.rejection
    (cands (domainOf sc n (requestKind p.request) p.request.name) t).map fun x => .answer p.id ⟨t, x⟩
  let events := (List.finRange v.subscribes.length).flatMap fun i =>
    (cands (domainOf sc n "source" (v.subscribes.get i).name) (v.subscribes.get i).event).map (.event i ·)
  commands ++ queries ++ answers ++ events ++ (clockTimes sc n).map .clock

section
variable (T : List TypeDecl)

/-- One response's waiting triggers after a step with the moment `m`: those it answers leave, those it opens and does
not answer join with the step's time, and those it comes past the deadline of leave too, as the run already broke the
response there (`late`). -/
def watchStep (resp : ResponseV v.records v.event) (m : Moment v.event) (trs : List (v.event.den0 × Int)) :
    Bool × List (v.event.den0 × Int) :=
  let late := trs.any fun (_, t) => decide (m.time > t + (resp.withinNat : Int))
  let kept := trs.filter fun (ev, t) => !decide (m.time > t + (resp.withinNat : Int)) && !resp.answers ev m
  let opened := (m.events.filter fun ev => resp.opens ev && !resp.answers ev m).map (·, m.time)
  (late, kept ++ opened)

/-- What one transition shows: the step's result, the responses it breaks (by index), and the node it reaches unless
it faults. -/
structure Move (v : ServiceV) where
  result : Result v
  broken : List Nat
  next : Option (Node v)

/-- The transition from the node on the input. -/
def move (n : Node v) (x : Input v) : Move v :=
  let r := step T v n.state x
  let watched : List Nat × Option (List (List (v.event.den0 × Int))) :=
    match n.watch with
    | none => ([], none)
    | some ws =>
      if timelyAt n.state x then
        let steps := (v.responses.zip ws).map fun (resp, trs) => watchStep resp r.moment trs
        ((steps.zipIdx.filter (·.1.1)).map (·.2), some (steps.map (·.2)))
      else ([], none)
  let held := stateIds r.state
  let shown := sortIds ((n.shown ++ (r.shownIds T).filter fun | .fresh .. => true | .named _ => false).filter
    held.contains)
  let next := match r.outcome with
    | .fault _ => none
    | _ => some ⟨r.state, shown, watched.2⟩
  ⟨r, watched.1, next⟩

end

/-- The step counters the node holds: in its state, in its waiting triggers and in its shown ids. -/
def Node.ctrs (n : Node v) : List Nat :=
  stateCtrs n.state ++ (n.watch.map fun ws => ws.flatMap fun trs => trs.flatMap fun (ev, _) => ctrsIn v.event ev).toList.flatten ++
    n.shown.flatMap (ctrsIn .id)

/-- How the node's key renames counters. -/
def Node.ctrRen (n : Node v) : Nat → Nat := renameBelow (belowOf n.ctrs n.state.fresh) n.state.fresh

/-- How the node's key renames wire ids. -/
def Node.wireRen (n : Node v) : Nat → Nat :=
  renameBelow (belowOf (n.state.pending.map (·.id)) n.state.nextId) n.state.nextId

/-- The node as a term, the same for two nodes exactly when they are the same once counters and wire ids are renamed
(`renameBelow`) and instants read relative to the state's time. -/
def Node.key (n : Node v) : Erl :=
  let s := n.state
  let σ := n.ctrRen
  let ω := n.wireRen
  let δ := -s.now
  .tuple [.int (belowOf n.ctrs s.fresh).size, .int (belowOf (s.pending.map (·.id)) s.nextId).size,
    keyBy σ δ v.records s.records,
    .list (s.machines.toSigma.map fun ⟨m, insts⟩ =>
      .list (insts.map fun i => .tuple [keyBy σ δ m.key i.key, keyBy σ δ m.state i.state])),
    .list (s.pending.map (pendingKey σ ω δ)),
    .list (n.shown.map (keyBy σ δ .id)),
    match n.watch with
    | none => .atom "untimely"
    | some ws => .list (ws.map fun trs =>
        .list (trs.map fun (ev, t) => .tuple [keyBy σ δ v.event ev, .int (t + δ)]))]

/-- A structural hash of a term. -/
partial def Erl.hash : Erl → UInt64
  | .int n => mixHash 1 (Hashable.hash n)
  | .atom s => mixHash 2 (Hashable.hash s)
  | .bin s => mixHash 3 (Hashable.hash s)
  | .tuple xs => xs.foldl (fun h x => mixHash h (Erl.hash x)) 4
  | .list xs => xs.foldl (fun h x => mixHash h (Erl.hash x)) 5
  | .map ks vs => vs.foldl (fun h x => mixHash h (Erl.hash x)) (ks.foldl (fun h x => mixHash h (Erl.hash x)) 6)

instance : Hashable Erl := ⟨Erl.hash⟩

/-- The first transition explore met that shows something: the run of its node's inputs and then its own. -/
structure Hit (v : ServiceV) where
  /-- The number of inputs of the run. -/
  depth : Nat
  /-- The order explore met it in, which breaks ties between equal depths. -/
  order : Nat
  node : Nat
  input : Input v

/-- What explore covered: every run of at most `depth` inputs on the scope's inputs, or of any length where
`exhausted` (no state was left to reach). `levels` counts the states first reached at each depth. -/
structure Coverage where
  depth : Nat
  exhausted : Bool
  /-- Whether the state cap stopped the search before its depth. -/
  capped : Bool
  levels : List Nat
  transitions : Nat

/-- What explore found: each node it kept with the node and input it came from, the first transition per class of
out line, per fault (by its summary) and per broken response (by index), and what it covered. -/
structure Found (v : ServiceV) where
  nodes : Array (Node v × Nat × Option (Input v))
  classes : List (OutClass × Hit v)
  faults : List (String × Fault × Hit v)
  responses : List (Nat × Hit v)
  coverage : Coverage

/-- The inputs of the run from the initial state to the node at `i`, in order. -/
partial def Found.path (f : Found v) (i : Nat) : List (Input v) :=
  match f.nodes[i]? with
  | some (_, p, some x) => f.path p ++ [x]
  | _ => []

/-- The run's inputs of a hit: its node's path and its input. -/
def Found.hitPath (f : Found v) (h : Hit v) : List (Input v) := f.path h.node ++ [h.input]

/-- Searches from the initial node, at most `depth` inputs deep, keeping at most `cap` nodes. -/
def search (T : List TypeDecl) (v : ServiceV) (sc : ScopeV) (depth cap : Nat) : Found v := Id.run do
  let n0 := Node.init v
  let mut nodes : Array (Node v × Nat × Option (Input v)) := #[(n0, 0, none)]
  let mut seen : Std.HashSet Erl := ({} : Std.HashSet Erl).insert n0.key
  let mut byClass : Std.HashMap OutClass (Hit v) := {}
  let mut classOrder : Array OutClass := #[]
  let mut byFault : Std.HashMap String (Fault × Hit v) := {}
  let mut faultOrder : Array String := #[]
  let mut byResp : Std.HashMap Nat (Hit v) := {}
  let mut order := 0
  let mut lo := 0
  let mut hi := 1
  let mut levels : Array Nat := #[1]
  let mut covered := 0
  let mut exhausted := false
  let mut capped := false
  let mut transitions := 0
  for k in [0:depth] do
    if lo == hi then
      exhausted := true
      break
    let mut full := false
    for i in [lo:hi] do
      let some (n, _, _) := nodes[i]? | continue
      for x in inputsOf sc n do
        let mv := move T n x
        transitions := transitions + 1
        let hit : Hit v := ⟨k + 1, order, i, x⟩
        let mut used := false
        for c in classes T v x mv.result do
          if !byClass.contains c then
            byClass := byClass.insert c hit
            classOrder := classOrder.push c
            used := true
        if let .fault f := mv.result.outcome then
          let key := (Outcome.fault f).summary
          if !byFault.contains key then
            byFault := byFault.insert key (f, hit)
            faultOrder := faultOrder.push key
            used := true
        for j in mv.broken do
          if !byResp.contains j then
            byResp := byResp.insert j hit
            used := true
        if used then order := order + 1
        if let some n' := mv.next then
          if !full then
            let key := n'.key
            if !seen.contains key then
              if nodes.size ≥ cap then full := true
              else
                seen := seen.insert key
                nodes := nodes.push (n', i, some x)
    levels := levels.push (nodes.size - hi)
    lo := hi
    hi := nodes.size
    covered := k + 1
    if full then
      capped := true
      break
  if !capped && !exhausted && lo == hi then exhausted := true
  let coverage : Coverage :=
    { depth := covered, exhausted := exhausted, capped := capped, levels := levels.toList, transitions := transitions }
  return {
    nodes := nodes
    classes := classOrder.toList.filterMap fun c => (byClass.get? c).map (c, ·)
    faults := faultOrder.toList.filterMap fun key => (byFault.get? key).map fun (f, h) => (key, f, h)
    responses := byResp.toList.mergeSort fun a b => a.1 ≤ b.1
    coverage := coverage }

end Tazuna.Explore
