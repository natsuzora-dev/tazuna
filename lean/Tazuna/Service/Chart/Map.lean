import Tazuna.Service.Chart.Microstep

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def setCopyKeys (copyKeys : List (String × List Value)) (map : String) (cs : List Value) : List (String × List Value) :=
  if copyKeys.any (·.1 == map) then copyKeys.map fun (k, v) => if k == map then (k, cs) else (k, v)
  else copyKeys ++ [(map, cs)]

/--
Starts the copy of the map state `map` for `key`; a copy's context starts as the defaults of its fields, which load
checks (Malformed.defaultSchema).
-/
def startCopy (st : Service) (step : Nat) (owner : InstanceId) (map : String) (key : Value) : Processing → m Processing :=
  withMachine owner fun o r => do
    let schema := .mapContext (st.ref o.chart.name) map
    let context ← expectFound s!"defaults of the copy context of {map}" (← fs.defaults schema).toOption
    let id := .copy o.id map key
    let copy : Instance := { chart := o.chart, id, context, input := o.input, itemKey := some key }
    let started : State := { r.state with copies := r.state.copies.filter (·.id != id) ++ [copy] }
    let (s, copyStep) := started.newStep (.caused step)
    MonadNote.note (.stepBegins copyStep (.start id) (some id))
    let r ← match (o.chart.state? map).bind (·.spec.initial) with
      | some initial => enter fs st copyStep id [initial] ⟨s, r.queue⟩
      | none => pure ⟨s, r.queue⟩
    MonadNote.note .stepEnds
    pure r

def exitLeftCopy (st : Service) (owner : InstanceId) (map : String) (itemKeys : List Value) (r : Processing) (k : Value) :
    m Processing :=
  if k ∈ itemKeys then pure r else unlessHalted (endWith (exitOne fs st st.exitFuel) (.copy owner map k)) r

def newKeys (current : List Value) (keys : List Value) : List Value :=
  keys.filter (· ∉ current)

/-- The item keys in the order of their canonical JSON, since a map state takes its items as a set. -/
def sortItemKeys (keys : List Value) : List Value :=
  keys.mergeSort fun a b => decide (a.canonical ≤ b.canonical)

/-- The processing after map state `map` syncs its copies with its items, and whether anything changed. -/
def syncMap (st : Service) (step : Nat) (owner : InstanceId) (r : Processing) (map : String) : m (Processing × Bool) := do
  if r.halted then pure (r, false) else
  match r.state.machine? owner with
  | none => pure (r, false)
  | some o => do
    MonadNote.note (.readStates [(o.id, map)])
    match ← fs.items (r.state.scopeOf o (some map)) r.state.records with
    | .error e =>
      pure (r.report (.fault (issueViolation (st.ref o.chart.name) e fun _ =>
        .itemsSchema (st.ref o.chart.name) map)), true)
    | .ok items =>
      let itemKeys := sortItemKeys items
      let current := o.copyKeysOf map
      match firstDuplicate id itemKeys with
      | some k => pure (r.report (.fault (.duplicateItemKey (st.ref o.chart.name) map k)), true)
      | none =>
      if current == itemKeys then pure (r, false) else do
      MonadNote.note (.wroteCopies o.id map)
      let r ← current.reverse.foldlM (exitLeftCopy fs st o.id map itemKeys) r
      let r ← (newKeys current itemKeys).foldlM (fun r k => unlessHalted (startCopy fs st step owner map k) r) r
      pure (⟨r.state.setMachine owner fun o => { o with copyKeys := setCopyKeys o.copyKeys map itemKeys }, r.queue⟩, true)

/-- The processing after each active map state of `owner` syncs its copies, and whether any map state changed. -/
def syncCopies (st : Service) (step : Nat) (owner : InstanceId) (r : Processing) : m (Processing × Bool) := do
  match r.state.machine? owner with
  | none => pure (r, false)
  | some o =>
    let tree := o.chart.tree
    (o.active.filter fun n => tree.kindOf n == some .map).foldlM
      (fun acc map => do let synced ← syncMap fs st step owner acc.1 map; pure (synced.1, acc.2 || synced.2)) (r, false)

end

end Tazuna.Service
