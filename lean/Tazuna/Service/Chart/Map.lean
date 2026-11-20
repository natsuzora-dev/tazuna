import Tazuna.Service.Chart.Microstep

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def setCopyKeys (copyKeys : List (String × List Value)) (map : String) (cs : List Value) : List (String × List Value) :=
  if copyKeys.any (·.1 == map) then copyKeys.map fun (k, v) => if k == map then (k, cs) else (k, v)
  else copyKeys ++ [(map, cs)]

def startCopy (st : Service) (step : Nat) (owner : InstanceId) (map : String) (key encodedKey : Value) : Processing → m Processing :=
  withMachine owner fun o r => do
    let context ← fs.copyContext o.chart.name map
    let id := .copy o.id map encodedKey
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

def newKeys (current : List Value) (keys : List (Value × Value)) : List (Value × Value) :=
  keys.filter (·.2 ∉ current)

/-- The item keys in the order of their canonical JSON, since a map state takes its items as a set. -/
def sortItemKeys (keys : List (Value × Value)) : List (Value × Value) :=
  keys.mergeSort fun a b => decide (a.2.canonical ≤ b.2.canonical)

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
      let keys := sortItemKeys items
      let current := o.copyKeysOf map
      let itemKeys := keys.map (·.2)
      match firstDuplicate (·.2) keys with
      | some k => pure (r.report (.fault (.duplicateItemKey (st.ref o.chart.name) map k.1)), true)
      | none =>
      if current == itemKeys then pure (r, false) else do
      MonadNote.note (.wroteCopies o.id map)
      let r ← current.reverse.foldlM (exitLeftCopy fs st o.id map itemKeys) r
      let r ← (newKeys current keys).foldlM (fun r k => unlessHalted (startCopy fs st step owner map k.1 k.2) r) r
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
