import Tazuna.Service.Chart.Basic
import Tazuna.Service.Note

namespace Tazuna.Service

open Tazuna.Data

inductive Change where
  | none
  /-- The creation of a record. `key` is the payload field that holds the entity key. -/
  | create (entity : String) (key : String) (fields : List String)
  /-- An overwrite of `writes` of the keyed record, which creates the record from the payload if it is missing. -/
  | update (entity : String) (key : String) (writes : List String)
  /-- The deletion of the keyed record of `entity`. -/
  | delete (entity : String) (key : String) (fields : List String)
  | set (entity : String) (writes : List String)
deriving DecidableEq, Repr, Inhabited

/-- The requirements that a command or query checks before processing, in declaration order. -/
structure Requirements where
  /-- The input ref fields, each with the entity that it points to. -/
  refs : List (String × Spec.Ref) := []
  binds : List String := []
  requires : List String := []
deriving Repr, Inhabited

structure Automation where
  name : String
  /-- The rank among the spec's definitions. -/
  order : Nat
  receives : Spec.Ref
  /-- The command that the automation sends, a `sends` activity. -/
  sends : Activity
  binds : List String
  guard : List String
deriving DecidableEq, Repr, Inhabited

/--
A schema that a definition declares. `mapContext` is the copy context of the map state `map`, and `record` the fields
of the entity `entity`.
-/
inductive Schema where
  | input (definition : Spec.Ref)
  | payload (event : Spec.Ref)
  | output (definition : Spec.Ref)
  | control (screen : Spec.Ref) (control : String)
  | held (chart : Spec.Ref) (state name : String)
  | context (chart : Spec.Ref)
  | mapContext (chart : Spec.Ref) (map : String)
  | mapKey (chart : Spec.Ref) (map : String)
  | record (entity : Spec.Ref)
deriving DecidableEq, Repr, Inhabited

derive_wire Schema tag "kind"

end Tazuna.Service

namespace Tazuna

open Tazuna.Data Tazuna.Service

/-- The values of a service read from the structure JSON; Functions evaluates the function bodies. -/
structure Service where
  service : String
  «structure» : Spec.Structure
  commands : List String
  queries : List String
  /-- The own events, each with how it changes records. -/
  events : List (String × Change)
  /--
  The events of other services' contracts that the service's definitions receive: an automation's or a chart's event,
  or a result event of a command that an automation or a chart sends. A simulation delivers an event only to the
  services that receive it.
  -/
  receives : List Spec.Ref
  /-- The automations in definition order. -/
  automations : List Automation
  /-- The machines and screens in definition order. -/
  charts : List Chart
  /-- The JSON Schemas of the service's definitions, read to sort sortedBy arrays. -/
  schemas : List (Schema × Value) := []
  /-- The own entities, in the order of the service's `entities`. -/
  entities : List String := []
  singles : List String := []
  /-- The `ref()` fields as entity, field, and referenced entity, in entity then field order. -/
  references : List (String × String × String) := []
  uniques : List (String × List String) := []
  /-- The key positions of each own entity's records, in the order of `entities`. -/
  recordKeys : List (String × List Spec.KeyPosition) := []
  requirements : List (String × Requirements) := []
deriving Repr, Inhabited

end Tazuna

namespace Tazuna.Service

open Tazuna.Data

/-- The JSON Schema of `schema`. A schema missing from the structure reads nothing. -/
def schemaOf (st : Service) (schema : Schema) : Value := (st.schemas.lookup schema).getD (.obj [])

def chart? (st : Service) (name : String) : Option Chart := st.charts.find? (·.name == name)

def ref (st : Service) (name : String) : Spec.Ref := { service := st.service, name }

def Schema.owner : Schema → Spec.Ref
  | .input d | .output d => d
  | .payload e => e
  | .control screen _ => screen
  | .held chart .. | .context chart | .mapContext chart _ | .mapKey chart _ => chart
  | .record entity => entity

/-- How the event `r` changes records, when it is an own event. -/
def changeOf (st : Service) (r : Spec.Ref) : Option Change :=
  if r.service == st.service then st.events.lookup r.name else none

def uniqueOf (st : Service) (entity : String) : List String := (st.uniques.lookup entity).getD []

open Tazuna.Spec in
/-- The requirements of each own command, query, and screen of `service`, in definition order. -/
def requirementsOf (j : Spec.Structure) (service : String) : List (String × Requirements) :=
  j.definitions.filterMap fun d =>
    if d.service != service then none else
    match d.body with
    | .command c =>
      some (d.name, { refs := c.references.map fun r => (r.field, r.entity), binds := c.binds, requires := c.requires })
    | .query q => some (d.name, { requires := q.requires })
    | .screen c => some (d.name, { requires := c.requires })
    | _ => none

open Tazuna.Spec in
/--
The service named `service`. An entity that an event changes or the service lists is guaranteed by the loader, which
reports a reference to anything else (Malformed.unresolvedReference); a lookup that finds none notes a bug.
-/
def ofStructure {m : Type → Type} [Monad m] [MonadNote m] (j : Spec.Structure) (service : String) : m Service := do
  let own := j.definitions.zipIdx.filter (·.1.service == service)
  let entityBody (r : Ref) : m EntityBody :=
    expectFound s!"entity {r.service}.{r.name}" (j.definitions.findSome? fun d =>
      match d.body with
      | .entity body => if d.ref == r then some body else none
      | _ => none)
  let keyed (r : Ref) : m (String × List String) := do
    let body ← entityBody r
    pure ((← expectFound s!"key of the entity {r.name}" body.key), body.fields)
  let charts := own.filterMap fun (d, order) =>
    d.chart?.map (Chart.ofSpec · d.name order d.isScreen (d.isScreen && j.isOpenedByScreen d.ref))
  let mut commands := []
  let mut queries := []
  let mut events : List (String × Change) := []
  let mut automations := []
  let mut schemas : List (Schema × Value) := []
  for (d, order) in own do
    let name := d.name
    match d.body with
    | .entity .. => pure ()
    | .event { change, payload } =>
      schemas := schemas ++ [(.payload d.ref, payload)]
      match change with
      | none => events := events ++ [(name, .none)]
      | some { kind := .create, entity := e } =>
        let (key, fields) ← keyed e
        events := events ++ [(name, .create e.name key fields)]
      | some { kind := .update, entity := e } =>
        match (← entityBody e).key with
        | none => events := events ++ [(name, .set e.name (schemaProperties payload))]
        | some key => events := events ++ [(name, .update e.name key ((schemaProperties payload).filter (· != key)))]
      | some { kind := .delete, entity := e } =>
        let (key, fields) ← keyed e
        events := events ++ [(name, .delete e.name key fields)]
    | .command c =>
      commands := commands ++ [name]
      schemas := schemas ++ [(.input d.ref, c.input)]
    | .query q =>
      queries := queries ++ [name]
      schemas := schemas ++ [(.input d.ref, q.input)] ++ (q.output.map fun o => [(.output d.ref, o)]).getD []
    | .automation a =>
      let sends := Activity.sends name a.command
      automations := automations ++
        [({ name, order, receives := a.receives, sends, binds := a.binds, guard := a.guard } : Automation)]
      if a.command.service != service then
        if let some input := j.definitions.findSome? fun d =>
            match d.body with
            | .command c => if d.ref == a.command then some c.input else none
            | _ => none then
          schemas := schemas ++ [(.input a.command, input)]
    | .machine _ => pure ()
    | .screen c =>
      schemas := schemas ++ c.controls.filterMap fun (control, payload) => payload.map ((.control d.ref control, ·))
  let listed := j.contracts.filter (·.service != service) |>.flatMap fun c =>
    c.members.filterMap fun (_, r) => r.bind fun r =>
      if j.definitions.any (fun d => d.kind == "event" && d.ref == r) then some r else none
  let heard := own.flatMap fun (d, _) =>
    match d.body with
    | .automation a => [a.receives]
    | .machine c | .screen c => c.receives.map (·.2)
    | _ => []
  let sent := own.flatMap fun (d, _) =>
    match d.body with
    | .automation a => [a.command]
    | .machine c | .screen c => c.commands.map (·.2)
    | _ => []
  let results := j.definitions.flatMap fun d =>
    match d.body with
    | .command c => if sent.contains d.ref then c.emits else []
    | _ => []
  let receives := listed.filter (heard ++ results).contains
  let entities ← expectFound s!"service {service}" ((j.services.find? (·.name == service)).map (·.entities))
  let bodies ← entities.mapM fun e => do pure (e, ← entityBody { service, name := e })
  pure { service, «structure» := j, commands, queries, events, receives, automations, charts, schemas, entities,
         singles := bodies.filterMap fun (e, b) => if b.key.isNone then some e else none
         references := bodies.flatMap fun (e, b) => b.references.map fun r => (e, r.field, r.entity.name)
         uniques := bodies.map fun (e, b) => (e, b.unique)
         recordKeys := bodies.map fun (e, b) => (e, b.keys)
         requirements := requirementsOf j service }

end Tazuna.Service
