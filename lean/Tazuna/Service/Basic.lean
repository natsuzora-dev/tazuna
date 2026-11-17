import Tazuna.Service.Chart.Basic

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
  /-- The trace name of the received event (`todo.taskAdded` for another service's event). -/
  receives : String
  /-- The command that the automation sends; `sends.own` is whether the command belongs to the automation's service. -/
  sends : Activity
deriving DecidableEq, Repr, Inhabited

/--
A schema that a definition declares. `mapContext` is the copy context of the map state `map`, and `record` the fields
of the entity `entity`.
-/
inductive Schema where
  | input (definition : String)
  | payload (event : String)
  | output (definition : String)
  | control (screen control : String)
  | held (chart state name : String)
  | context (chart : String)
  | mapContext (chart map : String)
  | mapKey (chart map : String)
  | record (entity : String)
deriving DecidableEq, Repr, Inhabited

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
  The trace names of the events of other services' contracts that the service's definitions receive: an automation's
  or a chart's event, or a result event of a command that an automation or a chart sends. A simulation delivers an
  event only to the services that receive it.
  -/
  receives : List String
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
  requirements : List (String × Requirements) := []
deriving Repr, Inhabited

end Tazuna

namespace Tazuna.Service

open Tazuna.Data

/-- The JSON Schema of `schema`. A schema missing from the structure reads nothing. -/
def schemaOf (st : Service) (schema : Schema) : Value := (st.schemas.lookup schema).getD (.obj [])

def chart? (st : Service) (name : String) : Option Chart := st.charts.find? (·.name == name)

def ref (st : Service) (name : String) : Spec.Ref := { service := st.service, name }

/-- The ref that a trace name, as seen from the service, spells, without looking the definition up. -/
def refOf (st : Service) (traceName : String) : Spec.Ref := Spec.Ref.ofTraceName st.service traceName

def schemaOwner (st : Service) : Schema → Spec.Ref
  | .input d | .output d => st.refOf d
  | .payload e => st.refOf e
  | .control screen _ => st.ref screen
  | .held chart .. | .context chart | .mapContext chart _ | .mapKey chart _ => st.ref chart
  | .record entity => st.ref entity

def uniqueOf (st : Service) (entity : String) : List String := (st.uniques.lookup entity).getD []

def requirementsOf (st : Service) (name : String) : Requirements := (st.requirements.lookup name).getD {}

open Tazuna.Spec in
/-- The service named `service`, or the reason why it has a definition that the Lean model does not cover. -/
def ofStructure (j : Spec.Structure) (service : String) : Except String Service := do
  let own := j.definitions.zipIdx.filter (·.1.service == service)
  let entity (r : Ref) : Except String (String × List String) :=
    match j.definitions.findSome? fun d =>
      match d.body with
      | .entity (some key) fields _ _ => if d.ref == r then some (key, fields) else none
      | _ => none with
    | some found => pure found
    | none => throw s!"the entity {r.name} has no key"
  let single (r : Ref) : Bool := j.definitions.any fun d =>
    d.ref == r && match d.body with
      | .entity none .. => true
      | _ => false
  let charts ← (own.filterMap fun (d, order) => d.chart?.map (d, ·, order)).mapM fun (d, c, order) =>
    Chart.ofSpec c service d.name order d.isScreen (d.isScreen && j.isOpenedByScreen d.ref)
  let mut commands := []
  let mut queries := []
  let mut events : List (String × Change) := []
  let mut automations := []
  let mut schemas : List (Schema × Value) := []
  let mut requirements : List (String × Requirements) := []
  for (d, order) in own do
    let name := d.name
    match d.body with
    | .entity .. => pure ()
    | .event change entityRef payload =>
      schemas := schemas ++ [(.payload name, payload)]
      match change, entityRef with
      | .none, _ => events := events ++ [(name, .none)]
      | .create, some e =>
        let (key, fields) ← entity e
        events := events ++ [(name, .create e.name key fields)]
      | .update, some e =>
        if single e then events := events ++ [(name, .set e.name (schemaProperties payload))]
        else
          let (key, _) ← entity e
          events := events ++ [(name, .update e.name key ((schemaProperties payload).filter (· != key)))]
      | .delete, some e =>
        let (key, fields) ← entity e
        events := events ++ [(name, .delete e.name key fields)]
      | _, none => throw s!"the event {name} changes records without an entity"
    | .command _ input _ _ references binds conditions =>
      let refs ← references.mapM fun r =>
        match r.entity with
        | some e => pure (r.field, e)
        | none => throw s!"the ref field {r.field} of {name} points to no entity"
      commands := commands ++ [name]
      schemas := schemas ++ [(.input name, input)]
      requirements := requirements ++ [(name, { refs, binds, requires := conditions })]
    | .query _ input output conditions =>
      queries := queries ++ [name]
      schemas := schemas ++ [(.input name, input)] ++ (output.map fun o => [(.output name, o)]).getD []
      requirements := requirements ++ [(name, { requires := conditions })]
    | .automation (some receives) (some command) _ _ =>
      let sends := { keyword := "sends", key := name, target := command.traceName service, service := command.service,
                     name := command.name, own := command.service == service }
      automations := automations ++ [{ name, order, receives := receives.traceName service, sends }]
      if command.service != service then
        if let some input := j.definitions.findSome? fun d =>
            match d.body with
            | .command _ input .. => if d.ref == command then some input else none
            | _ => none then
          schemas := schemas ++ [(.input sends.target, input)]
    | .automation .. => throw s!"the automation {name} has no event or command"
    | .machine _ => pure ()
    | .screen c =>
      schemas := schemas ++ c.controls.filterMap fun (control, payload) => payload.map ((.control name control, ·))
      requirements := requirements ++ [(name, { requires := c.requires })]
  let listed := j.contracts.filter (·.service != service) |>.flatMap fun c =>
    c.members.filterMap fun (_, r) => r.bind fun r =>
      if j.definitions.any (fun d => d.kind == "event" && d.ref == r) then some (r.traceName service) else none
  let heard := own.flatMap fun (d, _) =>
    match d.body with
    | .automation (some e) .. => [e]
    | .machine c | .screen c => c.receives.filterMap (·.2)
    | _ => []
  let sent := own.flatMap fun (d, _) =>
    match d.body with
    | .automation _ (some c) .. => [c]
    | .machine c | .screen c => c.commands.filterMap (·.2)
    | _ => []
  let results := j.definitions.flatMap fun d =>
    match d.body with
    | .command _ _ _ emits .. => if sent.contains d.ref then emits.filterMap id else []
    | _ => []
  let receives := listed.filter fun n => (heard ++ results).any (·.traceName service == n)
  let entities := ((j.services.find? (·.name == service)).map (·.entities)).getD []
  let references := entities.flatMap fun e =>
    ((j.definitions.findSome? fun d =>
      match d.body with
      | .entity _ _ _ references => if d.service == service && d.name == e then some references else none
      | _ => none).getD []).filterMap fun r => r.entity.map fun target => (e, r.field, target.name)
  let uniques := entities.filterMap fun e =>
    j.definitions.findSome? fun d =>
      match d.body with
      | .entity _ _ unique _ => if d.service == service && d.name == e then some (e, unique) else none
      | _ => none
  let singles := entities.filter fun e => single { service, name := e }
  pure { service, «structure» := j, commands, queries, events, receives, automations, charts, schemas, entities, singles,
         references, uniques, requirements }

end Tazuna.Service
