import Tazuna.Spec.Definition
import Tazuna.Ir.Expr

namespace Tazuna.Spec

open Tazuna.Data

/--
The whole spec without source locations, as TS `structureOf` writes it, with the bodies of its spec functions as IR,
which TS converts once check passes.
-/
structure Structure where
  services : List ServiceInfo
  contracts : List Contract
  /-- The definitions, in the order of the spec. -/
  definitions : List Definition
  /-- The `explore()` calls, at most one per service. -/
  explores : List Explore
  program : Ir.Program := {}
deriving Repr, Inhabited

derive_wire Structure

def Structure.body? (s : Structure) (r : Ref) : Option Body :=
  (s.definitions.find? (·.ref == r)).map (·.body)

def Structure.state? (s : Structure) (chart : Ref) (state : String) : Option State :=
  (s.body? chart).bind fun
    | .machine c | .screen c => c.states.find? (·.name == state)
    | _ => none

/--
The JSON Schema that `schema` names: a control without a payload's as an object without fields. None when the
structure has no such schema.
-/
def Structure.schemaOf (s : Structure) : Schema → Option Value
  | .input d => (s.body? d).bind fun
    | .command c => some c.input
    | .query q => some q.input
    | .machine c | .screen c => some c.input
    | _ => none
  | .output d => (s.body? d).bind fun
    | .command c => c.output
    | .query q => q.output
    | .machine c | .screen c => some c.output
    | _ => none
  | .payload e => (s.body? e).bind fun
    | .event b => some b.payload
    | _ => none
  | .control screen control => (s.body? screen).bind fun
    | .screen c => (c.controls.lookup control).map (·.getD (.obj []))
    | _ => none
  | .held chart state => ((s.state? chart state).bind (·.held)).map (·.schema)
  | .context chart => (s.body? chart).bind fun
    | .machine c | .screen c => some c.context
    | _ => none
  | .mapContext chart map => ((s.state? chart map).bind (·.type.map?)).map (·.context)
  | .mapKey chart map => ((s.state? chart map).bind (·.type.map?)).map (·.key)
  | .record entity => (s.body? entity).bind fun
    | .entity b => some b.fields
    | _ => none

/-- The commands that the automations and charts of `service` send. -/
def Structure.sentOf (s : Structure) (service : String) : List Ref :=
  (s.definitions.filter (·.service == service)).flatMap fun d =>
    match d.body with
    | .automation a => [a.command]
    | .machine c | .screen c => c.commands.map (·.2)
    | _ => []

/-- The commands and queries that the automations and charts of `service` send, each once. -/
def Structure.requestsOf (s : Structure) (service : String) : List Ref :=
  (s.sentOf service ++ (s.definitions.filter (·.service == service)).flatMap fun d =>
    match d.body with
    | .machine c | .screen c => c.queries.map (·.2)
    | _ => []).eraseDups

/--
The events of other services' contracts that the definitions of `service` receive: an automation's or a chart's
event, or a result event of a command that an automation or a chart sends.
-/
def Structure.receivesOf (s : Structure) (service : String) : List Ref :=
  let listed := s.contracts.filter (·.service != service) |>.flatMap fun c =>
    c.members.filterMap fun (_, r) => r.bind fun r =>
      if s.definitions.any (fun d => d.kind == "event" && d.ref == r) then some r else none
  let heard := (s.definitions.filter (·.service == service)).flatMap fun d =>
    match d.body with
    | .automation a => [a.receives]
    | .machine c | .screen c => c.receives.map (·.2)
    | _ => []
  let sent := s.sentOf service
  let results := s.definitions.flatMap fun d =>
    match d.body with
    | .command c => if sent.contains d.ref then c.emits else []
    | _ => []
  listed.filter (heard ++ results).contains

def Chart.state? (c : Chart) (n : String) : Option State := c.states.find? (·.name == n)

def Structure.isOpenedByScreen (s : Structure) (r : Ref) : Bool :=
  s.definitions.any fun d =>
    match d.body with
    | .screen c => c.screens.any (·.2 == r)
    | _ => false

/-- The definition with trace name `name` whose kind is one of `kinds`. -/
def Structure.named (s : Structure) (service : String) (name : Option String) (kinds : List String) :
    Option Definition :=
  name.bind fun n => s.definitions.find? fun d => kinds.contains d.kind && d.traceName service == n

/-- The services whose contract lists `r`. -/
def Structure.contractsListing (s : Structure) (r : Ref) : List String :=
  (s.contracts.filter (·.members.any (·.2 == some r))).map (·.service)

/--
The kinds that an answer to the command or query `r` may be rejected with when a definition of `service` sends it: for
an external `r`, the kinds it declares. Otherwise `requires` needs a requires condition or a binds value, `notFound` an
input ref field, and `alreadyExists` an emitted event that creates or updates a record, and a request to another
service may also be rejected with `unavailable`, and a command to another service with `reusedId`. An answer
rejected with `invalidInput` is the sender's fault (rejectedInput?), so it is not listed.
-/
def Structure.rejectionKinds (s : Structure) (service : String) (r : Ref) : List RejectionKind :=
  let other (kinds : List RejectionKind) := if r.service == service then [] else kinds
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.query { rejects := some kinds, .. }) | some (.command { rejects := some kinds, .. }) => kinds
  | some (.query q) => (if q.requires.isEmpty then [] else [.requires]) ++ other [.unavailable]
  | some (.command c) =>
    let writes := c.emits.any fun e => s.definitions.any fun d =>
      d.ref == e && match d.body with
        | .event { change := some { kind := .create, .. }, .. }
        | .event { change := some { kind := .update, .. }, .. } => true
        | _ => false
    other [.reusedId] ++ (if c.references.isEmpty then [] else [.notFound]) ++
      (if c.binds.isEmpty && c.requires.isEmpty then [] else [.requires]) ++
      (if writes then [.alreadyExists] else []) ++ other [.unavailable]
  | _ => []

/-- The events that `r` lists in its emits, or no events when `r` is no command. -/
def Structure.emitsOf (s : Structure) (r : Ref) : List Ref :=
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.command c) => c.emits
  | _ => []

/-- The requires and ensures conditions of `r`, or none when `r` is no command or query. -/
def Structure.conditionsOf? (s : Structure) (r : Ref) : Option (List String × List String) :=
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.command c) => some (c.requires, c.ensures)
  | some (.query q) => some (q.requires, q.ensures)
  | _ => none

/-- The reasons that a requires rejection of the command or query `r` may name: its binds, then its requires. -/
def Structure.rejectionReasons (s : Structure) (r : Ref) : List String :=
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.command c) => c.binds ++ c.requires
  | some (.query q) => q.requires
  | _ => []

def Structure.hasOutput (s : Structure) (r : Ref) : Bool :=
  (s.definitions.find? (·.ref == r)).any (·.hasOutput)

/--
Whether an answer to the command or query `r` is checked against `r`'s assumed contract: `r` is a command or query of
an external service. test checks an answer from another service in the same spec against that service's run instead
(peerFindings).
-/
def Structure.isAssumed (s : Structure) (r : Ref) : Bool :=
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.query ..) | some (.command ..) => (s.services.find? (·.name == r.service)).any (·.external)
  | _ => false

/-- Why an event cannot be the result (resultOf) of a request. -/
inductive ResultOfMismatch where
  /-- The resultOf of the event names a request to a target that is not a command. -/
  | resultOfNonCommand
  /-- The resultOf of the event names a request that the answer did not accept. -/
  | resultOfUnacceptedRequest
  /-- The resultOf of the event names a request to a command whose emits do not list the event. -/
  | resultOfUnlistedEvent
deriving DecidableEq, Repr, Inhabited

derive_wire ResultOfMismatch

/--
Why `event` cannot be the result of a request to `target` that got `answers`, or none when it can. `event` can be the
result only when `target` is a command that lists `event` in its emits and no answer did not accept the request. A
request that no answer reached may have results, as an API response may be lost after the webhook is sent.
-/
def Structure.resultOfMismatch (s : Structure) (target : Ref) (answers : List Answer) (event : Ref) :
    Option ResultOfMismatch :=
  match (s.definitions.find? (·.ref == target)).map Definition.body with
  | some (.command c) =>
    if !answers.all (· matches .accepted _) then some .resultOfUnacceptedRequest
    else if c.emits.contains event then none
    else some .resultOfUnlistedEvent
  | _ => some .resultOfNonCommand

/-- What an answer to a request, or its result events, break of the target's contract. -/
inductive AssumptionMismatch where
  /-- The answer rejects the request with a kind that the target does not list. -/
  | unlistedRejectionKind (rejection : Rejection)
  /-- The answer has an output that does not match the target's output schema. -/
  | answerOutputSchema
  /-- The answer rejects the request for requires, although the input meets the target's assumed requires. -/
  | rejectedAssumedRequires
  /-- The answer is no rejection, although the input fails the target's assumed requires `condition`. -/
  | failedAssumedRequires (condition : String)
  /-- The answer, or the result events so far, fail the target's assumed ensures `condition`. -/
  | failedAssumedEnsures (condition : String)
deriving DecidableEq, Repr, Inhabited

derive_wire AssumptionMismatch tag "kind"

/--
The assumption that an answer breaks, given the first assumed requires that fails and, when the requires hold and
the answer is no rejection, the first assumed ensures that fails. A broken requires promises no ensures.
-/
def assumptionMismatch (answer : Answer) (failedRequires failedEnsures : Option String) : Option AssumptionMismatch :=
  match answer, failedRequires with
  | .rejected r, none => if r.kind == .requires then some .rejectedAssumedRequires else none
  | .rejected _, some _ => none
  | _, some c => some (.failedAssumedRequires c)
  | _, none => failedEnsures.map .failedAssumedEnsures

def schemaProperties (schema : Value) : List String :=
  match schema.field? "properties" with
  | some (.obj fields) => fields.map (·.1)
  | _ => []

end Tazuna.Spec
