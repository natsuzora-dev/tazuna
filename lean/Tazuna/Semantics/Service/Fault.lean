import Tazuna.Ir.Answer
import Tazuna.Ir.Group
import Tazuna.Ir.Structure

namespace Tazuna.Semantics.Service

open Tazuna.Ir

/--
A definition that breaks the meaning while the run evaluates it. `definition` is the definition that causes it.
An exception or a notOnly has no `definition` when a service invariant causes it, since the subject is then the service.
-/
inductive Fault where
  /-- The command emits `event` with a payload that does not match the event's payload schema. -/
  | emittedPayloadSchema (definition : Ir.Ref) (event : Ir.Ref)
  /-- The command emits an event that its emits do not list. `event` is null when the event is no definition. -/
  | unlistedEmittedEvent (definition : Ir.Ref) (event : Option Ir.Ref)
  /--
  Two events of one Bag that the command's decide returns write one record of `entity`, so the record would depend on
  their order. `recordKey` is null for a single entity.
  -/
  | sameRecordInBag (definition : Ir.Ref) (entity : Ir.Ref) (recordKey : Option Value)
  /-- The query answers with an output that does not match its output schema. -/
  | outputSchema (definition : Ir.Ref)
  /-- The input that the chart or automation `definition` gives `target` does not match the input schema of `target`. -/
  | inputSchema (definition : Ir.Ref) (target : Ir.Ref)
  /-- The input that the chart gives the screen it opens fails the screen's requires `condition`. -/
  | failedRequires (definition : Ir.Ref) (screen : Ir.Ref) (condition : String)
  /-- The edge that enters `state` fills its parameters with a value off the state's held schema. -/
  | heldSchema (definition : Ir.Ref) (state : String)
  /--
  An offers entry of the control `control` returns a payload that does not match the control's payload schema. `state`
  is null for the offers of the chart's own `on`.
  -/
  | offersSchema (definition : Ir.Ref) (control : String) (state : Option String)
  /-- The initial context that the chart computes from its input does not match its context schema. -/
  | initialContextSchema (definition : Ir.Ref)
  /-- The output that the screen gives its opener when it is done does not match its output schema. -/
  | screenOutputSchema (definition : Ir.Ref)
  /--
  An assign of the chart writes a context of a copy of the map `map` that does not match the copy's context schema.
  -/
  | copyContextSchema (definition : Ir.Ref) (map : String)
  /-- An assign of the chart writes a context that does not match its context schema. -/
  | contextSchema (definition : Ir.Ref)
  /-- The items that the chart computes for the map `map` do not match their schema. -/
  | itemsSchema (definition : Ir.Ref) (map : String)
  /--
  The `at` of the deadline `deadline` of state `state` computes a value that is no safe integer of milliseconds, which
  the run's time cannot hold.
  -/
  | atSchema (definition : Ir.Ref) (state deadline : String)
  /--
  The delay of the deadline `deadline` of state `state` takes its time past the range of an instant, which the run's time
  cannot hold (Time.inRange, the rule that an `at` meets too).
  -/
  | deadlineOutOfRange (definition : Ir.Ref) (state deadline : String)
  /-- A function reads `held` (its state's parameter) under a name that the state does not have. -/
  | unheld (definition : Ir.Ref) (held : String)
  /--
  A function calls `only()` on a bag with more than one element, or `minBy` or `maxBy` on a bag whose least or greatest
  key more than one element has.
  -/
  | notOnly (definition : Option Ir.Ref)
  /--
  A spec function threw. `definition` is the definition whose function threw, or null when a service invariant throws.
  -/
  | exception (definition : Option Ir.Ref)
  /-- The record `recordKey` of entity `definition` refers in `field` to the missing record `targetKey`. -/
  | danglingRef (definition : Ir.Ref) (recordKey : Value) (field : String) (targetKey : Value) (command : Ir.Ref)
  /-- The record of the single entity `definition` refers in `field` to the missing record `targetKey`. -/
  | danglingSingleRef (definition : Ir.Ref) (field : String) (targetKey : Value) (command : Ir.Ref)
  /-- The answer of the command or query, or the output of the screen, fails its ensures `condition`. -/
  | failedEnsures (definition : Ir.Ref) (condition : String)
  /-- The record `recordKey` of the entity fails its invariant `condition` after the command `command`. -/
  | failedEntityInvariant (definition : Ir.Ref) (recordKey : Value) (condition : String) (command : Ir.Ref)
  /-- The record of the single entity fails its invariant `condition` after the command `command`. -/
  | failedSingleInvariant (definition : Ir.Ref) (condition : String) (command : Ir.Ref)
  /-- The records of the service fail its invariant `condition` after the command `command`. -/
  | failedServiceInvariant (condition : String) (command : Ir.Ref)
  /-- The chart fails its invariant `condition` after it starts or after a microstep. -/
  | failedChartInvariant (definition : Ir.Ref) (condition : String)
  /--
  Time passed `due` while the response `response` of the record `recordKey` of entity `definition` was open: its `when`
  held and its `expect` did not hold since, through `due`. The record of a single entity has no key.
  -/
  | missedResponse (definition : Ir.Ref) (recordKey : Option Value) (response : String) (due : Int)
  /-- Two items that the chart computes for the map `map` have the key `itemKey`. -/
  | duplicateItemKey (definition : Ir.Ref) (map : String) (itemKey : Value)
  /--
  A chain of commands that automations send to their own service, each on an event of the one before, is deeper than
  `limit`. `definition` sent the command past the limit.
  -/
  | exceededCommandDepth (definition : Ir.Ref) (limit : Nat)
  /--
  Automations send more than `limit` commands to their own service on one message. `definition` sent the command past
  the limit.
  -/
  | exceededMessageCommands (definition : Ir.Ref) (limit : Nat)
  /-- The chart's always transitions keep firing for more than `limit` rounds without the chart settling. -/
  | exceededAlwaysRounds (definition : Ir.Ref) (limit : Nat)
  /-- The chart's onDone transitions select states that finish again more than `limit` times in one work. -/
  | exceededOnDoneSelections (definition : Ir.Ref) (limit : Nat)
  /--
  One message runs more than `limit` work items and commands. They come from every definition that the message runs,
  none of which alone exceeds the limit, so the fault names no definition.
  -/
  | exceededMessageWork (limit : Nat)
  /--
  More than `limit` deadlines fall due in one clock advance. They belong to any charts, so the fault names no
  definition.
  -/
  | exceededDueDeadlines (limit : Nat)
  /--
  The automation's command is rejected for a reason that blames the caller, such as `requires` or `not-found`, so the
  automation sent a command that it must not send.
  -/
  | rejectedAutomationCommand (definition : Ir.Ref) (rejection : Rejection)
  /--
  The query of the screen's shows slot `slot` rejects for a reason that blames the caller, so the screen asked for a
  value that it must not ask for.
  -/
  | rejectedShows (definition : Ir.Ref) (slot : String) (rejection : Rejection)
deriving Repr

derive_group Fault

/--
Whether the fault halts the run, which it does when the behavior after the fault is undefined.
-/
def Fault.halts : Fault → Bool
  | .emittedPayloadSchema .. | .unlistedEmittedEvent .. | .sameRecordInBag .. | .outputSchema ..
  | .inputSchema .. | .failedRequires .. | .heldSchema ..
  | .offersSchema .. | .initialContextSchema .. | .screenOutputSchema .. | .copyContextSchema .. | .contextSchema ..
  | .itemsSchema .. | .atSchema .. | .deadlineOutOfRange .. | .unheld .. | .notOnly .. | .exception .. | .duplicateItemKey ..
  | .exceededCommandDepth ..
  | .exceededMessageCommands .. | .exceededAlwaysRounds .. | .exceededOnDoneSelections .. | .exceededMessageWork ..
  | .exceededDueDeadlines .. => true
  | .danglingRef .. | .danglingSingleRef .. | .failedEnsures .. | .failedEntityInvariant .. | .failedSingleInvariant ..
  | .failedServiceInvariant .. | .failedChartInvariant .. | .missedResponse .. | .rejectedAutomationCommand ..
  | .rejectedShows .. => false

/--
Whether no spec that `tazuna check` passes can produce the violation, as InvalidScenario.internal says: the IR names
only the events that a command's emits list.
-/
def Fault.internal : Fault → Bool
  | .unlistedEmittedEvent .. => true
  | _ => false

end Tazuna.Semantics.Service
