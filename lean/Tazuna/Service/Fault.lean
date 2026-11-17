import Tazuna.Data.Answer
import Tazuna.Data.Group
import Tazuna.Spec.Structure

namespace Tazuna.Service

open Tazuna.Data

/--
A definition that breaks the meaning while the run evaluates it. `definition` is the definition that causes it.
An exception has no `definition` when a service invariant throws, since the subject is then the service.
-/
inductive Fault where
  | emittedPayloadSchema (definition : Spec.Ref) (event : Spec.Ref)
  /-- The command emits an event that its emits do not list; `event` is null when the event is no definition. -/
  | unlistedEmittedEvent (definition : Spec.Ref) (event : Option Spec.Ref)
  /--
  Two events of one Bag that the command's decide returns write one record of `entity`, so the record would depend on
  their order; `recordKey` is null for a single entity.
  -/
  | sameRecordInBag (definition : Spec.Ref) (entity : Spec.Ref) (recordKey : Option String)
  | outputSchema (definition : Spec.Ref)
  /-- The input that the chart or automation `definition` gives `target` does not match the input schema of `target`. -/
  | inputSchema (definition : Spec.Ref) (target : Spec.Ref)
  /-- The input that the chart gives the screen it opens fails the screen's requires `condition`. -/
  | failedRequires (definition : Spec.Ref) (screen : Spec.Ref) (condition : String)
  | heldSchema (definition : Spec.Ref) (held state : String)
  /-- `state` is null for the offers of the chart's own `on`. -/
  | offersSchema (definition : Spec.Ref) (control : String) (state : Option String)
  | initialContextSchema (definition : Spec.Ref)
  | screenOutputSchema (definition : Spec.Ref)
  | copyContextSchema (definition : Spec.Ref) (map : String)
  | contextSchema (definition : Spec.Ref)
  | itemsSchema (definition : Spec.Ref) (map : String)
  /-- A function reads the held value `held` while its state does not hold it. -/
  | unheld (definition : Spec.Ref) (held : String)
  /-- A function calls `only()` on a bag with more than one element. -/
  | notOnly (definition : Spec.Ref)
  | exception (definition : Option Spec.Ref)
  /-- The record `recordKey` of entity `definition` refers in `field` to the missing record `targetKey`. -/
  | danglingRef (definition : Spec.Ref) (recordKey field targetKey : String) (command : Spec.Ref)
  /-- The record of the single entity `definition` refers in `field` to the missing record `targetKey`. -/
  | danglingSingleRef (definition : Spec.Ref) (field targetKey : String) (command : Spec.Ref)
  | failedEnsures (definition : Spec.Ref) (condition : String)
  | failedEntityInvariant (definition : Spec.Ref) (recordKey condition : String) (command : Spec.Ref)
  | failedSingleInvariant (definition : Spec.Ref) (condition : String) (command : Spec.Ref)
  | failedServiceInvariant (condition : String) (command : Spec.Ref)
  | failedChartInvariant (definition : Spec.Ref) (condition : String)
  | duplicateItemKey (definition : Spec.Ref) (map : String) (itemKey : Value)
  | exceededCommandDepth (definition : Spec.Ref) (limit : Nat)
  | exceededMessageCommands (definition : Spec.Ref) (limit : Nat)
  | exceededAlwaysRounds (definition : Spec.Ref) (limit : Nat)
  | exceededOnDoneSelections (definition : Spec.Ref) (limit : Nat)
  /--
  The work items and commands of one message come from every definition that the message runs, none of which alone
  exceeds the limit, so the fault names no definition.
  -/
  | exceededMessageWork (limit : Nat)
  /-- The deadlines of one clock advance belong to any charts, so the fault names no definition. -/
  | exceededDueDeadlines (limit : Nat)
  /-- The nested exits run through the copies and screens of several definitions, so the fault names no definition. -/
  | exceededExitDepth (limit : Nat)
  | rejectedAutomationCommand (definition : Spec.Ref) (rejection : Rejection)
  | rejectedShows (definition : Spec.Ref) (slot : String) (rejection : Rejection)
  /--
  The service sent `key` or holds it in a record, of the form of a key of `entity` that a running service creates, and
  no running service created it: a spec computed it. Only createKey makes a created key, so test could not tell it from
  one when it compares runs up to a renaming of created keys. The check follows the whole processing, whose definitions
  any may have computed it, so the fault names no definition.
  -/
  | computedKey (key : String) (entity : Spec.Ref)
deriving Repr

derive_group Fault

/--
Whether the fault halts the run, which it does when the behavior after the fault is undefined, or, for computedKey, when
test could no longer compare the run with another.
-/
def Fault.halts : Fault → Bool
  | .emittedPayloadSchema .. | .unlistedEmittedEvent .. | .sameRecordInBag .. | .outputSchema ..
  | .inputSchema .. | .failedRequires .. | .heldSchema ..
  | .offersSchema .. | .initialContextSchema .. | .screenOutputSchema .. | .copyContextSchema .. | .contextSchema ..
  | .itemsSchema .. | .unheld .. | .notOnly .. | .exception .. | .duplicateItemKey .. | .exceededCommandDepth ..
  | .exceededMessageCommands .. | .exceededAlwaysRounds .. | .exceededOnDoneSelections .. | .exceededMessageWork ..
  | .exceededDueDeadlines .. | .exceededExitDepth .. | .computedKey .. => true
  | .danglingRef .. | .danglingSingleRef .. | .failedEnsures .. | .failedEntityInvariant .. | .failedSingleInvariant ..
  | .failedServiceInvariant .. | .failedChartInvariant .. | .rejectedAutomationCommand .. | .rejectedShows .. => false

end Tazuna.Service
