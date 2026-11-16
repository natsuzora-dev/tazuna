import Tazuna.Data.Answer
import Tazuna.Data.Group
import Tazuna.Syntax.Structure

namespace Tazuna.Semantics

open Tazuna.Data

/--
A definition that breaks the meaning while the run evaluates it. `definition` is the definition that causes it.
An exception has no `definition` when a service invariant throws, since the subject is then the service.
-/
inductive Fault where
  | emittedPayloadSchema (definition : Syntax.Ref) (event : Syntax.Ref)
  /-- The command emits an event that its emits do not list; `event` is null when the event is no definition. -/
  | unlistedEmittedEvent (definition : Syntax.Ref) (event : Option Syntax.Ref)
  /--
  Two events of one Bag that the command's decide returns write one record of `entity`, so the record would depend on
  their order; `recordKey` is null for a single entity.
  -/
  | sameRecordInBag (definition : Syntax.Ref) (entity : Syntax.Ref) (recordKey : Option String)
  | outputSchema (definition : Syntax.Ref)
  | automationInputSchema (definition : Syntax.Ref)
  | requestInputSchema (definition : Syntax.Ref) (target : Syntax.Ref)
  | showsInputSchema (definition : Syntax.Ref) (slot : String)
  | screenInputSchema (definition : Syntax.Ref) (screen : Syntax.Ref)
  /-- The input that the chart gives the screen it opens fails the screen's requires `condition`. -/
  | failedRequires (definition : Syntax.Ref) (screen : Syntax.Ref) (condition : String)
  | heldSchema (definition : Syntax.Ref) (held state : String)
  /-- `state` is null for the offers of the chart's own `on`. -/
  | offersSchema (definition : Syntax.Ref) (control : String) (state : Option String)
  | initialContextSchema (definition : Syntax.Ref)
  | screenOutputSchema (definition : Syntax.Ref)
  | copyContextSchema (definition : Syntax.Ref) (map : String)
  | contextSchema (definition : Syntax.Ref)
  | itemsSchema (definition : Syntax.Ref) (map : String)
  /-- A function reads the held value `held` while its state does not hold it. -/
  | unheld (definition : Syntax.Ref) (held : String)
  /-- A function calls `only()` on a bag with more than one element. -/
  | notOnly (definition : Syntax.Ref)
  | exception (definition : Option Syntax.Ref)
  /-- The record `recordKey` of entity `definition` refers in `field` to the missing record `targetKey`. -/
  | danglingRef (definition : Syntax.Ref) (recordKey field targetKey : String) (command : Syntax.Ref)
  /-- The record of the single entity `definition` refers in `field` to the missing record `targetKey`. -/
  | danglingSingleRef (definition : Syntax.Ref) (field targetKey : String) (command : Syntax.Ref)
  | failedEnsures (definition : Syntax.Ref) (condition : String)
  | failedEntityInvariant (definition : Syntax.Ref) (recordKey condition : String) (command : Syntax.Ref)
  | failedSingleInvariant (definition : Syntax.Ref) (condition : String) (command : Syntax.Ref)
  | failedServiceInvariant (condition : String) (command : Syntax.Ref)
  | failedChartInvariant (definition : Syntax.Ref) (condition : String)
  | duplicateItemKey (definition : Syntax.Ref) (map : String) (itemKey : Value)
  | exceededCommandDepth (definition : Syntax.Ref) (limit : Nat)
  | exceededMessageCommands (definition : Syntax.Ref) (limit : Nat)
  | exceededAlwaysRounds (definition : Syntax.Ref) (limit : Nat)
  | exceededOnDoneSelections (definition : Syntax.Ref) (limit : Nat)
  /--
  The work items and commands of one message come from every definition that the message runs, none of which alone
  exceeds the limit, so the fault names no definition.
  -/
  | exceededMessageWork (limit : Nat)
  /-- The deadlines of one clock advance belong to any charts, so the fault names no definition. -/
  | exceededDueDeadlines (limit : Nat)
  /-- The nested exits run through the copies and screens of several definitions, so the fault names no definition. -/
  | exceededExitDepth (limit : Nat)
  | rejectedAutomationCommand (definition : Syntax.Ref) (rejection : Rejection)
  | rejectedShows (definition : Syntax.Ref) (slot : String) (rejection : Rejection)
deriving Repr

derive_group Fault

/-- Whether the fault halts the run, which it does when the behavior after the fault is undefined. -/
def Fault.halts : Fault → Bool
  | .emittedPayloadSchema .. | .unlistedEmittedEvent .. | .sameRecordInBag .. | .outputSchema ..
  | .automationInputSchema .. | .requestInputSchema .. | .showsInputSchema .. | .screenInputSchema ..
  | .failedRequires .. | .heldSchema ..
  | .offersSchema .. | .initialContextSchema .. | .screenOutputSchema .. | .copyContextSchema .. | .contextSchema ..
  | .itemsSchema .. | .unheld .. | .notOnly .. | .exception .. | .duplicateItemKey .. | .exceededCommandDepth ..
  | .exceededMessageCommands .. | .exceededAlwaysRounds .. | .exceededOnDoneSelections .. | .exceededMessageWork ..
  | .exceededDueDeadlines .. | .exceededExitDepth .. => true
  | .danglingRef .. | .danglingSingleRef .. | .failedEnsures .. | .failedEntityInvariant .. | .failedSingleInvariant ..
  | .failedServiceInvariant .. | .failedChartInvariant .. | .rejectedAutomationCommand .. | .rejectedShows .. => false

end Tazuna.Semantics
