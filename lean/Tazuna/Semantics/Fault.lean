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
  | unlistedEmittedEvent (definition : Syntax.Ref) (event : Option Syntax.Ref)
  | outputSchema (definition : Syntax.Ref)
  | automationInputSchema (definition : Syntax.Ref)
  | requestInputSchema (definition : Syntax.Ref) (target : Syntax.Ref)
  | showsInputSchema (definition : Syntax.Ref) (slot : String)
  | screenInputSchema (definition : Syntax.Ref) (screen : Syntax.Ref)
  | failedRequires (definition : Syntax.Ref) (screen : Syntax.Ref) (condition : String)
  | heldSchema (definition : Syntax.Ref) (held state : String)
  | offersSchema (definition : Syntax.Ref) (control state : String)
  | rootOffersSchema (definition : Syntax.Ref) (control : String)
  | initialContextSchema (definition : Syntax.Ref)
  | screenOutputSchema (definition : Syntax.Ref)
  | copyContextSchema (definition : Syntax.Ref) (map : String)
  | contextSchema (definition : Syntax.Ref)
  | itemsSchema (definition : Syntax.Ref) (map : String)
  | unheld (definition : Syntax.Ref) (held : String)
  | exception (definition : Option Syntax.Ref)
  | danglingRef (definition : Syntax.Ref) (key field targetKey : String) (command : Syntax.Ref)
  | danglingSingleRef (definition : Syntax.Ref) (field targetKey : String) (command : Syntax.Ref)
  | failedEnsures (definition : Syntax.Ref) (condition : String)
  | failedEntityInvariant (definition : Syntax.Ref) (key condition : String) (command : Syntax.Ref)
  | failedSingleInvariant (definition : Syntax.Ref) (condition : String) (command : Syntax.Ref)
  | failedServiceInvariant (condition : String) (command : Syntax.Ref)
  | failedChartInvariant (definition : Syntax.Ref) (condition : String)
  | duplicateItemKey (definition : Syntax.Ref) (map : String) (key : Value)
  | commandDepth (definition : Syntax.Ref)
  | messageCommands (definition : Syntax.Ref)
  | alwaysRounds (definition : Syntax.Ref)
  | onDoneSelections (definition : Syntax.Ref)
  /--
  The work items and commands of one message come from every definition that the message runs, none of which alone
  exceeds the limit, so the fault names no definition.
  -/
  | messageWork
  /-- The deadlines of one clock advance belong to any charts, so the fault names no definition. -/
  | dueDeadlines
  /-- The nested exits run through the copies and screens of several definitions, so the fault names no definition. -/
  | exitDepth
  | rejectedAutomationCommand (definition : Syntax.Ref) (rejection : Rejection)
  | rejectedShows (definition : Syntax.Ref) (slot : String) (rejection : Rejection)
deriving Repr

derive_group Fault

/-- Whether the fault halts the run, which it does when the behavior after the fault is undefined. -/
def Fault.halts : Fault → Bool
  | .emittedPayloadSchema .. | .unlistedEmittedEvent .. | .outputSchema .. | .automationInputSchema ..
  | .requestInputSchema .. | .showsInputSchema .. | .screenInputSchema .. | .failedRequires .. | .heldSchema ..
  | .offersSchema .. | .rootOffersSchema .. | .initialContextSchema .. | .screenOutputSchema .. | .copyContextSchema ..
  | .contextSchema .. | .itemsSchema .. | .unheld .. | .exception .. | .duplicateItemKey .. | .commandDepth ..
  | .messageCommands .. | .alwaysRounds .. | .onDoneSelections .. | .messageWork | .dueDeadlines | .exitDepth => true
  | .danglingRef .. | .danglingSingleRef .. | .failedEnsures .. | .failedEntityInvariant .. | .failedSingleInvariant ..
  | .failedServiceInvariant .. | .failedChartInvariant .. | .rejectedAutomationCommand .. | .rejectedShows .. => false

end Tazuna.Semantics
