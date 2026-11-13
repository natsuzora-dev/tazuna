import Tazuna.Data.Answer
import Tazuna.Data.Time
import Tazuna.Data.Trace
import Tazuna.Semantics.Note

namespace Tazuna.Semantics

open Tazuna.Data

/-- The waiting request that an answer input answers. -/
inductive Choice where
  /-- The request whose trace line has id `to`, which only test's search writes. -/
  | search (to : String)
  /-- The longest-waiting request whose input is `input`, when given, and that is stale exactly when `stale` is true. -/
  | mock (input : Option Value) (stale : Option Bool)
deriving Repr, Inhabited

derive_wire Choice untagged skip_serializing_none

inductive Step.Body where
  /-- An input that only advances the time and writes its line. -/
  | time
  /-- A restart of the service by its environment, such as the OS or a test harness. -/
  | restart
  | command (id : Option String) (name : String) (input : Value)
  | query (id : Option String) (name : String) (input : Value)
  | subscribe (id : Option String) (name : String) (input : Value)
  | unsubscribe (to : String)
  /-- An event whose `resultOf` is the index, from 0, of the answer input to the request that the event results from. -/
  | event (id : Option String) (name : String) (payload : Value) (resultOf : Option Nat)
  | operation (screen : String) (control : String) (payload : Value)
  | unacceptedOperation (screen : String) (control : String) (payload : Value)
  /--
  An answer to the request from `sender` to `target` that `choice` chooses, or without `choice`, to the longest-waiting
  request that is not stale.
  -/
  | answer (sender : String) (target : String) (answer : Answer) (choice : Option Choice)
deriving Repr, Inhabited

derive_wire Step.Body tag "type" skip_serializing_none

/-- The values that the input gives the service: an input, a payload, or an answer's output. -/
def Step.Body.values : Step.Body → List Value
  | .command _ _ input | .query _ _ input | .subscribe _ _ input => [input]
  | .event _ _ payload _ | .operation _ _ payload | .unacceptedOperation _ _ payload => [payload]
  | .answer _ _ a _ => a.output?.toList
  | .time | .restart | .unsubscribe _ => []

/--
An input of a run in JSON: the fields of its `in` line, with trace names in place of definitions and `id` only when
given, except that an answer has `choice` instead of `to` and an event's `resultOf` is the position of the answer input
instead of a line id. It arrives at `time`, after the deadlines due by then; `deadlineOrder` is the `deadlineOrder` of
its `in` line.
-/
structure Step where
  time : DateTime
  body : Step.Body
  deadlineOrder : Option (List DeadlineId)
  /--
  The steps that the internal queue takes first during the input, which only test's search writes: while entries
  remain, each work or own-service command that the queue takes is the ready one that the next entry names
  (InvalidInput.unreadyStep, InvalidInput.unusedStepOrder); after them, the queue order.
  -/
  stepOrder : Option (List StepName)
deriving Repr, Inhabited

derive_wire Step flatten body skip_serializing_none

end Tazuna.Semantics
