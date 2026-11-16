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
  /--
  A waiting request that is stale exactly when `stale` is true and, when `input` is given, whose input has each field of
  `input` equal (chosen).
  -/
  | mock (input : Option Value) (stale : Option Bool)
deriving Repr, Inhabited

derive_wire Choice untagged skip_serializing_none

/-- The subscription that an unsubscribe input ends. -/
inductive Ended where
  /-- The subscription whose subscribe line has id `to`, which only test's search and a peer's derived inputs write. -/
  | id (to : String)
  /-- The subscription that the subscribe input with handle `handle` opened. -/
  | handle (handle : String)
deriving Repr, Inhabited

derive_wire Ended untagged

inductive Step.Body where
  /-- An input that only advances the time and writes its line. -/
  | time
  /-- A restart of the service by its environment, such as the OS or a test harness. -/
  | restart
  | command (id : Option String) (name : String) (input : Value)
  | query (id : Option String) (name : String) (input : Value)
  /-- A subscribe input. `handle` is the name by which a later unsubscribe input names the subscription. -/
  | subscribe (id : Option String) (name : String) (input : Value) (handle : Option String)
  | unsubscribe (subscription : Ended)
  /-- An event whose `resultOf` is the handle of the answer input to the request that the event results from. -/
  | event (id : Option String) (name : String) (payload : Value) (resultOf : Option String)
  | operation (screen : String) (control : String) (payload : Value)
  | unacceptedOperation (screen : String) (control : String) (payload : Value)
  /--
  An answer to a request from `sender` to `target` that `choice` chooses, or without `choice`, to a request that is not
  stale (mock). `handle` is the name by which a later event's `resultOf` names the answer.
  -/
  | answer (sender : String) (target : String) (answer : Answer) (choice : Option Choice) (handle : Option String)
  /--
  An answer to the request to `target` whose trace line has id `to`, which only a peer's derived inputs write: the
  peer's run of them does not know which of its definitions sent the request.
  -/
  | answerTo (to : String) (target : String) (answer : Answer)
deriving Repr, Inhabited

derive_wire Step.Body tag "type" skip_serializing_none

/-- The values that the input gives the service: an input, a payload, or an answer's output. -/
def Step.Body.values : Step.Body → List Value
  | .command _ _ input | .query _ _ input | .subscribe _ _ input _ => [input]
  | .event _ _ payload _ | .operation _ _ payload | .unacceptedOperation _ _ payload => [payload]
  | .answer _ _ a _ _ | .answerTo _ _ a => a.output?.toList
  | .time | .restart | .unsubscribe _ => []

/--
An input of a run in JSON: the fields of its `in` line, with trace names in place of definitions and `id` only when
given, except that an answer has `choice` instead of `to`, an unsubscribe has `subscription` instead of `to`, an answer
or a subscribe may have a `handle`, and an event's `resultOf` is the handle of the answer input instead of a request id. It arrives at `time`, after the deadlines due by then;
`deadlineOrder` is the `deadlineOrder` of its `in` line.
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
  /--
  The createKey values that the input's processing creates, by entity name, in creation order within the input, which
  createKey returns in place of `<entity>-<n>` (InvalidInput.unusedKeys).
  -/
  keys : Option (List (String × List String))
deriving Repr, Inhabited

derive_wire Step flatten body skip_serializing_none

end Tazuna.Semantics
