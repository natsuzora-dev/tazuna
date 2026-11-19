import Tazuna.Verify.Compare

/-!
This module checks an external service's trace against the service's contract, as far as the spec's structure
allows. As test does with the requests that a service sent (Service.Exchange), verify gathers each request that the
external service received with its answers and result events, and checks it once the trace ends, since a result event
may come before or after its request's answer.
-/

namespace Tazuna.Verify

open Tazuna.Data
open Tazuna.Spec

/--
A request that the external service received, as its trace records it: its first line, the lines that send it again
(firstDuplicate), and the answers and the events naming it as their resultOf that later lines record, in trace order,
each with its line.
-/
structure Exchange where
  line : Nat
  resends : List Nat
  id : String
  definition : Definition
  answers : List (Nat × Answer)
  events : List (Nat × Ref)

/-- The trace's requests that have a definition of `service`, in trace order, each with what later lines record of it. -/
def exchanges (s : Structure) (service : String) (lines : List (Option TraceLine)) : List Exchange :=
  let numbered := (lines.zipIdx 1).filterMap fun (l, i) => l.map (i, ·)
  let sentWith (id : String) (l : TraceLine) := match l.body with
    | .command .in i .. | .query .in i .. => i == id
    | _ => false
  numbered.filterMap fun (i, l) =>
    let later := numbered.filter (·.1 > i)
    match l.body with
    | .command .in id name _ | .query .in id name _ =>
      if numbered.any fun (j, e) => j < i && sentWith id e then none
      else (s.named service (some name) [l.body.type]).map fun definition =>
        { line := i, id, definition
          resends := later.filterMap fun (j, r) => if sentWith id r then some j else none
          answers := later.filterMap fun (j, a) => match a.body with
            | .answer .out _ to answer => if to == id then some (j, answer) else none
            | _ => none
          events := later.filterMap fun (j, e) => match e.body with
            | .event .out _ name _ (some r) =>
              if r == id then (s.named service (some name) ["event"]).map (j, ·.ref) else none
            | _ => none }
    | _ => none

/-- The violation of the line alone. `requests` are the ids of the earlier request lines. -/
def checkLine (s : Structure) (service : String) (requests : List String) (line : Nat) (l : TraceLine) :
    Option Finding :=
  match l.body with
  | .command .in _ name _ | .query .in _ name _ =>
    if (s.named service (some name) [l.body.type]).isSome then none
    else some (.uncomparable (.unknownRequest line (Subject.of l)))
  | .answer .out _ to _ =>
    if requests.contains to then none else some (.uncomparable (.unknownAnswer line (Subject.of l)))
  | .event .out _ name _ resultOf =>
    match s.named service (some name) ["event"], resultOf with
    | none, _ => some (.uncomparable (.unknownEvent line (Subject.of l)))
    | some event, none =>
      if (s.contractsListing event.ref).contains service then none
      else some (.mismatch (.unlistedEvent line event.ref))
    | some event, some id =>
      if requests.contains id then none else some (.uncomparable (.resultOfUnknownRequest line event.ref id))
  | _ => none

/-- The violations of the lines alone. `line` is the number of the first of `lines`. -/
def checkLines (s : Structure) (service : String) : List (Option TraceLine) → Nat → List String → List Finding
  | [], _, _ => []
  | none :: ls, line, requests => checkLines s service ls (line + 1) requests
  | some l :: ls, line, requests =>
    let requests := match l.body with
      | .command .in id .. | .query .in id .. => requests ++ [id]
      | _ => requests
    (checkLine s service requests line l).toList ++ checkLines s service ls (line + 1) requests

/-- The violation of the answer `answer` at `line` to the request `id` of `definition`. -/
def checkAnswer (s : Structure) (service : String) (id : String) (definition : Definition) (line : Nat) :
    Answer → Option Finding
  | .rejected rejection =>
    if (s.rejectionKinds service definition.ref).contains rejection.kind then none
    else some (.mismatch (.assumption line id definition.ref (.unlistedRejectionKind rejection)))
  | .accepted _ => if definition.kind == "command" then none
    else some (.mismatch (.answerResult line id definition.ref "accepted"))
  | .fulfilled _ => if definition.kind == "query" then none
    else some (.mismatch (.answerResult line id definition.ref "fulfilled"))

def resultOfFinding (line : Nat) (event : Ref) (requestId : String) (target : Ref) : ResultOfMismatch → Finding
  | .resultOfNonCommand => .uncomparable (.resultOfNonCommand line event requestId target)
  | .resultOfUnacceptedRequest => .mismatch (.resultOfUnacceptedRequest line event requestId target)
  | .resultOfUnlistedEvent => .mismatch (.resultOfUnlistedEvent line event requestId target)

/--
The violations of the request `x`: of each answer that answers a send of it that no earlier answer answered, of each
other answer as repeated, and of each result event against the target and all the answers (Structure.resultOfMismatch,
as test checks them).
-/
def checkExchange (s : Structure) (service : String) (x : Exchange) : List Finding :=
  let target := x.definition.ref
  let sentBefore (line : Nat) := 1 + (x.resends.filter (· < line)).length
  let (answers, _) := x.answers.foldl (init := ([], 0)) fun (found, answered) (line, answer) =>
    if answered < sentBefore line then
      (found ++ (checkAnswer s service x.id x.definition line answer).toList, answered + 1)
    else (found ++ [.mismatch (.repeatedAnswer line x.id target)], answered)
  answers ++ x.events.filterMap fun (line, event) =>
    (s.resultOfMismatch target (x.answers.map (·.2)) event).map (resultOfFinding line event x.id target)

/--
The violations of the lines that verify checks (comparedLines with `in` requests), by line, followed by the violation of
the line that ends them.
-/
def checkExternal (s : Structure) (service : String) (trace : List (FileLine TraceLine)) : List Finding :=
  let (lines, cut) := comparedLines .in trace
  let found := checkLines s service lines 1 [] ++ (exchanges s service lines).flatMap (checkExchange s service)
  found.mergeSort (fun a b => decide (a.line ≤ b.line)) ++ (cut.map .uncomparable).toList

end Tazuna.Verify
