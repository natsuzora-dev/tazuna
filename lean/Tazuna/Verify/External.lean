import Tazuna.Verify.Compare

/-!
This module checks an external service's trace against the service's contract, as far as the spec's structure
allows.
-/

namespace Tazuna.Verify

open Tazuna.Data
open Tazuna.Spec

/-- A request of the trace: its first answer, if any, and the lines of the events naming it as their resultOf. -/
structure Request where
  definition : Definition
  answer : Option Answer := none
  results : List (Nat × Ref) := []

/-- Whether no answer rejected the request. -/
def Request.accepted (r : Request) : Bool := r.answer.all (· matches .accepted _)

def resultOfFinding (line : Nat) (event : Ref) (requestId : String) (target : Ref) : ResultOfMismatch → Finding
  | .resultOfNonCommand => .uncomparable (.resultOfNonCommand line event requestId target)
  | .resultOfUnacceptedRequest => .mismatch (.resultOfUnacceptedRequest line event requestId target)
  | .resultOfUnlistedEvent => .mismatch (.resultOfUnlistedEvent line event requestId target)

def checkLine (s : Structure) (service : String) (requests : List (String × Option Request)) (line : Nat)
    (l : TraceLine) : Option Finding × List (String × Option Request) :=
  match l.body with
  | .command .in id name _ | .query .in id name _ =>
    let definition := s.named service (some name) [l.body.type]
    (if definition.isSome then none else some (.uncomparable (.unknownRequest line (Subject.of l))),
      setAt requests id (definition.map fun definition => { definition }))
  | .answer .out _ to answer =>
    match requests.lookup to, answer with
    | none, _ => (some (.uncomparable (.unknownAnswer line (Subject.of l))), requests)
    | some none, _ => (none, requests)
    | some (some r), _ =>
      if r.answer.isSome then (some (.mismatch (.repeatedAnswer line to r.definition.ref)), requests) else
      let answered := setAt requests to (some { r with answer })
      match answer, r.definition.kind with
      | .rejected rejection, _ =>
        (if (s.rejectionKinds service r.definition.ref).contains rejection.kind then none
         else some (.mismatch (.assumption line to r.definition.ref (.unlistedRejectionKind rejection))), answered)
      | .accepted _, "command" | .fulfilled _, "query" => (none, answered)
      | .accepted _, _ => (some (.mismatch (.answerResult line to r.definition.ref "accepted")), answered)
      | .fulfilled _, _ => (some (.mismatch (.answerResult line to r.definition.ref "fulfilled")), answered)
  | .event .out _ name _ resultOf =>
    match s.named service (some name) ["event"], resultOf with
    | none, _ => (some (.uncomparable (.unknownEvent line (Subject.of l))), requests)
    | some event, none =>
      (if (s.contractsListing event.ref).contains service then none
       else some (.mismatch (.unlistedEvent line event.ref)), requests)
    | some event, some id =>
      match requests.lookup id with
      | none => (some (.uncomparable (.resultOfUnknownRequest line event.ref id)), requests)
      | some none => (none, requests)
      | some (some r) => (none, setAt requests id (some { r with results := r.results ++ [(line, event.ref)] }))
  | _ => (none, requests)

/--
The violations of the result events of the requests, found once the trace ends, since a result event may come before
or after its request's answer. A request that no answer reached may have results.
-/
def checkResults (s : Structure) (requests : List (String × Option Request)) : List Finding :=
  requests.flatMap fun (id, r) => match r with
    | none => []
    | some r => r.results.filterMap fun (line, event) =>
      (s.resultOfMismatch r.definition.ref r.accepted event).map
        (resultOfFinding line event id r.definition.ref)

/-- The violations of the lines, then of their result events. `line` is the number of the first of `lines`. -/
def checkLines (s : Structure) (service : String) :
    List (Option TraceLine) → Nat → List (String × Option Request) → List Finding
  | [], _, requests => checkResults s requests
  | none :: ls, line, requests => checkLines s service ls (line + 1) requests
  | some l :: ls, line, requests =>
    let (found, requests) := checkLine s service requests line l
    found.toList ++ checkLines s service ls (line + 1) requests

/-- The violations of the lines before the trace's first malformed line, followed by that line's violation. -/
def checkExternal (s : Structure) (service : String) (trace : List (FileLine TraceLine)) : List Finding :=
  let (lines, malformed) := untilMalformed trace
  checkLines s service lines 1 [] ++ (malformed.map fun n => .uncomparable (.lineSchema n)).toList

end Tazuna.Verify
