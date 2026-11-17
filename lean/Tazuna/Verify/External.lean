import Tazuna.Verify.Compare

/-!
This module checks an external service's trace against the service's contract, as far as the spec's structure
allows.
-/

namespace Tazuna.Verify

open Tazuna.Data
open Tazuna.Spec

structure Request where
  definition : Definition
  accepted : Bool
  answered : Bool

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
      setAt requests id (definition.map fun definition => { definition, accepted := false, answered := false }))
  | .answer .out _ to answer =>
    match requests.lookup to, answer with
    | none, _ => (some (.uncomparable (.unknownAnswer line (Subject.of l))), requests)
    | some none, _ => (none, requests)
    | some (some r), _ =>
      if r.answered then (some (.mismatch (.repeatedAnswer line to r.definition.ref)), requests) else
      let answered := setAt requests to (some { r with accepted := answer matches .accepted _, answered := true })
      match answer, r.definition.kind with
      | .rejected rejection, _ =>
        (if (s.rejectionKinds service r.definition.ref).contains rejection.kind then none
         else some (.mismatch (.assumption line to r.definition.ref (.unlistedRejectionKind rejection))), answered)
      | .accepted _, "command" | .fulfilled _, "query" => (none, answered)
      | .accepted _, _ => (some (.mismatch (.answerResult line to r.definition.ref "accepted")), answered)
      | .fulfilled _, _ => (some (.mismatch (.answerResult line to r.definition.ref "fulfilled")), answered)
  | .event .out _ name _ resultOf =>
    let found := match s.named service (some name) ["event"] with
      | none => some (.uncomparable (.unknownEvent line (Subject.of l)))
      | some event =>
        match resultOf with
        | none =>
          if (s.contractsListing event.ref).contains service then none
          else some (.mismatch (.unlistedEvent line event.ref))
        | some id =>
          match requests.lookup id with
          | none => some (.uncomparable (.resultOfUnknownRequest line event.ref id))
          | some none => none
          | some (some r) =>
            (s.resultOfMismatch r.definition.ref r.accepted event.ref).map
              (resultOfFinding line event.ref id r.definition.ref)
    (found, requests)
  | _ => (none, requests)

/-- The violations of the lines. `line` is the number of the first of `lines`. -/
def checkLines (s : Structure) (service : String) :
    List (Option TraceLine) → Nat → List (String × Option Request) → List Finding
  | [], _, _ => []
  | none :: ls, line, requests => checkLines s service ls (line + 1) requests
  | some l :: ls, line, requests =>
    let (found, requests) := checkLine s service requests line l
    found.toList ++ checkLines s service ls (line + 1) requests

/-- The violations of the lines before the trace's first malformed line, followed by that line's violation. -/
def checkExternal (s : Structure) (service : String) (trace : List (FileLine TraceLine)) : List Finding :=
  let (lines, malformed) := untilMalformed trace
  checkLines s service lines 1 [] ++ (malformed.map fun n => .uncomparable (.lineSchema n)).toList

end Tazuna.Verify
