import Tazuna.Service.Message

namespace Tazuna.Service

open Tazuna.Data

/-- The part of a command by which two commands with the same id are compared. -/
structure Request where
  name : String
  input : Value
deriving DecidableEq, Repr, Inhabited

/-- The first recorded answer for each id, with the request that it answered. -/
abbrev CommandAnswers := List (String × Request × Answer)

def CommandAnswers.find? (table : CommandAnswers) (id : String) : Option (Request × Answer) :=
  (List.find? (·.1 == id) table).map (·.2)

def answerAgain (known : Request × Answer) (request : Request) : Answer :=
  if known.1 = request then known.2 else .rejected { kind := .reusedId }

/--
Whether the answer is kept for its id. An invalid-input rejection is not kept, so the caller may correct the input and
send it again with the same id (corrected_input_processed): the command rejected the input before it ran, as Stripe
saves no idempotent result when the parameters fail validation; the IETF Idempotency-Key draft leaves this to the
server.
-/
def keepsAnswer : Answer → Bool
  | .rejected { kind := .invalidInput, .. } => false
  | _ => true

def CommandAnswers.keep (table : CommandAnswers) (id : String) (request : Request) (answer : Answer) :
    CommandAnswers :=
  if keepsAnswer answer then table ++ [(id, request, answer)] else table

end Tazuna.Service
