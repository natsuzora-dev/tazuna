import Tazuna.Validation.Illegal

namespace Tazuna.Validation.Commands

open Tazuna.Data
open Tazuna.Syntax

def foreignEvents (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    match d.body with
    | .command _ _ _ emits .. =>
      emits.filterMap fun e => e.bind fun e => if e.service == d.service then none else some (.foreignEvent d.ref e)
    | _ => []

/-- Whether `key` is an array index of ECMA-262: the canonical decimal form of a whole number below 2^32 - 1. -/
def isArrayIndex (key : String) : Bool :=
  match key.toNat? with
  | some n => n < 2 ^ 32 - 1 && toString n == key
  | none => false

def indexReasons (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    ((s.rejectionReasons d.ref).filter isArrayIndex).map (.indexReason d.ref)

def check (s : Structure) : List Illegal := foreignEvents s ++ indexReasons s

end Tazuna.Validation.Commands
