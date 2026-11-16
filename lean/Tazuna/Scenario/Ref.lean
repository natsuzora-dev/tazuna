import Tazuna.Data.Trace
import Tazuna.Syntax.Structure

/-!
A scenario names an earlier fact only through a handle: what a line, or the begin at the start, caused. Handles name
facts by content; the index of a line is internal and never written.
-/

namespace Tazuna.Scenario

open Tazuna.Data

/-- What caused a fact: the begin of every running service at the start, or the scenario line `index`, from 0. -/
inductive Origin where
  | begin
  | line (index : Nat)
deriving DecidableEq, Repr, Inhabited

derive_wire Origin tag "type"

/-- A fact that a line or the begin caused, named by content. -/
inductive Fact where
  /--
  The request to `target` that a running service sent while `origin` was processed, whose input has each field of
  `input`, when given, equal.
  -/
  | request (origin : Origin) (target : Syntax.Ref) (input : Option Value)
  /--
  The event `event` that its service emitted while `origin` was processed, with `payload` when given, as it travels to
  `receiver` when given, or to its only receiver.
  -/
  | event (origin : Origin) (event : Syntax.Ref) (payload : Option Value) (receiver : Option String)
  /-- The answer to the request that line `to` delivered, which its receiver gave while `origin` was processed. -/
  | answer (origin : Origin) (to : Nat)
  /-- The message that line `index` itself carried: a request it sent, or a message it delivered. -/
  | line (index : Nat)
  /-- The instance of screen `screen` that opened while `origin` was processed. -/
  | screen (origin : Origin) (screen : Syntax.Ref)
deriving DecidableEq, Repr, Inhabited

derive_wire Fact tag "type" skip_serializing_none

inductive Part where
  | input
  | output
deriving DecidableEq, Repr, Inhabited

derive_wire Part

/--
A value observed when the scenario runs: the field at `path` of the input of the request that `fact` names, or of the
output of its answer. An array element's path entry is its index as a string.
-/
structure ValueRef where
  fact : Fact
  part : Part
  path : List String
deriving DecidableEq, Repr, Inhabited

derive_wire ValueRef

inductive Fill where
  | ref (value : ValueRef)
  /-- A key that a running peer creates: the peer's run gives the value, which the scenario never writes. -/
  | created
deriving DecidableEq, Repr, Inhabited

derive_wire Fill tag "type"

/-- The place `path` of a template's value that the run fills. -/
structure Hole where
  path : List String
  fill : Fill
deriving DecidableEq, Repr, Inhabited

derive_wire Hole

/-- A written value whose `holes` the run fills. -/
structure Template where
  value : Value
  holes : List Hole := []
deriving DecidableEq, Repr, Inhabited

derive_wire Template

end Tazuna.Scenario
