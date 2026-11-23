import Tazuna.Ir.Trace
import Tazuna.Ir.Structure

/-!
A scenario names an earlier fact only through a handle: what a line, or the startup at the start, caused. Handles name
facts by content; the index of a line is internal and never written.
-/

namespace Tazuna.Semantics.Scenario

open Tazuna.Ir

/-- What caused a fact: the startup of every running service at the start, or the scenario line `index`, from 0. -/
inductive Origin where
  | startup
  | line (index : Nat)
deriving DecidableEq, Repr, Inhabited

derive_wire Origin tag "type"

inductive RequestType where
  | command
  | query
  | subscribe
deriving DecidableEq, Repr, Inhabited

derive_wire RequestType

inductive Part where
  | input
  | output
deriving DecidableEq, Repr, Inhabited

derive_wire Part

mutual
/-- A fact that a line or the startup caused, named by content. -/
inductive Fact where
  /--
  The requests of kind `kind` to `target` that running services sent while `origin` was processed, whose input has each
  field of `input`, when given, equal as the sender's input schema compares it. They must be equal, and a line that
  names them acts on each.
  -/
  | request (origin : Origin) (kind : RequestType) (target : Ir.Ref) (input : Option Template)
  /--
  The events `event` that running services emitted while `origin` was processed, with each field of `payload` equal when
  given, as they travel to `receiver` when given, or to their only receiver. They must be equal; of those on one channel,
  a line acts on the oldest in flight.
  -/
  | event (origin : Origin) (event : Ir.Ref) (payload : Option Template) (receiver : Option String)
  /--
  The answers to the requests that line `to` sent or delivered, which their receivers gave while `origin` was processed,
  one per request.
  -/
  | answer (origin : Origin) (to : Nat)
  /--
  The end of the subscription that the request `subscription` opened, which its sender sent while `origin` was
  processed.
  -/
  | «end» (origin : Origin) (subscription : Fact)
  /--
  The messages that line `index` itself carried: a request it sent, messages that a peer line stated, or those that it
  delivered.
  -/
  | line (index : Nat)
  /-- The instance of screen `screen` that opened while `origin` was processed. -/
  | screen (origin : Origin) (screen : Ir.Ref)
deriving BEq, Repr, Inhabited

/--
A value observed when the scenario runs: the field at `path` of the input of the request that `fact` names, or of the
output of its answer. An array element's path entry is its index as a string.
-/
structure ValueRef where
  fact : Fact
  part : Part
  path : List String
deriving BEq, Repr, Inhabited

inductive Fill where
  | ref (value : ValueRef)
  /-- A key that a running peer creates: the peer's run gives the value, which the scenario never writes. -/
  | created
deriving BEq, Repr, Inhabited

/-- The place `path` of a template's value that the run fills. -/
structure Hole where
  path : List String
  fill : Fill
deriving BEq, Repr, Inhabited

/-- A written value whose `holes` the run fills. -/
structure Template where
  value : Value
  holes : List Hole := []
deriving BEq, Repr, Inhabited
end

derive_wire_mutual (Fact tag "type" skip_serializing_none) (ValueRef) (Fill tag "type") (Hole) (Template)

def Template.created (t : Template) : Bool := t.holes.any (·.fill == .created)

mutual
/-- The templates that the handle writes as picks, with the picks of the handles that their holes read, at any depth. -/
partial def Fact.picks : Fact → List Template
  | .request _ _ _ input => (input.map fun t => t :: t.picks).getD []
  | .event _ _ payload _ => (payload.map fun t => t :: t.picks).getD []
  | .«end» _ subscription => subscription.picks
  | _ => []

/-- The picks of the handles that the template's holes read, at any depth. -/
partial def Template.picks (t : Template) : List Template :=
  t.holes.flatMap fun h => match h.fill with
    | .ref r => r.fact.picks
    | .created => []
end

end Tazuna.Semantics.Scenario
