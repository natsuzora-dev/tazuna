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
/-- A fact that a line or the begin caused, named by content. -/
inductive Fact where
  /--
  The request of kind `kind` to `target` that a participant sent while `origin` was processed, whose input has each
  field of `input`, when given, equal as the target's input schema compares it.
  -/
  | request (origin : Origin) (kind : RequestType) (target : Syntax.Ref) (input : Option Template)
  /--
  The handle `handle`, from 0, of the requests that `request` with the same fields names, which are equal as the
  target's input schema compares them and so interchangeable: which of them each handle names is a choice that test
  searches (World.assignments), and handles beyond their number name nothing.
  -/
  | requests (origin : Origin) (kind : RequestType) (target : Syntax.Ref) (input : Option Template) (handle : Nat)
  /--
  The event `event` that a participant emitted while `origin` was processed, with each field of `payload` equal when
  given, as it travels to `receiver` when given, or to its only receiver.
  -/
  | event (origin : Origin) (event : Syntax.Ref) (payload : Option Template) (receiver : Option String)
  /--
  The answer to the request that line `to` sent or delivered, which its receiver gave while `origin` was processed.
  -/
  | answer (origin : Origin) (to : Nat)
  /--
  The end of the subscription that the request `subscription` opened, which its sender sent while `origin` was
  processed.
  -/
  | «end» (origin : Origin) (subscription : Fact)
  /--
  The message that line `index` itself carried: a request it sent, a message that a peer line stated, or one that it
  delivered.
  -/
  | line (index : Nat)
  /-- The instance of screen `screen` that opened while `origin` was processed. -/
  | screen (origin : Origin) (screen : Syntax.Ref)
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
  | .request _ _ _ input | .requests _ _ _ input _ => (input.map fun t => t :: t.picks).getD []
  | .event _ _ payload _ => (payload.map fun t => t :: t.picks).getD []
  | .«end» _ subscription => subscription.picks
  | _ => []

/-- The picks of the handles that the template's holes read, at any depth. -/
partial def Template.picks (t : Template) : List Template :=
  t.holes.flatMap fun h => match h.fill with
    | .ref r => r.fact.picks
    | .created => []
end

/-- The group of the handle of `requests`: the fact with the handle 0, which every handle of the group shares. -/
def Fact.group? : Fact → Option Fact
  | .requests o kind target input _ => some (.requests o kind target input 0)
  | _ => none

mutual
/-- The handle and the handles that it reads, at any depth: those of an end's subscription and of its picks' holes. -/
partial def Fact.named (f : Fact) : List Fact :=
  f :: match f with
    | .request _ _ _ input | .requests _ _ _ input _ | .event _ _ input _ => (input.map Template.named).getD []
    | .«end» _ subscription => subscription.named
    | _ => []

/-- The handles that the template's holes read, at any depth. -/
partial def Template.named (t : Template) : List Fact :=
  t.holes.flatMap fun h => match h.fill with
    | .ref r => r.fact.named
    | .created => []
end

end Tazuna.Scenario
