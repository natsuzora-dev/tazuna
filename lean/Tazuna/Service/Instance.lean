import Tazuna.Data.Wire

namespace Tazuna.Service

open Tazuna.Data

/--
An instance of a machine or screen, or a copy of a map state, named by where it sits in the tree of instances, as an
Akka actor path or a React element's position names it. A machine, or a screen that no other screen opens, has one
instance, named by its chart. A screen that `opens` opened is named by the instance `opener` that opened it, the state
`state` and key `key` of that `opens`, and `nth`, which of that `opens`'s openings it is, from 0: each entry of the
state opens it again. A copy is the copy of `owner`'s map state `map` for the item whose key is `key`, a canonical value
(its fields in canonical order), so equal keys are equal values.
-/
inductive InstanceId where
  | top (chart : String)
  | opened (chart : String) (opener : InstanceId) (state key : String) (nth : Nat)
  | copy (owner : InstanceId) (map : String) (key : Value)
deriving DecidableEq, Repr, Inhabited

derive_wire_mutual (InstanceId tag "kind")

def InstanceId.chart : InstanceId → String
  | .top c | .opened c .. => c
  | .copy o _ _ => o.chart

/-- The instance itself, or the owner of a copy. -/
def InstanceId.owner : InstanceId → InstanceId
  | .copy o _ _ => o
  | i => i

/-- The map state of a copy. -/
def InstanceId.map? : InstanceId → Option String
  | .copy _ m _ => some m
  | _ => none

/-- The canonical item key of a copy. -/
def InstanceId.key? : InstanceId → Option Value
  | .copy _ _ k => some k
  | _ => none

/-- The opener of a screen that `opens` opened, with the state and key of that `opens`. -/
def InstanceId.opener? : InstanceId → Option (InstanceId × String × String)
  | .opened _ o s k _ => some (o, s, k)
  | _ => none

/-- Whether `i` is `r` or a copy of `r`. -/
def InstanceId.within (i r : InstanceId) : Bool := i == r || i.owner == r

end Tazuna.Service
