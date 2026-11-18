import Tazuna.Data.Wire

namespace Tazuna.Service

open Tazuna.Data

/--
An instance of a machine or screen, or a copy of a map state. `serial` numbers the instances of `chart` in creation
order from 0: a machine, or a screen that no other screen opens, has only serial 0. A copy is the copy of `owner`'s map
state `map` for the item whose key is `key`, a canonical value (its fields in canonical order), so equal keys are
equal values.
-/
inductive InstanceId where
  | top (chart : String) (serial : Nat)
  | copy (owner : InstanceId) (map : String) (key : Value)
deriving DecidableEq, Repr, Inhabited

derive_wire_mutual (InstanceId tag "kind")

def InstanceId.chart : InstanceId → String
  | .top c _ => c
  | .copy o _ _ => o.chart

/-- The instance itself, or the owner of a copy. -/
def InstanceId.owner : InstanceId → InstanceId
  | .copy o _ _ => o
  | i => i

/-- The map state of a copy. -/
def InstanceId.map? : InstanceId → Option String
  | .copy _ m _ => some m
  | .top .. => none

/-- The canonical item key of a copy. -/
def InstanceId.key? : InstanceId → Option Value
  | .copy _ _ k => some k
  | .top .. => none

/-- Whether `i` is `r` or a copy of `r`. -/
def InstanceId.within (i r : InstanceId) : Bool := i == r || i.owner == r

end Tazuna.Service
