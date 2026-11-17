namespace Tazuna.Service

/--
An instance of a machine or screen, or a copy of a map state. `serial` numbers the instances of `chart` in creation
order from 0: a machine, or a screen that no other screen opens, has only serial 0. A copy is the copy of `owner`'s map
state `map` for the item whose key has the canonical JSON `key`.
-/
inductive InstanceId where
  | top (chart : String) (serial : Nat)
  | copy (owner : InstanceId) (map key : String)
deriving DecidableEq, Repr, Inhabited

def InstanceId.chart : InstanceId → String
  | .top c _ => c
  | .copy o _ _ => o.chart

def InstanceId.serial : InstanceId → Nat
  | .top _ n => n
  | .copy o _ _ => o.serial

/-- The instance itself, or the owner of a copy. -/
def InstanceId.owner : InstanceId → InstanceId
  | .copy o _ _ => o
  | i => i

/-- The canonical item key of a copy. -/
def InstanceId.key? : InstanceId → Option String
  | .copy _ _ k => some k
  | .top .. => none

def InstanceId.copyOf (i : InstanceId) (map key : String) : InstanceId := .copy i map key

/-- Whether `i` is `r` or a copy of `r`. -/
def InstanceId.within (i r : InstanceId) : Bool := i == r || i.owner == r

end Tazuna.Service
