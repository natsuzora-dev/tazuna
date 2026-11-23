import Tazuna.Semantics.Value.Binding
import Tazuna.Thm.Ir.List

/-!
`Renamed` states when two values compare equal up to a relation between their strings: key references as the relation
relates them, leaves equal, and bags and objects in any order. The comparison theorems (Thm/Semantics/Value/Binding)
state what matchValue compares equal by it.
-/

namespace Tazuna.Thm.Semantics.Value.Renaming

open Tazuna.Ir Tazuna.Semantics
open Tazuna.Thm.Ir.List (lookup_of_mem mem_of_lookup)

mutual

/--
`s` renames to `t` under the string relation `R`: key references as `R` relates them, leaves (strings too) equal,
arrays and runs element by element, and bags and objects after reordering the elements or fields of `t`. For objects
with distinct keys, as verify reads them, reordering the fields is what sameKeys and lookup compare.
-/
inductive Renamed (R : String → String → Prop) : CValue → CValue → Prop
  | ref {e e' s t : String} : R s t → Renamed R (.ref e s) (.ref e' t)
  | leaf {x : Value} : Renamed R (.leaf x) (.leaf x)
  | arr {xs ys : List CValue} : RenamedList R xs ys → Renamed R (.arr xs) (.arr ys)
  | runs {xs ys : List CValue} : RenamedList R xs ys → Renamed R (.runs xs) (.runs ys)
  | obj {fs gs gs' : List (String × CValue)} : RenamedFields R fs gs' → gs'.Perm gs → Renamed R (.obj fs) (.obj gs)
  | bag {xs ys ys' : List CValue} : RenamedList R xs ys' → ys'.Perm ys → Renamed R (.bag xs) (.bag ys)

inductive RenamedList (R : String → String → Prop) : List CValue → List CValue → Prop
  | nil : RenamedList R [] []
  | cons {x y : CValue} {xs ys : List CValue} : Renamed R x y → RenamedList R xs ys →
      RenamedList R (x :: xs) (y :: ys)

inductive RenamedFields (R : String → String → Prop) : List (String × CValue) → List (String × CValue) → Prop
  | nil : RenamedFields R [] []
  | cons {k : String} {x y : CValue} {fs gs : List (String × CValue)} : Renamed R x y → RenamedFields R fs gs →
      RenamedFields R ((k, x) :: fs) ((k, y) :: gs)

end

/-! ## The value relation -/

mutual

theorem Renamed.mono {R S : String → String → Prop} (hRS : ∀ s t, R s t → S s t) :
    {s t : CValue} → Renamed R s t → Renamed S s t
  | _, _, .ref h => .ref (hRS _ _ h)
  | _, _, .leaf => .leaf
  | _, _, .arr h => .arr (RenamedList.mono hRS h)
  | _, _, .runs h => .runs (RenamedList.mono hRS h)
  | _, _, .obj h hp => .obj (RenamedFields.mono hRS h) hp
  | _, _, .bag h hp => .bag (RenamedList.mono hRS h) hp

theorem RenamedList.mono {R S : String → String → Prop} (hRS : ∀ s t, R s t → S s t) :
    {xs ys : List CValue} → RenamedList R xs ys → RenamedList S xs ys
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons (Renamed.mono hRS h) (RenamedList.mono hRS hl)

theorem RenamedFields.mono {R S : String → String → Prop} (hRS : ∀ s t, R s t → S s t) :
    {fs gs : List (String × CValue)} → RenamedFields R fs gs → RenamedFields S fs gs
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons (Renamed.mono hRS h) (RenamedFields.mono hRS hl)

end

end Tazuna.Thm.Semantics.Value.Renaming
