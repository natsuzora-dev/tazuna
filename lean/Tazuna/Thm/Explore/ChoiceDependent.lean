import Tazuna.Explore.ChoiceDependent
import Tazuna.Thm.Data.Binding

namespace Tazuna.Thm.Explore.ChoiceDependent

open Tazuna.Data Tazuna.Explore
open Tazuna.Thm.Data.Binding
open Tazuna.Thm.Data.Renaming (Renamed)

/--
Parts that samePart finds the same, such as the states (sameState: records and instances together), are renamed into
each other under a binding that extends one of the output bindings: each created key of `original` stands for one
created key of `alternative`, one to one.
-/
theorem samePart_renamed {part : Settled → CValue} {set : List Binding} {original alternative : Settled}
    (hx : Distinct (part original)) (hy : Distinct (part alternative))
    (h : samePart part set original alternative = .same) :
    ∃ b ∈ set, ∃ c : Binding, b.Extends c ∧ OneToOne c.pairs ∧
      Renamed (BoundBy (fun s => (original.created.lookup s).getD "") c)
        (part original) (part alternative) := by
  unfold samePart Sameness.any at h
  dsimp only at h
  split at h
  · rename_i hc
    obtain ⟨sm, hsm, e⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
    unfold Matches.sameness at e
    split at e
    · rename_i c cs hm
      exact ⟨sm, hsm, c.val, c.property, c.val.pairs_oneToOne,
        matchValue_renamed _ sm _ _ hx hy hm c List.mem_cons_self⟩
    · cases e
    · cases e
  · split at h <;> cases h

end Tazuna.Thm.Explore.ChoiceDependent
