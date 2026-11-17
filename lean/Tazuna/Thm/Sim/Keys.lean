import Tazuna.Sim.Run
import Tazuna.Thm.Service.Keys

/-!
The createKey values of the participants of a simulation: each participant's values differ from each other, and from
every string that the scenario may write, so a Given record never holds a key that a participant creates later.
-/

namespace Tazuna.Thm.Sim.Keys

open Tazuna.Data Tazuna.Semantics Tazuna.Sim
open Tazuna.Thm.Service.Keys

/--
A string that writtenKey? lets a scenario write is no createKey value of a keyed entity of a running participant `p`,
in any state whose values `p` qualifies.
-/
theorem unwritten_not_created {w : World} {p : String} {st : Service} (hs : (p, st) ∈ w.services) {s : State}
    (ho : s.keyOwner = some p) {e k : String} (he : e ∈ st.entities) (hk : st.singles.contains e = false)
    (hw : w.writtenKey? (.str k) = none) : (e, k) ∉ s.created := by
  intro h
  obtain ⟨n, hn, hc⟩ := created_form h
  rw [ho] at hc
  have hkey := keyChars_isKeyOf p e n hn k hc
  simp only [World.writtenKey?, Value.strings, List.findSome?_cons, List.findSome?_nil] at hw
  split at hw
  · cases hw
  · rename_i hnone
    have := List.findSome?_eq_none_iff.mp hnone (p, st) hs
    simp only [Option.map_eq_none_iff, List.find?_eq_none] at this
    exact this e he (by simp only [hkey, Bool.and_true, Bool.not_eq_eq_eq_not, Bool.not_true]; exact hk)

end Tazuna.Thm.Sim.Keys
