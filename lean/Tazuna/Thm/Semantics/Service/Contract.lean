import Tazuna.Semantics.Service.Contract
import Tazuna.Thm.Semantics.Value.Basic
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Semantics.Service.Contract

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Value.Basic

variable {st : Service} {fs : Functions Id}

@[guarantee] theorem failed_ensures_blames_command (name : String) (input : Value) (caller : Caller) (before after : Records)
    (now : Time) (c : String) (he : fs.ensures name input caller before after now = .ok (some c)) :
    commandEnsures st fs name input caller before after now = [.failedEnsures (st.ref name) c] := by
  simp [commandEnsures, he, Service.failedEnsures]

end Tazuna.Thm.Semantics.Service.Contract
