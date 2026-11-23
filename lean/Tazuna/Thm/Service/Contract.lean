import Tazuna.Service.Contract
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Service.Contract

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic

variable {st : Service} {fs : Functions Id}

@[guarantee] theorem failed_ensures_blames_command (name : String) (input : Value) (caller : Caller) (before after : Records)
    (now : Time) (c : String) (he : fs.ensures name input caller before after now = .ok (some c)) :
    commandEnsures st fs name input caller before after now = [.failedEnsures (st.ref name) c] := by
  simp [commandEnsures, he, Service.failedEnsures]

end Tazuna.Thm.Service.Contract
