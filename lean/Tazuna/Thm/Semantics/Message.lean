import Tazuna.Semantics.Message

namespace Tazuna.Thm.Semantics.Message

open Tazuna.Data Tazuna.Semantics

theorem unnamed_lines_counted_by_type (to : String) (a : Answer) :
    (LineBody.answer to a).idName = "answer" ∧ (LineBody.unsubscribe to).idName = "unsubscribe" ∧
      LineBody.time.idName = "time" ∧ LineBody.restart.idName = "restart" :=
  ⟨rfl, rfl, rfl, rfl⟩

end Tazuna.Thm.Semantics.Message
