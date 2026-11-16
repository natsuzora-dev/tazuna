import Tazuna.Service.Idempotency

namespace Tazuna.Thm.Service.Idempotency

open Tazuna.Data Tazuna.Semantics

theorem first_answer_kept (table : CommandAnswers) (id : String) (r : Request) (a : Answer)
    (hk : table.find? id = none) (ha : keepsAnswer a = true) :
    (table.keep id r a).find? id = some (r, a) := by
  unfold CommandAnswers.keep CommandAnswers.find? at *
  rw [Option.map_eq_none_iff] at hk
  simp [ha, List.find?_append, hk]

end Tazuna.Thm.Service.Idempotency
