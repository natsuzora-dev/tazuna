import Tazuna.Service.Note

namespace Tazuna.Thm.Service.Note

open Tazuna.Semantics

@[simp] theorem note_id (n : Note) : (MonadNote.note n : Id Unit) = pure () := rfl

end Tazuna.Thm.Service.Note
