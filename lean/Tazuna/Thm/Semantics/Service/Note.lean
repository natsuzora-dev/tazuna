import Tazuna.Semantics.Service.Note

namespace Tazuna.Thm.Semantics.Service.Note

open Tazuna.Semantics.Service

@[simp] theorem note_id (n : Note) : (MonadNote.note n : Id Unit) = pure () := rfl

end Tazuna.Thm.Semantics.Service.Note
