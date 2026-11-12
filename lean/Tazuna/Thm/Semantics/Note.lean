import Tazuna.Semantics.Note

namespace Tazuna.Thm.Semantics.Note

open Tazuna.Semantics

@[simp] theorem note_id (n : Note) : (MonadNote.note n : Id Unit) = pure () := rfl

end Tazuna.Thm.Semantics.Note
