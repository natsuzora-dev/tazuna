import Tazuna.Semantics.Validation.Illegal

namespace Tazuna.Semantics.Validation.Contracts

open Tazuna.Ir
open Tazuna.Ir

def check (s : Structure) : List Illegal :=
  s.contracts.flatMap fun c =>
    c.members.filterMap fun (key, member) =>
      member.bind fun m => if m.service == c.service then none else some (.foreignMember c.service key)

end Tazuna.Semantics.Validation.Contracts
