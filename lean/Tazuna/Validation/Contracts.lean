import Tazuna.Validation.Illegal

namespace Tazuna.Validation.Contracts

open Tazuna.Data
open Tazuna.Syntax

def check (s : Structure) : List Illegal :=
  s.contracts.flatMap fun c =>
    c.members.filterMap fun (key, member) =>
      member.bind fun m => if m.service == c.service then none else some (.foreignMember c.service key)

end Tazuna.Validation.Contracts
