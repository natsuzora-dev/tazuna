import Tazuna.Validation.Illegal

namespace Tazuna.Validation.Commands

open Tazuna.Data
open Tazuna.Syntax

def check (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    match d.body with
    | .command _ _ _ emits .. =>
      emits.filterMap fun e => e.bind fun e => if e.service == d.service then none else some (.foreignEvent d.ref e)
    | _ => []

end Tazuna.Validation.Commands
