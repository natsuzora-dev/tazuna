import Tazuna.Cli.Parts

open Tazuna.Cli in
/-- `size-parts <root> --ir <path> [--only <service>]`: one JSON line per input kind and per response, timer and
own-pair question of each service (`partsOf`). -/
def main : List String → IO UInt32
  | root :: "--ir" :: path :: rest => do
    let only := match rest with
      | ["--only", s] => some s
      | _ => none
    let exit ← IO.mkRef Tazuna.Exit.ok
    match ← (loadSpec root path).run exit with
    | some c =>
      for sv in c.services do
        if only.all (· == sv.v.name) then partsOf c sv
      return 0
    | none => return 1
  | _ => do
    IO.eprintln "usage: size-parts <root> --ir <path> [--only <service>]"
    return 3
