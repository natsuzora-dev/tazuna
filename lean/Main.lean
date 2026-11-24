import Tazuna.Cli.Check
import Tazuna.Version

/-- `tazuna-engine` prints the version; `tazuna-engine check <ir.json>` checks a converted spec. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => IO.println Tazuna.version; return 0
  | ["check", path] => Tazuna.Cli.check path
  | _ => IO.eprintln "usage: tazuna-engine [check <ir.json>]"; return 3
