import Tazuna.Cli.Check
import Tazuna.Version

/-- `tazuna-engine` prints the version. The launcher runs `tazuna-engine <command> <root> [...] --ir <path>`, with the
user's arguments as given and the IR it converted from them. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => IO.println Tazuna.version; return 0
  | ["check", _, "--ir", path] => Tazuna.Cli.check path
  | _ => IO.eprintln "usage: tazuna-engine [check <root> --ir <ir.json>]"; return 3
