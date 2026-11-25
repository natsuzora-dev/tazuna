import Tazuna.Cli.Test
import Tazuna.Cli.Prove
import Tazuna.Version

/-- `tazuna-engine` prints the version. The launcher runs `tazuna-engine <command> <root> [...] --ir <path>`, with the
user's arguments as given and the IR it converted from them. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => IO.println Tazuna.version; return 0
  | ["check", root, "--ir", path] => Tazuna.Cli.check root path
  | ["test", root, "--ir", path] => Tazuna.Cli.test root path false
  | ["test", root, "--update", "--ir", path] => Tazuna.Cli.test root path true
  | ["verify", root, dir, "--ir", path] => Tazuna.Cli.verify root dir path
  | ["prove", root, "--ir", path] => Tazuna.Cli.prove root path none
  | ["prove", root, "--only", prefix_, "--ir", path] => Tazuna.Cli.prove root path (some prefix_)
  | _ =>
    IO.eprintln "usage: tazuna-engine [check <root> | test <root> [--update] | verify <root> <traces-dir> | prove <root> [--only <prefix>]] --ir <ir.json>"
    return 3
