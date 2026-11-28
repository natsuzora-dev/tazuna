import Tazuna.Cli.Test
import Tazuna.Cli.Prove
import Tazuna.Cli.Generate
import Tazuna.Cli.Explain
import Tazuna.Version

open Tazuna.Cli in
/-- The command the arguments name, or none when they name none. The launcher runs `tazuna-engine <command> <root>
[...] --ir <path>`, with the user's arguments as given and the IR it converted from them; `explain [<kind>]` alone, as
it reads no spec; and no arguments for the version. -/
def commandOf : List String → Option (Cmd Unit)
  | [] => some (printLine .version [("version", Lean.Json.str Tazuna.version)])
  | ["check", root, "--ir", path] => some (check root path)
  | ["test", root, "--ir", path] => some (test root path false)
  | ["test", root, "--update", "--ir", path] => some (test root path true)
  | ["verify", root, dir, "--ir", path] => some (verify root dir path)
  | "prove" :: root :: rest => (optionsOf rest).map fun (opts, path) => prove root path opts
  | "generate" :: root :: dir :: rest => (optionsOf rest).map fun (opts, path) => generate root dir path opts
  | ["explain"] => some (explain none)
  | ["explain", kind] => some (explain (some kind))
  | _ => none

def main (args : List String) : IO UInt32 :=
  Tazuna.Cli.Cmd.exitCode <| match commandOf args with
    | some c => c
    | none => Tazuna.Cli.printLine (.usage .arguments) [("message", Lean.Json.str
        ("usage: check <root> | test <root> [--update] | verify <root> <traces-dir> | " ++
          "prove <root> [--only <prefix>] [--jobs <n>] [--timeout <seconds>] | " ++
          "generate <root> <dir> [--only <prefix>] [--jobs <n>] [--timeout <seconds>] | " ++
          "explain [<kind>]"))]
