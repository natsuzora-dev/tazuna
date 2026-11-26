import Tazuna.Cli.Test
import Tazuna.Cli.Prove
import Tazuna.Cli.Generate
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
  | "prove" :: root :: rest =>
    match Tazuna.Cli.optionsOf rest with
    | some (opts, path) =>
      try Tazuna.Cli.prove root path opts
      catch e =>
        IO.eprintln s!"tazuna-engine: internal error: {e}"
        return 4
    | none => usage
  | "generate" :: root :: dir :: rest =>
    match Tazuna.Cli.optionsOf rest with
    | some (opts, path) =>
      try Tazuna.Cli.generate root dir path opts
      catch e =>
        IO.eprintln s!"tazuna-engine: internal error: {e}"
        return 4
    | none => usage
  | _ => usage
where
  usage : IO UInt32 := do
    IO.eprintln ("usage: tazuna-engine [check <root> | test <root> [--update] | verify <root> <traces-dir> | " ++
      "prove <root> [--only <prefix>] [--jobs <n>] | generate <root> <dir> [--only <prefix>] [--jobs <n>]] " ++
      "--ir <ir.json>")
    return 3
